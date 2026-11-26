module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3StripBounds

/-!
# Assembly of `OuterS3` and `OuterS4` (`cts:smooth-env` (2)–(3))

Proves the remaining bounds for `EsmExt δ` and `EeExt δ` and assembles `theorem outerS3 : OuterS3`
and `theorem outerS4 : OuterS4` (with `Ee := EeExt δ`, `Esm := EsmExt δ` in `OuterStripStatements.lean`):

1. `norm_EsmExt_bounds`: two-sided bounds on `‖EsmExt δ b‖` on `bandUpper (1/16)`, uniform in `δ < 1/40`;
2. `norm_logDeriv_EsmExt_le`: `‖logDeriv (EsmExt δ) b‖ + ‖deriv (logDeriv (EsmExt δ)) b‖ ≤ C` on
   `bandUpper (1/16)`, uniform in `δ < 1/40`;
3. `norm_EeExt_strip_le`: global strip bound on `‖EeExt δ b‖` on `{|Im b| ≤ 1/2 + η_δ/2}`;
4. `norm_EeExt_upper_edge`: upper-edge identity
   `‖EeExt δ (vOf (yOfX x) + I/2)‖ = ‖fDelta Gout δ (starRingEnd ℂ (wPt (yOfX x)))‖` for `x > ξ_*`;
5. `outerS3 : OuterS3` and `outerS4 : OuterS4`.
-/

@[expose] public section

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

private lemma bandUpper_16_sub_8 : bandUpper (1 / 16) ⊆ bandUpper (1 / 8) := fun b hb =>
  lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num)

private lemma bandUpper_16_sub_quarter : bandUpper (1 / 16) ⊆ bandUpper (1 / 4) := fun b hb =>
  lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num)

private lemma bandUpper_16_sub_imStrip : bandUpper (1 / 16) ⊆ imStrip := fun b hb => by
  have h := abs_lt.mp (show |b.im - 1 / 2| < 1 / 16 from hb)
  exact ⟨by linarith, by linarith⟩

private lemma isOpen_bandUpper_16 : IsOpen (bandUpper (1 / 16)) :=
  isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

/-! ### 1. Two-sided bounds on `EsmExt δ` on `bandUpper (1/16)` -/

theorem norm_EsmExt_bounds :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ δ0 < 1 / 4 ∧ etaDelta δ0 < 1 / 16 ∧ 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 → ∀ b ∈ bandUpper (1 / 16),
        C⁻¹ * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) ≤ ‖EsmExt δ b‖ ∧
        ‖EsmExt δ b‖ ≤ C * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
  obtain ⟨δ0, hδ0_pos, hδ0_4, hη0, C_phi, hCphi_pos, hS4b⟩ := outerS4b
  obtain ⟨c1, C1, hc1_pos, h1sq⟩ := norm_one_add_zetaD_sq_sq_bounds
  have hC1_pos : 0 < C1 := by
    have h0 := h1sq (Complex.I / 2) (by change |(Complex.I / 2).im - 1 / 2| < 1 / 16; simp)
    simp only [Complex.div_ofNat_re, Complex.I_re, zero_div, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, mul_one] at h0
    linarith [h0.1, h0.2]
  obtain ⟨c2, C2, hc2_pos, hR4⟩ := norm_R4cStrip_bounds
  have hC2_pos : 0 < C2 := by
    have h0 := hR4 (Complex.I / 2) (by change |(Complex.I / 2).im - 1 / 2| < 1 / 16; simp)
    simp only [Complex.div_ofNat_re, Complex.I_re, zero_div, abs_zero, add_zero, Real.one_rpow,
      mul_one] at h0
    linarith [h0.1, h0.2]
  obtain ⟨M_lg, hMlg_pos, hlg⟩ := abs_re_logGhatRefl_le
  set U_esm : ℝ := C1 / (c2 * Real.exp (-M_lg)) * Real.exp C_phi
  set L_esm : ℝ := c1 / (C2 * Real.exp M_lg) * Real.exp (-C_phi)
  have hU_pos : 0 < U_esm := by positivity
  have hL_pos : 0 < L_esm := by positivity
  set C_esm : ℝ := max U_esm L_esm⁻¹
  have hC_pos : 0 < C_esm := lt_of_lt_of_le hU_pos (le_max_left _ _)
  refine ⟨δ0, C_esm, hδ0_pos, hδ0_4, hη0, hC_pos, fun δ hδ0 hδ1 b hb => ?_⟩
  have hb8 : b ∈ bandUpper (1 / 8) := bandUpper_16_sub_8 hb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_16_sub_quarter hb
  obtain ⟨h1sq_lo, h1sq_hi⟩ := h1sq b hb
  obtain ⟨hR4_lo, hR4_hi⟩ := hR4 b hb
  have hlg_bd : |(logGhatRefl b).re| ≤ M_lg :=
    hlg b (lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num))
  have hdp_bd : |(DeltaPhi δ b).re| ≤ C_phi :=
    (Complex.abs_re_le_norm _).trans ((hS4b δ hδ0 hδ1).2.2 b hb_q).1
  have hlg_lo : Real.exp (-M_lg) ≤ Real.exp (logGhatRefl b).re :=
    Real.exp_le_exp.mpr (abs_le.mp hlg_bd).1
  have hlg_hi : Real.exp (logGhatRefl b).re ≤ Real.exp M_lg :=
    Real.exp_le_exp.mpr (abs_le.mp hlg_bd).2
  have hdp_lo : Real.exp (-C_phi) ≤ Real.exp (-(DeltaPhi δ b).re) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hdp_bd).2])
  have hdp_hi : Real.exp (-(DeltaPhi δ b).re) ≤ Real.exp C_phi :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp hdp_bd).1])
  have hnorm_eq : ‖EsmExt δ b‖ =
      ‖(1 + zetaD b ^ 2) ^ 2‖ / (‖R4cStrip b‖ * Real.exp (logGhatRefl b).re) *
        Real.exp (-(DeltaPhi δ b).re) := by
    unfold EsmExt
    rw [norm_mul, norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
  have h_rpow_inv : ((1 + |b.re|) ^ (1 / 2 : ℝ))⁻¹ = (1 + |b.re|) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg (by positivity)]; congr 1; ring
  have hrp_pos : 0 < (1 + |b.re|) ^ (1 / 2 : ℝ) := by positivity
  have hexp_pos : 0 < Real.exp (-(2 * π * |b.re|)) := Real.exp_pos _
  have hC_inv_le : C_esm⁻¹ ≤ L_esm := by
    rw [inv_le_comm₀ hC_pos hL_pos]
    exact le_max_right _ _
  have hU_le_C : U_esm ≤ C_esm := le_max_left _ _
  have hR4_pos : 0 < ‖R4cStrip b‖ := norm_pos_iff.mpr (R4cStrip_ne_zero hb_q)
  rw [hnorm_eq]
  constructor
  · calc C_esm⁻¹ * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|)))
        ≤ L_esm * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by gcongr
      _ = (c1 * Real.exp (-(2 * π * |b.re|))) /
            ((C2 * (1 + |b.re|) ^ (1 / 2 : ℝ)) * Real.exp M_lg) * Real.exp (-C_phi) := by
          dsimp only [L_esm]; rw [← h_rpow_inv]; field_simp
      _ ≤ ‖(1 + zetaD b ^ 2) ^ 2‖ / (‖R4cStrip b‖ * Real.exp (logGhatRefl b).re) *
            Real.exp (-(DeltaPhi δ b).re) := by gcongr
  · calc ‖(1 + zetaD b ^ 2) ^ 2‖ / (‖R4cStrip b‖ * Real.exp (logGhatRefl b).re) *
            Real.exp (-(DeltaPhi δ b).re)
        ≤ (C1 * Real.exp (-(2 * π * |b.re|))) /
            ((c2 * (1 + |b.re|) ^ (1 / 2 : ℝ)) * Real.exp (-M_lg)) * Real.exp C_phi := by gcongr
      _ = U_esm * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
          dsimp only [U_esm]; rw [← h_rpow_inv]; field_simp
      _ ≤ C_esm * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by gcongr

/-! ### 2. Log-derivative bounds on `EsmExt δ` on `bandUpper (1/16)` -/

private lemma logDeriv_EsmExt_eq_on {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    EqOn (logDeriv (EsmExt δ))
      (fun b => logDeriv (fun w => (1 + zetaD w ^ 2) ^ 2) b - logDeriv R4cStrip b -
        deriv logGhatRefl b - deriv (DeltaPhi δ) b)
      (bandUpper (1 / 16)) := by
  intro b hb
  have hb8 : b ∈ bandUpper (1 / 8) := bandUpper_16_sub_8 hb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_16_sub_quarter hb
  have hb_strip : b ∈ imStrip := bandUpper_16_sub_imStrip hb
  have hopen8 : IsOpen (bandUpper (1 / 8)) :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hzd : DifferentiableAt ℂ zetaD b :=
    differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have hA_diff : DifferentiableAt ℂ (fun w => (1 + zetaD w ^ 2) ^ 2) b := by fun_prop
  have hB_diff : DifferentiableAt ℂ R4cStrip b :=
    differentiableOn_R4cStrip.differentiableAt (isOpen_band.mem_nhds hb_q)
  have hlg_diff : DifferentiableAt ℂ logGhatRefl b :=
    differentiableOn_logGhatRefl.differentiableAt (hopen8.mem_nhds hb8)
  have hdp_diff : DifferentiableAt ℂ (DeltaPhi δ) b :=
    (differentiableOn_DeltaPhi_imStrip hδ0 hδ1).differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have hC_diff : DifferentiableAt ℂ (fun w => Complex.exp (logGhatRefl w)) b := hlg_diff.cexp
  have hD_diff : DifferentiableAt ℂ (fun w => Complex.exp (-DeltaPhi δ w)) b := hdp_diff.neg.cexp
  have hA_ne : (1 + zetaD b ^ 2) ^ 2 ≠ 0 := by
    obtain ⟨c1, _, hc1_pos, h1sq⟩ := norm_one_add_zetaD_sq_sq_bounds
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (h1sq b hb).1)
  have hB_ne : R4cStrip b ≠ 0 := R4cStrip_ne_zero hb_q
  have hC_ne : Complex.exp (logGhatRefl b) ≠ 0 := Complex.exp_ne_zero _
  have hD_ne : Complex.exp (-DeltaPhi δ b) ≠ 0 := Complex.exp_ne_zero _
  have hBC_ne : R4cStrip b * Complex.exp (logGhatRefl b) ≠ 0 := mul_ne_zero hB_ne hC_ne
  have hE_has : HasDerivAt (EsmExt δ)
      (((deriv (fun w => (1 + zetaD w ^ 2) ^ 2) b * (R4cStrip b * Complex.exp (logGhatRefl b)) -
          (1 + zetaD b ^ 2) ^ 2 * (deriv R4cStrip b * Complex.exp (logGhatRefl b) +
            R4cStrip b * (Complex.exp (logGhatRefl b) * deriv logGhatRefl b))) /
        (R4cStrip b * Complex.exp (logGhatRefl b)) ^ 2) * Complex.exp (-DeltaPhi δ b) +
        ((1 + zetaD b ^ 2) ^ 2 / (R4cStrip b * Complex.exp (logGhatRefl b))) *
          (Complex.exp (-DeltaPhi δ b) * (-deriv (DeltaPhi δ) b))) b := by
    have h1 := hA_diff.hasDerivAt
    have h2 := hB_diff.hasDerivAt
    have h3 := hlg_diff.hasDerivAt.cexp
    have h4 := hdp_diff.hasDerivAt.neg.cexp
    exact (h1.div (h2.mul h3) hBC_ne).mul h4
  simp only [logDeriv_apply]
  rw [hE_has.deriv]
  unfold EsmExt
  set A_val : ℂ := (1 + zetaD b ^ 2) ^ 2
  change _ = _ / A_val - _ - _ - _
  have hA_val_ne : A_val ≠ 0 := hA_ne
  field_simp [hA_val_ne, hB_ne, hC_ne, hD_ne]
  ring

theorem norm_logDeriv_EsmExt_le :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ δ0 < 1 / 4 ∧ etaDelta δ0 < 1 / 16 ∧ 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 → ∀ b ∈ bandUpper (1 / 16),
        ‖logDeriv (EsmExt δ) b‖ + ‖deriv (logDeriv (EsmExt δ)) b‖ ≤ C := by
  obtain ⟨δ0, hδ0_pos, hδ0_4, hη0, C_phi, hCphi_pos, hS4b⟩ := outerS4b
  obtain ⟨C_A, hCA_pos, hA⟩ := norm_logDeriv_one_add_zetaD_sq_sq_le
  obtain ⟨C_B, hCB_pos, hB⟩ := norm_logDeriv_R4cStrip_le
  obtain ⟨C_lg, hClg_pos, hlg⟩ := norm_deriv_logGhatRefl_le
  refine ⟨δ0, C_A + C_B + C_lg + 2 * C_phi, hδ0_pos, hδ0_4, hη0, by positivity,
    fun δ hδ0 hδ1 b hb => ?_⟩
  have hδ4 : δ < 1 / 4 := lt_trans hδ1 hδ0_4
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_16_sub_quarter hb
  have heq := logDeriv_EsmExt_eq_on hδ0 hδ4
  have hev : logDeriv (EsmExt δ) =ᶠ[nhds b]
      (fun w => logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) w - logDeriv R4cStrip w -
        deriv logGhatRefl w - deriv (DeltaPhi δ) w) :=
    Filter.eventuallyEq_of_mem (isOpen_bandUpper_16.mem_nhds hb) heq
  have hval : logDeriv (EsmExt δ) b =
      logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) b - logDeriv R4cStrip b -
        deriv logGhatRefl b - deriv (DeltaPhi δ) b := heq hb
  have h8_open : IsOpen (bandUpper (1 / 8)) :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hb8 : b ∈ bandUpper (1 / 8) := bandUpper_16_sub_8 hb
  have hb_strip : b ∈ imStrip := bandUpper_16_sub_imStrip hb
  have hzd_an : AnalyticOnNhd ℂ zetaD (bandUpper (1 / 16)) :=
    (differentiableOn_zetaD_imStrip.mono bandUpper_16_sub_imStrip).analyticOnNhd isOpen_bandUpper_16
  have hA_an : AnalyticOnNhd ℂ (fun w => (1 + zetaD w ^ 2) ^ 2) (bandUpper (1 / 16)) :=
    fun w hw => ((analyticAt_const.add ((hzd_an w hw).pow 2)).pow 2)
  have hB_an : AnalyticOnNhd ℂ R4cStrip (bandUpper (1 / 16)) :=
    (differentiableOn_R4cStrip.mono bandUpper_16_sub_quarter).analyticOnNhd isOpen_bandUpper_16
  have hA_ne : ∀ w ∈ bandUpper (1 / 16), (1 + zetaD w ^ 2) ^ 2 ≠ 0 := fun w hw => by
    obtain ⟨c1, _, hc1_pos, h1sq⟩ := norm_one_add_zetaD_sq_sq_bounds
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (h1sq w hw).1)
  have hB_ne : ∀ w ∈ bandUpper (1 / 16), R4cStrip w ≠ 0 := fun w hw =>
    R4cStrip_ne_zero (bandUpper_16_sub_quarter hw)
  have hd_lA : DifferentiableAt ℂ (logDeriv (fun w => (1 + zetaD w ^ 2) ^ 2)) b := by
    have : DifferentiableOn ℂ (fun w => deriv (fun z => (1 + zetaD z ^ 2) ^ 2) w / (1 + zetaD w ^ 2) ^ 2)
        (bandUpper (1 / 16)) :=
      (hA_an.deriv.differentiableOn).div hA_an.differentiableOn hA_ne
    exact (this.congr (fun w _ => logDeriv_apply _ w)).differentiableAt (isOpen_bandUpper_16.mem_nhds hb)
  have hd_lB : DifferentiableAt ℂ (logDeriv R4cStrip) b := by
    have : DifferentiableOn ℂ (fun w => deriv R4cStrip w / R4cStrip w) (bandUpper (1 / 16)) :=
      (hB_an.deriv.differentiableOn).div hB_an.differentiableOn hB_ne
    exact (this.congr (fun w _ => logDeriv_apply _ w)).differentiableAt (isOpen_bandUpper_16.mem_nhds hb)
  have hlg_an : AnalyticOnNhd ℂ logGhatRefl (bandUpper (1 / 16)) :=
    (differentiableOn_logGhatRefl.mono bandUpper_16_sub_8).analyticOnNhd isOpen_bandUpper_16
  have hd_lg : DifferentiableAt ℂ (deriv logGhatRefl) b :=
    hlg_an.deriv.differentiableOn.differentiableAt (isOpen_bandUpper_16.mem_nhds hb)
  have hdp_an : AnalyticOnNhd ℂ (DeltaPhi δ) (bandUpper (1 / 16)) :=
    ((differentiableOn_DeltaPhi_imStrip hδ0 hδ4).mono bandUpper_16_sub_imStrip).analyticOnNhd
      isOpen_bandUpper_16
  have hd_dp : DifferentiableAt ℂ (deriv (DeltaPhi δ)) b :=
    hdp_an.deriv.differentiableOn.differentiableAt (isOpen_bandUpper_16.mem_nhds hb)
  have hderiv : deriv (logDeriv (EsmExt δ)) b =
      deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b - deriv (logDeriv R4cStrip) b -
        deriv (deriv logGhatRefl) b - deriv (deriv (DeltaPhi δ)) b := by
    have hd_all := ((hd_lA.hasDerivAt.sub hd_lB.hasDerivAt).sub hd_lg.hasDerivAt).sub hd_dp.hasDerivAt
    have hd_eq : deriv (fun w => logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) w - logDeriv R4cStrip w -
        deriv logGhatRefl w - deriv (DeltaPhi δ) w) b =
        deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b - deriv (logDeriv R4cStrip) b -
          deriv (deriv logGhatRefl) b - deriv (deriv (DeltaPhi δ)) b := hd_all.deriv
    rw [hev.deriv_eq, hd_eq]
  have hn1 : ‖logDeriv (EsmExt δ) b‖ ≤
      ‖logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) b‖ + ‖logDeriv R4cStrip b‖ +
        ‖deriv logGhatRefl b‖ + ‖deriv (DeltaPhi δ) b‖ := by
    rw [hval]
    calc ‖logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) b - logDeriv R4cStrip b -
            deriv logGhatRefl b - deriv (DeltaPhi δ) b‖
        ≤ ‖logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) b - logDeriv R4cStrip b -
            deriv logGhatRefl b‖ + ‖deriv (DeltaPhi δ) b‖ := norm_sub_le _ _
      _ ≤ ‖logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) b - logDeriv R4cStrip b‖ +
            ‖deriv logGhatRefl b‖ + ‖deriv (DeltaPhi δ) b‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2) b‖ + ‖logDeriv R4cStrip b‖ +
            ‖deriv logGhatRefl b‖ + ‖deriv (DeltaPhi δ) b‖ := by gcongr; exact norm_sub_le _ _
  have hn2 : ‖deriv (logDeriv (EsmExt δ)) b‖ ≤
      ‖deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b‖ + ‖deriv (logDeriv R4cStrip) b‖ +
        ‖deriv (deriv logGhatRefl) b‖ + ‖deriv (deriv (DeltaPhi δ)) b‖ := by
    rw [hderiv]
    calc ‖deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b - deriv (logDeriv R4cStrip) b -
            deriv (deriv logGhatRefl) b - deriv (deriv (DeltaPhi δ)) b‖
        ≤ ‖deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b - deriv (logDeriv R4cStrip) b -
            deriv (deriv logGhatRefl) b‖ + ‖deriv (deriv (DeltaPhi δ)) b‖ := norm_sub_le _ _
      _ ≤ ‖deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b - deriv (logDeriv R4cStrip) b‖ +
            ‖deriv (deriv logGhatRefl) b‖ + ‖deriv (deriv (DeltaPhi δ)) b‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖deriv (logDeriv (fun z => (1 + zetaD z ^ 2) ^ 2)) b‖ + ‖deriv (logDeriv R4cStrip) b‖ +
            ‖deriv (deriv logGhatRefl) b‖ + ‖deriv (deriv (DeltaPhi δ)) b‖ := by
          gcongr; exact norm_sub_le _ _
  have hA_b := hA b hb
  have hB_b := hB b hb
  have hlg_b := hlg b hb
  have hdp_b := (hS4b δ hδ0 hδ1).2.2 b hb_q
  linarith

/-! ### 3. Global strip bound on `EeExt δ` -/

private lemma norm_sub_I_half_le_add {b : ℂ} (hb : 0 < b.im) :
    ‖b - Complex.I / 2‖ ≤ ‖b + Complex.I / 2‖ := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.I_re, zero_div,
    sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.I_im]
  nlinarith

private lemma etaDelta_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4) : 0 < etaDelta δ := by
  unfold etaDelta
  refine div_pos (Real.arcsin_pos.mpr ?_) Real.pi_pos
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (by nlinarith)) (by nlinarith [sq_nonneg δ])

private lemma etaDelta_lt_sixteenth {δ : ℝ} (hδ0 : 0 < δ) (hδ40 : δ ≤ 1 / 40) :
    etaDelta δ < 1 / 16 := by
  have hpi := Real.pi_pos
  have hnum : √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) < 1 / 12 := by
    have hsqrt2 : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hden_ge : 3 / 2 ≤ 2 - 2 * δ + δ ^ 2 := by nlinarith [sq_nonneg δ]
    rw [div_lt_iff₀ (by linarith)]
    have h1 : √2 * (2 * δ - δ ^ 2) ≤ (3 / 2) * (2 * δ) :=
      mul_le_mul hsqrt2.le (by linarith [sq_nonneg δ]) (by nlinarith) (by norm_num)
    linarith only [h1, hden_ge, hδ40]
  have hsin16 : 1 / 12 ≤ Real.sin (π / 16) := by
    have hmono : MonotoneOn (fun y : ℝ => Real.sin y - y / 2) (Icc 0 (π / 3)) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 3))
        (Real.continuous_sin.sub (continuous_id.div_const 2)).continuousOn
        (fun y _ => ((Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).div_const 2)).differentiableAt.differentiableWithinAt)
        (fun y hy => by
          have hy' := interior_subset hy
          have hd : HasDerivAt (fun z : ℝ => Real.sin z - z / 2) (Real.cos y - 1 / 2) y :=
            (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).div_const 2)
          rw [hd.deriv]
          have hcos : 1 / 2 ≤ Real.cos y := by
            rw [← Real.cos_pi_div_three]
            exact Real.cos_le_cos_of_nonneg_of_le_pi hy'.1 (by linarith) hy'.2
          linarith)
    have h1 := hmono ⟨le_rfl, by positivity⟩ ⟨by positivity, by linarith⟩ (by positivity : (0 : ℝ) ≤ π / 16)
    simp only [Real.sin_zero, zero_div, sub_zero] at h1
    linarith [Real.pi_gt_three]
  have harcsin : Real.arcsin (√2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2)) < π / 16 := by
    rw [← Real.arcsin_sin (by linarith : -(π / 2) ≤ π / 16) (by linarith)]
    have hnn : 0 ≤ √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) :=
      div_nonneg (mul_nonneg (Real.sqrt_pos.mpr (by norm_num)).le (by nlinarith)) (by nlinarith [sq_nonneg δ])
    exact Real.arcsin_lt_arcsin (by linarith) (hnum.trans_le hsin16) (Real.sin_le_one _)
  unfold etaDelta
  rw [div_lt_iff₀ hpi]; linarith

theorem norm_EeExt_strip_le :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ δ0 < 1 / 4 ∧ etaDelta δ0 < 1 / 16 ∧ 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∀ b : ℂ, |b.im| ≤ 1 / 2 + etaDelta δ / 2 →
          ‖EeExt δ b‖ ≤ C * (min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) + δ) ^ (-(1 : ℝ) / 2) *
            ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
  obtain ⟨C_est, hCest_pos, hEst⟩ := norm_Estripped_interior_le
  obtain ⟨δ0_e, C_esm, hδ0_pos, hδ0_4, _, hCesm_pos, hEsm⟩ := norm_EsmExt_bounds
  obtain ⟨c_bp, hcbp_pos, hbp⟩ := norm_one_sub_one_sub_delta_zetaD_ge
  set δ0 : ℝ := min (1 / 40) δ0_e
  have hδ0_p : 0 < δ0 := lt_min (by norm_num) hδ0_pos
  have hδ0_40 : δ0 ≤ 1 / 40 := min_le_left _ _
  have hδ0_lt4 : δ0 < 1 / 4 := lt_of_le_of_lt hδ0_40 (by norm_num)
  have hη0 : etaDelta δ0 < 1 / 16 := etaDelta_lt_sixteenth hδ0_p hδ0_40
  set C_glob : ℝ := max (C_est * √2) (C_esm / √c_bp)
  have hCglob_pos : 0 < C_glob := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hpos_half : ∀ δ : ℝ, 0 < δ → δ < δ0 → ∀ b : ℂ, 0 < b.im → b.im ≤ 1 / 2 + etaDelta δ / 2 →
      ‖EeExt δ b‖ ≤ C_glob * (min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) + δ) ^ (-(1 : ℝ) / 2) *
        ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
    intro δ hδ0 hδ1 b hb0 hb_hi
    have hδ40 : δ < 1 / 40 := lt_of_lt_of_le hδ1 hδ0_40
    have hδ_e : δ < δ0_e := lt_of_lt_of_le hδ1 (min_le_right _ _)
    have hδ4 : δ < 1 / 4 := lt_trans hδ40 (by norm_num)
    have hδ10 : δ < 1 / 10 := lt_trans hδ40 (by norm_num)
    have hη_lt : etaDelta δ < 1 / 16 := etaDelta_lt_sixteenth hδ0 hδ40.le
    set m : ℝ := min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) + δ
    have hm_pos : 0 < m := by
      have : 0 ≤ min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) :=
        le_min zero_le_one (le_min (norm_nonneg _) (norm_nonneg _))
      linarith
    rcases le_or_gt b.im (7 / 16) with hb7 | hb7
    · have hbim_half : b.im < 1 / 2 := by linarith
      have hEe : EeExt δ b = Estripped δ b :=
        EeExt_eq_Estripped hδ0 hδ4 hb0 hbim_half
      rw [hEe]
      have hm_le2 : m ≤ 2 := by
        have h1 : min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) ≤ 1 := min_le_left _ _
        dsimp only [m]; linarith
      have hrp_ge : (√2)⁻¹ ≤ m ^ (-(1 : ℝ) / 2) := by
        rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg hm_pos.le,
          ← Real.sqrt_eq_rpow, inv_le_inv₀ (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr hm_pos)]
        exact Real.sqrt_le_sqrt hm_le2
      have hC_ge : C_est ≤ C_glob * m ^ (-(1 : ℝ) / 2) := by
        calc C_est = (C_est * √2) * (√2)⁻¹ := by
              have hne : √2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
              field_simp
          _ ≤ C_glob * (√2)⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ C_glob * m ^ (-(1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hrp_ge hCglob_pos.le
      calc ‖Estripped δ b‖
          ≤ C_est * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := hEst δ hδ0 hδ40 b hb0 hb7
        _ ≤ (C_glob * m ^ (-(1 : ℝ) / 2)) * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
            gcongr
        _ = C_glob * m ^ (-(1 : ℝ) / 2) * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by ring
    · have hb_band : b ∈ bandUpper (1 / 16) := by
        change |b.im - 1 / 2| < 1 / 16
        rw [abs_lt]; constructor <;> linarith
      have hη_pos : 0 < etaDelta δ := etaDelta_pos hδ0 hδ4
      have hb_lt_eta : b.im < 1 / 2 + etaDelta δ := by linarith
      have hfac := (EeExt_factor_EsmExt hδ0 hδ10).2.2 b hb_band hb_lt_eta
      have hesm := (hEsm δ hδ0 hδ_e b hb_band).2
      have hbp_lo := hbp δ hδ0 hδ40 b hb7 hb_hi
      have hmin_eq : min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖ = ‖b - Complex.I / 2‖ :=
        min_eq_left (norm_sub_I_half_le_add hb0)
      have hbp_m : c_bp * m ≤ ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
        dsimp only [m]; rw [hmin_eq]; exact hbp_lo
      have hbp_pos : 0 < ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ :=
        lt_of_lt_of_le (mul_pos hcbp_pos hm_pos) hbp_m
      have hpow_le : ‖(1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ))‖ ≤ (c_bp * m) ^ (-(1 : ℝ) / 2) := by
        have hne : 1 - ((1 - δ : ℝ) : ℂ) * zetaD b ≠ 0 := norm_pos_iff.mp hbp_pos
        rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp]
        have hre_p : (Complex.log (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) * (-(1 / 2 : ℂ))).re =
            -(1 / 2 : ℝ) * Real.log ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ := by
          simp [Complex.mul_re, Complex.log_re]; ring
        rw [hre_p, show -(1 / 2 : ℝ) * Real.log ‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ =
          Real.log (‖1 - ((1 - δ : ℝ) : ℂ) * zetaD b‖ ^ (-(1 / 2 : ℝ))) by
          rw [Real.log_rpow hbp_pos], Real.exp_log (Real.rpow_pos_of_pos hbp_pos _)]
        rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring]
        exact Real.rpow_le_rpow_of_nonpos (mul_pos hcbp_pos hm_pos) hbp_m (by norm_num)
      have hcm_eq : (c_bp * m) ^ (-(1 : ℝ) / 2) = (√c_bp)⁻¹ * m ^ (-(1 : ℝ) / 2) := by
        rw [Real.mul_rpow hcbp_pos.le hm_pos.le, show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
          Real.rpow_neg hcbp_pos.le, Real.sqrt_eq_rpow]
      have hC_ge : (√c_bp)⁻¹ * C_esm ≤ C_glob := by
        calc (√c_bp)⁻¹ * C_esm = C_esm / √c_bp := by ring
          _ ≤ C_glob := le_max_right _ _
      rw [hfac, norm_mul]
      calc ‖(1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ))‖ * ‖EsmExt δ b‖
          ≤ ((√c_bp)⁻¹ * m ^ (-(1 : ℝ) / 2)) *
              (C_esm * ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|)))) := by
            rw [← hcm_eq]
            exact mul_le_mul hpow_le hesm (norm_nonneg _) (by positivity)
        _ = ((√c_bp)⁻¹ * C_esm) * m ^ (-(1 : ℝ) / 2) *
              ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by ring
        _ ≤ C_glob * m ^ (-(1 : ℝ) / 2) *
              ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
            gcongr
  refine ⟨δ0, C_glob, hδ0_p, hδ0_lt4, hη0, hCglob_pos, fun δ hδ0 hδ1 b hb => ?_⟩
  have hδ40 : δ < 1 / 40 := lt_of_lt_of_le hδ1 hδ0_40
  have hδ4 : δ < 1 / 4 := lt_trans hδ40 (by norm_num)
  have hδ10 : δ < 1 / 10 := lt_trans hδ40 (by norm_num)
  rcases lt_trichotomy 0 b.im with hb0 | hb0 | hb0
  · exact hpos_half δ hδ0 hδ1 b hb0 (le_trans (le_abs_self _) hb)
  · -- b.im = 0: limit from above along b + I * ε
    have hη_pos : 0 < etaDelta δ := etaDelta_pos hδ0 hδ4
    have hcont_E : ContinuousAt (fun t : ℝ => ‖EeExt δ (b + (t : ℂ) * Complex.I)‖) 0 := by
      have hmem : {w : ℂ | |w.im| < 1 / 2 + etaDelta δ} ∈ nhds b :=
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds
          (by change |b.im| < 1 / 2 + etaDelta δ; rw [← hb0, abs_zero]; linarith)
      have hc : ContinuousAt (EeExt δ) b :=
        ((differentiableOn_EeExt hδ0 hδ10).continuousOn.continuousAt hmem)
      have hcont_t : ContinuousAt (fun t : ℝ => b + (t : ℂ) * Complex.I) 0 :=
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
      have h0 : b + ((0 : ℝ) : ℂ) * Complex.I = b := by simp
      have hc0 : ContinuousAt (EeExt δ) (b + ((0 : ℝ) : ℂ) * Complex.I) := by rw [h0]; exact hc
      exact (ContinuousAt.comp (f := fun t : ℝ => b + (t : ℂ) * Complex.I) (g := EeExt δ) hc0 hcont_t).norm
    have hcont_rhs : ContinuousAt
        (fun t : ℝ => C_glob * (min 1 (min ‖(b + (t : ℂ) * Complex.I) - Complex.I / 2‖
          ‖(b + (t : ℂ) * Complex.I) + Complex.I / 2‖) + δ) ^ (-(1 : ℝ) / 2) *
          ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|)))) 0 := by
      have hbase_pos : 0 < min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) + δ := by
        have : 0 ≤ min 1 (min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖) :=
          le_min zero_le_one (le_min (norm_nonneg _) (norm_nonneg _))
        linarith
      have hbase_cont : Continuous (fun t : ℝ => min 1 (min ‖(b + (t : ℂ) * Complex.I) - Complex.I / 2‖
          ‖(b + (t : ℂ) * Complex.I) + Complex.I / 2‖) + δ) := by
        refine Continuous.add (continuous_const.min (Continuous.min ?_ ?_)) continuous_const
        · exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).norm
        · exact ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).add continuous_const).norm
      have hrp : ContinuousAt (fun t : ℝ => (min 1 (min ‖(b + (t : ℂ) * Complex.I) - Complex.I / 2‖
          ‖(b + (t : ℂ) * Complex.I) + Complex.I / 2‖) + δ) ^ (-(1 : ℝ) / 2)) 0 :=
        hbase_cont.continuousAt.rpow continuousAt_const (Or.inl (by simpa using hbase_pos.ne'))
      exact (continuousAt_const.mul hrp).mul continuousAt_const
    have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
        ‖EeExt δ (b + (t : ℂ) * Complex.I)‖ ≤
          C_glob * (min 1 (min ‖(b + (t : ℂ) * Complex.I) - Complex.I / 2‖
            ‖(b + (t : ℂ) * Complex.I) + Complex.I / 2‖) + δ) ^ (-(1 : ℝ) / 2) *
            ((1 + |b.re|) ^ (-(1 : ℝ) / 2) * Real.exp (-(2 * π * |b.re|))) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with t ht
      have hre : (b + (t : ℂ) * Complex.I).re = b.re := by simp
      have him : (b + (t : ℂ) * Complex.I).im = t := by simp [← hb0]
      have hbd := hpos_half δ hδ0 hδ1 (b + (t : ℂ) * Complex.I) (by rw [him]; exact ht.1)
        (by rw [him]; linarith [ht.2])
      simpa [hre] using hbd
    have hres := le_of_tendsto_of_tendsto hcont_E.continuousWithinAt hcont_rhs.continuousWithinAt hev
    simpa using hres
  · -- b.im < 0: use evenness EeExt δ (-b) = EeExt δ b
    have hneg : (-b).im > 0 := by simp [hb0]
    have hneg_hi : (-b).im ≤ 1 / 2 + etaDelta δ / 2 := by
      have : |b.im| = -b.im := abs_of_neg hb0
      simpa [this] using hb
    have hbd := hpos_half δ hδ0 hδ1 (-b) hneg hneg_hi
    have heven := EeExt_neg hδ0 hδ4 b
    have hmin : min ‖(-b) - Complex.I / 2‖ ‖(-b) + Complex.I / 2‖ =
        min ‖b - Complex.I / 2‖ ‖b + Complex.I / 2‖ := by
      have h1 : ‖(-b) - Complex.I / 2‖ = ‖b + Complex.I / 2‖ := by
        rw [show (-b) - Complex.I / 2 = -(b + Complex.I / 2) by ring, norm_neg]
      have h2 : ‖(-b) + Complex.I / 2‖ = ‖b - Complex.I / 2‖ := by
        rw [show (-b) + Complex.I / 2 = -(b - Complex.I / 2) by ring, norm_neg]
      rw [h1, h2, min_comm]
    simpa [heven, hmin, abs_neg] using hbd

/-! ### 4. Upper-edge identity on `E_+` -/

theorem norm_EeExt_upper_edge :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 / 4 ∧ etaDelta δ0 < 1 / 16 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 → ∀ x : ℝ, xiStar < x →
        ‖EeExt δ ((vOf (yOfX x) : ℂ) + Complex.I / 2)‖ =
          ‖fDelta Gout δ (starRingEnd ℂ (wPt (yOfX x)))‖ := by
  obtain ⟨δ0_4b, hδ0_pos, hδ0_4, hη0, _, _, hS4b⟩ := outerS4b
  set δ0 : ℝ := min (1 / 40) δ0_4b
  have hδ0_p : 0 < δ0 := lt_min (by norm_num) hδ0_pos
  have hδ0_40 : δ0 ≤ 1 / 40 := min_le_left _ _
  have hδ0_lt4 : δ0 < 1 / 4 := lt_of_le_of_lt hδ0_40 (by norm_num)
  refine ⟨δ0, hδ0_p, hδ0_lt4, etaDelta_lt_sixteenth hδ0_p hδ0_40, fun δ hδ0 hδ1 x hx => ?_⟩
  have hδ40 : δ < 1 / 40 := lt_of_lt_of_le hδ1 hδ0_40
  have hδ_4b : δ < δ0_4b := lt_of_lt_of_le hδ1 (min_le_right _ _)
  have hδ4 : δ < 1 / 4 := lt_trans hδ40 (by norm_num)
  have hδ10 : δ < 1 / 10 := lt_trans hδ40 (by norm_num)
  have hy := yOfX_mem hx
  set y : ℝ := yOfX x
  set b : ℂ := (vOf y : ℂ) + Complex.I / 2
  set z : ℂ := starRingEnd ℂ (wPt y)
  have hzb : zetaD b = z := zetaD_edge_eq_conj_wPt hy
  have hb_band : b ∈ bandUpper (1 / 16) := by
    change |b.im - 1 / 2| < 1 / 16; simp [b]
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_16_sub_quarter hb_band
  have hη_pos : 0 < etaDelta δ := etaDelta_pos hδ0 hδ4
  have hb_lt : b.im < 1 / 2 + etaDelta δ := by simp [b]; linarith
  have hfac := (EeExt_factor_EsmExt hδ0 hδ10).2.2 b hb_band hb_lt
  have hlg : logGhatRefl b = logGhatLower b := logGhatRefl_eq_lower (by simp [b])
  have hre_lg : (logGhatLower b).re = (uE (vOf y : ℂ)).re := re_logGhatLower_edge (vOf y)
  have hre_uE := re_uE_eq_log_norm_Ghat hy
  have hre_dp : (DeltaPhi δ b).re = 0 := (hS4b δ hδ0 hδ_4b).2.1 (vOf y)
  have hnorm_dp : ‖Complex.exp (-DeltaPhi δ b)‖ = 1 := by
    rw [Complex.norm_exp, Complex.neg_re, hre_dp, neg_zero, Real.exp_zero]
  have hnorm_w : ‖wPt y‖ = 1 := by
    have hsq : ‖wPt y‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, re_wPt, im_wPt]
      have hden : 1 + y ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    nlinarith [norm_nonneg (wPt y)]
  have hnorm_z : ‖z‖ = 1 := by simpa [z] using hnorm_w
  have hz_im_neg : z.im < 0 := by
    dsimp only [z]
    rw [Complex.conj_im, im_wPt]
    have : 0 < 2 * y / (1 + y ^ 2) := div_pos (by linarith [hy.1]) (by positivity)
    linarith
  have hz_ne_one : z ≠ 1 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hz_sing : z ∈ closure halfDisc \ singPts := by
    have hcl := zetaD_edge_mem_closure (vOf y)
    rw [hzb] at hcl
    refine ⟨hcl.1, fun h => ?_⟩
    simp only [singPts, mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h
    · exact hcl.2 (by simp [h])
    · exact hcl.2 (by simp [h])
    · exact hz_ne_one h
  have h1sub_ne : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne_one.symm
  have h1dz_ne : 1 - ((1 - δ : ℝ) : ℂ) * z ≠ 0 := by
    intro h
    have h1 : ‖((1 - δ : ℝ) : ℂ) * z‖ = 1 - δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hnorm_z, mul_one]
    have h2 : ((1 - δ : ℝ) : ℂ) * z = 1 := sub_eq_zero.mp h |>.symm
    rw [h2, norm_one] at h1
    linarith
  have h1z2_ne : 1 + z ^ 2 ≠ 0 := by
    have hz_re_pos : 0 < z.re := by
      dsimp only [z]; rw [Complex.conj_re, re_wPt]
      exact div_pos (by nlinarith [hy.1, hy.2]) (by positivity)
    intro h
    have hsq : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right h
    have hre := congrArg Complex.re hsq
    simp only [sq, Complex.mul_re, Complex.neg_re, Complex.one_re] at hre
    have hns : z.re ^ 2 + z.im ^ 2 = 1 := by
      have := Complex.sq_norm z
      rw [Complex.normSq_apply, hnorm_z, one_pow] at this
      linarith
    nlinarith [sq_nonneg z.re, hz_re_pos]
  have hR4_ne : R4cStrip b ≠ 0 := R4cStrip_ne_zero hb_q
  have hG_ne : Gout z ≠ 0 := by
    have hfs := fStar_ne_zero gout_outerDatum_g1Out hz_sing
    unfold fStar at hfs
    intro h0; rw [h0, div_zero] at hfs; exact hfs rfl
  have hm_ne : (1 - z) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h1sub_ne]; exact Complex.exp_ne_zero _
  have hghat_pos : 0 < ‖(1 - z) ^ (-(1 / 2 : ℂ)) * ((1 + z ^ 2) * Gout z / R4cStrip b)‖ := by
    rw [norm_mul, norm_div, norm_mul]
    exact mul_pos (norm_pos_iff.mpr hm_ne) (div_pos (mul_pos (norm_pos_iff.mpr h1z2_ne) (norm_pos_iff.mpr hG_ne)) (norm_pos_iff.mpr hR4_ne))
  have hnorm_lg : ‖Complex.exp (logGhatRefl b)‖ =
      ‖(1 - z) ^ (-(1 / 2 : ℂ)) * ((1 + z ^ 2) * Gout z / R4cStrip b)‖ := by
    rw [hlg, Complex.norm_exp, hre_lg, hre_uE, Real.exp_log hghat_pos]
  have hmEps_eq : mEps δ z = ((1 - z) ^ (-(1 / 2 : ℂ)))⁻¹ * (1 - ((1 - δ : ℝ) : ℂ) * z) ^ (-(1 / 2 : ℂ)) := by
    unfold mEps
    rw [mul_sub, Complex.exp_sub, Complex.cpow_def_of_ne_zero h1sub_ne, Complex.cpow_def_of_ne_zero h1dz_ne,
      div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_neg]
    congr 2 <;> ring
  have hf_norm : ‖fDelta Gout δ z‖ =
      ‖(1 - ((1 - δ : ℝ) : ℂ) * z) ^ (-(1 / 2 : ℂ))‖ * ‖1 + z ^ 2‖ /
        (‖(1 - z) ^ (-(1 / 2 : ℂ))‖ * ‖Gout z‖) := by
    unfold fDelta fStar
    rw [hmEps_eq, norm_mul, norm_mul, norm_div, norm_inv]
    field_simp [norm_pos_iff.mpr hm_ne, norm_pos_iff.mpr hG_ne]
  rw [hfac]
  unfold EsmExt
  rw [norm_mul, norm_mul, norm_div, norm_mul, hnorm_dp, mul_one, hnorm_lg, hzb,
    norm_mul, norm_div, norm_mul, norm_pow]
  field_simp [norm_pos_iff.mpr hR4_ne, norm_pos_iff.mpr hm_ne, norm_pos_iff.mpr hG_ne,
    norm_pos_iff.mpr h1z2_ne]
  rw [hf_norm]
  field_simp [norm_pos_iff.mpr hm_ne, norm_pos_iff.mpr hG_ne]

/-! ### 5. Assembly of `OuterS3` and `OuterS4` -/

theorem outerS4 : OuterS4 := ⟨outerS4a, outerS4b⟩

theorem outerS3 : OuterS3 := by
  obtain ⟨δ0_1, C1, hδ1_p, _, _, hC1_p, hEsm⟩ := norm_EsmExt_bounds
  obtain ⟨δ0_2, C2, hδ2_p, _, _, hC2_p, hLD⟩ := norm_logDeriv_EsmExt_le
  obtain ⟨δ0_3, C3, hδ3_p, _, _, hC3_p, hStrip⟩ := norm_EeExt_strip_le
  obtain ⟨δ0_4, hδ4_p, _, _, hEdge⟩ := norm_EeExt_upper_edge
  set δ0 : ℝ := min (1 / 40) (min δ0_1 (min δ0_2 (min δ0_3 δ0_4)))
  have hδ0_p : 0 < δ0 := lt_min (by norm_num) (lt_min hδ1_p (lt_min hδ2_p (lt_min hδ3_p hδ4_p)))
  have hδ0_40 : δ0 ≤ 1 / 40 := min_le_left _ _
  have hδ0_4 : δ0 < 1 / 4 := lt_of_le_of_lt hδ0_40 (by norm_num)
  have hη0 : etaDelta δ0 < 1 / 16 := etaDelta_lt_sixteenth hδ0_p hδ0_40
  set C : ℝ := max C1 (max C2 C3)
  have hC_p : 0 < C := lt_of_lt_of_le hC1_p (le_max_left _ _)
  refine ⟨δ0, hδ0_p, hδ0_4, hη0, C, hC_p, fun δ hδ0 hδ => ?_⟩
  have hδ1 : δ < δ0_1 := lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_left _ _))
  have hδ2 : δ < δ0_2 := lt_of_lt_of_le hδ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ3 : δ < δ0_3 := lt_of_lt_of_le hδ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδ4 : δ < δ0_4 := lt_of_lt_of_le hδ ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδ_lt4 : δ < 1 / 4 := lt_trans hδ hδ0_4
  have hδ_lt10 : δ < 1 / 10 := lt_trans hδ (lt_of_le_of_lt hδ0_40 (by norm_num))
  have hfac := EeExt_factor_EsmExt hδ0 hδ_lt10
  refine ⟨EeExt δ, EsmExt δ,
    differentiableOn_EeExt hδ0 hδ_lt10,
    fun b hb => EeExt_ne_zero hδ0 hδ_lt10 hb,
    fun b => EeExt_neg hδ0 hδ_lt4 b,
    fun x => EeExt_real_pos hδ0 hδ_lt4 x,
    fun b hb0 hb_half _ => EeExt_eq_Estripped hδ0 hδ_lt4 hb0 (abs_lt.mp hb_half).2,
    hfac.1, hfac.2.1,
    fun b hb => ?_,
    fun b hb => ?_,
    fun b hb => (hLD δ hδ0 hδ2 b hb).trans (le_trans (le_max_left _ _) (le_max_right _ _)),
    fun b hb => ?_,
    fun x hx => EeExt_modulus_identity hδ0 hδ_lt4 hx,
    fun x hx => hEdge δ hδ0 hδ4 x hx⟩
  · by_cases hlt : b.im < 1 / 2 + etaDelta δ
    · exact hfac.2.2 b hb hlt
    · have hbm : 1 / 2 < b.im := by linarith [etaDelta_pos hδ0 hδ_lt4]
      have hmid : ¬ |b.im| < 1 / 2 := fun h => absurd (abs_lt.mp h).2 hbm.not_gt
      have hb0 : 0 < b.im := by linarith
      unfold EeExt
      rw [ite_eq_right_iff.mpr (fun h => absurd h hmid), ite_eq_left_iff.mpr (fun h => absurd hb0 h)]
      rfl
  · obtain ⟨hlo, hhi⟩ := hEsm δ hδ0 hδ1 b hb
    have hC1_le : C1 ≤ C := le_max_left _ _
    have hC_inv : C⁻¹ ≤ C1⁻¹ := inv_anti₀ hC1_p hC1_le
    refine ⟨(mul_le_mul_of_nonneg_right hC_inv (by positivity)).trans hlo,
      hhi.trans (mul_le_mul_of_nonneg_right hC1_le (by positivity))⟩
  · have hC3_le : C3 ≤ C := (le_max_right C2 C3).trans (le_max_right C1 _)
    exact (hStrip δ hδ0 hδ3 b hb).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC3_le (by positivity)) (by positivity))

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_EsmExt_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_EsmExt_bounds

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_logDeriv_EsmExt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_logDeriv_EsmExt_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_EeExt_strip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_EeExt_strip_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_EeExt_upper_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_EeExt_upper_edge

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS4

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS3
