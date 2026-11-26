module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3UE
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3Ee
public import FormalResearch.Complex.SchwarzReflection

/-!
# FIVE-S, S3 (step 3b): extension of `Ee` across `E_+` to `{|Im b| < 1/2 + η_δ}`

Completes Step 3 of `OuterS3` (`cts:smooth-env` (2)) for `δ ∈ (0, 1/10)` (so `η_δ < 1/16 < 1/8`):

* Defines `logGhatLower` on `bandUpper (1/8) ∩ {b | b.im ≤ 1/2}`, proves it is continuous there,
  holomorphic on `{b.im < 1/2}`, satisfies `exp (logGhatLower b) = (1 - ζ_D b)^{-1/2} G̃(ζ_D b)`,
  and has real part `(uE v).re` on `E_+ = {b = v + i/2}`.
* Applies `schwarzReflection_prescribed_re` across `Im w = 0` to extend `log Ĝ ∘ ζ_D` holomorphically
  to `bandUpper (1/8)` (`logGhatRefl`).
* Defines `EsmExt δ` (holomorphic and zero-free on `bandUpper (1/8)`) and glues
  `EeUpper δ b = (1 - (1 - δ) ζ_D b)^{-1/2} EsmExt δ b` with `Ee δ` from `OuterS3Ee` to obtain
  `EeExt δ : ℂ → ℂ`, even, holomorphic, and zero-free on `{|Im b| < 1/2 + η_δ}`, real and positive
  on `ℝ`, agreeing with `Estripped δ` on `0 < Im b < 1/2`, and satisfying the slit modulus identity.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.Complex
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-! ### 1. Explicit logarithm `logGhatLower` on `bandUpper (1/8) ∩ {b | b.im ≤ 1/2}` -/

/-- Explicit logarithm of `Ĝ(ζ_D(b)) = (1 - ζ_D(b))^{-1/2} G̃(ζ_D(b))` on `bandUpper (1/8) ∩ {Im b ≤ 1/2}`. -/
noncomputable def logGhatLower (b : ℂ) : ℂ :=
  hbarA aAmp (sInv (zetaD b)) +
    Complex.log (1 + zetaD b ^ 2) -
    2 * Complex.log (1 + zetaD b) -
    (1 / 4 : ℂ) * Complex.log (qBd (zetaD b)) -
    (1 / 2 : ℂ) * Complex.log ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) -
    (1 / 2 : ℂ) * Complex.log ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) +
    Complex.log (kap : ℂ)

private lemma bandUpper_eighth_subset_quarter : bandUpper (1 / 8) ⊆ bandUpper (1 / 4) := fun b hb =>
  lt_trans (show |b.im - 1 / 2| < 1 / 8 from hb) (by norm_num)

private lemma bandUpper_eighth_subset_imStrip : bandUpper (1 / 8) ⊆ imStrip := fun b hb =>
  ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 8 from hb)).1],
    by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 8 from hb)).2]⟩

private lemma zetaD_mem_closure_of_le_half {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im ≤ 1 / 2) :
    zetaD b ∈ closure halfDisc \ {Complex.I, -Complex.I} := by
  rcases lt_or_eq_of_le hb1 with hlt | heq
  · have hhd := zetaD_mem_halfDisc hb0 hlt
    exact ⟨subset_closure hhd, fun h => by
      simp only [mem_insert_iff, mem_singleton_iff] at h
      obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hhd
      tauto⟩
  · have hb_eq : b = (b.re : ℂ) + Complex.I / 2 := by
      apply Complex.ext
      · simp
      · simp [heq]
    rw [hb_eq]
    exact zetaD_edge_mem_closure b.re

private lemma one_add_zetaD_sq_mem_slit_of_le_half {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im ≤ 1 / 2) :
    1 + zetaD b ^ 2 ∈ Complex.slitPlane := by
  have hb_strip : b ∈ imStrip := ⟨hb0, by linarith⟩
  rw [one_add_zetaD_sq_eq hb_strip, Complex.mem_slitPlane_iff]
  left
  have hpi := Real.pi_pos
  have hcos : 0 ≤ Real.cos (π * b.im) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hcre : 0 ≤ (Complex.cosh ((π : ℂ) * b)).re := by
    rw [re_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact mul_nonneg (Real.cosh_pos _).le hcos
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hre_den : 0 < ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hden_ne : (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 := by
    intro h; rw [h] at hre_den; simp at hre_den
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_mul, add_zero, zero_div]
  exact div_pos (mul_pos (by positivity) hre_den) (Complex.normSq_pos.mpr hden_ne)

private lemma continuousWithinAt_log_comp {f : ℂ → ℂ} {S : Set ℂ} {b : ℂ}
    (hf : ContinuousWithinAt f S b) (hslit : f b ∈ Complex.slitPlane) :
    ContinuousWithinAt (fun w => Complex.log (f w)) S b :=
  ContinuousAt.comp_continuousWithinAt (g := Complex.log) (f := f)
    (differentiableAt_id.clog hslit).continuousAt hf

private lemma continuousOn_logGhatLower :
    ContinuousOn logGhatLower (bandUpper (1 / 8) ∩ {b : ℂ | b.im ≤ 1 / 2}) := by
  set S : Set ℂ := bandUpper (1 / 8) ∩ {b : ℂ | b.im ≤ 1 / 2}
  have hS_strip : S ⊆ imStrip := fun b hb => bandUpper_eighth_subset_imStrip hb.1
  have hS_q : S ⊆ bandUpper (1 / 4) := fun b hb => bandUpper_eighth_subset_quarter hb.1
  have hzeta_cont : ContinuousOn zetaD S :=
    (differentiableOn_zetaD_imStrip.continuousOn).mono hS_strip
  have hzeta_mem : MapsTo zetaD S (closure halfDisc \ {Complex.I, -Complex.I}) :=
    fun b hb => zetaD_mem_closure_of_le_half (hS_strip hb).1 hb.2
  have h1 : ContinuousOn (fun b => hbarA aAmp (sInv (zetaD b))) S := by
    have hsInv : ContinuousOn (fun b => sInv (zetaD b)) S :=
      continuousOn_sInv.comp hzeta_cont hzeta_mem
    refine (continuousOn_hbarA amp_aAmp).comp hsInv fun b hb => ?_
    have hm := hzeta_mem hb
    exact sInv_mem_closedStrip hm.1 (ne_of_mem_diff hm).1 (ne_of_mem_diff hm).2
  have h2 : ContinuousOn (fun b => Complex.log (1 + zetaD b ^ 2)) S := by
    intro b hb
    exact continuousWithinAt_log_comp
      (continuousWithinAt_const.add ((hzeta_cont b hb).pow 2))
      (one_add_zetaD_sq_mem_slit_of_le_half (hS_strip hb).1 hb.2)
  have h3 : ContinuousOn (fun b => 2 * Complex.log (1 + zetaD b)) S := by
    refine continuousOn_const.mul fun b hb => ?_
    exact continuousWithinAt_log_comp
      (continuousWithinAt_const.add (hzeta_cont b hb))
      (one_add_mem_slit (hzeta_mem hb).1)
  have h4 : ContinuousOn (fun b => (1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) S := by
    refine continuousOn_const.mul fun b hb => ?_
    have hm := hzeta_mem hb
    exact continuousWithinAt_log_comp
      ((continuousOn_qBd (zetaD b) hm).comp (hzeta_cont b hb) hzeta_mem)
      (exists_qBd hm.1 (ne_of_mem_diff hm).1 (ne_of_mem_diff hm).2).1
  have h5 : ContinuousOn (fun b => (1 / 2 : ℂ) * Complex.log ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2))) S := by
    refine continuousOn_const.mul fun b hb => ?_
    have h1sq := one_add_zetaD_sq_ne_zero_imStrip (hS_strip hb)
    exact continuousWithinAt_log_comp
      (((continuousWithinAt_const.add (continuousWithinAt_const.mul (hzeta_cont b hb))).sub
        ((hzeta_cont b hb).pow 2)).div (continuousWithinAt_const.add ((hzeta_cont b hb).pow 2)) h1sq)
      (r4c_alg_factor_mem_slitPlane (hS_q hb))
  have h6 : ContinuousOn (fun b => (1 / 2 : ℂ) * Complex.log ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b))) S := by
    refine continuousOn_const.mul fun b hb => ?_
    have hslit := pi_mul_div_sinh_mem_slitPlane (hS_strip hb)
    have hsh_ne : Complex.sinh ((π : ℂ) * b) ≠ 0 := by
      intro h0; rw [h0, div_zero] at hslit; exact Complex.slitPlane_ne_zero hslit rfl
    exact continuousWithinAt_log_comp
      ((continuousWithinAt_const.mul continuousWithinAt_id).div
        (Complex.continuous_sinh.continuousAt.comp_continuousWithinAt
          (continuousWithinAt_const.mul continuousWithinAt_id)) hsh_ne)
      hslit
  unfold logGhatLower
  exact (((((h1.add h2).sub h3).sub h4).sub h5).sub h6).add continuousOn_const

private lemma differentiableOn_logGhatLower :
    DifferentiableOn ℂ logGhatLower (bandUpper (1 / 8) ∩ {b : ℂ | b.im < 1 / 2}) := by
  intro b hb
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb.1
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hb.1
  have hb_lt : b.im < 1 / 2 := hb.2
  have hzeta_hd : zetaD b ∈ halfDisc := zetaD_mem_halfDisc hb_strip.1 hb_lt
  have hzeta_diff : DifferentiableAt ℂ zetaD b :=
    differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have hcl : zetaD b ∈ closure halfDisc := subset_closure hzeta_hd
  obtain ⟨hpm1, hpm2⟩ := halfDisc_ne_pm_I hzeta_hd
  have hsInv_diff : DifferentiableAt ℂ sInv (zetaD b) := differentiableAt_sInv hcl hpm1 hpm2
  have h1 : DifferentiableAt ℂ (fun w => hbarA aAmp (sInv (zetaD w))) b :=
    DifferentiableAt.comp (g := hbarA aAmp) (f := fun w => sInv (zetaD w)) b
      (differentiableAt_hbarA_aAmp (sInv_mem_strip hzeta_hd)) (hsInv_diff.comp b hzeta_diff)
  have h2 : DifferentiableAt ℂ (fun w => Complex.log (1 + zetaD w ^ 2)) b :=
    ((differentiableAt_const _).add (hzeta_diff.pow 2)).clog
      (one_add_zetaD_sq_mem_slit_of_le_half hb_strip.1 hb_lt.le)
  have h3 : DifferentiableAt ℂ (fun w => 2 * Complex.log (1 + zetaD w)) b :=
    (differentiableAt_const _).mul (((differentiableAt_const _).add hzeta_diff).clog (one_add_mem_slit hcl))
  have h4 : DifferentiableAt ℂ (fun w => (1 / 4 : ℂ) * Complex.log (qBd (zetaD w))) b := by
    have hqB : DifferentiableAt ℂ qBd (zetaD b) := by
      refine (differentiableOn_qHat.differentiableAt (isOpen_halfDisc.mem_nhds hzeta_hd)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_halfDisc.mem_nhds hzeta_hd] with z hz using qBd_of_mem hz
    exact (differentiableAt_const _).mul ((hqB.comp b hzeta_diff).clog
      (by simp only [Function.comp_apply, qBd_of_mem hzeta_hd]; exact qHat_mem_slit hzeta_hd))
  have h5 : DifferentiableAt ℂ (fun w => (1 / 2 : ℂ) * Complex.log ((1 + 2 * zetaD w - zetaD w ^ 2) / (1 + zetaD w ^ 2))) b := by
    have h1sq := one_add_zetaD_sq_ne_zero_imStrip hb_strip
    exact (differentiableAt_const _).mul
      (((((differentiableAt_const _).add ((differentiableAt_const _).mul hzeta_diff)).sub (hzeta_diff.pow 2)).div
        ((differentiableAt_const _).add (hzeta_diff.pow 2)) h1sq).clog (r4c_alg_factor_mem_slitPlane hb_q))
  have h6 : DifferentiableAt ℂ (fun w => (1 / 2 : ℂ) * Complex.log ((π : ℂ) * w / Complex.sinh ((π : ℂ) * w))) b := by
    have hslit := pi_mul_div_sinh_mem_slitPlane hb_strip
    have hsh_ne : Complex.sinh ((π : ℂ) * b) ≠ 0 := by
      intro h0; rw [h0, div_zero] at hslit; exact Complex.slitPlane_ne_zero hslit rfl
    exact (differentiableAt_const _).mul
      ((((differentiableAt_const _).mul differentiableAt_id).div
        (Complex.differentiableAt_sinh.comp b ((differentiableAt_const _).mul differentiableAt_id)) hsh_ne).clog hslit)
  unfold logGhatLower
  exact ((((((h1.add h2).sub h3).sub h4).sub h5).sub h6).add (differentiableAt_const _)).differentiableWithinAt

private lemma exp_logGhatLower_eq {b : ℂ} (hb : b ∈ bandUpper (1 / 8)) (hb_lt : b.im < 1 / 2) :
    Complex.exp (logGhatLower b) = (1 - zetaD b) ^ (-(1 / 2 : ℂ)) * Gtilde R4c (zetaD b) := by
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hb
  have hzeta_hd : zetaD b ∈ halfDisc := zetaD_mem_halfDisc hb_strip.1 hb_lt
  have hcl : zetaD b ∈ closure halfDisc := subset_closure hzeta_hd
  have h1sq_ne : 1 + zetaD b ^ 2 ≠ 0 := one_add_zetaD_sq_ne_zero_imStrip hb_strip
  have h1z_ne : 1 + zetaD b ≠ 0 := one_add_ne_zero' hcl
  have hq_ne : qBd (zetaD b) ≠ 0 := qBd_ne_zero (halfDisc_mem_diff hzeta_hd)
  have hkap_ne : (kap : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr kap_pos.ne'
  have hr1_ne : (1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2) ≠ 0 :=
    Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hb_q)
  have hr2_ne : (π : ℂ) * b / Complex.sinh ((π : ℂ) * b) ≠ 0 :=
    Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hb_strip)
  have h1sub_ne : 1 - zetaD b ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mem_slit hcl (halfDisc_ne_special hzeta_hd).2.2)
  -- Expand exp(logGhatLower b):
  unfold logGhatLower
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_add]
  rw [Complex.exp_log h1sq_ne, Complex.exp_log hkap_ne]
  have he_1z : Complex.exp (2 * Complex.log (1 + zetaD b)) = (1 + zetaD b) ^ 2 := by
    rw [show (2 : ℂ) * Complex.log (1 + zetaD b) = Complex.log (1 + zetaD b) + Complex.log (1 + zetaD b) by ring,
      Complex.exp_add, Complex.exp_log h1z_ne, sq]
  have he_q : (Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))))⁻¹ = (qBd (zetaD b)) ^ (-(1 / 4 : ℂ)) := by
    rw [← Complex.exp_neg, Complex.cpow_def_of_ne_zero hq_ne]; congr 1; ring
  have he_r1 : Complex.exp ((1 / 2 : ℂ) * Complex.log ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2))) =
      ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hr1_ne]; congr 1; ring
  have he_r2 : Complex.exp ((1 / 2 : ℂ) * Complex.log ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b))) =
      ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hr2_ne]; congr 1; ring
  rw [he_1z, he_r1, he_r2]
  have hcancel : (1 - zetaD b) ^ (-(1 / 2 : ℂ)) * (1 - zetaD b) ^ (1 / 2 : ℂ) = 1 := by
    rw [Complex.cpow_def_of_ne_zero h1sub_ne, Complex.cpow_def_of_ne_zero h1sub_ne, ← Complex.exp_add]
    simp
  unfold Gtilde Gout
  rw [← R4cStrip_eq_R4c hb_q hb_lt]
  unfold R4cStrip
  have hR1_ne : ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hr1_ne]; exact Complex.exp_ne_zero _
  have hR2_ne : ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hr2_ne]; exact Complex.exp_ne_zero _
  have hq_exp_ne : Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) ≠ 0 := Complex.exp_ne_zero _
  have h1z2_ne : (1 + zetaD b) ^ 2 ≠ 0 := pow_ne_zero 2 h1z_ne
  rw [← he_q]
  have hprod : (1 - zetaD b) ^ (-(1 / 2 : ℂ)) *
      ((1 + zetaD b ^ 2) * (Complex.exp (hbarA aAmp (sInv (zetaD b))) * (1 - zetaD b) ^ (1 / 2 : ℂ) /
        (1 + zetaD b) ^ 2 * (Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))))⁻¹) /
        (((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) *
          ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) / (kap : ℂ))) =
      ((1 - zetaD b) ^ (-(1 / 2 : ℂ)) * (1 - zetaD b) ^ (1 / 2 : ℂ)) *
      (Complex.exp (hbarA aAmp (sInv (zetaD b))) * (1 + zetaD b ^ 2) / (1 + zetaD b) ^ 2 /
        Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) /
        ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) /
        ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) * (kap : ℂ)) := by
    field_simp
  rw [hprod, hcancel, one_mul]

private lemma exp_logGhatLower_edge_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Complex.exp (logGhatLower ((vOf y : ℂ) + Complex.I / 2)) =
      (1 - starRingEnd ℂ (wPt y)) ^ (-(1 / 2 : ℂ)) *
        ((1 + (starRingEnd ℂ (wPt y)) ^ 2) * Gout (starRingEnd ℂ (wPt y)) /
          R4cStrip ((vOf y : ℂ) + Complex.I / 2)) := by
  set b := (vOf y : ℂ) + Complex.I / 2
  have hb_strip : b ∈ imStrip := by simp [b, imStrip]; norm_num
  have hb_q : b ∈ bandUpper (1 / 4) := by
    change |b.im - 1 / 2| < 1 / 4; simp [b]
  have hzb : zetaD b = starRingEnd ℂ (wPt y) := zetaD_edge_eq_conj_wPt hy
  have hcl_diff : zetaD b ∈ closure halfDisc \ {Complex.I, -Complex.I} := zetaD_edge_mem_closure (vOf y)
  have hne1 : starRingEnd ℂ (wPt y) ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.conj_im, Complex.one_im, im_wPt] at him
    have hpos : 0 < 2 * y / (1 + y ^ 2) := div_pos (by linarith [hy.1]) (by positivity)
    linarith
  have hcl_sing : zetaD b ∈ closure halfDisc \ singPts := by
    refine ⟨hcl_diff.1, fun h => ?_⟩
    simp only [singPts, mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h
    · exact hcl_diff.2 (by simp [h])
    · exact hcl_diff.2 (by simp [h])
    · exact hne1 (hzb ▸ h)
  have h1sq_ne : 1 + zetaD b ^ 2 ≠ 0 := one_add_zetaD_sq_ne_zero_imStrip hb_strip
  have h1z_ne : 1 + zetaD b ≠ 0 := one_add_ne_zero' hcl_diff.1
  have hq_ne : qBd (zetaD b) ≠ 0 := qBd_ne_zero hcl_sing
  have hkap_ne : (kap : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr kap_pos.ne'
  have hr1_ne : (1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2) ≠ 0 :=
    Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hb_q)
  have hr2_ne : (π : ℂ) * b / Complex.sinh ((π : ℂ) * b) ≠ 0 :=
    Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hb_strip)
  have h1sub_ne : 1 - starRingEnd ℂ (wPt y) ≠ 0 := sub_ne_zero.mpr hne1.symm
  unfold logGhatLower
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, Complex.exp_add]
  rw [Complex.exp_log h1sq_ne, Complex.exp_log hkap_ne]
  have he_1z : Complex.exp (2 * Complex.log (1 + zetaD b)) = (1 + zetaD b) ^ 2 := by
    rw [show (2 : ℂ) * Complex.log (1 + zetaD b) = Complex.log (1 + zetaD b) + Complex.log (1 + zetaD b) by ring,
      Complex.exp_add, Complex.exp_log h1z_ne, sq]
  have he_q : (Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))))⁻¹ = (qBd (zetaD b)) ^ (-(1 / 4 : ℂ)) := by
    rw [← Complex.exp_neg, Complex.cpow_def_of_ne_zero hq_ne]; congr 1; ring
  have he_r1 : Complex.exp ((1 / 2 : ℂ) * Complex.log ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2))) =
      ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hr1_ne]; congr 1; ring
  have he_r2 : Complex.exp ((1 / 2 : ℂ) * Complex.log ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b))) =
      ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hr2_ne]; congr 1; ring
  rw [he_1z, he_r1, he_r2]
  have hcancel : (1 - starRingEnd ℂ (wPt y)) ^ (-(1 / 2 : ℂ)) * (1 - starRingEnd ℂ (wPt y)) ^ (1 / 2 : ℂ) = 1 := by
    rw [Complex.cpow_def_of_ne_zero h1sub_ne, Complex.cpow_def_of_ne_zero h1sub_ne, ← Complex.exp_add]
    simp
  unfold Gout R4cStrip
  have hR1_ne : ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hr1_ne]; exact Complex.exp_ne_zero _
  have hR2_ne : ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hr2_ne]; exact Complex.exp_ne_zero _
  have hq_exp_ne : Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) ≠ 0 := Complex.exp_ne_zero _
  have h1z2_ne : (1 + zetaD b) ^ 2 ≠ 0 := pow_ne_zero 2 h1z_ne
  rw [← hzb] at hcancel ⊢
  rw [← he_q]
  have hprod : (1 - zetaD b) ^ (-(1 / 2 : ℂ)) *
      ((1 + zetaD b ^ 2) * (Complex.exp (hbarA aAmp (sInv (zetaD b))) * (1 - zetaD b) ^ (1 / 2 : ℂ) /
        (1 + zetaD b) ^ 2 * (Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))))⁻¹) /
        (((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) *
          ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) / (kap : ℂ))) =
      ((1 - zetaD b) ^ (-(1 / 2 : ℂ)) * (1 - zetaD b) ^ (1 / 2 : ℂ)) *
      (Complex.exp (hbarA aAmp (sInv (zetaD b))) * (1 + zetaD b ^ 2) / (1 + zetaD b) ^ 2 /
        Complex.exp ((1 / 4 : ℂ) * Complex.log (qBd (zetaD b))) /
        ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) /
        ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) * (kap : ℂ)) := by
    field_simp
  rw [hprod, hcancel, one_mul]

private lemma exists_vOf_eq {v : ℝ} (hv : 0 < v) : ∃ y ∈ Ioo (0 : ℝ) 1, vOf y = v := by
  set s := Real.sinh (π * v)
  have hs : 0 < s := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hv)
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : 0 < √(2 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  set y := s / (√2 + √(2 + s ^ 2))
  have hy0 : 0 < y := div_pos hs (by positivity)
  have hlt : s < √(2 + s ^ 2) := by
    rw [Real.lt_sqrt hs.le]; linarith
  have hy1 : y < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨y, ⟨hy0, hy1⟩, ?_⟩
  have h1y : 0 < 1 - y ^ 2 := by nlinarith
  have hratio : 2 * √2 * y / (1 - y ^ 2) = s := by
    have hden : √2 + √(2 + s ^ 2) ≠ 0 := by positivity
    have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq2s : √(2 + s ^ 2) ^ 2 = 2 + s ^ 2 := Real.sq_sqrt (by positivity)
    rw [div_eq_iff h1y.ne']
    simp only [y]
    field_simp
    nlinarith [hsq2, hsq2s]
  have hu : uSlit y - 1 = s ^ 2 := by
    have h1 : uSlit y - 1 = (2 * √2 * y / (1 - y ^ 2)) ^ 2 := by
      unfold uSlit
      have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith [hsq2]
    rw [h1, hratio]
  unfold vOf
  rw [hu, Real.sqrt_sq hs.le, show s = Real.sinh (π * v) from rfl, Real.arsinh_sinh,
    mul_div_cancel_left₀ _ Real.pi_ne_zero]

private lemma norm_exp_logGhatLower_neg_conj {b : ℂ} (hb : b ∈ bandUpper (1 / 8)) (hb_lt : b.im < 1 / 2) :
    ‖Complex.exp (logGhatLower (-starRingEnd ℂ b))‖ = ‖Complex.exp (logGhatLower b)‖ := by
  have hnb : (-starRingEnd ℂ b) ∈ bandUpper (1 / 8) := by
    change |(-starRingEnd ℂ b).im - 1 / 2| < 1 / 8
    simpa using (show |b.im - 1 / 2| < 1 / 8 from hb)
  have hnb_lt : (-starRingEnd ℂ b).im < 1 / 2 := by simpa using hb_lt
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb
  have hnb_strip : (-starRingEnd ℂ b) ∈ imStrip := bandUpper_eighth_subset_imStrip hnb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hb
  have hnb_q : (-starRingEnd ℂ b) ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hnb
  rw [exp_logGhatLower_eq hnb hnb_lt, exp_logGhatLower_eq hb hb_lt]
  have hzeta_conj : zetaD (-starRingEnd ℂ b) = starRingEnd ℂ (zetaD b) := by
    have hcosh : Complex.cosh ((π : ℂ) * (-starRingEnd ℂ b)) =
        starRingEnd ℂ (Complex.cosh ((π : ℂ) * b)) := by
      rw [show (π : ℂ) * (-starRingEnd ℂ b) = -(starRingEnd ℂ ((π : ℂ) * b)) by
          rw [map_mul, Complex.conj_ofReal]; ring,
        Complex.cosh_neg]
      apply Complex.ext <;> simp [re_cosh', im_cosh']
    obtain ⟨_, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb_strip
    have harg : (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) /
        ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))).arg ≠ π := Complex.slitPlane_arg_ne_pi hw_slit
    unfold zetaD
    rw [hcosh, ← Complex.conj_ofReal √2, ← map_sub, ← map_add, ← map_div₀]
    have hc := Complex.cpow_conj (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) /
      ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))) (1 / 2 : ℂ) harg
    have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [one_div, map_inv₀, map_ofNat]
    rw [hhalf] at hc
    have h := congrArg (starRingEnd ℂ) hc
    simpa using h.symm
  have hhd := zetaD_mem_halfDisc hb_strip.1 hb_lt
  unfold Gtilde
  rw [← R4cStrip_eq_R4c hb_q hb_lt, ← R4cStrip_eq_R4c hnb_q hnb_lt]
  rw [hzeta_conj, gout_outerDatum_g1Out.conj _ hhd]
  rw [norm_mul, norm_mul, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_conj]
  have h1 : ‖(1 - starRingEnd ℂ (zetaD b)) ^ (-(1 / 2 : ℂ))‖ = ‖(1 - zetaD b) ^ (-(1 / 2 : ℂ))‖ := by
    have h1sub : 1 - starRingEnd ℂ (zetaD b) = starRingEnd ℂ (1 - zetaD b) := by simp
    have h1slit := one_sub_mem_slit (subset_closure hhd) (halfDisc_ne_special hhd).2.2
    have hnhalf : starRingEnd ℂ (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by rw [map_neg, one_div, map_inv₀, map_ofNat]
    have hc := conj_cpow_slit h1slit (-(1 / 2 : ℂ))
    rw [hnhalf] at hc
    rw [h1sub, ← hc, Complex.norm_conj]
  have h2 : ‖1 + (starRingEnd ℂ (zetaD b)) ^ 2‖ = ‖1 + zetaD b ^ 2‖ := by
    rw [show (1 : ℂ) + (starRingEnd ℂ (zetaD b)) ^ 2 = starRingEnd ℂ (1 + zetaD b ^ 2) by simp,
      Complex.norm_conj]
  have h3 : ‖R4cStrip (-starRingEnd ℂ b)‖ = ‖R4cStrip b‖ := by
    unfold R4cStrip
    rw [hzeta_conj]
    have ha : (1 + 2 * starRingEnd ℂ (zetaD b) - (starRingEnd ℂ (zetaD b)) ^ 2) /
        (1 + (starRingEnd ℂ (zetaD b)) ^ 2) =
        starRingEnd ℂ ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) := by
      simp [map_ofNat]
    have hsh : Complex.sinh ((π : ℂ) * (-starRingEnd ℂ b)) =
        -starRingEnd ℂ (Complex.sinh ((π : ℂ) * b)) := by
      rw [show (π : ℂ) * (-starRingEnd ℂ b) = -(starRingEnd ℂ ((π : ℂ) * b)) by
          rw [map_mul, Complex.conj_ofReal]; ring,
        Complex.sinh_neg]
      congr 1; apply Complex.ext <;> simp [re_sinh', im_sinh']
    have hb_ratio : (π : ℂ) * (-starRingEnd ℂ b) / Complex.sinh ((π : ℂ) * (-starRingEnd ℂ b)) =
        starRingEnd ℂ ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) := by
      rw [hsh, map_div₀, map_mul, Complex.conj_ofReal]; ring
    have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [one_div, map_inv₀, map_ofNat]
    have hc1 := conj_cpow_slit (r4c_alg_factor_mem_slitPlane hb_q) (1 / 2 : ℂ)
    have hc2 := conj_cpow_slit (pi_mul_div_sinh_mem_slitPlane hb_strip) (1 / 2 : ℂ)
    rw [hhalf] at hc1 hc2
    rw [ha, hb_ratio, ← hc1, ← hc2, norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj,
      norm_div, norm_mul]
  rw [h1, h2, h3]

/-- On `E_+ = {b = v + i/2}`, `Re(logGhatLower (v + i/2)) = Re(uE v)` for all `v : ℝ`. -/
theorem re_logGhatLower_edge (v : ℝ) :
    (logGhatLower ((v : ℂ) + Complex.I / 2)).re = (uE (v : ℂ)).re := by
  have hpos : ∀ w : ℝ, 0 < w → (logGhatLower ((w : ℂ) + Complex.I / 2)).re = (uE (w : ℂ)).re := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := exists_vOf_eq hw
    have hexp := exp_logGhatLower_edge_eq hy
    rw [← Real.log_exp (logGhatLower ((vOf y : ℂ) + Complex.I / 2)).re, ← Complex.norm_exp, hexp]
    exact (re_uE_eq_log_norm_Ghat hy).symm
  have heven : ∀ w : ℝ, (logGhatLower (((-w : ℝ) : ℂ) + Complex.I / 2)).re =
      (logGhatLower ((w : ℂ) + Complex.I / 2)).re := by
    intro w
    set L := fun t : ℝ => (logGhatLower ((w : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I)).re
    set R := fun t : ℝ => (logGhatLower (((-w : ℝ) : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I)).re
    have hcont_line : ∀ u : ℝ, Tendsto (fun t : ℝ => (logGhatLower ((u : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (logGhatLower ((u : ℂ) + Complex.I / 2)).re) := by
      intro u
      have hu_mem : ((u : ℂ) + Complex.I / 2) ∈ bandUpper (1 / 8) ∩ {b : ℂ | b.im ≤ 1 / 2} :=
        ⟨by change |((u : ℂ) + Complex.I / 2).im - 1 / 2| < 1 / 8; simp, by simp⟩
      refine (Complex.continuous_re.continuousAt.tendsto.comp
        ((continuousOn_logGhatLower _ hu_mem).tendsto.comp ?_))
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ => (u : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I) := by fun_prop
        have h0 : (u : ℂ) + ((1 / 2 - (0 : ℝ) : ℝ) : ℂ) * Complex.I = (u : ℂ) + Complex.I / 2 := by
          push_cast; ring
        rw [← h0]
        exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))]
          with t ht0 ht1
        have ht0' : 0 < t := mem_Ioi.mp ht0
        refine ⟨?_, ?_⟩
        · change |((u : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I).im - 1 / 2| < 1 / 8
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
          rw [abs_lt]; constructor <;> linarith
        · change ((u : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I).im ≤ 1 / 2
          simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
          linarith
    refine tendsto_nhds_unique (hcont_line (-w)) ?_
    refine (hcont_line w).congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))]
      with t ht0 ht1
    have ht0' : 0 < t := mem_Ioi.mp ht0
    set b := (w : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I
    have hb_mem : b ∈ bandUpper (1 / 8) := by
      change |b.im - 1 / 2| < 1 / 8
      simp only [b, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      rw [abs_lt]; constructor <;> linarith
    have hb_lt : b.im < 1 / 2 := by
      simp only [b, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]; linarith
    have hnb : -starRingEnd ℂ b = ((-w : ℝ) : ℂ) + ((1 / 2 - t : ℝ) : ℂ) * Complex.I := by
      simp only [b, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    have hnorm := norm_exp_logGhatLower_neg_conj hb_mem hb_lt
    rw [hnb, Complex.norm_exp, Complex.norm_exp] at hnorm
    exact (Real.exp_injective hnorm).symm
  rcases lt_trichotomy v 0 with hlt | rfl | hgt
  · have h1 := heven (-v)
    rw [neg_neg] at h1
    rw [h1, hpos (-v) (by linarith), show ((-v : ℝ) : ℂ) = -(v : ℂ) by push_cast; ring, uE_neg]
  · -- v = 0 by continuity from v > 0
    have hcont_L : Tendsto (fun w : ℝ => (logGhatLower ((w : ℂ) + Complex.I / 2)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (logGhatLower (((0 : ℝ) : ℂ) + Complex.I / 2)).re) := by
      have h0_mem : (((0 : ℝ) : ℂ) + Complex.I / 2) ∈ bandUpper (1 / 8) ∩ {b : ℂ | b.im ≤ 1 / 2} :=
        ⟨by change |(((0 : ℝ) : ℂ) + Complex.I / 2).im - 1 / 2| < 1 / 8; simp, by simp⟩
      refine Complex.continuous_re.continuousAt.tendsto.comp
        ((continuousOn_logGhatLower _ h0_mem).tendsto.comp ?_)
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact ((Complex.continuous_ofReal.add continuous_const).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      · filter_upwards with w
        exact ⟨by change |((w : ℂ) + Complex.I / 2).im - 1 / 2| < 1 / 8; simp, by simp⟩
    have hcont_R : Tendsto (fun w : ℝ => (uE (w : ℂ)).re) (𝓝[>] (0 : ℝ)) (𝓝 (uE ((0 : ℝ) : ℂ)).re) := by
      have h0_mem : ((0 : ℝ) : ℂ) ∈ {w : ℂ | |w.im| < 1 / 8} := by simp
      have hopen : IsOpen {w : ℂ | |w.im| < 1 / 8} :=
        isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
      have hc : ContinuousAt uE ((0 : ℝ) : ℂ) :=
        (differentiableOn_uE.continuousOn).continuousAt (hopen.mem_nhds h0_mem)
      exact (Complex.continuous_re.continuousAt.tendsto.comp
        (hc.tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique hcont_L (hcont_R.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hpos w (mem_Ioi.mp hw)).symm
  · exact hpos v hgt

/-! ### 2. Schwarz reflection with prescribed real part `uE` across `Im b = 1/2` -/

/-- Holomorphic reflection of `log Ĝ ∘ ζ_D` across `E_+` onto `bandUpper (1/8)`. -/
noncomputable def logGhatRefl (b : ℂ) : ℂ :=
  schwarzReflectPrescribedRe 0 (fun w => logGhatLower (-w + Complex.I / 2)) uE (Complex.I / 2 - b)

/-- `logGhatRefl` is holomorphic on `bandUpper (1/8)`. -/
theorem differentiableOn_logGhatRefl : DifferentiableOn ℂ logGhatRefl (bandUpper (1 / 8)) := by
  set U : Set ℂ := {w : ℂ | |w.im| < 1 / 8}
  have hU_open : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hU_symm : ∀ w ∈ U, reflHoriz 0 w ∈ U := by
    intro w hw
    change |(reflHoriz 0 w).im| < 1 / 8
    rw [reflHoriz_im, two_mul, zero_add, zero_sub, abs_neg]
    exact hw
  have hf_cont : ContinuousOn (fun w => logGhatLower (-w + Complex.I / 2)) (U ∩ {w : ℂ | 0 ≤ w.im}) := by
    refine continuousOn_logGhatLower.comp (by fun_prop) fun w hw => ?_
    refine ⟨?_, ?_⟩
    · change |(-w + Complex.I / 2).im - 1 / 2| < 1 / 8
      have : (-w + Complex.I / 2).im - 1 / 2 = -w.im := by simp
      rw [this, abs_neg]; exact hw.1
    · change (-w + Complex.I / 2).im ≤ 1 / 2
      have hw0 : 0 ≤ w.im := hw.2
      simp; linarith
  have hf_holo : DifferentiableOn ℂ (fun w => logGhatLower (-w + Complex.I / 2)) (U ∩ {w : ℂ | 0 < w.im}) := by
    refine differentiableOn_logGhatLower.comp (by fun_prop) fun w hw => ?_
    refine ⟨?_, ?_⟩
    · change |(-w + Complex.I / 2).im - 1 / 2| < 1 / 8
      have : (-w + Complex.I / 2).im - 1 / 2 = -w.im := by simp
      rw [this, abs_neg]; exact hw.1
    · change (-w + Complex.I / 2).im < 1 / 2
      have hw0 : 0 < w.im := hw.2
      simp; linarith
  have hf_re : ∀ w ∈ U, w.im = 0 → (logGhatLower (-w + Complex.I / 2)).re = (uE w).re := by
    intro w _ hwim
    have hw_eq : w = (w.re : ℂ) := Complex.ext rfl (by simpa using hwim)
    rw [hw_eq, show -((w.re : ℂ)) + Complex.I / 2 = (((-w.re : ℝ) : ℂ) + Complex.I / 2) by push_cast; ring,
      re_logGhatLower_edge (-w.re), show ((-w.re : ℝ) : ℂ) = -(w.re : ℂ) by push_cast; ring, uE_neg]
  have hrefl := schwarzReflection_prescribed_re hU_open hU_symm differentiableOn_uE
    (fun w _ hwim => by
      have hw_eq : w = (w.re : ℂ) := Complex.ext rfl (by simpa using hwim)
      rw [hw_eq]; exact im_uE_real w.re)
    hf_cont hf_holo hf_re
  unfold logGhatRefl
  refine hrefl.comp (by fun_prop) fun b hb => ?_
  change |(Complex.I / 2 - b).im| < 1 / 8
  have : (Complex.I / 2 - b).im = -(b.im - 1 / 2) := by simp
  rw [this, abs_neg]
  exact hb

lemma logGhatRefl_eq_lower {b : ℂ} (hb : b.im ≤ 1 / 2) : logGhatRefl b = logGhatLower b := by
  have hge : 0 ≤ (Complex.I / 2 - b).im := by simp; linarith
  simp only [logGhatRefl, schwarzReflectPrescribedRe, hge, ↓reduceIte]
  congr 1; ring

/-! ### 3. `EsmExt`, `EeUpper`, and the glued extension `EeExt` on `{|Im b| < 1/2 + η_δ}` -/

/-- The smooth factor `Esm` on `bandUpper (1/8)`: holomorphic and zero-free. -/
noncomputable def EsmExt (δ : ℝ) (b : ℂ) : ℂ :=
  (1 + zetaD b ^ 2) ^ 2 / (R4cStrip b * Complex.exp (logGhatRefl b)) * Complex.exp (-DeltaPhi δ b)

/-- Upper-band formula for `Ee` on `bandUpper (1/8) ∩ {Im b < 1/2 + η_δ}`. -/
noncomputable def EeUpper (δ : ℝ) (b : ℂ) : ℂ :=
  (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ)) * EsmExt δ b

/-- Even holomorphic zero-free extension of `Estripped δ` to `{|Im b| < 1/2 + η_δ}` (`cts:smooth-env` (2)). -/
noncomputable def EeExt (δ : ℝ) (b : ℂ) : ℂ :=
  if |b.im| < 1 / 2 then Ee δ b
  else if 0 < b.im then EeUpper δ b
  else EeUpper δ (-b)

lemma differentiableOn_EsmExt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    DifferentiableOn ℂ (EsmExt δ) (bandUpper (1 / 8)) := by
  intro b hb
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hb
  have hopen8 : IsOpen (bandUpper (1 / 8)) :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hzeta : DifferentiableAt ℂ zetaD b :=
    differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have hR4 : DifferentiableAt ℂ R4cStrip b :=
    differentiableOn_R4cStrip.differentiableAt (isOpen_band.mem_nhds hb_q)
  have hlog : DifferentiableAt ℂ logGhatRefl b :=
    differentiableOn_logGhatRefl.differentiableAt (hopen8.mem_nhds hb)
  have hdp : DifferentiableAt ℂ (DeltaPhi δ) b :=
    (differentiableOn_DeltaPhi_imStrip hδ0 hδ1).differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have hden : R4cStrip b * Complex.exp (logGhatRefl b) ≠ 0 :=
    mul_ne_zero (R4cStrip_ne_zero hb_q) (Complex.exp_ne_zero _)
  unfold EsmExt
  exact (((((differentiableAt_const _).add (hzeta.pow 2)).pow 2).div (hR4.mul hlog.cexp) hden).mul
    hdp.neg.cexp).differentiableWithinAt

lemma EsmExt_ne_zero {δ : ℝ} {b : ℂ} (hb : b ∈ bandUpper (1 / 8)) : EsmExt δ b ≠ 0 := by
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hb
  unfold EsmExt
  exact mul_ne_zero
    (div_ne_zero (pow_ne_zero 2 (one_add_zetaD_sq_ne_zero_imStrip hb_strip))
      (mul_ne_zero (R4cStrip_ne_zero hb_q) (Complex.exp_ne_zero _)))
    (Complex.exp_ne_zero _)

private lemma differentiableOn_EeUpper {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    DifferentiableOn ℂ (EeUpper δ) (bandUpper (1 / 8) ∩ {b : ℂ | b.im < 1 / 2 + etaDelta δ}) := by
  intro b hb
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb.1
  have hopen8 : IsOpen (bandUpper (1 / 8)) :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hzeta : DifferentiableAt ℂ zetaD b :=
    differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have hEsm : DifferentiableAt ℂ (EsmExt δ) b :=
    (differentiableOn_EsmExt hδ0 hδ1).differentiableAt (hopen8.mem_nhds hb.1)
  have hslit := one_sub_one_sub_delta_zetaD_mem_slitPlane hδ0 hδ1 hb_strip.1 hb.2
  have hfac : DifferentiableAt ℂ (fun w => (1 - ((1 - δ : ℝ) : ℂ) * zetaD w) ^ (-(1 / 2 : ℂ))) b :=
    ((differentiableAt_const _).sub ((differentiableAt_const _).mul hzeta)).cpow_const hslit
  unfold EeUpper
  exact (hfac.mul hEsm).differentiableWithinAt

private lemma EeUpper_ne_zero {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb : b ∈ bandUpper (1 / 8)) (hb_lt : b.im < 1 / 2 + etaDelta δ) :
    EeUpper δ b ≠ 0 := by
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb
  have hslit := one_sub_one_sub_delta_zetaD_mem_slitPlane hδ0 hδ1 hb_strip.1 hb_lt
  unfold EeUpper
  refine mul_ne_zero ?_ (EsmExt_ne_zero hb)
  rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hslit)]
  exact Complex.exp_ne_zero _

private lemma EeUpper_eq_Estripped {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb : b ∈ bandUpper (1 / 8)) (hb_lt : b.im < 1 / 2) :
    EeUpper δ b = Estripped δ b := by
  have hb_strip : b ∈ imStrip := bandUpper_eighth_subset_imStrip hb
  have hb_q : b ∈ bandUpper (1 / 4) := bandUpper_eighth_subset_quarter hb
  have hhd := zetaD_mem_halfDisc hb_strip.1 hb_lt
  unfold EeUpper EsmExt Estripped
  rw [logGhatRefl_eq_lower hb_lt.le, exp_logGhatLower_eq hb hb_lt, R4cStrip_eq_R4c hb_q hb_lt,
    fDelta_factor hδ0 (by linarith) hhd]
  ring

/-- **`EeExt δ` is holomorphic on `{|Im b| < 1/2 + η_δ}`** (`OuterS3`, `cts:smooth-env` (2)). -/
theorem differentiableOn_EeExt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10) :
    DifferentiableOn ℂ (EeExt δ) {b : ℂ | |b.im| < 1 / 2 + etaDelta δ} := by
  have hδ4 : δ < 1 / 4 := by linarith
  have heta_pos : 0 < etaDelta δ := (etaDelta_mem hδ0 hδ4).1
  have heta_lt : etaDelta δ < 1 / 16 := etaDelta_lt_one_sixteenth hδ0 hδ1.le
  intro b hb
  have hbim : |b.im| < 1 / 2 + etaDelta δ := hb
  by_cases hmid : |b.im| < 1 / 2
  · have hopen : IsOpen {z : ℂ | |z.im| < 1 / 2} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
    have hd : DifferentiableAt ℂ (Ee δ) b :=
      (differentiableOn_Ee_symmStrip hδ0 hδ4).differentiableAt (hopen.mem_nhds hmid)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hopen.mem_nhds hmid] with z hz
    have hz' : |z.im| < 1 / 2 := hz
    rw [EeExt, ite_eq_left_iff.mpr (fun h => absurd hz' h)]
  · rcases lt_or_gt_of_ne (show b.im ≠ 0 by intro h; apply hmid; simp [h]) with hneg | hpos
    · -- Lower band: -(1/2 + η_δ) < Im b < -3/8
      set V : Set ℂ := {z : ℂ | -(1 / 2 + etaDelta δ) < z.im ∧ z.im < -(3 / 8)}
      have hV_open : IsOpen V :=
        (isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)
      have hbV : b ∈ V := ⟨by linarith [(abs_lt.mp hbim).1], by
        have : b.im ≤ -(1 / 2) := by
          by_contra h; push Not at h; apply hmid; rw [abs_lt]; exact ⟨h, by linarith⟩
        linarith⟩
      have hd : DifferentiableAt ℂ (fun z => EeUpper δ (-z)) b := by
        have hnb_mem : (-b) ∈ bandUpper (1 / 8) ∩ {z : ℂ | z.im < 1 / 2 + etaDelta δ} := by
          refine ⟨?_, ?_⟩
          · change |(-b).im - 1 / 2| < 1 / 8
            simp only [Complex.neg_im]; rw [abs_lt]; constructor <;> linarith [hbV.1, hbV.2]
          · change (-b).im < 1 / 2 + etaDelta δ
            simp only [Complex.neg_im]; linarith [hbV.1]
        have hopenU : IsOpen (bandUpper (1 / 8) ∩ {z : ℂ | z.im < 1 / 2 + etaDelta δ}) :=
          (isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const).inter
            (isOpen_lt Complex.continuous_im continuous_const)
        exact ((differentiableOn_EeUpper hδ0 hδ4).differentiableAt (hopenU.mem_nhds hnb_mem)).comp b
          differentiableAt_id.neg
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hV_open.mem_nhds hbV] with z hz
      unfold EeExt
      by_cases hzm : |z.im| < 1 / 2
      · rw [ite_eq_left_iff.mpr (fun h => absurd hzm h), ← Ee_neg hδ0 hδ4 z]
        have hnz0 : 0 < (-z).im := by simp; linarith [hz.2]
        have hnz1 : (-z).im < 1 / 2 := by simp; linarith [(abs_lt.mp hzm).1]
        have hnz_b : (-z) ∈ bandUpper (1 / 8) := by
          change |(-z).im - 1 / 2| < 1 / 8; simp; rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
        rw [Ee_eq_Estripped hδ0 hδ4 hnz0 hnz1, EeUpper_eq_Estripped hδ0 hδ4 hnz_b hnz1]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hzm),
          ite_eq_right_iff.mpr (fun h => by linarith [hz.2])]
    · -- Upper band: 3/8 < Im b < 1/2 + η_δ
      set V : Set ℂ := {z : ℂ | 3 / 8 < z.im ∧ z.im < 1 / 2 + etaDelta δ}
      have hV_open : IsOpen V :=
        (isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)
      have hbV : b ∈ V := ⟨by
        have : 1 / 2 ≤ b.im := by
          by_contra h; push Not at h; apply hmid; rw [abs_lt]; exact ⟨by linarith, h⟩
        linarith, (abs_lt.mp hbim).2⟩
      have hb_mem : b ∈ bandUpper (1 / 8) ∩ {z : ℂ | z.im < 1 / 2 + etaDelta δ} := by
        refine ⟨?_, hbV.2⟩
        change |b.im - 1 / 2| < 1 / 8; rw [abs_lt]; constructor <;> linarith [hbV.1, hbV.2]
      have hopenU : IsOpen (bandUpper (1 / 8) ∩ {z : ℂ | z.im < 1 / 2 + etaDelta δ}) :=
        (isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const).inter
          (isOpen_lt Complex.continuous_im continuous_const)
      have hd : DifferentiableAt ℂ (EeUpper δ) b :=
        (differentiableOn_EeUpper hδ0 hδ4).differentiableAt (hopenU.mem_nhds hb_mem)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hV_open.mem_nhds hbV] with z hz
      unfold EeExt
      by_cases hzm : |z.im| < 1 / 2
      · rw [ite_eq_left_iff.mpr (fun h => absurd hzm h)]
        have hz0 : 0 < z.im := by linarith [hz.1]
        have hz1 : z.im < 1 / 2 := (abs_lt.mp hzm).2
        have hz_b : z ∈ bandUpper (1 / 8) := by
          change |z.im - 1 / 2| < 1 / 8; rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
        rw [Ee_eq_Estripped hδ0 hδ4 hz0 hz1, EeUpper_eq_Estripped hδ0 hδ4 hz_b hz1]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hzm),
          ite_eq_left_iff.mpr (fun h => by linarith [hz.1])]

/-- **`EeExt δ` is zero-free on `{|Im b| < 1/2 + η_δ}`** (`OuterS3`, `cts:smooth-env` (2)). -/
theorem EeExt_ne_zero {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10)
    {b : ℂ} (hb : |b.im| < 1 / 2 + etaDelta δ) : EeExt δ b ≠ 0 := by
  have hδ4 : δ < 1 / 4 := by linarith
  have heta_lt : etaDelta δ < 1 / 16 := etaDelta_lt_one_sixteenth hδ0 hδ1.le
  unfold EeExt
  by_cases hmid : |b.im| < 1 / 2
  · rw [ite_eq_left_iff.mpr (fun h => absurd hmid h)]
    exact Ee_ne_zero_symmStrip hδ0 hδ4 hmid
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hmid)]
    by_cases hpos : 0 < b.im
    · rw [ite_eq_left_iff.mpr (fun h => absurd hpos h)]
      have hge : 1 / 2 ≤ b.im := by
        by_contra h; push Not at h; apply hmid; rw [abs_lt]; exact ⟨by linarith, h⟩
      have hbb : b ∈ bandUpper (1 / 8) := by
        change |b.im - 1 / 2| < 1 / 8; rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hb).2]
      exact EeUpper_ne_zero hδ0 hδ4 hbb (abs_lt.mp hb).2
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hpos)]
      have hle : b.im ≤ -(1 / 2) := by
        by_contra h; push Not at h; apply hmid; rw [abs_lt]; exact ⟨h, by linarith⟩
      have hbb : (-b) ∈ bandUpper (1 / 8) := by
        change |(-b).im - 1 / 2| < 1 / 8; simp; rw [abs_lt]; constructor <;> linarith [(abs_lt.mp hb).1]
      exact EeUpper_ne_zero hδ0 hδ4 hbb (by simp; linarith [(abs_lt.mp hb).1])

/-- **`EeExt δ` is even**: `EeExt δ (-b) = EeExt δ b` for all `b : ℂ` (`OuterS3`). -/
theorem EeExt_neg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (b : ℂ) :
    EeExt δ (-b) = EeExt δ b := by
  unfold EeExt
  by_cases hmid : |b.im| < 1 / 2
  · have hnb : |(-b).im| < 1 / 2 := by simpa using hmid
    rw [ite_eq_left_iff.mpr (fun h => absurd hnb h), ite_eq_left_iff.mpr (fun h => absurd hmid h)]
    exact Ee_neg hδ0 hδ1 b
  · have hnb : ¬ |(-b).im| < 1 / 2 := by simpa using hmid
    rw [ite_eq_right_iff.mpr (fun h => absurd h hnb), ite_eq_right_iff.mpr (fun h => absurd h hmid)]
    rcases lt_or_gt_of_ne (show b.im ≠ 0 by intro h; apply hmid; simp [h]) with hneg | hpos
    · have h1 : 0 < (-b).im := by simp; linarith
      have h2 : ¬ 0 < b.im := by linarith
      rw [ite_eq_left_iff.mpr (fun h => absurd h1 h), ite_eq_right_iff.mpr (fun h => absurd h h2)]
    · have h1 : ¬ 0 < (-b).im := by simp; linarith
      rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_left_iff.mpr (fun h => absurd hpos h), neg_neg]

/-- **`EeExt δ` is real and strictly positive on `ℝ`** (`OuterS3`). -/
theorem EeExt_real_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    0 < (EeExt δ (x : ℂ)).re ∧ (EeExt δ (x : ℂ)).im = 0 := by
  have hx : |(x : ℂ).im| < 1 / 2 := by simp
  rw [EeExt, ite_eq_left_iff.mpr (fun h => absurd hx h)]
  exact Ee_real_pos hδ0 hδ1 x

/-- **`EeExt δ` agrees with `Estripped δ` on `0 < Im b < 1/2`** (`OuterS3`). -/
theorem EeExt_eq_Estripped {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) :
    EeExt δ b = Estripped δ b := by
  have hb : |b.im| < 1 / 2 := abs_lt.mpr ⟨by linarith, hb1⟩
  rw [EeExt, ite_eq_left_iff.mpr (fun h => absurd hb h)]
  exact Ee_eq_Estripped hδ0 hδ1 hb0 hb1

/-- **`EeExt δ` slit modulus identity** (`OuterS3`): `‖EeExt δ x‖ * e^{Re ΔΦ_δ(x)} = ‖F_δ(i y(x))‖`. -/
theorem EeExt_modulus_identity {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : xiStar ≤ x) :
    ‖EeExt δ (x : ℂ)‖ * Real.exp (DeltaPhi δ (x : ℂ)).re =
      ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ := by
  have hx' : |(x : ℂ).im| < 1 / 2 := by simp
  rw [EeExt, ite_eq_left_iff.mpr (fun h => absurd hx' h)]
  exact Ee_modulus_identity hδ0 hδ1 hx

/-- **Branch-point factorisation on `bandUpper (1/16) ∩ {Im b < 1/2 + η_δ}`** (`OuterS3`):
`EeExt δ b = (1 - (1 - δ) ζ_D b)^{-1/2} * EsmExt δ b` with `EsmExt δ` holomorphic and zero-free on
`bandUpper (1/16)`. -/
theorem EeExt_factor_EsmExt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10) :
    DifferentiableOn ℂ (EsmExt δ) (bandUpper (1 / 16)) ∧
    (∀ b ∈ bandUpper (1 / 16), EsmExt δ b ≠ 0) ∧
    (∀ b ∈ bandUpper (1 / 16), b.im < 1 / 2 + etaDelta δ →
      EeExt δ b = (1 - ((1 - δ : ℝ) : ℂ) * zetaD b) ^ (-(1 / 2 : ℂ)) * EsmExt δ b) := by
  have hδ4 : δ < 1 / 4 := by linarith
  have hsub : bandUpper (1 / 16) ⊆ bandUpper (1 / 8) := fun b hb =>
    lt_trans (show |b.im - 1 / 2| < 1 / 16 from hb) (by norm_num)
  refine ⟨(differentiableOn_EsmExt hδ0 hδ4).mono hsub, fun b hb => EsmExt_ne_zero (hsub hb), fun b hb _ => ?_⟩
  have hb8 : b ∈ bandUpper (1 / 8) := hsub hb
  have hb0 : 0 < b.im := by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 16 from hb)).1]
  unfold EeExt
  by_cases hmid : |b.im| < 1 / 2
  · rw [ite_eq_left_iff.mpr (fun h => absurd hmid h),
      Ee_eq_Estripped hδ0 hδ4 hb0 (abs_lt.mp hmid).2,
      ← EeUpper_eq_Estripped hδ0 hδ4 hb8 (abs_lt.mp hmid).2]
    rfl
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hmid),
      ite_eq_left_iff.mpr (fun h => absurd hb0 h)]
    rfl

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.re_logGhatLower_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.re_logGhatLower_edge

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_logGhatRefl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_logGhatRefl

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_EeExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_EeExt

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_ne_zero

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_neg

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_real_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_real_pos

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_eq_Estripped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_eq_Estripped

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_modulus_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_modulus_identity

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_factor_EsmExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.EeExt_factor_EsmExt
