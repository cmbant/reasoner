module

public import FormalResearch.SignUncertainty.UctAiryTransClosed

/-!
# The holomorphic extensions of `f̃₁`, `g̃₁` and their ODEs (`uct:airy-trans`, F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:airy-trans` (1)-(2) (the proof of the asymptotics
`(uct:Fstar-asym)` rotates the contour; here the same information is obtained from the linear ODEs).

`uctF1Ext w = c w^{1/2} E(w)` (`c = k/√π`) and `uctG1Ext w = k E₁(w) + c w^{3/2} E₂(w)` are holomorphic on the slit plane and agree
with `f̃₁(i w)`, `g̃₁(i w)` on `Re w ≥ 0` (`airyTwistedLaplaceC_ceF1_closed`, `airyTwistedLaplaceC_ceG1_closed`).  They solve
`Φ' = (a₁ - w²/4) Φ + (c/2) w^{-1/2}` and `Ψ' = (a₁ - w²/4) Ψ + Φ` (`hasDerivAt_uctF1Ext`, `hasDerivAt_uctG1Ext`), which follow from
the integration by parts identities `uct_kap_ibp`, `uct_kap1_ibp` for `∫₀¹ t^{-1/2} e^{ψ(wt)} dt` and `∫₀¹ (1-t) t^{-1/2} e^{ψ(wt)} dt`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma hasDerivAt_uctPsi_real (w : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => uctPsi (w * (t : ℂ))) (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4) t := by
  have h := (hasDerivAt_uctPsi_mul w (t : ℂ)).comp_ofReal
  have e : (fun t : ℝ => uctPsi ((t : ℂ) * w)) = fun t : ℝ => uctPsi (w * (t : ℂ)) := by
    funext t; rw [mul_comm]
  rw [e] at h
  convert h using 1; ring

/-- Integration by parts for `q(t) e^{ψ(w t)}` on `[0,1]` -/
lemma uct_ibp (w : ℂ) {q q' : ℝ → ℂ} (hq : ContinuousOn q (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt q (q' t) t) (hi : IntegrableOn q' (Ioc 0 1)) :
    ∫ t in Ioc (0 : ℝ) 1, (q' t + q t * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) * cexp (uctPsi (w * (t : ℂ))) =
      q 1 * cexp (uctPsi w) - q 0 := by
  set H : ℝ → ℂ := fun t => q t * cexp (uctPsi (w * (t : ℂ))) with hH
  have hcont : Continuous fun t : ℝ => cexp (uctPsi (w * (t : ℂ))) := by
    unfold uctPsi; fun_prop
  have hHc : ContinuousOn H (Icc 0 1) := hq.mul hcont.continuousOn
  have hHd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt H ((q' t + q t * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) * cexp (uctPsi (w * (t : ℂ)))) t := by
    intro t ht
    have h2 := ((hasDerivAt_uctPsi_real w t).cexp)
    have h3 := (hd t ht).mul h2
    convert h3 using 1; ring
  have hint : IntervalIntegrable (fun t : ℝ => (q' t + q t * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) * cexp (uctPsi (w * (t : ℂ)))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hpoly : Continuous fun t : ℝ => (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4) := by fun_prop
    have hqp : IntegrableOn (fun t : ℝ => q t * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) (Ioc 0 1) :=
      ((hq.mul hpoly.continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hsum : IntegrableOn (fun t : ℝ => q' t + q t * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) (Icc 0 1) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mpr (hi.add hqp)
    exact (hsum.mul_continuousOn hcont.continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hHc hHd hint
  rw [intervalIntegral.integral_of_le zero_le_one] at this
  rw [this]
  simp [hH, uctPsi]

lemma continuousOn_ofReal_cpow_half : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ)) (Icc 0 1) := by
  intro t ht
  have h := (Complex.continuousAt_cpow_const_of_re_pos (z := (t : ℂ)) (w := (1 / 2 : ℂ)) (Or.inl (by simpa using ht.1)) (by norm_num))
  exact (h.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

lemma hasDerivAt_ofReal_cpow_half {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * uctKap t) t := by
  have hs : (t : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using ht)
  have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := (1 / 2 : ℂ)) hs).comp_ofReal
  refine h.congr_deriv ?_
  unfold uctKap
  simp only [id, mul_one]
  congr 2; norm_num

lemma integrableOn_uctKap_mul {g : ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn (fun t : ℝ => uctKap t * g t) (Ioc 0 1) := by
  have h : IntegrableOn uctKap (Icc 0 1) := (integrableOn_Icc_iff_integrableOn_Ioc).mpr integrableOn_uctKap
  exact (h.mul_continuousOn hg.continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self

lemma uctKap_mul_t' {t : ℝ} (ht : 0 < t) : uctKap t * (t : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
  have := uctKap_mul_t ht
  push_cast at this
  exact this

/-- `w ∫ κ e^{ψ(wt)} (-a₁ t + w² t³/4) dt + ½ ∫ κ e^{ψ(wt)} dt = e^{ψ(w)}` (`κ = t^{-1/2}`). -/
lemma uct_kap_ibp (w : ℂ) :
    w * (∫ t in Ioc (0 : ℝ) 1, uctKap t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4)) +
      (1 / 2) * uctWI uctKap w = cexp (uctPsi w) := by
  have h := uct_ibp w (q := fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ)) (q' := fun t : ℝ => (1 / 2 : ℂ) * uctKap t)
    continuousOn_ofReal_cpow_half (fun t ht => hasDerivAt_ofReal_cpow_half ht.1) (integrableOn_uctKap.const_mul _)
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, ((1 / 2 : ℂ) * uctKap t + (t : ℂ) ^ (1 / 2 : ℂ) * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) * cexp (uctPsi (w * (t : ℂ))) =
      (1 / 2 : ℂ) * (uctKap t * cexp (uctPsi (w * (t : ℂ)))) + w * (uctKap t * (cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4))) := by
    intro t ht
    rw [← uctKap_mul_t' ht.1]; ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt] at h
  have hc1 : Continuous fun t : ℝ => cexp (uctPsi (w * (t : ℂ))) := by unfold uctPsi; fun_prop
  have hc2 : Continuous fun t : ℝ => cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4) := by unfold uctPsi; fun_prop
  rw [integral_add ((integrableOn_uctKap_mul hc1).const_mul _) ((integrableOn_uctKap_mul hc2).const_mul _), integral_const_mul, integral_const_mul] at h
  simp only [Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero] at h
  have h0 : (0 : ℂ) ^ (1 / 2 : ℂ) = 0 := Complex.zero_cpow (by norm_num)
  rw [h0, sub_zero, one_mul] at h
  unfold uctWI
  have e : ∀ t : ℝ, uctKap t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4) =
      uctKap t * (cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4)) := fun t => by ring
  simp_rw [e]
  rw [← h]; ring

lemma integrableOn_uctKap1_mul {g : ℝ → ℂ} (hg : Continuous g) :
    IntegrableOn (fun t : ℝ => uctKap1 t * g t) (Ioc 0 1) := by
  have h : IntegrableOn uctKap1 (Icc 0 1) := (integrableOn_Icc_iff_integrableOn_Ioc).mpr integrableOn_uctKap1
  exact (h.mul_continuousOn hg.continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self

lemma uctKap1_mul_t {t : ℝ} (ht : 0 < t) : uctKap1 t * (t : ℂ) = ((1 - t : ℝ) : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ) := by
  unfold uctKap1
  rw [mul_assoc, ← uctKap_mul_t' ht]; rfl

lemma uctKap1_eq (t : ℝ) : uctKap1 t = ((1 - t : ℝ) : ℂ) * uctKap t := rfl

/-- `w U' + (3/2) U = ∫ κ e` with `U = ∫ (1-t) κ e^{ψ(wt)}`. -/
lemma uct_kap1_ibp (w : ℂ) :
    w * (∫ t in Ioc (0 : ℝ) 1, uctKap1 t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4)) +
      (3 / 2) * uctWI uctKap1 w = uctWI uctKap w := by
  have hq : ContinuousOn (fun t : ℝ => ((1 - t : ℝ) : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ)) (Icc 0 1) :=
    (Continuous.continuousOn (by fun_prop)).mul continuousOn_ofReal_cpow_half
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => ((1 - t : ℝ) : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ)) ((3 / 2 : ℂ) * uctKap1 t - uctKap t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => ((1 - t : ℝ) : ℂ)) (-1) t := by
      have := ((hasDerivAt_id t).const_sub 1).ofReal_comp
      simpa using this
    have h2 := h1.mul (hasDerivAt_ofReal_cpow_half ht.1)
    refine h2.congr_deriv ?_
    have := uctKap_mul_t' ht.1
    rw [uctKap1_eq]
    have e : (t : ℂ) ^ (1 / 2 : ℂ) = uctKap t * (t : ℂ) := this.symm
    rw [e]; push_cast; ring
  have hint : IntegrableOn (fun t : ℝ => (3 / 2 : ℂ) * uctKap1 t - uctKap t) (Ioc 0 1) :=
    (integrableOn_uctKap1.const_mul _).sub integrableOn_uctKap
  have h := uct_ibp w hq hd hint
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, (((3 / 2 : ℂ) * uctKap1 t - uctKap t) + ((1 - t : ℝ) : ℂ) * (t : ℂ) ^ (1 / 2 : ℂ) * (-(uctA1 * w) + w ^ 3 * (t : ℂ) ^ 2 / 4)) * cexp (uctPsi (w * (t : ℂ))) =
      (3 / 2 : ℂ) * (uctKap1 t * cexp (uctPsi (w * (t : ℂ)))) - uctKap t * cexp (uctPsi (w * (t : ℂ))) +
        w * (uctKap1 t * (cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4))) := by
    intro t ht
    rw [← uctKap1_mul_t ht.1]; ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt] at h
  have hc1 : Continuous fun t : ℝ => cexp (uctPsi (w * (t : ℂ))) := by unfold uctPsi; fun_prop
  have hc2 : Continuous fun t : ℝ => cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4) := by unfold uctPsi; fun_prop
  have i1 := ((integrableOn_uctKap1_mul hc1).const_mul (3 / 2 : ℂ))
  have i2 := integrableOn_uctKap_mul hc1
  have i3 := ((integrableOn_uctKap1_mul hc2).const_mul w)
  have h12 : IntegrableOn (fun x : ℝ => 3 / 2 * (uctKap1 x * cexp (uctPsi (w * (x : ℂ)))) - uctKap x * cexp (uctPsi (w * (x : ℂ)))) (Ioc 0 1) := i1.sub i2
  rw [integral_add h12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul] at h
  simp only [Complex.ofReal_one, sub_self, zero_mul, Complex.ofReal_zero, sub_zero] at h
  have h0 : (0 : ℂ) ^ (1 / 2 : ℂ) = 0 := Complex.zero_cpow (by norm_num)
  rw [h0, mul_zero, zero_sub] at h
  unfold uctWI
  have e : ∀ t : ℝ, uctKap1 t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4) =
      uctKap1 t * (cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4)) := fun t => by ring
  simp_rw [e]
  linear_combination h


/-! ### Derivatives of `E`, `E₂` and the ODEs -/

noncomputable def uctC : ℂ := (ceK : ℂ) / (Real.sqrt π : ℂ)

lemma exp_uctG_mul_exp_psi (w : ℂ) : cexp (uctA1 * w - w ^ 3 / 12) * cexp (uctPsi w) = 1 := by
  rw [← Complex.exp_add]; unfold uctPsi
  rw [show uctA1 * w - w ^ 3 / 12 + (-(uctA1 * w) + w ^ 3 / 12) = 0 by ring, Complex.exp_zero]

lemma hasDerivAt_uctE {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt uctE ((uctA1 - w ^ 2 / 4) * uctE w + (1 - uctE w) / (2 * w)) w := by
  have hg := hasDerivAt_uctG w
  have hW := uctWI_hasDerivAt integrableOn_uctKap w
  have h := (hg.const_mul (1 / 2 : ℂ)).mul hW
  unfold uctE
  refine h.congr_deriv ?_
  have hid := uct_kap_ibp w
  set D := ∫ t in Ioc (0 : ℝ) 1, uctKap t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4) with hD
  have hD' : D = (cexp (uctPsi w) - (1 / 2) * uctWI uctKap w) / w := by
    rw [eq_div_iff hw]; linear_combination hid
  have hge := exp_uctG_mul_exp_psi w
  set Eg := cexp (uctA1 * w - w ^ 3 / 12) with hEg
  set e := cexp (uctPsi w) with he
  set W := uctWI uctKap w with hW'
  have key : (1 / 2 : ℂ) * Eg * D = (1 - 1 / 2 * Eg * W) / (2 * w) := by
    rw [hD']
    have : (1 / 2 : ℂ) * Eg * ((e - 1 / 2 * W) / w) = (1 / 2 * (Eg * e) - 1 / 4 * Eg * W) / w := by ring
    rw [this, hge]
    field_simp
    ring
  linear_combination key


lemma hasDerivAt_uctE2 {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt uctE2 ((uctA1 - w ^ 2 / 4) * uctE2 w + (uctE w - (3 / 2) * uctE2 w) / w) w := by
  have hg := hasDerivAt_uctG w
  have hW := uctWI_hasDerivAt integrableOn_uctKap1 w
  have h := (hg.const_mul (1 / 2 : ℂ)).mul hW
  unfold uctE2
  refine h.congr_deriv ?_
  have hid := uct_kap1_ibp w
  set D := ∫ t in Ioc (0 : ℝ) 1, uctKap1 t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4) with hD
  have hD' : D = (uctWI uctKap w - (3 / 2) * uctWI uctKap1 w) / w := by
    rw [eq_div_iff hw]; linear_combination hid
  set Eg := cexp (uctA1 * w - w ^ 3 / 12) with hEg
  set W := uctWI uctKap w with hW'
  set U := uctWI uctKap1 w with hU
  have key : (1 / 2 : ℂ) * Eg * D = (1 / 2 * Eg * W - 3 / 2 * (1 / 2 * Eg * U)) / w := by
    rw [hD']; ring
  have hE : uctE w = 1 / 2 * Eg * W := rfl
  rw [hE]
  linear_combination key

lemma cpow_half_mul_self {w : ℂ} (hw : w ≠ 0) : w ^ (1 / 2 : ℂ) * w = w ^ (3 / 2 : ℂ) := by
  calc w ^ (1 / 2 : ℂ) * w = w ^ (1 / 2 : ℂ) * w ^ (1 : ℂ) := by rw [Complex.cpow_one]
    _ = w ^ (1 / 2 + 1 : ℂ) := (Complex.cpow_add _ _ hw).symm
    _ = _ := by congr 1; norm_num

lemma cpow_neg_half_mul_self {w : ℂ} (hw : w ≠ 0) : w ^ (-(1 / 2) : ℂ) * w = w ^ (1 / 2 : ℂ) := by
  calc w ^ (-(1 / 2) : ℂ) * w = w ^ (-(1 / 2) : ℂ) * w ^ (1 : ℂ) := by rw [Complex.cpow_one]
    _ = w ^ (-(1 / 2) + 1 : ℂ) := (Complex.cpow_add _ _ hw).symm
    _ = _ := by congr 1; norm_num

/-- `F̃₁` extended holomorphically: `c w^{1/2} E(w)`, `c = k/√π`. -/
noncomputable def uctF1Ext (w : ℂ) : ℂ := uctC * w ^ (1 / 2 : ℂ) * uctE w

/-- `g̃₁` extended holomorphically: `k E₁(w) + c w^{3/2} E₂(w)`. -/
noncomputable def uctG1Ext (w : ℂ) : ℂ := (ceK : ℂ) * uctE1 w + uctC * w ^ (3 / 2 : ℂ) * uctE2 w

lemma hasDerivAt_cpow_half {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => w ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * w ^ (-(1 / 2) : ℂ)) w := by
  have h := (hasDerivAt_id w).cpow_const (c := (1 / 2 : ℂ)) hw
  refine h.congr_deriv ?_
  simp only [id, mul_one]; congr 2; norm_num

lemma hasDerivAt_cpow_three_half {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => w ^ (3 / 2 : ℂ)) ((3 / 2 : ℂ) * w ^ (1 / 2 : ℂ)) w := by
  have h := (hasDerivAt_id w).cpow_const (c := (3 / 2 : ℂ)) hw
  refine h.congr_deriv ?_
  simp only [id, mul_one]; congr 2; norm_num

theorem hasDerivAt_uctF1Ext {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt uctF1Ext ((uctA1 - w ^ 2 / 4) * uctF1Ext w + (uctC / 2) * w ^ (-(1 / 2) : ℂ)) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have h := ((hasDerivAt_cpow_half hw).const_mul uctC).mul (hasDerivAt_uctE hw0)
  unfold uctF1Ext
  refine h.congr_deriv ?_
  have h1 := cpow_neg_half_mul_self hw0
  have h2 : w ^ (1 / 2 : ℂ) = w ^ (-(1 / 2) : ℂ) * w := h1.symm
  rw [h2]
  field_simp
  ring

theorem hasDerivAt_uctG1Ext {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt uctG1Ext ((uctA1 - w ^ 2 / 4) * uctG1Ext w + uctF1Ext w) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have hE1 : HasDerivAt uctE1 (uctE1 w * (uctA1 - w ^ 2 / 4)) w := hasDerivAt_uctG w
  have h := (hE1.const_mul (ceK : ℂ)).add (((hasDerivAt_cpow_three_half hw).const_mul uctC).mul (hasDerivAt_uctE2 hw0))
  unfold uctG1Ext
  refine h.congr_deriv ?_
  unfold uctF1Ext
  have h1 : w ^ (3 / 2 : ℂ) = w ^ (1 / 2 : ℂ) * w := (cpow_half_mul_self hw0).symm
  rw [h1]
  field_simp
  ring

end FormalResearch.SignUncertainty
