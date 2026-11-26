module

public import FormalResearch.ModularBootstrap.FiveTerm.StripCoord
public import FormalResearch.ModularBootstrap.FiveTerm.QFactor
public import FormalResearch.SignUncertainty.CtOuterBoundary
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# The inverse strip coordinate `s = (4/π) arctan z` (FIVE-0 slice 4a)

`sInv z = (4/π) arctan z` inverts `sTan s = tan(π s/4)` between the closed strip `0 ≤ Re s ≤ 1` and
`closure Ω ∖ {±i}`: with `q = (1 + iz)/(1 - iz)` (the first-quadrant point `(i-z)/(i+z)`) one has
`Re s = (2/π) arg q`.

* `sTan_sInv`, `sInv_sTan`: mutually inverse;
* `sInv_mem_strip`, `sInv_mem_closedStrip`: `Ω → strip`, `closure Ω ∖ {±i} → closedStrip`;
* `sInv_conj`, `sInv_sigma`: `sInv z̄ = conj (sInv z)`, `sInv σ(z) = 1 - sInv z`;
* holomorphy and continuity.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The inverse strip coordinate. -/
noncomputable def sInv (z : ℂ) : ℂ := (4 / (π : ℂ)) * Complex.arctan z

/-- The first-quadrant point `q = (1 + zi)/(1 - zi)`. -/
noncomputable def qArc (z : ℂ) : ℂ := (1 + z * Complex.I) / (1 - z * Complex.I)

lemma sTan_sInv {z : ℂ} (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) : sTan (sInv z) = z := by
  unfold sTan sInv
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (π : ℂ) * (4 / (π : ℂ) * Complex.arctan z) / 4 = Complex.arctan z := by field_simp
  rw [this]
  exact Complex.tan_arctan h1 h2

lemma sInv_sTan {s : ℂ} (hs : s ∈ closedStrip) : sInv (sTan s) = s := by
  unfold sInv sTan
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hre : ((π : ℂ) * s / 4).re = π * s.re / 4 := re_pi_mul_div_four s
  have h0 : (π : ℂ) * s / 4 ≠ π / 2 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    nlinarith [hs.2, Real.pi_pos]
  rw [Complex.arctan_tan h0 (by rw [hre]; nlinarith [hs.1, Real.pi_pos]) (by rw [hre]; nlinarith [hs.2, Real.pi_pos])]
  field_simp

lemma re_qArc {z : ℂ} : (qArc z).re = (1 - ‖z‖ ^ 2) / ((1 + z.im) ^ 2 + z.re ^ 2) := by
  unfold qArc
  rw [Complex.div_re]
  have hD : Complex.normSq (1 - z * Complex.I) = (1 + z.im) ^ 2 + z.re ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hD, ← add_div, Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp; ring

lemma im_qArc {z : ℂ} : (qArc z).im = 2 * z.re / ((1 + z.im) ^ 2 + z.re ^ 2) := by
  unfold qArc
  rw [Complex.div_im]
  have hD : Complex.normSq (1 - z * Complex.I) = (1 + z.im) ^ 2 + z.re ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hD, ← sub_div]
  congr 1
  simp; ring

lemma one_sub_mul_I_ne_zero {z : ℂ} (hz : z ≠ -Complex.I) : 1 - z * Complex.I ≠ 0 := by
  intro h
  apply hz
  have h1 : z * Complex.I - 1 = 0 := by linear_combination -h
  linear_combination (-Complex.I) * h1 + z * Complex.I_sq

lemma re_sInv {z : ℂ} (hz : 1 - z * Complex.I ≠ 0) (hq : qArc z ≠ 0) :
    (sInv z).re = 2 / π * Complex.arg (qArc z) := by
  unfold sInv Complex.arctan
  rw [← qArc]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (4 / (π : ℂ)) * (-Complex.I / 2 * Complex.log (qArc z)) =
      ((2 / π : ℝ) : ℂ) * (-Complex.I * Complex.log (qArc z)) := by
    push_cast; field_simp; ring
  rw [this, Complex.re_ofReal_mul]
  congr 1
  simp [Complex.log_im]

lemma denom_pos {z : ℂ} (hz : z ≠ -Complex.I) : 0 < (1 + z.im) ^ 2 + z.re ^ 2 := by
  by_contra h
  push Not at h
  have h1 : (1 + z.im) ^ 2 = 0 := by nlinarith [sq_nonneg (1 + z.im), sq_nonneg z.re]
  have h2 : z.re ^ 2 = 0 := by nlinarith [sq_nonneg (1 + z.im), sq_nonneg z.re]
  apply hz
  apply Complex.ext
  · simpa using pow_eq_zero_iff (two_ne_zero) |>.mp h2
  · have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    simp; linarith

lemma qArc_ne_zero {z : ℂ} (hz : z ≠ Complex.I) (hz2 : z ≠ -Complex.I) : qArc z ≠ 0 := by
  unfold qArc
  intro h
  rcases div_eq_zero_iff.mp h with h | h
  · apply hz
    have h1 : z * Complex.I + 1 = 0 := by linear_combination h
    have : z = Complex.I := by
      linear_combination (-Complex.I) * h1 + z * Complex.I_sq + 2 * Complex.I
    exact this
  · exact one_sub_mul_I_ne_zero hz2 h

lemma sInv_mem_closedStrip {z : ℂ} (hz : z ∈ closure halfDisc) (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) :
    sInv z ∈ closedStrip := by
  obtain ⟨hn, hr⟩ := closure_halfDisc_subset hz
  have hD := denom_pos h2
  have hre : 0 ≤ (qArc z).re := by
    rw [re_qArc]
    apply div_nonneg _ hD.le
    nlinarith [norm_nonneg z]
  have him : 0 ≤ (qArc z).im := by
    rw [im_qArc]; positivity
  have hq := qArc_ne_zero h1 h2
  show 0 ≤ (sInv z).re ∧ (sInv z).re ≤ 1
  rw [re_sInv (one_sub_mul_I_ne_zero h2) hq]
  have a1 : 0 ≤ Complex.arg (qArc z) := Complex.arg_nonneg_iff.mpr him
  have a2 : Complex.arg (qArc z) ≤ π / 2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre)
  have hpi := Real.pi_pos
  constructor
  · positivity
  · rw [div_mul_eq_mul_div, div_le_one hpi]; linarith

lemma halfDisc_ne_pm_I {z : ℂ} (hz : z ∈ halfDisc) : z ≠ Complex.I ∧ z ≠ -Complex.I := by
  constructor
  · intro h; have := hz.1; rw [h] at this; simp at this
  · intro h; have := hz.1; rw [h] at this; simp at this

lemma sInv_mem_strip {z : ℂ} (hz : z ∈ halfDisc) : sInv z ∈ strip := by
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hD := denom_pos h2
  have hre : 0 < (qArc z).re := by
    rw [re_qArc]
    apply div_pos _ hD
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z, hz.1]
    linarith
  have him : 0 < (qArc z).im := by
    rw [im_qArc]; have := hz.2; positivity
  have hq := qArc_ne_zero h1 h2
  show 0 < (sInv z).re ∧ (sInv z).re < 1
  rw [re_sInv (one_sub_mul_I_ne_zero h2) hq]
  have a1 : 0 ≤ Complex.arg (qArc z) := Complex.arg_nonneg_iff.mpr him.le
  have a1' : Complex.arg (qArc z) ≠ 0 := by
    intro h
    have := Complex.arg_eq_zero_iff.mp h
    linarith [this.2]
  have a2 : |Complex.arg (qArc z)| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hpi := Real.pi_pos
  constructor
  · have : 0 < Complex.arg (qArc z) := lt_of_le_of_ne a1 (Ne.symm a1')
    positivity
  · rw [div_mul_eq_mul_div, div_lt_one hpi]
    have := (abs_lt.mp a2).2
    linarith

lemma qArc_mem_slit {z : ℂ} (hz : z ∈ closure halfDisc) (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) :
    qArc z ∈ Complex.slitPlane := by
  obtain ⟨hn, hr⟩ := closure_halfDisc_subset hz
  have hD := denom_pos h2
  have hre : 0 ≤ (qArc z).re := by
    rw [re_qArc]; apply div_nonneg _ hD.le; nlinarith [norm_nonneg z]
  have him : 0 ≤ (qArc z).im := by rw [im_qArc]; exact div_nonneg (by linarith) hD.le
  have hq := qArc_ne_zero h1 h2
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  apply hq
  apply Complex.ext
  · simp; linarith [hcon.1]
  · simp; linarith [hcon.2]

lemma differentiableAt_sInv {z : ℂ} (hz : z ∈ closure halfDisc) (h1 : z ≠ Complex.I) (h2 : z ≠ -Complex.I) :
    DifferentiableAt ℂ sInv z := by
  have hq := qArc_mem_slit hz h1 h2
  have hd := one_sub_mul_I_ne_zero h2
  unfold sInv Complex.arctan
  have hqd : DifferentiableAt ℂ (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) hd
  have hl : DifferentiableAt ℂ (fun z : ℂ => Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))) z :=
    hqd.clog hq
  exact (differentiableAt_const _).mul ((differentiableAt_const _).mul hl)

lemma sInv_sigma {z : ℂ} (hz : z ∈ halfDisc) : sInv (sigmaHD z) = 1 - sInv z := by
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hs : sInv z ∈ unitStrip := sInv_mem_strip hz
  have e : sTan (sInv z) = z := sTan_sInv h1 h2
  have hσ : sigmaHD z = sTan (1 - sInv z) := by
    rw [sTan_one_sub hs, e]
  rw [hσ]
  apply sInv_sTan
  exact ⟨by have := hs.2; simp; linarith, by have := hs.1; simp; linarith⟩

lemma qArc_conj {z : ℂ} : qArc (starRingEnd ℂ z) = (starRingEnd ℂ (qArc z))⁻¹ := by
  unfold qArc
  rw [map_div₀, inv_div]
  simp only [map_add, map_sub, map_mul, map_one, Complex.conj_I]
  ring

lemma sInv_conj {z : ℂ} (hz : z ∈ halfDisc) : sInv (starRingEnd ℂ z) = starRingEnd ℂ (sInv z) := by
  obtain ⟨h1, h2⟩ := halfDisc_ne_pm_I hz
  have hq := qArc_mem_slit (subset_closure hz) h1 h2
  have harg : (qArc z).arg ≠ π := Complex.slitPlane_arg_ne_pi hq
  have hqc : (starRingEnd ℂ (qArc z)).arg ≠ π := by
    rw [Complex.arg_conj, if_neg harg]
    intro h
    have := Complex.neg_pi_lt_arg (qArc z)
    linarith [Real.pi_pos]
  unfold sInv Complex.arctan
  rw [← qArc, ← qArc, qArc_conj, Complex.log_inv _ hqc, Complex.log_conj _ harg]
  simp only [map_mul, map_div₀, map_neg, Complex.conj_I]
  have : (starRingEnd ℂ) (4 : ℂ) = 4 := map_ofNat _ 4
  have h2' : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  have hπ : (starRingEnd ℂ) (π : ℂ) = π := Complex.conj_ofReal π
  rw [this, h2', hπ]
  ring

lemma continuousOn_sInv : ContinuousOn sInv (closure halfDisc \ {Complex.I, -Complex.I}) := by
  intro z hz
  have h1 : z ≠ Complex.I := fun h => hz.2 (by simp [h])
  have h2 : z ≠ -Complex.I := fun h => hz.2 (by simp [h])
  exact (differentiableAt_sInv hz.1 h1 h2).continuousAt.continuousWithinAt

end FormalResearch.ModularBootstrap.FiveTerm
