/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj
public import FormalResearch.SignUncertainty.FctSplittingCont
public import FormalResearch.SignUncertainty.FctSplittingEdgeDeriv
public import FormalResearch.SignUncertainty.FctPhiKillSymbol

/-!
# Left-edge `C²` regularity of `Ψ_c` and `Φ̂_c` (`SplittingRest.left_c2`)

Paper I (`constant_terms_five.tex`), `fct:splitting` (2), `left_c2` clause of `SplittingRest`.

* `fctPsi_hasDerivAt_pos`: for `τ > 0`, `(d/dτ) Ψ_c(iτ) = i (A_ε(iτ) - (K₀'/K₀)(iτ) Ψ_c(iτ))` by the FTC
  on `i ∫₀^τ K₀ A_ε(iu) du` (using `s ↦ u/τ` change of variables).
* `fctPsi_contDiffOn_left`: `τ ↦ Ψ_c(iτ)` is `C²` on `{τ : ℝ | τ ≠ 0}` (via `contDiffOn_succ_iff_deriv_of_isOpen`
  on `(0, ∞)` and real symmetry `fctPsi_conj` on `(-∞, 0)`).
* `fctPhiHat_left_c2`: discharges `SplittingRest.left_c2` for `fctPhiHat h` from `FctDescentStmt` (`K₄ ≥ 1`).

Class: `fctPsi_contDiffOn_left` is unconditional in `D_{τ₁}` data (`CompData`), `fctPhiHat_left_c2` is proved
from `FctDescentStmt` (named input).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma fctWarpKA_imag_integrable_half {K4 ε c L1 α : ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    IntervalIntegrable (fun u : ℝ => fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) volume 0 (1 / 2) := by
  obtain ⟨r, M, hr, hM, hbd⟩ := fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) hc hDb
  set r' : ℝ := min r (1 / 2) with hr'
  have hr'pos : 0 < r' := lt_min hr (by norm_num)
  have hr'h : r' ≤ 1 / 2 := min_le_right _ _
  have hcont : ContinuousOn (fun u : ℝ => fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) (Ioc 0 (1 / 2)) := by
    refine (fctWarpKA_continuousOn hc hDc).comp (by fun_prop) fun u hu => ?_
    refine ⟨by simp, by simp, ?_⟩
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hu.1.ne') Complex.I_ne_zero
  have h1 : IntervalIntegrable (fun u : ℝ => fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) volume 0 r' := by
    have hint : IntervalIntegrable (fun u : ℝ => M * u ^ (-(1 / 2 : ℝ))) volume 0 r' :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul M
    refine hint.mono_fun' ?_ ?_
    · rw [Set.uIoc_of_le hr'pos.le]
      exact (hcont.mono (Ioc_subset_Ioc_right hr'h)).aestronglyMeasurable measurableSet_Ioc
    · rw [Set.uIoc_of_le hr'pos.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hun : ‖(u : ℂ) * Complex.I‖ = u := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.1.le, Complex.norm_I, mul_one]
      have hne : (u : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu.1.ne') Complex.I_ne_zero
      have hb := hbd ((u : ℂ) * Complex.I) (by simp) (by simp) hne (by rw [hun]; exact hu.2.trans (min_le_left _ _))
      rwa [hun] at hb
  have h2 : IntervalIntegrable (fun u : ℝ => fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) volume r' (1 / 2) := by
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hr'h]
    exact fun u hu => ⟨hr'pos.trans_le hu.1, hu.2⟩
  simpa using h1.trans h2

private lemma fctWarpKA_imag_contDiffOn {K4 ε c L1 α : ℝ} {P : ℝ → ℝ} (hc : 0 < c)
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) P) :
    ContDiffOn ℝ 2 (fun t : ℝ => fctWarpKA K4 ε c L1 α ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
  have hline : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  have hmemE : ∀ t : ℝ, (t : ℂ) * Complex.I ∈ edgeStrip := fun t => by
    show |((t : ℂ) * Complex.I).re| < 1
    simp
  have hK0 : ContDiff ℝ 2 (fun t : ℝ => mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1)) := by
    rw [← contDiffOn_univ]
    exact ((differentiableOn_mellinK0 hc (fctXi1 L1)).contDiffOn isOpen_edgeStrip |>.restrict_scalars ℝ).comp
      hline.contDiffOn fun t _ => hmemE t
  have hG : ContDiff ℝ 2 (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) := by
    rw [← contDiffOn_univ]
    exact (differentiableOn_stripG.contDiffOn isOpen_edgeStrip |>.restrict_scalars ℝ).comp
      hline.contDiffOn fun t _ => hmemE t
  have hPhiK : ContDiff ℝ 2 (fun t : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)) :=
    (FctSym.contDiff_phiKill_imag (Real.rpow_pos_of_pos hc _)).of_le (by norm_cast)
  have hD : ContDiff ℝ 2 (fun t : ℝ => fctDcompAt K4 c α ((t : ℂ) * Complex.I)) := hEnv.1
  obtain ⟨MZ, hZE⟩ := ejZE ε
  have hHG : ContDiffOn ℝ 2 (fun t : ℝ => ctHG ε ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
    have hprod := (hZE.c2.mul edgeR_EJ.c2).mul edgeS_EJ.c2
    exact hprod.congr fun t _ => ctHG_edge ε t
  have hA : ContDiffOn ℝ 2 (fun t : ℝ => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} :=
    (((hG.add (contDiff_const.mul hPhiK)).mul hD).contDiffOn).mul hHG
  exact (hK0.contDiffOn).mul hA

private lemma fctPsi_eq_integral_of_ne_zero (K4 ε c L1 α : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) =
      (mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1))⁻¹ *
        (Complex.I * ∫ u in (0 : ℝ)..τ, fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)) := by
  unfold fctPsi fctWarpKA
  congr 1
  have hc : (∫ s in (0 : ℝ)..1,
      mellinK0 c ((s : ℂ) * ((τ : ℂ) * Complex.I)) (fctXi1 L1) *
        fctWarpA K4 ε c L1 α ((s : ℂ) * ((τ : ℂ) * Complex.I))) =
      τ⁻¹ • ∫ u in (0 : ℝ)..τ,
        mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1) *
          fctWarpA K4 ε c L1 α ((u : ℂ) * Complex.I) := by
    have h := intervalIntegral.integral_comp_mul_right
      (f := fun u : ℝ => mellinK0 c ((u : ℂ) * Complex.I) (fctXi1 L1) *
        fctWarpA K4 ε c L1 α ((u : ℂ) * Complex.I)) hτ (a := (0 : ℝ)) (b := (1 : ℝ))
    simp only [zero_mul, one_mul, Complex.ofReal_mul, mul_assoc] at h ⊢
    exact h
  rw [hc, Complex.real_smul, Complex.ofReal_inv]
  have htc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  field_simp

/-- **Derivative of `τ ↦ Ψ_c(iτ)` along the positive left edge `τ > 0`**:
`(d/dτ) Ψ_c(iτ) = i (A_ε(iτ) - (K₀'/K₀)(iτ) Ψ_c(iτ))` (`constant_terms_five.tex`, `fct:splitting`). -/
theorem fctPsi_hasDerivAt_pos {K4 ε c L1 α : ℝ} {P : ℝ → ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) P)
    {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I))
      (Complex.I * (fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) -
        (deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I) /
          mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)) *
          fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))) τ := by
  set KA : ℝ → ℂ := fun u => fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)
  have hKA_half : IntervalIntegrable KA volume 0 (1 / 2) := fctWarpKA_imag_integrable_half hc hDc hDb
  have hKA_c2 : ContDiffOn ℝ 2 KA {t : ℝ | t ≠ 0} := fctWarpKA_imag_contDiffOn hc hEnv
  have hKA_cont : ContinuousOn KA (Ioi 0) :=
    hKA_c2.continuousOn.mono fun t ht => ht.ne'
  set J : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, KA u
  have hJ_split : ∀ t ∈ Ioi (0 : ℝ), J t = (∫ u in (0 : ℝ)..(1 / 2), KA u) + ∫ u in (1 / 2)..t, KA u := by
    intro t (ht : 0 < t)
    have h12 : IntervalIntegrable KA volume (1 / 2) t := by
      refine (hKA_cont.mono ?_).intervalIntegrable
      intro x hx
      rw [Set.mem_uIcc] at hx
      show 0 < x
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact (intervalIntegral.integral_add_adjacent_intervals hKA_half h12).symm
  have hJ_hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt J (KA t) t := fun t (ht : 0 < t) => by
    have hm : IntervalIntegrable KA volume (1 / 2) t := by
      refine (hKA_cont.mono ?_).intervalIntegrable
      intro x hx
      rw [Set.mem_uIcc] at hx
      show 0 < x
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hsm : StronglyMeasurableAtFilter KA (𝓝 t) volume :=
      hKA_cont.stronglyMeasurableAtFilter isOpen_Ioi t ht
    have htc : ContinuousAt KA t := hKA_cont.continuousAt (isOpen_Ioi.mem_nhds ht)
    have h_int := intervalIntegral.integral_hasDerivAt_right hm hsm htc
    have h_add := h_int.const_add (∫ u in (0 : ℝ)..(1 / 2), KA u)
    refine h_add.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx using hJ_split x hx
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
  have hK_da : DifferentiableAt ℂ (fun w => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I) :=
    (differentiableOn_mellinK0 hc (fctXi1 L1)).differentiableAt (isOpen_edgeStrip.mem_nhds (by
      show |((τ : ℂ) * Complex.I).re| < 1; simp))
  have hK_hd : HasDerivAt (fun t : ℝ => mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1))
      (deriv (fun w => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I) * Complex.I) τ := by
    have hcomp := (hK_da.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hline
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using hcomp
  have hKne : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) ≠ 0 :=
    mellinK0_ne_zero c (by simp) _
  have hKinv : HasDerivAt (fun t : ℝ => (mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1))⁻¹)
      (-(deriv (fun w => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I) * Complex.I) /
        mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) ^ 2) τ :=
    hK_hd.inv hKne
  have hprod := hKinv.mul ((hJ_hd τ hτ).const_mul Complex.I)
  have hev : (fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)) =ᶠ[𝓝 τ]
      fun t => (mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1))⁻¹ * (Complex.I * J t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with t ht using fctPsi_eq_integral_of_ne_zero K4 ε c L1 α ht.ne'
  refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
  set K0 := mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1)
  set K0' := deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1)) ((τ : ℂ) * Complex.I)
  set A := fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)
  have hpsi_eq : fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) = K0⁻¹ * (Complex.I * J τ) :=
    fctPsi_eq_integral_of_ne_zero K4 ε c L1 α hτ.ne'
  have hKA_eq : KA τ = K0 * A := rfl
  change -(K0' * Complex.I) / K0 ^ 2 * (Complex.I * J τ) + K0⁻¹ * (Complex.I * KA τ) =
    Complex.I * (A - K0' / K0 * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I))
  rw [hKA_eq, hpsi_eq]
  field_simp [hKne]
  ring

/-- **`Ψ_c(iτ)` is `C²` off `0` along the left edge** (`ContDiffOn ℝ 2`). -/
theorem fctPsi_contDiffOn_left {K4 ε c L1 α : ℝ} {P : ℝ → ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hDconj : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) P) :
    ContDiffOn ℝ 2 (fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
  set KA : ℝ → ℂ := fun u => fctWarpKA K4 ε c L1 α ((u : ℂ) * Complex.I)
  have hKA_half : IntervalIntegrable KA volume 0 (1 / 2) := fctWarpKA_imag_integrable_half hc hDc hDb
  have hKA_c2 : ContDiffOn ℝ 2 KA {t : ℝ | t ≠ 0} := fctWarpKA_imag_contDiffOn hc hEnv
  have hKA_cont : ContinuousOn KA (Ioi 0) :=
    hKA_c2.continuousOn.mono fun t ht => ht.ne'
  set J : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, KA u
  have h12_int : ∀ t : ℝ, 0 < t → IntervalIntegrable KA volume (1 / 2) t := fun t ht => by
    refine (hKA_cont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.mem_uIcc] at hx
    show 0 < x
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hJ_split : ∀ t ∈ Ioi (0 : ℝ), J t = (∫ u in (0 : ℝ)..(1 / 2), KA u) + ∫ u in (1 / 2)..t, KA u :=
    fun t (ht : 0 < t) => (intervalIntegral.integral_add_adjacent_intervals hKA_half (h12_int t ht)).symm
  have hJ_hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt J (KA t) t := fun t (ht : 0 < t) => by
    have hsm : StronglyMeasurableAtFilter KA (𝓝 t) volume :=
      hKA_cont.stronglyMeasurableAtFilter isOpen_Ioi t ht
    have htc : ContinuousAt KA t := hKA_cont.continuousAt (isOpen_Ioi.mem_nhds ht)
    have h_int := intervalIntegral.integral_hasDerivAt_right (h12_int t ht) hsm htc
    refine (h_int.const_add (∫ u in (0 : ℝ)..(1 / 2), KA u)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx using hJ_split x hx
  have hJ_c2 : ContDiffOn ℝ 2 J (Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi (n := 1)).2 ?_
    refine ⟨fun t ht => (hJ_hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
    have hKA_1 : ContDiffOn ℝ 1 KA (Ioi 0) :=
      (hKA_c2.of_le (by simp : ((1 : ℕ∞) : WithTop ℕ∞) ≤ 2)).mono fun t (ht : 0 < t) => ht.ne'
    exact ⟨fun h => by simp at h, hKA_1.congr fun t ht => (hJ_hd t ht).deriv⟩
  have hline : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  have hK0_c2 : ContDiff ℝ 2 (fun t : ℝ => mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1)) := by
    rw [← contDiffOn_univ]
    exact ((differentiableOn_mellinK0 hc (fctXi1 L1)).contDiffOn isOpen_edgeStrip |>.restrict_scalars ℝ).comp
      hline.contDiffOn fun t _ => by show |((t : ℂ) * Complex.I).re| < 1; simp
  have hK0inv_c2 : ContDiffOn ℝ 2 (fun t : ℝ => (mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1))⁻¹) (Ioi 0) :=
    (hK0_c2.contDiffOn).inv fun t _ => mellinK0_ne_zero c (by simp) _
  have hpos_c2 : ContDiffOn ℝ 2 (fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)) (Ioi 0) := by
    have hIJ : ContDiffOn ℝ 2 (fun t : ℝ => Complex.I * J t) (Ioi 0) :=
      contDiffOn_const.mul hJ_c2
    exact (hK0inv_c2.mul hIJ).congr fun t (ht : 0 < t) =>
      fctPsi_eq_integral_of_ne_zero K4 ε c L1 α ht.ne'
  have hneg_c2 : ContDiffOn ℝ 2 (fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)) (Iio 0) := by
    have hconj_c2 : ContDiffOn ℝ 2 (Complex.conjCLE : ℂ → ℂ) Set.univ :=
      (Complex.conjCLE.contDiff.contDiffOn (s := Set.univ)).of_le (by norm_cast)
    have hcomp : ContDiffOn ℝ 2 (fun t : ℝ => Complex.conjCLE (fctPsi K4 ε c L1 α (((-t : ℝ) : ℂ) * Complex.I))) (Iio 0) :=
      hconj_c2.comp
        (hpos_c2.comp (contDiff_neg.contDiffOn) fun t (ht : t < 0) => show 0 < -t by linarith)
        fun _ _ => Set.mem_univ _
    refine hcomp.congr fun t (ht : t < 0) => ?_
    have hcj := fctPsi_conj (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) hDconj
      (ζ := ((-t : ℝ) : ℂ) * Complex.I) (by simp) (by simp)
    have harg : starRingEnd ℂ (((-t : ℝ) : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [← harg, hcj]
    rfl
  intro τ hτ
  rcases lt_or_gt_of_ne hτ with hlt | hgt
  · exact (hneg_c2.contDiffAt (isOpen_Iio.mem_nhds hlt)).contDiffWithinAt
  · exact (hpos_c2.contDiffAt (isOpen_Ioi.mem_nhds hgt)).contDiffWithinAt

/-- **`fct:splitting` (2), `left_c2` clause of `SplittingRest`**: for `c ≥ c₀` and `ε = ±1`,
`τ ↦ Φ̂_c(iτ)` is `C²` on `{τ : ℝ | τ ≠ 0}`. Proved from `FctDescentStmt` (`K₄ ≥ 1`). -/
theorem fctPhiHat_left_c2 {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContDiffOn ℝ 2 (fun t : ℝ => fctPhiHat h ε c ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨c0T, hTail⟩ := fctPhiHat_left_tail_EJ hK4 hD
  obtain ⟨c0s, _, hSetup⟩ := fctSplitting_setup hK4 hD
  refine ⟨max c0D (max c0T c0s), fun ε c hε hc => ?_⟩
  have hDD := hcD ε c hε ((le_max_left _ _).trans hc)
  obtain ⟨_, hTail_EJ⟩ := hTail ε c hε ((le_max_left _ _).trans (le_max_right _ _) |>.trans hc)
  obtain ⟨hcpos, _, hDc, hDb, _, hDconj⟩ := hSetup ε c hε ((le_max_right _ _).trans (le_max_right _ _) |>.trans hc)
  obtain ⟨P, _, hEnv⟩ := hDD.env
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  have hPsi_c2 : ContDiffOn ℝ 2 (fun t : ℝ => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} :=
    fctPsi_contDiffOn_left hcpos hDc hDb hDconj hEnv
  obtain ⟨MZ, hZE⟩ := ejZE ε
  have hHG_c2 : ContDiffOn ℝ 2 (fun t : ℝ => ctHG ε ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} :=
    ((hZE.c2.mul edgeR_EJ.c2).mul edgeS_EJ.c2).congr fun t _ => ctHG_edge ε t
  have hden_c2 : ContDiffOn ℝ 2 (fun t : ℝ => fctDcompAt K4 c α ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I))
      {τ : ℝ | τ ≠ 0} := hEnv.1.contDiffOn.mul hHG_c2
  have hden_ne : ∀ t ∈ {τ : ℝ | τ ≠ 0},
      fctDcompAt K4 c α ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I) ≠ 0 := fun t ht =>
    mul_ne_zero (fctDcompAt_ne_zero _) (ctHG_ne_zero_of_closed_band ε (by simp) (by simp)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero))
  have h_cPsi : ContDiffOn ℝ 2 (fun t : ℝ => (c : ℂ) * fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} :=
    contDiffOn_const.mul hPsi_c2
  have hPhiC_c2 : ContDiffOn ℝ 2 (fun t : ℝ => fctPhiC K4 ε c L1 α ((t : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} :=
    (h_cPsi.mul (hden_c2.inv hden_ne)).congr fun _ _ => div_eq_mul_inv _ _
  have hres := ((hPhiC_c2.div_const Nc).add hTail_EJ.c2)
  exact hres.congr fun τ _ => fctPhiHatAt_left_eq_add_tail K4 ε c L1 α τ

/-- info: 'FormalResearch.SignUncertainty.fctPsi_contDiffOn_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_contDiffOn_left

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_left_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_left_c2

end FormalResearch.SignUncertainty
