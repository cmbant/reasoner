/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingCont

/-!
# Abstract horizontal Fubini/FTC identity on `[0, 3/8] × [0, 1]`

Helper module for `FctSplittingPsiFar.lean`: for a holomorphic function `f` on `strip` with an
integrable `O(|t|^{-1/2})` singularity at `0` and continuous ray integrals on `psiDom`,
`z ↦ z ∫₀¹ f(sz) ds` satisfies the horizontal FTC identity between `iτ` and `3/8 + iτ` (`τ > 0`):
`((3/8 + iτ) ∫₀¹ f(s(3/8 + iτ)) ds) - (iτ ∫₀¹ f(s iτ) ds) = ∫₀^{3/8} f(r + iτ) dr`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma strip_half_mem_dom {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 3 / 8) (hτ : 0 < τ) :
    ((r : ℂ) + (τ : ℂ) * Complex.I) ∈ psiDom := by
  refine ⟨by simpa using hr0, by simp; linarith, ?_⟩
  intro h
  have := congr_arg Complex.im h
  simp at this
  linarith

private lemma tendsto_gt_of_continuousOn_Icc {E : Type*} [TopologicalSpace E] {g : ℝ → E}
    {b : ℝ} (hb : 0 < b) (hg : ContinuousOn g (Icc (0 : ℝ) b)) :
    Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := by
  refine (hg.continuousWithinAt ⟨le_rfl, hb.le⟩).mono_left ?_
  rw [nhdsWithin_le_iff, mem_nhdsWithin]
  refine ⟨Iio b, isOpen_Iio, hb, fun x hx => ?_⟩
  exact ⟨hx.2.le, hx.1.le⟩

/-- Horizontal Fubini/FTC identity from `iτ` to `3/8 + iτ` (`τ > 0`) for an abstract holomorphic
function `f` on `strip`. -/
theorem horiz_ftc_gen {f : ℂ → ℂ}
    (hf_hol : DifferentiableOn ℂ f strip)
    (hf_cont : ContinuousOn f {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0})
    (hf_near : ∃ r₀ M₀ : ℝ, 0 < r₀ ∧ 0 ≤ M₀ ∧ ∀ t : ℂ, 0 ≤ t.re → t.re < 1 → t ≠ 0 →
      ‖t‖ ≤ r₀ → ‖f t‖ ≤ M₀ * ‖t‖ ^ (-(1 / 2 : ℝ)))
    (hf_seg : ∀ z : ℂ, 0 ≤ z.re → z.re < 1 → z ≠ 0 →
      IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * z)) volume 0 1)
    (hf_psi_cont : ContinuousOn (fun z : ℂ => ∫ s in (0 : ℝ)..1, f ((s : ℂ) * z)) psiDom)
    {τ : ℝ} (hτ : 0 < τ) :
    ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
      ((τ : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I))) =
      ∫ r in (0 : ℝ)..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I) := by
  have hf_deriv_cont : ContinuousOn (deriv f) strip :=
    (hf_hol.contDiffOn isOpen_strip (n := 2)).continuousOn_deriv_of_isOpen isOpen_strip (by norm_num)
  let Φ : ℝ → ℝ → ℂ := fun r s =>
    f ((s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)) +
      (s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I) *
        deriv f ((s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))
  have hmem_strip : ∀ {r s : ℝ}, 0 < r → r < 1 → 0 < s → s ≤ 1 →
      (s : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I) ∈ strip := fun hr0 hr1 hs0 hs1 => by
    simp only [strip, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.I_re, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.I_im,
      mul_one, zero_add, zero_mul]
    exact ⟨mul_pos hs0 hr0, by nlinarith⟩
  have hbox : ∀ {ε₀ δ : ℝ}, 0 < ε₀ → ε₀ < 3 / 8 → 0 < δ → δ < 1 →
      (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
        (∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))) =
      ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
        ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
    intro ε₀ δ hε0 hε38 hδ0 hδ1
    have hcont_Φ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc ε₀ (3 / 8) ×ˢ Icc δ 1) := by
      have harg : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) * ((p.1 : ℂ) + (τ : ℂ) * Complex.I)) := by
        fun_prop
      have hmap : MapsTo (fun p : ℝ × ℝ => (p.2 : ℂ) * ((p.1 : ℂ) + (τ : ℂ) * Complex.I))
          (Icc ε₀ (3 / 8) ×ˢ Icc δ 1) strip := fun p hp =>
        hmem_strip (hε0.trans_le hp.1.1) (hp.1.2.trans_lt (by norm_num))
          (hδ0.trans_le hp.2.1) hp.2.2
      exact (hf_hol.continuousOn.comp harg.continuousOn hmap).add
        (harg.continuousOn.mul (hf_deriv_cont.comp harg.continuousOn hmap))
    have hInt_prod : Integrable (fun p : ℝ × ℝ => Φ p.1 p.2)
        ((volume.restrict (Ioc ε₀ (3 / 8))).prod (volume.restrict (Ioc δ 1))) := by
      have hIcc : IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc ε₀ (3 / 8) ×ˢ Icc δ 1) :=
        hcont_Φ.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hIoc := hIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hIoc
    have hswap : (∫ r in ε₀..(3 / 8 : ℝ), (∫ s in δ..1, Φ r s)) =
        ∫ s in δ..1, (∫ r in ε₀..(3 / 8 : ℝ), Φ r s) := by
      simp only [intervalIntegral.integral_of_le hε38.le, intervalIntegral.integral_of_le hδ1.le]
      exact integral_integral_swap hInt_prod
    have hLHS_inner : ∀ r ∈ Icc ε₀ (3 / 8),
        (∫ s in δ..1, Φ r s) = f ((r : ℂ) + (τ : ℂ) * Complex.I) -
          (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)) := by
      intro r hr
      have hint_s : IntervalIntegrable (Φ r) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        exact hcont_Φ.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨hr, hs⟩
      have hderiv_s : ∀ s ∈ uIcc δ 1,
          HasDerivAt (fun t : ℝ => (t : ℂ) * f ((t : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
            (Φ r s) s := by
        intro s hs
        rw [uIcc_of_le hδ1.le] at hs
        have hms := hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt (by norm_num))
          (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))
            ((r : ℂ) + (τ : ℂ) * Complex.I) s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ((r : ℂ) + (τ : ℂ) * Complex.I)
        have hcomp := (Complex.ofRealCLM.hasDerivAt (x := s)).mul (hdf.comp s harg)
        refine hcomp.congr_deriv ?_
        simp only [Φ, Complex.ofRealCLM_apply, Function.comp_def, Complex.ofReal_one, one_mul]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_s hint_s]
      simp
    have hRHS_inner : ∀ s ∈ Icc δ 1,
        (∫ r in ε₀..(3 / 8 : ℝ), Φ r s) =
          ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)) -
            ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)) := by
      intro s hs
      have hint_r : IntervalIntegrable (fun r => Φ r s) volume ε₀ (3 / 8) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hε38.le]
        exact hcont_Φ.comp (continuousOn_id.prodMk continuousOn_const) fun r hr => ⟨hr, hs⟩
      have hderiv_r : ∀ r ∈ uIcc ε₀ (3 / 8),
          HasDerivAt (fun x : ℝ => ((x : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((x : ℂ) + (τ : ℂ) * Complex.I)))
            (Φ r s) r := by
        intro r hr
        rw [uIcc_of_le hε38.le] at hr
        have hms := hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt (by norm_num))
          (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have hz_d : HasDerivAt (fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I) 1 r := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).add_const ((τ : ℂ) * Complex.I)
        have harg : HasDerivAt (fun x : ℝ => (s : ℂ) * ((x : ℂ) + (τ : ℂ) * Complex.I))
            (s : ℂ) r := by
          simpa using hz_d.const_mul (s : ℂ)
        have hcomp := hz_d.mul (hdf.comp r harg)
        refine hcomp.congr_deriv ?_
        simp only [Φ, Function.comp_def, one_mul]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_r hint_r]
      norm_num
    have hL : (∫ r in ε₀..(3 / 8 : ℝ), (∫ s in δ..1, Φ r s)) =
        (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
          (∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
      have hc1 : IntervalIntegrable (fun r : ℝ => f ((r : ℂ) + (τ : ℂ) * Complex.I)) volume ε₀ (3 / 8) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hε38.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun r hr => ?_
        simp only [strip, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
        exact ⟨hε0.trans_le hr.1, hr.2.trans_lt (by norm_num)⟩
      have hc2 : IntervalIntegrable (fun r : ℝ => (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
          volume ε₀ (3 / 8) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hε38.le]
        refine continuousOn_const.mul (hf_hol.continuousOn.comp (by fun_prop) fun r hr => ?_)
        exact hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt (by norm_num)) hδ0 hδ1.le
      rw [intervalIntegral.integral_congr (fun r hr => hLHS_inner r (by rwa [uIcc_of_le hε38.le] at hr))]
      exact intervalIntegral.integral_sub hc1 hc2
    have hR : (∫ s in δ..1, (∫ r in ε₀..(3 / 8 : ℝ), Φ r s)) =
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
      have hc1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)))
          volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun s hs => ?_
        simpa using hmem_strip (r := 3 / 8) (s := s) (by norm_num) (by norm_num) (hδ0.trans_le hs.1) hs.2
      have hc2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
          volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun s hs => ?_
        exact hmem_strip (r := ε₀) (s := s) hε0 (by linarith) (hδ0.trans_le hs.1) hs.2
      rw [intervalIntegral.integral_congr (fun s hs => hRHS_inner s (by rwa [uIcc_of_le hδ1.le] at hs))]
      rw [intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hL, hswap, hR]
  have heps_eq : ∀ {ε₀ : ℝ}, 0 < ε₀ → ε₀ < 3 / 8 →
      (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) =
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
    intro ε₀ hε0 hε38
    obtain ⟨r₀, M₀, hr₀, hM₀, hnear⟩ := hf_near
    have hRHS_lim : Tendsto (fun δ : ℝ =>
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))) := by
      have hi1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)))
          volume 0 1 := by
        refine hf_seg _ (by norm_num) (by norm_num) ?_
        intro h0; have := congr_arg Complex.im h0; simp at this; linarith
      have hi2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
          volume 0 1 := by
        refine hf_seg _ (by simpa using hε0.le) (by simp; linarith) ?_
        intro h0; have := congr_arg Complex.im h0; simp at this; linarith
      have hc1 : ContinuousOn (fun x => ∫ s in x..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I)))
          (Icc 0 1) := by
        have hneg : ContinuousOn (fun x => -(∫ s in (1 : ℝ)..x, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))))
            (Icc 0 1) := by
          have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ)) hi1.symm (by simp)
          rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
          exact h.neg
        exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
      have hc2 : ContinuousOn (fun x => ∫ s in x..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))
          (Icc 0 1) := by
        have hneg : ContinuousOn (fun x => -(∫ s in (1 : ℝ)..x, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
            (Icc 0 1) := by
          have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ)) hi2.symm (by simp)
          rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
          exact h.neg
        exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
      exact (tendsto_const_nhds.mul (tendsto_gt_of_continuousOn_Icc one_pos hc1)).sub
        (tendsto_const_nhds.mul (tendsto_gt_of_continuousOn_Icc one_pos hc2))
    have htail_lim : Tendsto (fun δ : ℝ =>
        ∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro e he
      set δ_cap : ℝ := min (1 / 2) (r₀ / (1 + τ))
      have hδ_cap : 0 < δ_cap := lt_min (by norm_num) (div_pos hr₀ (by positivity))
      set K_e : ℝ := (3 / 8) * M₀ * τ ^ (-(1 / 2 : ℝ))
      have hKe : 0 ≤ K_e := by positivity
      refine ⟨min δ_cap ((e / (K_e + 1)) ^ 2), lt_min hδ_cap (pow_pos (div_pos he (by positivity)) 2),
        fun δ hδ hdist => ?_⟩
      have hδpos : 0 < δ := hδ
      rw [Real.dist_eq, sub_zero, abs_of_pos hδpos] at hdist
      have hδ_lt_cap : δ < δ_cap := hdist.trans_le (min_le_left _ _)
      have hδr0 : δ * (1 + τ) ≤ r₀ := by
        have hlt : δ ≤ r₀ / (1 + τ) := hδ_lt_cap.le.trans (min_le_right _ _)
        rwa [le_div_iff₀ (by positivity)] at hlt
      have hbd_int : ∀ r ∈ uIoc ε₀ (3 / 8),
          ‖(δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
            M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
        intro r hr
        rw [uIoc_of_le hε38.le] at hr
        set t : ℂ := (δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)
        have ht_re0 : 0 ≤ t.re := by simp [t]; exact mul_nonneg hδpos.le (by linarith [hr.1])
        have ht_re1 : t.re < 1 := by
          have : δ < 1 := hδ_lt_cap.trans_le ((min_le_left _ _).trans (by norm_num))
          simp [t]; nlinarith [hr.2]
        have ht_ne : t ≠ 0 := by
          intro h0
          have him0 := congr_arg Complex.im h0
          simp [t] at him0
          rcases him0 with h | h
          · exact hδpos.ne' h
          · exact hτ.ne' h
        have hnr : ‖(r : ℂ) + (τ : ℂ) * Complex.I‖ ≤ 1 + τ := by
          have h1 := Complex.norm_le_abs_re_add_abs_im ((r : ℂ) + (τ : ℂ) * Complex.I)
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
            Complex.mul_im, zero_add, abs_of_pos (hε0.trans hr.1), abs_of_pos hτ] at h1
          linarith [hr.2]
        have hnt_hi : ‖t‖ ≤ r₀ := by
          calc ‖t‖ = δ * ‖(r : ℂ) + (τ : ℂ) * Complex.I‖ := by
                simp [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
            _ ≤ δ * (1 + τ) := mul_le_mul_of_nonneg_left hnr hδpos.le
            _ ≤ r₀ := hδr0
        have hnt_lo : δ * τ ≤ ‖t‖ := by
          have := Complex.abs_im_le_norm t
          simpa [t, abs_of_pos hδpos, abs_of_pos hτ] using this
        have hpow : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (δ * τ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hδpos hτ) hnt_lo (by norm_num)
        have hft := hnear t ht_re0 ht_re1 ht_ne hnt_hi
        calc ‖(δ : ℂ) * f t‖ = δ * ‖f t‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
          _ ≤ δ * (M₀ * ‖t‖ ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hft hδpos.le
          _ ≤ δ * (M₀ * (δ * τ) ^ (-(1 / 2 : ℝ))) := by gcongr
          _ = M₀ * τ ^ (-(1 / 2 : ℝ)) * (δ ^ (1 : ℝ) * δ ^ (-(1 / 2 : ℝ))) := by
              rw [Real.mul_rpow hδpos.le hτ.le, Real.rpow_one]; ring
          _ = M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_add hδpos, show (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 by ring]
      have hint_norm := intervalIntegral.norm_integral_le_of_norm_le_const hbd_int
      have hlen : |((3 / 8 : ℝ) - ε₀)| ≤ 3 / 8 := by rw [abs_of_nonneg (by linarith)]; linarith
      have hsqrt : δ ^ (1 / 2 : ℝ) < e / (K_e + 1) := by
        have h1 : δ < (e / (K_e + 1)) ^ 2 := hdist.trans_le (min_le_right _ _)
        rw [← Real.sqrt_eq_rpow]
        exact (Real.sqrt_lt' (div_pos he (by positivity))).mpr h1
      rw [dist_zero_right]
      calc ‖∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))‖
          ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * |3 / 8 - ε₀| := hint_norm
        _ ≤ K_e * δ ^ (1 / 2 : ℝ) := by
            have := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ))
            linarith [show M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * (3 / 8) = K_e * δ ^ (1 / 2 : ℝ) from by ring]
        _ ≤ (K_e + 1) * δ ^ (1 / 2 : ℝ) := by gcongr; linarith
        _ < (K_e + 1) * (e / (K_e + 1)) := mul_lt_mul_of_pos_left hsqrt (by positivity)
        _ = e := by field_simp
    have hLHS_lim : Tendsto (fun δ : ℝ =>
        (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
          (∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
      simpa using tendsto_const_nhds.sub htail_lim
    have hev_eq : (fun δ : ℝ =>
        (∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
          (∫ r in ε₀..(3 / 8 : ℝ), (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun δ : ℝ =>
          ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
              (∫ s in δ..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
            ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
              (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      exact hbox hε0 hε38 hδ.1 hδ.2
    exact tendsto_nhds_unique hLHS_lim (hRHS_lim.congr' hev_eq.symm)
  have hi_r : IntervalIntegrable (fun r : ℝ => f ((r : ℂ) + (τ : ℂ) * Complex.I)) volume 0 (3 / 8) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine hf_cont.comp (by fun_prop) fun r hr => ?_
    exact strip_half_mem_dom hr.1 hr.2 hτ
  have hLHS_lim0 : Tendsto (fun ε₀ : ℝ => ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in (0 : ℝ)..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
    have hc : ContinuousOn (fun x => ∫ r in x..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I))
        (Icc 0 (3 / 8)) := by
      have hneg : ContinuousOn (fun x => -(∫ r in (3 / 8 : ℝ)..x, f ((r : ℂ) + (τ : ℂ) * Complex.I)))
          (Icc 0 (3 / 8)) := by
        have h := intervalIntegral.continuousOn_primitive_interval' (a := (3 / 8 : ℝ)) hi_r.symm (by simp)
        rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 8)] at h
        exact h.neg
      exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
    exact tendsto_gt_of_continuousOn_Icc (by norm_num) hc
  have hPsi_cont : ContinuousOn (fun ε₀ : ℝ => ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
      (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) (Icc (0 : ℝ) (3 / 8)) := by
    have hmap : MapsTo (fun ε₀ : ℝ => (ε₀ : ℂ) + (τ : ℂ) * Complex.I) (Icc (0 : ℝ) (3 / 8)) psiDom :=
      fun ε₀ hε₀ => strip_half_mem_dom hε₀.1 hε₀.2 hτ
    exact (by fun_prop : ContinuousOn (fun ε₀ : ℝ => (ε₀ : ℂ) + (τ : ℂ) * Complex.I) (Icc 0 (3 / 8))).mul
      (hf_psi_cont.comp (by fun_prop) hmap)
  have hRHS_lim0 : Tendsto (fun ε₀ : ℝ =>
      ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
        ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
        ((τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I))))) := by
    have hlim2 : Tendsto (fun ε₀ : ℝ => ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
        (𝓝[>] (0 : ℝ)) (𝓝 (((τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I))))) := by
      simpa using tendsto_gt_of_continuousOn_Icc (by norm_num : (0 : ℝ) < 3 / 8) hPsi_cont
    exact tendsto_const_nhds.sub hlim2
  have hev0 : (fun ε₀ : ℝ => ∫ r in ε₀..(3 / 8 : ℝ), f ((r : ℂ) + (τ : ℂ) * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε₀ : ℝ =>
        ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((3 / 8 : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 8)] with ε₀ hε₀
    exact heps_eq hε₀.1 hε₀.2
  exact (tendsto_nhds_unique hLHS_lim0 (hRHS_lim0.congr' hev0.symm)).symm

end FormalResearch.SignUncertainty
