/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctRayTanLower
public import FormalResearch.SignUncertainty.FctRayHG
public import FormalResearch.SignUncertainty.FctRayAmp
public import FormalResearch.SignUncertainty.FctSplittingHorizFTC
public import FormalResearch.SignUncertainty.FctDescentOfRay

/-!
# Ray closing `(b)` and full `FctRayStmt` / `FctDescentStmt` (`fct:splitting` (1))

Closes step `(b)` of the descent proof in Paper I (`constant_terms_five.tex`, `fct:splitting` (1))
for `f := fctWarpKA K4 ε c L1 α`:
`ζ ∫₀¹ K₀A_ε(sζ) ds = -i ∫₀^∞ K₀A_ε(ζ + is) ds` on `5/16 ≤ ζ.re ≤ 7/16`, `0 ≤ ζ.im`,
by horizontal + vertical Fubini/FTC on `[0, ζ.re] × [0, 1]` and `[0, 1] × [ζ.im, ζ.im + T]`
together with `fctWarpI = 0` (`fctWarpI_pair`) and exponential decay as `T → ∞` (`fctWarpKA_left_ray_bound`).

Combines this with `fctRayP_lower_interior` (`FctRayTanLower`) and
`fctRayW_interior_derivs_and_near_one` (`FctRayAmp`) to prove `FctRayStmt h` unconditionally for any
`h : FctWarpSolveStmt K4`, and hence `FctDescentStmt h` via `fctDescent_of_ray`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

private lemma strip_pt_mem_dom {r τ σ : ℝ} (hσ1 : σ < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ σ) (hτ : 0 < τ) :
    ((r : ℂ) + (τ : ℂ) * Complex.I) ∈ psiDom := by
  refine ⟨by simpa using hr0, by simp; linarith, fun h => ?_⟩
  have := congr_arg Complex.im h
  simp at this
  linarith

private lemma tendsto_gt_of_continuousOn_Icc' {E : Type*} [TopologicalSpace E] {g : ℝ → E}
    {b : ℝ} (hb : 0 < b) (hg : ContinuousOn g (Icc (0 : ℝ) b)) :
    Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := by
  refine (hg.continuousWithinAt ⟨le_rfl, hb.le⟩).mono_left ?_
  rw [nhdsWithin_le_iff, mem_nhdsWithin]
  refine ⟨Iio b, isOpen_Iio, hb, fun x hx => ?_⟩
  exact ⟨hx.2.le, hx.1.le⟩

/-- Horizontal Fubini/FTC identity from `iτ` to `σ + iτ` (`0 < σ < 1`, `τ > 0`) for an abstract
holomorphic function `f` on `strip` with `O(|t|^{-1/2})` growth near `0`. -/
theorem horiz_ftc_gen_pt {f : ℂ → ℂ}
    (hf_hol : DifferentiableOn ℂ f strip)
    (hf_cont : ContinuousOn f {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0})
    (hf_near : ∃ r₀ M₀ : ℝ, 0 < r₀ ∧ 0 ≤ M₀ ∧ ∀ t : ℂ, 0 ≤ t.re → t.re < 1 → t ≠ 0 →
      ‖t‖ ≤ r₀ → ‖f t‖ ≤ M₀ * ‖t‖ ^ (-(1 / 2 : ℝ)))
    (hf_seg : ∀ z : ℂ, 0 ≤ z.re → z.re < 1 → z ≠ 0 →
      IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * z)) volume 0 1)
    (hf_psi_cont : ContinuousOn (fun z : ℂ => ∫ s in (0 : ℝ)..1, f ((s : ℂ) * z)) psiDom)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hτ : 0 < τ) :
    ((σ : ℂ) + (τ : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
      ((τ : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I))) =
      ∫ r in (0 : ℝ)..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I) := by
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
  have hbox : ∀ {ε₀ δ : ℝ}, 0 < ε₀ → ε₀ < σ → 0 < δ → δ < 1 →
      (∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
        (∫ r in ε₀..σ, (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))) =
      ((σ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
        ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
    intro ε₀ δ hε0 hεσ hδ0 hδ1
    have hcont_Φ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc ε₀ σ ×ˢ Icc δ 1) := by
      have harg : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) * ((p.1 : ℂ) + (τ : ℂ) * Complex.I)) := by
        fun_prop
      have hmap : MapsTo (fun p : ℝ × ℝ => (p.2 : ℂ) * ((p.1 : ℂ) + (τ : ℂ) * Complex.I))
          (Icc ε₀ σ ×ˢ Icc δ 1) strip := fun p hp =>
        hmem_strip (hε0.trans_le hp.1.1) (hp.1.2.trans_lt hσ1) (hδ0.trans_le hp.2.1) hp.2.2
      exact (hf_hol.continuousOn.comp harg.continuousOn hmap).add
        (harg.continuousOn.mul (hf_deriv_cont.comp harg.continuousOn hmap))
    have hInt_prod : Integrable (fun p : ℝ × ℝ => Φ p.1 p.2)
        ((volume.restrict (Ioc ε₀ σ)).prod (volume.restrict (Ioc δ 1))) := by
      have hIcc : IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc ε₀ σ ×ˢ Icc δ 1) :=
        hcont_Φ.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hIoc := hIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hIoc
    have hswap : (∫ r in ε₀..σ, (∫ s in δ..1, Φ r s)) =
        ∫ s in δ..1, (∫ r in ε₀..σ, Φ r s) := by
      simp only [intervalIntegral.integral_of_le hεσ.le, intervalIntegral.integral_of_le hδ1.le]
      exact integral_integral_swap hInt_prod
    have hLHS_inner : ∀ r ∈ Icc ε₀ σ,
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
        have hms := hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt hσ1) (hδ0.trans_le hs.1) hs.2
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
        (∫ r in ε₀..σ, Φ r s) =
          ((σ : ℂ) + (τ : ℂ) * Complex.I) * f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I)) -
            ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) * f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)) := by
      intro s hs
      have hint_r : IntervalIntegrable (fun r => Φ r s) volume ε₀ σ := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hεσ.le]
        exact hcont_Φ.comp (continuousOn_id.prodMk continuousOn_const) fun r hr => ⟨hr, hs⟩
      have hderiv_r : ∀ r ∈ uIcc ε₀ σ,
          HasDerivAt (fun x : ℝ => ((x : ℂ) + (τ : ℂ) * Complex.I) *
              f ((s : ℂ) * ((x : ℂ) + (τ : ℂ) * Complex.I)))
            (Φ r s) r := by
        intro r hr
        rw [uIcc_of_le hεσ.le] at hr
        have hms := hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt hσ1) (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have hz_d : HasDerivAt (fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I) 1 r := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).add_const ((τ : ℂ) * Complex.I)
        have harg : HasDerivAt (fun x : ℝ => (s : ℂ) * ((x : ℂ) + (τ : ℂ) * Complex.I)) (s : ℂ) r := by
          simpa using hz_d.const_mul (s : ℂ)
        have hcomp := hz_d.mul (hdf.comp r harg)
        refine hcomp.congr_deriv ?_
        simp only [Φ, Function.comp_def, one_mul]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_r hint_r]
    have hL : (∫ r in ε₀..σ, (∫ s in δ..1, Φ r s)) =
        (∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
          (∫ r in ε₀..σ, (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
      have hc1 : IntervalIntegrable (fun r : ℝ => f ((r : ℂ) + (τ : ℂ) * Complex.I)) volume ε₀ σ := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hεσ.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun r hr => ?_
        simp only [strip, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
        exact ⟨hε0.trans_le hr.1, hr.2.trans_lt hσ1⟩
      have hc2 : IntervalIntegrable (fun r : ℝ => (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))
          volume ε₀ σ := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hεσ.le]
        refine continuousOn_const.mul (hf_hol.continuousOn.comp (by fun_prop) fun r hr => ?_)
        exact hmem_strip (hε0.trans_le hr.1) (hr.2.trans_lt hσ1) hδ0 hδ1.le
      rw [intervalIntegral.integral_congr (fun r hr => hLHS_inner r (by rwa [uIcc_of_le hεσ.le] at hr))]
      exact intervalIntegral.integral_sub hc1 hc2
    have hR : (∫ s in δ..1, (∫ r in ε₀..σ, Φ r s)) =
        ((σ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
      have hc1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun s hs => ?_
        simpa using hmem_strip hσ0 hσ1 (hδ0.trans_le hs.1) hs.2
      have hc2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        refine hf_hol.continuousOn.comp (by fun_prop) fun s hs => ?_
        exact hmem_strip hε0 (hεσ.le.trans_lt hσ1) (hδ0.trans_le hs.1) hs.2
      rw [intervalIntegral.integral_congr (fun s hs => hRHS_inner s (by rwa [uIcc_of_le hδ1.le] at hs))]
      rw [intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hL, hswap, hR]
  have heps_eq : ∀ {ε₀ : ℝ}, 0 < ε₀ → ε₀ < σ →
      (∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) =
        ((σ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) := by
    intro ε₀ hε0 hεσ
    obtain ⟨r₀, M₀, hr₀, hM₀, hnear⟩ := hf_near
    have hRHS_lim : Tendsto (fun δ : ℝ =>
        ((σ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((σ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))) := by
      have hi1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) volume 0 1 := by
        refine hf_seg _ (by simp; exact hσ0.le) (by simp; exact hσ1) ?_
        intro h0; have := congr_arg Complex.im h0; simp at this; linarith
      have hi2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) volume 0 1 := by
        refine hf_seg _ (by simpa using hε0.le) (by simp; linarith) ?_
        intro h0; have := congr_arg Complex.im h0; simp at this; linarith
      have hc1 : ContinuousOn (fun x => ∫ s in x..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) (Icc 0 1) := by
        have hneg : ContinuousOn (fun x => -(∫ s in (1 : ℝ)..x, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))))
            (Icc 0 1) := by
          have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ)) hi1.symm (by simp)
          rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
          exact h.neg
        exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
      have hc2 : ContinuousOn (fun x => ∫ s in x..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))) (Icc 0 1) := by
        have hneg : ContinuousOn (fun x => -(∫ s in (1 : ℝ)..x, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
            (Icc 0 1) := by
          have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ)) hi2.symm (by simp)
          rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
          exact h.neg
        exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
      exact (tendsto_const_nhds.mul (tendsto_gt_of_continuousOn_Icc' one_pos hc1)).sub
        (tendsto_const_nhds.mul (tendsto_gt_of_continuousOn_Icc' one_pos hc2))
    have htail_lim : Tendsto (fun δ : ℝ =>
        ∫ r in ε₀..σ, (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro e he
      set δ_cap : ℝ := min (1 / 2) (r₀ / (1 + τ))
      have hδ_cap : 0 < δ_cap := lt_min (by norm_num) (div_pos hr₀ (by positivity))
      set K_e : ℝ := σ * M₀ * τ ^ (-(1 / 2 : ℝ))
      have hKe : 0 ≤ K_e := by positivity
      refine ⟨min δ_cap ((e / (K_e + 1)) ^ 2), lt_min hδ_cap (pow_pos (div_pos he (by positivity)) 2),
        fun δ hδ hdist => ?_⟩
      have hδpos : 0 < δ := hδ
      rw [Real.dist_eq, sub_zero, abs_of_pos hδpos] at hdist
      have hδ_lt_cap : δ < δ_cap := hdist.trans_le (min_le_left _ _)
      have hδr0 : δ * (1 + τ) ≤ r₀ := by
        have hlt : δ ≤ r₀ / (1 + τ) := hδ_lt_cap.le.trans (min_le_right _ _)
        rwa [le_div_iff₀ (by positivity)] at hlt
      have hbd_int : ∀ r ∈ uIoc ε₀ σ,
          ‖(δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))‖ ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
        intro r hr
        rw [uIoc_of_le hεσ.le] at hr
        set t : ℂ := (δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)
        have ht_re0 : 0 ≤ t.re := by simp [t]; exact mul_nonneg hδpos.le (by linarith [hr.1])
        have ht_re1 : t.re < 1 := by
          have : δ < 1 := hδ_lt_cap.trans_le ((min_le_left _ _).trans (by norm_num))
          simp [t]; nlinarith [hr.2]
        have ht_ne : t ≠ 0 := fun h0 => by
          have him0 := congr_arg Complex.im h0; simp [t] at him0
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
          simpa [t, abs_of_pos hδpos, abs_of_pos hτ] using Complex.abs_im_le_norm t
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
      have hlen : |σ - ε₀| ≤ σ := by rw [abs_of_nonneg (by linarith)]; linarith
      have hsqrt : δ ^ (1 / 2 : ℝ) < e / (K_e + 1) := by
        have h1 : δ < (e / (K_e + 1)) ^ 2 := hdist.trans_le (min_le_right _ _)
        rw [← Real.sqrt_eq_rpow]
        exact (Real.sqrt_lt' (div_pos he (by positivity))).mpr h1
      rw [dist_zero_right]
      calc ‖∫ r in ε₀..σ, (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))‖
          ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * |σ - ε₀| := hint_norm
        _ ≤ K_e * δ ^ (1 / 2 : ℝ) := by
            have := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ))
            linarith [show M₀ * τ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * σ = K_e * δ ^ (1 / 2 : ℝ) from by simp only [K_e]; ring]
        _ ≤ (K_e + 1) * δ ^ (1 / 2 : ℝ) := by gcongr; linarith
        _ < (K_e + 1) * (e / (K_e + 1)) := mul_lt_mul_of_pos_left hsqrt (by positivity)
        _ = e := by field_simp
    have hLHS_lim : Tendsto (fun δ : ℝ =>
        (∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
          (∫ r in ε₀..σ, (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I))))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
      simpa using tendsto_const_nhds.sub htail_lim
    have hev_eq : (fun δ : ℝ =>
        (∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) -
          (∫ r in ε₀..σ, (δ : ℂ) * f ((δ : ℂ) * ((r : ℂ) + (τ : ℂ) * Complex.I)))) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun δ : ℝ =>
          ((σ : ℂ) + (τ : ℂ) * Complex.I) *
              (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
            ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
              (∫ s in δ..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      exact hbox hε0 hεσ hδ.1 hδ.2
    exact tendsto_nhds_unique hLHS_lim (hRHS_lim.congr' hev_eq.symm)
  have hi_r : IntervalIntegrable (fun r : ℝ => f ((r : ℂ) + (τ : ℂ) * Complex.I)) volume 0 σ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hσ0.le]
    refine hf_cont.comp (by fun_prop) fun r hr => strip_pt_mem_dom hσ1 hr.1 hr.2 hτ
  have hLHS_lim0 : Tendsto (fun ε₀ : ℝ => ∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in (0 : ℝ)..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I))) := by
    have hc : ContinuousOn (fun x => ∫ r in x..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) (Icc 0 σ) := by
      have hneg : ContinuousOn (fun x => -(∫ r in σ..x, f ((r : ℂ) + (τ : ℂ) * Complex.I))) (Icc 0 σ) := by
        have h := intervalIntegral.continuousOn_primitive_interval' (a := σ) hi_r.symm (by simp)
        rw [uIcc_comm, uIcc_of_le hσ0.le] at h
        exact h.neg
      exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
    exact tendsto_gt_of_continuousOn_Icc' hσ0 hc
  have hPsi_cont : ContinuousOn (fun ε₀ : ℝ => ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
      (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) (Icc (0 : ℝ) σ) := by
    have hmap : MapsTo (fun ε₀ : ℝ => (ε₀ : ℂ) + (τ : ℂ) * Complex.I) (Icc (0 : ℝ) σ) psiDom :=
      fun ε₀ hε₀ => strip_pt_mem_dom hσ1 hε₀.1 hε₀.2 hτ
    exact (by fun_prop : ContinuousOn (fun ε₀ : ℝ => (ε₀ : ℂ) + (τ : ℂ) * Complex.I) (Icc 0 σ)).mul
      (hf_psi_cont.comp (by fun_prop) hmap)
  have hRHS_lim0 : Tendsto (fun ε₀ : ℝ =>
      ((σ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
        ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((σ : ℂ) + (τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
        ((τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I))))) := by
    have hlim2 : Tendsto (fun ε₀ : ℝ => ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I))))
        (𝓝[>] (0 : ℝ)) (𝓝 (((τ : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((τ : ℂ) * Complex.I))))) := by
      simpa using tendsto_gt_of_continuousOn_Icc' hσ0 hPsi_cont
    exact tendsto_const_nhds.sub hlim2
  have hev0 : (fun ε₀ : ℝ => ∫ r in ε₀..σ, f ((r : ℂ) + (τ : ℂ) * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε₀ : ℝ =>
        ((σ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))) -
          ((ε₀ : ℂ) + (τ : ℂ) * Complex.I) *
            (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((ε₀ : ℂ) + (τ : ℂ) * Complex.I)))) := by
    filter_upwards [Ioo_mem_nhdsGT hσ0] with ε₀ hε₀
    exact heps_eq hε₀.1 hε₀.2
  exact (tendsto_nhds_unique hLHS_lim0 (hRHS_lim0.congr' hev0.symm)).symm

/-- Vertical Fubini/FTC identity along `σ + iv` (`0 < σ < 1`, `0 ≤ y`, `0 < T`):
`G(σ + i(y+T)) - G(σ + iy) = i ∫₀^T f(σ + i(y+s)) ds`, where `G(z) = z ∫₀¹ f(sz) ds`. -/
theorem vert_ftc_gen_pt {f : ℂ → ℂ}
    (hf_hol : DifferentiableOn ℂ f strip)
    (hf_near : ∃ r₀ M₀ : ℝ, 0 < r₀ ∧ 0 ≤ M₀ ∧ ∀ t : ℂ, 0 ≤ t.re → t.re < 1 → t ≠ 0 →
      ‖t‖ ≤ r₀ → ‖f t‖ ≤ M₀ * ‖t‖ ^ (-(1 / 2 : ℝ)))
    (hf_seg : ∀ z : ℂ, 0 ≤ z.re → z.re < 1 → z ≠ 0 →
      IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * z)) volume 0 1)
    {σ y T : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hy : 0 ≤ y) (hT : 0 < T) :
    ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
      ((σ : ℂ) + (y : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) =
      Complex.I * ∫ s in (0 : ℝ)..T, f (((σ : ℂ) + (y : ℂ) * Complex.I) + (s : ℂ) * Complex.I) := by
  have hf_deriv_cont : ContinuousOn (deriv f) strip :=
    (hf_hol.contDiffOn isOpen_strip (n := 2)).continuousOn_deriv_of_isOpen isOpen_strip (by norm_num)
  let Ψ : ℝ → ℝ → ℂ := fun v s =>
    Complex.I * (f ((s : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)) +
      (s : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I) *
        deriv f ((s : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)))
  have hmem_strip : ∀ {v s : ℝ}, 0 < s → s ≤ 1 →
      (s : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I) ∈ strip := fun hs0 hs1 => by
    simp only [strip, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.I_re, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.I_im,
      mul_one, zero_add, zero_mul]
    exact ⟨mul_pos hs0 hσ0, by nlinarith⟩
  have hbox : ∀ {δ : ℝ}, 0 < δ → δ < 1 →
      Complex.I * (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)) -
        Complex.I * (∫ v in y..(y + T), (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))) =
      ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
        ((σ : ℂ) + (y : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) := by
    intro δ hδ0 hδ1
    have hcont_Ψ : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) (Icc y (y + T) ×ˢ Icc δ 1) := by
      have harg : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ) * ((σ : ℂ) + (p.1 : ℂ) * Complex.I)) := by
        fun_prop
      have hmap : MapsTo (fun p : ℝ × ℝ => (p.2 : ℂ) * ((σ : ℂ) + (p.1 : ℂ) * Complex.I))
          (Icc y (y + T) ×ˢ Icc δ 1) strip := fun p hp =>
        hmem_strip (hδ0.trans_le hp.2.1) hp.2.2
      exact continuousOn_const.mul ((hf_hol.continuousOn.comp harg.continuousOn hmap).add
        (harg.continuousOn.mul (hf_deriv_cont.comp harg.continuousOn hmap)))
    have hInt_prod : Integrable (fun p : ℝ × ℝ => Ψ p.1 p.2)
        ((volume.restrict (Ioc y (y + T))).prod (volume.restrict (Ioc δ 1))) := by
      have hIcc : IntegrableOn (fun p : ℝ × ℝ => Ψ p.1 p.2) (Icc y (y + T) ×ˢ Icc δ 1) :=
        hcont_Ψ.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hIoc := hIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hIoc
    have hswap : (∫ v in y..(y + T), (∫ s in δ..1, Ψ v s)) =
        ∫ s in δ..1, (∫ v in y..(y + T), Ψ v s) := by
      simp only [intervalIntegral.integral_of_le (by linarith : y ≤ y + T),
        intervalIntegral.integral_of_le hδ1.le]
      exact integral_integral_swap hInt_prod
    have hLHS_inner : ∀ v ∈ Icc y (y + T),
        (∫ s in δ..1, Ψ v s) = Complex.I * (f ((σ : ℂ) + (v : ℂ) * Complex.I) -
          (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))) := by
      intro v hv
      have hint_s : IntervalIntegrable (Ψ v) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        exact hcont_Ψ.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨hv, hs⟩
      have hderiv_s : ∀ s ∈ uIcc δ 1,
          HasDerivAt (fun t : ℝ => Complex.I * ((t : ℂ) * f ((t : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))))
            (Ψ v s) s := by
        intro s hs
        rw [uIcc_of_le hδ1.le] at hs
        have hms := hmem_strip (v := v) (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))
            ((σ : ℂ) + (v : ℂ) * Complex.I) s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const ((σ : ℂ) + (v : ℂ) * Complex.I)
        have hcomp := ((Complex.ofRealCLM.hasDerivAt (x := s)).mul (hdf.comp s harg)).const_mul Complex.I
        refine hcomp.congr_deriv ?_
        simp only [Ψ, Complex.ofRealCLM_apply, Function.comp_def, Complex.ofReal_one, one_mul]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_s hint_s]
      simp only [Complex.ofReal_one, one_mul]; ring
    have hRHS_inner : ∀ s ∈ Icc δ 1,
        (∫ v in y..(y + T), Ψ v s) =
          ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) * f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)) -
            ((σ : ℂ) + (y : ℂ) * Complex.I) * f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
      intro s hs
      have hint_v : IntervalIntegrable (fun v => Ψ v s) volume y (y + T) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le (by linarith : y ≤ y + T)]
        exact hcont_Ψ.comp (continuousOn_id.prodMk continuousOn_const) fun v hv => ⟨hv, hs⟩
      have hderiv_v : ∀ v ∈ uIcc y (y + T),
          HasDerivAt (fun u : ℝ => ((σ : ℂ) + (u : ℂ) * Complex.I) *
              f ((s : ℂ) * ((σ : ℂ) + (u : ℂ) * Complex.I)))
            (Ψ v s) v := by
        intro v hv
        rw [uIcc_of_le (by linarith : y ≤ y + T)] at hv
        have hms := hmem_strip (v := v) (hδ0.trans_le hs.1) hs.2
        have hdf := (hf_hol.differentiableAt (isOpen_strip.mem_nhds hms)).hasDerivAt
        have hz_d : HasDerivAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * Complex.I) Complex.I v := by
          have h1 := (Complex.ofRealCLM.hasDerivAt (x := v)).mul_const Complex.I
          simpa using h1.const_add (σ : ℂ)
        have harg : HasDerivAt (fun u : ℝ => (s : ℂ) * ((σ : ℂ) + (u : ℂ) * Complex.I))
            ((s : ℂ) * Complex.I) v := hz_d.const_mul (s : ℂ)
        have hcomp := hz_d.mul (hdf.comp v harg)
        refine hcomp.congr_deriv ?_
        simp only [Ψ, Function.comp_def]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_v hint_v]
    have hL : (∫ v in y..(y + T), (∫ s in δ..1, Ψ v s)) =
        Complex.I * (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)) -
          Complex.I * (∫ v in y..(y + T), (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))) := by
      have hc1 : IntervalIntegrable (fun v : ℝ => f ((σ : ℂ) + (v : ℂ) * Complex.I)) volume y (y + T) := by
        refine ContinuousOn.intervalIntegrable ?_
        refine hf_hol.continuousOn.comp (by fun_prop) fun v _ => ?_
        simpa [strip] using ⟨hσ0, hσ1⟩
      have hc2 : IntervalIntegrable (fun v : ℝ => (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)))
          volume y (y + T) := by
        refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (hf_hol.continuousOn.comp (by fun_prop) fun v _ => ?_)
        exact hmem_strip hδ0 hδ1.le
      rw [intervalIntegral.integral_congr (fun v hv => hLHS_inner v (by rwa [uIcc_of_le (by linarith)] at hv))]
      simp_rw [mul_sub]
      rw [intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hR : (∫ s in δ..1, (∫ v in y..(y + T), Ψ v s)) =
        ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
          ((σ : ℂ) + (y : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) := by
      have hc1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        exact hf_hol.continuousOn.comp (by fun_prop) fun s hs => hmem_strip (hδ0.trans_le hs.1) hs.2
      have hc2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) volume δ 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hδ1.le]
        exact hf_hol.continuousOn.comp (by fun_prop) fun s hs => hmem_strip (hδ0.trans_le hs.1) hs.2
      rw [intervalIntegral.integral_congr (fun s hs => hRHS_inner s (by rwa [uIcc_of_le hδ1.le] at hs))]
      rw [intervalIntegral.integral_sub (hc1.const_mul _) (hc2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hL, hswap, hR]
  obtain ⟨r₀, M₀, hr₀, hM₀, hnear⟩ := hf_near
  have hRHS_lim : Tendsto (fun δ : ℝ =>
      ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
        ((σ : ℂ) + (y : ℂ) * Complex.I) *
          (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
        ((σ : ℂ) + (y : ℂ) * Complex.I) *
          (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))))) := by
    have hi1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) volume 0 1 :=
      hf_seg _ (by simp; exact hσ0.le) (by simp; exact hσ1) (fun h0 => by
        have := congr_arg Complex.re h0; simp at this; linarith)
    have hi2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) volume 0 1 :=
      hf_seg _ (by simp; exact hσ0.le) (by simp; exact hσ1) (fun h0 => by
        have := congr_arg Complex.re h0; simp at this; linarith)
    have hc1 : ContinuousOn (fun x => ∫ s in x..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) (Icc 0 1) := by
      have hneg : ContinuousOn (fun x => -(∫ s in (1 : ℝ)..x, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))))
          (Icc 0 1) := by
        have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ)) hi1.symm (by simp)
        rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
        exact h.neg
      exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
    have hc2 : ContinuousOn (fun x => ∫ s in x..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) (Icc 0 1) := by
      have hneg : ContinuousOn (fun x => -(∫ s in (1 : ℝ)..x, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))))
          (Icc 0 1) := by
        have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ)) hi2.symm (by simp)
        rw [uIcc_comm, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
        exact h.neg
      exact hneg.congr fun x _ => by rw [intervalIntegral.integral_symm]
    exact (tendsto_const_nhds.mul (tendsto_gt_of_continuousOn_Icc' one_pos hc1)).sub
      (tendsto_const_nhds.mul (tendsto_gt_of_continuousOn_Icc' one_pos hc2))
  have htail_lim : Tendsto (fun δ : ℝ =>
      Complex.I * (∫ v in y..(y + T), (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    set δ_cap : ℝ := min (1 / 2) (r₀ / (1 + y + T))
    have hδ_cap : 0 < δ_cap := lt_min (by norm_num) (div_pos hr₀ (by positivity))
    set K_e : ℝ := T * M₀ * σ ^ (-(1 / 2 : ℝ))
    have hKe : 0 ≤ K_e := by positivity
    refine ⟨min δ_cap ((e / (K_e + 1)) ^ 2), lt_min hδ_cap (pow_pos (div_pos he (by positivity)) 2),
      fun δ hδ hdist => ?_⟩
    have hδpos : 0 < δ := hδ
    rw [Real.dist_eq, sub_zero, abs_of_pos hδpos] at hdist
    have hδ_lt_cap : δ < δ_cap := hdist.trans_le (min_le_left _ _)
    have hδr0 : δ * (1 + y + T) ≤ r₀ := by
      have hlt : δ ≤ r₀ / (1 + y + T) := hδ_lt_cap.le.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at hlt
    have hbd_int : ∀ v ∈ uIoc y (y + T),
        ‖(δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))‖ ≤ M₀ * σ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
      intro v hv
      rw [uIoc_of_le (by linarith)] at hv
      set t : ℂ := (δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)
      have ht_re0 : 0 ≤ t.re := by simp [t]; positivity
      have ht_re1 : t.re < 1 := by
        have : δ < 1 := hδ_lt_cap.trans_le ((min_le_left _ _).trans (by norm_num))
        simp [t]; nlinarith
      have ht_ne : t ≠ 0 := fun h0 => by
        have hre0 := congr_arg Complex.re h0; simp [t] at hre0
        rcases hre0 with h | h
        · exact hδpos.ne' h
        · exact hσ0.ne' h
      have hnr : ‖(σ : ℂ) + (v : ℂ) * Complex.I‖ ≤ 1 + y + T := by
        have h1 := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + (v : ℂ) * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add, abs_of_pos hσ0, abs_of_nonneg (hy.trans hv.1.le)] at h1
        linarith [hv.2]
      have hnt_hi : ‖t‖ ≤ r₀ := by
        calc ‖t‖ = δ * ‖(σ : ℂ) + (v : ℂ) * Complex.I‖ := by
              simp [t, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
          _ ≤ δ * (1 + y + T) := mul_le_mul_of_nonneg_left hnr hδpos.le
          _ ≤ r₀ := hδr0
      have hnt_lo : δ * σ ≤ ‖t‖ := by
        simpa [t, abs_of_pos hδpos, abs_of_pos hσ0] using Complex.abs_re_le_norm t
      have hpow : ‖t‖ ^ (-(1 / 2 : ℝ)) ≤ (δ * σ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hδpos hσ0) hnt_lo (by norm_num)
      have hft := hnear t ht_re0 ht_re1 ht_ne hnt_hi
      calc ‖(δ : ℂ) * f t‖ = δ * ‖f t‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
        _ ≤ δ * (M₀ * ‖t‖ ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hft hδpos.le
        _ ≤ δ * (M₀ * (δ * σ) ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = M₀ * σ ^ (-(1 / 2 : ℝ)) * (δ ^ (1 : ℝ) * δ ^ (-(1 / 2 : ℝ))) := by
            rw [Real.mul_rpow hδpos.le hσ0.le, Real.rpow_one]; ring
        _ = M₀ * σ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add hδpos, show (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 by ring]
    have hint_norm := intervalIntegral.norm_integral_le_of_norm_le_const hbd_int
    have hlen : |(y + T) - y| = T := by rw [add_sub_cancel_left, abs_of_pos hT]
    have hsqrt : δ ^ (1 / 2 : ℝ) < e / (K_e + 1) := by
      have h1 : δ < (e / (K_e + 1)) ^ 2 := hdist.trans_le (min_le_right _ _)
      rw [← Real.sqrt_eq_rpow]
      exact (Real.sqrt_lt' (div_pos he (by positivity))).mpr h1
    rw [dist_zero_right, norm_mul, Complex.norm_I, one_mul]
    calc ‖∫ v in y..(y + T), (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ M₀ * σ ^ (-(1 / 2 : ℝ)) * δ ^ (1 / 2 : ℝ) * |(y + T) - y| := hint_norm
      _ = K_e * δ ^ (1 / 2 : ℝ) := by rw [hlen]; simp only [K_e]; ring
      _ ≤ (K_e + 1) * δ ^ (1 / 2 : ℝ) := by gcongr; linarith
      _ < (K_e + 1) * (e / (K_e + 1)) := mul_lt_mul_of_pos_left hsqrt (by positivity)
      _ = e := by field_simp
  have hLHS_lim : Tendsto (fun δ : ℝ =>
      Complex.I * (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)) -
        Complex.I * (∫ v in y..(y + T), (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I))))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.I * (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)))) := by
    simpa using tendsto_const_nhds.sub htail_lim
  have hev_eq : (fun δ : ℝ =>
      Complex.I * (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)) -
        Complex.I * (∫ v in y..(y + T), (δ : ℂ) * f ((δ : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ =>
        ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
          ((σ : ℂ) + (y : ℂ) * Complex.I) *
            (∫ s in δ..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)))) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
    exact hbox hδ.1 hδ.2
  have heq_y : ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))) -
      ((σ : ℂ) + (y : ℂ) * Complex.I) *
        (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I))) =
      Complex.I * (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)) :=
    (tendsto_nhds_unique hLHS_lim (hRHS_lim.congr' hev_eq.symm)).symm
  rw [heq_y]
  congr 1
  have hshift : (∫ v in y..(y + T), f ((σ : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ s in (0 : ℝ)..T, f ((σ : ℂ) + ((s + y : ℝ) : ℂ) * Complex.I) := by
    simpa [zero_add, add_comm] using
      (intervalIntegral.integral_comp_add_right (fun v : ℝ => f ((σ : ℂ) + (v : ℂ) * Complex.I)) y (a := 0) (b := T)).symm
  rw [hshift]
  refine intervalIntegral.integral_congr fun s _ => ?_
  congr 1; push_cast; ring

/-- **`(b)` of `fct:splitting` (1)** (`FctRayData.shift`): for `h : FctWarpSolveStmt K4`,
`ζ ∫₀¹ K₀A_ε(sζ) ds = -i ∫₀^∞ K₀A_ε(ζ + is) ds` on `0 < ζ.re ≤ 7/16`, `0 ≤ ζ.im`, `c ≥ c₀`. -/
theorem fctRay_shift_of_solve {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ σ y : ℝ, 0 < σ → σ ≤ 7 / 16 → 0 ≤ y →
        ((σ : ℂ) + (y : ℂ) * Complex.I) *
            ∫ s in (0 : ℝ)..1, mellinK0 c ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)) (fctXi1 (fctWarpL1 h ε c)) *
              fctWarpA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((s : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)) =
          -(Complex.I * ∫ s in Ioi (0 : ℝ),
            fctWarpKA K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c)
              (((σ : ℂ) + (y : ℂ) * Complex.I) + (s : ℂ) * Complex.I)) := by
  set c0_pair : ℝ := h.choose_spec.choose
  obtain ⟨Cz, c0z, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, c0z, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨C_l, c0_left, hCl0, hc0_left, hleft_bd⟩ := fctWarpKA_left_ray_bound hK4 h
  set c₀ : ℝ := max (max c0_pair c0D) (max c0_left 1)
  have hc01 : 1 ≤ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c₀, hc01, fun ε c hε hc σ y hσ0 hσ1 hy => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hc_pair : h.choose_spec.choose ≤ c := hc.trans' ((le_max_left _ _).trans (le_max_left _ _))
  have hcD' := hcD ε c hε (hc.trans' ((le_max_right _ _).trans (le_max_left _ _)))
  have hc_left : c0_left ≤ c := hc.trans' ((le_max_left _ _).trans (le_max_right _ _))
  set L1 : ℝ := fctWarpL1 h ε c
  set α : ℝ := fctWarpAlpha h ε c
  set f : ℂ → ℂ := fctWarpKA K4 ε c L1 α
  set ζ : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hf_hol : DifferentiableOn ℂ f strip := fctWarpKA_differentiableOn hcpos hcD'.hol
  have hf_cont : ContinuousOn f {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} :=
    fctWarpKA_continuousOn hcpos hcD'.cont
  have hf_near : ∃ r₀ M₀ : ℝ, 0 < r₀ ∧ 0 ≤ M₀ ∧ ∀ t : ℂ, 0 ≤ t.re → t.re < 1 → t ≠ 0 →
      ‖t‖ ≤ r₀ → ‖f t‖ ≤ M₀ * ‖t‖ ^ (-(1 / 2 : ℝ)) :=
    fctWarpKA_near_zero hcpos hcD'.bd
  have hf_seg : ∀ z : ℂ, 0 ≤ z.re → z.re < 1 → z ≠ 0 →
      IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * z)) volume 0 1 := fun _ hz0 hz1 _ =>
    fctWarpKA_segment_integrable (K4 := K4) (ε := ε) (L1 := L1) (α := α) hcpos hcD'.cont hcD'.bd hz0 hz1
  have hf_psi_cont : ContinuousOn (fun z : ℂ => ∫ s in (0 : ℝ)..1, f ((s : ℂ) * z)) psiDom :=
    fctPsi_integral_continuousOn hcpos hcD'.cont hcD'.bd
  have hrel : ∀ T : ℝ, 1 ≤ T →
      ζ * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ζ)) =
        ((y + T : ℝ) : ℂ) * Complex.I * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I))) +
          (∫ r in (0 : ℝ)..σ, f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)) -
            Complex.I * ∫ s in (0 : ℝ)..T, f (ζ + (s : ℂ) * Complex.I) := fun T hT => by
    have hV := vert_ftc_gen_pt (σ := σ) (y := y) (T := T) hf_hol hf_near hf_seg
      (by linarith) (by linarith) hy (by linarith)
    have hH := horiz_ftc_gen_pt (σ := σ) (τ := y + T) hf_hol hf_cont hf_near hf_seg hf_psi_cont
      (by linarith) (by linarith) (by linarith : 0 < y + T)
    linear_combination -hV + hH
  -- 1. `G(i(y+T)) → fctWarpI = 0`
  have hI_pair : FctWarpZero K4 ε c L1 α := (fctWarpPair_spec h hε hc_pair).2
  have hG0_lim : Tendsto (fun T : ℝ =>
      ((y + T : ℝ) : ℂ) * Complex.I * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I))))
      atTop (𝓝 0) := by
    have hEq : ∀ T : ℝ, 1 ≤ T →
        ((y + T : ℝ) : ℂ) * Complex.I * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I))) =
          Complex.I * ∫ u in (0 : ℝ)..(y + T), fctWarpIntegrand K4 ε c L1 α u := by
      intro T hT
      have hsub := intervalIntegral.integral_comp_mul_right (fun u : ℝ => fctWarpIntegrand K4 ε c L1 α u)
        (show y + T ≠ 0 by linarith) (a := (0 : ℝ)) (b := (1 : ℝ))
      rw [zero_mul, one_mul, Complex.real_smul, Complex.ofReal_inv] at hsub
      have hsub' : ((y + T : ℝ) : ℂ) * ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * (y + T)) =
          ∫ u in (0 : ℝ)..(y + T), fctWarpIntegrand K4 ε c L1 α u := by
        rw [hsub]
        have hne : ((y + T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
        field_simp [hne]
      have harg : (∫ s in (0 : ℝ)..1, f ((s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I))) =
          ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * (y + T)) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [f, fctWarpKA, fctWarpIntegrand]
        rw [show (s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I) = ((s * (y + T) : ℝ) : ℂ) * Complex.I by
          rw [Complex.ofReal_mul, mul_assoc]]
      rw [harg]
      calc ((y + T : ℝ) : ℂ) * Complex.I * (∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * (y + T)))
          = Complex.I * (((y + T : ℝ) : ℂ) * ∫ s in (0 : ℝ)..1, fctWarpIntegrand K4 ε c L1 α (s * (y + T))) := by ring
        _ = Complex.I * ∫ u in (0 : ℝ)..(y + T), fctWarpIntegrand K4 ε c L1 α u := congr_arg (Complex.I * ·) hsub'
    have htend_Ioi := intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ)) hI_pair.1
      (tendsto_atTop_add_const_left atTop y tendsto_id)
    have htend0 : Tendsto (fun T : ℝ => Complex.I * ∫ u in (0 : ℝ)..(y + T), fctWarpIntegrand K4 ε c L1 α u)
        atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := Complex.I)).mul htend_Ioi
      rwa [← show fctWarpI K4 ε c L1 α = Complex.I * ∫ u in Ioi (0 : ℝ), fctWarpIntegrand K4 ε c L1 α u from rfl,
        hI_pair.2] at this
    exact htend0.congr' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT; exact (hEq T hT).symm)
  -- 2. Horizontal top side `∫ r in 0..σ, f(r + i(y+T)) → 0`
  have hN_comp : ContinuousOn (fun r : ℝ => fctRayN K4 ε c L1 α ((r : ℂ) + Complex.I)) (Icc 0 (7 / 16)) := by
    have hmap : MapsTo (fun r : ℝ => (r : ℂ) + Complex.I) (Icc (0 : ℝ) (7 / 16))
        {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} := fun r hr =>
      ⟨by simpa using hr.1, by simp; linarith [hr.2], fun h => by
        have := congr_arg Complex.im h; simp at this⟩
    have hK0 : ContinuousOn (fun t : ℂ => mellinK0 c t (fctXi1 L1)) {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} :=
      (differentiableOn_mellinK0 hcpos _).continuousOn.mono fun t ht => by
        show |t.re| < 1; rw [abs_lt]; constructor <;> linarith [ht.1, ht.2.1]
    have hD : ContinuousOn (fctDcompAt K4 c α) {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} :=
      hcD'.cont.mono fun t ht => ⟨ht.1, ht.2.1.le⟩
    have hH : ContinuousOn (ctHG ε) {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} :=
      (ctHG_continuousOn ε).mono fun t ht => ⟨⟨ht.1, ht.2.1.le⟩, ht.2.2, fun h => by
        have := ht.2.1; rw [h] at this; simp at this⟩
    have hN : ContinuousOn (fctRayN K4 ε c L1 α) {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} := by
      unfold fctRayN; exact (hK0.mul hD).mul hH
    exact hN.comp (by fun_prop) hmap
  obtain ⟨MN, hMN⟩ := isCompact_Icc.exists_bound_of_continuousOn hN_comp
  have hHoriz_lim : Tendsto (fun T : ℝ => ∫ r in (0 : ℝ)..σ, f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    have hbd_T : ∀ T : ℝ, 1 ≤ T →
        ‖∫ r in (0 : ℝ)..σ, f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)‖ ≤
          σ * C_l * |MN| * (1 + y + T) * Real.exp (-2 * (y + T - 1)) := by
      intro T hT
      have hconst : ∀ r ∈ uIoc 0 σ,
          ‖f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)‖ ≤
            C_l * |MN| * (1 + y + T) * Real.exp (-2 * (y + T - 1)) := by
        intro r hr
        rw [uIoc_of_le (by linarith)] at hr
        have hleft := hleft_bd ε c hε hc_left ((r : ℂ) + Complex.I) (by simp; exact hr.1.le)
          (by simp; linarith [hr.2]) (by simp) (y + T - 1) (by linarith)
        have heqpt : ((r : ℂ) + Complex.I) + ((y + T - 1 : ℝ) : ℂ) * Complex.I =
            (r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [heqpt] at hleft
        have hnr : ‖fctRayN K4 ε c L1 α ((r : ℂ) + Complex.I)‖ ≤ |MN| :=
          (hMN r ⟨hr.1.le, hr.2.trans hσ1⟩).trans (le_abs_self MN)
        have him_sum : (1 + ((r : ℂ) + Complex.I).im + (y + T - 1)) = 1 + y + T := by simp; ring
        rw [him_sum] at hleft
        calc ‖f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)‖
            ≤ C_l * (1 + y + T) * Real.exp (-2 * (y + T - 1)) * ‖fctRayN K4 ε c L1 α ((r : ℂ) + Complex.I)‖ := hleft
          _ ≤ C_l * (1 + y + T) * Real.exp (-2 * (y + T - 1)) * |MN| := by gcongr
          _ = C_l * |MN| * (1 + y + T) * Real.exp (-2 * (y + T - 1)) := by ring
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const hconst
      have hlen : |σ - 0| = σ := by rw [sub_zero, abs_of_pos (by linarith)]
      rw [hlen] at hint
      exact hint.trans_eq (by ring)
    have hlim_env' : Tendsto (fun T : ℝ => σ * C_l * |MN| * (1 + y + T) * Real.exp (-2 * (y + T - 1)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => (1 + u) * Real.exp (-(2 * u))) atTop (𝓝 0) := by
        have hlin : (fun u : ℝ => (1 + u) * Real.exp (-(2 * u))) =
            fun u => u ^ (0 : ℝ) * Real.exp (-(2 * u)) + u ^ (1 : ℝ) * Real.exp (-(2 * u)) := by
          ext u; simp [Real.rpow_zero, Real.rpow_one]; ring
        rw [hlin]
        simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 2 (by norm_num)).add
          (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 2 (by norm_num))
      have hcomp := (h1.comp (tendsto_atTop_add_const_left atTop y tendsto_id)).const_mul
        (σ * C_l * |MN| * Real.exp 2)
      refine (hcomp.congr fun T => ?_).trans (by simp)
      dsimp only [Function.comp_def, id_def]
      have hexp : Real.exp 2 * Real.exp (-(2 * (y + T))) = Real.exp (-2 * (y + T - 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc σ * C_l * |MN| * Real.exp 2 * ((1 + (y + T)) * Real.exp (-(2 * (y + T))))
          = σ * C_l * |MN| * (1 + y + T) * (Real.exp 2 * Real.exp (-(2 * (y + T)))) := by ring
        _ = σ * C_l * |MN| * (1 + y + T) * Real.exp (-2 * (y + T - 1)) := by rw [hexp]
    exact squeeze_zero_norm' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT; exact hbd_T T hT) hlim_env'
  -- 3. Vertical ray integral `∫ s in 0..T, f(ζ + is) → ∫ s in Ioi 0, f(ζ + is)`
  have hRay_int : IntegrableOn (fun s : ℝ => f (ζ + (s : ℂ) * Complex.I)) (Ioi 0) := by
    have hcont_ray : ContinuousOn (fun s : ℝ => f (ζ + (s : ℂ) * Complex.I)) (Ici 0) :=
      hf_cont.comp (by fun_prop) fun s _ => ⟨by simp [ζ]; linarith, by simp [ζ]; linarith,
        fun h0 => by have := congr_arg Complex.re h0; simp [ζ] at this; linarith⟩
    have hIoc : IntegrableOn (fun s : ℝ => f (ζ + (s : ℂ) * Complex.I)) (Ioc 0 1) :=
      ((hcont_ray.mono (fun _ (hx : _ ∈ Icc (0 : ℝ) 1) => hx.1)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hIoi1 : IntegrableOn (fun s : ℝ => f (ζ + (s : ℂ) * Complex.I)) (Ioi 1) := by
      set B_r : ℝ := C_l * (2 + y) * ‖fctRayN K4 ε c L1 α (ζ + Complex.I)‖ * Real.exp 1
      have hdom_int : IntegrableOn (fun s : ℝ => B_r * Real.exp (-s)) (Ioi 1) :=
        ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 1).congr_fun
          (fun x _ => by simp) measurableSet_Ioi).const_mul B_r
      refine hdom_int.mono'
        ((hcont_ray.mono (fun _ (hx : _ ∈ Ioi (1 : ℝ)) => le_of_lt (zero_lt_one.trans hx))).aestronglyMeasurable
          measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs1 : 1 < s := hs
      have hleft := hleft_bd ε c hε hc_left (ζ + Complex.I) (by simp [ζ]; linarith) (by simp [ζ]; linarith)
        (by simp [ζ]; linarith) (s - 1) (by linarith)
      have heqs : (ζ + Complex.I) + ((s - 1 : ℝ) : ℂ) * Complex.I = ζ + (s : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [heqs] at hleft
      have hpoly : 1 + (ζ + Complex.I).im + (s - 1) ≤ (2 + y) * Real.exp (s - 1) := by
        have h1 : 1 + (ζ + Complex.I).im + (s - 1) = (2 + y) + (s - 1) := by simp [ζ]; ring
        have hexp : 1 + (s - 1) ≤ Real.exp (s - 1) := by linarith [Real.add_one_le_exp (s - 1)]
        have h2y : (1 : ℝ) ≤ 2 + y := by linarith
        calc 1 + (ζ + Complex.I).im + (s - 1) = (2 + y) + (s - 1) := h1
          _ ≤ (2 + y) * (1 + (s - 1)) := by nlinarith
          _ ≤ (2 + y) * Real.exp (s - 1) := mul_le_mul_of_nonneg_left hexp (by linarith)
      have hmul := hleft.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hCl0) (Real.exp_pos _).le) (norm_nonneg _))
      refine hmul.trans_eq ?_
      have hexp2 : Real.exp (s - 1) * Real.exp (-2 * (s - 1)) = Real.exp 1 * Real.exp (-s) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc C_l * ((2 + y) * Real.exp (s - 1)) * Real.exp (-2 * (s - 1)) * ‖fctRayN K4 ε c L1 α (ζ + Complex.I)‖
          = C_l * (2 + y) * ‖fctRayN K4 ε c L1 α (ζ + Complex.I)‖ *
              (Real.exp (s - 1) * Real.exp (-2 * (s - 1))) := by ring
        _ = B_r * Real.exp (-s) := by rw [hexp2]; simp only [B_r]; ring
    simpa [Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)] using hIoc.union hIoi1
  have hRay_lim : Tendsto (fun T : ℝ =>
      -(Complex.I * ∫ s in (0 : ℝ)..T, f (ζ + (s : ℂ) * Complex.I)))
      atTop (𝓝 (-(Complex.I * ∫ s in Ioi (0 : ℝ), f (ζ + (s : ℂ) * Complex.I)))) :=
    ((tendsto_const_nhds (x := Complex.I)).mul (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ)) hRay_int tendsto_id)).neg
  have hRHS_lim : Tendsto (fun T : ℝ =>
      ((y + T : ℝ) : ℂ) * Complex.I * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I))) +
        (∫ r in (0 : ℝ)..σ, f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)) -
          Complex.I * ∫ s in (0 : ℝ)..T, f (ζ + (s : ℂ) * Complex.I))
      atTop (𝓝 (-(Complex.I * ∫ s in Ioi (0 : ℝ), f (ζ + (s : ℂ) * Complex.I)))) := by
    have h0 := (hG0_lim.add hHoriz_lim).add hRay_lim
    rw [zero_add, zero_add] at h0
    simpa only [sub_eq_add_neg] using h0
  have hev_const : (fun _ : ℝ => ζ * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * ζ))) =ᶠ[atTop]
      (fun T : ℝ =>
        ((y + T : ℝ) : ℂ) * Complex.I * (∫ s in (0 : ℝ)..1, f ((s : ℂ) * (((y + T : ℝ) : ℂ) * Complex.I))) +
          (∫ r in (0 : ℝ)..σ, f ((r : ℂ) + ((y + T : ℝ) : ℂ) * Complex.I)) -
            Complex.I * ∫ s in (0 : ℝ)..T, f (ζ + (s : ℂ) * Complex.I)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact hrel T hT
  have heq := tendsto_nhds_unique tendsto_const_nhds (hRHS_lim.congr' hev_const.symm)
  simpa [ζ, f, fctWarpKA] using heq

/-- **`FctRayStmt h` unconditionally** (`fct:splitting` (1), steps (a)-(e)) for any `h : FctWarpSolveStmt K4`. -/
theorem fctRayStmt_uncond {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) : FctRayStmt h := by
  obtain ⟨c0s, hc0s1, hshift⟩ := fctRay_shift_of_solve hK4 h
  obtain ⟨q0, Lmax, hq0, hLmax, hphase⟩ := fctRayP_lower_interior
  obtain ⟨CL1, c0L1, hCL10, hc0L1, hL1_bd⟩ := abs_fctWarpL1_le h
  obtain ⟨B0, c0w, hBw0, hc0w1, hW⟩ := fctRayW_interior_derivs_and_near_one hK4 h
  set c_L_th : ℝ := (|CL1| / Lmax + 1) ^ 2
  set c₀ : ℝ := max (max c0s (max c0L1 c_L_th)) (max c0w 1)
  have hc01 : 1 ≤ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B0, q0, c₀, hq0, fun ε c hε hc σ y hσ0 hσ1 hy => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' hc01
  have hcpos : 0 < c := by linarith
  have hsh := hshift ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_left _ _))) σ y (by linarith) hσ1 hy
  have hL1c := hL1_bd ε c hε (hc.trans' (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)))
  have hL1_le : |fctWarpL1 h ε c| ≤ Lmax := by
    have hsq : (|CL1| / Lmax + 1) ^ 2 ≤ c :=
      hc.trans' (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
    have hsqrt : |CL1| / Lmax + 1 ≤ c ^ (2 / 3 : ℝ) := by
      have := Real.le_sqrt_of_sq_le hsq
      rw [Real.sqrt_eq_rpow] at this
      exact this.trans (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num))
    have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hcpos _
    have hcl_le : CL1 ≤ |CL1| := le_abs_self _
    have hmul : CL1 ≤ Lmax * c ^ (2 / 3 : ℝ) := by
      have h0 : |CL1| ≤ Lmax * (|CL1| / Lmax + 1) := by
        rw [mul_add, mul_div_cancel₀ _ hLmax.ne']; linarith [hLmax]
      exact hcl_le.trans (h0.trans (mul_le_mul_of_nonneg_left hsqrt hLmax.le))
    have hdiv : CL1 * c ^ (-(2 / 3 : ℝ)) ≤ Lmax := by
      rw [Real.rpow_neg hcpos.le, ← div_eq_mul_inv, div_le_iff₀ hc23]
      exact hmul
    exact hL1c.trans hdiv
  have hW' := hW ε c hε (hc.trans' ((le_max_left _ _).trans (le_max_right _ _)))
    ((σ : ℂ) + (y : ℂ) * Complex.I) (by simp; exact hσ0) (by simp; exact hσ1) (by simp; exact hy)
  refine ⟨hsh, ?_, fun s hs => (hW'.1 s hs).1, fun s hs => (hW'.1 s hs).2.1, fun s hs => (hW'.1 s hs).2.2, hW'.2⟩
  intro s hs
  have hz_eq : ((σ : ℂ) + ((y + s : ℝ) : ℂ) * Complex.I) =
      ((σ : ℂ) + (y : ℂ) * Complex.I) + (s : ℂ) * Complex.I := by
    push_cast; ring
  have him_eq : ((σ : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have hlog_le : Real.log (2 + y) ≤ Real.log (2 + (y + s)) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [him_eq]
  calc q0 * Real.log (2 + y) ≤ q0 * Real.log (2 + (y + s)) := by gcongr
    _ ≤ ‖fctRayP (fctWarpL1 h ε c) ((σ : ℂ) + ((y + s : ℝ) : ℂ) * Complex.I)‖ :=
        hphase (fctWarpL1 h ε c) hL1_le σ (y + s) hσ0 hσ1 (by linarith)
    _ = ‖fctRayP (fctWarpL1 h ε c) (((σ : ℂ) + (y : ℂ) * Complex.I) + (s : ℂ) * Complex.I)‖ := by
        rw [hz_eq]

/-- **Unconditional `(fct:F-38-bnd)`** (`FctDescentStmt h`) from `fct:warp-asymp` (1) (`K₄ ≥ 1`). -/
theorem fctDescent_uncond {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) : FctDescentStmt h :=
  fctDescent_of_ray hK4 (fctRayStmt_uncond hK4 h)

/-- info: 'FormalResearch.SignUncertainty.fctRay_shift_of_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRay_shift_of_solve

/-- info: 'FormalResearch.SignUncertainty.fctRayStmt_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctRayStmt_uncond

/-- info: 'FormalResearch.SignUncertainty.fctDescent_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctDescent_uncond

end FormalResearch.SignUncertainty
