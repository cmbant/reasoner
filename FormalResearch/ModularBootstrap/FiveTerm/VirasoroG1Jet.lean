module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Deriv

/-!
# The slope `g₁ = Gout'(0)` in terms of the slope of `h̄_a` at `0` (FIVE-0, `ctu:jets`, step 1)

Near the tip `Gout = exp ∘ L` with `L z = H(s(z)) + ½ log(1-z) - 2 log(1+z) - ¼ log tipExt z`, `H` the local
holomorphic extension of `h̄_a` at `s = 0`.  Hence
`g₁ = (4/π) H'(0) - 5/2 + √2/π`, where `H'(0) = lim_{ε → 0⁺} (Re h̄_a(ε) - a(0))/ε`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The logarithm of `Gout` near the tip, with the edge extension `H` of `h̄_a`. -/
noncomputable def Lloc (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  H (sInv z) + Complex.log (1 - z) / 2 - 2 * Complex.log (1 + z) - Complex.log (tipExt z) / 4

lemma exists_local_radius {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ (∀ z : ℂ, ‖z‖ < ρ → sInv z ∈ ball (0 : ℂ) δ) ∧
      (∀ z : ℂ, ‖z‖ < ρ → 0 < (tipExt z).re) := by
  have hsI0 : ContinuousAt sInv 0 := (differentiableAt_sInv_ball (by simp)).continuousAt
  obtain ⟨ρ1, hρ1, hS⟩ := Metric.continuousAt_iff.mp hsI0 δ hδ
  have hT0 : ContinuousAt tipExt 0 :=
    differentiableOn_tipExt.continuousOn.continuousAt (isOpen_ball.mem_nhds (by simp))
  have ht0 : 0 < π / 2 / Real.arsinh 1 := by have := arsinh_one_pos; positivity
  obtain ⟨ρ2, hρ2, hT⟩ := Metric.continuousAt_iff.mp hT0 (π / 2 / Real.arsinh 1) ht0
  refine ⟨min (min ρ1 ρ2) (1 / 4), lt_min (lt_min hρ1 hρ2) (by norm_num), min_le_right _ _, ?_, ?_⟩
  · intro z hz
    have := hS (x := z) (by
      rw [dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _)))
    rw [sInv_zero, dist_zero_right] at this
    simpa using this
  · intro z hz
    have := hT (x := z) (by
      rw [dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _)))
    rw [tipExt_zero, dist_eq_norm] at this
    have h2 : ‖tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)‖ < π / 2 / Real.arsinh 1 := this
    have h3 : |(tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)).re| ≤
        ‖tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    have h4 : (tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)).re = (tipExt z).re - π / 2 / Real.arsinh 1 := by
      simp
    rw [h4] at h3
    have := (abs_lt.mp (lt_of_le_of_lt h3 h2)).1
    linarith

lemma gout_eq_exp_Lloc {H : ℂ → ℂ} {δ ρ : ℝ} (hH0 : DifferentiableOn ℂ H (ball (Complex.I * ((0 : ℝ) : ℂ)) δ))
    (heq0 : ∀ ζ ∈ strip, ζ ∈ ball (Complex.I * ((0 : ℝ) : ℂ)) δ → genH aAmp ζ = H ζ)
    (hρ4 : ρ ≤ 1 / 4) (hsI : ∀ z : ℂ, ‖z‖ < ρ → sInv z ∈ ball (0 : ℂ) δ)
    (hT : ∀ z : ℂ, ‖z‖ < ρ → 0 < (tipExt z).re) :
    ∀ z ∈ closure halfDisc, ‖z‖ < ρ → Gout z = Complex.exp (Lloc H z) := by
  intro z hz hzn
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have hz4 : ‖z‖ < 1 / 4 := by linarith
  have hz1 : ‖z‖ < 1 := by linarith
  have hI : z ≠ Complex.I := by intro h; rw [h] at hz4; simp at hz4; linarith
  have hI' : z ≠ -Complex.I := by intro h; rw [h] at hz4; simp at hz4; linarith
  have hs : sInv z ∈ closedStrip := sInv_mem_closedStrip hz hI hI'
  have hb : hbarA aAmp (sInv z) = H (sInv z) := by
    refine hbarA_eq_local hH0 heq0 ?_ hs
    rw [hc]; exact hsI z hzn
  have h1 : (1 - z) ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz1; simp at hz1
  have h2 : (1 + z) ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this] at hz1; simp at hz1
  have h3 : tipExt z ≠ 0 := by
    intro h
    have := hT z hzn
    rw [h] at this; simp at this
  unfold Gout
  rw [hb, qBd_eq_tipExt hz hz4]
  unfold Lloc
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h3]
  have e2 : ((1 + z) ^ 2)⁻¹ = Complex.exp (-(2 * Complex.log (1 + z))) := by
    rw [Complex.exp_neg, show (2 : ℂ) * Complex.log (1 + z) = ((2 : ℕ) : ℂ) * Complex.log (1 + z) by norm_num,
      Complex.exp_nat_mul, Complex.exp_log h2]
  rw [div_eq_mul_inv, e2, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- `deriv H 0` is the one-sided real slope of `h̄_a` at `0`. -/
lemma deriv_H_eq {H : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hH0 : DifferentiableOn ℂ H (ball (Complex.I * ((0 : ℝ) : ℂ)) δ))
    (heq0 : ∀ ζ ∈ strip, ζ ∈ ball (Complex.I * ((0 : ℝ) : ℂ)) δ → genH aAmp ζ = H ζ) {d : ℝ}
    (hd : Tendsto (fun ε : ℝ => ((hbarA aAmp (ε : ℂ)).re - aAmp 0) / ε) (𝓝[>] 0) (𝓝 d)) :
    deriv H 0 = (d : ℂ) ∧ H 0 = ((aAmp 0 : ℝ) : ℂ) := by
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  rw [hc] at hH0
  have hcl0 : (0 : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  have hH00 : H 0 = ((aAmp 0 : ℝ) : ℂ) := by
    have h := hbarA_eq_local (a := aAmp) (y₀ := 0) (H := H) (ζ' := 0) (by rw [hc]; exact hH0)
      heq0 (by rw [hc]; exact mem_ball_self hδ) hcl0
    rw [← h]; exact hbarA_zero
  have hHd : HasDerivAt H (deriv H 0) 0 :=
    (hH0.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).hasDerivAt
  refine ⟨?_, hH00⟩
  have hsl := hasDerivAt_iff_tendsto_slope.mp hHd
  have hmap : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
        simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using (ne_of_gt hε)
  have h1 := hsl.comp hmap
  have h2 : Tendsto (fun ε : ℝ => ((((hbarA aAmp (ε : ℂ)).re - aAmp 0) / ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (d : ℂ)) :=
    (Complex.continuous_ofReal.tendsto d).comp hd
  have heqf : (fun ε : ℝ => ((((hbarA aAmp (ε : ℂ)).re - aAmp 0) / ε : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      (slope H 0 ∘ fun ε : ℝ => (ε : ℂ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min δ 1 by positivity)] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεδ : ε < δ := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hst : (ε : ℂ) ∈ strip := ⟨by simpa using hε0, by simpa using hε1⟩
    have hball : (ε : ℂ) ∈ ball (0 : ℂ) δ := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]; exact hεδ
    have hHe : H (ε : ℂ) = hbarA aAmp (ε : ℂ) := by
      rw [← heq0 _ hst (by rw [hc]; exact hball), hbarA_of_mem_strip amp_aAmp hst]
    have him : (hbarA aAmp (ε : ℂ)).im = 0 := by
      have hcl : (ε : ℂ) ∈ closedStrip := strip_subset_closedStrip hst
      have := hbarA_conj amp_aAmp hcl
      rw [Complex.conj_ofReal] at this
      have := congrArg Complex.im this
      simp at this
      linarith
    simp only [Function.comp, slope_def_field, hHe, hH00, sub_zero]
    have hre : hbarA aAmp (ε : ℂ) = (((hbarA aAmp (ε : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using him)
    rw [hre]
    push_cast
    simp [div_eq_inv_mul]
  have h3 := h2.congr' heqf
  exact tendsto_nhds_unique h1 h3

/-- **The slope of `Gout` at the tip**: `g₁ = (4/π) d - 5/2 + √2/π`, where `d` is the one-sided slope of
`ε ↦ Re h̄_a(ε)` at `0`. -/
theorem g1Out_of_slope {d : ℝ}
    (hd : Tendsto (fun ε : ℝ => ((hbarA aAmp (ε : ℂ)).re - aAmp 0) / ε) (𝓝[>] 0) (𝓝 d)) :
    g1Out = 4 / π * d - 5 / 2 + √2 / π := by
  obtain ⟨δ, hδ, H, hH0, heq0, -⟩ := exists_edge_dataA amp_aAmp 0
  obtain ⟨hdH, -⟩ := deriv_H_eq hδ hH0 heq0 hd
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  obtain ⟨ρ, hρ, hρ4, hsI, hT⟩ := exists_local_radius hδ
  have hL := gout_eq_exp_Lloc hH0 heq0 hρ4 hsI hT
  have hH0' : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by rw [hc] at hH0; exact hH0
  have hHd : HasDerivAt H (deriv H 0) 0 :=
    (hH0'.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).hasDerivAt
  have hH1 : HasDerivAt (fun z => H (sInv z)) (deriv H 0 * ((4 / π : ℝ) : ℂ)) 0 := by
    have : HasDerivAt H (deriv H 0) (sInv 0) := by rw [sInv_zero]; exact hHd
    exact this.comp (0 : ℂ) hasDerivAt_sInv_zero
  have hl1 : HasDerivAt (fun z : ℂ => Complex.log (1 - z)) ((-1) / (1 - (0 : ℂ))) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_sub 1
    exact (h.clog (by simp)).congr_deriv (by simp)
  have hl2 : HasDerivAt (fun z : ℂ => Complex.log (1 + z)) (1 / (1 + (0 : ℂ))) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_add 1
    exact (h.clog (by simp)).congr_deriv (by simp)
  have hts : tipExt 0 ∈ Complex.slitPlane := by
    rw [tipExt_zero, Complex.mem_slitPlane_iff]; left
    have := arsinh_one_pos; have := Real.pi_pos
    simp; positivity
  have hl3 := hasDerivAt_tipExt_zero.clog hts
  have hLd : HasDerivAt (Lloc H) (deriv H 0 * ((4 / π : ℝ) : ℂ) + (-1) / (1 - (0 : ℂ)) / 2 -
      2 * (1 / (1 + (0 : ℂ))) - ((-(2 * ((√2 : ℝ) : ℂ)) / ((Real.arsinh 1 : ℝ) : ℂ)) / tipExt 0) / 4) 0 := by
    have := ((hH1.add (hl1.div_const 2)).sub (hl2.const_mul 2)).sub (hl3.div_const 4)
    exact this
  have hexp := hLd.cexp
  have hone : Complex.exp (Lloc H 0) = 1 := by
    rw [← hL 0 zero_mem_closure_halfDisc (by simpa using hρ)]; exact gout_zero
  rw [hone, one_mul] at hexp
  -- the slope along the real axis
  have hsl := hasDerivAt_iff_tendsto_slope.mp hexp
  have hmap : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 0) := by
        simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa using (ne_of_gt hε)
  have h1 := hsl.comp hmap
  -- the jet gives the same limit
  obtain ⟨C, r, hr, hjet⟩ := gout_outerDatum_g1Out.jet
  have h2 : Tendsto (fun x : ℝ => (x : ℂ)⁻¹ * (Gout (x : ℂ) - 1)) (𝓝[>] 0) (𝓝 (g1Out : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun x : ℝ => |C| * x) (𝓝[>] 0) (𝓝 0) by
        have : Tendsto (fun x : ℝ => |C| * x) (𝓝 0) (𝓝 (|C| * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min r 1 by positivity)] with x hx
    have hx0 : 0 < x := hx.1
    have hxr : x < r := lt_of_lt_of_le hx.2 (min_le_left _ _)
    have hx1 : x < 1 := lt_of_lt_of_le hx.2 (min_le_right _ _)
    have hxc : (x : ℂ) ∈ closure halfDisc :=
      subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
    have hb := hjet (x : ℂ) hxc (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hxr)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hb
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have : (x : ℂ)⁻¹ * (Gout (x : ℂ) - 1) - (g1Out : ℂ) = (x : ℂ)⁻¹ * (Gout (x : ℂ) - 1 - g1Out * x) := by
      field_simp
    rw [this, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    calc x⁻¹ * ‖Gout (x : ℂ) - 1 - g1Out * (x : ℂ)‖ ≤ x⁻¹ * (C * x ^ 2) := by gcongr
      _ = C * x := by field_simp
      _ ≤ |C| * x := mul_le_mul_of_nonneg_right (le_abs_self C) hx0.le
  have h1' : Tendsto (fun x : ℝ => (x : ℂ)⁻¹ * (Gout (x : ℂ) - 1)) (𝓝[>] 0)
      (𝓝 (deriv H 0 * ((4 / π : ℝ) : ℂ) + (-1) / (1 - (0 : ℂ)) / 2 -
      2 * (1 / (1 + (0 : ℂ))) - ((-(2 * ((√2 : ℝ) : ℂ)) / ((Real.arsinh 1 : ℝ) : ℂ)) / tipExt 0) / 4)) := by
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ by exact hρ)] with x hx
    have hx0 : 0 < x := hx.1
    have hxρ : ‖(x : ℂ)‖ < ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx.2
    have hx1 : x < 1 := by linarith [hx.2]
    have hxc : (x : ℂ) ∈ closure halfDisc :=
      subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
    simp only [Function.comp, slope_def_field, sub_zero]
    rw [← hL _ hxc hxρ, ← hL 0 zero_mem_closure_halfDisc (by simpa using hρ), gout_zero]
    rw [div_eq_inv_mul]
  have heqC := tendsto_nhds_unique h2 h1'
  rw [hdH, tipExt_logderiv] at heqC
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have : ((g1Out : ℝ) : ℂ) = ((4 / π * d - 5 / 2 + √2 / π : ℝ) : ℂ) := by
    rw [heqC]
    push_cast
    field_simp
    ring
  exact_mod_cast this

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.g1Out_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.g1Out_of_slope

end FormalResearch.ModularBootstrap.FiveTerm
