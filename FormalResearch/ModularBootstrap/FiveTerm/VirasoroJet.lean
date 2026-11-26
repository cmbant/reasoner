module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroOuter

/-!
# `G_outer` near the tip `z = 0` (FIVE-0 slice 4; `OuterDatum.jet`)

Near `z = 0` the three factors of `Gout` extend holomorphically across the diameter: `h̄_a` through the local
holomorphic extension at the edge point `s = 0` (`exists_edge_dataA`), `Q̂` through `tipExt`.  Hence `Gout` is the
restriction of a function `Gl` holomorphic on a disc, `Gout(0) = 1` (the amplitude `a` is *defined* so that this
holds: `a(0) = -¼ log(2ξ*)`), `Gl'(0)` is real by real symmetry, and the jet bound follows from Taylor.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- A function holomorphic on a disc has a second-order Taylor bound at the centre. -/
lemma jet_ball {h : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hd : DifferentiableOn ℂ h (ball (0 : ℂ) ρ)) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → ‖h z - h 0 - deriv h 0 * z‖ ≤ C * ‖z‖ ^ 2 := by
  have hgd : DifferentiableOn ℂ (dslope h 0) (ball (0 : ℂ) ρ) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hρ))).mpr hd
  have hcd : ContDiffAt ℂ 1 (dslope h 0) 0 :=
    (hgd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  obtain ⟨K, t, ht, hK⟩ := hcd.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, r, hr, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · subst hz0; simp
  have hzt : z ∈ t := hrt (by simpa using hz)
  have h0t : (0 : ℂ) ∈ t := hrt (by simpa using hr)
  have hL := hK.norm_sub_le hzt h0t
  have e1 : dslope h 0 z = (h z - h 0) / z := by
    rw [dslope_of_ne _ hz0, slope_def_field, sub_zero]
  have e2 : dslope h 0 0 = deriv h 0 := dslope_same _ _
  have e3 : h z - h 0 - deriv h 0 * z = z * (dslope h 0 z - dslope h 0 0) := by
    rw [e1, e2]; field_simp
  rw [e3, norm_mul]
  have : ‖dslope h 0 z - dslope h 0 0‖ ≤ K * ‖z‖ := by
    simpa [dist_eq_norm] using hL
  calc ‖z‖ * ‖dslope h 0 z - dslope h 0 0‖ ≤ ‖z‖ * (K * ‖z‖) := by gcongr
    _ = K * ‖z‖ ^ 2 := by ring

lemma differentiableAt_sInv_ball {z : ℂ} (hz : ‖z‖ < 1) : DifferentiableAt ℂ sInv z := by
  have h2 : z ≠ -Complex.I := by
    intro h; rw [h] at hz; simp at hz
  have hD := denom_pos h2
  have hq : qArc z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    rw [re_qArc]; apply div_pos _ hD; nlinarith [norm_nonneg z]
  have hd := one_sub_mul_I_ne_zero h2
  unfold sInv Complex.arctan
  have hqd : DifferentiableAt ℂ (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) hd
  have hl : DifferentiableAt ℂ (fun z : ℂ => Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))) z :=
    hqd.clog hq
  exact (differentiableAt_const _).mul ((differentiableAt_const _).mul hl)

lemma sInv_zero : sInv 0 = 0 := by simp [sInv, Complex.arctan]

lemma qBd_eq_tipExt {z : ℂ} (hz : z ∈ closure halfDisc) (hz4 : ‖z‖ < 1 / 4) : qBd z = tipExt z := by
  have hne : (𝓝[halfDisc] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  have hc : ContinuousAt tipExt z :=
    differentiableOn_tipExt.continuousOn.continuousAt (isOpen_ball.mem_nhds (by simpa using hz4))
  have ht : Tendsto tipExt (𝓝[halfDisc] z) (𝓝 (tipExt z)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : qHat =ᶠ[𝓝[halfDisc] z] tipExt := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (by simpa using hz4) : ball (0 : ℂ) (1 / 4) ∈ 𝓝 z)]
      with w hw hw4
    exact qHat_eq_tipExt hw (by simpa using hw4)
  exact extLim_eq_of_tendsto hz (ht.congr' hev.symm)

lemma xT_zero : xT 0 = xiStar := by unfold xT xiStar; simp

lemma vT_zero : vT 0 = 0 := by unfold vT; simp

lemma bT_zero : bT 0 = 1 / 2 := by
  unfold bT; rw [vT_zero, show (0 : ℝ) ^ 2 + 1 / 4 = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma lamT_zero : lamT 0 = 1 := by
  unfold lamT; rw [xT_zero]
  have hxi := xiStar_pos
  have : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by
    have : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
      rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr
      have := Real.pi_pos; nlinarith
    exact this.ne'
  exact div_self this

lemma aAmp_zero : aAmp 0 = -(1 / 4) * Real.log (2 * xiStar) := by
  have hxi := xiStar_pos
  unfold aAmp
  rw [xT_zero, bT_zero, lamT_zero]
  simp only [mul_zero, zero_div, Real.cosh_zero, Real.log_one, mul_one]
  rw [Real.log_mul (by norm_num) hxi.ne', show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

lemma hbarA_zero : hbarA aAmp 0 = ((aAmp 0 : ℝ) : ℂ) := by
  have h1 := re_hbarA_left amp_aAmp 0
  simp only [Complex.ofReal_zero, mul_zero] at h1
  have h2 := hbarA_conj amp_aAmp (ζ := 0) ⟨by simp, by simp⟩
  simp only [map_zero] at h2
  have him : (hbarA aAmp 0).im = 0 := by
    have := congrArg Complex.im h2
    simp at this; linarith
  exact Complex.ext (by simpa using h1) (by simpa using him)

lemma gout_zero : Gout 0 = 1 := by
  have hxi := xiStar_pos
  have h0 : (0 : ℂ) ∈ closure halfDisc := by
    have := sTan_mem_closure (s := 0) ⟨by simp, by simp⟩
    have h : sTan 0 = 0 := by simp [sTan]
    rwa [h] at this
  have hq : qBd 0 = ((1 / (2 * xiStar) : ℝ) : ℂ) := by
    rw [qBd_eq_tipExt h0 (by simp), tipExt_zero]
    congr 1
    unfold xiStar; have := arsinh_one_pos; have := Real.pi_pos; field_simp
  unfold Gout
  rw [sInv_zero, hbarA_zero, hq]
  have hr : 0 < 1 / (2 * xiStar) := by positivity
  have h1 : (-(1 / 4 : ℂ)) = ((-(1 / 4) : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_cpow hr.le, ← Complex.ofReal_exp]
  simp only [sub_zero, add_zero, Complex.one_cpow, div_one, mul_one, one_pow]
  rw [← Complex.ofReal_mul]
  have : Real.exp (aAmp 0) * (1 / (2 * xiStar)) ^ (-(1 / 4) : ℝ) = 1 := by
    have hl : Real.log (1 / (2 * xiStar)) = -Real.log (2 * xiStar) := by rw [one_div, Real.log_inv]
    rw [Real.rpow_def_of_pos hr, ← Real.exp_add, aAmp_zero, hl]
    rw [← Real.exp_zero]; congr 1; ring
  rw [this]; simp

/-- `Gout` is the restriction of a function holomorphic on a disc about the tip. -/
theorem gout_local : ∃ (Gl : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ ρ ≤ 1 / 4 ∧ DifferentiableOn ℂ Gl (ball (0 : ℂ) ρ) ∧
    ∀ z ∈ closure halfDisc, ‖z‖ < ρ → Gout z = Gl z := by
  obtain ⟨δ, hδ, H, hH0, heq0, -⟩ := exists_edge_dataA amp_aAmp 0
  have hc : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have hH : DifferentiableOn ℂ H (ball (0 : ℂ) δ) := by rw [hc] at hH0; exact hH0
  -- radii
  have hsI0 : ContinuousAt sInv 0 := (differentiableAt_sInv_ball (by simp)).continuousAt
  obtain ⟨ρ1, hρ1, hS⟩ := Metric.continuousAt_iff.mp hsI0 δ hδ
  have hT0 : ContinuousAt tipExt 0 :=
    differentiableOn_tipExt.continuousOn.continuousAt (isOpen_ball.mem_nhds (by simp))
  have ht0 : 0 < π / 2 / Real.arsinh 1 := by have := arsinh_one_pos; positivity
  obtain ⟨ρ2, hρ2, hT⟩ := Metric.continuousAt_iff.mp hT0 (π / 2 / Real.arsinh 1) ht0
  set ρ : ℝ := min (min ρ1 ρ2) (1 / 4) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ1 hρ2) (by norm_num)
  have hρ4 : ρ ≤ 1 / 4 := min_le_right _ _
  have hsIball : ∀ z : ℂ, ‖z‖ < ρ → sInv z ∈ ball (0 : ℂ) δ := by
    intro z hz
    have := hS (x := z) (by rw [dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _)))
    rw [sInv_zero, dist_zero_right] at this
    simpa using this
  have hTre : ∀ z : ℂ, ‖z‖ < ρ → 0 < (tipExt z).re := by
    intro z hz
    have := hT (x := z) (by rw [dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _)))
    rw [tipExt_zero, dist_eq_norm] at this
    have h2 : ‖tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)‖ < π / 2 / Real.arsinh 1 := this
    have h3 : |(tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)).re| ≤
        ‖tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    have h4 : (tipExt z - ((π / 2 / Real.arsinh 1 : ℝ) : ℂ)).re = (tipExt z).re - π / 2 / Real.arsinh 1 := by
      simp
    rw [h4] at h3
    have := (abs_lt.mp (lt_of_le_of_lt h3 h2)).1
    linarith
  refine ⟨fun z => Complex.exp (H (sInv z)) * (1 - z) ^ (1 / 2 : ℂ) / (1 + z) ^ 2 * (tipExt z) ^ (-(1 / 4 : ℂ)),
    ρ, hρ, hρ4, ?_, ?_⟩
  · intro z hz
    have hzn : ‖z‖ < ρ := by simpa using hz
    have hz1 : ‖z‖ < 1 := by linarith
    have hHd : DifferentiableAt ℂ H (sInv z) :=
      hH.differentiableAt (isOpen_ball.mem_nhds (hsIball z hzn))
    have hA : DifferentiableAt ℂ (fun w => H (sInv w)) z :=
      DifferentiableAt.comp (g := H) (f := sInv) z hHd (differentiableAt_sInv_ball hz1)
    have hslit : 1 - z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have := Complex.re_le_norm z
      simp; linarith
    have hP : DifferentiableAt ℂ (fun w : ℂ => (1 - w) ^ (1 / 2 : ℂ)) z :=
      DifferentiableAt.cpow_const (by fun_prop) hslit
    have hD : (1 + z) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro h
      have : z = -1 := eq_neg_of_add_eq_zero_right h
      rw [this] at hz1; simp at hz1
    have hTd : DifferentiableAt ℂ tipExt z :=
      differentiableOn_tipExt.differentiableAt (isOpen_ball.mem_nhds (by simp; linarith))
    have hTs : tipExt z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; exact hTre z hzn
    have hQ : DifferentiableAt ℂ (fun w => (tipExt w) ^ (-(1 / 4 : ℂ))) z :=
      DifferentiableAt.cpow_const hTd hTs
    exact ((((hA.cexp).mul hP).div (by fun_prop) hD).mul hQ).differentiableWithinAt
  · intro z hz hzn
    have hz4 : ‖z‖ < 1 / 4 := by linarith
    have hI : z ≠ Complex.I := by intro h; rw [h] at hz4; simp at hz4; linarith
    have hI' : z ≠ -Complex.I := by intro h; rw [h] at hz4; simp at hz4; linarith
    have hs : sInv z ∈ closedStrip := sInv_mem_closedStrip hz hI hI'
    have hb : hbarA aAmp (sInv z) = H (sInv z) := by
      refine hbarA_eq_local hH0 heq0 ?_ hs
      rw [hc]; exact hsIball z hzn
    unfold Gout
    rw [hb, qBd_eq_tipExt hz hz4]

lemma zero_mem_closure_halfDisc : (0 : ℂ) ∈ closure halfDisc := by
  have := sTan_mem_closure (s := 0) ⟨by simp, by simp⟩
  have h : sTan 0 = 0 := by simp [sTan]
  rwa [h] at this

lemma gout_real_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : (Gout (x : ℂ)).im = 0 := by
  have hx : (x : ℂ) ∈ halfDisc := ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
  have h := gout_conj hx
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- **The jet at the tip** (`OuterDatum.jet`) with `g₁ = G'(0)` real. -/
theorem gout_jet : ∃ g1 : ℝ, ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r →
    ‖Gout z - 1 - g1 * z‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨Gl, ρ, hρ, hρ4, hdiff, hGl⟩ := gout_local
  obtain ⟨C, r0, hr0, hjet⟩ := jet_ball hρ hdiff
  have h0 : Gl 0 = 1 := by
    rw [← hGl 0 zero_mem_closure_halfDisc (by simpa using hρ)]; exact gout_zero
  set d : ℂ := deriv Gl 0 with hd
  set r1 : ℝ := min r0 ρ with hr1
  have hr1pos : 0 < r1 := lt_min hr0 hρ
  have hGlx : ∀ x : ℝ, 0 < x → x < r1 → (Gl (x : ℂ)).im = 0 := by
    intro x hx0 hx
    have hxρ : ‖(x : ℂ)‖ < ρ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact lt_of_lt_of_le hx (min_le_right _ _)
    have hx1 : x < 1 := by
      have := lt_of_lt_of_le hx (min_le_right _ _); linarith
    have hxc : (x : ℂ) ∈ closure halfDisc :=
      subset_closure ⟨by simpa [abs_of_pos hx0] using hx1, by simpa using hx0⟩
    rw [← hGl _ hxc hxρ]
    exact gout_real_pos hx0 hx1
  have hdim : d.im = 0 := by
    by_contra hne
    have ha : 0 < |d.im| := abs_pos.mpr hne
    set x : ℝ := min (r1 / 2) (|d.im| / (2 * (|C| + 1))) with hx
    have hx0 : 0 < x := lt_min (by positivity) (by positivity)
    have hxr : x < r1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hb := hjet (x : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact lt_of_lt_of_le hxr (min_le_left _ _))
    rw [h0] at hb
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at hb
    have him : |(Gl (x : ℂ) - 1 - d * (x : ℂ)).im| ≤ ‖Gl (x : ℂ) - 1 - d * (x : ℂ)‖ := Complex.abs_im_le_norm _
    have hcalc : (Gl (x : ℂ) - 1 - d * (x : ℂ)).im = -(d.im * x) := by
      simp [hGlx x hx0 hxr]
    rw [hcalc, abs_neg, abs_mul, abs_of_pos hx0] at him
    have h1 : |d.im| * x ≤ C * x ^ 2 := him.trans hb
    have h2 : |d.im| ≤ C * x := by
      have := h1
      nlinarith [hx0]
    have h3 : x ≤ |d.im| / (2 * (|C| + 1)) := min_le_right _ _
    have h4 : C * x ≤ |C| * x := mul_le_mul_of_nonneg_right (le_abs_self C) hx0.le
    have h5 : |C| * x < |d.im| := by
      have hC1 : 0 < |C| + 1 := by positivity
      calc |C| * x ≤ (|C| + 1) * x := by nlinarith [abs_nonneg C]
        _ ≤ (|C| + 1) * (|d.im| / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left h3 hC1.le
        _ = |d.im| / 2 := by field_simp
        _ < |d.im| := by linarith
    linarith
  refine ⟨d.re, C, r1, hr1pos, fun z hz hzr => ?_⟩
  have hdd : d = (d.re : ℂ) := Complex.ext (by simp) (by simpa using hdim)
  have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hzr (min_le_right _ _)
  have hzr0 : ‖z‖ < r0 := lt_of_lt_of_le hzr (min_le_left _ _)
  have := hjet z hzr0
  rw [h0, hdd] at this
  rw [hGl z hz hzρ]
  exact this

end FormalResearch.ModularBootstrap.FiveTerm
