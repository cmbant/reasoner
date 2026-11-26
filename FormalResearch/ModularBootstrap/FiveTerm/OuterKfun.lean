module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroXb
public import FormalResearch.ModularBootstrap.FiveTerm.StripOuterBoundary
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroSlit

/-!
# The strip function `K(s) = (1 + sin πs) S(cos πs) S(-cos πs) / (π² ξ*²)` (FIVE-S, `cts:outer-strip`)

`K` is holomorphic and zero-free on `0 < Re s < 1`, symmetric under `s ↦ 1 - s` and conjugation, and extends
continuously to the closed strip (`Kb`), because `S(-cos πs) = Q̂(tan(πs/4)) S(cos πs)` with `Q̂ = qHat` which has
boundary limits.  On the left edge `K̄(it) = (1 + i sinh πt) (1/2 - i v_T) / x_T · S(cosh πt)² / (π² ξ*²)`, so that
`|K̄| = x_T b_T / ξ*²` on both edges.  This is the comparison function for the Phragmen-Lindelof identification of
`exp(4 h̄_{a_xb})` (`OuterPhase`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- `K(s) = (1 + sin πs) S(cos πs) S(cos π(1-s)) / (π² ξ*²)`. -/
noncomputable def Kfun (s : ℂ) : ℂ :=
  (1 + Complex.sin ((π : ℂ) * s)) * (gS s * gS (1 - s)) / ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2)

lemma gS_one_sub (s : ℂ) : gS (1 - s) = sInt (-(cC s)) := by
  unfold gS cC
  congr 1
  rw [mul_sub, mul_one, Complex.cos_pi_sub]

lemma cos_im_zero_cases {s : ℂ} (hs : s.re ∈ Ico (0 : ℝ) 1) : cC s ∈ sDom := by
  rintro ⟨him, hre⟩
  rw [im_cC] at him
  rw [re_cC] at hre
  obtain ⟨h0, h1⟩ := hs
  have hpi := Real.pi_pos
  rcases h0.eq_or_lt with h | h
  · rw [← h] at hre
    simp at hre
    have := Real.one_le_cosh (π * s.im)
    linarith
  · have hsin : 0 < Real.sin (π * s.re) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    have hsh : Real.sinh (π * s.im) = 0 := by
      have := mul_eq_zero.mp (neg_eq_zero.mp him)
      rcases this with h' | h'
      · exact absurd h' hsin.ne'
      · exact h'
    have him0 : s.im = 0 := by
      have := Real.sinh_eq_zero.mp hsh
      have h2 : π * s.im = 0 := this
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hpi.ne'
      · exact h3
    rw [him0] at hre
    simp at hre
    have hc : -1 < Real.cos (π * s.re) := by
      have : Real.cos (π * s.re) > Real.cos π := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl (by nlinarith)
      rwa [Real.cos_pi] at this
    linarith

lemma neg_cC_mem_sDom {s : ℂ} (hs : s.re ∈ Ioc (0 : ℝ) 1) : -(cC s) ∈ sDom := by
  have h : 1 - s ∈ {s : ℂ | s.re ∈ Ico (0 : ℝ) 1} := by
    simp only [mem_ofPred_eq, Complex.sub_re, Complex.one_re]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := cos_im_zero_cases h
  unfold cC at this ⊢
  have e : Complex.cos ((π : ℂ) * (1 - s)) = -Complex.cos ((π : ℂ) * s) := by
    rw [mul_sub, mul_one, Complex.cos_pi_sub]
  rwa [e] at this

lemma Kfun_one_sub (s : ℂ) : Kfun (1 - s) = Kfun s := by
  unfold Kfun
  rw [sub_sub_cancel, mul_comm (gS (1 - s)) (gS s)]
  congr 3
  rw [mul_sub, mul_one, Complex.sin_pi_sub]

lemma differentiableAt_gS {s : ℂ} (hs : s.re ∈ Ico (0 : ℝ) 1) : DifferentiableAt ℂ gS s := by
  unfold gS
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Complex.cos ((π : ℂ) * s)) s := by fun_prop
  exact (differentiableOn_sInt.differentiableAt (isOpen_sDom.mem_nhds (cos_im_zero_cases hs))).comp s h1

lemma xiStar_ne : (xiStar : ℂ) ≠ 0 := by
  have := xiStar_pos
  exact_mod_cast this.ne'

lemma pi_xi_ne : ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2) ≠ 0 := by
  have := xiStar_ne
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  positivity

lemma differentiableOn_Kfun : DifferentiableOn ℂ Kfun unitStrip := by
  intro s hs
  have h1 : DifferentiableAt ℂ gS s := differentiableAt_gS ⟨hs.1.le, hs.2⟩
  have h2 : DifferentiableAt ℂ (fun s => gS (1 - s)) s := by
    have : DifferentiableAt ℂ gS (1 - s) := differentiableAt_gS ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩
    exact this.comp s (by fun_prop)
  unfold Kfun
  exact ((((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => 1 + Complex.sin ((π : ℂ) * s)) s).mul
    (h1.mul h2))).div_const _).differentiableWithinAt

lemma sin_re_im_strip {s : ℂ} (hs : s ∈ unitStrip) : 1 + Complex.sin ((π : ℂ) * s) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  have hre : (Complex.sin ((π : ℂ) * s)).re = Real.sin (π * s.re) * Real.cosh (π * s.im) := by
    have := sin_re' ((π : ℂ) * s)
    simpa using this
  have him : (Complex.sin ((π : ℂ) * s)).im = Real.cos (π * s.re) * Real.sinh (π * s.im) := by
    have := sin_im' ((π : ℂ) * s)
    simpa using this
  simp only [Complex.add_re, Complex.one_re, hre, Complex.zero_re] at h1
  have hsin : 0 < Real.sin (π * s.re) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1, Real.pi_pos]) (by nlinarith [hs.2, Real.pi_pos])
  have := Real.one_le_cosh (π * s.im)
  nlinarith [mul_pos hsin (Real.cosh_pos (π * s.im))]

lemma Kfun_ne_zero {s : ℂ} (hs : s ∈ unitStrip) : Kfun s ≠ 0 := by
  unfold Kfun
  have h1 := sin_re_im_strip hs
  have h2 : gS s ≠ 0 := sInt_ne_zero (cos_im_zero_cases ⟨hs.1.le, hs.2⟩)
  have h3 : gS (1 - s) ≠ 0 := by
    rw [gS_one_sub]; exact sInt_ne_zero (neg_cC_mem_sDom ⟨hs.1, hs.2.le⟩)
  exact div_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 h3)) pi_xi_ne

lemma uC_sTan {s : ℂ} (hs : s ∈ unitStripCl) : uC (sTan s) = cC s := by
  have hc : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := cos_ne_zero_of_cl hs
  unfold uC cC
  rw [sTan_eq]
  set w : ℂ := (π : ℂ) * s / 4 with hw
  have h4 : (π : ℂ) * s = 2 * (2 * w) := by rw [hw]; ring
  rw [h4, Complex.cos_two_mul, Complex.cos_two_mul]
  have hid : Complex.sin w ^ 2 + Complex.cos w ^ 2 = 1 := Complex.sin_sq_add_cos_sq w
  have hden : (1 + (Complex.sin w / Complex.cos w) ^ 2) = (Complex.cos w ^ 2)⁻¹ := by
    field_simp; linear_combination hid
  rw [hden]
  field_simp
  have hs2 : Complex.sin w ^ 2 = 1 - Complex.cos w ^ 2 := by linear_combination hid
  have h4' : Complex.sin w ^ 4 = (Complex.sin w ^ 2) ^ 2 := by ring
  rw [h4', hs2]
  ring


lemma Kfun_eq_qHat {s : ℂ} (hs : s ∈ unitStrip) :
    Kfun s = (1 + Complex.sin ((π : ℂ) * s)) * (qHat (sTan s) * gS s ^ 2) /
      ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2) := by
  have h2 : gS s ≠ 0 := sInt_ne_zero (cos_im_zero_cases ⟨hs.1.le, hs.2⟩)
  have hq : qHat (sTan s) = sInt (-(cC s)) / gS s := by
    unfold qHat sHat
    rw [uC_sTan (unitStrip_subset_cl hs)]
    rfl
  unfold Kfun
  rw [gS_one_sub, hq]
  field_simp

lemma tendsto_sTan_strip {s₀ : ℂ} (hs₀ : s₀ ∈ unitStripCl) :
    Tendsto sTan (𝓝[unitStrip] s₀) (𝓝[halfDisc] (sTan s₀)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuousOn_sTan.continuousWithinAt hs₀).tendsto.mono_left (nhdsWithin_mono _ unitStrip_subset_cl)
  · filter_upwards [self_mem_nhdsWithin] with s hs using sTan_mem_halfDisc hs

lemma tendsto_oneSub_strip (s₀ : ℂ) :
    Tendsto (fun s : ℂ => 1 - s) (𝓝[unitStrip] s₀) (𝓝[unitStrip] (1 - s₀)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩

/-- The limit of `K` at a left-edge point. -/
lemma tendsto_Kfun_left {s₀ : ℂ} (h0 : s₀.re = 0) :
    ∃ L, Tendsto Kfun (𝓝[unitStrip] s₀) (𝓝 L) := by
  have hs₀ : s₀ ∈ unitStripCl := ⟨h0.ge, by rw [h0]; norm_num⟩
  obtain ⟨Lq, _, hLq⟩ := exists_limit_qHat (sTan_mem_closure hs₀) (sTan_ne_I s₀ hs₀) (sTan_ne_neg_I s₀ hs₀)
  have hq := hLq.comp (tendsto_sTan_strip hs₀)
  have hg : ContinuousAt gS s₀ := (differentiableAt_gS ⟨h0.ge, by rw [h0]; norm_num⟩).continuousAt
  have hsin : ContinuousAt (fun s : ℂ => 1 + Complex.sin ((π : ℂ) * s)) s₀ := by fun_prop
  have hlim : Tendsto (fun s : ℂ => (1 + Complex.sin ((π : ℂ) * s)) * (qHat (sTan s) * gS s ^ 2) /
      ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2)) (𝓝[unitStrip] s₀)
      (𝓝 ((1 + Complex.sin ((π : ℂ) * s₀)) * (Lq * gS s₀ ^ 2) / ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2))) := by
    refine Tendsto.div_const (hsin.tendsto.mono_left nhdsWithin_le_nhds |>.mul
      (hq.mul ((hg.tendsto.mono_left nhdsWithin_le_nhds).pow 2))) _
  exact ⟨_, hlim.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (Kfun_eq_qHat hs).symm)⟩

lemma exists_limit_Kfun {s : ℂ} (hs : s ∈ unitStripCl) :
    ∃ L, Tendsto Kfun (𝓝[unitStrip] s) (𝓝 L) := by
  rcases hs.1.eq_or_lt with h0 | h0
  · exact tendsto_Kfun_left h0.symm
  rcases hs.2.eq_or_lt with h1 | h1
  · obtain ⟨L, hL⟩ := tendsto_Kfun_left (s₀ := 1 - s) (by simp [h1])
    refine ⟨L, ?_⟩
    have := hL.comp (tendsto_oneSub_strip s)
    refine this.congr' ?_
    filter_upwards with t
    simp [Function.comp, Kfun_one_sub]
  · exact ⟨Kfun s, (differentiableOn_Kfun.continuousOn.continuousAt
      (isOpen_unitStrip.mem_nhds ⟨h0, h1⟩)).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- The boundary extension of `K`. -/
noncomputable def Kb : ℂ → ℂ := extLim unitStrip Kfun

lemma Kb_of_mem {s : ℂ} (hs : s ∈ unitStrip) : Kb s = Kfun s :=
  extLim_of_mem hs (differentiableOn_Kfun.continuousOn.continuousAt
    (isOpen_unitStrip.mem_nhds hs)).continuousWithinAt

lemma tendsto_Kb {s : ℂ} (hs : s ∈ unitStripCl) : Tendsto Kfun (𝓝[unitStrip] s) (𝓝 (Kb s)) :=
  tendsto_extLim (exists_limit_Kfun hs)

lemma continuousOn_Kb : ContinuousOn Kb unitStripCl := by
  have h := continuousOn_extLim (U := unitStrip) (f := Kfun) (bad := ∅)
    (fun _z hz => exists_limit_Kfun (closure_unitStrip_subset (by simpa using hz.1)))
  refine h.mono ?_
  intro z hz
  exact ⟨unitStripCl_subset_closure hz, by simp⟩

lemma Kb_one_sub {s : ℂ} (hs : s ∈ unitStripCl) : Kb (1 - s) = Kb s := by
  have hs' : 1 - s ∈ unitStripCl := ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩
  have h1 := (tendsto_Kb hs').comp (tendsto_oneSub_strip s |>.mono_right le_rfl) |> fun h => h
  have hA : Tendsto (fun t : ℂ => Kfun (1 - t)) (𝓝[unitStrip] s) (𝓝 (Kb (1 - s))) :=
    (tendsto_Kb hs').comp (tendsto_oneSub_strip s)
  have hB : Tendsto (fun t : ℂ => Kfun (1 - t)) (𝓝[unitStrip] s) (𝓝 (Kb s)) := by
    refine (tendsto_Kb hs).congr' ?_
    filter_upwards with t
    exact (Kfun_one_sub t).symm
  have := mem_closure_iff_nhdsWithin_neBot.mp (unitStripCl_subset_closure hs)
  exact tendsto_nhds_unique hA hB


lemma xT_zero : xT 0 = xiStar := by
  unfold xT xiStar; simp

lemma vT_zero : vT 0 = 0 := by unfold vT; simp

lemma bT_zero : bT 0 = 1 / 2 := by
  unfold bT; rw [vT_zero]; rw [show ((0 : ℝ) ^ 2 + 1 / 4) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The boundary value of `Q̂` over the left edge point `s = it` has modulus `b_T/x_T`. -/
lemma exists_qlim_edge (t : ℝ) : ∃ Lq : ℂ, ‖Lq‖ = bT t / xT t ∧
    Tendsto qHat (𝓝[halfDisc] (sTan ((t : ℂ) * Complex.I))) (𝓝 Lq) := by
  rw [sTan_I_mul]
  have hpi := Real.pi_pos
  have key : ∀ r : ℝ, 0 < r → ∃ Lq : ℂ, ‖Lq‖ = bT r / xT r ∧
      Tendsto qHat (𝓝[halfDisc] (Complex.I * ((Real.tanh (π * r / 4) : ℝ) : ℂ))) (𝓝 Lq) := by
    intro r hr
    have hy0 : 0 < Real.tanh (π * r / 4) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
    have hy1 : Real.tanh (π * r / 4) < 1 := Real.tanh_lt_one _
    refine ⟨slitVal (Real.tanh (π * r / 4)), ?_, tendsto_qHat_slit hy0 hy1⟩
    rw [norm_slitVal ⟨hy0, hy1⟩, xOf_tanh, vOf_tanh hr.le]
    rfl
  rcases lt_trichotomy t 0 with ht | ht | ht
  · obtain ⟨L, hL, hlim⟩ := key (-t) (by linarith)
    refine ⟨starRingEnd ℂ L, by rw [Complex.norm_conj, hL, bT_even, xT_even], ?_⟩
    apply tendsto_qHat_conj
    have e : starRingEnd ℂ (Complex.I * ((Real.tanh (π * t / 4) : ℝ) : ℂ)) =
        Complex.I * ((Real.tanh (π * (-t) / 4) : ℝ) : ℂ) := by
      have : π * (-t) / 4 = -(π * t / 4) := by ring
      rw [this, Real.tanh_neg, Complex.ofReal_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [e]; exact hlim
  · subst ht
    refine ⟨tipExt 0, ?_, ?_⟩
    · rw [tipExt_zero, bT_zero, xT_zero]
      unfold xiStar
      have : 0 < Real.arsinh 1 := arsinh_one_pos
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    · have : Complex.I * ((Real.tanh (π * 0 / 4) : ℝ) : ℂ) = 0 := by simp
      rw [this]; exact tendsto_qHat_tip
  · exact key t ht

lemma tendsto_Kfun_left_val {s₀ : ℂ} (h0 : s₀.re = 0) {Lq : ℂ}
    (hLq : Tendsto qHat (𝓝[halfDisc] (sTan s₀)) (𝓝 Lq)) :
    Tendsto Kfun (𝓝[unitStrip] s₀)
      (𝓝 ((1 + Complex.sin ((π : ℂ) * s₀)) * (Lq * gS s₀ ^ 2) / ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2))) := by
  have hs₀ : s₀ ∈ unitStripCl := ⟨h0.ge, by rw [h0]; norm_num⟩
  have hq := hLq.comp (tendsto_sTan_strip hs₀)
  have hg : ContinuousAt gS s₀ := (differentiableAt_gS ⟨h0.ge, by rw [h0]; norm_num⟩).continuousAt
  have hsin : ContinuousAt (fun s : ℂ => 1 + Complex.sin ((π : ℂ) * s)) s₀ := by fun_prop
  have hlim := Tendsto.div_const (hsin.tendsto.mono_left nhdsWithin_le_nhds |>.mul
      (hq.mul ((hg.tendsto.mono_left nhdsWithin_le_nhds).pow 2))) ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2)
  exact hlim.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (Kfun_eq_qHat hs).symm)

lemma Kb_left_val {s₀ : ℂ} (h0 : s₀.re = 0) {Lq : ℂ}
    (hLq : Tendsto qHat (𝓝[halfDisc] (sTan s₀)) (𝓝 Lq)) :
    Kb s₀ = (1 + Complex.sin ((π : ℂ) * s₀)) * (Lq * gS s₀ ^ 2) / ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2) := by
  have hs₀ : s₀ ∈ unitStripCl := ⟨h0.ge, by rw [h0]; norm_num⟩
  have := mem_closure_iff_nhdsWithin_neBot.mp (unitStripCl_subset_closure hs₀)
  exact tendsto_nhds_unique (tendsto_Kb hs₀) (tendsto_Kfun_left_val h0 hLq)

lemma norm_one_add_sin_edge (t : ℝ) :
    ‖1 + Complex.sin ((π : ℂ) * ((t : ℂ) * Complex.I))‖ = Real.cosh (π * t) := by
  have h : Complex.sin ((π : ℂ) * ((t : ℂ) * Complex.I)) = ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I := by
    have : (π : ℂ) * ((t : ℂ) * Complex.I) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [h]
  have e : (1 : ℂ) + ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I =
      ((1 : ℝ) : ℂ) + ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I := by simp
  rw [e, Complex.norm_add_mul_I]
  have : 1 ^ 2 + Real.sinh (π * t) ^ 2 = Real.cosh (π * t) ^ 2 := by
    nlinarith [Real.cosh_sq (π * t)]
  rw [this, Real.sqrt_sq (Real.cosh_pos _).le]

lemma gS_left (t : ℝ) : gS ((t : ℂ) * Complex.I) = ((π * xT t / √(Real.cosh (π * t)) : ℝ) : ℂ) := by
  unfold gS
  have := cC_left t
  unfold cC at this
  rw [this, sInt_pos_real (Real.cosh_pos _)]
  congr 1
  unfold xT
  have hpi := Real.pi_pos
  field_simp

/-- **Edge modulus.** `|K̄(it)| = x_T b_T / ξ*²`. -/
lemma norm_Kb_left (t : ℝ) : ‖Kb ((t : ℂ) * Complex.I)‖ = xT t * bT t / xiStar ^ 2 := by
  obtain ⟨Lq, hL, hlim⟩ := exists_qlim_edge t
  have hpi := Real.pi_pos
  have hx := xT_pos t
  have hxi := xiStar_pos
  have hb := bT_pos t
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hsc : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
  have hsq : √(Real.cosh (π * t)) ^ 2 = Real.cosh (π * t) := Real.sq_sqrt hc.le
  have hN : ‖(π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2‖ = π ^ 2 * xiStar ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hpi, abs_of_pos hxi]
  have hg : ‖gS ((t : ℂ) * Complex.I)‖ = π * xT t / √(Real.cosh (π * t)) := by
    rw [gS_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Kb_left_val (by simp) hlim, norm_div, norm_mul, norm_mul, norm_pow, norm_one_add_sin_edge, hL, hg, hN]
  rw [div_pow, mul_pow, hsq]
  field_simp

lemma norm_Kb_right (t : ℝ) : ‖Kb (1 + (t : ℂ) * Complex.I)‖ = xT t * bT t / xiStar ^ 2 := by
  have e : (1 + (t : ℂ) * Complex.I) = 1 - (((-t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  have hs : (((-t : ℝ) : ℂ) * Complex.I) ∈ unitStripCl := ⟨by simp, by simp⟩
  rw [e, Kb_one_sub hs, norm_Kb_left, xT_even, bT_even]


lemma Kb_ne_zero {s : ℂ} (hs : s ∈ unitStripCl) : Kb s ≠ 0 := by
  rcases hs.1.eq_or_lt with h0 | h0
  · have e : s = (s.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [← h0]
    intro h
    have := norm_Kb_left s.im
    rw [← e, h, norm_zero] at this
    have hx := xT_pos s.im
    have hb := bT_pos s.im
    have hxi := xiStar_pos
    have : 0 < xT s.im * bT s.im / xiStar ^ 2 := by positivity
    linarith
  rcases hs.2.eq_or_lt with h1 | h1
  · have e : s = 1 + (s.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [h1]
    intro h
    have := norm_Kb_right s.im
    rw [← e, h, norm_zero] at this
    have hx := xT_pos s.im
    have hb := bT_pos s.im
    have hxi := xiStar_pos
    have : 0 < xT s.im * bT s.im / xiStar ^ 2 := by positivity
    linarith
  · rw [Kb_of_mem ⟨h0, h1⟩]; exact Kfun_ne_zero ⟨h0, h1⟩

lemma norm_sInt_le_one {u : ℂ} (hu : u ∈ sDom) (hre : 0 ≤ u.re) : ‖sInt u‖ ≤ 1 := by
  unfold sInt
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖(1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
    intro t ht
    have hre1 : 1 ≤ (1 + u * (t : ℂ) ^ 2).re := by
      have : (u * (t : ℂ) ^ 2).re = u.re * t ^ 2 := by
        rw [show ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_mul_ofReal]
      simp only [Complex.add_re, Complex.one_re, this]
      nlinarith [mul_nonneg hre (sq_nonneg t)]
    have hn1 : 1 ≤ ‖1 + u * (t : ℂ) ^ 2‖ := le_trans hre1 (Complex.re_le_norm _)
    have e : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  calc ‖∫ t in Icc (0 : ℝ) 1, (1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖
      ≤ ∫ t in Icc (0 : ℝ) 1, ‖(1 + u * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Icc (0 : ℝ) 1, (1 : ℝ) := by
        refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Icc hb
        exact (continuousOn_sIntegrand hu).norm.integrableOn_Icc
    _ = 1 := by simp


lemma exp_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos x, Real.exp_pos (-x)]
  · rw [h]; linarith [Real.exp_pos x, Real.exp_pos (-x)]

lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [h]
    have : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    linarith

lemma norm_cos_quarter_ge {s : ℂ} (hs : s ∈ unitStripCl) :
    Real.exp (π * |s.im| / 4) / 2 ≤ ‖Complex.cos ((π : ℂ) * s / 4)‖ := by
  have h1 := norm_cos_sq_ge hs
  have h2 := exp_div_two_le_cosh (π * s.im / 2)
  have h3 : |π * s.im / 2| = π * |s.im| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]; norm_num
  rw [h3] at h2
  have h4 : (Real.exp (π * |s.im| / 4) / 2) ^ 2 ≤ ‖Complex.cos ((π : ℂ) * s / 4)‖ ^ 2 := by
    have : (Real.exp (π * |s.im| / 4)) ^ 2 = Real.exp (π * |s.im| / 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    nlinarith [this]
  exact abs_le_of_sq_le_sq' h4 (norm_nonneg _) |>.2

lemma tan_sub_I_aux {w : ℂ} (hc : Complex.cos w ≠ 0) :
    Complex.sin w / Complex.cos w - Complex.I = -Complex.I * Complex.exp (w * Complex.I) / Complex.cos w := by
  rw [Complex.exp_mul_I]
  field_simp
  linear_combination (Complex.sin w) * Complex.I_sq

lemma tan_add_I_aux {w : ℂ} (hc : Complex.cos w ≠ 0) :
    Complex.sin w / Complex.cos w + Complex.I = Complex.I * Complex.exp (-w * Complex.I) / Complex.cos w := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  field_simp
  linear_combination (Complex.sin w) * Complex.I_sq

lemma norm_sTan_sub_I {s : ℂ} (hs : s ∈ unitStripCl) (hτ : 0 < s.im) :
    ‖sTan s - Complex.I‖ ≤ 2 * Real.exp (-(π * s.im / 2)) := by
  have hc : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := cos_ne_zero_of_cl hs
  set w : ℂ := (π : ℂ) * s / 4 with hw
  have e : sTan s - Complex.I = -Complex.I * Complex.exp (w * Complex.I) / Complex.cos w := by
    rw [sTan_eq]; exact tan_sub_I_aux hc
  have hexp : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-(π * s.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [hw]
  have hcos := norm_cos_quarter_ge hs
  rw [abs_of_pos hτ] at hcos
  rw [e, norm_div, norm_mul, hexp, norm_neg, Complex.norm_I, one_mul]
  have hpos : 0 < Real.exp (π * s.im / 4) / 2 := by positivity
  calc Real.exp (-(π * s.im / 4)) / ‖Complex.cos w‖ ≤ Real.exp (-(π * s.im / 4)) / (Real.exp (π * s.im / 4) / 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hcos
    _ = 2 * Real.exp (-(π * s.im / 2)) := by
        have h1 : Real.exp (-(π * s.im / 2)) =
            Real.exp (-(π * s.im / 4)) * Real.exp (-(π * s.im / 4)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h1, Real.exp_neg (π * s.im / 4)]
        have : Real.exp (π * s.im / 4) ≠ 0 := (Real.exp_pos _).ne'
        field_simp

lemma norm_sTan_add_I {s : ℂ} (hs : s ∈ unitStripCl) (hτ : s.im < 0) :
    ‖sTan s + Complex.I‖ ≤ 2 * Real.exp (-(π * |s.im| / 2)) := by
  have hc : Complex.cos ((π : ℂ) * s / 4) ≠ 0 := cos_ne_zero_of_cl hs
  set w : ℂ := (π : ℂ) * s / 4 with hw
  have e : sTan s + Complex.I = Complex.I * Complex.exp (-w * Complex.I) / Complex.cos w := by
    rw [sTan_eq]; exact tan_add_I_aux hc
  have hexp : ‖Complex.exp (-w * Complex.I)‖ = Real.exp (-(π * |s.im| / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    rw [abs_of_neg hτ]
    simp [hw]
    ring
  have hcos := norm_cos_quarter_ge hs
  rw [e, norm_div, norm_mul, hexp, Complex.norm_I, one_mul]
  have hpos : 0 < Real.exp (π * |s.im| / 4) / 2 := by positivity
  calc Real.exp (-(π * |s.im| / 4)) / ‖Complex.cos w‖ ≤
        Real.exp (-(π * |s.im| / 4)) / (Real.exp (π * |s.im| / 4) / 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hcos
    _ = 2 * Real.exp (-(π * |s.im| / 2)) := by
        have h1 : Real.exp (-(π * |s.im| / 2)) =
            Real.exp (-(π * |s.im| / 4)) * Real.exp (-(π * |s.im| / 4)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h1, Real.exp_neg (π * |s.im| / 4)]
        have : Real.exp (π * |s.im| / 4) ≠ 0 := (Real.exp_pos _).ne'
        field_simp


lemma exp_six_gt : (24 : ℝ) < Real.exp 6 := by
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num)
  nlinarith

lemma near_pm_I {s : ℂ} (hs : s ∈ unitStrip) (hτ : 4 ≤ |s.im|) :
    ‖sTan s - Complex.I‖ < 1 / 12 ∨ ‖sTan s + Complex.I‖ < 1 / 12 := by
  have hcl := unitStrip_subset_cl hs
  have hpi := Real.pi_gt_three
  have hb : ∀ a : ℝ, 4 ≤ a → 2 * Real.exp (-(π * a / 2)) < 1 / 12 := by
    intro a ha
    have h1 : Real.exp (-(π * a / 2)) ≤ Real.exp (-6) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have h2 : Real.exp (-6) < 1 / 24 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      simpa using exp_six_gt
    linarith
  rcases lt_or_gt_of_ne (show s.im ≠ 0 by intro h; rw [h] at hτ; simp at hτ; linarith) with h | h
  · right
    have := norm_sTan_add_I hcl h
    exact lt_of_le_of_lt this (hb _ hτ)
  · left
    have := norm_sTan_sub_I hcl h
    rw [abs_of_pos h] at hτ
    exact lt_of_le_of_lt this (hb _ hτ)

lemma norm_one_add_sin_ge {s : ℂ} (hs : s ∈ unitStrip) : 1 ≤ ‖1 + Complex.sin ((π : ℂ) * s)‖ := by
  have hre : (Complex.sin ((π : ℂ) * s)).re = Real.sin (π * s.re) * Real.cosh (π * s.im) := by
    have := sin_re' ((π : ℂ) * s)
    simpa using this
  have hsin : 0 < Real.sin (π * s.re) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hs.1, Real.pi_pos]) (by nlinarith [hs.2, Real.pi_pos])
  refine le_trans ?_ (Complex.re_le_norm _)
  simp only [Complex.add_re, Complex.one_re, hre]
  nlinarith [mul_pos hsin (Real.cosh_pos (π * s.im))]

lemma norm_one_add_sin_le (s : ℂ) : ‖1 + Complex.sin ((π : ℂ) * s)‖ ≤ 2 * Real.exp (π * |s.im|) := by
  have h1 : ‖Complex.sin ((π : ℂ) * s)‖ ≤ Real.cosh (π * s.im) := by
    have h := norm_sin_sq' ((π : ℂ) * s)
    have hre : ((π : ℂ) * s).im = π * s.im := by simp
    rw [hre] at h
    have : ‖Complex.sin ((π : ℂ) * s)‖ ^ 2 ≤ Real.cosh (π * s.im) ^ 2 := by
      rw [h, Real.cosh_sq]; nlinarith [Real.sin_sq_le_one (((π : ℂ) * s).re)]
    exact abs_le_of_sq_le_sq' this (Real.cosh_pos _).le |>.2
  have h2 := cosh_le_exp_abs (π * s.im)
  have h3 : |π * s.im| = π * |s.im| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [h3] at h2
  have h4 : 1 ≤ Real.exp (π * |s.im|) := Real.one_le_exp (by positivity)
  calc ‖1 + Complex.sin ((π : ℂ) * s)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.sin ((π : ℂ) * s)‖ := norm_add_le _ _
    _ ≤ 2 * Real.exp (π * |s.im|) := by simp; linarith

lemma Kfun_bounds_left {s : ℂ} (hs : s ∈ unitStrip) (hre : s.re ≤ 1 / 2) (hτ : 4 ≤ |s.im|) :
    ‖Kfun s‖ ≤ 2 * Cq / (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|) ∧
    Real.exp (-(π * |s.im|)) / (8 * Cq * (π ^ 2 * xiStar ^ 2)) ≤ ‖Kfun s‖ := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  have hCq := Cq_pos
  have hNN : 0 < π ^ 2 * xiStar ^ 2 := by positivity
  have hN : ‖(π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2‖ = π ^ 2 * xiStar ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hpi, abs_of_pos hxi]
  have hcl := unitStrip_subset_cl hs
  obtain ⟨hq1, hq2⟩ := qHat_bounds_near_I (sTan_mem_halfDisc hs) (by
    rcases near_pm_I hs hτ with h | h
    · left; exact h
    · right; exact h)
  have hKeq : ‖Kfun s‖ = ‖1 + Complex.sin ((π : ℂ) * s)‖ * (‖qHat (sTan s)‖ * ‖gS s‖ ^ 2) / (π ^ 2 * xiStar ^ 2) := by
    rw [Kfun_eq_qHat hs, norm_div, norm_mul, norm_mul, norm_pow, hN]
  have hτne : s.im ≠ 0 := by intro h; rw [h] at hτ; simp at hτ; linarith
  -- bounds on gS
  have hcos : 0 ≤ (cC s).re := by
    rw [re_cC]
    refine mul_nonneg (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩) (Real.cosh_pos _).le
    · nlinarith [hs.1]
    · nlinarith [hre]
  have hg1 : ‖gS s‖ ≤ 1 := norm_sInt_le_one (cos_im_zero_cases ⟨hs.1.le, hs.2⟩) hcos
  have hg2 := norm_gS_lower hs hτne
  have hx0 : 0 ≤ π * |s.im| := by positivity
  have hcC : ‖cC s‖ ≤ Real.exp (π * |s.im|) := by
    refine le_trans norm_cC_le ?_
    have := cosh_le_exp_abs (π * |s.im|)
    rwa [abs_of_nonneg hx0] at this
  have hsq : √‖cC s‖ ≤ Real.exp (π * |s.im| / 2) := by
    rw [Real.sqrt_le_iff]
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [← Real.exp_nat_mul]
    calc ‖cC s‖ ≤ Real.exp (π * |s.im|) := hcC
      _ = Real.exp (↑(2 : ℕ) * (π * |s.im| / 2)) := by congr 1; push_cast; ring
  have he1 : 1 ≤ Real.exp (π * |s.im| / 2) := Real.one_le_exp (by positivity)
  have hden : 1 + √‖cC s‖ ≤ 2 * Real.exp (π * |s.im| / 2) := by linarith
  have hgl : 1 / (2 * Real.exp (π * |s.im| / 2)) / √2 ≤ ‖gS s‖ := by
    refine le_trans ?_ hg2
    rw [div_div, show (1 : ℝ) / √2 * (1 / (1 + √‖cC s‖)) = 1 / (√2 * (1 + √‖cC s‖)) by field_simp]
    apply one_div_le_one_div_of_le (by positivity [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)])
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hA1 := norm_one_add_sin_ge hs
  have hA2 := norm_one_add_sin_le s
  have hq0 : 0 ≤ ‖qHat (sTan s)‖ := norm_nonneg _
  have hg0 : 0 ≤ ‖gS s‖ := norm_nonneg _
  have hE := Real.exp_pos (π * |s.im|)
  have hee : Real.exp (-(π * |s.im|)) = 1 / Real.exp (π * |s.im|) := by rw [Real.exp_neg]; simp
  have he2 : Real.exp (π * |s.im| / 2) ^ 2 = Real.exp (π * |s.im|) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he2pos := Real.exp_pos (π * |s.im| / 2)
  have hg2' : 1 / (8 * Real.exp (π * |s.im|)) ≤ ‖gS s‖ ^ 2 := by
    have h8 : (1 / (2 * Real.exp (π * |s.im| / 2)) / √2) ^ 2 = 1 / (8 * Real.exp (π * |s.im|)) := by
      rw [div_pow, div_pow, Real.sq_sqrt (by norm_num), mul_pow, he2]
      field_simp; norm_num
    rw [← h8]
    exact pow_le_pow_left₀ (by positivity) hgl 2
  constructor
  · rw [hKeq]
    have h1 : ‖qHat (sTan s)‖ * ‖gS s‖ ^ 2 ≤ Cq * 1 :=
      mul_le_mul hq2 (pow_le_one₀ hg0 hg1) (by positivity) hCq.le
    calc ‖1 + Complex.sin ((π : ℂ) * s)‖ * (‖qHat (sTan s)‖ * ‖gS s‖ ^ 2) / (π ^ 2 * xiStar ^ 2)
        ≤ (2 * Real.exp (π * |s.im|)) * (Cq * 1) / (π ^ 2 * xiStar ^ 2) := by
          apply div_le_div_of_nonneg_right _ hNN.le
          exact mul_le_mul hA2 h1 (by positivity) (by positivity)
      _ = 2 * Cq / (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|) := by ring
  · rw [hKeq, hee]
    have h1 : 1 / Cq * (1 / (8 * Real.exp (π * |s.im|))) ≤ ‖qHat (sTan s)‖ * ‖gS s‖ ^ 2 := by
      have hq1' : 1 / Cq ≤ ‖qHat (sTan s)‖ := hq1
      exact mul_le_mul hq1' hg2' (by positivity) hq0
    calc 1 / Real.exp (π * |s.im|) / (8 * Cq * (π ^ 2 * xiStar ^ 2))
        = 1 * (1 / Cq * (1 / (8 * Real.exp (π * |s.im|)))) / (π ^ 2 * xiStar ^ 2) := by
          field_simp
      _ ≤ ‖1 + Complex.sin ((π : ℂ) * s)‖ * (‖qHat (sTan s)‖ * ‖gS s‖ ^ 2) / (π ^ 2 * xiStar ^ 2) := by
          apply div_le_div_of_nonneg_right _ hNN.le
          exact mul_le_mul hA1 h1 (by positivity) (by positivity)

lemma Kfun_bounds {s : ℂ} (hs : s ∈ unitStrip) (hτ : 4 ≤ |s.im|) :
    ‖Kfun s‖ ≤ 2 * Cq / (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|) ∧
    Real.exp (-(π * |s.im|)) / (8 * Cq * (π ^ 2 * xiStar ^ 2)) ≤ ‖Kfun s‖ := by
  rcases le_total s.re (1 / 2) with h | h
  · exact Kfun_bounds_left hs h hτ
  · have hs' : 1 - s ∈ unitStrip := ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩
    have := Kfun_bounds_left hs' (by simp; linarith) (by simpa using hτ)
    rw [Kfun_one_sub] at this
    simpa using this

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Kfun_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kfun_bounds

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_Kb_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_Kb_left

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
