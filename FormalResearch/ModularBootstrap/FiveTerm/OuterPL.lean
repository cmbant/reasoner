module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterKfun
public import FormalResearch.ModularBootstrap.FiveTerm.OuterRest
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# `exp(4 h̄_{a_xb}) = K̄` on the closed strip (FIVE-S, `cts:outer-strip`)

With `H_xb = h̄_a - h̄_{a_rest}` (so `Re H_xb(it) = Re H_xb(1+it) = a_xb(t) = (1/4) log x_T + (1/4) log b_T - (1/2) log ξ*`),
the functions `exp(-4 H_xb) K̄` and `exp(4 H_xb) / K̄` are bounded by `1` on both edges (`|K̄| = x_T b_T/ξ*²`,
`OuterKfun`) and of controlled growth in the strip (`Kfun_bounds` for `|Im s| ≥ 4`, `re_hbarA_le/ge`), hence bounded by
`1` by Phragmen-Lindelof.  So `|exp(4 H_xb)| = |K̄|`, the ratio is a unimodular holomorphic function, constant, and
equal to `1` at `s = 1/2`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- `H_xb = h̄_a - h̄_{a_rest}`. -/
noncomputable def Hxb (s : ℂ) : ℂ := hbarA aAmp s - hbarA aRest s

lemma continuousOn_Hxb : ContinuousOn Hxb closedStrip :=
  (continuousOn_hbarA amp_aAmp).sub (continuousOn_hbarA amp_aRest)

lemma differentiableOn_hbarA_strip {a : ℝ → ℝ} (ha : Amp a) : DifferentiableOn ℂ (hbarA a) strip :=
  (differentiableOn_genH ha).congr (fun _ hs => hbarA_of_mem_strip ha hs)

lemma differentiableOn_Hxb : DifferentiableOn ℂ Hxb strip :=
  (differentiableOn_hbarA_strip amp_aAmp).sub (differentiableOn_hbarA_strip amp_aRest)

lemma re_Hxb_left (t : ℝ) : (Hxb (Complex.I * (t : ℂ))).re = aXb t := by
  unfold Hxb
  rw [Complex.sub_re, re_hbarA_left amp_aAmp, re_hbarA_left amp_aRest, aAmp_eq_aXb_add_aRest]; ring

lemma re_Hxb_right (t : ℝ) : (Hxb (1 + Complex.I * (t : ℂ))).re = aXb t := by
  unfold Hxb
  rw [Complex.sub_re, re_hbarA_right amp_aAmp, re_hbarA_right amp_aRest, aAmp_eq_aXb_add_aRest]; ring

lemma exists_re_Hxb_bound : ∃ a b : ℝ, 0 ≤ a ∧ ∀ s ∈ closedStrip, |(Hxb s).re| ≤ a * |s.im| + b := by
  obtain ⟨⟨m, hm⟩, ⟨β, hβ⟩⟩ := exists_aAmp_bounds
  obtain ⟨κ, hκ⟩ := re_hbarA_le amp_aAmp (by positivity : (0 : ℝ) ≤ 5 * π / 8) hβ
  obtain ⟨κ', hκ'⟩ := re_hbarA_le amp_aRest (by positivity : (0 : ℝ) ≤ π / 2) (fun t => aRest_le t)
  set β' : ℝ := ((1 / 2) * Real.log 2 - 2 * Real.log (1 - Real.exp (-(4 * π * xiStar)))) with hβ'
  have hpi := Real.pi_pos
  refine ⟨5 * π / 8 + π / 2, |m| + |β| + 5 * π / 8 * |κ| + |(-((13 / 4) * Real.log 2))| + |β'| + π / 2 * |κ'|,
    by positivity, fun s hs => ?_⟩
  have h1 := re_hbarA_ge amp_aAmp hm hs
  have h2 := hκ s hs
  have h3 := re_hbarA_ge amp_aRest (fun t => aRest_ge t) hs
  have h4 := hκ' s hs
  have hs0 : 0 ≤ |s.im| := abs_nonneg _
  have hRe : (Hxb s).re = (hbarA aAmp s).re - (hbarA aRest s).re := by unfold Hxb; rw [Complex.sub_re]
  rw [hRe, abs_le]
  have a1 : -(|m|) ≤ m := neg_abs_le m
  have a2 : β ≤ |β| := le_abs_self β
  have a3 : 5 * π / 8 * κ ≤ 5 * π / 8 * |κ| := mul_le_mul_of_nonneg_left (le_abs_self κ) (by positivity)
  have a4 : -((13 / 4) * Real.log 2) ≤ |(-((13 / 4) * Real.log 2))| := le_abs_self _
  have a5 : -(|(-((13 / 4) * Real.log 2))|) ≤ -((13 / 4) * Real.log 2) := neg_abs_le _
  have a6 : β' ≤ |β'| := le_abs_self β'
  have a7 : -(|β'|) ≤ β' := neg_abs_le β'
  have a8 : π / 2 * κ' ≤ π / 2 * |κ'| := mul_le_mul_of_nonneg_left (le_abs_self κ') (by positivity)
  have a9 : π / 2 * (-|κ'|) ≤ π / 2 * κ' := mul_le_mul_of_nonneg_left (neg_abs_le κ') (by positivity)
  have a10 : 5 * π / 8 * (-|κ|) ≤ 5 * π / 8 * κ := mul_le_mul_of_nonneg_left (neg_abs_le κ) (by positivity)
  have hn : 0 ≤ |m| + |β| + 5 * π / 8 * |κ| + |(-((13 / 4) * Real.log 2))| + |β'| + π / 2 * |κ'| := by positivity
  constructor
  · nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ π / 2) hs0, mul_nonneg (by positivity : (0 : ℝ) ≤ 5 * π / 8) hs0,
      abs_nonneg m, abs_nonneg β, abs_nonneg κ, abs_nonneg β', abs_nonneg κ', abs_nonneg ((-((13 / 4) * Real.log 2)))]
  · nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ π / 2) hs0, mul_nonneg (by positivity : (0 : ℝ) ≤ 5 * π / 8) hs0,
      abs_nonneg m, abs_nonneg β, abs_nonneg κ, abs_nonneg β', abs_nonneg κ', abs_nonneg ((-((13 / 4) * Real.log 2)))]

/-- Phragmen-Lindelof on the unit strip in the form used here. -/
lemma pl_unit_strip {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f unitStrip) (hc : ContinuousOn f unitStripCl)
    {a b : ℝ} (ha : 0 ≤ a)
    (hg : ∀ s ∈ unitStrip, 4 ≤ |s.im| → ‖f s‖ ≤ Real.exp (a * |s.im| + b))
    (hl : ∀ t : ℝ, ‖f ((t : ℂ) * Complex.I)‖ ≤ 1) (hr : ∀ t : ℝ, ‖f (1 + (t : ℂ) * Complex.I)‖ ≤ 1) :
    ∀ s ∈ unitStripCl, ‖f s‖ ≤ 1 := by
  intro s hs
  have hS : (re ⁻¹' Ioo (0 : ℝ) 1) = unitStrip := by
    ext z; simp [unitStrip]
  have hcl : closure (re ⁻¹' Ioo (0 : ℝ) 1) ⊆ unitStripCl := by
    rw [hS]; exact closure_unitStrip_subset
  refine PhragmenLindelof.vertical_strip (a := 0) (b := 1) (C := 1) ?_ ?_ ?_ ?_ hs.1 hs.2
  · exact ⟨by rw [hS]; exact hd, hc.mono hcl⟩
  · refine ⟨1, by linarith [Real.pi_gt_three], a + |b|, ?_⟩
    refine Asymptotics.IsBigO.of_bound 1 ?_
    rw [eventually_inf_principal]
    filter_upwards [(eventually_ge_atTop (4 : ℝ)).comap (_root_.abs ∘ Complex.im)] with z hz hzS
    rw [hS] at hzS
    have hz4 : 4 ≤ |z.im| := hz
    have h1 := hg z hzS hz4
    have h2 : |z.im| ≤ Real.exp |z.im| := by have := Real.add_one_le_exp |z.im|; linarith
    have h3 : 1 ≤ Real.exp |z.im| := Real.one_le_exp (abs_nonneg _)
    have h4 : a * |z.im| + b ≤ (a + |b|) * Real.exp (1 * |z.im|) := by
      rw [one_mul]
      nlinarith [le_abs_self b, mul_nonneg ha (by linarith : 0 ≤ Real.exp |z.im| - |z.im|),
        mul_nonneg (abs_nonneg b) (by linarith : 0 ≤ Real.exp |z.im| - 1)]
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h1.trans (Real.exp_le_exp.mpr h4)
  · intro z hz
    have := hl z.im
    have e : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz]
    rw [e]; exact this
  · intro z hz
    have := hr z.im
    have e : z = 1 + (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz]
    rw [e]; exact this


lemma convex_unitStrip : Convex ℝ unitStrip := by
  have : unitStrip = (Complex.reLm ⁻¹' Ioo (0 : ℝ) 1) := by
    ext z; simp [unitStrip]
  rw [this]
  exact (convex_Ioo (0 : ℝ) 1).linear_preimage Complex.reLm

lemma norm_exp_neg4 (s : ℂ) : ‖Complex.exp ((-4 : ℂ) * Hxb s)‖ = Real.exp (-4 * (Hxb s).re) := by
  rw [Complex.norm_exp]; simp

lemma norm_exp_pos4 (s : ℂ) : ‖Complex.exp ((4 : ℂ) * Hxb s)‖ = Real.exp (4 * (Hxb s).re) := by
  rw [Complex.norm_exp]; simp

lemma exp_mul_const {x C : ℝ} (hC : 0 < C) : Real.exp x * C = Real.exp (x + Real.log C) := by
  rw [Real.exp_add, Real.exp_log hC]

/-- Growth of `exp(±4 H_xb)`. -/
lemma norm_Hxb_pm_bound : ∃ A B : ℝ, 0 ≤ A ∧ ∀ s ∈ closedStrip,
    ‖Complex.exp ((-4 : ℂ) * Hxb s)‖ ≤ Real.exp (A * |s.im| + B) ∧
    ‖Complex.exp ((4 : ℂ) * Hxb s)‖ ≤ Real.exp (A * |s.im| + B) := by
  obtain ⟨a, b, ha, hb⟩ := exists_re_Hxb_bound
  refine ⟨4 * a, 4 * b, by positivity, fun s hs => ?_⟩
  have h := hb s hs
  rw [norm_exp_neg4, norm_exp_pos4]
  have := abs_le.mp h
  constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [this.1, this.2]

lemma re_Hxb_left' (t : ℝ) : (Hxb ((t : ℂ) * Complex.I)).re = aXb t := by
  rw [mul_comm]; exact re_Hxb_left t

lemma re_Hxb_right' (t : ℝ) : (Hxb (1 + (t : ℂ) * Complex.I)).re = aXb t := by
  rw [mul_comm]; exact re_Hxb_right t

lemma pos_xb (t : ℝ) : 0 < xT t * bT t / xiStar ^ 2 := by
  have := xT_pos t; have := bT_pos t; have := xiStar_pos; positivity

theorem norm_exp_four_Hxb_eq {s : ℂ} (hs : s ∈ unitStripCl) :
    ‖Complex.exp ((4 : ℂ) * Hxb s)‖ = ‖Kb s‖ := by
  obtain ⟨A, B, hA, hAB⟩ := norm_Hxb_pm_bound
  have hNN : 0 < π ^ 2 * xiStar ^ 2 := by have := xiStar_pos; have := Real.pi_pos; positivity
  have hCq := Cq_pos
  have hC1 : 0 < 2 * Cq / (π ^ 2 * xiStar ^ 2) := by positivity
  have hC2 : 0 < 8 * Cq * (π ^ 2 * xiStar ^ 2) := by positivity
  have hKne : ∀ s ∈ unitStripCl, Kb s ≠ 0 := fun s hs => Kb_ne_zero hs
  have hKc := continuousOn_Kb
  have hHc : ContinuousOn Hxb unitStripCl := continuousOn_Hxb
  have hKd : DifferentiableOn ℂ Kb unitStrip :=
    differentiableOn_Kfun.congr (fun _ hs => Kb_of_mem hs)
  have hHd : DifferentiableOn ℂ Hxb unitStrip := differentiableOn_Hxb
  have hKne' : ∀ s ∈ unitStrip, Kb s ≠ 0 := fun s hs => Kb_ne_zero (unitStrip_subset_cl hs)
  -- f1 = exp(-4H) K
  have h1 : ‖Complex.exp ((-4 : ℂ) * Hxb s) * Kb s‖ ≤ 1 := by
    refine pl_unit_strip (f := fun s => Complex.exp ((-4 : ℂ) * Hxb s) * Kb s)
      (a := A + π) (b := B + Real.log (2 * Cq / (π ^ 2 * xiStar ^ 2)))
      ((hHd.const_mul _).cexp.mul hKd)
      (((hHc.const_mul _).cexp).mul hKc) (by positivity) ?_ ?_ ?_ s hs
    · intro s hs hτ
      rw [norm_mul, Kb_of_mem hs]
      have h1 := (hAB s (unitStrip_subset_cl hs)).1
      have h2 := (Kfun_bounds hs hτ).1
      calc ‖Complex.exp ((-4 : ℂ) * Hxb s)‖ * ‖Kfun s‖
          ≤ Real.exp (A * |s.im| + B) * (2 * Cq / (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp ((A + π) * |s.im| + (B + Real.log (2 * Cq / (π ^ 2 * xiStar ^ 2)))) := by
            have : Real.exp (A * |s.im| + B) * (2 * Cq / (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|)) =
                Real.exp (A * |s.im| + B) * Real.exp (π * |s.im|) * (2 * Cq / (π ^ 2 * xiStar ^ 2)) := by ring
            rw [this, ← Real.exp_add, exp_mul_const hC1]; congr 1; ring
    · intro t
      rw [norm_mul, norm_exp_neg4, re_Hxb_left', norm_Kb_left, ← exp_four_aXb, ← Real.exp_add]; simp
    · intro t
      rw [norm_mul, norm_exp_neg4, re_Hxb_right', norm_Kb_right, ← exp_four_aXb, ← Real.exp_add]; simp
  -- f2 = exp(4H) / K
  have h2 : ‖Complex.exp ((4 : ℂ) * Hxb s) * (Kb s)⁻¹‖ ≤ 1 := by
    refine pl_unit_strip (f := fun s => Complex.exp ((4 : ℂ) * Hxb s) * (Kb s)⁻¹)
      (a := A + π) (b := B + Real.log (8 * Cq * (π ^ 2 * xiStar ^ 2)))
      ((hHd.const_mul _).cexp.mul (hKd.inv hKne'))
      (((hHc.const_mul _).cexp).mul (hKc.inv₀ hKne)) (by positivity) ?_ ?_ ?_ s hs
    · intro s hs hτ
      rw [norm_mul, norm_inv, Kb_of_mem hs]
      have h1 := (hAB s (unitStrip_subset_cl hs)).2
      have h2 := (Kfun_bounds hs hτ).2
      have hKpos : 0 < ‖Kfun s‖ := norm_pos_iff.mpr (Kfun_ne_zero hs)
      have h3 : ‖Kfun s‖⁻¹ ≤ 8 * Cq * (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|) := by
        have := inv_anti₀ (by positivity) h2
        rw [inv_div, Real.exp_neg, div_inv_eq_mul] at this
        simpa [mul_comm, mul_assoc, mul_left_comm] using this
      calc ‖Complex.exp ((4 : ℂ) * Hxb s)‖ * ‖Kfun s‖⁻¹
          ≤ Real.exp (A * |s.im| + B) * (8 * Cq * (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|)) :=
            mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
        _ = Real.exp ((A + π) * |s.im| + (B + Real.log (8 * Cq * (π ^ 2 * xiStar ^ 2)))) := by
            have : Real.exp (A * |s.im| + B) * (8 * Cq * (π ^ 2 * xiStar ^ 2) * Real.exp (π * |s.im|)) =
                Real.exp (A * |s.im| + B) * Real.exp (π * |s.im|) * (8 * Cq * (π ^ 2 * xiStar ^ 2)) := by ring
            rw [this, ← Real.exp_add, exp_mul_const hC2]; congr 1; ring
    · intro t
      rw [norm_mul, norm_inv, norm_exp_pos4, re_Hxb_left', norm_Kb_left, ← exp_four_aXb]
      have := Real.exp_pos (4 * aXb t)
      field_simp; simp
    · intro t
      rw [norm_mul, norm_inv, norm_exp_pos4, re_Hxb_right', norm_Kb_right, ← exp_four_aXb]
      have := Real.exp_pos (4 * aXb t)
      field_simp; simp
  have hKpos : 0 < ‖Kb s‖ := norm_pos_iff.mpr (hKne s hs)
  rw [norm_mul, norm_exp_neg4] at h1
  rw [norm_mul, norm_inv, norm_exp_pos4] at h2
  rw [norm_exp_pos4]
  have e1 : Real.exp (-4 * (Hxb s).re) = (Real.exp (4 * (Hxb s).re))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e1] at h1
  have hEpos := Real.exp_pos (4 * (Hxb s).re)
  apply le_antisymm
  · rwa [← div_eq_mul_inv, div_le_one hKpos] at h2
  · rwa [← div_eq_inv_mul, div_le_one hEpos] at h1


lemma Kfun_half : Kfun (1 / 2 : ℂ) = ((2 / (π ^ 2 * xiStar ^ 2) : ℝ) : ℂ) := by
  have h1 : Complex.sin ((π : ℂ) * (1 / 2)) = 1 := by
    rw [show (π : ℂ) * (1 / 2) = (π / 2 : ℂ) by ring, Complex.sin_pi_div_two]
  have h2 : gS (1 / 2 : ℂ) = 1 := by
    unfold gS
    rw [show (π : ℂ) * (1 / 2) = (π / 2 : ℂ) by ring, Complex.cos_pi_div_two]
    exact sInt_zero'
  have h3 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  unfold Kfun
  rw [h3, h1, h2]
  push_cast
  ring

lemma im_Hxb_real {s : ℂ} (hs : s ∈ closedStrip) (hr : starRingEnd ℂ s = s) : (Hxb s).im = 0 := by
  unfold Hxb
  have h1 := hbarA_conj amp_aAmp hs
  have h2 := hbarA_conj amp_aRest hs
  rw [hr] at h1 h2
  have a1 : (hbarA aAmp s).im = 0 := by
    have := congrArg Complex.im h1; simp at this; linarith
  have a2 : (hbarA aRest s).im = 0 := by
    have := congrArg Complex.im h2; simp at this; linarith
  rw [Complex.sub_im, a1, a2]; simp

/-- **`exp(4 H_xb) = K̄` on the closed strip.** -/
theorem exp_four_Hxb {s : ℂ} (hs : s ∈ unitStripCl) : Complex.exp ((4 : ℂ) * Hxb s) = Kb s := by
  have hKne : ∀ s ∈ unitStripCl, Kb s ≠ 0 := fun s hs => Kb_ne_zero hs
  have hKd : DifferentiableOn ℂ Kb unitStrip :=
    differentiableOn_Kfun.congr (fun _ hs => Kb_of_mem hs)
  have hKne' : ∀ s ∈ unitStrip, Kb s ≠ 0 := fun s hs => Kb_ne_zero (unitStrip_subset_cl hs)
  set E : ℂ → ℂ := fun s => Complex.exp ((4 : ℂ) * Hxb s) * (Kb s)⁻¹ with hE
  have hEd : DifferentiableOn ℂ E unitStrip := (differentiableOn_Hxb.const_mul _).cexp.mul (hKd.inv hKne')
  have hEn : ∀ s ∈ unitStrip, ‖E s‖ = 1 := by
    intro s hs
    have := norm_exp_four_Hxb_eq (unitStrip_subset_cl hs)
    have hk : 0 < ‖Kb s‖ := norm_pos_iff.mpr (hKne' s hs)
    rw [hE]; simp only [norm_mul, norm_inv, this]
    field_simp
  have hc : (1 / 2 : ℂ) ∈ unitStrip := ⟨by simp, by simp; norm_num⟩
  have hmax : IsMaxOn (norm ∘ E) unitStrip (1 / 2 : ℂ) := by
    intro z hz
    simp only [Function.comp, mem_ofPred_eq]
    rw [hEn z hz, hEn _ hc]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm convex_unitStrip.isPreconnected
    isOpen_unitStrip hEd hc hmax
  -- value at 1/2
  have hE1 : E (1 / 2 : ℂ) = 1 := by
    have hcl : (1 / 2 : ℂ) ∈ closedStrip := ⟨by simp, by simp; norm_num⟩
    have hreal : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by apply Complex.ext <;> simp
    have him := im_Hxb_real hcl hreal
    have hH : Hxb (1 / 2 : ℂ) = (((Hxb (1 / 2 : ℂ)).re : ℝ) : ℂ) := by
      exact Complex.ext (by simp) (by simpa using him)
    have hK : Kb (1 / 2 : ℂ) = Kfun (1 / 2 : ℂ) := Kb_of_mem hc
    have hpos : 0 < 2 / (π ^ 2 * xiStar ^ 2) := by
      have := xiStar_pos; have := Real.pi_pos; positivity
    have hEval : E (1 / 2 : ℂ) =
        ((Real.exp (4 * (Hxb (1 / 2 : ℂ)).re) / (2 / (π ^ 2 * xiStar ^ 2)) : ℝ) : ℂ) := by
      rw [hE]
      simp only
      rw [hK, Kfun_half, hH]
      push_cast
      simp [div_eq_mul_inv]
    have hnorm := hEn _ hc
    rw [hEval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hnorm
    rw [hEval, hnorm]; simp
  have hall : ∀ s ∈ unitStrip, Complex.exp ((4 : ℂ) * Hxb s) = Kb s := by
    intro s hs
    have h := hconst hs
    simp only [Function.const_apply] at h
    rw [hE1] at h
    have : Complex.exp ((4 : ℂ) * Hxb s) * (Kb s)⁻¹ = 1 := h
    have hk := hKne' s hs
    field_simp at this
    exact this
  have hcont1 : ContinuousOn (fun s => Complex.exp ((4 : ℂ) * Hxb s)) unitStripCl :=
    (continuousOn_Hxb.const_mul _).cexp
  exact (Set.EqOn.of_subset_closure hall hcont1 continuousOn_Kb unitStrip_subset_cl
    unitStripCl_subset_closure) hs

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.exp_four_Hxb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_four_Hxb

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
