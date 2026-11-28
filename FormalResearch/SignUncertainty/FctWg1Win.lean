/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.UctSeedWindow
public import FormalResearch.SignUncertainty.FctWg1EdgeBounds

/-!
# Fixed Airy window `(fct:hg1-win)` for `ctWg1`

Proves `ctWg1_win_bound`: for `ε = ±1`, `Sw : ℝ`, `c ≥ c₀(Sw)`, and `|hbS c ξ| ≤ Sw`,

  `|normDensity (ctWg1 ε c) c ξ - (ceK / ceCs) * ceG1 (airyZero 1) (-ceBeta1 * hbS c ξ + ceBeta1 * (deriv (outerTheta ε) 0 / π²) * liftEps c)| ≤ C * c ^ (-(2 / 3 : ℝ))`.

Proof: clone `UctSeedWindow.seed_window` for `wg1PartA` (replacing left `seedT δ` with `ctTg1 = seedT 0 - seedT 1` on `0 ≤ w.re`,
with `hasU2_ceG1` and `continuous_ceG1` in `airy_reference_identity`) and absorb `wg1PartB` via `ctWg1_partB_bound`.

Class: proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma ctTg1_eq_seedT_sub {w : ℂ} (hw : 0 ≤ w.re) :
    ctTg1 w = seedT 0 w - seedT 1 w := by
  rw [seedT_eq_text 0 hw, seedT_eq_text 1 hw]
  unfold seedText ctTg1
  rw [uctG1Ext_eq hw]
  simp

private lemma wg1PartA_differentiableOn {ε c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (wg1PartA ε c) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
  have ha := seedScale_pos hc
  have hZ : DifferentiableOn ℂ (uctSeedZ ε) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (differentiableOn_uctSeedZ ε).mono fun ζ hζ => ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have hH : DifferentiableOn ℂ outerHbar {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    differentiableOn_outerH.congr fun z hz => outerHbar_of_mem_strip hz
  have hT0 : DifferentiableOn ℂ (fun ζ : ℂ => seedT 0 ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (seedT_differentiableOn 0).comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => (seedScale c : ℂ) * ζ).differentiableOn
      fun ζ hζ => by show 0 < ((seedScale c : ℂ) * ζ).re; rw [re_mul_real]; exact mul_pos ha hζ.1
  have hT1 : DifferentiableOn ℂ (fun ζ : ℂ => seedT 1 ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (seedT_differentiableOn 1).comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => (seedScale c : ℂ) * ζ).differentiableOn
      fun ζ hζ => by show 0 < ((seedScale c : ℂ) * ζ).re; rw [re_mul_real]; exact mul_pos ha hζ.1
  have hG1 : DifferentiableOn ℂ (fun ζ : ℂ => ctTg1 ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (hT0.sub hT1).congr fun ζ hζ => by
      have hre : 0 ≤ ((seedScale c : ℂ) * ζ).re := by rw [re_mul_real]; exact (mul_pos ha hζ.1).le
      exact ctTg1_eq_seedT_sub hre
  have hT2 : DifferentiableOn ℂ (fun ζ : ℂ => seedT 0 ((seedScale c : ℂ) * (1 - ζ))) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (seedT_differentiableOn 0).comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).differentiableOn
      fun ζ hζ => by show 0 < ((seedScale c : ℂ) * (1 - ζ)).re; rw [re_mul_real_one_sub]; exact mul_pos ha (by linarith [hζ.2])
  unfold wg1PartA
  exact (((hZ.mul hH.neg.cexp).mul (hG1.mul hT2))).const_mul _

private lemma wg1PartA_continuousOn {ε c : ℝ} (hc : 0 < c) :
    ContinuousOn (wg1PartA ε c) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
  have ha := seedScale_pos hc
  have hZ : ContinuousOn (uctSeedZ ε) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (differentiableOn_uctSeedZ ε).continuousOn.mono fun ζ hζ => ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
  have hH : ContinuousOn outerHbar {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := continuousOn_outerHbar
  have hT0 : ContinuousOn (fun ζ : ℂ => seedT 0 ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (seedT_continuousOn 0).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * ζ).continuousOn
      fun ζ hζ => by show 0 ≤ ((seedScale c : ℂ) * ζ).re; rw [re_mul_real]; exact mul_nonneg ha.le hζ.1
  have hT1 : ContinuousOn (fun ζ : ℂ => seedT 1 ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (seedT_continuousOn 1).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * ζ).continuousOn
      fun ζ hζ => by show 0 ≤ ((seedScale c : ℂ) * ζ).re; rw [re_mul_real]; exact mul_nonneg ha.le hζ.1
  have hG1 : ContinuousOn (fun ζ : ℂ => ctTg1 ((seedScale c : ℂ) * ζ)) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (hT0.sub hT1).congr fun ζ hζ => by
      have hre : 0 ≤ ((seedScale c : ℂ) * ζ).re := by rw [re_mul_real]; exact mul_nonneg ha.le hζ.1
      exact ctTg1_eq_seedT_sub hre
  have hT2 : ContinuousOn (fun ζ : ℂ => seedT 0 ((seedScale c : ℂ) * (1 - ζ))) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (seedT_continuousOn 0).comp (by fun_prop : Continuous fun ζ : ℂ => (seedScale c : ℂ) * (1 - ζ)).continuousOn
      fun ζ hζ => by show 0 ≤ ((seedScale c : ℂ) * (1 - ζ)).re; rw [re_mul_real_one_sub]; exact mul_nonneg ha.le (by linarith [hζ.2])
  unfold wg1PartA
  exact (((hZ.mul hH.neg.cexp).mul (hG1.mul hT2))).const_mul _

private lemma wg1PartA_sy_bound (ε : ℝ) :
    ∃ c₁ CW : ℝ, 64 ≤ c₁ ∧ 0 < CW ∧ ∀ {c : ℝ}, c₁ ≤ c → ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖wg1PartA ε c ((liftEps c : ℂ) * w)‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨c₁, hc₁, hratio⟩ := seed_ratio_bound
  obtain ⟨CZ, hCZ0, hZh⟩ := seedZh_bound ε
  obtain ⟨CT, hCT0, hT⟩ := seedT_unif
  refine ⟨c₁, 8 * (CZ + 1) * (2 * CT) + 1, hc₁, by positivity, fun {c} hc w hw0 hw1 => ?_⟩
  have hc64 : 64 ≤ c := hc₁.trans hc
  have hc0 : 0 < c := by linarith
  have hς14 : liftEps c ≤ 1 / 4 := liftEps_le_quarter hc64
  have hς0 : 0 ≤ liftEps c := (liftEps_pos hc0).le
  set ζ : ℂ := (liftEps c : ℂ) * w
  have hζ_le_ς : ζ.re ≤ liftEps c := by
    dsimp only [ζ]; rw [re_mul_real]; exact mul_le_of_le_one_right hς0 hw1
  have hζ_mem : ζ ∈ closedStrip := ⟨by rw [re_mul_real]; exact mul_nonneg hς0 hw0,
    hζ_le_ς.trans (by linarith)⟩
  have hzh := hZh ζ hζ_mem
  have hrt := hratio c 0 hc le_rfl zero_le_one ζ hζ_mem.1 hζ_le_ς
  have hsc : (seedScale c : ℂ) * ζ = (ceCs : ℂ) * w := by
    dsimp only [ζ]; rw [← mul_assoc, ← Complex.ofReal_mul, seedScale_mul_liftEps hc0]
  have hG1 : ‖ctTg1 ((ceCs : ℂ) * w)‖ ≤ 2 * CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    have hre : 0 ≤ ((ceCs : ℂ) * w).re := by rw [re_mul_real]; exact mul_nonneg ceCs_pos.le hw0
    rw [ctTg1_eq_seedT_sub hre]
    have h0 := hT 0 le_rfl zero_le_one w hw0
    have h1 := hT 1 zero_le_one le_rfl w hw0
    calc ‖seedT 0 ((ceCs : ℂ) * w) - seedT 1 ((ceCs : ℂ) * w)‖
        ≤ ‖seedT 0 ((ceCs : ℂ) * w)‖ + ‖seedT 1 ((ceCs : ℂ) * w)‖ := norm_sub_le _ _
      _ ≤ CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) + CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := add_le_add h0 h1
      _ = 2 * CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by ring
  have hpart : wg1PartA ε c ζ =
      ((seedT 0 (seedScale c : ℂ))⁻¹ * seedT 0 ((seedScale c : ℂ) * (1 - ζ))) *
        (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)) * ctTg1 ((ceCs : ℂ) * w) := by
    unfold wg1PartA; rw [hsc]; ring
  rw [hpart, norm_mul, norm_mul]
  calc ‖(seedT 0 (seedScale c : ℂ))⁻¹ * seedT 0 ((seedScale c : ℂ) * (1 - ζ))‖ *
        ‖uctSeedZ ε ζ * Complex.exp (-outerHbar ζ)‖ * ‖ctTg1 ((ceCs : ℂ) * w)‖
      ≤ 8 * CZ * (2 * CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (mul_le_mul hrt hzh (norm_nonneg _) (by positivity)) hG1 (norm_nonneg _) (by positivity)
    _ ≤ (8 * (CZ + 1) * (2 * CT) + 1) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
        have hpos : 0 ≤ (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by positivity
        nlinarith

private lemma wg1PartA_win_single {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (Sw : ℝ) :
    ∃ c₀ C : ℝ, 64 ≤ c₀ ∧ 0 < C ∧ ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      |normDensity (wg1PartA ε c) c ξ -
          ceK / ceCs * ceG1 (Special.airyZero 1)
            (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)| ≤
        C * c ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨c₁, CW, hc₁, hCW, hSy⟩ := wg1PartA_sy_bound ε
  obtain ⟨CT, hCT, hT⟩ := seedT_unif
  obtain ⟨c₂, Cq, hc₂, hCq, hQ⟩ := seedQ_expansion hε
  obtain ⟨Cm, hCm, hmain⟩ := main_line_diff_sym Sw CW hCW
  set lam : ℝ := seedLam ε
  set θ : ℝ := deriv (outerTheta ε) 0
  have hlamθ : lam = θ + 1 / 2 := rfl
  set CE : ℝ := Real.exp |lam| * (2 * CT)
  obtain ⟨Cr, hCr, href⟩ := ref_symbol_diff Sw (4 * Cq * CT) CW CE (by positivity) hCW.le (by positivity)
  refine ⟨max (max c₁ c₂) (max 32768 64), (Cm + Cr) / (2 * Real.pi) + 1,
    le_max_of_le_right (le_max_right _ _), by positivity, fun {c ξ} hc hξ hS => ?_⟩
  have hcc1 : c₁ ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcc2 : c₂ ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc32 : 32768 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith
  set ς : ℝ := liftEps c
  have hς : 0 < ς := liftEps_pos hc0
  have hcube : c * ς ^ 3 = 1 := by have := liftEps_cube_mul hc0; linarith
  have hς1 : ς ≤ 1 / 32 := liftEps_le_of_large hc32
  have hς2 : ς ≤ 1 / 2 := by linarith
  set S : ℝ := hbS c ξ
  have hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ς ^ 2 * S := hb_L_eq hc0
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  set Sy : ℂ → ℂ := fun w => wg1PartA ε c ((ς : ℂ) * w)
  have hSyb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Sy w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) :=
    fun w h0 h1 => hSy hcc1 w h0 h1
  have hlin : Differentiable ℂ (fun w : ℂ => (ς : ℂ) * w) := (differentiable_const _).mul differentiable_id
  have hSyc : ContinuousOn Sy {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} :=
    (wg1PartA_continuousOn hc0).comp hlin.continuous.continuousOn fun w hw => by
      simp only [Set.mem_ofPred_eq, re_mul_real]; constructor <;> nlinarith [hw.1, hw.2]
  have hSyd : DifferentiableOn ℂ Sy {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (wg1PartA_differentiableOn hc0).comp hlin.differentiableOn fun w hw => by
      simp only [Set.mem_ofPred_eq, re_mul_real]; constructor <;> nlinarith [hw.1, hw.2]
  obtain ⟨hKc, hKd, hKb⟩ := K0_kernel_props (c := c) (S := S) hς hcube hς2 hξ hL
  set BK : ℝ := 2 * Real.exp (1 + Real.pi ^ 2 * |S|)
  have hAb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖mellinK0 c ((ς : ℂ) * w) ξ * Sy w‖ ≤ (BK * CW) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := fun w h0 h1 => by
    rw [norm_mul]
    calc ‖mellinK0 c ((ς : ℂ) * w) ξ‖ * ‖Sy w‖ ≤ BK * (CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (hKb w h0 h1) (hSyb w h0 h1) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have shA : ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I) =
      ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((v : ℂ) * Complex.I)) ξ * Sy ((v : ℂ) * Complex.I) := by
    have := strip_shift_weight (H := fun w => mellinK0 c ((ς : ℂ) * w) ξ * Sy w) (B := BK * CW)
      (hKc.mul hSyc) (hKd.mul hSyd) hAb
    simpa using this
  set Eref : ℝ := Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1)
  have hRb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖refKernel S ς w‖ ≤ Eref := fun w h0 h1 => by
    have := norm_refKernel_strip_le (S := S) (ε := ς) (σ := w.re) (v := w.im) (Sw := Sw) (by linarith) hS h0 h1
    rwa [Complex.re_add_im] at this
  have hRdiff : Differentiable ℂ (refKernel S ς) := by unfold refKernel; fun_prop
  set Ey : ℂ → ℂ := fun w => Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w)) * ctTg1 ((ceCs : ℂ) * w)
  have hexpb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))‖ ≤ Real.exp |lam| := by
    intro w h0 h1
    rw [Complex.norm_exp]; refine Real.exp_le_exp.mpr ?_
    have : (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w)).re = -(lam * (ς * w.re)) := by simp [Complex.mul_re]
    rw [this]
    have h2 : ς * w.re ≤ 1 := by nlinarith
    have h3 : 0 ≤ ς * w.re := by positivity
    calc -(lam * (ς * w.re)) ≤ |lam * (ς * w.re)| := neg_le_abs _
      _ = |lam| * (ς * w.re) := by rw [abs_mul, abs_of_nonneg h3]
      _ ≤ |lam| * 1 := by gcongr
      _ = |lam| := mul_one _
  have hG1_unif : ∀ w : ℂ, 0 ≤ w.re → ‖ctTg1 ((ceCs : ℂ) * w)‖ ≤ 2 * CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := fun w hw0 => by
    have hre : 0 ≤ ((ceCs : ℂ) * w).re := by rw [re_mul_real]; exact mul_nonneg ceCs_pos.le hw0
    rw [ctTg1_eq_seedT_sub hre]
    calc ‖seedT 0 ((ceCs : ℂ) * w) - seedT 1 ((ceCs : ℂ) * w)‖
        ≤ ‖seedT 0 ((ceCs : ℂ) * w)‖ + ‖seedT 1 ((ceCs : ℂ) * w)‖ := norm_sub_le _ _
      _ ≤ CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) + CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) :=
          add_le_add (hT 0 le_rfl zero_le_one w hw0) (hT 1 zero_le_one le_rfl w hw0)
      _ = 2 * CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by ring
  have hEyb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Ey w‖ ≤ CE * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := fun w h0 h1 => by
    dsimp only [Ey, CE]; rw [norm_mul]
    calc ‖Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))‖ * ‖ctTg1 ((ceCs : ℂ) * w)‖
        ≤ Real.exp |lam| * (2 * CT * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (hexpb w h0 h1) (hG1_unif w h0) (norm_nonneg _) (Real.exp_pos _).le
      _ = (Real.exp |lam| * (2 * CT)) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by ring
  have hG1_sym : ∀ {w : ℂ}, 0 ≤ w.re → ‖liftSymbol (ceG1 (Special.airyZero 1)) 0 0 w‖ ≤
      (2 * CT) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := fun {w} hw0 => by
    rw [liftSymbol_zero_order]; exact hG1_unif w hw0
  have hshR : ∫ v : ℝ, refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * Ey ((1 : ℂ) + (v : ℂ) * Complex.I) =
      ∫ v : ℝ, refKernel S ς ((v : ℂ) * Complex.I) * Ey ((v : ℂ) * Complex.I) := by
    have hpt : ∀ w : ℂ, refKernel S ς w * Ey w =
        (refKernel S ς w * Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))) *
          liftSymbol (ceG1 (Special.airyZero 1)) 0 0 w := fun w => by
      dsimp only [Ey, ctTg1]; rw [liftSymbol_zero_order]; ring
    simp_rw [hpt]
    exact shift_kernel_lift hasU2_ceG1 le_rfl 0 hG1_sym
      (Kf := fun w => refKernel S ς w * Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w)))
      ((hRdiff.continuous.continuousOn).mul (by fun_prop))
      (hRdiff.differentiableOn.mul (by fun_prop))
      fun w h0 h1 => by
        rw [norm_mul]
        exact mul_le_mul (hRb w h0 h1) (hexpb w h0 h1) (norm_nonneg _) (Real.exp_pos _).le
  have hm1 := hmain (fun {w} => hSyb w) hς hcube hς1 hξ hL hS
  have hd_sym : ∀ v : ℝ, ς * (1 + |v|) ≤ 1 / 4 →
      ‖Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ (4 * Cq * CT) * ς ^ 2 := fun v hv => by
    set w : ℂ := (1 : ℂ) + (v : ℂ) * Complex.I
    have hwn : ‖w‖ ≤ 1 + |v| := by
      calc ‖(1 : ℂ) + (v : ℂ) * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 1 + |v| := by simp
    have hζn : ‖(ς : ℂ) * w‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hς]
      exact (mul_le_mul_of_nonneg_left hwn hς.le).trans hv
    have hqe := hQ c 0 hcc2 le_rfl zero_le_one ((ς : ℂ) * w) hζn
    have hc23 : c ^ (-(2 / 3 : ℝ)) = ς ^ 2 := by
      dsimp only [ς, liftEps]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hc23] at hqe
    have hςn2 : ς ^ 2 * ‖(ς : ℂ) * w‖ + ‖(ς : ℂ) * w‖ ^ 2 ≤ 2 * ς ^ 2 * (1 + |v|) ^ 2 := by
      have hzw : ‖(ς : ℂ) * w‖ ≤ ς * (1 + |v|) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hς]; exact mul_le_mul_of_nonneg_left hwn hς.le
      have h1v : 1 ≤ 1 + |v| := le_add_of_nonneg_right (abs_nonneg v)
      have hς01 : ς ≤ 1 := by linarith
      calc ς ^ 2 * ‖(ς : ℂ) * w‖ + ‖(ς : ℂ) * w‖ ^ 2
          ≤ ς ^ 2 * (ς * (1 + |v|)) + (ς * (1 + |v|)) ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hzw (sq_nonneg _)) (pow_le_pow_left₀ (norm_nonneg _) hzw 2)
        _ ≤ ς ^ 2 * (1 * (1 + |v|) ^ 2) + ς ^ 2 * (1 + |v|) ^ 2 := by
            have h2a : ς * (1 + |v|) ≤ 1 * (1 + |v|) ^ 2 := by nlinarith [h1v]
            rw [mul_pow]
            exact add_le_add (mul_le_mul_of_nonneg_left h2a (sq_nonneg _)) le_rfl
        _ = 2 * ς ^ 2 * (1 + |v|) ^ 2 := by ring
    have hwre : w.re = 1 := by simp [w]
    have hwim : w.im = v := by simp [w]
    have hG1w := hG1_unif w (by rw [hwre]; norm_num)
    rw [hwim] at hG1w
    have hdiff_eq : Sy w - Ey w =
        (seedQ ε 0 c ((ς : ℂ) * w) - Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))) * ctTg1 ((ceCs : ℂ) * w) := by
      dsimp only [Sy, Ey]; unfold wg1PartA seedQ
      have hsc : (seedScale c : ℂ) * ((ς : ℂ) * w) = (ceCs : ℂ) * w := by
        rw [← mul_assoc, ← Complex.ofReal_mul, seedScale_mul_liftEps hc0]
      have hζ_cl : (ς : ℂ) * w ∈ closedStrip := by
        refine ⟨?_, ?_⟩ <;> rw [re_mul_real, hwre, mul_one] <;> linarith
      have hζ_ball : (ς : ℂ) * w ∈ ball (0 : ℂ) (1 / 2) := by
        rw [mem_ball_zero_iff]; linarith
      rw [hsc, outerHbar_eq_H0 hζ_cl hζ_ball]; ring
    rw [hdiff_eq, norm_mul]
    have hsq := sq_mul_neg_rpow_le (show (1 : ℝ) ≤ 1 + |v| by linarith [abs_nonneg v])
    calc ‖seedQ ε 0 c ((ς : ℂ) * w) - Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * w))‖ * ‖ctTg1 ((ceCs : ℂ) * w)‖
        ≤ (Cq * (2 * ς ^ 2 * (1 + |v|) ^ 2)) * (2 * CT * (1 + |v|) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (hqe.trans (mul_le_mul_of_nonneg_left hςn2 hCq)) hG1w (norm_nonneg _) (by positivity)
      _ = (4 * Cq * CT) * ς ^ 2 * ((1 + |v|) ^ 2 * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ (4 * Cq * CT) * ς ^ 2 * 1 := by gcongr
      _ = (4 * Cq * CT) * ς ^ 2 := mul_one _
  have hr1 := href hς hς1 hS
    (fun v => by simpa using hSyb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp))
    (fun v => by simpa using hEyb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)) hd_sym
  have href_id := airy_reference_identity hasU2_ceG1 (continuous_ceG1 _) (le_refl (0 : ℝ)) 0 hξ
    (Real.pi ^ 2 * S - θ * ς)
  have hR_eq : (∫ v : ℝ, refKernel S ς ((v : ℂ) * Complex.I) * Ey ((v : ℂ) * Complex.I)) =
      ∫ v : ℝ, liftSymbol (ceG1 (Special.airyZero 1)) 0 0 ((v : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    dsimp only [Ey]
    rw [liftSymbol_zero_order, exp_matches]
    have hexp_m : Complex.exp (-((lam : ℝ) : ℂ) * ((ς : ℂ) * ((v : ℂ) * Complex.I))) *
        Complex.exp (Complex.I * (((Real.pi ^ 2 * S + ς / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (((Real.pi ^ 2 * S - θ * ς) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; rw [hlamθ]; push_cast; ring
    dsimp only [ctTg1]
    rw [← mul_assoc, mul_comm (Complex.exp (Complex.I * (((Real.pi ^ 2 * S + ς / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))),
      hexp_m, mul_comm]
  have hwindow0 : windowSmooth 0 0 (ceG1 (Special.airyZero 1)) = ceG1 (Special.airyZero 1) := by
    funext x; simp [windowSmooth]
  have href_val : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, refKernel S ς ((v : ℂ) * Complex.I) * Ey ((v : ℂ) * Complex.I) =
      ((ceK / ceCs * ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ) := by
    have h1 := congrArg (fun z : ℂ => (ξ : ℂ) * z) href_id
    have hξ0 : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
    have harg : -((Real.pi ^ 2 * S - θ * ς) / ceCs) = -(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς := by
      have hcm := ceCs_mul_ceBeta1
      rw [← hcm]; field_simp [ceCs_pos.ne', ceBeta1_pos.ne']; ring
    rw [hwindow0, harg] at h1
    rw [hR_eq]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ)⁻¹ = (ξ : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ := by
      push_cast; field_simp [hξ0]
    calc ((2 * Real.pi : ℝ) : ℂ)⁻¹ * _
        = (ξ : ℂ) * (((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * _) := by rw [h2pi, mul_assoc]
      _ = (ξ : ℂ) * ((ceK : ℂ) / ((ceCs : ℂ) * (ξ : ℂ)) *
            ((ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ)) := h1
      _ = _ := by push_cast; field_simp [hξ0]
  have hH_eq : ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I) := by
    rw [shA]
    set g : ℝ → ℂ := fun τ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I)
    have h1 := MeasureTheory.Measure.integral_comp_mul_left g ς
    have h2 : ∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((v : ℂ) * Complex.I)) ξ * Sy ((v : ℂ) * Complex.I) =
        ∫ v : ℝ, g (ς * v) := by
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      have hev : ((ς * v : ℝ) : ℂ) * Complex.I = (ς : ℂ) * ((v : ℂ) * Complex.I) := by push_cast; ring
      dsimp only [g, Sy]; rw [hev]
    have hinv : ς⁻¹ = c ^ (1 / 3 : ℝ) := by dsimp only [ς, liftEps]; rw [Real.rpow_neg hc0.le, inv_inv]
    rw [h2, h1, Complex.real_smul, abs_of_pos (inv_pos.mpr hς), hinv]; push_cast; ring
  have href_val' : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ v : ℝ, refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * Ey ((1 : ℂ) + (v : ℂ) * Complex.I) =
      ((ceK / ceCs * ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ) := by
    rw [hshR]; exact href_val
  have hCdiff : ‖((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I)) -
      ((ceK / ceCs * ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς) : ℝ) : ℂ)‖ ≤
      ((Cm + Cr) / (2 * Real.pi)) * ς ^ 2 := by
    rw [hH_eq, ← href_val', ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hEyc : ContinuousOn Ey {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := by
      have hct : ContinuousOn (fun w : ℂ => ctTg1 ((ceCs : ℂ) * w)) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := by
        have hlin2 : Continuous fun w : ℂ => (ceCs : ℂ) * w := by fun_prop
        have hct0 : ContinuousOn (fun w : ℂ => seedT 0 ((ceCs : ℂ) * w)) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} :=
          (seedT_continuousOn 0).comp hlin2.continuousOn fun w hw => by
            show 0 ≤ ((ceCs : ℂ) * w).re; rw [re_mul_real]; exact mul_nonneg ceCs_pos.le hw.1
        have hct1 : ContinuousOn (fun w : ℂ => seedT 1 ((ceCs : ℂ) * w)) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} :=
          (seedT_continuousOn 1).comp hlin2.continuousOn fun w hw => by
            show 0 ≤ ((ceCs : ℂ) * w).re; rw [re_mul_real]; exact mul_nonneg ceCs_pos.le hw.1
        exact (hct0.sub hct1).congr fun w hw => by
          have hre : 0 ≤ ((ceCs : ℂ) * w).re := by rw [re_mul_real]; exact mul_nonneg ceCs_pos.le hw.1
          exact ctTg1_eq_seedT_sub hre
      exact (Continuous.continuousOn (by fun_prop)).mul hct
    have hline1 : Continuous fun v : ℝ => (1 : ℂ) + (v : ℂ) * Complex.I := by fun_prop
    have hmem1 : ∀ v : ℝ, ((1 : ℂ) + (v : ℂ) * Complex.I) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := fun v => by simp
    have hi1 : Integrable (fun v : ℝ => mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I)) :=
      (integrable_weight (BK * CW)).mono' (((hKc.mul hSyc).comp_continuous hline1 hmem1).aestronglyMeasurable)
        (ae_of_all _ fun v => by simpa using hAb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp))
    have hi2 : Integrable (fun v : ℝ => refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * Sy ((1 : ℂ) + (v : ℂ) * Complex.I)) :=
      (integrable_weight (Eref * CW)).mono' (((hRdiff.continuous.continuousOn.mul hSyc).comp_continuous hline1 hmem1).aestronglyMeasurable)
        (ae_of_all _ fun v => by
          rw [norm_mul]
          simpa [mul_assoc] using mul_le_mul (hRb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp))
            (hSyb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)) (norm_nonneg _) (by positivity))
    have hi3 : Integrable (fun v : ℝ => refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * Ey ((1 : ℂ) + (v : ℂ) * Complex.I)) :=
      (integrable_weight (Eref * CE)).mono' (((hRdiff.continuous.continuousOn.mul hEyc).comp_continuous hline1 hmem1).aestronglyMeasurable)
        (ae_of_all _ fun v => by
          rw [norm_mul]
          simpa [mul_assoc] using mul_le_mul (hRb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp))
            (hEyb ((1 : ℂ) + (v : ℂ) * Complex.I) (by simp) (by simp)) (norm_nonneg _) (by positivity))
    have hsub_int : (∫ v : ℝ, mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ * Sy ((1 : ℂ) + (v : ℂ) * Complex.I)) -
        (∫ v : ℝ, refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) * Ey ((1 : ℂ) + (v : ℂ) * Complex.I)) =
        (∫ v : ℝ, (mellinK0 c ((ς : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ - refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          Sy ((1 : ℂ) + (v : ℂ) * Complex.I)) +
        ∫ v : ℝ, refKernel S ς ((1 : ℂ) + (v : ℂ) * Complex.I) *
          (Sy ((1 : ℂ) + (v : ℂ) * Complex.I) - Ey ((1 : ℂ) + (v : ℂ) * Complex.I)) := by
      rw [← integral_sub hi1 hi3,
        ← integral_add ((hi1.sub hi2).congr (Eventually.of_forall fun v => by dsimp [Pi.sub_apply]; ring))
          ((hi2.sub hi3).congr (Eventually.of_forall fun v => by dsimp [Pi.sub_apply]; ring))]
      refine integral_congr_ae (ae_of_all _ fun v => by ring)
    rw [hsub_int]
    calc (2 * Real.pi)⁻¹ * ‖_‖ ≤ (2 * Real.pi)⁻¹ * (‖_‖ + ‖_‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ (2 * Real.pi)⁻¹ * (Cm * ς ^ 2 + Cr * ς ^ 2) := by gcongr
      _ = ((Cm + Cr) / (2 * Real.pi)) * ς ^ 2 := by ring
  have hre : |normDensity (wg1PartA ε c) c ξ - ceK / ceCs * ceG1 (Special.airyZero 1)
      (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς)| ≤ ((Cm + Cr) / (2 * Real.pi)) * ς ^ 2 := by
    have heq_nd : normDensity (wg1PartA ε c) c ξ =
        (((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I)).re := by
      unfold normDensity; rw [Complex.re_ofReal_mul]
    rw [heq_nd, ← Complex.ofReal_re (ceK / ceCs * ceG1 (Special.airyZero 1) (-(ceBeta1 * S) + ceBeta1 * (θ / Real.pi ^ 2) * ς)),
      ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hCdiff
  have hc23 : ς ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    dsimp only [ς, liftEps]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  rw [← hc23]
  exact hre.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

/-- **`(fct:hg1-win)`**: fixed Airy window expansion of `normDensity (ctWg1 ε c) c ξ` on `|hbS c ξ| ≤ Sw`. -/
theorem ctWg1_win_bound (Sw : ℝ) :
    ∃ c₀ C : ℝ, 64 ≤ c₀ ∧ 0 < C ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      |normDensity (ctWg1 ε c) c ξ -
          ceK / ceCs * ceG1 (Special.airyZero 1)
            (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)| ≤
        C * c ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨c1, C1, hc1, hC1, h1⟩ := wg1PartA_win_single (Or.inl rfl) Sw
  obtain ⟨c2, C2, hc2, hC2, h2⟩ := wg1PartA_win_single (Or.inr rfl) Sw
  obtain ⟨cS, hcS, hsp⟩ := ctWg1_normDensity_split
  obtain ⟨cB, CB, hcB, hCB0, hB⟩ := ctWg1_partB_bound
  refine ⟨max (max c1 c2) (max cS cB), max C1 C2 + CB, le_max_of_le_left (le_max_of_le_left hc1),
    by positivity, fun {ε c ξ} hε hc hξ hS => ?_⟩
  rw [hsp hε ((le_max_left cS cB).trans ((le_max_right _ _).trans hc)) hξ]
  have hA_bd : |normDensity (wg1PartA ε c) c ξ - ceK / ceCs * ceG1 (Special.airyZero 1)
      (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)| ≤
      max C1 C2 * c ^ (-(2 / 3 : ℝ)) := by
    have hc0 : 0 < c := by linarith [hc1.trans ((le_max_left c1 c2).trans ((le_max_left _ _).trans hc))]
    rcases hε with rfl | rfl
    · exact (h1 ((le_max_left c1 c2).trans ((le_max_left _ _).trans hc)) hξ hS).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hc0 _).le)
    · exact (h2 ((le_max_right c1 c2).trans ((le_max_left _ _).trans hc)) hξ hS).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hc0 _).le)
  have hB_bd := (hB hε ((le_max_right cS cB).trans ((le_max_right _ _).trans hc)) hξ).1
  have htri : normDensity (wg1PartA ε c) c ξ + normDensity (wg1PartB ε c) c ξ -
      ceK / ceCs * ceG1 (Special.airyZero 1)
        (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c) =
      (normDensity (wg1PartA ε c) c ξ - ceK / ceCs * ceG1 (Special.airyZero 1)
        (-(ceBeta1 * hbS c ξ) + ceBeta1 * (deriv (outerTheta ε) 0 / Real.pi ^ 2) * liftEps c)) +
      normDensity (wg1PartB ε c) c ξ := by ring
  rw [htri]
  calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
    _ ≤ max C1 C2 * c ^ (-(2 / 3 : ℝ)) + CB * c ^ (-(2 / 3 : ℝ)) := add_le_add hA_bd hB_bd
    _ = (max C1 C2 + CB) * c ^ (-(2 / 3 : ℝ)) := by ring

/-- info: 'FormalResearch.SignUncertainty.ctWg1_win_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_win_bound

end FormalResearch.SignUncertainty