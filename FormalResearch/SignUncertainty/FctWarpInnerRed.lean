/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpInnerInts
public import FormalResearch.Special.AiryCftZeros

/-!
# `(fct:RI-bounds)` residual bounds and Airy derivative evaluation for `fct:warp-asymp` (1)

Paper I (`constant_terms_five.tex`), Proposition FCT.5 (1), Steps 2–3:
1. Evaluates `fctG0`, `deriv fctG0`, and `iteratedDeriv 2 fctG0` at `airyZero 1`, including
   `deriv fctG0 (airyZero 1) = 2 i √π`, `(iteratedDeriv 2 fctG0 (airyZero 1)).re = 4 π^{3/2} Ai'(a₁)²`,
   and Lipschitz control of `fctG0` near `airyZero 1`.
2. Combines the concrete inner pullback (`FctWarpInnerInts`) with `(fct:inner-symbols)` (`fctInnerSymbolsA`,
   `fctInnerSymbolsMonomial`, `fctInnerSymbolsG0`, `concreteInnerB3`, `concreteInnerB4`) and the outer
   shoulder IBP estimate (`fctWarpOuter_shoulder_bounds`) to establish `(fct:RI-bounds)`:
   - `fctWarpI_zero_residual`: `‖N₀ I_ε(L₁, 0) - i G₀(û)‖ ≤ C c^{-4/3}`
   - `fctWarpI_derivL_at_a1_err`: `‖(N₀ / û_L) ∂_{L₁} I_ε(L₁, α) - i G₀'(a₁)‖ ≤ C c^{-1/2}`
   - `fctWarpI_derivAlpha_at_a1_err`: `‖c^{2/3} N₀ ∂_α I_ε(L₁, α) + i c₂* G₀''(a₁)‖ ≤ C c^{-1/2}`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff
open FormalResearch.CohnElkies
open FormalResearch.Special
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-! ### 1. Exact values and Lipschitz bounds of `fctG0` near `airyZero 1` -/

lemma fctG0_airyZero : fctG0 (airyZero 1) = 0 := by
  simp [fctG0, airyAi_airyZero 1]

noncomputable def fctG0DerivFn (u : ℝ) : ℂ :=
  ((2 * π ^ (3 / 2 : ℝ) * (2 * airyAi u * airyAi' u) : ℝ) : ℂ) -
    Complex.I * ((2 * π ^ (3 / 2 : ℝ) * (airyAi' u * airyBi u + airyAi u * airyBiDeriv u) : ℝ) : ℂ)

noncomputable def fctG0Deriv2Fn (u : ℝ) : ℂ :=
  ((2 * π ^ (3 / 2 : ℝ) * (2 * (airyAi' u) ^ 2 + 2 * u * (airyAi u) ^ 2) : ℝ) : ℂ) -
    Complex.I * ((2 * π ^ (3 / 2 : ℝ) *
      (2 * u * airyAi u * airyBi u + 2 * airyAi' u * airyBiDeriv u) : ℝ) : ℂ)

lemma hasDerivAt_fctG0 (u : ℝ) : HasDerivAt fctG0 (fctG0DerivFn u) u := by
  have hAi : HasDerivAt airyAi (airyAi' u) u := hasDerivAt_airyAi u
  have hBi : HasDerivAt airyBi (airyBiDeriv u) u := hasDerivAt_airyBi u
  have h1 : HasDerivAt (fun x => 2 * π ^ (3 / 2 : ℝ) * (airyAi x) ^ 2)
      (2 * π ^ (3 / 2 : ℝ) * (2 * airyAi u * airyAi' u)) u := by
    have hp := (hAi.pow 2).const_mul (2 * π ^ (3 / 2 : ℝ))
    convert hp using 1; ring
  have h2 : HasDerivAt (fun x => 2 * π ^ (3 / 2 : ℝ) * (airyAi x * airyBi x))
      (2 * π ^ (3 / 2 : ℝ) * (airyAi' u * airyBi u + airyAi u * airyBiDeriv u)) u :=
    (hAi.mul hBi).const_mul (2 * π ^ (3 / 2 : ℝ))
  have hc := (h1.ofReal_comp).sub ((h2.ofReal_comp).const_mul Complex.I)
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · dsimp only [fctG0, Pi.sub_apply]
  · dsimp only [fctG0DerivFn]

lemma hasDerivAt_fctG0DerivFn (u : ℝ) : HasDerivAt fctG0DerivFn (fctG0Deriv2Fn u) u := by
  have hAi := hasDerivAt_airyAi u
  have hAi' := hasDerivAt_airyAi' u
  have hBi := hasDerivAt_airyBi u
  have hBi' := hasDerivAt_airyBiDeriv u
  have h1 : HasDerivAt (fun x => 2 * π ^ (3 / 2 : ℝ) * (2 * airyAi x * airyAi' x))
      (2 * π ^ (3 / 2 : ℝ) * (2 * (airyAi' u) ^ 2 + 2 * u * (airyAi u) ^ 2)) u := by
    have hp := ((hAi.const_mul 2).mul hAi').const_mul (2 * π ^ (3 / 2 : ℝ))
    convert hp using 1; simp only [mul_assoc]; ring
  have h2 : HasDerivAt (fun x => 2 * π ^ (3 / 2 : ℝ) * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x))
      (2 * π ^ (3 / 2 : ℝ) * (2 * u * airyAi u * airyBi u + 2 * airyAi' u * airyBiDeriv u)) u := by
    have hm := ((hAi'.mul hBi).add (hAi.mul hBi')).const_mul (2 * π ^ (3 / 2 : ℝ))
    convert hm using 1; ring
  have hc := (h1.ofReal_comp).sub ((h2.ofReal_comp).const_mul Complex.I)
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · dsimp only [fctG0DerivFn, Pi.sub_apply]
  · dsimp only [fctG0Deriv2Fn]

lemma airyAi'_mul_airyBi_airyZero :
    airyAi' (airyZero 1) * airyBi (airyZero 1) = -(1 / π) := by
  have hw := congrArg Complex.re (airyAiC_wronskian_airyBiC_eq (airyZero 1 : ℂ))
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal, airyBiC_ofReal, airyBiC'_ofReal, airyAi_airyZero 1] at hw
  simp only [Complex.ofReal_zero, zero_mul, zero_sub, Complex.neg_re, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hw
  linarith

lemma deriv_fctG0_airyZero :
    deriv fctG0 (airyZero 1) = Complex.I * ((2 * Real.sqrt π : ℝ) : ℂ) := by
  rw [(hasDerivAt_fctG0 (airyZero 1)).deriv]
  unfold fctG0DerivFn
  simp only [airyAi_airyZero 1, mul_zero, zero_mul, add_zero, airyAi'_mul_airyBi_airyZero]
  have hpi32 : π ^ (3 / 2 : ℝ) * (-(1 / π)) = -Real.sqrt π := by
    rw [Real.sqrt_eq_rpow]
    have h1 : π ^ (3 / 2 : ℝ) * π⁻¹ = π ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add Real.pi_pos]; norm_num
    calc π ^ (3 / 2 : ℝ) * (-(1 / π)) = -(π ^ (3 / 2 : ℝ) * π⁻¹) := by ring
      _ = -π ^ (1 / 2 : ℝ) := by rw [h1]
  have hre : (2 * π ^ (3 / 2 : ℝ) * (-(1 / π))) = -(2 * Real.sqrt π) := by
    calc 2 * π ^ (3 / 2 : ℝ) * (-(1 / π)) = 2 * (π ^ (3 / 2 : ℝ) * (-(1 / π))) := by ring
      _ = 2 * (-Real.sqrt π) := by rw [hpi32]
      _ = -(2 * Real.sqrt π) := by ring
  rw [hre]; push_cast; ring

lemma iteratedDeriv_two_fctG0_eq (u : ℝ) :
    iteratedDeriv 2 fctG0 u = fctG0Deriv2Fn u := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hf : deriv fctG0 = fctG0DerivFn := funext fun x => (hasDerivAt_fctG0 x).deriv
  rw [hf]
  exact (hasDerivAt_fctG0DerivFn u).deriv

lemma iteratedDeriv_two_fctG0_airyZero_re :
    (iteratedDeriv 2 fctG0 (airyZero 1)).re =
      4 * π ^ (3 / 2 : ℝ) * (airyAi' (airyZero 1)) ^ 2 := by
  rw [iteratedDeriv_two_fctG0_eq, fctG0Deriv2Fn, airyAi_airyZero 1]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    zero_mul, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, sub_zero]
  ring

noncomputable def fctG0Deriv3Fn (u : ℝ) : ℂ :=
  ((2 * π ^ (3 / 2 : ℝ) * (2 * (airyAi u) ^ 2 + 8 * u * airyAi u * airyAi' u) : ℝ) : ℂ) -
    Complex.I * ((2 * π ^ (3 / 2 : ℝ) *
      (2 * airyAi u * airyBi u + 4 * u * airyAi' u * airyBi u +
        4 * u * airyAi u * airyBiDeriv u) : ℝ) : ℂ)

lemma hasDerivAt_fctG0Deriv2Fn (u : ℝ) : HasDerivAt fctG0Deriv2Fn (fctG0Deriv3Fn u) u := by
  have hAi := hasDerivAt_airyAi u
  have hAi' := hasDerivAt_airyAi' u
  have hBi := hasDerivAt_airyBi u
  have hBi' := hasDerivAt_airyBiDeriv u
  have h1 : HasDerivAt (fun x => 2 * π ^ (3 / 2 : ℝ) * (2 * (airyAi' x) ^ 2 + 2 * x * (airyAi x) ^ 2))
      (2 * π ^ (3 / 2 : ℝ) * (2 * (airyAi u) ^ 2 + 8 * u * airyAi u * airyAi' u)) u := by
    have ha2 : HasDerivAt (fun x => 2 * (airyAi' x) ^ 2) (4 * u * airyAi u * airyAi' u) u := by
      convert (hAi'.pow 2).const_mul 2 using 1; ring
    have hb2 : HasDerivAt (fun x => 2 * x * (airyAi x) ^ 2)
        (2 * (airyAi u) ^ 2 + 4 * u * airyAi u * airyAi' u) u := by
      have hm := ((hasDerivAt_id u).mul (hAi.pow 2)).const_mul 2
      convert hm using 1
      · ext x; simp [mul_assoc]
      · simp; ring
    convert (ha2.add hb2).const_mul (2 * π ^ (3 / 2 : ℝ)) using 1; ring
  have h2 : HasDerivAt (fun x => 2 * π ^ (3 / 2 : ℝ) *
        (2 * x * airyAi x * airyBi x + 2 * airyAi' x * airyBiDeriv x))
      (2 * π ^ (3 / 2 : ℝ) *
        (2 * airyAi u * airyBi u + 4 * u * airyAi' u * airyBi u +
          4 * u * airyAi u * airyBiDeriv u)) u := by
    have hp1 : HasDerivAt (fun x => 2 * x * airyAi x * airyBi x)
        (2 * airyAi u * airyBi u + 2 * u * airyAi' u * airyBi u + 2 * u * airyAi u * airyBiDeriv u) u := by
      have hm := (((hasDerivAt_id u).mul hAi).mul hBi).const_mul 2
      convert hm using 1
      · ext x; simp [mul_assoc]
      · simp; ring
    have hp2 : HasDerivAt (fun x => 2 * airyAi' x * airyBiDeriv x)
        (2 * u * airyAi u * airyBiDeriv u + 2 * u * airyAi' u * airyBi u) u := by
      have hm := (hAi'.mul hBi').const_mul 2
      convert hm using 1
      · ext x; simp [mul_assoc]
      · ring
    convert (hp1.add hp2).const_mul (2 * π ^ (3 / 2 : ℝ)) using 1; ring
  have hc := (h1.ofReal_comp).sub ((h2.ofReal_comp).const_mul Complex.I)
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · dsimp only [fctG0Deriv2Fn, Pi.sub_apply]
  · dsimp only [fctG0Deriv3Fn]

lemma fctG0_lipschitz_near_airyZero :
    ∃ C_g : ℝ, 0 ≤ C_g ∧ ∀ {k : ℕ}, k ≤ 2 → ∀ û : ℝ, |û - airyZero 1| ≤ 1 →
      ‖iteratedDeriv k fctG0 û - iteratedDeriv k fctG0 (airyZero 1)‖ ≤ C_g * |û - airyZero 1| := by
  let S : Set ℝ := Icc (airyZero 1 - 1) (airyZero 1 + 1)
  have hS : IsCompact S := isCompact_Icc
  have hcont0 : ContinuousOn fctG0DerivFn S :=
    fun u _ => (hasDerivAt_fctG0DerivFn u).continuousAt.continuousWithinAt
  have hcont1 : ContinuousOn fctG0Deriv2Fn S :=
    fun u _ => (hasDerivAt_fctG0Deriv2Fn u).continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn fctG0Deriv3Fn S := by
    unfold fctG0Deriv3Fn
    have h1 : Continuous airyAi := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAi x).continuousAt
    have h2 : Continuous airyAi' := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAi' x).continuousAt
    have h3 : Continuous airyBi := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyBi x).continuousAt
    have h4 : Continuous airyBiDeriv := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyBiDeriv x).continuousAt
    exact Continuous.continuousOn (by fun_prop)
  obtain ⟨M0, hM0⟩ := hS.exists_bound_of_continuousOn hcont0
  obtain ⟨M1, hM1⟩ := hS.exists_bound_of_continuousOn hcont1
  obtain ⟨M2, hM2⟩ := hS.exists_bound_of_continuousOn hcont2
  let C_g : ℝ := max (max M0 M1) (max M2 0)
  have hCg0 : 0 ≤ C_g := le_max_of_le_right (le_max_right _ _)
  refine ⟨C_g, hCg0, fun {k} hk û hû => ?_⟩
  have hû_mem : û ∈ S := by
    have := abs_le.mp hû
    exact ⟨by linarith only [this.1], by linarith only [this.2]⟩
  have ha1_mem : airyZero 1 ∈ S := ⟨by linarith, by linarith⟩
  have hseg : ∀ (f f' : ℝ → ℂ), (∀ x, HasDerivAt f (f' x) x) →
      (∀ x ∈ S, ‖f' x‖ ≤ C_g) → ‖f û - f (airyZero 1)‖ ≤ C_g * |û - airyZero 1| := by
    intro f f' hfd hbd
    have hsub := (convex_Icc (airyZero 1 - 1) (airyZero 1 + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (fun x _ => (hfd x).hasDerivWithinAt) (fun x hx => hbd x hx) ha1_mem hû_mem
    simpa only [Real.norm_eq_abs] using hsub
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · refine hseg fctG0 fctG0DerivFn hasDerivAt_fctG0 fun x hx =>
      (hM0 x hx).trans ((le_max_left M0 M1).trans (le_max_left _ _))
  · simp only [iteratedDeriv_one]
    have hf : deriv fctG0 = fctG0DerivFn := funext fun x => (hasDerivAt_fctG0 x).deriv
    rw [hf]
    refine hseg fctG0DerivFn fctG0Deriv2Fn hasDerivAt_fctG0DerivFn fun x hx =>
      (hM1 x hx).trans ((le_max_right M0 M1).trans (le_max_left _ _))
  · simp_rw [iteratedDeriv_two_fctG0_eq]
    refine hseg fctG0Deriv2Fn fctG0Deriv3Fn hasDerivAt_fctG0Deriv2Fn fun x hx =>
      (hM2 x hx).trans ((le_max_left M2 0).trans (le_max_right _ _))

/-! ### 2. Unified `fctS` symbol-residual estimate for `(concreteInnerFamily K4 ε)` -/

lemma warpNu_sub_one_le {K4 ε c L1 α : ℝ} (_hc0 : 0 < c)
    (hV0 : |concreteInnerV K4 ε c L1 α 0 - warpTauStar| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)))
    (hsmall : pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5) :
    |warpNu K4 ε c L1 α - 1| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ∧
    |warpNu K4 ε c L1 α| ≤ 2 := by
  have hτs : (1.06 : ℝ) ≤ warpTauStar := warpTauStar_ge
  have hV0_abs := abs_le.mp (hV0.trans hsmall)
  have hV0_pos : 0 < concreteInnerV K4 ε c L1 α 0 := by linarith only [hτs, hV0_abs.1]
  have hrat_pos : 0 < concreteInnerV K4 ε c L1 α 0 / warpTauStar := div_pos hV0_pos (by linarith only [hτs])
  have hsq : Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) = warpNu K4 ε c L1 α := rfl
  have h1p : (1 : ℝ) ≤ Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) + 1 := by
    linarith only [Real.sqrt_nonneg (concreteInnerV K4 ε c L1 α 0 / warpTauStar)]
  have hne : Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) + 1 ≠ 0 := by linarith only [h1p]
  have hmul : (Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) - 1) *
      (Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) + 1) =
      concreteInnerV K4 ε c L1 α 0 / warpTauStar - 1 := by
    nlinarith [Real.mul_self_sqrt hrat_pos.le]
  have hdiff : |warpNu K4 ε c L1 α - 1| ≤ |concreteInnerV K4 ε c L1 α 0 - warpTauStar| := by
    rw [← hsq, show Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) - 1 =
      (concreteInnerV K4 ε c L1 α 0 / warpTauStar - 1) /
        (Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) + 1) from by
      rw [← hmul]; field_simp [hne]]
    rw [abs_div, abs_of_pos (show 0 < Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) + 1 by linarith only [h1p])]
    have hdiv_le : |concreteInnerV K4 ε c L1 α 0 / warpTauStar - 1| /
        (Real.sqrt (concreteInnerV K4 ε c L1 α 0 / warpTauStar) + 1) ≤
        |concreteInnerV K4 ε c L1 α 0 / warpTauStar - 1| := div_le_self (abs_nonneg _) h1p
    have hrat_sub : |concreteInnerV K4 ε c L1 α 0 / warpTauStar - 1| ≤
        |concreteInnerV K4 ε c L1 α 0 - warpTauStar| := by
      have hτne : warpTauStar ≠ 0 := by linarith only [hτs]
      rw [show concreteInnerV K4 ε c L1 α 0 / warpTauStar - 1 =
        (concreteInnerV K4 ε c L1 α 0 - warpTauStar) / warpTauStar from by
        field_simp [hτne]]
      rw [abs_div, abs_of_pos (show 0 < warpTauStar by linarith only [hτs])]
      exact div_le_self (abs_nonneg (concreteInnerV K4 ε c L1 α 0 - warpTauStar)) (by linarith only [hτs])
    exact hdiv_le.trans hrat_sub
  refine ⟨hdiff.trans hV0, ?_⟩
  have h1 := abs_le.mp (hdiff.trans hV0 |>.trans hsmall)
  rw [abs_le]; constructor <;> linarith only [h1.1, h1.2]

lemma fctS_pow_chi_mu_err {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ (C c₀ : ℝ), 0 ≤ C ∧ max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 α : ℝ} {k : ℕ}, c₀ ≤ c → k ≤ 2 → (concreteInnerFamily K4 ε).adm c L1 α →
        let S := concreteBoxS K4 ε c
        let V := concreteInnerV K4 ε c L1 α
        let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
        ‖fctS û (extUc c (fun u => (u : ℂ) ^ k * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (concreteInnerFamily K4 ε).mu c L1 α u)) -
          fctS û (fun u => (u : ℂ) ^ k)‖ ≤
          C * (c ^ (-(4 / 3 : ℝ)) + |α| * c ^ (-(2 / 3 : ℝ))) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  have hB3 := concreteInnerB3 (K4 := K4) (ε := ε) hK4
  set C3 : ℝ := |hB3.choose|
  obtain ⟨C_χ, c_χ, hB2⟩ := fctInnerB2 outerChiIn_cutoff pbKV_nonneg
  have hA12 := fctInnerSymbolsA (M := 3) (n := 8) (p := 12) (by norm_num) (by norm_num) (by norm_num)
  have hA4 := fctInnerSymbolsA (M := 3) (n := 8) (p := 4) (by norm_num) (by norm_num) (by norm_num)
  have hA2 := fctInnerSymbolsA (M := 3) (n := 8) (p := 2) (by norm_num) (by norm_num) (by norm_num)
  set C_a := max (max hA12.choose hA4.choose) hA2.choose
  have hCa0 : 0 ≤ C_a := le_max_of_le_right hA2.choose_spec.1
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ hB3.choose_spec.choose ≤ c ∧ c_χ ≤ c ∧
      pbKV * c ^ (-(1 / 2 : ℝ)) ≤ 1e-3 ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5 ∧
      c ^ (-(7 / 6 : ℝ)) ≤ 0.5 ∧
      6 ≤ fctUstar c ∧ 1 ≤ c := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop hB3.choose_spec.choose)
        (Eventually.and (eventually_ge_atTop c_χ)
          (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ (eventually_ge_atTop 1)))))))
    · have h0 : Tendsto (fun c : ℝ => pbKV * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul pbKV
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1e-3))
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually
        (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · have h0 : Tendsto fctUstar atTop atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).const_mul_atTop (by norm_num : (0 : ℝ) < 2.7)
      exact h0.eventually (eventually_ge_atTop 6)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  -- Bound on constants:
  let B_gk : ℝ := 2 ^ (8 : ℕ)
  let B_1 : ℝ := 2 ^ 8 * B_gk * (2 ^ 8 * (|C_χ| + 1) * |hB3.choose|)
  let B_2 : ℝ := 2 ^ 8 * B_gk * (2 ^ 8 * (|C_χ| + 1) * (9 * 2 ^ 8))
  let B_3 : ℝ := 2 ^ 8 * B_gk * max (|C_χ| + 1) 1
  let C_tot : ℝ := C_a * (B_1 + B_2 + B_3)
  refine ⟨C_tot, max cbase c₀, by positivity, le_max_left _ _, fun {c L1 α k} hc hk hadm => ?_⟩
  obtain ⟨hcbase, hc3, hcχ, hKV, hV0_small, hc76, hUstar6, hc1⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hc0 : 0 < c := hfacts.1
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  have hDi := uniqueDiffOn_Ici (0 : ℝ)
  have hVjets := hfacts.2.2.2.2.2.2.2.2.2.1.1
  have hb2 := hB2 c hcχ _ hVjets
  have hb3 := hB3.choose_spec.choose_spec c hc3 L1 α hadm
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 α
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α)
  have hCχ_nn : 0 ≤ |C_χ| + 1 := by positivity
  have hb2_chi : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (|C_χ| + 1)
      (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ)) :=
    (hb2.2.2.1).mono_B Icc_subset_Ici_self (by linarith [le_abs_self C_χ])
  have hb2_1m : FctSymClsOn (Icc 0 (fctUc c)) 8 0 (|C_χ| + 1)
      (fun u => ((1 - fctInnerChi outerChiIn c V u : ℝ) : ℂ)) :=
    (hb2.2.2.2.1).mono_B Icc_subset_Ici_self (by linarith [le_abs_self C_χ])
  have hû3 : |û| ≤ 3 := by
    have ha1 := airyZero_one
    have hu1 : |û - airyZero 1| ≤ c ^ (-(7 / 6 : ℝ)) := hadm.2.2.1
    have hsub := abs_le.mp (hu1.trans hc76)
    rw [abs_le]; constructor <;> linarith only [ha1.1, ha1.2, hsub.1, hsub.2]
  -- SymCls for `(u : ℂ) ^ k` (`k ≤ 2`)
  have hgk_sym : FctSymCls 8 2 B_gk (fun u : ℝ => (u : ℂ) ^ k) := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · simpa only [pow_zero] using
        ((one_symCls 8).mono_p Subset.rfl (by positivity) (by norm_num : (0 : ℝ) ≤ 2)).mono_B Subset.rfl
          (by norm_num : (1 : ℝ) ≤ 2 ^ (8 : ℕ))
    · simpa only [pow_one] using
        ((id_symCls 8).mono_p Subset.rfl (by positivity) (by norm_num : (1 : ℝ) ≤ 2)).mono_B Subset.rfl
          (by norm_num : (1 : ℝ) ≤ 2 ^ (8 : ℕ))
    · exact sq_symCls 8
  have hgk_on : FctSymClsOn (Icc 0 (fctUc c)) 8 2 B_gk (fun u : ℝ => (u : ℂ) ^ k) :=
    hgk_sym.mono_set Icc_subset_Ici_self hDu hDi
  -- Term 1: `χ * (μ - 1 - c^{-2/3} α c₂ u²)`
  let δμ : ℝ → ℂ := fun u => (concreteInnerFamily K4 ε).mu c L1 α u - 1 -
    ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)
  have hδμ_B : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (|hB3.choose| * c ^ (-(4 / 3 : ℝ))) δμ :=
    hb3.mono_B Icc_subset_Ici_self (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hc0.le _))
  have hT1_sym : FctSymCls 8 12 (B_1 * c ^ (-(4 / 3 : ℝ)))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * ((u : ℂ) ^ k * δμ u))) := by
    have hprod := (hb2_chi.mul Icc_subset_Ici_self hDu (hgk_on.mul Icc_subset_Ici_self hDu hδμ_B)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + (2 + 10) ≤ 12)
    have h1 := extUc_mem_symCls hc1 (by positivity) hprod (fun u hu => by rw [hb2.1 u hu]; simp)
    exact h1.mono_B Subset.rfl (le_of_eq (by dsimp only [B_1]; ring))
  -- Term 2: `χ * (c^{-2/3} α c₂ u²)`
  have hc2_bd : |(concreteInnerFamily K4 ε).c2 c L1 α| ≤ 9 := by
    dsimp only [concreteInnerFamily]
    have hV0_abs := abs_le.mp (hfacts.2.2.2.2.2.2.2.2.2.2.2.trans hV0_small)
    have hτs_lt : (12 / π ^ 2) ^ (1 / 3 : ℝ) < 2 := by
      have hpi2 : (9 : ℝ) < π ^ 2 := by nlinarith only [Real.pi_gt_three]
      have h12 : (12 : ℝ) / π ^ 2 < 8 := by rw [div_lt_iff₀ (by positivity)]; linarith
      calc (12 / π ^ 2) ^ (1 / 3 : ℝ) < (8 : ℝ) ^ (1 / 3 : ℝ) :=
            Real.rpow_lt_rpow (by positivity) h12 (by norm_num)
        _ = 2 := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) from by norm_num, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num)]; norm_num
    have hV0_2 : |V 0| ≤ 3 := by
      have hτs0 : 0 ≤ (12 / π ^ 2) ^ (1 / 3 : ℝ) := by positivity
      rw [abs_le]; constructor <;> linarith only [hV0_abs.1, hV0_abs.2, hτs_lt, hτs0]
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hV0_eq : (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), 0) = V 0 :=
      (hfacts.2.2.2.2.2.2.2.2.2.1.2 0 ⟨le_rfl, by norm_num⟩).symm
    change |((2 : ℝ) ^ (-(4 / 3 : ℝ))) * ((concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), 0)) ^ 2| ≤ 9
    rw [hV0_eq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _), abs_sq, ← sq_abs (V 0)]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |V 0| ^ 2 ≤ 1 * 3 ^ 2 := by
          gcongr
      _ = 9 := by norm_num
  let c2fac : ℝ := c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α
  have hc2fac_bd : |c2fac| ≤ 9 * (|α| * c ^ (-(2 / 3 : ℝ))) := by
    dsimp only [c2fac]
    rw [abs_mul, abs_mul]
    calc |c ^ (-(2 / 3 : ℝ))| * |α| * |(concreteInnerFamily K4 ε).c2 c L1 α|
        = c ^ (-(2 / 3 : ℝ)) * |α| * |(concreteInnerFamily K4 ε).c2 c L1 α| := by
          rw [abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
      _ ≤ c ^ (-(2 / 3 : ℝ)) * |α| * 9 := by gcongr
      _ = 9 * (|α| * c ^ (-(2 / 3 : ℝ))) := by ring
  have hq_on : FctSymClsOn (Icc 0 (fctUc c)) 8 2 (9 * 2 ^ 8 * (|α| * c ^ (-(2 / 3 : ℝ))))
      (fun u => ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)) := by
    have heq : (fun u : ℝ => ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)) =
        fun u : ℝ => ((c2fac : ℝ) : ℂ) * (u : ℂ) ^ 2 := by ext u; dsimp only [c2fac]; push_cast; ring
    rw [heq]
    have hsm := ((sq_symCls 8).mono_set Icc_subset_Ici_self hDu hDi).const_mul hDu ((c2fac : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hsm
    exact hsm.mono_B Icc_subset_Ici_self (by
      calc |c2fac| * 2 ^ 8 ≤ (9 * (|α| * c ^ (-(2 / 3 : ℝ)))) * 2 ^ 8 := by gcongr
        _ = 9 * 2 ^ 8 * (|α| * c ^ (-(2 / 3 : ℝ))) := by ring)
  have hT2_sym : FctSymCls 8 4 (B_2 * (|α| * c ^ (-(2 / 3 : ℝ))))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)))) := by
    have hprod := (hb2_chi.mul Icc_subset_Ici_self hDu (hgk_on.mul Icc_subset_Ici_self hDu hq_on)).mono_p
      Icc_subset_Ici_self (by positivity) (by norm_num : (0 : ℝ) + (2 + 2) ≤ 4)
    have h1 := extUc_mem_symCls hc1 (by positivity) hprod (fun u hu => by rw [hb2.1 u hu]; simp)
    exact h1.mono_B Subset.rfl (le_of_eq (by dsimp only [B_2]; ring))
  -- Term 3: `(u : ℂ) ^ k * (1 - chiExt c V u)`
  have h1m_sym := one_sub_chiExt_symCls (V := V) hc1 hCχ_nn hb2_1m hb2.1
  have hT3_sym : FctSymCls 8 2 B_3 (fun u : ℝ => (u : ℂ) ^ k * (1 - chiExt c V u)) := by
    have hprod := (hgk_sym.mul Subset.rfl hDi h1m_sym).mono_p Subset.rfl (by positivity) (by norm_num : (2 : ℝ) + 0 ≤ 2)
    exact hprod.mono_B Subset.rfl (le_of_eq (by dsimp only [B_3]))
  -- Apply `fctInnerSymbolsA` to `hT1_sym`, `hT2_sym`, `hT3_sym`
  obtain ⟨hA12_nn, hA12_spec⟩ := hA12.choose_spec
  obtain ⟨hA4_nn, hA4_spec⟩ := hA4.choose_spec
  obtain ⟨hA2_nn, hA2_spec⟩ := hA2.choose_spec
  obtain ⟨⟨L1_s, hL1_s⟩, hbd1, _⟩ := hA12_spec û (B_1 * c ^ (-(4 / 3 : ℝ))) _ hû3 (by positivity) hT1_sym
  obtain ⟨⟨L2_s, hL2_s⟩, hbd2, _⟩ := hA4_spec û (B_2 * (|α| * c ^ (-(2 / 3 : ℝ)))) _ hû3 (by positivity) hT2_sym
  obtain ⟨⟨L3_s, hL3_s⟩, _, htail3⟩ := hA2_spec û B_3 _ hû3 (by positivity) hT3_sym
  have hzero3 : ∀ u ∈ Icc (0 : ℝ) (fctUstar c), (u : ℂ) ^ k * (1 - chiExt c V u) = 0 := by
    intro u hu
    have huc : fctUstar c ≤ fctUc c := by
      dsimp only [fctUstar, fctUc]; linarith only [Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 12)]
    have hcu : u ≤ fctUc c := hu.2.trans huc
    simp only [chiExt, extUc, hcu, ↓reduceIte]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, hb2.2.2.2.2 u hu, Complex.ofReal_zero, mul_zero]
  have hsqrt24 : Real.sqrt (8 * 3) ≤ 6 := by rw [Real.sqrt_le_iff]; norm_num
  have hbd3_tail := htail3 (fctUstar c) (max_le hUstar6 (hsqrt24.trans hUstar6)) hzero3
  have htail_le : fctUstar c ^ ((2 : ℝ) + 1 / 2 - 3 * (8 : ℕ)) ≤ c ^ (-(4 / 3 : ℝ)) := by
    have hexp_eq : (2 : ℝ) + 1 / 2 - 3 * ((8 : ℕ) : ℝ) = -(43 / 2 : ℝ) := by norm_num
    rw [hexp_eq]
    have h1u : c ^ ((1 : ℝ) / 12) ≤ fctUstar c := by
      dsimp only [fctUstar]; linarith only [Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 12)]
    have hc12_pos : 0 < c ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hc0 _
    calc (fctUstar c) ^ (-(43 / 2 : ℝ))
        ≤ (c ^ ((1 : ℝ) / 12)) ^ (-(43 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hc12_pos h1u (by norm_num)
      _ = c ^ (-(43 / 24 : ℝ)) := by rw [← Real.rpow_mul hc0.le]; norm_num
      _ ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hbd3 : ‖fctS û (fun u => (u : ℂ) ^ k * (1 - chiExt c V u))‖ ≤ C_a * B_3 * c ^ (-(4 / 3 : ℝ)) := by
    calc ‖fctS û (fun u => (u : ℂ) ^ k * (1 - chiExt c V u))‖
        ≤ hA2.choose * B_3 * fctUstar c ^ ((2 : ℝ) + 1 / 2 - 3 * (8 : ℕ)) := hbd3_tail
      _ ≤ C_a * B_3 * c ^ (-(4 / 3 : ℝ)) := by
          have hC2_le : hA2.choose ≤ C_a := le_max_right _ _
          gcongr
  -- Monomial limit for `(u : ℂ) ^ k`
  have hmono_lim := fctInnerSymbolsMonomial k û
  rw [← hmono_lim.fctS_eq] at hmono_lim
  -- Combine via `fctSLimit` algebra
  have h1s : FctSLimit û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * ((u : ℂ) ^ k * δμ u)))
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * ((u : ℂ) ^ k * δμ u)))) := by
    rw [hL1_s.fctS_eq]; exact hL1_s
  have h2s : FctSLimit û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
      ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ))))
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
      ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ))))) := by
    rw [hL2_s.fctS_eq]; exact hL2_s
  have h3s : FctSLimit û (fun u => (u : ℂ) ^ k * (1 - chiExt c V u))
      (fctS û (fun u => (u : ℂ) ^ k * (1 - chiExt c V u))) := by
    rw [hL3_s.fctS_eq]; exact hL3_s
  have hgk_12 : FctSymCls 8 12 B_gk (fun u : ℝ => (u : ℂ) ^ k) :=
    hgk_sym.mono_p Subset.rfl (by positivity) (by norm_num : (2 : ℝ) ≤ 12)
  have hT2_12 : FctSymCls 8 12 (B_2 * (|α| * c ^ (-(2 / 3 : ℝ))))
      (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)))) :=
    hT2_sym.mono_p Subset.rfl (by positivity) (by norm_num : (4 : ℝ) ≤ 12)
  have hT3_12 : FctSymCls 8 12 B_3 (fun u : ℝ => (u : ℂ) ^ k * (1 - chiExt c V u)) :=
    hT3_sym.mono_p Subset.rfl (by positivity) (by norm_num : (2 : ℝ) ≤ 12)
  have hs01 := fctSLimit_add (by positivity) (by positivity) hgk_12 hT1_sym hmono_lim h1s
  have hsym01 := hgk_12.add hDi hT1_sym
  have hs012 := fctSLimit_add (by positivity) (by positivity) hsym01 hT2_12 hs01 h2s
  have hsym012 := hsym01.add hDi hT2_12
  have hs_all := fctSLimit_sub (by positivity) (by positivity) hsym012 hT3_12 hs012 h3s
  have hfn_eq : (fun u : ℝ => (u : ℂ) ^ k +
      extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * ((u : ℂ) ^ k * δμ u)) u +
      extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ))) u -
      (u : ℂ) ^ k * (1 - chiExt c V u)) =
      extUc c (fun u => (u : ℂ) ^ k * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u) := by
    ext u
    rcases le_or_gt u (fctUc c) with hle | hgt
    · simp only [chiExt, extUc, hle, ↓reduceIte, δμ]; ring
    · simp only [chiExt, extUc_zero_of_gt _ hgt, sub_zero, mul_one, add_zero, sub_self]
  rw [hfn_eq] at hs_all
  have hdiff : fctS û (extUc c (fun u => (u : ℂ) ^ k * ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 α u)) - fctS û (fun u => (u : ℂ) ^ k) =
      fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * ((u : ℂ) ^ k * δμ u))) +
      fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)))) -
      fctS û (fun u => (u : ℂ) ^ k * (1 - chiExt c V u)) := by
    rw [hs_all.fctS_eq]; ring
  dsimp only
  rw [hdiff]
  have hbd1' : ‖fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) * ((u : ℂ) ^ k * δμ u)))‖ ≤
      C_a * B_1 * c ^ (-(4 / 3 : ℝ)) := by
    calc _ ≤ hA12.choose * (B_1 * c ^ (-(4 / 3 : ℝ))) := hbd1
      _ ≤ C_a * (B_1 * c ^ (-(4 / 3 : ℝ))) := by gcongr; exact (le_max_left _ _).trans (le_max_left _ _)
      _ = C_a * B_1 * c ^ (-(4 / 3 : ℝ)) := by ring
  have hbd2' : ‖fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
      ((u : ℂ) ^ k * ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ))))‖ ≤
      C_a * B_2 * (|α| * c ^ (-(2 / 3 : ℝ))) := by
    calc _ ≤ hA4.choose * (B_2 * (|α| * c ^ (-(2 / 3 : ℝ)))) := hbd2
      _ ≤ C_a * (B_2 * (|α| * c ^ (-(2 / 3 : ℝ)))) := by gcongr; exact (le_max_right _ _).trans (le_max_left _ _)
      _ = C_a * B_2 * (|α| * c ^ (-(2 / 3 : ℝ))) := by ring
  calc ‖_ + _ - _‖ ≤ ‖_‖ + ‖_‖ + ‖_‖ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C_a * B_1 * c ^ (-(4 / 3 : ℝ)) + C_a * B_2 * (|α| * c ^ (-(2 / 3 : ℝ))) + C_a * B_3 * c ^ (-(4 / 3 : ℝ)) :=
        add_le_add (add_le_add hbd1' hbd2') hbd3
    _ ≤ C_a * (B_1 + B_2 + B_3) * (c ^ (-(4 / 3 : ℝ)) + |α| * c ^ (-(2 / 3 : ℝ))) := by
        have h1 : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
        have h2 : 0 ≤ |α| * c ^ (-(2 / 3 : ℝ)) := mul_nonneg (abs_nonneg α) (Real.rpow_nonneg hc0.le _)
        have hCa1 : 0 ≤ C_a * B_1 := by positivity
        have hCa2 : 0 ≤ C_a * B_2 := by positivity
        have hCa3 : 0 ≤ C_a * B_3 := by positivity
        nlinarith only [h1, h2, hCa1, hCa2, hCa3]

/-! ### 3. Full-axis residual bounds `(fct:RI-bounds)` -/

lemma fctWarpI_zero_residual {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ (C_R c₀ : ℝ), 0 ≤ C_R ∧ max 100 ((30 * pbC0 + 1) ^ 2) ≤ c₀ ∧
      ∀ {c L1 : ℝ}, c₀ ≤ c → (concreteInnerFamily K4 ε).adm c L1 0 →
        let S := concreteBoxS K4 ε c
        let û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, 0)
        ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û‖ ≤
          C_R * c ^ (-(4 / 3 : ℝ)) := by
  let cbase : ℝ := max 100 ((30 * pbC0 + 1) ^ 2)
  obtain ⟨c_in, hc_in_base, hin_eq⟩ := fctInner_warpI_in_eq (K4 := K4) (ε := ε) hK4
  obtain ⟨C_sym, c_sym, hCsym0, hc_sym_base, hsym_err⟩ := fctS_pow_chi_mu_err (K4 := K4) (ε := ε) hK4
  obtain ⟨C_sh, c_sh, hCsh0, hc_sh16, hsh⟩ := fctWarpOuter_shoulder_bounds
  obtain ⟨C_g, hCg0, hg_lip⟩ := fctG0_lipschitz_near_airyZero
  set C_N0 : ℝ := 12 * (2 : ℝ) ^ (1 / 3 : ℝ) / (π ^ 2 * Real.sqrt 1.06)
  have hCN0 : 0 ≤ C_N0 := by positivity
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ c_in ≤ c ∧ c_sym ≤ c ∧ c_sh ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5 ∧
      c ^ (-(7 / 6 : ℝ)) ≤ 1 ∧
      c ^ (-(1 / 3 : ℝ)) ≤ 1 ∧
      c ^ (-(19 / 8 : ℝ)) ≤ 1 := by
    refine Eventually.and (eventually_ge_atTop cbase)
      (Eventually.and (eventually_ge_atTop c_in)
        (Eventually.and (eventually_ge_atTop c_sym)
          (Eventually.and (eventually_ge_atTop c_sh)
            (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_ ?_)))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1)
    · have h0 : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (pbcV * pbC0)
      exact h0.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 6)).eventually (Iic_mem_nhds zero_lt_one)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually (Iic_mem_nhds zero_lt_one)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19 / 8)).eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨2 * C_sym + pbcV * pbC0 * C_g + C_N0 * C_sh, max cbase c₀,
    by have := pbcV_nonneg; have := pbC0_nonneg; positivity, le_max_left _ _,
    fun {c L1} hc hadm => ?_⟩
  obtain ⟨hcbase, hcin, hcsym, hcsh, hτD, hV0_small, hc76, hc13, hc198⟩ := hc₀ c ((le_max_right cbase c₀).trans hc)
  have hfacts := concrete_adm_facts hcbase hadm
  have hvalid := hadm.1
  have hε := hvalid.2.1
  have hc0 := hfacts.1
  have hc1 : 1 ≤ c := by linarith only [hfacts.2.1]
  have hK4t : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 := hvalid.2.2.2.2
  have hell : concreteEll1 ε c L1 ∈ Ioo (0 : ℝ) 2.55 := hfacts.2.2.2.2.1
  have hsh_bds := hsh (α := (0 : ℝ)) hK4 hε hcsh hτD hK4t hell (by rw [abs_zero]; positivity)
  have hint_full := integrableOn_fctWarpIntegrand hK4 hε hc1 hτD L1 0
  have hint_out := hsh_bds.1
  have hint_in : IntegrableOn (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ) (Ioi 0) := by
    have heq : (fun τ : ℝ => ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ) =
        fun τ => fctWarpIntegrand K4 ε c L1 0 τ - ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ := by
      ext τ; push_cast; ring
    rw [heq]; exact hint_full.sub hint_out
  have hsplit : fctWarpI K4 ε c L1 0 =
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((1 - outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ) +
      (Complex.I * ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ) := by
    unfold fctWarpI
    rw [← mul_add, ← MeasureTheory.integral_add hint_in hint_out]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    push_cast; ring
  set S := concreteBoxS K4 ε c
  set V := concreteInnerV K4 ε c L1 0
  set û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, 0)
  have hin := hin_eq hcin hadm
  dsimp only at hin
  have hsub_eq : ((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c L1 0 - Complex.I * fctG0 û =
      Complex.I * ((warpNu K4 ε c L1 0 : ℝ) : ℂ) *
        (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
            (concreteInnerFamily K4 ε).mu c L1 0 u)) - fctG0 û) +
      Complex.I * ((warpNu K4 ε c L1 0 - 1 : ℝ) : ℂ) * fctG0 û +
      ((warpN0 c : ℝ) : ℂ) * Complex.I *
        ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ := by
    rw [hsplit, mul_add, ← mul_assoc ((warpN0 c : ℝ) : ℂ) Complex.I _, hin]
    push_cast; ring
  have hnu := warpNu_sub_one_le (K4 := K4) (ε := ε) (L1 := L1) (α := 0) hc0 hfacts.2.2.2.2.2.2.2.2.2.2.2 hV0_small
  have hsym := hsym_err (k := 0) hcsym (by norm_num) hadm
  dsimp only at hsym
  simp only [pow_zero, one_mul, abs_zero, zero_mul, add_zero] at hsym
  rw [(fctInnerSymbolsG0 û).fctS_eq] at hsym
  have hg_û : ‖fctG0 û‖ ≤ C_g * c ^ (-(7 / 6 : ℝ)) := by
    have h1 := hg_lip (k := 0) (by norm_num) û (hadm.2.2.1.trans hc76)
    simp only [iteratedDeriv_zero, fctG0_airyZero, sub_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hadm.2.2.1 hCg0)
  have hN0_bd : |warpN0 c| ≤ C_N0 * c ^ (1 / 6 : ℝ) := by
    unfold warpN0
    have hws : Real.sqrt 1.06 ≤ Real.sqrt warpTauStar := Real.sqrt_le_sqrt warpTauStar_ge
    have hc16_pos : 0 ≤ c ^ (1 / 6 : ℝ) := Real.rpow_nonneg hc0.le _
    rw [abs_of_nonneg (by positivity)]
    calc 12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt warpTauStar)
        ≤ 12 * (2 : ℝ) ^ (1 / 3 : ℝ) * c ^ (1 / 6 : ℝ) / (π ^ 2 * Real.sqrt 1.06) := by gcongr
      _ = C_N0 * c ^ (1 / 6 : ℝ) := by dsimp only [C_N0]; ring
  have hsh_prod : ‖((warpN0 c : ℝ) : ℂ) * Complex.I *
      ∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ‖ ≤
      C_N0 * C_sh * c ^ (-(4 / 3 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have hpow : c ^ (1 / 6 : ℝ) * c ^ (-(31 / 8 : ℝ)) = c ^ (-(4 / 3 : ℝ)) * c ^ (-(19 / 8 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    calc |warpN0 c| * ‖∫ τ in Ioi (0 : ℝ), ((outerChiOut c τ : ℝ) : ℂ) * fctWarpIntegrand K4 ε c L1 0 τ‖
        ≤ (C_N0 * c ^ (1 / 6 : ℝ)) * (C_sh * c ^ (-(31 / 8 : ℝ))) :=
          mul_le_mul hN0_bd hsh_bds.2.2.2.1 (norm_nonneg _) (by positivity)
      _ = C_N0 * C_sh * (c ^ (1 / 6 : ℝ) * c ^ (-(31 / 8 : ℝ))) := by ring
      _ = C_N0 * C_sh * (c ^ (-(4 / 3 : ℝ)) * c ^ (-(19 / 8 : ℝ))) := by rw [hpow]
      _ ≤ C_N0 * C_sh * (c ^ (-(4 / 3 : ℝ)) * 1) := by gcongr
      _ = C_N0 * C_sh * c ^ (-(4 / 3 : ℝ)) := by ring
  have hnu_prod : ‖Complex.I * ((warpNu K4 ε c L1 0 - 1 : ℝ) : ℂ) * fctG0 û‖ ≤
      pbcV * pbC0 * C_g * c ^ (-(4 / 3 : ℝ)) := by
    have hpp : 0 ≤ pbcV * pbC0 * C_g := mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) hCg0
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpow : c ^ (-(1 / 2 : ℝ)) * c ^ (-(7 / 6 : ℝ)) = c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    calc |warpNu K4 ε c L1 0 - 1| * ‖fctG0 û‖
        ≤ (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) * (C_g * c ^ (-(7 / 6 : ℝ))) :=
          mul_le_mul hnu.1 hg_û (norm_nonneg _) (mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) (by positivity))
      _ = pbcV * pbC0 * C_g * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(7 / 6 : ℝ))) := by ring
      _ = pbcV * pbC0 * C_g * (c ^ (-(4 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := by rw [hpow]
      _ ≤ pbcV * pbC0 * C_g * (c ^ (-(4 / 3 : ℝ)) * 1) := by gcongr
      _ = pbcV * pbC0 * C_g * c ^ (-(4 / 3 : ℝ)) := by ring
  have h1_prod : ‖Complex.I * ((warpNu K4 ε c L1 0 : ℝ) : ℂ) *
      (fctS û (extUc c (fun u => ((fctInnerChi outerChiIn c V u : ℝ) : ℂ) *
        (concreteInnerFamily K4 ε).mu c L1 0 u)) - fctG0 û)‖ ≤
      2 * C_sym * c ^ (-(4 / 3 : ℝ)) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |warpNu K4 ε c L1 0| * ‖_‖ ≤ 2 * (C_sym * c ^ (-(4 / 3 : ℝ))) :=
          mul_le_mul hnu.2 hsym (norm_nonneg _) (by norm_num)
      _ = 2 * C_sym * c ^ (-(4 / 3 : ℝ)) := by ring
  dsimp only
  rw [hsub_eq]
  calc ‖_ + _ + _‖ ≤ ‖_‖ + ‖_‖ + ‖_‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * C_sym * c ^ (-(4 / 3 : ℝ)) + pbcV * pbC0 * C_g * c ^ (-(4 / 3 : ℝ)) + C_N0 * C_sh * c ^ (-(4 / 3 : ℝ)) :=
        add_le_add (add_le_add h1_prod hnu_prod) hsh_prod
    _ = (2 * C_sym + pbcV * pbC0 * C_g + C_N0 * C_sh) * c ^ (-(4 / 3 : ℝ)) := by ring

/-- info: 'FormalResearch.SignUncertainty.fctWarpI_zero_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpI_zero_residual

end FormalResearch.SignUncertainty
