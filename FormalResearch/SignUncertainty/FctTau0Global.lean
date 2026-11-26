/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTau0Symbol
public import FormalResearch.SignUncertainty.CtMDeriv
public import FormalResearch.SignUncertainty.CtBoasBlocks
public import FormalResearch.SignUncertainty.FctSymInv
public import FormalResearch.SignUncertainty.FctSymScale

/-!
# `τ₀` on all of `(0, ∞)`: smoothness, derivative, and the logarithmic derivative `τ₀'/τ₀` (`fct:bump-sym-check`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`): `τ₀(L̃) ≍ L^{1/2}` for `L ≤ 1`,
`τ₀(L̃) ≍ e^L` for `L ≥ 1`, `∂_L = m'(t)^{-1} ∂_t`.

`τ₀ = m^{-1}` (`m = uctM`, `m'(t) = 1/t - π/sinh(πt)`, `mPrime`), proved here to be `C^∞` on `(0, ∞)` with
`τ₀' = 1/m'(τ₀)` (inverse function theorem).  The two-sided size bounds of `τ₀` used by the symbol calculus are proved:

* `tau0_sq_le`, `tau0_sq_ge`: `c x ≤ τ₀(x)² ≤ C x` for `0 < x ≤ 1`;
* `tau0_ge_exp`: `τ₀(x) ≥ (2/π)(e^x - 1)` (from `x coth x ≤ 1 + x`), the `τ₀ ≍ e^L` growth.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real Nat

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD FormalResearch.CohnElkies
  FormalResearch.SignUncertainty.CtOuter

lemma uctMderiv_eq_mPrime {t : ℝ} (ht : 0 < t) : uctMderiv t = mPrime t := by
  unfold uctMderiv uctEllDeriv mPrime
  have h : 2 * (π * t / 2) = π * t := by ring
  rw [h]
  have := Real.pi_pos
  field_simp

lemma mPrime_pos {t : ℝ} (ht : 0 < t) : 0 < mPrime t := by
  rw [← uctMderiv_eq_mPrime ht]; exact uctMderiv_pos ht

lemma contDiffOn_uctM : ContDiffOn ℝ ∞ uctM (Ioi 0) := CtMDeriv.contDiffOn_hankelEdgeM

lemma hasDerivAt_uctM' {t : ℝ} (ht : 0 < t) : HasDerivAt uctM (mPrime t) t := by
  have := hasDerivAt_uctM ht
  rwa [uctMderiv_eq_mPrime ht] at this

/-- `τ₀` is `C^∞` on `(0, ∞)` (inverse function theorem for `m = uctM`, `m' > 0`). -/
theorem contDiffOn_tau0 : ContDiffOn ℝ ∞ tau0 (Ioi 0) := by
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  have hx₀' : 0 < x₀ := hx₀
  set t₀ := tau0 x₀ with ht₀
  have ht₀p : 0 < t₀ := tau0_pos hx₀'
  have hI : Ioi (0 : ℝ) ∈ 𝓝 t₀ := Ioi_mem_nhds ht₀p
  have hφ0 : ContDiffAt ℝ ∞ uctM t₀ := contDiffOn_uctM.contDiffAt hI
  have hd0 := hasDerivAt_uctM' ht₀p
  have hne : mPrime t₀ ≠ 0 := (mPrime_pos ht₀p).ne'
  have hf' := hd0.hasFDerivAt_equiv hne
  set Ψ := hφ0.toOpenPartialHomeomorph uctM hf' (by simp) with hΨ
  have hsrc : t₀ ∈ Ψ.source := hφ0.mem_toOpenPartialHomeomorph_source hf' (by simp)
  have hcoe : (Ψ : ℝ → ℝ) = uctM := rfl
  have hfx : uctM t₀ = x₀ := ceEll_tau0 hx₀'
  have hxt : x₀ ∈ Ψ.target := by
    have := hφ0.image_mem_toOpenPartialHomeomorph_target hf' (by simp)
    rwa [hfx] at this
  have hsymm : Ψ.symm x₀ = t₀ := by
    have := Ψ.left_inv hsrc
    rwa [hcoe, hfx] at this
  have hsd : ContDiffAt ℝ ∞ Ψ.symm x₀ := by
    refine Ψ.contDiffAt_symm_deriv (n := ∞) (f₀' := mPrime t₀) hne hxt (by rwa [hsymm]) (by rwa [hsymm])
  have hev : tau0 =ᶠ[𝓝 x₀] Ψ.symm := by
    have h1 : ∀ᶠ y in 𝓝 x₀, y ∈ Ψ.target := Ψ.open_target.mem_nhds hxt
    have h2 : ∀ᶠ y in 𝓝 x₀, Ψ.symm y ∈ Ioi (0 : ℝ) := by
      have hc : ContinuousAt Ψ.symm x₀ := hsd.continuousAt
      exact hc.eventually (by rw [hsymm]; exact hI)
    have h3 : ∀ᶠ y in 𝓝 x₀, y ∈ Ioi (0 : ℝ) := Ioi_mem_nhds hx₀'
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    have e1 : uctM (Ψ.symm y) = y := by
      have := Ψ.right_inv hy1
      rwa [hcoe] at this
    have e2 : uctM (tau0 y) = y := ceEll_tau0 hy3
    exact uctM_strictMonoOn.injOn (tau0_pos hy3) hy2 (e2.trans e1.symm)
  exact hsd.congr_of_eventuallyEq hev

lemma hasDerivAt_tau0 {x : ℝ} (hx : 0 < x) : HasDerivAt tau0 (mPrime (tau0 x))⁻¹ x := by
  have hc : ContinuousAt tau0 x := (contDiffOn_tau0.continuousOn).continuousAt (Ioi_mem_nhds hx)
  refine HasDerivAt.of_local_left_inverse hc (hasDerivAt_uctM' (tau0_pos hx)) (mPrime_pos (tau0_pos hx)).ne' ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy using ceEll_tau0 (show 0 < y from hy)

lemma deriv_tau0 {x : ℝ} (hx : 0 < x) : deriv tau0 x = (mPrime (tau0 x))⁻¹ := (hasDerivAt_tau0 hx).deriv


/-! ### Lower bound for `θ(t) = t m'(t) = 1 - πt/sinh(πt)` -/

lemma sinh_ge_cubic {y : ℝ} (hy : 0 ≤ y) : y + y ^ 3 / 6 ≤ Real.sinh y := by
  have h := Real.hasSum_sinh y
  have hnn : ∀ n ∉ Finset.range 2, 0 ≤ y ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) := fun n _ => by positivity
  have := sum_le_hasSum (Finset.range 2) hnn h
  simp [Finset.sum_range_succ, Nat.factorial] at this
  linarith

lemma theta_eq {t : ℝ} (ht : 0 < t) : t * mPrime t = 1 - π * t / Real.sinh (π * t) := by
  unfold mPrime
  field_simp

lemma theta_ge {t : ℝ} (ht : 0 < t) : (π * t) ^ 2 / (6 + (π * t) ^ 2) ≤ t * mPrime t := by
  rw [theta_eq ht]
  set y := π * t with hy
  have hy0 : 0 < y := by positivity
  have hs := sinh_ge_cubic hy0.le
  have hsp : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy0
  have h6 : 0 < 6 + y ^ 2 := by positivity
  rw [div_le_iff₀ h6, sub_mul, one_mul]
  have : y / Real.sinh y * (6 + y ^ 2) ≤ 6 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hsp]
    nlinarith [hs]
  nlinarith [this]

lemma theta_ge_Ici {t : ℝ} (ht : 1 / 8 ≤ t) :
    (π * (1 / 8)) ^ 2 / (6 + (π * (1 / 8)) ^ 2) ≤ t * mPrime t := by
  have ht0 : 0 < t := by linarith
  refine le_trans ?_ (theta_ge ht0)
  set y₀ := π * (1 / 8) with hy₀
  have hy0 : 0 < y₀ := by positivity
  have hyy : y₀ ≤ π * t := by rw [hy₀]; exact mul_le_mul_of_nonneg_left ht Real.pi_pos.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hy0 hy0, sq_nonneg (π * t - y₀), mul_nonneg hy0.le (sub_nonneg.mpr hyy)]

/-- `A(t) = 1/(t m'(t))`: `τ₀'/τ₀ = A ∘ τ₀`. -/
noncomputable def tauA (t : ℝ) : ℝ := (t * mPrime t)⁻¹


/-! ### Size of `τ₀` -/

lemma mQ_bounds : ∃ m₀ B : ℝ, 0 < m₀ ∧ m₀ ≤ B ∧ ∀ y ∈ Icc (0 : ℝ) (1 / 8), m₀ ≤ mQ y ∧ mQ y ≤ B := by
  have hc : ContinuousOn mQ (Icc (0 : ℝ) (1 / 8)) :=
    contDiffOn_mQ.continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨y₁, hy₁, h₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn ⟨0, by simp⟩ hc
  obtain ⟨y₂, hy₂, h₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMaxOn ⟨0, by simp⟩ hc
  have hp : 0 < mQ y₁ := mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [hy₁.1], by linarith [hy₁.2]⟩)
  exact ⟨mQ y₁, mQ y₂, hp, h₁ hy₂, fun y hy => ⟨h₁ hy, h₂ hy⟩⟩

/-- `τ₀(x)² ≥ c x` for `0 < x ≤ 1` (`m(t) ≤ C t²`). -/
lemma tau0_sq_ge : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ioc (0 : ℝ) 1, c * x ≤ tau0 x ^ 2 := by
  obtain ⟨m₀, B, hm₀, -, hB⟩ := mQ_bounds
  refine ⟨1 / max B 64, by positivity, fun x hx => ?_⟩
  have hB' : 0 < max B 64 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ht := tau0_pos hx.1
  have hxm : uctM (tau0 x) = x := ceEll_tau0 hx.1
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hB']
  rcases le_or_gt (tau0 x) (1 / 8) with h | h
  · have h1 := (hB (tau0 x) ⟨ht.le, h⟩).2
    rw [uctM_eq_sq_mul_mQ ht] at hxm
    nlinarith [le_max_left B 64, sq_nonneg (tau0 x), mul_le_mul_of_nonneg_left h1 (sq_nonneg (tau0 x))]
  · have h2 : (1 / 8 : ℝ) ^ 2 < tau0 x ^ 2 := by nlinarith
    nlinarith [le_max_right B 64, hx.2]

/-- `τ₀(x)² ≤ C x` for `0 < x ≤ 1` (`m(t) ≥ c t²` on `(0, τ₀(1)]`). -/
lemma tau0_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Ioc (0 : ℝ) 1, tau0 x ^ 2 ≤ C * x := by
  obtain ⟨m₀, B, hm₀, -, hB⟩ := mQ_bounds
  have hT : 0 < tau0 1 := tau0_pos one_pos
  have hμ : 0 < uctM (1 / 8) := uctM_pos (by norm_num)
  refine ⟨max (1 / m₀) (tau0 1 ^ 2 / uctM (1 / 8)), lt_of_lt_of_le (by positivity) (le_max_left _ _), fun x hx => ?_⟩
  have ht := tau0_pos hx.1
  have hxm : uctM (tau0 x) = x := ceEll_tau0 hx.1
  have hle : tau0 x ≤ tau0 1 := tau0_mono hx.1 hx.2
  rcases le_or_gt (tau0 x) (1 / 8) with h | h
  · have h1 := (hB (tau0 x) ⟨ht.le, h⟩).1
    rw [uctM_eq_sq_mul_mQ ht] at hxm
    have : tau0 x ^ 2 ≤ x / m₀ := by
      rw [le_div_iff₀ hm₀]; nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (tau0 x))]
    calc tau0 x ^ 2 ≤ x / m₀ := this
      _ = (1 / m₀) * x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hx.1.le
  · have hmono : uctM (1 / 8) ≤ x := by
      rw [← hxm]; exact (uctM_strictMonoOn.monotoneOn (by norm_num : (0 : ℝ) < 1 / 8) ht h.le)
    have h2 : tau0 x ^ 2 ≤ tau0 1 ^ 2 := pow_le_pow_left₀ ht.le hle 2
    have h3 : tau0 1 ^ 2 ≤ (tau0 1 ^ 2 / uctM (1 / 8)) * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
      exact mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
    exact (h2.trans h3).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.1.le)

lemma div_tanh_le {z : ℝ} (hz : 0 < z) : z / Real.tanh z ≤ 1 + z := by
  have hs : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hz
  have hc : 0 < Real.cosh z := Real.cosh_pos z
  rw [Real.tanh_eq_sinh_div_cosh, div_div_eq_mul_div, div_le_iff₀ hs]
  have h1 : z ≤ Real.sinh z := Real.self_le_sinh_iff.mpr hz.le
  have h2 : Real.cosh z - Real.sinh z = Real.exp (-z) := Real.cosh_sub_sinh z
  have h3 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith [Real.exp_pos (-z), mul_le_mul_of_nonneg_left h3 hz.le]

/-- `τ₀(x) ≥ (2/π)(e^x - 1)`: the growth `τ₀ ≍ e^L` (from `x coth x ≤ 1 + x`). -/
lemma tau0_ge_exp {x : ℝ} (hx : 0 < x) : 2 / π * (Real.exp x - 1) ≤ tau0 x := by
  have ht := tau0_pos hx
  have hxm : ceEll (π * tau0 x / 2) = x := ceEll_tau0 hx
  have hz : 0 < π * tau0 x / 2 := by positivity
  have h1 : x ≤ Real.log (1 + π * tau0 x / 2) := by
    calc x = ceEll (π * tau0 x / 2) := hxm.symm
      _ ≤ _ := by
        unfold ceEll
        exact Real.log_le_log (div_pos hz (by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr hz) (Real.cosh_pos _))) (div_tanh_le hz)
  have h2 : Real.exp x ≤ 1 + π * tau0 x / 2 := by
    calc Real.exp x ≤ Real.exp (Real.log (1 + π * tau0 x / 2)) := Real.exp_le_exp.mpr h1
      _ = _ := Real.exp_log (by positivity)
  have hπ := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hπ]
  nlinarith

end FormalResearch.SignUncertainty.FctSym
