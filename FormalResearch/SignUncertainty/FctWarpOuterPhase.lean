/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpOuterBase
public import FormalResearch.SignUncertainty.FctInnerPhase
public import FormalResearch.Asymptotics.BinetRemainder

/-!
# Outer phase and compensator/Binet `edgeW` bounds (`fct:warp-asymp` (1))

Leaf helper module for `FctWarpOuterIbp.lean`:
* `binetImag_edge_bounds`: uniform bounds for `t ↦ binetDiff c (i t)` on `{t ≠ 0}`.
* `vTotal_thetaD_edge_bounds`: uniform `edgeW`-weighted derivative bounds for
  `vTotal`, `fctThetaD (vTotal)`, `vAlpha 1 τ₁`, and `fctThetaD (vAlpha 1 τ₁)` on `τ > 1.85 τ₁`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.Asymptotics FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctEdgeIbp FormalResearch.SignUncertainty.FctSym

namespace FormalResearch.SignUncertainty

/-! ### 1. Binet remainder `edgeW` bounds on `{τ ≠ 0}` -/

private lemma binetDiff_differentiableOn_left {c : ℝ} (hc : 0 < c) :
    DifferentiableOn ℂ (binetDiff c) {ζ : ℂ | ζ.re < 1} := by
  have h1 : DifferentiableOn ℂ (fun ζ : ℂ => binetRem ((c : ℂ) * (1 - ζ))) {ζ : ℂ | ζ.re < 1} := by
    refine binetRem_differentiableOn.comp ?_ ?_
    · exact (differentiable_const _ |>.mul (differentiable_const _ |>.sub differentiable_id)).differentiableOn
    · intro ζ hζ
      simp only [mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, zero_mul, sub_zero]
      have : 0 < 1 - ζ.re := sub_pos.mpr hζ
      positivity
  exact h1.sub (differentiableOn_const _)

private lemma contDiff_binetImag {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ⊤ (fun τ : ℝ => binetDiff c ((τ : ℂ) * Complex.I)) := by
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hcd_C : ContDiffOn ℂ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} :=
    (binetDiff_differentiableOn_left hc).contDiffOn hopen
  have hcd_R : ContDiffOn ℝ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} := hcd_C.restrict_scalars ℝ
  rw [contDiff_iff_contDiffAt]
  intro τ
  have hmem : ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < 1} := by simp
  have hat : ContDiffAt ℝ ⊤ (binetDiff c) ((τ : ℂ) * Complex.I) := hcd_R.contDiffAt (hopen.mem_nhds hmem)
  have hlin : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact hat.comp τ hlin.contDiffAt

private lemma iteratedDeriv_binetImag {c : ℝ} (hc : 0 < c) (k : ℕ) (τ : ℝ) :
    iteratedDeriv k (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) τ =
      Complex.I ^ k * iteratedDeriv k (binetDiff c) ((τ : ℂ) * Complex.I) := by
  have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hcd_C : ContDiffOn ℂ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} :=
    (binetDiff_differentiableOn_left hc).contDiffOn hopen
  induction k generalizing τ with
  | zero => simp
  | succ k ih =>
    have hfun : iteratedDeriv k (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.I ^ k * iteratedDeriv k (binetDiff c) ((t : ℂ) * Complex.I) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hmem : ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | ζ.re < 1} := by simp
    have hcd_k : ContDiffOn ℂ ⊤ (iteratedDeriv k (binetDiff c)) {ζ : ℂ | ζ.re < 1} := by
      clear hmem ih hfun τ
      induction k with
      | zero => simpa using hcd_C
      | succ k ihk =>
        rw [show iteratedDeriv (k + 1) (binetDiff c) = deriv (iteratedDeriv k (binetDiff c)) by
          ext z; rw [iteratedDeriv_succ]]
        exact ihk.deriv_of_isOpen hopen (by simp)
    have hd_C : HasDerivAt (iteratedDeriv k (binetDiff c))
        (iteratedDeriv (k + 1) (binetDiff c) ((τ : ℂ) * Complex.I)) ((τ : ℂ) * Complex.I) := by
      rw [iteratedDeriv_succ]
      exact ((hcd_k.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
    have hcomp := (hd_C.scomp τ hlin).const_mul (Complex.I ^ k)
    have hcomp_deriv : deriv (fun t : ℝ => Complex.I ^ k * iteratedDeriv k (binetDiff c) ((t : ℂ) * Complex.I)) τ =
        Complex.I ^ k * (Complex.I * iteratedDeriv (k + 1) (binetDiff c) ((τ : ℂ) * Complex.I)) := by
      simpa [Function.comp, smul_eq_mul] using hcomp.deriv
    rw [hcomp_deriv, pow_succ]
    ring

lemma binetImag_edge_bounds (n : ℕ) :
    ∀ {c : ℝ}, 1 ≤ c →
      ContDiff ℝ ⊤ (fun t : ℝ => binetDiff c (Complex.I * (t : ℂ))) ∧
      (∀ τ : ℝ, ‖binetDiff c (Complex.I * (τ : ℂ))‖ ≤ 1 / 6) ∧
      (∀ k, 1 ≤ k → k ≤ n → ∀ τ : ℝ, τ ≠ 0 →
        ‖iteratedDeriv k (fun t : ℝ => binetDiff c (Complex.I * (t : ℂ))) τ‖ ≤
          ((n.factorial : ℝ) / 12) * edgeW τ ^ (-(k : ℤ))) := by
  intro c hc
  have hc0 : 0 < c := by linarith
  have heq_fn : (fun t : ℝ => binetDiff c (Complex.I * (t : ℂ))) =
      fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I) := by
    ext t; ring_nf
  refine ⟨by rw [heq_fn]; exact contDiff_binetImag hc0, ?_, ?_⟩
  · intro τ
    have hre : (Complex.I * (τ : ℂ)).re ≤ 0 := by simp
    refine (binetDiff_norm_le_left hc0 hre).trans ?_
    have : 6 ≤ 6 * c := by linarith
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) this
  · intro k hk1 hkn τ hτ0
    rw [heq_fn, iteratedDeriv_binetImag hc0 k τ, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    have hre : ((τ : ℂ) * Complex.I).re ≤ 0 := by simp
    have hbd := binetDiff_iteratedDeriv_norm_le hc0 hre hk1
    have hfac : (k.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hkn
    have h12c : (12 : ℝ) ≤ 12 * c := by linarith
    have hw : 1 ≤ edgeW τ ^ (-(k : ℤ)) := one_le_edgeW_inv hτ0 k
    calc ‖iteratedDeriv k (binetDiff c) ((τ : ℂ) * Complex.I)‖
        ≤ (k.factorial : ℝ) / (12 * c) := hbd
      _ ≤ (n.factorial : ℝ) / 12 :=
          div_le_div₀ (by positivity) hfac (by positivity) h12c
      _ ≤ ((n.factorial : ℝ) / 12) * edgeW τ ^ (-(k : ℤ)) :=
          le_mul_of_one_le_right (by positivity) hw

/-! ### 2. `vTotal` and `fctThetaD` `edgeW` bounds on `τ > 1.85 τ₁` -/

private lemma tau1_pow_le_helpers {K4 c τ₁ : ℝ} (hτ₁ : 0 < τ₁) (hτ₁_le1 : τ₁ ≤ 1)
    (hcτ : τ₁ ^ 4 * c = 1) (hK4τ : K4 * τ₁ ^ 2 ≤ 1) (r : ℕ) :
    τ₁ ^ ((2 : ℤ) - r) ≤ τ₁ ^ (-(r : ℤ)) ∧
    K4 * τ₁ ^ ((4 : ℤ) - r) ≤ τ₁ ^ (-(r : ℤ)) ∧
    c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) ≤ τ₁ ^ (-(r : ℤ)) ∧
    K4 * (c⁻¹ * τ₁ ^ ((1 : ℤ) - r)) ≤ τ₁ ^ (-(r : ℤ)) := by
  have hcinv : c⁻¹ = τ₁ ^ 4 := inv_eq_of_mul_eq_one_right (by rwa [mul_comm])
  have hpow2 : τ₁ ^ ((2 : ℤ) - r) ≤ τ₁ ^ (-(r : ℤ)) := by
    rw [show ((2 : ℤ) - r) = (2 : ℤ) + (-(r : ℤ)) by ring, zpow_add₀ hτ₁.ne',
      show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
    exact mul_le_of_le_one_left (zpow_nonneg hτ₁.le _) (pow_le_one₀ hτ₁.le hτ₁_le1)
  have hzK4_0m : K4 * τ₁ ^ ((4 : ℤ) - r) ≤ τ₁ ^ (-(r : ℤ)) := by
    rw [show ((4 : ℤ) - r) = (4 : ℤ) + (-(r : ℤ)) by ring, zpow_add₀ hτ₁.ne',
      show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast,
      show K4 * (τ₁ ^ 4 * τ₁ ^ (-(r : ℤ))) = (K4 * τ₁ ^ 2) * τ₁ ^ 2 * τ₁ ^ (-(r : ℤ)) by ring]
    have h1 : K4 * τ₁ ^ 2 * τ₁ ^ 2 ≤ 1 * 1 := mul_le_mul hK4τ (pow_le_one₀ hτ₁.le hτ₁_le1) (sq_nonneg τ₁) zero_le_one
    rw [mul_one] at h1
    exact mul_le_of_le_one_left (zpow_nonneg hτ₁.le _) h1
  have hz_1b : c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) ≤ τ₁ ^ (-(r : ℤ)) := by
    rw [hcinv, ← zpow_natCast τ₁ 4, ← zpow_add₀ hτ₁.ne',
      show ((4 : ℕ) : ℤ) + ((-1 : ℤ) - r) = (3 : ℤ) + (-(r : ℤ)) by ring, zpow_add₀ hτ₁.ne',
      show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast]
    exact mul_le_of_le_one_left (zpow_nonneg hτ₁.le _) (pow_le_one₀ hτ₁.le hτ₁_le1)
  have hzK4_1m : K4 * (c⁻¹ * τ₁ ^ ((1 : ℤ) - r)) ≤ τ₁ ^ (-(r : ℤ)) := by
    rw [hcinv, ← zpow_natCast τ₁ 4, ← zpow_add₀ hτ₁.ne',
      show ((4 : ℕ) : ℤ) + ((1 : ℤ) - r) = (5 : ℤ) + (-(r : ℤ)) by ring, zpow_add₀ hτ₁.ne',
      show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, zpow_natCast,
      show K4 * (τ₁ ^ 5 * τ₁ ^ (-(r : ℤ))) = (K4 * τ₁ ^ 2) * τ₁ ^ 3 * τ₁ ^ (-(r : ℤ)) by ring]
    have h1 : K4 * τ₁ ^ 2 * τ₁ ^ 3 ≤ 1 * 1 := mul_le_mul hK4τ (pow_le_one₀ hτ₁.le hτ₁_le1) (by positivity) zero_le_one
    rw [mul_one] at h1
    exact mul_le_of_le_one_left (zpow_nonneg hτ₁.le _) h1
  exact ⟨hpow2, hzK4_0m, hz_1b, hzK4_1m⟩

private lemma tau1_to_edgeW_le {τ₁ τ : ℝ} (hτ₁ : 0 < τ₁) (hτ_pos : 0 < τ) (hle : τ ≤ 12 * τ₁) (k : ℕ) :
    τ₁ ^ (-(k : ℤ)) ≤ (12 : ℝ) ^ k * edgeW τ ^ (-(k : ℤ)) := by
  have hw_le : edgeW τ ≤ 12 * τ₁ := (edgeW_le_abs τ).trans (by rwa [abs_of_pos hτ_pos])
  have hw_pos : 0 < edgeW τ := edgeW_pos hτ_pos.ne'
  have h1 : τ₁⁻¹ ≤ 12 * (edgeW τ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hw_pos, inv_mul_le_iff₀ hτ₁]; linarith
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h1 k

private lemma vAlpha1_bounds_helper {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc0 : 0 < c)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) :
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    let Cva := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.2.1
    let Ctha := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.2.2.2.2.2.2.1
    let CLa := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    let C_tail := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (∀ r t, |iteratedDeriv r (vAlpha 1 τ₁) t| ≤ Cva r * τ₁ ^ ((2 : ℤ) - r)) ∧
    (∀ r t, |t| ≤ 12 * τ₁ → |iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤ Ctha r * τ₁ ^ ((2 : ℤ) - r)) ∧
    (∀ r t, 12 * τ₁ ≤ |t| → |iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤
      C_tail r * CLa * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|)) ∧
    (∀ t, 10 * τ₁ ≤ |t| → vAlpha 1 τ₁ t = 0) := by
  intro τ₁ Cva Ctha CLa C_tail
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    exact inv_mul_cancel₀ hc0.ne'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCv_nn, hCth_nn, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have hsq := hmain hK4 hc0 hτ₁ hτD hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
  have hv1 := fun s => (fctThetaD_vAlpha_eq hK4 hc0 hτ₁ hτD hcτ (τ₁ ^ 2) s).1
  have hfn_v : vAlpha 1 τ₁ = fun s => (τ₁ ^ 2)⁻¹ * vAlpha (τ₁ ^ 2) τ₁ s :=
    funext fun s => vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ s (pow_ne_zero 2 hτ₁.ne')
  have hfn_th : fctThetaD (vAlpha 1 τ₁) = fun s => (τ₁ ^ 2)⁻¹ * fctThetaD (vAlpha (τ₁ ^ 2) τ₁) s := by
    ext s; rw [hv1 s]; field_simp [pow_ne_zero 2 hτ₁.ne']
  refine ⟨fun r t => ?_, fun r t ht => ?_, fun r t ht => ?_, fun t ht => ?_⟩
  · have h1 := (hsq.2.2.2.2.1 r t).2.2.1
    rw [abs_of_nonneg (sq_nonneg τ₁)] at h1
    rw [hfn_v, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hτ₁))]
    calc (τ₁ ^ 2)⁻¹ * |iteratedDeriv r (vAlpha (τ₁ ^ 2) τ₁) t|
        ≤ (τ₁ ^ 2)⁻¹ * (Cva r * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cva r * τ₁ ^ ((2 : ℤ) - r) := by field_simp [pow_ne_zero 2 hτ₁.ne']
  · have h1 := (hsq.2.2.2.2.2.1 r t ht).2.2.1
    rw [abs_of_nonneg (sq_nonneg τ₁)] at h1
    have hmin : min (1 : ℝ) ((|t| / τ₁) ^ (11 - r)) ≤ 1 := min_le_left _ _
    have h1' : |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t| ≤ Ctha r * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r) :=
      h1.trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (hCth_nn r).2.2.1 (sq_nonneg _))
        (zpow_nonneg hτ₁.le _)) hmin)
    rw [hfn_th, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hτ₁))]
    calc (τ₁ ^ 2)⁻¹ * |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t|
        ≤ (τ₁ ^ 2)⁻¹ * (Ctha r * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r)) := mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = Ctha r * τ₁ ^ ((2 : ℤ) - r) := by field_simp [pow_ne_zero 2 hτ₁.ne']
  · have h1 := (hsq.2.2.2.2.2.2.1 r t ht).2.2
    rw [abs_of_nonneg (sq_nonneg τ₁)] at h1
    rw [hfn_th, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hτ₁))]
    calc (τ₁ ^ 2)⁻¹ * |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t|
        ≤ (τ₁ ^ 2)⁻¹ * (C_tail r * CLa * τ₁ ^ 2 * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C_tail r * CLa * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          field_simp [pow_ne_zero 2 hτ₁.ne']
  · have hsupp := hsq.2.2.2.1.2.2.1
    have ha0 : vAlpha (τ₁ ^ 2) τ₁ t = 0 := by
      by_contra hne
      have hmem := hsupp hne
      rcases abs_lt.mp hmem with ⟨h1, h2⟩
      have : |t| < 10 * τ₁ := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    rw [vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ t (pow_ne_zero 2 hτ₁.ne'), ha0, mul_zero]

private lemma vTotal_deriv_helper {K4 c α : ℝ} (hK4 : 1 ≤ K4) (hc0 : 0 < c)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hK4τ : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1) (hα : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2) :
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    let Cv0b := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.1
    let Cv0m := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.1
    let Cva := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.1
    let Cv1b := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.2.1
    let Cv1m := (fct_comp_D_part1 StripKernelChoice.star).choose_spec.2.2.2.2.2.2.1
    ∀ r t, |iteratedDeriv r (vTotal StripKernelChoice.star K4 c α τ₁) t| ≤
      (Cv0b r + Cv0m r + Cv1b r + Cv1m r + 2 * Cva r) * τ₁ ^ (-(r : ℤ)) := by
  intro τ₁ Cv0b Cv0m Cva Cv1b Cv1m r t
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    exact inv_mul_cancel₀ hc0.ne'
  obtain ⟨_, hτD_le, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCv_nn, _, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have hτ₁_le1 : τ₁ ≤ 1 := hτD.trans (hτD_le.trans (by norm_num))
  have h0 := hmain hK4 hc0 hτ₁ hτD hcτ (show |(0 : ℝ)| ≤ τ₁ ^ 2 by rw [abs_zero]; exact sq_nonneg τ₁)
  have hva := (vAlpha1_bounds_helper hK4 hc0 hτD).1 r t
  have hv0_data := vTotal_data hK4 hc0 hτD 0
  have hva_1_cd : ContDiff ℝ ⊤ (vAlpha 1 τ₁) := (fctThetaD_vAlpha_eq hK4 hc0 hτ₁ hτD hcτ (τ₁ ^ 2) 0).2.1
  obtain ⟨hpow2, hzK4_0m, hz_1b, hzK4_1m⟩ := tau1_pow_le_helpers hτ₁ hτ₁_le1 hcτ hK4τ r
  have hv0_eq : vTotal StripKernelChoice.star K4 c 0 τ₁ =
      fun s => (v0Base StripKernelChoice.star τ₁ s + K4 * v0Marg τ₁ s) +
        (v1Base StripKernelChoice.star c τ₁ s + K4 * v1Marg c τ₁ s) := rfl
  have hv_split : vTotal StripKernelChoice.star K4 c α τ₁ =
      fun s => vTotal StripKernelChoice.star K4 c 0 τ₁ s + α * vAlpha 1 τ₁ s :=
    funext (vTotal_eq_zero_add_smul K4 c α τ₁)
  have hcd0 : ContDiffAt ℝ r (vTotal StripKernelChoice.star K4 c 0 τ₁) t := hv0_data.1.contDiffAt.of_le (by exact_mod_cast le_top)
  have hcda : ContDiffAt ℝ r (fun s => α * vAlpha 1 τ₁ s) t := (contDiff_const.mul hva_1_cd).contDiffAt.of_le (by exact_mod_cast le_top)
  have hcdb0 : ContDiffAt ℝ r (v0Base StripKernelChoice.star τ₁) t := h0.1.1.contDiffAt.of_le (by exact_mod_cast le_top)
  have hcdm0 : ContDiffAt ℝ r (fun s => K4 * v0Marg τ₁ s) t := (contDiff_const.mul h0.1.2.1).contDiffAt.of_le (by exact_mod_cast le_top)
  have hcdb1 : ContDiffAt ℝ r (v1Base StripKernelChoice.star c τ₁) t := h0.1.2.2.2.1.contDiffAt.of_le (by exact_mod_cast le_top)
  have hcdm1 : ContDiffAt ℝ r (fun s => K4 * v1Marg c τ₁ s) t := (contDiff_const.mul h0.1.2.2.2.2.1).contDiffAt.of_le (by exact_mod_cast le_top)
  have hr_v0 : iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) t =
      (iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t + K4 * iteratedDeriv r (v0Marg τ₁) t) +
        (iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t + K4 * iteratedDeriv r (v1Marg c τ₁) t) := by
    rw [hv0_eq]
    change iteratedDeriv r ((fun s => v0Base StripKernelChoice.star τ₁ s + K4 * v0Marg τ₁ s) +
      (fun s => v1Base StripKernelChoice.star c τ₁ s + K4 * v1Marg c τ₁ s)) t = _
    rw [iteratedDeriv_add (hcdb0.add hcdm0) (hcdb1.add hcdm1),
      iteratedDeriv_add hcdb0 hcdm0, iteratedDeriv_add hcdb1 hcdm1,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hr_v : iteratedDeriv r (vTotal StripKernelChoice.star K4 c α τ₁) t =
      iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) t + α * iteratedDeriv r (vAlpha 1 τ₁) t := by
    rw [hv_split]
    change iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁ + fun s => α * vAlpha 1 τ₁ s) t = _
    rw [iteratedDeriv_add hcd0 hcda, iteratedDeriv_const_mul_field]
  rw [hr_v, hr_v0]
  obtain ⟨d1, d2, _, d4, d5⟩ := h0.2.2.2.2.1 r t
  have hK4_nn : 0 ≤ K4 := by linarith
  have ht2 : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁.le hτ₁_le1
  have hα_bd : |α| * τ₁ ^ ((2 : ℤ) - r) ≤ 2 * τ₁ ^ (-(r : ℤ)) :=
    calc |α| * τ₁ ^ ((2 : ℤ) - r) ≤ (2 * τ₁ ^ 2) * τ₁ ^ ((2 : ℤ) - r) :=
          mul_le_mul_of_nonneg_right hα (zpow_nonneg hτ₁.le _)
      _ ≤ (2 * 1) * τ₁ ^ (-(r : ℤ)) := mul_le_mul (by linarith) hpow2 (zpow_nonneg hτ₁.le _) zero_le_two
      _ = 2 * τ₁ ^ (-(r : ℤ)) := by ring
  have t1 : |iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t| ≤ Cv0b r * τ₁ ^ (-(r : ℤ)) :=
    d1.trans (mul_le_mul_of_nonneg_left hpow2 (hCv_nn r).1)
  have t2 : K4 * |iteratedDeriv r (v0Marg τ₁) t| ≤ Cv0m r * τ₁ ^ (-(r : ℤ)) :=
    (mul_le_mul_of_nonneg_left d2 hK4_nn).trans (by
      calc K4 * (Cv0m r * τ₁ ^ ((4 : ℤ) - r)) = Cv0m r * (K4 * τ₁ ^ ((4 : ℤ) - r)) := by ring
        _ ≤ Cv0m r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hzK4_0m (hCv_nn r).2.1)
  have t4 : |iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t| ≤ Cv1b r * τ₁ ^ (-(r : ℤ)) :=
    d4.trans (by
      calc Cv1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) = Cv1b r * (c⁻¹ * τ₁ ^ ((-1 : ℤ) - r)) := by ring
        _ ≤ Cv1b r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hz_1b (hCv_nn r).2.2.2.1)
  have t5 : K4 * |iteratedDeriv r (v1Marg c τ₁) t| ≤ Cv1m r * τ₁ ^ (-(r : ℤ)) :=
    (mul_le_mul_of_nonneg_left d5 hK4_nn).trans (by
      calc K4 * (Cv1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r)) = Cv1m r * (K4 * (c⁻¹ * τ₁ ^ ((1 : ℤ) - r))) := by ring
        _ ≤ Cv1m r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hzK4_1m (hCv_nn r).2.2.2.2)
  have tα : |α| * |iteratedDeriv r (vAlpha 1 τ₁) t| ≤ 2 * Cva r * τ₁ ^ (-(r : ℤ)) :=
    (mul_le_mul_of_nonneg_left hva (abs_nonneg α)).trans (by
      calc |α| * (Cva r * τ₁ ^ ((2 : ℤ) - r)) = Cva r * (|α| * τ₁ ^ ((2 : ℤ) - r)) := by ring
        _ ≤ Cva r * (2 * τ₁ ^ (-(r : ℤ))) := mul_le_mul_of_nonneg_left hα_bd (hCv_nn r).2.2.1
        _ = 2 * Cva r * τ₁ ^ (-(r : ℤ)) := by ring)
  have a1 := abs_add_le ((iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t +
    K4 * iteratedDeriv r (v0Marg τ₁) t) +
    (iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t + K4 * iteratedDeriv r (v1Marg c τ₁) t))
    (α * iteratedDeriv r (vAlpha 1 τ₁) t)
  have a2 := abs_add_le (iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t + K4 * iteratedDeriv r (v0Marg τ₁) t)
    (iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t + K4 * iteratedDeriv r (v1Marg c τ₁) t)
  have a3 := abs_add_le (iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t) (K4 * iteratedDeriv r (v0Marg τ₁) t)
  have a4 := abs_add_le (iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t) (K4 * iteratedDeriv r (v1Marg c τ₁) t)
  rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4; rw [abs_mul] at a1
  have hsum : (Cv0b r + Cv0m r + Cv1b r + Cv1m r + 2 * Cva r) * τ₁ ^ (-(r : ℤ)) =
      Cv0b r * τ₁ ^ (-(r : ℤ)) + Cv0m r * τ₁ ^ (-(r : ℤ)) + Cv1b r * τ₁ ^ (-(r : ℤ)) +
      Cv1m r * τ₁ ^ (-(r : ℤ)) + 2 * Cva r * τ₁ ^ (-(r : ℤ)) := by ring
  linarith only [a1, a2, a3, a4, t1, t2, t4, t5, tα, hsum]

end FormalResearch.SignUncertainty
