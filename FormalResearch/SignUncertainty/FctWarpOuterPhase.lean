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

private lemma vAlpha1_all_helpers {K4 c τ₁ : ℝ} {Cva Ctha C_tail : ℕ → ℝ} {CLa : ℝ}
    (hK4 : 1 ≤ K4) (hc0 : 0 < c) (hτ₁ : 0 < τ₁) (hτD : τ₁ ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hcτ : τ₁ ^ 4 * c = 1) (hCtha0 : ∀ r, 0 ≤ Ctha r)
    (h_d : ∀ r t, |iteratedDeriv r (vAlpha (τ₁ ^ 2) τ₁) t| ≤ Cva r * |τ₁ ^ 2| * τ₁ ^ ((2 : ℤ) - r))
    (h_in : ∀ r t, |t| ≤ 12 * τ₁ →
      |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t| ≤ Ctha r * |τ₁ ^ 2| * τ₁ ^ ((2 : ℤ) - r) * min 1 ((|t| / τ₁) ^ (11 - r)))
    (h_tail : ∀ r t, 12 * τ₁ ≤ |t| →
      |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t| ≤ C_tail r * CLa * |τ₁ ^ 2| * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|))
    (h_supp : Function.support (vAlpha (τ₁ ^ 2) τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁)) :
    (∀ r t, |iteratedDeriv r (vAlpha 1 τ₁) t| ≤ Cva r * τ₁ ^ ((2 : ℤ) - r)) ∧
    (∀ r t, |t| ≤ 12 * τ₁ → |iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤ Ctha r * τ₁ ^ ((2 : ℤ) - r)) ∧
    (∀ r t, 12 * τ₁ ≤ |t| → |iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤
      C_tail r * CLa * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|)) ∧
    (∀ t, 10 * τ₁ ≤ |t| → vAlpha 1 τ₁ t = 0) := by
  have hv1 := fun s => (fctThetaD_vAlpha_eq hK4 hc0 hτ₁ hτD hcτ (τ₁ ^ 2) s).1
  have hfn_v : vAlpha 1 τ₁ = fun s => (τ₁ ^ 2)⁻¹ * vAlpha (τ₁ ^ 2) τ₁ s :=
    funext fun s => vAlpha_eq_inv_mul (τ₁ ^ 2) τ₁ s (pow_ne_zero 2 hτ₁.ne')
  have hfn_th : fctThetaD (vAlpha 1 τ₁) = fun s => (τ₁ ^ 2)⁻¹ * fctThetaD (vAlpha (τ₁ ^ 2) τ₁) s := by
    ext s; rw [hv1 s]; field_simp [pow_ne_zero 2 hτ₁.ne']
  refine ⟨fun r t => ?_, fun r t ht => ?_, fun r t ht => ?_, fun t ht => ?_⟩
  · have h1 := h_d r t
    rw [abs_of_nonneg (sq_nonneg τ₁)] at h1
    rw [hfn_v, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hτ₁))]
    calc (τ₁ ^ 2)⁻¹ * |iteratedDeriv r (vAlpha (τ₁ ^ 2) τ₁) t|
        ≤ (τ₁ ^ 2)⁻¹ * (Cva r * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cva r * τ₁ ^ ((2 : ℤ) - r) := by field_simp [pow_ne_zero 2 hτ₁.ne']
  · have h1 := h_in r t ht
    rw [abs_of_nonneg (sq_nonneg τ₁)] at h1
    have hmin : min (1 : ℝ) ((|t| / τ₁) ^ (11 - r)) ≤ 1 := min_le_left _ _
    have h1' : |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t| ≤ Ctha r * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r) :=
      h1.trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (hCtha0 r) (sq_nonneg _)) (zpow_nonneg hτ₁.le _)) hmin)
    rw [hfn_th, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hτ₁))]
    calc (τ₁ ^ 2)⁻¹ * |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t|
        ≤ (τ₁ ^ 2)⁻¹ * (Ctha r * τ₁ ^ 2 * τ₁ ^ ((2 : ℤ) - r)) := mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = Ctha r * τ₁ ^ ((2 : ℤ) - r) := by field_simp [pow_ne_zero 2 hτ₁.ne']
  · have h1 := h_tail r t ht
    rw [abs_of_nonneg (sq_nonneg τ₁)] at h1
    rw [hfn_th, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hτ₁))]
    calc (τ₁ ^ 2)⁻¹ * |iteratedDeriv r (fctThetaD (vAlpha (τ₁ ^ 2) τ₁)) t|
        ≤ (τ₁ ^ 2)⁻¹ * (C_tail r * CLa * τ₁ ^ 2 * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C_tail r * CLa * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) := by
          field_simp [pow_ne_zero 2 hτ₁.ne']
  · have ha0 : vAlpha (τ₁ ^ 2) τ₁ t = 0 := by
      by_contra hne
      have hmem := h_supp hne
      have habs : |t| < 10 * τ₁ := abs_lt.mpr ⟨by linarith [hmem.1], hmem.2⟩
      linarith
    rw [vAlpha_eq_smul (τ₁ ^ 2) τ₁ t] at ha0
    exact (mul_eq_zero.mp ha0).resolve_left (pow_ne_zero 2 hτ₁.ne')

private lemma vTotal_deriv_all_helper {K4 c α τ₁ : ℝ} {Cv0b Cv0m Cva Cv1b Cv1m : ℕ → ℝ}
    (hK4_nn : 0 ≤ K4) (hτ₁ : 0 < τ₁) (hτ₁_le1 : τ₁ ≤ 1) (hcτ : τ₁ ^ 4 * c = 1) (hK4τ : K4 * τ₁ ^ 2 ≤ 1)
    (hα : |α| ≤ 2 * τ₁ ^ 2)
    (hCv0 : ∀ r, 0 ≤ Cv0b r ∧ 0 ≤ Cv0m r ∧ 0 ≤ Cva r ∧ 0 ≤ Cv1b r ∧ 0 ≤ Cv1m r)
    (hcd_b0 : ContDiff ℝ ∞ (v0Base StripKernelChoice.star τ₁))
    (hcd_m0 : ContDiff ℝ ∞ (v0Marg τ₁))
    (hcd_b1 : ContDiff ℝ ∞ (v1Base StripKernelChoice.star c τ₁))
    (hcd_m1 : ContDiff ℝ ∞ (v1Marg c τ₁))
    (hcd_v0 : ContDiff ℝ ∞ (vTotal StripKernelChoice.star K4 c 0 τ₁))
    (hcd_a1 : ContDiff ℝ ∞ (vAlpha 1 τ₁))
    (h_d0 : ∀ r t,
      |iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t| ≤ Cv0b r * τ₁ ^ ((2 : ℤ) - r) ∧
      |iteratedDeriv r (v0Marg τ₁) t| ≤ Cv0m r * τ₁ ^ ((4 : ℤ) - r) ∧
      |iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t| ≤ Cv1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) ∧
      |iteratedDeriv r (v1Marg c τ₁) t| ≤ Cv1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r))
    (h_a1 : ∀ r t, |iteratedDeriv r (vAlpha 1 τ₁) t| ≤ Cva r * τ₁ ^ ((2 : ℤ) - r)) :
    ∀ r t, |iteratedDeriv r (vTotal StripKernelChoice.star K4 c α τ₁) t| ≤
      (Cv0b r + Cv0m r + Cv1b r + Cv1m r + 2 * Cva r) * τ₁ ^ (-(r : ℤ)) := by
  intro r t
  obtain ⟨hpow2, hzK4_0m, hz_1b, hzK4_1m⟩ := tau1_pow_le_helpers hτ₁ hτ₁_le1 hcτ hK4τ r
  have hv0_eq : vTotal StripKernelChoice.star K4 c 0 τ₁ =
      (v0Base StripKernelChoice.star τ₁ + fun s => K4 * v0Marg τ₁ s) +
        (v1Base StripKernelChoice.star c τ₁ + fun s => K4 * v1Marg c τ₁ s) := by
    funext s; unfold vTotal v0 v1
    rw [show vAlpha (0 : ℝ) τ₁ s = 0 by rw [vAlpha_eq_smul]; ring, add_zero]; rfl
  have hv_split : vTotal StripKernelChoice.star K4 c α τ₁ =
      vTotal StripKernelChoice.star K4 c 0 τ₁ + fun s => α * vAlpha 1 τ₁ s :=
    funext (vTotal_eq_zero_add_smul K4 c α τ₁)
  have hle_top : ((r : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hcd0 : ContDiffAt ℝ r (vTotal StripKernelChoice.star K4 c 0 τ₁) t := hcd_v0.contDiffAt.of_le hle_top
  have hcda : ContDiffAt ℝ r (fun s => α * vAlpha 1 τ₁ s) t := (contDiff_const.mul hcd_a1).contDiffAt.of_le hle_top
  have hcdb0 : ContDiffAt ℝ r (v0Base StripKernelChoice.star τ₁) t := hcd_b0.contDiffAt.of_le hle_top
  have hcdm0 : ContDiffAt ℝ r (fun s => K4 * v0Marg τ₁ s) t := (contDiff_const.mul hcd_m0).contDiffAt.of_le hle_top
  have hcdb1 : ContDiffAt ℝ r (v1Base StripKernelChoice.star c τ₁) t := hcd_b1.contDiffAt.of_le hle_top
  have hcdm1 : ContDiffAt ℝ r (fun s => K4 * v1Marg c τ₁ s) t := (contDiff_const.mul hcd_m1).contDiffAt.of_le hle_top
  have hcd_p0 : ContDiffAt ℝ r (v0Base StripKernelChoice.star τ₁ + fun s => K4 * v0Marg τ₁ s) t := hcdb0.add hcdm0
  have hcd_p1 : ContDiffAt ℝ r (v1Base StripKernelChoice.star c τ₁ + fun s => K4 * v1Marg c τ₁ s) t := hcdb1.add hcdm1
  have hr_v0 : iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) t =
      (iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t + K4 * iteratedDeriv r (v0Marg τ₁) t) +
        (iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t + K4 * iteratedDeriv r (v1Marg c τ₁) t) := by
    rw [hv0_eq, iteratedDeriv_add hcd_p0 hcd_p1,
      iteratedDeriv_add hcdb0 hcdm0, iteratedDeriv_add hcdb1 hcdm1,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hr_v : iteratedDeriv r (vTotal StripKernelChoice.star K4 c α τ₁) t =
      iteratedDeriv r (vTotal StripKernelChoice.star K4 c 0 τ₁) t + α * iteratedDeriv r (vAlpha 1 τ₁) t := by
    rw [hv_split, iteratedDeriv_add hcd0 hcda, iteratedDeriv_const_mul_field]
  rw [hr_v, hr_v0]
  obtain ⟨d1, d2, d4, d5⟩ := h_d0 r t
  have da := h_a1 r t
  have hCv := hCv0 r
  have hα_bd : |α| * τ₁ ^ ((2 : ℤ) - r) ≤ 2 * τ₁ ^ (-(r : ℤ)) :=
    calc |α| * τ₁ ^ ((2 : ℤ) - r) ≤ (2 * τ₁ ^ 2) * τ₁ ^ ((2 : ℤ) - r) := mul_le_mul_of_nonneg_right hα (zpow_nonneg hτ₁.le _)
      _ ≤ (2 * 1) * τ₁ ^ (-(r : ℤ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hτ₁.le hτ₁_le1) zero_le_two)
            hpow2 (zpow_nonneg hτ₁.le _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
      _ = 2 * τ₁ ^ (-(r : ℤ)) := by ring
  have t1 : |iteratedDeriv r (v0Base StripKernelChoice.star τ₁) t| ≤ Cv0b r * τ₁ ^ (-(r : ℤ)) :=
    d1.trans (mul_le_mul_of_nonneg_left hpow2 hCv.1)
  have t2 : K4 * |iteratedDeriv r (v0Marg τ₁) t| ≤ Cv0m r * τ₁ ^ (-(r : ℤ)) :=
    (mul_le_mul_of_nonneg_left d2 hK4_nn).trans (by
      calc K4 * (Cv0m r * τ₁ ^ ((4 : ℤ) - r)) = Cv0m r * (K4 * τ₁ ^ ((4 : ℤ) - r)) := by ring
        _ ≤ Cv0m r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hzK4_0m hCv.2.1)
  have t4 : |iteratedDeriv r (v1Base StripKernelChoice.star c τ₁) t| ≤ Cv1b r * τ₁ ^ (-(r : ℤ)) :=
    d4.trans (by
      calc Cv1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) = Cv1b r * (c⁻¹ * τ₁ ^ ((-1 : ℤ) - r)) := by ring
        _ ≤ Cv1b r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hz_1b hCv.2.2.2.1)
  have t5 : K4 * |iteratedDeriv r (v1Marg c τ₁) t| ≤ Cv1m r * τ₁ ^ (-(r : ℤ)) :=
    (mul_le_mul_of_nonneg_left d5 hK4_nn).trans (by
      calc K4 * (Cv1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r)) = Cv1m r * (K4 * (c⁻¹ * τ₁ ^ ((1 : ℤ) - r))) := by ring
        _ ≤ Cv1m r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hzK4_1m hCv.2.2.2.2)
  have tα : |α| * |iteratedDeriv r (vAlpha 1 τ₁) t| ≤ 2 * Cva r * τ₁ ^ (-(r : ℤ)) :=
    (mul_le_mul_of_nonneg_left da (abs_nonneg α)).trans (by
      calc |α| * (Cva r * τ₁ ^ ((2 : ℤ) - r)) = Cva r * (|α| * τ₁ ^ ((2 : ℤ) - r)) := by ring
        _ ≤ Cva r * (2 * τ₁ ^ (-(r : ℤ))) := mul_le_mul_of_nonneg_left hα_bd hCv.2.2.1
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

private lemma fctThetaD_zero_split {K4 c : ℝ} (hK4 : 1 ≤ K4) (hc0 : 0 < c)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hcd_v0 : ContDiff ℝ ∞ (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_v0 : HasCompactSupport (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
    (hcd_v1 : ContDiff ℝ ∞ (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))))
    (hcs_v1 : HasCompactSupport (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))))
    (hcd_va0 : ContDiff ℝ ∞ (vAlpha 0 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_va0 : HasCompactSupport (vAlpha 0 (c ^ (-(1 / 4 : ℝ))))) :
    ∀ s, fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) s =
      fctThetaD (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))) s +
        fctThetaD (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))) s := by
  intro s
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    exact inv_mul_cancel₀ hc0.ne'
  have l0 := fctThetaD_linear hcd_v0 hcs_v0 hcd_v1 hcs_v1 1 1 s
  have ha0 : fctThetaD (vAlpha 0 τ₁) s = 0 := by simpa using (fctThetaD_vAlpha_eq hK4 hc0 hτ₁ hτD hcτ 0 s).1
  have l0' := fctThetaD_linear (hcd_v0.add hcd_v1) (hcs_v0.add hcs_v1) hcd_va0 hcs_va0 1 1 s
  simp only [one_mul] at l0 l0'
  change fctThetaD (fun u => v0 StripKernelChoice.star K4 τ₁ u + v1 StripKernelChoice.star K4 c τ₁ u + vAlpha 0 τ₁ u) s = _
  rw [l0', ha0, add_zero, l0]

private lemma fctThetaD_tail_all_helper {K4 c α : ℝ} {C_tail : ℕ → ℝ} {CL0b CL0m CLa CL1b CL1m : ℝ}
    (hK4 : 1 ≤ K4) (hc0 : 0 < c)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hτ₁_le1 : c ^ (-(1 / 4 : ℝ)) ≤ 1)
    (hK4τ : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1) (hα : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2)
    (hCL : 0 ≤ CL0b ∧ 0 ≤ CL0m ∧ 0 ≤ CLa ∧ 0 ≤ CL1b ∧ 0 ≤ CL1m) (hCt : ∀ r, 0 ≤ C_tail r)
    (hcd_v0 : ContDiff ℝ ∞ (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_v0 : HasCompactSupport (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
    (hcd_v1 : ContDiff ℝ ∞ (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))))
    (hcs_v1 : HasCompactSupport (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))))
    (hcd_va0 : ContDiff ℝ ∞ (vAlpha 0 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_va0 : HasCompactSupport (vAlpha 0 (c ^ (-(1 / 4 : ℝ)))))
    (hcd_a1 : ContDiff ℝ ∞ (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_a1 : HasCompactSupport (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))))
    (ht01 : ∀ r t, 12 * c ^ (-(1 / 4 : ℝ)) ≤ |t| →
      |iteratedDeriv r (fctThetaD (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ))))) t| ≤
        C_tail r * (CL0b + K4 * CL0m) * (c ^ (-(1 / 4 : ℝ))) ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|) ∧
      |iteratedDeriv r (fctThetaD (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))))) t| ≤
        C_tail r * (CL1b + K4 * CL1m) * c⁻¹ * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|))
    (hta1 : ∀ r t, 12 * c ^ (-(1 / 4 : ℝ)) ≤ |t| →
      |iteratedDeriv r (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) t| ≤
        C_tail r * CLa * (c ^ (-(1 / 4 : ℝ))) ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|)) :
    ∀ r t, 12 * c ^ (-(1 / 4 : ℝ)) ≤ |t| →
      |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) t| ≤
        (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)) * c ^ (-(1 / 4 : ℝ)) * |t| ^ (-(1 + (r : ℤ))) := by
  intro r t hgt
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    exact inv_mul_cancel₀ hc0.ne'
  have hcinv : c⁻¹ = τ₁ ^ 4 := inv_eq_of_mul_eq_one_right (by rwa [mul_comm])
  have ht_pos : 0 < |t| := lt_of_lt_of_le (by positivity) hgt
  have hexp1 : Real.exp (-(π / 2) * |t|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (abs_nonneg _))
  have hfac_nn : 0 ≤ |t| ^ (-(1 + (r : ℤ))) := zpow_nonneg ht_pos.le _
  obtain ⟨ht0, ht1⟩ := ht01 r t hgt
  have hta := hta1 r t hgt
  have h0_eq := fctThetaD_zero_split hK4 hc0 hτD hcd_v0 hcs_v0 hcd_v1 hcs_v1 hcd_va0 hcs_va0
  have hth_a1_cd : ContDiff ℝ ∞ (fctThetaD (vAlpha 1 τ₁)) := contDiff_fctThetaD hcd_a1 hcs_a1
  have hsp' : fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁) =
      (fctThetaD (v0 StripKernelChoice.star K4 τ₁) + fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) +
      fun s => α * fctThetaD (vAlpha 1 τ₁) s := by
    ext s; rw [vTotal_thetaD_eq_zero_add_smul hK4 hc0 hτD α s, h0_eq s]; rfl
  have hle_top : ((r : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hcd0 : ContDiffAt ℝ r (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t :=
    (contDiff_fctThetaD hcd_v0 hcs_v0).contDiffAt.of_le hle_top
  have hcd1 : ContDiffAt ℝ r (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) t :=
    (contDiff_fctThetaD hcd_v1 hcs_v1).contDiffAt.of_le hle_top
  have hcd01 : ContDiffAt ℝ r (fctThetaD (v0 StripKernelChoice.star K4 τ₁) + fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) t :=
    hcd0.add hcd1
  have hcda : ContDiffAt ℝ r (fun s => α * fctThetaD (vAlpha 1 τ₁) s) t :=
    (contDiff_const.mul hth_a1_cd).contDiffAt.of_le hle_top
  rw [hsp', iteratedDeriv_add hcd01 hcda, iteratedDeriv_add hcd0 hcd1, iteratedDeriv_const_mul_field]
  have s0 : |iteratedDeriv r (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t| ≤
      C_tail r * (CL0b + CL0m) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by
    refine (ht0.trans (mul_le_of_le_one_right (by have := hCt r; have := hCL.1; have := hCL.2.1; positivity) hexp1)).trans ?_
    have hK_le : (CL0b + K4 * CL0m) * τ₁ ^ 3 ≤ (CL0b + CL0m) * τ₁ := by
      have hτ31 : τ₁ ^ 3 ≤ τ₁ :=
        calc τ₁ ^ 3 = τ₁ * τ₁ ^ 2 := by ring
          _ ≤ τ₁ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hτ₁.le hτ₁_le1) hτ₁.le
          _ = τ₁ := mul_one _
      calc (CL0b + K4 * CL0m) * τ₁ ^ 3 = CL0b * τ₁ ^ 3 + CL0m * (K4 * τ₁ ^ 2) * τ₁ := by ring
        _ ≤ CL0b * τ₁ + CL0m * 1 * τ₁ := add_le_add (mul_le_mul_of_nonneg_left hτ31 hCL.1)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK4τ hCL.2.1) hτ₁.le)
        _ = (CL0b + CL0m) * τ₁ := by ring
    calc C_tail r * (CL0b + K4 * CL0m) * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ)))
        = C_tail r * ((CL0b + K4 * CL0m) * τ₁ ^ 3) * |t| ^ (-(1 + (r : ℤ))) := by ring
      _ ≤ C_tail r * ((CL0b + CL0m) * τ₁) * |t| ^ (-(1 + (r : ℤ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_le (hCt r)) hfac_nn
      _ = C_tail r * (CL0b + CL0m) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by ring
  have s1 : |iteratedDeriv r (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) t| ≤
      C_tail r * (CL1b + CL1m) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by
    refine (ht1.trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (mul_nonneg (hCt r)
      (add_nonneg hCL.2.2.2.1 (mul_nonneg (by linarith only [hK4]) hCL.2.2.2.2)))
      (inv_nonneg.mpr hc0.le)) hfac_nn) hexp1)).trans ?_
    have hK_le : (CL1b + K4 * CL1m) * c⁻¹ ≤ (CL1b + CL1m) * τ₁ := by
      rw [hcinv]
      have hτ41 : τ₁ ^ 4 ≤ τ₁ :=
        calc τ₁ ^ 4 = τ₁ * τ₁ ^ 3 := by ring
          _ ≤ τ₁ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hτ₁.le hτ₁_le1) hτ₁.le
          _ = τ₁ := mul_one _
      have hτ21 : τ₁ ^ 2 ≤ τ₁ :=
        calc τ₁ ^ 2 = τ₁ * τ₁ := by ring
          _ ≤ τ₁ * 1 := mul_le_mul_of_nonneg_left hτ₁_le1 hτ₁.le
          _ = τ₁ := mul_one _
      calc (CL1b + K4 * CL1m) * τ₁ ^ 4 = CL1b * τ₁ ^ 4 + CL1m * (K4 * τ₁ ^ 2) * τ₁ ^ 2 := by ring
        _ ≤ CL1b * τ₁ + CL1m * 1 * τ₁ := add_le_add (mul_le_mul_of_nonneg_left hτ41 hCL.2.2.2.1)
            (mul_le_mul (mul_le_mul_of_nonneg_left hK4τ hCL.2.2.2.2) hτ21 (sq_nonneg τ₁)
              (mul_nonneg hCL.2.2.2.2 zero_le_one))
        _ = (CL1b + CL1m) * τ₁ := by ring
    calc C_tail r * (CL1b + K4 * CL1m) * c⁻¹ * |t| ^ (-(1 + (r : ℤ)))
        = C_tail r * ((CL1b + K4 * CL1m) * c⁻¹) * |t| ^ (-(1 + (r : ℤ))) := by ring
      _ ≤ C_tail r * ((CL1b + CL1m) * τ₁) * |t| ^ (-(1 + (r : ℤ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_le (hCt r)) hfac_nn
      _ = C_tail r * (CL1b + CL1m) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by ring
  have sa : |α| * |iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤
      C_tail r * (2 * CLa) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by
    refine (mul_le_mul_of_nonneg_left (hta.trans (mul_le_of_le_one_right
      (mul_nonneg (mul_nonneg (mul_nonneg (hCt r) hCL.2.2.1) (pow_nonneg hτ₁.le 3)) hfac_nn) hexp1))
      (abs_nonneg α)).trans ?_
    have hατ : |α| * τ₁ ^ 3 ≤ 2 * τ₁ := by
      have hτ4_le : τ₁ ^ 4 ≤ 1 := pow_le_one₀ hτ₁.le hτ₁_le1
      calc |α| * τ₁ ^ 3 ≤ (2 * τ₁ ^ 2) * τ₁ ^ 3 := mul_le_mul_of_nonneg_right hα (pow_nonneg hτ₁.le 3)
        _ = 2 * τ₁ ^ 4 * τ₁ := by ring
        _ ≤ 2 * 1 * τ₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ4_le zero_le_two) hτ₁.le
        _ = 2 * τ₁ := by ring
    calc |α| * (C_tail r * CLa * τ₁ ^ 3 * |t| ^ (-(1 + (r : ℤ))))
        = C_tail r * CLa * (|α| * τ₁ ^ 3) * |t| ^ (-(1 + (r : ℤ))) := by ring
      _ ≤ C_tail r * CLa * (2 * τ₁) * |t| ^ (-(1 + (r : ℤ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hατ (mul_nonneg (hCt r) hCL.2.2.1)) hfac_nn
      _ = C_tail r * (2 * CLa) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by ring
  have a1 := abs_add_le (iteratedDeriv r (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t +
    iteratedDeriv r (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) t) (α * iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t)
  have a2 := abs_add_le (iteratedDeriv r (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t)
    (iteratedDeriv r (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) t)
  rw [abs_mul] at a1
  have hsum : C_tail r * (CL0b + CL0m) * τ₁ * |t| ^ (-(1 + (r : ℤ))) +
      C_tail r * (CL1b + CL1m) * τ₁ * |t| ^ (-(1 + (r : ℤ))) +
      C_tail r * (2 * CLa) * τ₁ * |t| ^ (-(1 + (r : ℤ))) =
      (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)) * τ₁ * |t| ^ (-(1 + (r : ℤ))) := by ring
  linarith only [a1, a2, s0, s1, sa, hsum]

private lemma fctThetaD_all_helper {K4 c α : ℝ} {Cth0b Cth0m Ctha Cth1b Cth1m C_tail : ℕ → ℝ}
    {CL0b CL0m CLa CL1b CL1m : ℝ}
    (hK4 : 1 ≤ K4) (hc0 : 0 < c)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hτ₁_le1 : c ^ (-(1 / 4 : ℝ)) ≤ 1)
    (hK4τ : K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1) (hα : |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2)
    (hCth : ∀ r, 0 ≤ Cth0b r ∧ 0 ≤ Cth0m r ∧ 0 ≤ Ctha r ∧ 0 ≤ Cth1b r ∧ 0 ≤ Cth1m r)
    (hCL : 0 ≤ CL0b ∧ 0 ≤ CL0m ∧ 0 ≤ CLa ∧ 0 ≤ CL1b ∧ 0 ≤ CL1m) (hCt : ∀ r, 0 ≤ C_tail r)
    (hcd_b0 : ContDiff ℝ ∞ (v0Base StripKernelChoice.star (c ^ (-(1 / 4 : ℝ)))))
    (hcs_b0 : HasCompactSupport (v0Base StripKernelChoice.star (c ^ (-(1 / 4 : ℝ)))))
    (hcd_m0 : ContDiff ℝ ∞ (v0Marg (c ^ (-(1 / 4 : ℝ)))))
    (hcs_m0 : HasCompactSupport (v0Marg (c ^ (-(1 / 4 : ℝ)))))
    (hcd_b1 : ContDiff ℝ ∞ (v1Base StripKernelChoice.star c (c ^ (-(1 / 4 : ℝ)))))
    (hcs_b1 : HasCompactSupport (v1Base StripKernelChoice.star c (c ^ (-(1 / 4 : ℝ)))))
    (hcd_m1 : ContDiff ℝ ∞ (v1Marg c (c ^ (-(1 / 4 : ℝ)))))
    (hcs_m1 : HasCompactSupport (v1Marg c (c ^ (-(1 / 4 : ℝ)))))
    (hcd_v0 : ContDiff ℝ ∞ (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_v0 : HasCompactSupport (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
    (hcd_v1 : ContDiff ℝ ∞ (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))))
    (hcs_v1 : HasCompactSupport (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))))
    (hcd_va0 : ContDiff ℝ ∞ (vAlpha 0 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_va0 : HasCompactSupport (vAlpha 0 (c ^ (-(1 / 4 : ℝ)))))
    (hcd_a1 : ContDiff ℝ ∞ (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))))
    (hcs_a1 : HasCompactSupport (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))))
    (hcd_tv0 : ContDiff ℝ ∞ (fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))))))
    (hth_in0 : ∀ r t, |t| ≤ 12 * c ^ (-(1 / 4 : ℝ)) →
      |iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star (c ^ (-(1 / 4 : ℝ))))) t| ≤
          Cth0b r * (c ^ (-(1 / 4 : ℝ))) ^ ((2 : ℤ) - r) * min 1 ((|t| / c ^ (-(1 / 4 : ℝ))) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v0Marg (c ^ (-(1 / 4 : ℝ))))) t| ≤
          Cth0m r * (c ^ (-(1 / 4 : ℝ))) ^ ((4 : ℤ) - r) * min 1 ((|t| / c ^ (-(1 / 4 : ℝ))) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c (c ^ (-(1 / 4 : ℝ))))) t| ≤
          Cth1b r * c⁻¹ * (c ^ (-(1 / 4 : ℝ))) ^ ((-1 : ℤ) - r) * min 1 ((|t| / c ^ (-(1 / 4 : ℝ))) ^ (11 - r)) ∧
      |iteratedDeriv r (fctThetaD (v1Marg c (c ^ (-(1 / 4 : ℝ))))) t| ≤
          Cth1m r * c⁻¹ * (c ^ (-(1 / 4 : ℝ))) ^ ((1 : ℤ) - r) * min 1 ((|t| / c ^ (-(1 / 4 : ℝ))) ^ (11 - r)))
    (hth_a1_in : ∀ r t, |t| ≤ 12 * c ^ (-(1 / 4 : ℝ)) →
      |iteratedDeriv r (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) t| ≤ Ctha r * (c ^ (-(1 / 4 : ℝ))) ^ ((2 : ℤ) - r))
    (hth_tail : ∀ r t, 12 * c ^ (-(1 / 4 : ℝ)) ≤ |t| →
      |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) t| ≤
        (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)) * c ^ (-(1 / 4 : ℝ)) * |t| ^ (-(1 + (r : ℤ)))) :
    ∀ r t, |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) t| ≤
      max (Cth0b r + Cth0m r + Cth1b r + Cth1m r + 2 * Ctha r)
        (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa) * (12 : ℝ) ^ (-(1 + (r : ℤ)))) *
        (c ^ (-(1 / 4 : ℝ))) ^ (-(r : ℤ)) := by
  intro r t
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    dsimp only [τ₁]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num [Real.rpow_neg_one]
    exact inv_mul_cancel₀ hc0.ne'
  have hK4_nn : 0 ≤ K4 := by linarith
  have hMtail_nn : 0 ≤ C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa) :=
    mul_nonneg (hCt r) (by linarith [hCL.1, hCL.2.1, hCL.2.2.1, hCL.2.2.2.1, hCL.2.2.2.2])
  rcases le_or_gt |t| (12 * τ₁) with hle | hgt
  · obtain ⟨hpow2, hzK4_0m, hz_1b, hzK4_1m⟩ := tau1_pow_le_helpers hτ₁ hτ₁_le1 hcτ hK4τ r
    have hth_a1_cd := contDiff_fctThetaD hcd_a1 hcs_a1
    have hsplit : fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁) =
        fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) + fun s => α * fctThetaD (vAlpha 1 τ₁) s :=
      funext (vTotal_thetaD_eq_zero_add_smul hK4 hc0 hτD α)
    rw [hsplit]
    have hle_top : ((r : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hcd0 : ContDiffAt ℝ r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) t := hcd_tv0.contDiffAt.of_le hle_top
    have hcda : ContDiffAt ℝ r (fun s => α * fctThetaD (vAlpha 1 τ₁) s) t := (contDiff_const.mul hth_a1_cd).contDiffAt.of_le hle_top
    rw [iteratedDeriv_add hcd0 hcda, iteratedDeriv_const_mul_field]
    have h0' : |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) t| ≤
        (Cth0b r + Cth0m r + Cth1b r + Cth1m r) * τ₁ ^ (-(r : ℤ)) := by
      obtain ⟨hb0, hm0, hb1, hm1⟩ := hth_in0 r t hle
      have hmin : min (1 : ℝ) ((|t| / τ₁) ^ (11 - r)) ≤ 1 := min_le_left _ _
      have hv0_th_eq : fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁) =
          (fctThetaD (v0Base StripKernelChoice.star τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) +
            (fctThetaD (v1Base StripKernelChoice.star c τ₁) + fun s => K4 * fctThetaD (v1Marg c τ₁) s) := by
        ext s
        have l1 := fctThetaD_zero_split hK4 hc0 hτD hcd_v0 hcs_v0 hcd_v1 hcs_v1 hcd_va0 hcs_va0 s
        have l2 := fctThetaD_linear hcd_b0 hcs_b0 hcd_m0 hcs_m0 1 K4 s
        have l3 := fctThetaD_linear hcd_b1 hcs_b1 hcd_m1 hcs_m1 1 K4 s
        simp only [one_mul] at l2 l3
        exact l1.trans (congrArg₂ (· + ·) l2 l3)
      rw [hv0_th_eq]
      have cb0 : ContDiffAt ℝ r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t :=
        (contDiff_fctThetaD hcd_b0 hcs_b0).contDiffAt.of_le hle_top
      have cm0 : ContDiffAt ℝ r (fun s => K4 * fctThetaD (v0Marg τ₁) s) t :=
        (contDiff_const.mul (contDiff_fctThetaD hcd_m0 hcs_m0)).contDiffAt.of_le hle_top
      have cb1 : ContDiffAt ℝ r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t :=
        (contDiff_fctThetaD hcd_b1 hcs_b1).contDiffAt.of_le hle_top
      have cm1 : ContDiffAt ℝ r (fun s => K4 * fctThetaD (v1Marg c τ₁) s) t :=
        (contDiff_const.mul (contDiff_fctThetaD hcd_m1 hcs_m1)).contDiffAt.of_le hle_top
      have c0 : ContDiffAt ℝ r (fctThetaD (v0Base StripKernelChoice.star τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t :=
        cb0.add cm0
      have c1 : ContDiffAt ℝ r (fctThetaD (v1Base StripKernelChoice.star c τ₁) + fun s => K4 * fctThetaD (v1Marg c τ₁) s) t :=
        cb1.add cm1
      rw [iteratedDeriv_add c0 c1, iteratedDeriv_add cb0 cm0,
        iteratedDeriv_add cb1 cm1, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
      have t1 := (hb0.trans (mul_le_of_le_one_right (mul_nonneg (hCth r).1 (zpow_nonneg hτ₁.le _)) hmin)).trans
        (mul_le_mul_of_nonneg_left hpow2 (hCth r).1)
      have t2 : K4 * |iteratedDeriv r (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m r * τ₁ ^ (-(r : ℤ)) :=
        (mul_le_mul_of_nonneg_left (hm0.trans (mul_le_of_le_one_right (mul_nonneg (hCth r).2.1
          (zpow_nonneg hτ₁.le _)) hmin)) hK4_nn).trans (by
            calc K4 * (Cth0m r * τ₁ ^ ((4 : ℤ) - r)) = Cth0m r * (K4 * τ₁ ^ ((4 : ℤ) - r)) := by ring
              _ ≤ Cth0m r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hzK4_0m (hCth r).2.1)
      have t4 : |iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t| ≤ Cth1b r * τ₁ ^ (-(r : ℤ)) :=
        (hb1.trans (mul_le_of_le_one_right (by have := (hCth r).2.2.2.1; positivity) hmin)).trans (by
          calc Cth1b r * c⁻¹ * τ₁ ^ ((-1 : ℤ) - r) = Cth1b r * (c⁻¹ * τ₁ ^ ((-1 : ℤ) - r)) := by ring
            _ ≤ Cth1b r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hz_1b (hCth r).2.2.2.1)
      have t5 : K4 * |iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t| ≤ Cth1m r * τ₁ ^ (-(r : ℤ)) :=
        (mul_le_mul_of_nonneg_left (hm1.trans (mul_le_of_le_one_right
          (by have := (hCth r).2.2.2.2; positivity) hmin)) hK4_nn).trans (by
            calc K4 * (Cth1m r * c⁻¹ * τ₁ ^ ((1 : ℤ) - r)) = Cth1m r * (K4 * (c⁻¹ * τ₁ ^ ((1 : ℤ) - r))) := by ring
              _ ≤ Cth1m r * τ₁ ^ (-(r : ℤ)) := mul_le_mul_of_nonneg_left hzK4_1m (hCth r).2.2.2.2)
      have a1 := abs_add_le (iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t + K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) t)
        (iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t + K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t)
      have a2 := abs_add_le (iteratedDeriv r (fctThetaD (v0Base StripKernelChoice.star τ₁)) t) (K4 * iteratedDeriv r (fctThetaD (v0Marg τ₁)) t)
      have a3 := abs_add_le (iteratedDeriv r (fctThetaD (v1Base StripKernelChoice.star c τ₁)) t) (K4 * iteratedDeriv r (fctThetaD (v1Marg c τ₁)) t)
      rw [abs_mul, abs_of_nonneg hK4_nn] at a2 a3
      have hsum : Cth0b r * τ₁ ^ (-(r : ℤ)) + Cth0m r * τ₁ ^ (-(r : ℤ)) + Cth1b r * τ₁ ^ (-(r : ℤ)) +
          Cth1m r * τ₁ ^ (-(r : ℤ)) = (Cth0b r + Cth0m r + Cth1b r + Cth1m r) * τ₁ ^ (-(r : ℤ)) := by ring
      linarith only [a1, a2, a3, t1, t2, t4, t5, hsum]
    have hta := hth_a1_in r t hle
    have ha2 : |α| * τ₁ ^ ((2 : ℤ) - r) ≤ 2 * τ₁ ^ (-(r : ℤ)) :=
      calc |α| * τ₁ ^ ((2 : ℤ) - r) ≤ (2 * τ₁ ^ 2) * τ₁ ^ ((2 : ℤ) - r) := mul_le_mul_of_nonneg_right hα (zpow_nonneg hτ₁.le _)
        _ ≤ (2 * 1) * τ₁ ^ (-(r : ℤ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_one₀ hτ₁.le hτ₁_le1) zero_le_two)
              hpow2 (zpow_nonneg hτ₁.le _) (by norm_num : (0 : ℝ) ≤ 2 * 1)
        _ = 2 * τ₁ ^ (-(r : ℤ)) := by ring
    have ha' : |α| * |iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤ 2 * Ctha r * τ₁ ^ (-(r : ℤ)) :=
      (mul_le_mul_of_nonneg_left hta (abs_nonneg α)).trans (by
        calc |α| * (Ctha r * τ₁ ^ ((2 : ℤ) - r)) = Ctha r * (|α| * τ₁ ^ ((2 : ℤ) - r)) := by ring
          _ ≤ Ctha r * (2 * τ₁ ^ (-(r : ℤ))) := mul_le_mul_of_nonneg_left ha2 (hCth r).2.2.1
          _ = 2 * Ctha r * τ₁ ^ (-(r : ℤ)) := by ring)
    have htri := abs_add_le (iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) t)
      (α * iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t)
    rw [abs_mul] at htri
    have hsum : (Cth0b r + Cth0m r + Cth1b r + Cth1m r) * τ₁ ^ (-(r : ℤ)) + 2 * Ctha r * τ₁ ^ (-(r : ℤ)) =
        (Cth0b r + Cth0m r + Cth1b r + Cth1m r + 2 * Ctha r) * τ₁ ^ (-(r : ℤ)) := by ring
    have hle' : |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c 0 τ₁)) t +
        α * iteratedDeriv r (fctThetaD (vAlpha 1 τ₁)) t| ≤
        (Cth0b r + Cth0m r + Cth1b r + Cth1m r + 2 * Ctha r) * τ₁ ^ (-(r : ℤ)) := by linarith only [htri, h0', ha', hsum]
    exact hle'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg hτ₁.le _))
  · have htl := hth_tail r t hgt.le
    have hpow : |t| ^ (-(1 + (r : ℤ))) ≤ (12 * τ₁) ^ (-(1 + (r : ℤ))) := by
      rw [zpow_neg, zpow_neg]; refine inv_anti₀ (by positivity) ?_
      rw [show (1 + (r : ℤ)) = ((1 + r : ℕ) : ℤ) by omega, zpow_natCast, zpow_natCast]
      exact pow_le_pow_left₀ (by positivity) hgt.le (1 + r)
    have hsp : (12 * τ₁) ^ (-(1 + (r : ℤ))) = (12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ))) := mul_zpow 12 τ₁ _
    have hmul_t : τ₁ * τ₁ ^ (-(1 + (r : ℤ))) = τ₁ ^ (-(r : ℤ)) := by
      rw [mul_comm, ← zpow_add_one₀ hτ₁.ne']; congr 1; ring
    refine htl.trans ?_
    calc (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)) * τ₁ * |t| ^ (-(1 + (r : ℤ)))
        ≤ (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)) * τ₁ * ((12 : ℝ) ^ (-(1 + (r : ℤ))) * τ₁ ^ (-(1 + (r : ℤ)))) := by
          rw [← hsp]; exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hMtail_nn hτ₁.le)
      _ = (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa) * (12 : ℝ) ^ (-(1 + (r : ℤ)))) * τ₁ ^ (-(r : ℤ)) := by
          rw [mul_assoc _ τ₁, mul_assoc (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)),
            mul_left_comm τ₁ ((12 : ℝ) ^ (-(1 + (r : ℤ)))), hmul_t]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg hτ₁.le _)

private lemma alpha1_zero_helper {τ₁ τ Cva0 Ctha0 C_tail0 CLa : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₁_le1 : τ₁ ≤ 1) (hτ_pos : 0 < τ)
    (hCva0 : 0 ≤ Cva0) (hCtha0 : 0 ≤ Ctha0) (hCt0 : 0 ≤ C_tail0) (hCLa : 0 ≤ CLa)
    (hv : |vAlpha 1 τ₁ τ| ≤ Cva0 * τ₁ ^ ((2 : ℤ) - 0))
    (hin : |τ| ≤ 12 * τ₁ → |fctThetaD (vAlpha 1 τ₁) τ| ≤ Ctha0 * τ₁ ^ ((2 : ℤ) - 0))
    (htl : 12 * τ₁ ≤ |τ| → |fctThetaD (vAlpha 1 τ₁) τ| ≤ C_tail0 * CLa * τ₁ ^ 3 * |τ| ^ (-(1 + (0 : ℤ))) * Real.exp (-(π / 2) * |τ|)) :
    |vAlpha 1 τ₁ τ| + |fctThetaD (vAlpha 1 τ₁) τ| ≤ (Cva0 + Ctha0) + (Cva0 + C_tail0 * CLa * (12 : ℝ) ^ (-1 : ℤ)) := by
  have h1 : |vAlpha 1 τ₁ τ| ≤ Cva0 := by
    simp only [sub_zero, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast] at hv
    exact hv.trans (mul_le_of_le_one_right hCva0 (pow_le_one₀ hτ₁.le hτ₁_le1))
  have h2 : |fctThetaD (vAlpha 1 τ₁) τ| ≤ Ctha0 + C_tail0 * CLa * (12 : ℝ) ^ (-1 : ℤ) := by
    rcases le_or_gt τ (12 * τ₁) with hle | hgt
    · have h1' := hin (by rwa [abs_of_pos hτ_pos])
      simp only [sub_zero, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast] at h1'
      have h1'' := h1'.trans (mul_le_of_le_one_right hCtha0 (pow_le_one₀ hτ₁.le hτ₁_le1))
      linarith only [h1'', show (0 : ℝ) ≤ C_tail0 * CLa * (12 : ℝ) ^ (-1 : ℤ) by positivity]
    · have h1' := htl (by rw [abs_of_pos hτ_pos]; exact hgt.le)
      simp only [add_zero] at h1'
      have hexp1 : Real.exp (-(π / 2) * |τ|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (abs_nonneg _))
      have hpow : |τ| ^ (-1 : ℤ) ≤ (12 * τ₁) ^ (-1 : ℤ) := by
        rw [zpow_neg_one, zpow_neg_one]; exact inv_anti₀ (by positivity) (by rw [abs_of_pos hτ_pos]; exact hgt.le)
      have hm := h1'.trans (mul_le_of_le_one_right (by positivity) hexp1)
      rw [mul_zpow] at hpow
      have h1'' : C_tail0 * CLa * τ₁ ^ 3 * |τ| ^ (-1 : ℤ) ≤ C_tail0 * CLa * (12 : ℝ) ^ (-1 : ℤ) :=
        calc C_tail0 * CLa * τ₁ ^ 3 * |τ| ^ (-1 : ℤ)
            ≤ C_tail0 * CLa * (τ₁ ^ 3 * ((12 : ℝ) ^ (-1 : ℤ) * τ₁ ^ (-1 : ℤ))) := by
              rw [mul_assoc (C_tail0 * CLa)]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (pow_nonneg hτ₁.le 3)) (mul_nonneg hCt0 hCLa)
          _ = C_tail0 * CLa * (12 : ℝ) ^ (-1 : ℤ) * τ₁ ^ 2 := by
              rw [zpow_neg_one τ₁, zpow_neg_one (12 : ℝ)]; field_simp [hτ₁.ne']
          _ ≤ C_tail0 * CLa * (12 : ℝ) ^ (-1 : ℤ) :=
              mul_le_of_le_one_right (by positivity) (pow_le_one₀ hτ₁.le hτ₁_le1)
      linarith only [hm.trans h1'', hCtha0]
  linarith only [h1, h2, hCva0]

private lemma alpha1_k_edge_helper {τ₁ τ : ℝ} {Cva Ctha : ℝ} {C_tailk CLa : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₁_le1 : τ₁ ≤ 1) (hτ_pos : 0 < τ)
    (hCva : 0 ≤ Cva) (hCtha : 0 ≤ Ctha) (hCtk : 0 ≤ C_tailk) (hCLa : 0 ≤ CLa)
    (k : ℕ)
    (hv : |iteratedDeriv k (vAlpha 1 τ₁) τ| ≤ Cva * τ₁ ^ ((2 : ℤ) - k))
    (hin : |τ| ≤ 12 * τ₁ → |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ| ≤ Ctha * τ₁ ^ ((2 : ℤ) - k))
    (htl : 12 * τ₁ ≤ |τ| → |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ| ≤
      C_tailk * CLa * τ₁ ^ 3 * |τ| ^ (-(1 + (k : ℤ))) * Real.exp (-(π / 2) * |τ|))
    (hsp : ∀ t, 10 * τ₁ ≤ |t| → vAlpha 1 τ₁ t = 0) :
    |iteratedDeriv k (vAlpha 1 τ₁) τ| + |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ| ≤
      max ((Cva + Ctha) * 12 ^ k) (Cva + C_tailk * CLa * (12 : ℝ) ^ (-1 : ℤ)) * edgeW τ ^ (-(k : ℤ)) := by
  have hτ_ne := hτ_pos.ne'
  rcases le_or_gt τ (12 * τ₁) with hle | hgt
  · have hth1_bd := hin (by rwa [abs_of_pos hτ_pos])
    have hpow2 : τ₁ ^ ((2 : ℤ) - k) ≤ τ₁ ^ (-(k : ℤ)) := by
      rw [show ((2 : ℤ) - k) = (2 : ℤ) + (-(k : ℤ)) by ring, zpow_add₀ hτ₁.ne',
        show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      exact mul_le_of_le_one_left (zpow_nonneg hτ₁.le _) (pow_le_one₀ hτ₁.le hτ₁_le1)
    calc |iteratedDeriv k (vAlpha 1 τ₁) τ| + |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ|
        ≤ (Cva + Ctha) * τ₁ ^ ((2 : ℤ) - k) := by linarith only [hv, hth1_bd]
      _ ≤ (Cva + Ctha) * ((12 : ℝ) ^ k * edgeW τ ^ (-(k : ℤ))) :=
          mul_le_mul_of_nonneg_left (hpow2.trans (tau1_to_edgeW_le hτ₁ hτ_pos hle k)) (add_nonneg hCva hCtha)
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg (edgeW_pos hτ_ne).le _)
  · have hva_zero : vAlpha 1 τ₁ =ᶠ[𝓝 τ] 0 :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds (by linarith : 10 * τ₁ < τ)) fun s hs =>
        hsp s (by rw [abs_of_pos (lt_trans (by positivity) (mem_Ioi.mp hs))]; linarith [mem_Ioi.mp hs])
    rw [hva_zero.iteratedDeriv_eq k, iteratedDeriv_const_zero, abs_zero, zero_add]
    have hta := htl (by rw [abs_of_pos hτ_pos]; exact hgt.le)
    have hexp1 : Real.exp (-(π / 2) * |τ|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (abs_nonneg _))
    have hta' := hta.trans (mul_le_of_le_one_right (by positivity) hexp1)
    rw [abs_of_pos hτ_pos] at hta'
    have hsp_z : τ ^ (-(1 + (k : ℤ))) = τ ^ (-1 : ℤ) * τ ^ (-(k : ℤ)) := by
      rw [show -(1 + (k : ℤ)) = (-1 : ℤ) + (-(k : ℤ)) by ring, zpow_add₀ hτ_ne]
    have hτ1 : τ ^ (-1 : ℤ) ≤ (12 * τ₁) ^ (-1 : ℤ) := by
      rw [zpow_neg_one, zpow_neg_one]; exact inv_anti₀ (by positivity) hgt.le
    have h12sp : (12 * τ₁) ^ (-1 : ℤ) = (12 : ℝ) ^ (-1 : ℤ) * τ₁ ^ (-1 : ℤ) := mul_zpow 12 τ₁ (-1)
    have hτk_ew : τ ^ (-(k : ℤ)) ≤ edgeW τ ^ (-(k : ℤ)) := by
      have := abs_inv_le_edgeW_inv hτ_ne k; rwa [abs_of_pos hτ_pos] at this
    have hτ31 : τ₁ ^ 3 * τ₁ ^ (-1 : ℤ) ≤ 1 := by
      rw [zpow_neg_one, show τ₁ ^ 3 * τ₁⁻¹ = τ₁ ^ 2 * (τ₁ * τ₁⁻¹) by ring, mul_inv_cancel₀ hτ₁.ne', mul_one]
      exact pow_le_one₀ hτ₁.le hτ₁_le1
    calc |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ|
        ≤ C_tailk * CLa * τ₁ ^ 3 * (τ ^ (-1 : ℤ) * τ ^ (-(k : ℤ))) := by rw [← hsp_z]; exact hta'
      _ ≤ C_tailk * CLa * (τ₁ ^ 3 * ((12 : ℝ) ^ (-1 : ℤ) * τ₁ ^ (-1 : ℤ))) * edgeW τ ^ (-(k : ℤ)) := by
          rw [show C_tailk * CLa * τ₁ ^ 3 * (τ ^ (-1 : ℤ) * τ ^ (-(k : ℤ))) =
              C_tailk * CLa * (τ₁ ^ 3 * τ ^ (-1 : ℤ)) * τ ^ (-(k : ℤ)) by ring]
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h12sp ▸ hτ1) (pow_nonneg hτ₁.le 3))
            (mul_nonneg hCtk hCLa)) hτk_ew (zpow_nonneg hτ_pos.le _) (by positivity)
      _ ≤ C_tailk * CLa * (12 : ℝ) ^ (-1 : ℤ) * edgeW τ ^ (-(k : ℤ)) := by
          rw [show τ₁ ^ 3 * ((12 : ℝ) ^ (-1 : ℤ) * τ₁ ^ (-1 : ℤ)) = (12 : ℝ) ^ (-1 : ℤ) * (τ₁ ^ 3 * τ₁ ^ (-1 : ℤ)) by ring]
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_right (by positivity) hτ31) (mul_nonneg hCtk hCLa))
            (zpow_nonneg (edgeW_pos hτ_ne).le _)
      _ ≤ (Cva + C_tailk * CLa * (12 : ℝ) ^ (-1 : ℤ)) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCva]) (zpow_nonneg (edgeW_pos hτ_ne).le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg (edgeW_pos hτ_ne).le _)

private lemma fctThetaD_cinv_edge_helper {K4 c α τ₁ τ : ℝ} {Mth_k Mth_tail : ℝ}
    (hc0 : 0 < c) (hτ₁ : 0 < τ₁) (hτ_pos : 0 < τ) (hcτ : τ₁ ^ 4 * c = 1)
    (hτ₁2 : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ))) (hMk : 0 ≤ Mth_k) (hMt : 0 ≤ Mth_tail)
    {k : ℕ} (_hk1 : 1 ≤ k)
    (hth_bd : |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ Mth_k * τ₁ ^ (-(k : ℤ)))
    (hth_tl : 12 * τ₁ ≤ |τ| →
      |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ Mth_tail * τ₁ * |τ| ^ (-(1 + (k : ℤ)))) :
    c⁻¹ * |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤
      max (Mth_k * (12 : ℝ) ^ (k - 1)) (Mth_tail / 144) * τ₁ * c ^ (-(1 / 2 : ℝ)) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)) := by
  have hτ_ne := hτ_pos.ne'
  have hcinv : c⁻¹ = τ₁ ^ 4 := inv_eq_of_mul_eq_one_right (by rwa [mul_comm])
  rcases le_or_gt τ (12 * τ₁) with hle | hgt
  · have hpow := tau1_to_edgeW_le hτ₁ hτ_pos hle (k - 1)
    have hzk : τ₁ * τ₁ ^ (-(k : ℤ)) = τ₁ ^ (-((k - 1 : ℕ) : ℤ)) := by
      rw [mul_comm, ← zpow_add_one₀ hτ₁.ne' (-(k : ℤ))]; congr 1; omega
    have hcinv_pow : c⁻¹ * τ₁ ^ (-(k : ℤ)) = τ₁ * c ^ (-(1 / 2 : ℝ)) * τ₁ ^ (-((k - 1 : ℕ) : ℤ)) :=
      calc c⁻¹ * τ₁ ^ (-(k : ℤ)) = τ₁ ^ 4 * τ₁ ^ (-(k : ℤ)) := by rw [hcinv]
        _ = τ₁ * τ₁ ^ 2 * (τ₁ * τ₁ ^ (-(k : ℤ))) := by ring
        _ = τ₁ * c ^ (-(1 / 2 : ℝ)) * τ₁ ^ (-((k - 1 : ℕ) : ℤ)) := by rw [hτ₁2, hzk]
    calc c⁻¹ * |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ|
        ≤ c⁻¹ * (Mth_k * τ₁ ^ (-(k : ℤ))) := mul_le_mul_of_nonneg_left hth_bd (inv_nonneg.mpr hc0.le)
      _ = Mth_k * (τ₁ * c ^ (-(1 / 2 : ℝ)) * τ₁ ^ (-((k - 1 : ℕ) : ℤ))) := by rw [← hcinv_pow]; ring
      _ ≤ Mth_k * (τ₁ * c ^ (-(1 / 2 : ℝ)) * ((12 : ℝ) ^ (k - 1) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)))) := by gcongr
      _ = (Mth_k * (12 : ℝ) ^ (k - 1)) * τ₁ * c ^ (-(1 / 2 : ℝ)) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)) := by ring
      _ ≤ _ := by gcongr; exact zpow_nonneg (edgeW_pos hτ_ne).le _; exact le_max_left _ _
  · have htl := hth_tl (by rw [abs_of_pos hτ_pos]; exact hgt.le)
    rw [abs_of_pos hτ_pos] at htl
    have hsp : τ ^ (-(1 + (k : ℤ))) = τ ^ (-2 : ℤ) * τ ^ (-((k - 1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hτ_ne]; congr 1; omega
    have hτ2_le : τ ^ (-2 : ℤ) ≤ (12 * τ₁) ^ (-2 : ℤ) := by
      rw [zpow_neg, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hgt.le 2)
    have h12sp : (12 * τ₁) ^ (-2 : ℤ) = (144 : ℝ)⁻¹ * τ₁ ^ (-2 : ℤ) := by
      rw [mul_zpow, show (12 : ℝ) ^ (-2 : ℤ) = (144 : ℝ)⁻¹ by norm_num]
    have hτ_ew : τ ^ (-((k - 1 : ℕ) : ℤ)) ≤ edgeW τ ^ (-((k - 1 : ℕ) : ℤ)) := by
      have := abs_inv_le_edgeW_inv hτ_ne (k - 1); rwa [abs_of_pos hτ_pos] at this
    have hpow_tot : c⁻¹ * τ₁ * τ₁ ^ (-2 : ℤ) = τ₁ * c ^ (-(1 / 2 : ℝ)) := by
      rw [hcinv, ← hτ₁2, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      have hτ2_ne : τ₁ ^ 2 ≠ 0 := pow_ne_zero 2 hτ₁.ne'
      calc τ₁ ^ 4 * τ₁ * (τ₁ ^ 2)⁻¹ = τ₁ * τ₁ ^ 2 * (τ₁ ^ 2 * (τ₁ ^ 2)⁻¹) := by ring
        _ = τ₁ * τ₁ ^ 2 := by rw [mul_inv_cancel₀ hτ2_ne, mul_one]
    calc c⁻¹ * |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ|
        ≤ c⁻¹ * (Mth_tail * τ₁ * (τ ^ (-2 : ℤ) * τ ^ (-((k - 1 : ℕ) : ℤ)))) := by
          rw [← hsp]; exact mul_le_mul_of_nonneg_left htl (inv_nonneg.mpr hc0.le)
      _ = Mth_tail * (c⁻¹ * τ₁ * τ ^ (-2 : ℤ)) * τ ^ (-((k - 1 : ℕ) : ℤ)) := by ring
      _ ≤ Mth_tail * (c⁻¹ * τ₁ * ((144 : ℝ)⁻¹ * τ₁ ^ (-2 : ℤ))) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (h12sp ▸ hτ2_le) (by positivity)) hMt) hτ_ew
            (zpow_nonneg hτ_pos.le _) (mul_nonneg hMt (by positivity))
      _ = (Mth_tail / 144) * (c⁻¹ * τ₁ * τ₁ ^ (-2 : ℤ)) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)) := by ring
      _ = (Mth_tail / 144) * τ₁ * c ^ (-(1 / 2 : ℝ)) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)) := by
          rw [hpow_tot, ← mul_assoc (Mth_tail / 144)]
      _ ≤ _ := by gcongr; exact zpow_nonneg (edgeW_pos hτ_ne).le _; exact le_max_right _ _

private lemma vTotal_k_edge_helper {K4 c α τ₁ τ Mv_k : ℝ} (hτ₁ : 0 < τ₁) (hτ_pos : 0 < τ) (hM : 0 ≤ Mv_k) (k : ℕ)
    (hv_bd : |iteratedDeriv k (vTotal StripKernelChoice.star K4 c α τ₁) τ| ≤ Mv_k * τ₁ ^ (-(k : ℤ)))
    (hsb0 : Function.support (v0Base StripKernelChoice.star τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁))
    (hsm0 : Function.support (v0Marg τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁))
    (hsb1 : Function.support (v1Base StripKernelChoice.star c τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁))
    (hsm1 : Function.support (v1Marg c τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁))
    (hva_sp : ∀ t, 10 * τ₁ ≤ |t| → vAlpha 1 τ₁ t = 0) :
    |iteratedDeriv k (vTotal StripKernelChoice.star K4 c α τ₁) τ| ≤ Mv_k * 12 ^ k * edgeW τ ^ (-(k : ℤ)) := by
  rcases le_or_gt τ (11 * τ₁) with hle | hgt
  · exact hv_bd.trans (by
      calc Mv_k * τ₁ ^ (-(k : ℤ)) ≤ Mv_k * ((12 : ℝ) ^ k * edgeW τ ^ (-(k : ℤ))) :=
            mul_le_mul_of_nonneg_left (tau1_to_edgeW_le hτ₁ hτ_pos (by linarith) k) hM
        _ = _ := by ring)
  · have hv_zero : vTotal StripKernelChoice.star K4 c α τ₁ =ᶠ[𝓝 τ] 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds (by linarith : 10 * τ₁ < τ)] with s hs
      have hs' := mem_Ioi.mp hs
      have hs_abs : 10 * τ₁ ≤ |s| := by rw [abs_of_pos (lt_trans (by positivity) hs')]; linarith
      have hns : ¬ s < 10 * τ₁ := not_lt_of_ge hs'.le
      have hb0 : v0Base StripKernelChoice.star τ₁ s = 0 := by by_contra hne; exact hns (hsb0 hne).2
      have hm0 : v0Marg τ₁ s = 0 := by by_contra hne; exact hns (hsm0 hne).2
      have hb1 : v1Base StripKernelChoice.star c τ₁ s = 0 := by by_contra hne; exact hns (hsb1 hne).2
      have hm1 : v1Marg c τ₁ s = 0 := by by_contra hne; exact hns (hsm1 hne).2
      have ha1 := hva_sp s hs_abs
      have haa : vAlpha α τ₁ s = 0 := by rw [vAlpha_eq_smul, ha1, mul_zero]
      unfold vTotal v0 v1; simp [hb0, hm0, hb1, hm1, haa]
    rw [hv_zero.iteratedDeriv_eq k, iteratedDeriv_const_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hM (by positivity)) (zpow_nonneg (edgeW_pos hτ_pos.ne').le _)

private lemma fctThetaD_k_edge_helper {K4 c α τ₁ τ Mth_k Mth_tail : ℝ}
    (hτ₁ : 0 < τ₁) (hτ_pos : 0 < τ) (hMk : 0 ≤ Mth_k) (hMt : 0 ≤ Mth_tail) (k : ℕ)
    (hth_bd : |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ Mth_k * τ₁ ^ (-(k : ℤ)))
    (hth_tl : 12 * τ₁ ≤ |τ| →
      |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ Mth_tail * τ₁ * |τ| ^ (-(1 + (k : ℤ)))) :
    |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤
      max (Mth_k * 12 ^ k) (Mth_tail / 12) * edgeW τ ^ (-(k : ℤ)) := by
  have hτ_ne := hτ_pos.ne'
  rcases le_or_gt τ (12 * τ₁) with hle | hgt
  · exact hth_bd.trans (by
      calc Mth_k * τ₁ ^ (-(k : ℤ)) ≤ Mth_k * ((12 : ℝ) ^ k * edgeW τ ^ (-(k : ℤ))) :=
            mul_le_mul_of_nonneg_left (tau1_to_edgeW_le hτ₁ hτ_pos hle k) hMk
        _ = Mth_k * (12 : ℝ) ^ k * edgeW τ ^ (-(k : ℤ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (zpow_nonneg (edgeW_pos hτ_ne).le _))
  · have htl := hth_tl (by rw [abs_of_pos hτ_pos]; exact hgt.le)
    rw [abs_of_pos hτ_pos] at htl
    have hsp : τ ^ (-(1 + (k : ℤ))) = τ⁻¹ * τ ^ (-(k : ℤ)) := by
      rw [show (-(1 + (k : ℤ))) = (-1 : ℤ) + (-(k : ℤ)) by ring, zpow_add₀ hτ_ne, zpow_neg_one]
    have hτ_12 : τ₁ * τ⁻¹ ≤ 1 / 12 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hτ_pos (by norm_num)]; linarith
    have hτk_ew : τ ^ (-(k : ℤ)) ≤ edgeW τ ^ (-(k : ℤ)) := by
      have := abs_inv_le_edgeW_inv hτ_ne k; rwa [abs_of_pos hτ_pos] at this
    refine htl.trans ?_
    calc Mth_tail * τ₁ * τ ^ (-(1 + (k : ℤ))) = Mth_tail * (τ₁ * τ⁻¹) * τ ^ (-(k : ℤ)) := by rw [hsp]; ring
      _ ≤ Mth_tail * (1 / 12) * edgeW τ ^ (-(k : ℤ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hτ_12 hMt) hτk_ew
            (zpow_nonneg hτ_pos.le _) (mul_nonneg hMt (by norm_num))
      _ ≤ _ := by rw [show Mth_tail * (1 / 12) = Mth_tail / 12 by ring]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (zpow_nonneg (edgeW_pos hτ_ne).le _)

private lemma vTotal_pointwise_sub {n : ℕ} {K4 c α : ℝ} {Mv_k Mth_k Mth_tail Cva Ctha C_tail : ℕ → ℝ} {CLa : ℝ}
    (hc0 : 0 < c) (hτ₁ : 0 < c ^ (-(1 / 4 : ℝ))) (hτ₁_le1 : c ^ (-(1 / 4 : ℝ)) ≤ 1)
    (hcτ : (c ^ (-(1 / 4 : ℝ))) ^ 4 * c = 1) (hτ₁2 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)))
    (hMv_nn : ∀ r, 0 ≤ Mv_k r) (hMth_nn : ∀ r, 0 ≤ Mth_k r) (hMtail_nn : ∀ r, 0 ≤ Mth_tail r)
    (hCva_nn : ∀ r, 0 ≤ Cva r) (hCtha_nn : ∀ r, 0 ≤ Ctha r) (hCt_nn : ∀ r, 0 ≤ C_tail r) (hCLa : 0 ≤ CLa)
    (hv_bd : ∀ r t, |iteratedDeriv r (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) t| ≤ Mv_k r * (c ^ (-(1 / 4 : ℝ))) ^ (-(r : ℤ)))
    (hth_bd : ∀ r t, |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) t| ≤ Mth_k r * (c ^ (-(1 / 4 : ℝ))) ^ (-(r : ℤ)))
    (hth_tl : ∀ r t, 12 * c ^ (-(1 / 4 : ℝ)) ≤ |t| →
      |iteratedDeriv r (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) t| ≤
        Mth_tail r * c ^ (-(1 / 4 : ℝ)) * |t| ^ (-(1 + (r : ℤ))))
    (hva_d : ∀ r t, |iteratedDeriv r (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) t| ≤ Cva r * (c ^ (-(1 / 4 : ℝ))) ^ ((2 : ℤ) - r))
    (htha_in : ∀ r t, |t| ≤ 12 * c ^ (-(1 / 4 : ℝ)) →
      |iteratedDeriv r (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) t| ≤ Ctha r * (c ^ (-(1 / 4 : ℝ))) ^ ((2 : ℤ) - r))
    (htha_tl : ∀ r t, 12 * c ^ (-(1 / 4 : ℝ)) ≤ |t| →
      |iteratedDeriv r (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) t| ≤
        C_tail r * CLa * (c ^ (-(1 / 4 : ℝ))) ^ 3 * |t| ^ (-(1 + (r : ℤ))) * Real.exp (-(π / 2) * |t|))
    (hva_sp : ∀ t, 10 * c ^ (-(1 / 4 : ℝ)) ≤ |t| → vAlpha 1 (c ^ (-(1 / 4 : ℝ))) t = 0)
    (hsb0 : Function.support (v0Base StripKernelChoice.star (c ^ (-(1 / 4 : ℝ)))) ⊆ Ioo (-10 * c ^ (-(1 / 4 : ℝ))) (10 * c ^ (-(1 / 4 : ℝ))))
    (hsm0 : Function.support (v0Marg (c ^ (-(1 / 4 : ℝ)))) ⊆ Ioo (-10 * c ^ (-(1 / 4 : ℝ))) (10 * c ^ (-(1 / 4 : ℝ))))
    (hsb1 : Function.support (v1Base StripKernelChoice.star c (c ^ (-(1 / 4 : ℝ)))) ⊆ Ioo (-10 * c ^ (-(1 / 4 : ℝ))) (10 * c ^ (-(1 / 4 : ℝ))))
    (hsm1 : Function.support (v1Marg c (c ^ (-(1 / 4 : ℝ)))) ⊆ Ioo (-10 * c ^ (-(1 / 4 : ℝ))) (10 * c ^ (-(1 / 4 : ℝ)))) :
    ∀ τ : ℝ, 1.85 * c ^ (-(1 / 4 : ℝ)) < τ →
      |vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) τ| +
          |fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ| ≤ Mv_k 0 + Mth_k 0 ∧
      |vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ| + |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ| ≤
        (Cva 0 + Ctha 0) + (Cva 0 + C_tail 0 * CLa * (12 : ℝ) ^ (-1 : ℤ)) ∧
      (∀ k ≤ n,
        |iteratedDeriv k (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) τ| ≤ Mv_k k * 12 ^ k * edgeW τ ^ (-(k : ℤ)) ∧
        |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) τ| ≤
          max (Mth_k k * 12 ^ k) (Mth_tail k / 12) * edgeW τ ^ (-(k : ℤ)) ∧
        |iteratedDeriv k (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ| + |iteratedDeriv k (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) τ| ≤
          max ((Cva k + Ctha k) * 12 ^ k) (Cva k + C_tail k * CLa * (12 : ℝ) ^ (-1 : ℤ)) * edgeW τ ^ (-(k : ℤ))) ∧
      (∀ k, 1 ≤ k → k ≤ n + 1 →
        c⁻¹ * |iteratedDeriv k (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) τ| ≤
          max (Mth_k k * (12 : ℝ) ^ (k - 1)) (Mth_tail k / 144) * c ^ (-(1 / 4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) *
            edgeW τ ^ (-((k - 1 : ℕ) : ℤ))) := by
  intro τ hτr
  have hτ_pos : 0 < τ := lt_trans (by positivity) hτr
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := hv_bd 0 τ; have h2 := hth_bd 0 τ
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at h1 h2
    exact add_le_add h1 h2
  · exact alpha1_zero_helper hτ₁ hτ₁_le1 hτ_pos (hCva_nn 0) (hCtha_nn 0) (hCt_nn 0) hCLa
      (hva_d 0 τ) (htha_in 0 τ) (htha_tl 0 τ)
  · intro k _
    exact ⟨vTotal_k_edge_helper hτ₁ hτ_pos (hMv_nn k) k (hv_bd k τ) hsb0 hsm0 hsb1 hsm1 hva_sp,
      fctThetaD_k_edge_helper hτ₁ hτ_pos (hMth_nn k) (hMtail_nn k) k (hth_bd k τ) (hth_tl k τ),
      alpha1_k_edge_helper hτ₁ hτ₁_le1 hτ_pos (hCva_nn k) (hCtha_nn k) (hCt_nn k) hCLa k
        (hva_d k τ) (htha_in k τ) (htha_tl k τ) hva_sp⟩
  · intro k hk1 _
    exact fctThetaD_cinv_edge_helper (K4 := K4) (α := α) hc0 hτ₁ hτ_pos hcτ hτ₁2
      (hMth_nn k) (hMtail_nn k) hk1 (hth_bd k τ) (hth_tl k τ)

lemma vTotal_thetaD_edge_bounds (n : ℕ) :
    ∃ (B_v B_α : ℝ) (C_v C_th C_th_c C_α : ℕ → ℝ),
      0 ≤ B_v ∧ 0 ≤ B_α ∧ (∀ k, 0 ≤ C_v k) ∧ (∀ k, 0 ≤ C_th k) ∧ (∀ k, 0 ≤ C_th_c k) ∧ (∀ k, 0 ≤ C_α k) ∧
      ∀ {K4 c α : ℝ}, 1 ≤ K4 → 1 ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 → |α| ≤ 2 * (c ^ (-(1 / 4 : ℝ))) ^ 2 →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        let v := vTotal StripKernelChoice.star K4 c α τ₁
        ContDiff ℝ ∞ v ∧ ContDiff ℝ ∞ (fctThetaD v) ∧
        ContDiff ℝ ∞ (vAlpha 1 τ₁) ∧ ContDiff ℝ ∞ (fctThetaD (vAlpha 1 τ₁)) ∧
        (∀ τ : ℝ, 1.85 * τ₁ < τ →
          |v τ| + |fctThetaD v τ| ≤ B_v ∧
          |vAlpha 1 τ₁ τ| + |fctThetaD (vAlpha 1 τ₁) τ| ≤ B_α ∧
          (∀ k ≤ n,
            |iteratedDeriv k v τ| ≤ C_v k * edgeW τ ^ (-(k : ℤ)) ∧
            |iteratedDeriv k (fctThetaD v) τ| ≤ C_th k * edgeW τ ^ (-(k : ℤ)) ∧
            |iteratedDeriv k (vAlpha 1 τ₁) τ| + |iteratedDeriv k (fctThetaD (vAlpha 1 τ₁)) τ| ≤
              C_α k * edgeW τ ^ (-(k : ℤ))) ∧
          (∀ k, 1 ≤ k → k ≤ n + 1 →
            c⁻¹ * |iteratedDeriv k (fctThetaD v) τ| ≤
              C_th_c k * τ₁ * c ^ (-(1 / 2 : ℝ)) * edgeW τ ^ (-((k - 1 : ℕ) : ℤ)))) := by
  obtain ⟨_, _, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    CL0b, CL0m, CLa, CL1b, CL1m, C_tail, _, hCv_nn, hCth_nn, hCL_nn, hCtail_nn, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  let Mv_k : ℕ → ℝ := fun r => Cv0b r + Cv0m r + Cv1b r + Cv1m r + 2 * Cva r
  let Mth_k : ℕ → ℝ := fun r =>
    max (Cth0b r + Cth0m r + Cth1b r + Cth1m r + 2 * Ctha r)
      (C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa) * (12 : ℝ) ^ (-(1 + (r : ℤ))))
  let Mth_tail : ℕ → ℝ := fun r => C_tail r * (CL0b + CL0m + CL1b + CL1m + 2 * CLa)
  have hMv_nn : ∀ r, 0 ≤ Mv_k r := fun r => by
    have hv := hCv_nn r; dsimp only [Mv_k]
    linarith only [hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  have hMth_nn : ∀ r, 0 ≤ Mth_k r := fun r => by
    have hth := hCth_nn r; refine le_trans ?_ (le_max_left _ _)
    linarith only [hth.1, hth.2.1, hth.2.2.1, hth.2.2.2.1, hth.2.2.2.2]
  have hMtail_nn : ∀ r, 0 ≤ Mth_tail r := fun r => mul_nonneg (hCtail_nn r).1
    (by linarith only [hCL_nn.1, hCL_nn.2.1, hCL_nn.2.2.1, hCL_nn.2.2.2.1, hCL_nn.2.2.2.2])
  have hBa_nn : 0 ≤ (Cva 0 + Ctha 0) + (Cva 0 + C_tail 0 * CLa * (12 : ℝ) ^ (-1 : ℤ)) := by
    have h1 := (hCv_nn 0).2.2.1; have h2 := (hCth_nn 0).2.2.1
    have h3 := (hCtail_nn 0).1; have h4 := hCL_nn.2.2.1; positivity
  refine ⟨Mv_k 0 + Mth_k 0, (Cva 0 + Ctha 0) + (Cva 0 + C_tail 0 * CLa * (12 : ℝ) ^ (-1 : ℤ)),
    fun k => Mv_k k * 12 ^ k, fun k => max (Mth_k k * 12 ^ k) (Mth_tail k / 12),
    fun k => max (Mth_k k * (12 : ℝ) ^ (k - 1)) (Mth_tail k / 144),
    fun k => max ((Cva k + Ctha k) * 12 ^ k) (Cva k + C_tail k * CLa * (12 : ℝ) ^ (-1 : ℤ)),
    add_nonneg (hMv_nn 0) (hMth_nn 0), hBa_nn,
    fun k => mul_nonneg (hMv_nn k) (by positivity),
    fun k => le_trans (mul_nonneg (hMth_nn k) (by positivity)) (le_max_left _ _),
    fun k => le_trans (mul_nonneg (hMth_nn k) (by positivity)) (le_max_left _ _),
    fun k => le_trans (mul_nonneg (add_nonneg (hCv_nn k).2.2.1 (hCth_nn k).2.2.1) (by positivity)) (le_max_left _ _), ?_⟩
  intro K4 c α hK4 hc1 hτD hK4τ hα
  dsimp only
  have hc0 : 0 < c := by linarith only [hc1]
  have hτ₁ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hτ₁_le1 : c ^ (-(1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hcτ : (c ^ (-(1 / 4 : ℝ))) ^ 4 * c = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    norm_num; rw [Real.rpow_neg_one]; exact inv_mul_cancel₀ hc0.ne'
  have hτ₁2 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have h0 := hmain hK4 hc0 hτ₁ hτD hcτ (show |(0 : ℝ)| ≤ (c ^ (-(1 / 4 : ℝ))) ^ 2 by
    rw [abs_zero]; exact sq_nonneg _)
  have hsq := hmain hK4 hc0 hτ₁ hτD hcτ (show |(c ^ (-(1 / 4 : ℝ))) ^ 2| ≤ (c ^ (-(1 / 4 : ℝ))) ^ 2 by
    rw [abs_of_nonneg (sq_nonneg _)])
  obtain ⟨⟨hv0b_cd, hv0m_cd, hva0_cd, hv1b_cd, hv1m_cd, _⟩, _, _,
    ⟨hsb0, hsm0, _, hsb1, hsm1, _, _, _, _, _, _, _, _, _, hv0b_cs, hv0m_cs, hva0_cs, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs, _⟩,
    _, _, hderiv0, _, hth_in0, hth_tail0, _⟩ := h0
  obtain ⟨_, _, _, ⟨_, _, hspa_sq, _⟩, _, _, hderiv_sq, _, hth_in_sq, hth_tail_sq, _⟩ := hsq
  have hv0_data := vTotal_data hK4 hc0 hτD 0
  have hva_1_cd : ContDiff ℝ ∞ (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) := (fctThetaD_vAlpha_eq hK4 hc0 hτ₁ hτD hcτ ((c ^ (-(1 / 4 : ℝ))) ^ 2) 0).2.1
  have hva_1_cs : HasCompactSupport (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) := (fctThetaD_vAlpha_eq hK4 hc0 hτ₁ hτD hcτ ((c ^ (-(1 / 4 : ℝ))) ^ 2) 0).2.2
  have hth_v0_cd : ContDiff ℝ ∞ (fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))))) :=
    contDiff_fctThetaD hv0_data.1 hv0_data.2.1
  have hth_a1_cd : ContDiff ℝ ∞ (fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ))))) := contDiff_fctThetaD hva_1_cd hva_1_cs
  have hv_cd : ContDiff ℝ ∞ (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) := by
    have hv_eq : vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))) =
        fun s => vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ))) s + α * vAlpha 1 (c ^ (-(1 / 4 : ℝ))) s :=
      funext (vTotal_eq_zero_add_smul K4 c α (c ^ (-(1 / 4 : ℝ))))
    rw [hv_eq]
    exact hv0_data.1.add (contDiff_const.mul hva_1_cd)
  have hth_v_cd : ContDiff ℝ ∞ (fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ))))) := by
    have hth_eq : fctThetaD (vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))) =
        fun s => fctThetaD (vTotal StripKernelChoice.star K4 c 0 (c ^ (-(1 / 4 : ℝ)))) s +
          α * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) s :=
      funext (vTotal_thetaD_eq_zero_add_smul hK4 hc0 hτD α)
    rw [hth_eq]
    exact hth_v0_cd.add (contDiff_const.mul hth_a1_cd)
  obtain ⟨hva_d, htha_in, htha_tl, hva_sp⟩ :=
    vAlpha1_all_helpers hK4 hc0 hτ₁ hτD hcτ (fun r => (hCth_nn r).2.2.1)
      (fun r t => (hderiv_sq r t).2.2.1) (fun r t ht => (hth_in_sq r t ht).2.2.1)
      (fun r t ht => (hth_tail_sq r t ht).2.2) hspa_sq
  have hv_bd := vTotal_deriv_all_helper (by linarith only [hK4]) hτ₁ hτ₁_le1 hcτ hK4τ hα hCv_nn
    hv0b_cd hv0m_cd hv1b_cd hv1m_cd hv0_data.1 hva_1_cd
    (fun r t => let h := hderiv0 r t; ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩) hva_d
  have hcd_v0 : ContDiff ℝ ∞ (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))) := hv0b_cd.add (contDiff_const.mul hv0m_cd)
  have hcd_v1 : ContDiff ℝ ∞ (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ)))) := hv1b_cd.add (contDiff_const.mul hv1m_cd)
  have hth_tl := fctThetaD_tail_all_helper hK4 hc0 hτD hτ₁_le1 hK4τ hα hCL_nn (fun r => (hCtail_nn r).1)
    hcd_v0 hv0_cs hcd_v1 hv1_cs hva0_cd hva0_cs hva_1_cd hva_1_cs
    (fun r t ht => let h := hth_tail0 r t ht; ⟨h.1, h.2.1⟩) htha_tl
  have hth_bd := fctThetaD_all_helper hK4 hc0 hτD hτ₁_le1 hK4τ hα hCth_nn hCL_nn (fun r => (hCtail_nn r).1)
    hv0b_cd hv0b_cs hv0m_cd hv0m_cs hv1b_cd hv1b_cs hv1m_cd hv1m_cs
    hcd_v0 hv0_cs hcd_v1 hv1_cs hva0_cd hva0_cs hva_1_cd hva_1_cs hth_v0_cd
    (fun r t ht => let h := hth_in0 r t ht; ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩) htha_in hth_tl
  exact ⟨hv_cd, hth_v_cd, hva_1_cd, hth_a1_cd,
    vTotal_pointwise_sub hc0 hτ₁ hτ₁_le1 hcτ hτ₁2 hMv_nn hMth_nn hMtail_nn
      (fun r => (hCv_nn r).2.2.1) (fun r => (hCth_nn r).2.2.1) (fun r => (hCtail_nn r).1) hCL_nn.2.2.1
      hv_bd hth_bd hth_tl hva_d htha_in htha_tl hva_sp hsb0 hsm0 hsb1 hsm1⟩

/-- info: 'FormalResearch.SignUncertainty.binetImag_edge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms binetImag_edge_bounds

/-- info: 'FormalResearch.SignUncertainty.vTotal_thetaD_edge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vTotal_thetaD_edge_bounds

end FormalResearch.SignUncertainty
