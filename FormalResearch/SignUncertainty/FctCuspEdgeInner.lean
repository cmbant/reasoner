/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCuspEdgeIbp
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Cutoffs, absolute bound, and inner-region estimates for `fct:cusp-edge` (F2a)

Support module for `FctCuspEdge.lean` (`CFT/sign_uncertainty/paper/constant_terms_five.tex`,
Lemma FCT.7a `fct:cusp-edge`, lines 1025–1092).

Contents:
* `CuspAmplitude`, `CuspProfile`, `cuspEdgeJ`: definitions matching Lemma FCT.7a.
* Smooth cutoffs `chi0`, `rhoSaddle`, `rhoInner` and their derivative bounds through order `3`.
* `cusp_abs_bound`: global `O(1)` bound and integrability for all `c ≥ 1`, `L ∈ ℝ`.
* `cusp_inner_bound`: `O(S^{-α-1})` bound for the inner region `|u| ≤ 5/4` (valid uniformly
  for all `L > 0` with `S = c^{2/3} L ≥ 16`, without splitting `L ≤ 1` vs `L ≥ 1`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctCuspEdge

open FormalResearch.CohnElkies

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Statement structures and main integral definition -/

/-- Hypotheses on the amplitude `A_c` in Lemma FCT.7a (`fct:cusp-edge`). -/
structure CuspAmplitude (η C_A : ℝ) (A : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ 3 A
  deriv_bound : ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j A τ‖ ≤ C_A * Real.exp (-η * |τ|)

/-- Hypotheses on the cusp profile `Y` and its local decomposition `Y = Y₀ + R` in Lemma FCT.7a (`fct:cusp-edge`). -/
structure CuspProfile (α C_Y : ℝ) (Y Y₀ R : ℝ → ℂ) : Prop where
  contDiffOn_Y : ContDiffOn ℝ 3 Y ({0}ᶜ)
  far_bound : ∀ j ≤ 3, ∀ u : ℝ, 1 ≤ |u| →
    ‖iteratedDeriv j Y u‖ ≤ C_Y * |u| ^ (-(2 * α + 3 / 2) - (j : ℝ))
  decomp : ∀ u : ℝ, |u| ≤ 2 → Y u = Y₀ u + R u
  contDiffOn_Y0 : ContDiffOn ℝ 3 Y₀ (Ioo (-2) 2)
  Y0_bound : ∀ j ≤ 3, ∀ u : ℝ, |u| < 2 → ‖iteratedDeriv j Y₀ u‖ ≤ C_Y
  R_bound : ∀ j ≤ 3, ∀ u : ℝ, 0 < |u| → |u| < 2 → ‖iteratedDeriv j R u‖ ≤ C_Y * |u| ^ (α - (j : ℝ))

/-- The oscillatory integral `J_c(L)` of Lemma FCT.7a (`fct:cusp-edge`). -/
noncomputable def cuspEdgeJ (c L : ℝ) (A Y : ℝ → ℂ) : ℂ :=
  ((c ^ ((1 : ℝ) / 3) / (2 * π) : ℝ) : ℂ) *
    ∫ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * A τ * Y (c ^ ((1 : ℝ) / 3) * τ)

/-! ### Smooth cutoffs and Leibniz helpers -/

/-- Underlying bump for `chi0`: `1` on `[-1, 1]`, `0` outside `(-5/4, 5/4)`. -/
noncomputable def chi0Bump : ContDiffBump (0 : ℝ) := ⟨1, 5 / 4, by norm_num, by norm_num⟩

/-- Even smooth cutoff equal to `1` on `[-1, 1]` and `0` for `|x| ≥ 5/4`. -/
noncomputable def chi0 (x : ℝ) : ℝ := (chi0Bump x + chi0Bump (-x)) / 2

lemma contDiff_chi0 : ContDiff ℝ ∞' chi0 :=
  (chi0Bump.contDiff.add (chi0Bump.contDiff.comp contDiff_neg)).div_const 2

lemma chi0_nonneg (x : ℝ) : 0 ≤ chi0 x := by
  unfold chi0; linarith [chi0Bump.nonneg' x, chi0Bump.nonneg' (-x)]

lemma chi0_le_one (x : ℝ) : chi0 x ≤ 1 := by
  unfold chi0; linarith [chi0Bump.le_one (x := x), chi0Bump.le_one (x := -x)]

lemma chi0_eq_one {x : ℝ} (hx : |x| ≤ 1) : chi0 x = 1 := by
  unfold chi0
  have h1 : x ∈ Metric.closedBall (0 : ℝ) chi0Bump.rIn := by simpa [chi0Bump, Real.norm_eq_abs] using hx
  have h2 : -x ∈ Metric.closedBall (0 : ℝ) chi0Bump.rIn := by simpa [chi0Bump, Real.norm_eq_abs] using hx
  rw [chi0Bump.one_of_mem_closedBall h1, chi0Bump.one_of_mem_closedBall h2]; norm_num

lemma chi0_eq_zero {x : ℝ} (hx : 5 / 4 ≤ |x|) : chi0 x = 0 := by
  unfold chi0
  have h1 : x ∉ Function.support chi0Bump := by
    rw [chi0Bump.support_eq]
    simp only [chi0Bump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hx
  have h2 : -x ∉ Function.support chi0Bump := by
    rw [chi0Bump.support_eq]
    simp only [chi0Bump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, not_lt]
    exact hx
  rw [Function.notMem_support.mp h1, Function.notMem_support.mp h2]; norm_num

/-- Smooth saddle cutoff: `1` on `[3/4, 3/2]`, `0` outside `(1/2, 7/4) ⊂ (1/2, 2)`. -/
noncomputable def rhoSaddleBump : ContDiffBump (9 / 8 : ℝ) := ⟨3 / 8, 5 / 8, by norm_num, by norm_num⟩

noncomputable def rhoSaddle (x : ℝ) : ℝ := rhoSaddleBump x

lemma contDiff_rhoSaddle : ContDiff ℝ ∞' rhoSaddle := rhoSaddleBump.contDiff

lemma rhoSaddle_nonneg (x : ℝ) : 0 ≤ rhoSaddle x := rhoSaddleBump.nonneg' x

lemma rhoSaddle_le_one (x : ℝ) : rhoSaddle x ≤ 1 := rhoSaddleBump.le_one

lemma rhoSaddle_eq_one {x : ℝ} (hx1 : 3 / 4 ≤ x) (hx2 : x ≤ 3 / 2) : rhoSaddle x = 1 := by
  apply rhoSaddleBump.one_of_mem_closedBall
  simp only [rhoSaddleBump, Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith

lemma rhoSaddle_eq_zero_of_le {x : ℝ} (hx : x ≤ 1 / 2) : rhoSaddle x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support rhoSaddleBump := hne
  rw [rhoSaddleBump.support_eq] at hmem
  simp only [rhoSaddleBump, Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
  linarith

lemma rhoSaddle_eq_zero_of_ge {x : ℝ} (hx : 7 / 4 ≤ x) : rhoSaddle x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support rhoSaddleBump := hne
  rw [rhoSaddleBump.support_eq] at hmem
  simp only [rhoSaddleBump, Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
  linarith

/-- Smooth inner cutoff for `L ≥ 1`: `1` on `|x| ≤ 1/2`, `0` on `|x| ≥ 1`. -/
noncomputable def rhoInnerBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def rhoInner (x : ℝ) : ℝ := rhoInnerBump x

lemma contDiff_rhoInner : ContDiff ℝ ∞' rhoInner := rhoInnerBump.contDiff

lemma rhoInner_nonneg (x : ℝ) : 0 ≤ rhoInner x := rhoInnerBump.nonneg' x

lemma rhoInner_le_one (x : ℝ) : rhoInner x ≤ 1 := rhoInnerBump.le_one

lemma rhoInner_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : rhoInner x = 1 := by
  apply rhoInnerBump.one_of_mem_closedBall
  simpa [rhoInnerBump, Real.norm_eq_abs] using hx

lemma rhoInner_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : rhoInner x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support rhoInnerBump := hne
  rw [rhoInnerBump.support_eq] at hmem
  simp only [rhoInnerBump, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  linarith

/-- Uniform derivative bound through order `3` for any `C^∞` compactly supported function. -/
lemma smooth_compact_deriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞' f)
    {R : ℝ} (hsupp : ∀ x : ℝ, R ≤ |x| → f x = 0) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ 3, ∀ x : ℝ, |iteratedDeriv j f x| ≤ B := by
  have hbd : ∀ j : ℕ, ∃ B : ℝ, ∀ x : ℝ, |iteratedDeriv j f x| ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(max R 1 + 1)) (b := max R 1 + 1)).exists_bound_of_continuousOn
      (hf.continuous_iteratedDeriv j (by exact_mod_cast le_top)).continuousOn
    refine ⟨max B 0, fun x => ?_⟩
    by_cases hx : |x| ≤ max R 1 + 1
    · have hmem : x ∈ Icc (-(max R 1 + 1)) (max R 1 + 1) := abs_le.mp hx
      have h1 : |iteratedDeriv j f x| ≤ B := by simpa [Real.norm_eq_abs] using hB x hmem
      exact h1.trans (le_max_left _ _)
    · push Not at hx
      have hev : f =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
          (show max R 1 < |x| by linarith)] with y hy
        exact hsupp y (le_trans (le_max_left R 1) hy.le)
      rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, abs_zero]
      exact le_max_right _ _
  choose B hB using hbd
  refine ⟨max 1 (max (max (B 0) (B 1)) (max (B 2) (B 3))), le_max_left _ _, fun j hj x => ?_⟩
  interval_cases j
  · exact (hB 0 x).trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _))
  · exact (hB 1 x).trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _))
  · exact (hB 2 x).trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
  · exact (hB 3 x).trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))

lemma chi0_deriv_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ 3, ∀ x : ℝ, |iteratedDeriv j chi0 x| ≤ B :=
  smooth_compact_deriv_bound contDiff_chi0 (R := 5 / 4) fun _ hx => chi0_eq_zero hx

lemma rhoSaddle_deriv_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ 3, ∀ x : ℝ, |iteratedDeriv j rhoSaddle x| ≤ B :=
  smooth_compact_deriv_bound contDiff_rhoSaddle (R := 2) fun x hx => by
    rcases le_or_gt 0 x with h | h
    · exact rhoSaddle_eq_zero_of_ge (by rw [abs_of_nonneg h] at hx; linarith)
    · exact rhoSaddle_eq_zero_of_le (by rw [abs_of_neg h] at hx; linarith)

lemma rhoInner_deriv_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ j ≤ 3, ∀ x : ℝ, |iteratedDeriv j rhoInner x| ≤ B :=
  smooth_compact_deriv_bound contDiff_rhoInner (R := 1) fun _ hx => rhoInner_eq_zero hx

/-- Scaling formula for `iteratedDeriv` of `f (a * x)`. -/
lemma iteratedDeriv_comp_mul_left_C (k : ℕ) (f : ℝ → ℂ) (a x : ℝ) :
    iteratedDeriv k (fun t => f (a * t)) x = ((a ^ k : ℝ) : ℂ) * iteratedDeriv k f (a * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun t => f (a * t)) =
      fun t => ((a ^ k : ℝ) : ℂ) * iteratedDeriv k f (a * t) from funext ih]
    rw [deriv_const_mul_field']
    dsimp only
    rw [deriv_comp_mul_left a (iteratedDeriv k f) x, ← iteratedDeriv_succ]
    simp only [Complex.real_smul, pow_succ, Complex.ofReal_mul]
    ring

lemma iteratedDeriv_comp_mul_left_R (k : ℕ) (f : ℝ → ℝ) (a x : ℝ) :
    iteratedDeriv k (fun t => f (a * t)) x = a ^ k * iteratedDeriv k f (a * x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun t => f (a * t)) =
      fun t => a ^ k * iteratedDeriv k f (a * t) from funext ih]
    rw [deriv_const_mul_field']
    dsimp only
    rw [deriv_comp_mul_left a (iteratedDeriv k f) x, ← iteratedDeriv_succ]
    simp only [smul_eq_mul, pow_succ]
    ring

/-- Product derivative bound through order `3` with a common weight `w > 0`. -/
lemma leibniz3_bound {f g : ℝ → ℂ} {x M₁ M₂ w : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hw : 0 < w)
    (hf_bd : ∀ j ≤ 3, ‖iteratedDeriv j f x‖ ≤ M₁ * w ^ (-(j : ℤ)))
    (hg_bd : ∀ j ≤ 3, ‖iteratedDeriv j g x‖ ≤ M₂ * w ^ (-(j : ℤ))) :
    ∀ j ≤ 3, ‖iteratedDeriv j (fun t => f t * g t) x‖ ≤ 8 * M₁ * M₂ * w ^ (-(j : ℤ)) := by
  intro j hj
  have hleib := iteratedDeriv_mul (n := j) (hf.of_le (by exact_mod_cast hj)) (hg.of_le (by exact_mod_cast hj))
  rw [show (fun t => f t * g t) = f * g from rfl, hleib]
  calc ‖∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDeriv i f x * iteratedDeriv (j - i) g x‖
      ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDeriv i f x * iteratedDeriv (j - i) g x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M₁ * M₂ * w ^ (-(j : ℤ))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [mul_assoc, norm_mul, norm_mul, Complex.norm_natCast]
        have ha := hf_bd i (by omega)
        have hb := hg_bd (j - i) (by omega)
        have hw_eq : w ^ (-(i : ℤ)) * w ^ (-((j - i : ℕ) : ℤ)) = w ^ (-(j : ℤ)) := by
          rw [← zpow_add₀ hw.ne']; congr 1; omega
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        calc ‖iteratedDeriv i f x‖ * ‖iteratedDeriv (j - i) g x‖
            ≤ (M₁ * w ^ (-(i : ℤ))) * (M₂ * w ^ (-((j - i : ℕ) : ℤ))) :=
              mul_le_mul ha hb (norm_nonneg _) (by positivity)
          _ = M₁ * M₂ * (w ^ (-(i : ℤ)) * w ^ (-((j - i : ℕ) : ℤ))) := by ring
          _ = M₁ * M₂ * w ^ (-(j : ℤ)) := by rw [hw_eq]
    _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * (M₁ * M₂ * w ^ (-(j : ℤ))) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ j * (M₁ * M₂ * w ^ (-(j : ℤ))) := by
        have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hsum]
    _ ≤ 8 * M₁ * M₂ * w ^ (-(j : ℤ)) := by
        have h2 : (2 : ℝ) ^ j ≤ 8 := by
          calc (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
            _ = 8 := by norm_num
        have hnn : 0 ≤ M₁ * M₂ * w ^ (-(j : ℤ)) := by positivity
        nlinarith

lemma iteratedDeriv_ofReal_eq' (n : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv n (fun t => (g t : ℂ)) x = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  induction n generalizing g x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ,
      show iteratedDeriv n (fun t => (g t : ℂ)) = fun t => ((iteratedDeriv n g t : ℝ) : ℂ) from funext (ih g)]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv n g) x
    · exact hd.hasDerivAt.ofReal_comp.deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun t => ((iteratedDeriv n g t : ℝ) : ℂ)) x :=
        fun hcd => hd (Complex.reCLM.differentiableAt.comp x hcd)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, Complex.ofReal_zero]

/-- Real-scalar-times-complex version of `leibniz3_bound`. -/
lemma leibniz3_real_mul_bound {f : ℝ → ℝ} {g : ℝ → ℂ} {x M₁ M₂ w : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hw : 0 < w)
    (hf_bd : ∀ j ≤ 3, |iteratedDeriv j f x| ≤ M₁ * w ^ (-(j : ℤ)))
    (hg_bd : ∀ j ≤ 3, ‖iteratedDeriv j g x‖ ≤ M₂ * w ^ (-(j : ℤ))) :
    ∀ j ≤ 3, ‖iteratedDeriv j (fun t => (f t : ℂ) * g t) x‖ ≤ 8 * M₁ * M₂ * w ^ (-(j : ℤ)) := by
  refine leibniz3_bound (Complex.ofRealCLM.contDiff.contDiffAt.comp x hf) hg hM₁ hM₂ hw ?_ hg_bd
  intro j hj
  rw [iteratedDeriv_ofReal_eq', Complex.norm_real, Real.norm_eq_abs]
  exact hf_bd j hj

/-- Exponential absorbs powers: `x^j * exp(-η/2 * x) ≤ j! * (2/η)^j` for `x ≥ 0`. -/
lemma pow_mul_exp_neg_le (j : ℕ) {η x : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    x ^ j * Real.exp (-(η / 2) * x) ≤ (j.factorial : ℝ) * (2 / η) ^ j := by
  have h1 := Real.pow_div_factorial_le_exp (η / 2 * x) (by positivity) j
  have hE : 0 < Real.exp (η / 2 * x) := Real.exp_pos _
  rw [show -(η / 2) * x = -(η / 2 * x) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  have hf : (0 : ℝ) < j.factorial := by positivity
  have h2 : (η / 2 * x) ^ j ≤ j.factorial * Real.exp (η / 2 * x) := by
    have := (div_le_iff₀ hf).mp h1; linarith
  have h3 : (η / 2) ^ j * x ^ j ≤ j.factorial * Real.exp (η / 2 * x) := by rwa [← mul_pow]
  have h4 : (2 / η) ^ j * (η / 2) ^ j = 1 := by rw [← mul_pow]; field_simp; simp
  calc x ^ j = ((2 / η) ^ j * (η / 2) ^ j) * x ^ j := by rw [h4, one_mul]
    _ = (2 / η) ^ j * ((η / 2) ^ j * x ^ j) := by ring
    _ ≤ (2 / η) ^ j * (j.factorial * Real.exp (η / 2 * x)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- Scaled amplitude `u ↦ A (ς * u)` satisfies `‖∂_u^j (A(ς u))‖ ≤ C_η * C_A * |u|^{-j} * exp(-η/2 * ς * |u|)`. -/
lemma scaled_amp_deriv_bound {η C_A ς : ℝ} {A : ℝ → ℂ}
    (hη : 0 < η) (hCA : 0 ≤ C_A) (hς : 0 < ς) (hA : CuspAmplitude η C_A A)
    {u : ℝ} (hu : u ≠ 0) :
    ∀ j ≤ 3, ‖iteratedDeriv j (fun t => A (ς * t)) u‖ ≤
      (6 * max 1 ((2 / η) ^ 3)) * C_A * Real.exp (-(η / 2) * ς * |u|) * |u| ^ (-(j : ℤ)) := by
  intro j hj
  rw [iteratedDeriv_comp_mul_left_C, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hς.le j)]
  have h1 := hA.deriv_bound j hj (ς * u)
  rw [abs_mul, abs_of_pos hς] at h1
  have habs_pos : 0 < |u| := abs_pos.mpr hu
  have hexp : Real.exp (-η * (ς * |u|)) = Real.exp (-(η / 2) * (ς * |u|)) * Real.exp (-(η / 2) * ς * |u|) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpow := pow_mul_exp_neg_le j hη (show 0 ≤ ς * |u| by positivity)
  have hfac : (j.factorial : ℝ) ≤ 6 := by
    interval_cases j <;> norm_num [Nat.factorial]
  have h2η : (2 / η) ^ j ≤ max 1 ((2 / η) ^ 3) := by
    rcases le_total (2 / η) 1 with hle | hge
    · exact (pow_le_one₀ (by positivity) hle).trans (le_max_left _ _)
    · exact (pow_le_pow_right₀ hge hj).trans (le_max_right _ _)
  have hprod : (ς * |u|) ^ j * Real.exp (-(η / 2) * (ς * |u|)) ≤ 6 * max 1 ((2 / η) ^ 3) := by
    calc (ς * |u|) ^ j * Real.exp (-(η / 2) * (ς * |u|))
        ≤ (j.factorial : ℝ) * (2 / η) ^ j := hpow
      _ ≤ 6 * max 1 ((2 / η) ^ 3) := mul_le_mul hfac h2η (by positivity) (by norm_num)
  have hzpow : ς ^ j = (ς * |u|) ^ j * |u| ^ (-(j : ℤ)) := by
    rw [mul_pow, zpow_neg, zpow_natCast]
    field_simp [pow_ne_zero j habs_pos.ne']
  calc ς ^ j * ‖iteratedDeriv j A (ς * u)‖
      ≤ ς ^ j * (C_A * Real.exp (-η * (ς * |u|))) := mul_le_mul_of_nonneg_left h1 (pow_nonneg hς.le j)
    _ = ((ς * |u|) ^ j * Real.exp (-(η / 2) * (ς * |u|))) * C_A * Real.exp (-(η / 2) * ς * |u|) * |u| ^ (-(j : ℤ)) := by
        rw [hexp, hzpow]; ring
    _ ≤ (6 * max 1 ((2 / η) ^ 3)) * C_A * Real.exp (-(η / 2) * ς * |u|) * |u| ^ (-(j : ℤ)) := by
        gcongr

/-! ### Global `O(1)` bound and integrability -/

lemma cusp_Y_norm_bound {α C_Y : ℝ} {Y Y₀ R : ℝ → ℂ}
    (hα0 : 0 < α) (hCY : 0 ≤ C_Y) (hY : CuspProfile α C_Y Y Y₀ R) :
    (∀ u : ℝ, 0 < |u| → |u| ≤ 1 → ‖Y u‖ ≤ 2 * C_Y) ∧
    (∀ u : ℝ, 1 ≤ |u| → ‖Y u‖ ≤ C_Y * |u| ^ (-(2 * α + 3 / 2))) := by
  constructor
  · intro u hu0 hu1
    rw [hY.decomp u (by linarith)]
    have h1 := hY.Y0_bound 0 (by omega) u (by linarith)
    have h2 := hY.R_bound 0 (by omega) u hu0 (by linarith)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1 h2
    have hrpow : |u| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg u) hu1 hα0.le
    calc ‖Y₀ u + R u‖ ≤ ‖Y₀ u‖ + ‖R u‖ := norm_add_le _ _
      _ ≤ C_Y + C_Y * |u| ^ α := add_le_add h1 h2
      _ ≤ C_Y + C_Y * 1 := by gcongr
      _ = 2 * C_Y := by ring
  · intro u hu1
    have h := hY.far_bound 0 (by omega) u hu1
    simpa [iteratedDeriv_zero] using h

lemma cusp_Y_integrable {α C_Y : ℝ} {Y Y₀ R : ℝ → ℂ}
    (hα0 : 0 < α) (hCY : 0 ≤ C_Y) (hY : CuspProfile α C_Y Y Y₀ R) :
    Integrable Y ∧ ∫ u : ℝ, ‖Y u‖ ≤ (4 + 2 / (2 * α + 1 / 2)) * C_Y := by
  obtain ⟨hnear, hfar⟩ := cusp_Y_norm_bound hα0 hCY hY
  have haesm : AEStronglyMeasurable Y volume := by
    have hrest : volume.restrict ({0}ᶜ : Set ℝ) = volume :=
      Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (by simp))
    rw [← hrest]
    exact hY.contDiffOn_Y.continuousOn.aestronglyMeasurable isOpen_compl_singleton.measurableSet
  let g : ℝ → ℝ := fun u => if |u| ≤ 1 then 2 * C_Y else C_Y * |u| ^ (-(2 * α + 3 / 2))
  have hg_int_Ioi : IntegrableOn (fun u : ℝ => C_Y * u ^ (-(2 * α + 3 / 2))) (Ioi 1) := by
    have h := integrableOn_Ioi_rpow_of_lt (show -(2 * α + 3 / 2) < -1 by linarith) zero_lt_one
    exact h.const_mul C_Y
  have hg_eq : ∀ u : ℝ, g u = (Icc (-1 : ℝ) 1).indicator (fun _ => 2 * C_Y) u +
      (Ioi (1 : ℝ)).indicator (fun x => C_Y * x ^ (-(2 * α + 3 / 2))) u +
      (Iio (-1 : ℝ)).indicator (fun x => C_Y * (-x) ^ (-(2 * α + 3 / 2))) u := by
    intro u
    dsimp only [g]
    by_cases h1 : |u| ≤ 1
    · have hm : u ∈ Icc (-1 : ℝ) 1 := abs_le.mp h1
      have h2 : u ∉ Ioi (1 : ℝ) := by simp; linarith [hm.2]
      have h3 : u ∉ Iio (-1 : ℝ) := by simp; linarith [hm.1]
      simp [h1, hm, h2, h3]
    · push Not at h1
      have hm : u ∉ Icc (-1 : ℝ) 1 := fun h => by linarith [abs_le.mpr h]
      rcases lt_or_gt_of_ne (show u ≠ 0 by intro h0; subst h0; simp at h1; linarith) with hneg | hpos
      · have h2 : u ∉ Ioi (1 : ℝ) := by simp; linarith
        have h3 : u ∈ Iio (-1 : ℝ) := by rw [abs_of_neg hneg] at h1; simp [mem_Iio]; linarith
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr h1)), Set.indicator_of_notMem hm,
          Set.indicator_of_notMem h2, Set.indicator_of_mem h3, abs_of_neg hneg]; ring
      · have h2 : u ∈ Ioi (1 : ℝ) := by rw [abs_of_pos hpos] at h1; exact h1
        have h3 : u ∉ Iio (-1 : ℝ) := by simp; linarith
        rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr h1)), Set.indicator_of_notMem hm,
          Set.indicator_of_mem h2, Set.indicator_of_notMem h3, abs_of_pos hpos]; ring
  have hg1 : Integrable (fun u : ℝ => (Icc (-1 : ℝ) 1).indicator (fun _ => 2 * C_Y) u) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hg2 : Integrable (fun u : ℝ => (Ioi (1 : ℝ)).indicator (fun x => C_Y * x ^ (-(2 * α + 3 / 2))) u) :=
    hg_int_Ioi.integrable_indicator measurableSet_Ioi
  have hg3_eq : (fun u : ℝ => (Iio (-1 : ℝ)).indicator (fun x => C_Y * (-x) ^ (-(2 * α + 3 / 2))) u) =
      fun u => (Ioi (1 : ℝ)).indicator (fun x => C_Y * x ^ (-(2 * α + 3 / 2))) (-u) := by
    ext u
    by_cases h : u < -1
    · have h1 : u ∈ Iio (-1 : ℝ) := h
      have h2 : -u ∈ Ioi (1 : ℝ) := by simp [mem_Ioi]; linarith
      simp [h1, h2]
    · have h1 : u ∉ Iio (-1 : ℝ) := h
      have h2 : -u ∉ Ioi (1 : ℝ) := by simp [mem_Ioi]; linarith
      simp [h1, h2]
  have hg3 : Integrable (fun u : ℝ => (Iio (-1 : ℝ)).indicator (fun x => C_Y * (-x) ^ (-(2 * α + 3 / 2))) u) := by
    rw [hg3_eq]; exact hg2.comp_neg
  have hg_int : Integrable g :=
    ((hg1.add hg2).add hg3).congr (Eventually.of_forall fun u => (hg_eq u).symm)
  have hdom : ∀ᵐ u ∂volume, ‖Y u‖ ≤ g u := by
    have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [hne] with u hu
    have hu0 : 0 < |u| := abs_pos.mpr hu
    dsimp only [g]
    split_ifs with h1
    · exact hnear u hu0 h1
    · exact hfar u (le_of_not_ge h1)
  have hY_int : Integrable Y := hg_int.mono' haesm hdom
  refine ⟨hY_int, ?_⟩
  have hg_val : ∫ u : ℝ, g u = (4 + 2 / (2 * α + 1 / 2)) * C_Y := by
    rw [integral_congr_ae (ae_of_all _ hg_eq),
      integral_add (f := fun u => (Icc (-1 : ℝ) 1).indicator (fun _ => 2 * C_Y) u +
        (Ioi (1 : ℝ)).indicator (fun x => C_Y * x ^ (-(2 * α + 3 / 2))) u) (hg1.add hg2) hg3,
      integral_add hg1 hg2]
    have hi1 : ∫ u : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => 2 * C_Y) u = 4 * C_Y := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const]
      simp; ring
    have hi2 : ∫ u : ℝ, (Ioi (1 : ℝ)).indicator (fun x => C_Y * x ^ (-(2 * α + 3 / 2))) u =
        C_Y / (2 * α + 1 / 2) := by
      rw [integral_indicator measurableSet_Ioi, integral_const_mul,
        integral_Ioi_rpow_of_lt (show -(2 * α + 3 / 2) < -1 by linarith) zero_lt_one,
        Real.one_rpow, show -(2 * α + 3 / 2) + 1 = -(2 * α + 1 / 2) by ring]
      have hne : (2 * α + 1 / 2 : ℝ) ≠ 0 := by linarith
      field_simp [hne]
    have hi3 : ∫ u : ℝ, (Iio (-1 : ℝ)).indicator (fun x => C_Y * (-x) ^ (-(2 * α + 3 / 2))) u =
        C_Y / (2 * α + 1 / 2) := by
      rw [hg3_eq, MeasureTheory.integral_neg_eq_self, hi2]
    rw [hi1, hi2, hi3]; ring
  calc ∫ u : ℝ, ‖Y u‖ ≤ ∫ u : ℝ, g u := integral_mono_ae hY_int.norm hg_int hdom
    _ = (4 + 2 / (2 * α + 1 / 2)) * C_Y := hg_val

/-- Change of variables `u = c^{1/3} τ` for `cuspEdgeJ`. -/
lemma cuspEdgeJ_eq_scaled {c L : ℝ} (hc : 0 < c) (A Y : ℝ → ℂ) :
    cuspEdgeJ c L A Y =
      ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ u : ℝ, Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
          A (c ^ (-(1 : ℝ) / 3) * u) * Y u := by
  unfold cuspEdgeJ
  set a : ℝ := c ^ ((1 : ℝ) / 3)
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hinv : a⁻¹ = c ^ (-(1 : ℝ) / 3) := by
    rw [← Real.rpow_neg hc.le]; congr 1; ring
  have hsub := Measure.integral_comp_mul_left (fun u =>
    Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
      A (c ^ (-(1 : ℝ) / 3) * u) * Y u) a
  have hcongr : (fun τ => Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * (a * τ)) : ℝ) : ℂ)) *
      A (c ^ (-(1 : ℝ) / 3) * (a * τ)) * Y (a * τ)) =
      fun τ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * A τ * Y (a * τ) := by
    ext τ
    have hmul : c ^ (-(1 : ℝ) / 3) * (a * τ) = τ := by
      rw [← hinv, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    rw [hmul]
  rw [hcongr, abs_of_pos (inv_pos.mpr ha), Complex.real_smul] at hsub
  rw [hsub]
  simp only [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_one]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  field_simp [haC]

/-- Global `O(1)` bound (first bound of Lemma FCT.7a). -/
theorem cusp_abs_bound {α η C_A C_Y : ℝ} (hα0 : 0 < α) (hη : 0 < η) (hCA : 0 ≤ C_A) (hCY : 0 ≤ C_Y)
    {c L : ℝ} (hc : 1 ≤ c) {A Y Y₀ R : ℝ → ℂ}
    (hA : CuspAmplitude η C_A A) (hY : CuspProfile α C_Y Y Y₀ R) :
    ‖cuspEdgeJ c L A Y‖ ≤ (1 / (2 * π)) * ((4 + 2 / (2 * α + 1 / 2)) * C_A * C_Y) := by
  have hc0 : 0 < c := by linarith
  rw [cuspEdgeJ_eq_scaled hc0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  obtain ⟨hY_int, hY_bd⟩ := cusp_Y_integrable hα0 hCY hY
  have hle : ∀ u : ℝ, ‖Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
      A (c ^ (-(1 : ℝ) / 3) * u) * Y u‖ ≤ C_A * ‖Y u‖ := by
    intro u
    rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    have hA0 := hA.deriv_bound 0 (by omega) (c ^ (-(1 : ℝ) / 3) * u)
    simp only [iteratedDeriv_zero] at hA0
    have hexp : Real.exp (-η * |c ^ (-(1 : ℝ) / 3) * u|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (c ^ (-(1 : ℝ) / 3) * u)])
    have hA_le : ‖A (c ^ (-(1 : ℝ) / 3) * u)‖ ≤ C_A := hA0.trans (by nlinarith)
    exact mul_le_mul_of_nonneg_right hA_le (norm_nonneg _)
  have hint_le : ‖∫ u : ℝ, Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
      A (c ^ (-(1 : ℝ) / 3) * u) * Y u‖ ≤ C_A * ∫ u : ℝ, ‖Y u‖ := by
    calc ‖∫ u : ℝ, Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
            A (c ^ (-(1 : ℝ) / 3) * u) * Y u‖
        ≤ ∫ u : ℝ, ‖Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
            A (c ^ (-(1 : ℝ) / 3) * u) * Y u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, C_A * ‖Y u‖ := by
          refine integral_mono ?_ (hY_int.norm.const_mul C_A) hle
          have hc1 : Continuous (fun u : ℝ => Complex.exp (Complex.I * ((c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u) : ℝ) : ℂ)) *
              A (c ^ (-(1 : ℝ) / 3) * u)) := by
            have h1 : Continuous (fun u : ℝ => edgePhi L (c ^ (-(1 : ℝ) / 3) * u)) :=
              (contDiff_edgePhi L).continuous.comp (continuous_const.mul continuous_id)
            have h2 : Continuous (fun u : ℝ => A (c ^ (-(1 : ℝ) / 3) * u)) :=
              hA.contDiff.continuous.comp (continuous_const.mul continuous_id)
            exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
              (continuous_const.mul h1)))).mul h2
          exact ((hY_int.norm.const_mul C_A).mono' (hc1.aestronglyMeasurable.mul hY_int.aestronglyMeasurable)
            (Eventually.of_forall hle)).norm
      _ = C_A * ∫ u : ℝ, ‖Y u‖ := integral_const_mul _ _
  have hprod : C_A * ∫ u : ℝ, ‖Y u‖ ≤ (4 + 2 / (2 * α + 1 / 2)) * C_A * C_Y := by
    calc C_A * ∫ u : ℝ, ‖Y u‖ ≤ C_A * ((4 + 2 / (2 * α + 1 / 2)) * C_Y) :=
          mul_le_mul_of_nonneg_left hY_bd hCA
      _ = (4 + 2 / (2 * α + 1 / 2)) * C_A * C_Y := by ring
  exact mul_le_mul_of_nonneg_left (hint_le.trans hprod) (by positivity)

/-! ### Scaled phase `ψ(u) = c Φ(ς u; L)` on the inner region `|u| ≤ 2` -/

/-- The scaled phase `ψ(u) = c * Φ(c^{-1/3} u; L)`. -/
noncomputable def scaledPsi (c L u : ℝ) : ℝ := c * edgePhi L (c ^ (-(1 : ℝ) / 3) * u)

lemma contDiff_scaledPsi (c L : ℝ) : ContDiff ℝ ∞' (scaledPsi c L) :=
  contDiff_const.mul ((contDiff_edgePhi L).comp (contDiff_const.mul contDiff_id))

lemma deriv_scaledPsi {c L : ℝ} (hc : 0 < c) (u : ℝ) :
    deriv (scaledPsi c L) u = c ^ ((2 : ℝ) / 3) * edgePhiDeriv L (c ^ (-(1 : ℝ) / 3) * u) := by
  unfold scaledPsi
  have hd : HasDerivAt (fun t => c * edgePhi L (c ^ (-(1 : ℝ) / 3) * t))
      (c * (edgePhiDeriv L (c ^ (-(1 : ℝ) / 3) * u) * c ^ (-(1 : ℝ) / 3))) u := by
    have h1 : HasDerivAt (fun t => c ^ (-(1 : ℝ) / 3) * t) (c ^ (-(1 : ℝ) / 3)) u := by
      simpa using (hasDerivAt_id u).const_mul (c ^ (-(1 : ℝ) / 3))
    exact ((hasDerivAt_edgePhi L (c ^ (-(1 : ℝ) / 3) * u)).comp u h1).const_mul c
  rw [hd.deriv]
  have hpow : c * c ^ (-(1 : ℝ) / 3) = c ^ ((2 : ℝ) / 3) := by
    calc c * c ^ (-(1 : ℝ) / 3) = c ^ (1 : ℝ) * c ^ (-(1 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = c ^ ((1 : ℝ) + (-(1 : ℝ) / 3)) := (Real.rpow_add hc (1 : ℝ) (-(1 : ℝ) / 3)).symm
      _ = c ^ ((2 : ℝ) / 3) := by norm_num
  calc c * (edgePhiDeriv L (c ^ (-(1 : ℝ) / 3) * u) * c ^ (-(1 : ℝ) / 3))
      = (c * c ^ (-(1 : ℝ) / 3)) * edgePhiDeriv L (c ^ (-(1 : ℝ) / 3) * u) := by ring
    _ = c ^ ((2 : ℝ) / 3) * edgePhiDeriv L (c ^ (-(1 : ℝ) / 3) * u) := by rw [hpow]

lemma iteratedDeriv_scaledPsi {c L : ℝ} (_hc : 0 < c) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (scaledPsi c L) u =
      c * (c ^ (-(1 : ℝ) / 3)) ^ k * iteratedDeriv k (edgePhi L) (c ^ (-(1 : ℝ) / 3) * u) := by
  unfold scaledPsi
  rw [iteratedDeriv_const_mul_field c (fun t => edgePhi L (c ^ (-(1 : ℝ) / 3) * t)),
    iteratedDeriv_comp_mul_left_R]
  ring

lemma edgePhiDeriv_eq_sub_m (L τ : ℝ) : edgePhiDeriv L τ = L - hankelEdgeM τ := by
  have hev : hankelEdgeM τ = hankelEdgeM |τ| := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, hankelEdgeM_even]
  rw [hev]
  unfold edgePhiDeriv hankelEdgeM ceEll
  by_cases hτ : τ = 0
  · simp [hτ]
  · simp only [hτ, ↓reduceIte]
    have h1 : Real.log (Real.tanh (π * |τ| / 2) / (π * |τ| / 2)) =
        -Real.log ((π * |τ| / 2) / Real.tanh (π * |τ| / 2)) := by
      rw [← Real.log_inv, inv_div]
    linarith

/-- On `|u| ≤ 2` with `S = c^{2/3} L ≥ 16`, `ψ'(u) ≥ S / 2` and `|ψ^{(j+1)}(u)| ≤ K_ψ` for `j = 1, 2, 3`. -/
lemma scaledPsi_inner_bounds :
    ∃ K_ψ : ℝ, 1 ≤ K_ψ ∧ ∀ (c L u : ℝ), 1 ≤ c → 16 ≤ c ^ ((2 : ℝ) / 3) * L → |u| ≤ 2 →
      c ^ ((2 : ℝ) / 3) * L / 2 ≤ deriv (scaledPsi c L) u ∧
      ∀ j ∈ ({1, 2, 3} : Finset ℕ), |iteratedDeriv (j + 1) (scaledPsi c L) u| ≤ K_ψ := by
  obtain ⟨C3, hC3_nn, hC3⟩ := edgePhi_iteratedDeriv_bound 3 (by norm_num)
  obtain ⟨C4, hC4_nn, hC4⟩ := edgePhi_iteratedDeriv_bound 4 (by norm_num)
  refine ⟨max 4 (max C3 C4), by exact le_trans (by norm_num) (le_max_left _ _), fun c L u hc hS hu => ?_⟩
  have hc0 : 0 < c := by linarith
  have hς_pos : 0 < c ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
  have hς_le : c ^ (-(1 : ℝ) / 3) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have hς_sq : c ^ ((2 : ℝ) / 3) * (c ^ (-(1 : ℝ) / 3)) ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  constructor
  · rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
    have hm := hankelEdgeM_le_sq (c ^ (-(1 : ℝ) / 3) * u)
    have hmul : c ^ ((2 : ℝ) / 3) * hankelEdgeM (c ^ (-(1 : ℝ) / 3) * u) ≤ π ^ 2 / 12 * u ^ 2 := by
      calc c ^ ((2 : ℝ) / 3) * hankelEdgeM (c ^ (-(1 : ℝ) / 3) * u)
          ≤ c ^ ((2 : ℝ) / 3) * (π ^ 2 / 12 * (c ^ (-(1 : ℝ) / 3) * u) ^ 2) :=
            mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hc0.le _)
        _ = (c ^ ((2 : ℝ) / 3) * (c ^ (-(1 : ℝ) / 3)) ^ 2) * (π ^ 2 / 12 * u ^ 2) := by ring
        _ = π ^ 2 / 12 * u ^ 2 := by rw [hς_sq, one_mul]
    have hu2 : u ^ 2 ≤ 4 := by nlinarith [abs_le.mp hu]
    have hpi : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hbound : π ^ 2 / 12 * u ^ 2 ≤ 4 := by nlinarith [sq_nonneg u]
    rw [mul_sub]
    linarith
  · intro j hj
    rw [iteratedDeriv_scaledPsi hc0]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · -- j = 1: |ψ''(u)| = c^{1/3} |Φ''(ς u)| ≤ (π²/6) |u| ≤ 4
      rw [edgePhi_iteratedDeriv_ge_two L 2 (by norm_num), show (2 - 2 : ℕ) = 0 by rfl, iteratedDeriv_zero]
      have h2 : |edgePhiDeriv2 (c ^ (-(1 : ℝ) / 3) * u)| ≤ π ^ 2 / 6 * (c ^ (-(1 : ℝ) / 3) * |u|) := by
        by_cases h0 : c ^ (-(1 : ℝ) / 3) * u = 0
        · rw [h0, show edgePhiDeriv2 0 = 0 by simp [edgePhiDeriv2], abs_zero]; positivity
        · have := (edgePhiDeriv2_abs_le h0).trans (min_le_left _ _)
          rwa [abs_mul, abs_of_pos hς_pos] at this
      have hc1 : c * (c ^ (-(1 : ℝ) / 3)) ^ 2 * c ^ (-(1 : ℝ) / 3) = 1 := by
        have : (c ^ (-(1 : ℝ) / 3)) ^ 2 * c ^ (-(1 : ℝ) / 3) = c ^ (-1 : ℝ) := by
          rw [← pow_succ, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
        rw [mul_assoc, this, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have hpi : π ^ 2 / 6 * |u| ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      calc c * (c ^ (-(1 : ℝ) / 3)) ^ 2 * |edgePhiDeriv2 (c ^ (-(1 : ℝ) / 3) * u)|
          ≤ c * (c ^ (-(1 : ℝ) / 3)) ^ 2 * (π ^ 2 / 6 * (c ^ (-(1 : ℝ) / 3) * |u|)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (c * (c ^ (-(1 : ℝ) / 3)) ^ 2 * c ^ (-(1 : ℝ) / 3)) * (π ^ 2 / 6 * |u|) := by ring
        _ = π ^ 2 / 6 * |u| := by rw [hc1, one_mul]
        _ ≤ 4 := hpi
        _ ≤ max 4 (max C3 C4) := le_max_left _ _
    · -- j = 2: |ψ'''(u)| = |Φ'''(ς u)| ≤ C3
      have hc1 : c * (c ^ (-(1 : ℝ) / 3)) ^ 3 = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num,
          Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
      rw [hc1, one_mul]
      have h3 := hC3 L (c ^ (-(1 : ℝ) / 3) * u)
      have hden : (1 : ℝ) ≤ (1 + |c ^ (-(1 : ℝ) / 3) * u|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg (c ^ (-(1 : ℝ) / 3) * u)])
      calc |iteratedDeriv 3 (edgePhi L) (c ^ (-(1 : ℝ) / 3) * u)|
          ≤ C3 / (1 + |c ^ (-(1 : ℝ) / 3) * u|) ^ 2 := h3
        _ ≤ C3 := div_le_self hC3_nn hden
        _ ≤ max 4 (max C3 C4) := le_trans (le_max_left _ _) (le_max_right _ _)
    · -- j = 3: |ψ^{(4)}(u)| = ς |Φ^{(4)}(ς u)| ≤ C4
      have hc1 : c * (c ^ (-(1 : ℝ) / 3)) ^ 4 = c ^ (-(1 : ℝ) / 3) := by
        have h3 : c * (c ^ (-(1 : ℝ) / 3)) ^ 3 = 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num,
            Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
        calc c * (c ^ (-(1 : ℝ) / 3)) ^ 4 = (c * (c ^ (-(1 : ℝ) / 3)) ^ 3) * c ^ (-(1 : ℝ) / 3) := by ring
          _ = c ^ (-(1 : ℝ) / 3) := by rw [h3, one_mul]
      rw [hc1, abs_mul, abs_of_pos hς_pos]
      have h4 := hC4 L (c ^ (-(1 : ℝ) / 3) * u)
      have hden : (1 : ℝ) ≤ (1 + |c ^ (-(1 : ℝ) / 3) * u|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg (c ^ (-(1 : ℝ) / 3) * u)])
      calc c ^ (-(1 : ℝ) / 3) * |iteratedDeriv 4 (edgePhi L) (c ^ (-(1 : ℝ) / 3) * u)|
          ≤ 1 * (C4 / (1 + |c ^ (-(1 : ℝ) / 3) * u|) ^ 3) :=
            mul_le_mul hς_le h4 (abs_nonneg _) zero_le_one
        _ ≤ C4 := by rw [one_mul]; exact div_le_self hC4_nn hden
        _ ≤ max 4 (max C3 C4) := le_trans (le_max_right _ _) (le_max_right _ _)

/-! ### Inner region bound (`|u| ≤ 5/4`, Pieces 1, 2, 3) -/

set_option maxHeartbeats 400000 in
/-- Bound for the inner region `∫_ℝ exp(i ψ(u)) * chi0(u) * A(ς u) * Y(u) du = O(S^{-α-1})`
for all `c ≥ 1`, `L > 0` with `S = c^{2/3} L ≥ 16`. -/
theorem cusp_inner_bound {α η C_A C_Y : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hη : 0 < η)
    (hCA : 0 ≤ C_A) (hCY : 0 ≤ C_Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c L : ℝ), 1 ≤ c → 16 ≤ c ^ ((2 : ℝ) / 3) * L →
      ∀ (A Y Y₀ R : ℝ → ℂ), CuspAmplitude η C_A A → CuspProfile α C_Y Y Y₀ R →
        ‖∫ u : ℝ, Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
          ((chi0 u : ℂ) * A (c ^ (-(1 : ℝ) / 3) * u) * Y u)‖ ≤
          C * (c ^ ((2 : ℝ) / 3) * L) ^ (-α - 1) := by
  obtain ⟨Bχ, hBχ1, hBχ⟩ := chi0_deriv_bound
  obtain ⟨K_ψ, hK_ψ1, hψ⟩ := scaledPsi_inner_bounds
  -- Constants for Pieces 1, 2, 3
  set C1 := 2 * C_A * C_Y / (α + 1) * (5 / 4 : ℝ) ^ (α + 1)
  set C2 := (104 * K_ψ ^ 3) ^ 3 * 8 * (64 * Bχ * C_A * C_Y) * 4
  set C3 := 2 * ((104 * (8 * K_ψ) ^ 3) ^ 3 * 8 *
    (8 * (8 * (16 * Bχ) * (2 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A) * (8 * C_Y)) *
    ((2 : ℝ) ^ (2 - α) / (2 - α)))
  refine ⟨C1 + C2 + C3, by positivity, fun c L hc hS A Y Y₀ R hA hY => ?_⟩
  have hc0 : 0 < c := by linarith
  set ς : ℝ := c ^ (-(1 : ℝ) / 3)
  set S : ℝ := c ^ ((2 : ℝ) / 3) * L
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have hS_pos : 0 < S := by linarith
  have hS_ge1 : 1 ≤ S := by linarith
  -- Split `chi0 u * Y u = chi0 u * Y₀ u + chi0 u * chi0 (S u) * R u + chi0 u * (1 - chi0 (S u)) * R u`
  -- on `Icc (-2) 2` (outside `|u| ≤ 5/4`, `chi0 u = 0`).
  let f_tot : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((chi0 u : ℂ) * A (ς * u) * Y u)
  let f1 : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
    (((chi0 u * chi0 (S * u) : ℝ) : ℂ) * A (ς * u) * R u)
  let f2 : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
    ((chi0 u : ℂ) * A (ς * u) * Y₀ u)
  let f3 : ℝ → ℂ := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
    (((chi0 u * (1 - chi0 (S * u)) : ℝ) : ℂ) * A (ς * u) * R u)
  have hzero_out : ∀ u : ℝ, 5 / 4 ≤ |u| → f_tot u = 0 ∧ f1 u = 0 ∧ f2 u = 0 ∧ f3 u = 0 := by
    intro u hu
    simp [f_tot, f1, f2, f3, chi0_eq_zero hu]
  have hsplit_pt : ∀ u : ℝ, f_tot u = f1 u + f2 u + f3 u := by
    intro u
    by_cases hu : |u| ≤ 2
    · dsimp only [f_tot, f1, f2, f3]
      rw [hY.decomp u hu]
      push_cast; ring
    · push Not at hu
      have h := hzero_out u (by linarith)
      rw [h.1, h.2.1, h.2.2.1, h.2.2.2]; simp
  have hint_eq_interval : ∀ (g : ℝ → ℂ), (∀ u : ℝ, 2 ≤ |u| → g u = 0) →
      ∫ u : ℝ, g u = ∫ u in (-2 : ℝ)..(2 : ℝ), g u := by
    intro g hg
    rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    rw [← integral_indicator measurableSet_Ioc]
    congr 1; ext u
    by_cases hm : u ∈ Ioc (-2 : ℝ) 2
    · simp [hm]
    · simp only [Set.indicator_of_notMem hm]
      refine hg u ?_
      rw [mem_Ioc] at hm; push Not at hm
      rcases le_or_gt u (-2) with h1 | h1
      · rw [abs_of_nonpos (by linarith)]; linarith
      · have hgt : 2 < u := hm h1
        rw [abs_of_pos (by linarith)]; linarith
  have htot_eq : ∫ u : ℝ, f_tot u = ∫ u in (-2 : ℝ)..(2 : ℝ), f_tot u :=
    hint_eq_interval f_tot fun u hu => (hzero_out u (by linarith)).1
  have hR_cd_all : ContDiffOn ℝ 3 R (Ioo (-2) 2 \ {0}) := by
    have h1 : ContDiffOn ℝ 3 (fun u => Y u - Y₀ u) (Ioo (-2) 2 \ {0}) :=
      (hY.contDiffOn_Y.mono fun u (hu : u ∈ Ioo (-2) 2 \ {0}) => hu.2).sub
        (hY.contDiffOn_Y0.mono fun u (hu : u ∈ Ioo (-2) 2 \ {0}) => hu.1)
    refine h1.congr fun u hu => ?_
    have hu2 : |u| ≤ 2 := (abs_lt.mpr hu.1).le
    have := hY.decomp u hu2
    linear_combination -this
  have hf1_int : IntervalIntegrable f1 volume (-2) 2 := by
    have hopen : IsOpen (Ioo (-2 : ℝ) 2 \ {0}) := isOpen_Ioo.sdiff isClosed_singleton
    have hcont : ContinuousOn f1 (Ioo (-2 : ℝ) 2 \ {0}) := by
      refine (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (contDiff_scaledPsi c L).continuous))).continuousOn.mul ?_
      refine ((Complex.continuous_ofReal.comp (contDiff_chi0.continuous.mul
        (contDiff_chi0.continuous.comp (continuous_const.mul continuous_id)))).continuousOn.mul
        (hA.contDiff.continuous.comp (continuous_const.mul continuous_id)).continuousOn).mul
        hR_cd_all.continuousOn
    have hae_ne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 ∧ u ≠ 2 := by
      have h0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
      have h2 : ∀ᵐ u : ℝ ∂volume, u ≠ 2 := ae_iff.mpr (by simp)
      exact h0.and h2
    have haesm : AEStronglyMeasurable f1 (volume.restrict (uIoc (-2) 2)) := by
      have hrest : (volume.restrict (uIoc (-2 : ℝ) 2)).restrict (Ioo (-2 : ℝ) 2 \ {0}) =
          volume.restrict (uIoc (-2 : ℝ) 2) := by
        refine Measure.restrict_eq_self_of_ae_mem ?_
        rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2), ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hae_ne] with u hu hIoc
        exact ⟨⟨hIoc.1, lt_of_le_of_ne hIoc.2 hu.2⟩, hu.1⟩
      rw [← hrest]
      exact hcont.aestronglyMeasurable hopen.measurableSet
    refine intervalIntegrable_iff.mpr ?_
    refine (integrableOn_const (by rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]; exact measure_Ioc_lt_top.ne) (C := C_A * C_Y * 2 ^ α)).mono' haesm ?_
    rw [uIoc_of_le (by norm_num : (-2 : ℝ) ≤ 2), ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hae_ne] with u hu hIoc
    have hu_lt : |u| < 2 := abs_lt.mpr ⟨hIoc.1, lt_of_le_of_ne hIoc.2 hu.2⟩
    have hu_pos : 0 < |u| := abs_pos.mpr hu.1
    dsimp only [f1]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have hchi : |chi0 u * chi0 (S * u)| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (chi0_nonneg _) (chi0_nonneg _))]
      nlinarith [chi0_le_one u, chi0_nonneg u, chi0_le_one (S * u), chi0_nonneg (S * u)]
    have hA0 : ‖A (ς * u)‖ ≤ C_A := by
      have h := hA.deriv_bound 0 (by omega) (ς * u)
      simp only [iteratedDeriv_zero] at h
      exact h.trans (mul_le_of_le_one_right hCA (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (ς * u)])))
    have hR0 : ‖R u‖ ≤ C_Y * 2 ^ α := by
      have h := hY.R_bound 0 (by omega) u hu_pos hu_lt
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
      exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg u) hu_lt.le hα0.le) hCY)
    calc |chi0 u * chi0 (S * u)| * ‖A (ς * u)‖ * ‖R u‖
        ≤ 1 * C_A * (C_Y * 2 ^ α) := mul_le_mul (mul_le_mul hchi hA0 (norm_nonneg _) zero_le_one) hR0 (norm_nonneg _) (by positivity)
      _ = C_A * C_Y * 2 ^ α := by ring
  have hf2_int : IntervalIntegrable f2 volume (-2) 2 := by
    have hcont : ContinuousOn f2 (Icc (-2) 2) := by
      have hcont_open : ContinuousOn f2 (Ioo (-2) 2) := by
        have h1 : ContinuousOn (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ))) (Ioo (-2) 2) :=
          (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
            (contDiff_scaledPsi c L).continuous))).continuousOn
        have h2 : ContinuousOn (fun u => (chi0 u : ℂ) * A (ς * u) * Y₀ u) (Ioo (-2) 2) :=
          (((Complex.continuous_ofReal.comp contDiff_chi0.continuous).continuousOn).mul
            ((hA.contDiff.continuous.comp (continuous_const.mul continuous_id)).continuousOn)).mul
            hY.contDiffOn_Y0.continuousOn
        exact h1.mul h2
      intro u hu
      by_cases hlt : |u| < 2
      · exact (hcont_open.continuousAt (isOpen_Ioo.mem_nhds (abs_lt.mp hlt))).continuousWithinAt
      · have hge : 5 / 4 < |u| := by
          have : 2 ≤ |u| := not_lt.mp hlt
          linarith
        have hev : f2 =ᶠ[𝓝 u] 0 := by
          filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hge] with y hy
          exact (hzero_out y hy.le).2.2.1
        exact (continuousAt_const.congr hev.symm).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hf3_int : IntervalIntegrable f3 volume (-2) 2 := by
    have hcont : ContinuousOn f3 (Icc (-2) 2) := by
      intro u hu
      by_cases h1 : |u| < 1 / S
      · have hev : f3 =ᶠ[𝓝 u] 0 := by
          filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds h1] with y hy
          have hSy : |S * y| ≤ 1 := by
            rw [abs_mul, abs_of_pos hS_pos]
            exact (le_div_iff₀' hS_pos).mp hy.le
          simp [f3, chi0_eq_one hSy]
        exact (continuousAt_const.congr hev.symm).continuousWithinAt
      · by_cases h2 : 5 / 4 < |u|
        · have hev : f3 =ᶠ[𝓝 u] 0 := by
            filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h2] with y hy
            exact (hzero_out y hy.le).2.2.2
          exact (continuousAt_const.congr hev.symm).continuousWithinAt
        · have hu_mem : u ∈ Ioo (-2 : ℝ) 2 \ {0} := by
            have hle : |u| ≤ 5 / 4 := not_lt.mp h2
            have hge : 1 / S ≤ |u| := not_lt.mp h1
            have hne : u ≠ 0 := by intro h0; subst h0; simp at hge; linarith [div_pos one_pos hS_pos]
            exact ⟨abs_lt.mp (by linarith), hne⟩
          have hopen : IsOpen (Ioo (-2 : ℝ) 2 \ {0}) := isOpen_Ioo.sdiff isClosed_singleton
          have hcont_open : ContinuousOn f3 (Ioo (-2 : ℝ) 2 \ {0}) := by
            refine (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
              (contDiff_scaledPsi c L).continuous))).continuousOn.mul ?_
            refine ((Complex.continuous_ofReal.comp (contDiff_chi0.continuous.mul
              (continuous_const.sub (contDiff_chi0.continuous.comp (continuous_const.mul continuous_id))))).continuousOn.mul
              (hA.contDiff.continuous.comp (continuous_const.mul continuous_id)).continuousOn).mul
              hR_cd_all.continuousOn
          exact (hcont_open.continuousAt (hopen.mem_nhds hu_mem)).continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  rw [htot_eq, intervalIntegral.integral_congr (fun u _ => hsplit_pt u),
    intervalIntegral.integral_add (hf1_int.add hf2_int) hf3_int,
    intervalIntegral.integral_add hf1_int hf2_int]
  -- Bound Piece 1: absolute integration on `|u| ≤ 5/(4S)`
  have hP1 : ‖∫ u in (-2 : ℝ)..(2 : ℝ), f1 u‖ ≤ C1 * S ^ (-α - 1) := by
    set δ : ℝ := 5 / (4 * S)
    have hδ_pos : 0 < δ := by positivity
    have hδ_lt : δ < 2 := by dsimp [δ]; rw [div_lt_iff₀ (by positivity)]; linarith
    have hzero_f1 : ∀ u : ℝ, δ ≤ |u| → f1 u = 0 := by
      intro u hu
      have hSu : 5 / 4 ≤ |S * u| := by
        rw [abs_mul, abs_of_pos hS_pos]
        dsimp [δ] at hu
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * S)).mp hu
        linarith
      simp [f1, chi0_eq_zero hSu]
    have hnorm_le : ∀ u : ℝ, u ∈ Icc (-δ) δ → u ≠ 0 → ‖f1 u‖ ≤ C_A * C_Y * |u| ^ α := by
      intro u hu hne
      have hu_lt : |u| < 2 := lt_of_le_of_lt (abs_le.mpr hu) hδ_lt
      dsimp only [f1]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have hchi : |chi0 u * chi0 (S * u)| ≤ 1 := by
        rw [abs_of_nonneg (mul_nonneg (chi0_nonneg _) (chi0_nonneg _))]
        nlinarith [chi0_le_one u, chi0_nonneg u, chi0_le_one (S * u), chi0_nonneg (S * u)]
      have hA0 : ‖A (ς * u)‖ ≤ C_A := by
        have h := hA.deriv_bound 0 (by omega) (ς * u)
        simp only [iteratedDeriv_zero] at h
        exact h.trans (mul_le_of_le_one_right hCA (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (ς * u)])))
      have hR0 := hY.R_bound 0 (by omega) u (abs_pos.mpr hne) hu_lt
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hR0
      calc |chi0 u * chi0 (S * u)| * ‖A (ς * u)‖ * ‖R u‖
          ≤ 1 * C_A * (C_Y * |u| ^ α) := mul_le_mul (mul_le_mul hchi hA0 (norm_nonneg _) zero_le_one) hR0 (norm_nonneg _) (by positivity)
        _ = C_A * C_Y * |u| ^ α := by ring
    have hdom_int : IntervalIntegrable (fun u : ℝ => C_A * C_Y * |u| ^ α) volume (-δ) δ :=
      (((continuous_abs.rpow_const fun _ => Or.inr hα0.le).continuousOn).const_mul (C_A * C_Y)).intervalIntegrable_of_Icc
        (by linarith)
    have hsplit_eq : ∫ u in (-2 : ℝ)..(2 : ℝ), f1 u = ∫ u in (-δ)..δ, f1 u := by
      have h1 := (intervalIntegral.integral_add_adjacent_intervals (a := (-2 : ℝ)) (b := -δ) (c := 2)
        (hf1_int.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩)))
        (hf1_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩) right_mem_uIcc))).symm
      have h2 := (intervalIntegral.integral_add_adjacent_intervals (a := -δ) (b := δ) (c := 2)
        (hf1_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩)
          (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩)))
        (hf1_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩) right_mem_uIcc))).symm
      have hz1 : ∫ u in (-2 : ℝ)..(-δ), f1 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by linarith)] at hu
          exact hzero_f1 u (by rw [abs_of_neg (by linarith [hu.2])]; linarith [hu.2]),
          intervalIntegral.integral_zero]
      have hz2 : ∫ u in δ..(2 : ℝ), f1 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by linarith)] at hu
          exact hzero_f1 u (by rw [abs_of_pos (by linarith [hu.1])]; linarith [hu.1]),
          intervalIntegral.integral_zero]
      rw [h1, h2, hz1, hz2, zero_add, add_zero]
    rw [hsplit_eq]
    have hval : ∫ u in (-δ)..δ, C_A * C_Y * |u| ^ α = C1 * S ^ (-α - 1) := by
      rw [intervalIntegral.integral_const_mul]
      have heven : ∫ u in (-δ)..δ, |u| ^ α = 2 * ∫ u in (0 : ℝ)..δ, u ^ α := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : ℝ))
          ((continuous_abs.rpow_const fun _ => Or.inr hα0.le).intervalIntegrable (-δ) 0)
          ((continuous_abs.rpow_const fun _ => Or.inr hα0.le).intervalIntegrable 0 δ)]
        have hleft : ∫ u in (-δ)..(0 : ℝ), |u| ^ α = ∫ u in (0 : ℝ)..δ, u ^ α := by
          have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := δ) (f := fun u => |u| ^ α)
          simp only [neg_zero, abs_neg] at h
          rw [← h]
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [uIcc_of_le hδ_pos.le] at hu
          rw [abs_of_nonneg hu.1]
        have hright : ∫ u in (0 : ℝ)..δ, |u| ^ α = ∫ u in (0 : ℝ)..δ, u ^ α :=
          intervalIntegral.integral_congr fun u hu => by
            rw [uIcc_of_le hδ_pos.le] at hu; rw [abs_of_nonneg hu.1]
        rw [hleft, hright]; ring
      rw [heven, integral_rpow (Or.inl (by linarith : -1 < α)), Real.zero_rpow (by linarith), sub_zero]
      dsimp only [C1, δ]
      have hδ_pow : (5 / (4 * S)) ^ (α + 1) = (5 / 4 : ℝ) ^ (α + 1) * S ^ (-α - 1) := by
        rw [show 5 / (4 * S) = (5 / 4) * S⁻¹ by ring, Real.mul_rpow (by norm_num) (by positivity),
          Real.inv_rpow hS_pos.le, ← Real.rpow_neg hS_pos.le]
        congr 2; ring
      rw [hδ_pow]; ring
    calc ‖∫ u in (-δ)..δ, f1 u‖ ≤ ∫ u in (-δ)..δ, ‖f1 u‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ ≤ ∫ u in (-δ)..δ, C_A * C_Y * |u| ^ α := by
          refine intervalIntegral.integral_mono_ae_restrict (by linarith)
            ((hf1_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩)
              (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, by linarith⟩))).norm)
            hdom_int ?_
          show ∀ᵐ u ∂(volume.restrict (Icc (-δ) δ)), ‖f1 u‖ ≤ C_A * C_Y * |u| ^ α
          rw [ae_restrict_iff' measurableSet_Icc]
          have hne0 : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
          filter_upwards [hne0] with u hu hIcc
          exact hnorm_le u hIcc hu
      _ = C1 * S ^ (-α - 1) := hval
  -- Bound Piece 2: 3-fold IBP on `[-3/2, 3/2] ⊂ (-2, 2)`
  have hP2 : ‖∫ u in (-2 : ℝ)..(2 : ℝ), f2 u‖ ≤ C2 * S ^ (-α - 1) := by
    have hsplit_eq : ∫ u in (-2 : ℝ)..(2 : ℝ), f2 u = ∫ u in (-(3 / 2 : ℝ))..(3 / 2 : ℝ), f2 u := by
      have h1 := (intervalIntegral.integral_add_adjacent_intervals (a := (-2 : ℝ)) (b := -(3 / 2)) (c := 2)
        (hf2_int.mono_set (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le (by norm_num)]; norm_num)))
        (hf2_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; norm_num) right_mem_uIcc))).symm
      have h2 := (intervalIntegral.integral_add_adjacent_intervals (a := -(3 / 2 : ℝ)) (b := 3 / 2) (c := 2)
        (hf2_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; norm_num)
          (by rw [uIcc_of_le (by norm_num)]; norm_num)))
        (hf2_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; norm_num) right_mem_uIcc))).symm
      have hz1 : ∫ u in (-2 : ℝ)..(-(3 / 2 : ℝ)), f2 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by norm_num)] at hu
          exact (hzero_out u (by rw [abs_of_neg (by linarith [hu.2])]; linarith [hu.2])).2.2.1,
          intervalIntegral.integral_zero]
      have hz2 : ∫ u in (3 / 2 : ℝ)..(2 : ℝ), f2 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by norm_num)] at hu
          exact (hzero_out u (by rw [abs_of_pos (by linarith [hu.1])]; linarith [hu.1])).2.2.1,
          intervalIntegral.integral_zero]
      rw [h1, h2, hz1, hz2, zero_add, add_zero]
    rw [hsplit_eq]
    let h2 : ℝ → ℂ := fun u => (chi0 u : ℂ) * A (ς * u) * Y₀ u
    have hh2_cd : ContDiffOn ℝ 3 h2 (Ioo (-2) 2) := by
      have h1 : ContDiffOn ℝ 3 (fun u : ℝ => (chi0 u : ℂ)) (Ioo (-2) 2) :=
        ((Complex.ofRealCLM.contDiff.comp contDiff_chi0).of_le (by simp)).contDiffOn
      have h2' : ContDiffOn ℝ 3 (fun u : ℝ => A (ς * u)) (Ioo (-2) 2) :=
        (hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffOn
      exact (h1.mul h2').mul hY.contDiffOn_Y0
    have hvan : ∀ x : ℝ, 5 / 4 < |x| → ∀ j ≤ 2, iteratedDeriv j h2 x = 0 := by
      intro x hx j _
      have hev : h2 =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
        simp [h2, chi0_eq_zero hy.le]
      rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero]
    have hh2_bd : ∀ u ∈ Icc (-(3 / 2 : ℝ)) (3 / 2), ∀ j ≤ 3,
        ‖iteratedDeriv j h2 u‖ ≤ (64 * Bχ * C_A * C_Y) * (1 : ℝ) ^ (-(j : ℤ)) := by
      intro u hu
      have hu_lt : |u| < 2 := by rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
      have hχA := leibniz3_real_mul_bound (f := chi0) (g := fun t => A (ς * t)) (x := u)
        (M₁ := Bχ) (M₂ := C_A) (w := 1)
        (contDiff_chi0.contDiffAt.of_le (by simp))
        ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffAt)
        (by linarith) hCA one_pos
        (fun j hj => by simpa using hBχ j hj u)
        (fun j hj => by
          simp only [one_zpow, mul_one]
          rw [iteratedDeriv_comp_mul_left_C, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hς_pos.le j)]
          have h1 := hA.deriv_bound j hj (ς * u)
          have h2 : ς ^ j ≤ 1 := pow_le_one₀ hς_pos.le hς_le
          have h3 : Real.exp (-η * |ς * u|) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (ς * u)])
          calc ς ^ j * ‖iteratedDeriv j A (ς * u)‖ ≤ 1 * (C_A * 1) :=
                mul_le_mul h2 (h1.trans (mul_le_mul_of_nonneg_left h3 hCA)) (norm_nonneg _) zero_le_one
            _ = C_A := by ring)
      have htot := leibniz3_bound (f := fun t => (chi0 t : ℂ) * A (ς * t)) (g := Y₀) (x := u)
        (M₁ := 8 * Bχ * C_A) (M₂ := C_Y) (w := 1)
        (((Complex.ofRealCLM.contDiff.comp contDiff_chi0).of_le (by simp)).contDiffAt.mul
          ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffAt))
        (hY.contDiffOn_Y0.contDiffAt (isOpen_Ioo.mem_nhds (abs_lt.mp hu_lt)))
        (by positivity) hCY one_pos hχA
        (fun j hj => by simpa using hY.Y0_bound j hj u hu_lt)
      intro j hj
      refine (htot j hj).trans (le_of_eq ?_); ring
    have hibp := ibp3_interval (a := -(3 / 2 : ℝ)) (b := 3 / 2) (by norm_num)
      isOpen_Ioo (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (φ := scaledPsi c L) (h := h2) (B := fun _ => 64 * Bχ * C_A * C_Y) (w := fun _ => 1)
      (Λ := S / 2) (K := K_ψ)
      ((contDiff_scaledPsi c L).of_le (by simp) |>.contDiffOn)
      hh2_cd
      (fun x hx => by
        have h1 := (hψ c L x hc hS (abs_lt.mpr hx).le).1
        linarith)
      (by positivity) hK_ψ1
      (hvan (-(3 / 2)) (by norm_num)) (hvan (3 / 2) (by norm_num))
      (fun _ _ => one_pos) (fun _ _ => by positivity)
      (fun x hx => by
        have h1 := (hψ c L x hc hS (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])).1
        rw [abs_of_pos (by linarith)]; exact h1)
      (fun x hx j hj => by
        have h1 := hψ c L x hc hS (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
        simp only [one_zpow, mul_one]
        have hge1 : 1 ≤ |deriv (scaledPsi c L) x| := by rw [abs_of_pos (by linarith [h1.1])]; linarith [h1.1]
        exact (h1.2 j hj).trans (le_mul_of_one_le_right (by linarith) hge1))
      hh2_bd (intervalIntegrable_const)
    have hS3 : (S / 2) ^ (-3 : ℤ) = 8 * S ^ (-3 : ℝ) := by
      rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, div_pow, inv_div,
        Real.rpow_neg hS_pos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num [div_eq_mul_inv]
    have hS_cmp : S ^ (-3 : ℝ) ≤ S ^ (-α - 1) :=
      Real.rpow_le_rpow_of_exponent_le hS_ge1 (by linarith)
    calc ‖∫ u in (-(3 / 2 : ℝ))..(3 / 2 : ℝ), f2 u‖
        ≤ (104 * K_ψ ^ 3) ^ 3 * (S / 2) ^ (-3 : ℤ) * ∫ _ in (-(3 / 2 : ℝ))..(3 / 2 : ℝ), (64 * Bχ * C_A * C_Y) * (1 : ℝ) ^ (-3 : ℤ) := hibp
      _ = (104 * K_ψ ^ 3) ^ 3 * (8 * S ^ (-3 : ℝ)) * (3 * (64 * Bχ * C_A * C_Y)) := by
          rw [hS3, intervalIntegral.integral_const]; norm_num
      _ ≤ C2 * S ^ (-α - 1) := by
          dsimp only [C2]
          have h34 : (3 : ℝ) ≤ 4 := by norm_num
          have hnn : 0 ≤ (104 * K_ψ ^ 3) ^ 3 * 8 * (64 * Bχ * C_A * C_Y) := by positivity
          calc (104 * K_ψ ^ 3) ^ 3 * (8 * S ^ (-3 : ℝ)) * (3 * (64 * Bχ * C_A * C_Y))
              = ((104 * K_ψ ^ 3) ^ 3 * 8 * (64 * Bχ * C_A * C_Y)) * 3 * S ^ (-3 : ℝ) := by ring
            _ ≤ ((104 * K_ψ ^ 3) ^ 3 * 8 * (64 * Bχ * C_A * C_Y)) * 4 * S ^ (-α - 1) :=
                mul_le_mul (mul_le_mul_of_nonneg_left h34 hnn) hS_cmp (Real.rpow_nonneg hS_pos.le _) (by positivity)
            _ = _ := by ring
  -- Bound Piece 3: 3-fold IBP on `[1/(2S), 3/2]` and `[-3/2, -1/(2S)]`
  have hP3 : ‖∫ u in (-2 : ℝ)..(2 : ℝ), f3 u‖ ≤ C3 * S ^ (-α - 1) := by
    let h3 : ℝ → ℂ := fun u => ((chi0 u * (1 - chi0 (S * u)) : ℝ) : ℂ) * A (ς * u) * R u
    have hh3_cd : ContDiffOn ℝ 3 h3 (Ioo (-2) 2 \ {0}) := by
      have h1 : ContDiffOn ℝ 3 (fun u : ℝ => ((chi0 u * (1 - chi0 (S * u)) : ℝ) : ℂ)) (Ioo (-2) 2 \ {0}) :=
        ((Complex.ofRealCLM.contDiff.comp (contDiff_chi0.mul
          (contDiff_const.sub (contDiff_chi0.comp (contDiff_const.mul contDiff_id))))).of_le (by simp)).contDiffOn
      have h2 : ContDiffOn ℝ 3 (fun u : ℝ => A (ς * u)) (Ioo (-2) 2 \ {0}) :=
        (hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffOn
      exact (h1.mul h2).mul hR_cd_all
    have hvan_inner : ∀ x : ℝ, |x| < 1 / S → ∀ j ≤ 2, iteratedDeriv j h3 x = 0 := by
      intro x hx j _
      have hev : h3 =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
        have hSy : |S * y| ≤ 1 := by
          rw [abs_mul, abs_of_pos hS_pos]
          exact (le_div_iff₀' hS_pos).mp hy.le
        simp [h3, chi0_eq_one hSy]
      rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero]
    have hvan_outer : ∀ x : ℝ, 5 / 4 < |x| → ∀ j ≤ 2, iteratedDeriv j h3 x = 0 := by
      intro x hx j _
      have hev : h3 =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
        simp [h3, chi0_eq_zero hy.le]
      rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero]
    have hh3_bd : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 2 → ∀ j ≤ 3,
        ‖iteratedDeriv j h3 u‖ ≤
          (8 * (8 * (16 * Bχ) * (2 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A) * (8 * C_Y)) *
            |u| ^ α * |u| ^ (-(j : ℤ)) := by
      intro u hu0 hu32
      have hu_lt : |u| < 2 := by linarith
      have hu_ne : u ≠ 0 := abs_pos.mp hu0
      have hcut1 : ∀ j ≤ 3, |iteratedDeriv j (fun t => 1 - chi0 (S * t)) u| ≤ 16 * Bχ * |u| ^ (-(j : ℤ)) := by
        intro j hj
        rcases eq_or_ne j 0 with rfl | hj0
        · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
          have h1 : |1 - chi0 (S * u)| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [chi0_le_one (S * u)])]; linarith [chi0_nonneg (S * u)]
          linarith
        · have hsub_d : iteratedDeriv j (fun t => 1 - chi0 (S * t)) u = -iteratedDeriv j (fun t => chi0 (S * t)) u := by
            have h1 := iteratedDeriv_sub (n := j) (x := u) (contDiffAt_const (c := (1 : ℝ)))
              ((contDiff_chi0.comp (contDiff_const (c := S) |>.mul contDiff_id)).contDiffAt.of_le (by simp))
            dsimp only [Function.comp_def, id_eq] at h1
            have hc0' : iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) u = 0 := by
              obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
              rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => (1 : ℝ)) = 0 from funext fun _ => deriv_const _ _,
                iteratedDeriv_const_zero]
            rw [show (fun t => 1 - chi0 (S * t)) = (fun _ => (1 : ℝ)) - (fun t => chi0 (S * t)) from rfl, h1,
              hc0', zero_sub]
          rw [hsub_d, abs_neg, iteratedDeriv_comp_mul_left_R, abs_mul, abs_of_pos (pow_pos hS_pos j)]
          by_cases hSu : |S * u| ≤ 5 / 4
          · have hSu' : S * |u| ≤ 5 / 4 := by rwa [abs_mul, abs_of_pos hS_pos] at hSu
            have hpow_le : (S * |u|) ^ j ≤ 16 := by
              calc (S * |u|) ^ j ≤ (5 / 4 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) hSu' j
                _ ≤ (5 / 4 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj
                _ ≤ 16 := by norm_num
            have hSj : S ^ j = (S * |u|) ^ j * |u| ^ (-(j : ℤ)) := by
              have hne : |u| ^ j ≠ 0 := pow_ne_zero j hu0.ne'
              rw [mul_pow S |u| j, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel₀ hne, mul_one]
            rw [hSj]
            calc (S * |u|) ^ j * |u| ^ (-(j : ℤ)) * |iteratedDeriv j chi0 (S * u)|
                ≤ 16 * |u| ^ (-(j : ℤ)) * Bχ :=
                  mul_le_mul (mul_le_mul_of_nonneg_right hpow_le (by positivity)) (hBχ j hj (S * u))
                    (abs_nonneg _) (by positivity)
              _ = 16 * Bχ * |u| ^ (-(j : ℤ)) := by ring
          · push Not at hSu
            have hev : chi0 =ᶠ[𝓝 (S * u)] 0 := by
              filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hSu] with y hy
              exact chi0_eq_zero hy.le
            rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, abs_zero, mul_zero]
            positivity
      have hcut0 : ∀ j ≤ 3, |iteratedDeriv j chi0 u| ≤ 2 * Bχ * |u| ^ (-(j : ℤ)) := by
        intro j hj
        rcases eq_or_ne j 0 with rfl | hj0
        · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
          have h0 := hBχ 0 (by omega) u
          simp only [iteratedDeriv_zero] at h0
          linarith
        · by_cases h54 : |u| ≤ 5 / 4
          · have hpow : |u| ^ j ≤ 2 := by
              calc |u| ^ j ≤ (5 / 4 : ℝ) ^ j := pow_le_pow_left₀ (abs_nonneg u) h54 j
                _ ≤ (5 / 4 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj
                _ ≤ 2 := by norm_num
            have h1 : (1 : ℝ) ≤ 2 * |u| ^ (-(j : ℤ)) := by
              rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, one_le_div (pow_pos hu0 j)]
              exact hpow
            calc |iteratedDeriv j chi0 u| ≤ Bχ * 1 := by rw [mul_one]; exact hBχ j hj u
              _ ≤ Bχ * (2 * |u| ^ (-(j : ℤ))) := mul_le_mul_of_nonneg_left h1 (by linarith)
              _ = 2 * Bχ * |u| ^ (-(j : ℤ)) := by ring
          · push Not at h54
            have hev : chi0 =ᶠ[𝓝 u] 0 := by
              filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h54] with y hy
              exact chi0_eq_zero hy.le
            rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, abs_zero]
            positivity
      have hcut_prod := leibniz3_real_mul_bound (f := chi0)
        (g := fun t => ((1 - chi0 (S * t) : ℝ) : ℂ)) (x := u)
        (M₁ := 2 * Bχ) (M₂ := 16 * Bχ) (w := |u|)
        (contDiff_chi0.contDiffAt.of_le (by simp))
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_chi0.comp (contDiff_const.mul contDiff_id)))).contDiffAt.of_le (by simp))
        (by positivity) (by positivity) hu0 hcut0
        (fun j hj => by
          rw [iteratedDeriv_ofReal_eq', Complex.norm_real, Real.norm_eq_abs]
          exact hcut1 j hj)
      have hcut_eq : (fun t => ((chi0 t * (1 - chi0 (S * t)) : ℝ) : ℂ)) =
          fun t => (chi0 t : ℂ) * ((1 - chi0 (S * t) : ℝ) : ℂ) := by
        ext t; push_cast; rfl
      have hA_bd : ∀ j ≤ 3, ‖iteratedDeriv j (fun t => A (ς * t)) u‖ ≤
          (6 * max 1 ((2 / η) ^ 3) * C_A) * |u| ^ (-(j : ℤ)) := by
        intro j hj
        have h := scaled_amp_deriv_bound hη hCA hς_pos hA hu_ne j hj
        have hexp : Real.exp (-(η / 2) * ς * |u|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have hnn : 0 ≤ (η / 2) * ς * |u| := by positivity
            linarith)
        calc ‖iteratedDeriv j (fun t => A (ς * t)) u‖
            ≤ (6 * max 1 ((2 / η) ^ 3)) * C_A * Real.exp (-(η / 2) * ς * |u|) * |u| ^ (-(j : ℤ)) := h
          _ ≤ (6 * max 1 ((2 / η) ^ 3)) * C_A * 1 * |u| ^ (-(j : ℤ)) := by gcongr
          _ = (6 * max 1 ((2 / η) ^ 3) * C_A) * |u| ^ (-(j : ℤ)) := by ring
      have hR_bd' : ∀ j ≤ 3, ‖iteratedDeriv j R u‖ ≤ (C_Y * |u| ^ α) * |u| ^ (-(j : ℤ)) := by
        intro j hj
        have h := hY.R_bound j hj u hu0 hu_lt
        have hrpow : |u| ^ (α - (j : ℝ)) = |u| ^ α * |u| ^ (-(j : ℤ)) := by
          rw [Real.rpow_sub hu0, Real.rpow_natCast, zpow_neg, zpow_natCast, div_eq_mul_inv]
        rw [hrpow] at h
        linarith
      have h12 := leibniz3_bound (f := fun t => ((chi0 t * (1 - chi0 (S * t)) : ℝ) : ℂ))
        (g := fun t => A (ς * t)) (x := u)
        (M₁ := 8 * (2 * Bχ) * (16 * Bχ)) (M₂ := 6 * max 1 ((2 / η) ^ 3) * C_A) (w := |u|)
        (by
          rw [hcut_eq]
          exact ((Complex.ofRealCLM.contDiff.comp contDiff_chi0).contDiffAt.of_le (by simp)).mul
            ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_chi0.comp (contDiff_const.mul contDiff_id)))).contDiffAt.of_le (by simp)))
        ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffAt)
        (by positivity) (by positivity) hu0
        (by rw [hcut_eq]; exact hcut_prod) hA_bd
      have h123 := leibniz3_bound
        (f := fun t => ((chi0 t * (1 - chi0 (S * t)) : ℝ) : ℂ) * A (ς * t))
        (g := R) (x := u)
        (M₁ := 8 * (8 * (2 * Bχ) * (16 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A))
        (M₂ := C_Y * |u| ^ α) (w := |u|)
        (by
          refine ContDiffAt.mul ?_ ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffAt)
          rw [hcut_eq]
          exact ((Complex.ofRealCLM.contDiff.comp contDiff_chi0).contDiffAt.of_le (by simp)).mul
            ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_chi0.comp (contDiff_const.mul contDiff_id)))).contDiffAt.of_le (by simp)))
        (hR_cd_all.contDiffAt ((isOpen_Ioo.sdiff isClosed_singleton).mem_nhds ⟨abs_lt.mp hu_lt, hu_ne⟩))
        (by positivity) (by positivity) hu0 h12 hR_bd'
      intro j hj
      refine (h123 j hj).trans (le_of_eq ?_); ring
    set ε : ℝ := 1 / (2 * S)
    have hε_pos : 0 < ε := by positivity
    have hε_lt : ε < 3 / 2 := by dsimp [ε]; rw [div_lt_iff₀ (by positivity)]; linarith
    have hsplit3 : ∫ u in (-2 : ℝ)..(2 : ℝ), f3 u =
        (∫ u in (-(3 / 2 : ℝ))..(-ε), f3 u) + (∫ u in ε..(3 / 2 : ℝ), f3 u) := by
      have hsub : ∀ p q : ℝ, -2 ≤ p → p ≤ q → q ≤ 2 → IntervalIntegrable f3 volume p q := fun p q hp hpq hq =>
        hf3_int.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (by norm_num)]; exact ⟨hp, by linarith⟩)
          (by rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, hq⟩))
      have ha1 := (intervalIntegral.integral_add_adjacent_intervals (hsub (-2) (-(3 / 2)) le_rfl (by norm_num) (by norm_num))
        (hsub (-(3 / 2)) 2 (by norm_num) (by norm_num) le_rfl)).symm
      have ha2 := (intervalIntegral.integral_add_adjacent_intervals (hsub (-(3 / 2)) (-ε) (by norm_num) (by linarith) (by linarith))
        (hsub (-ε) 2 (by linarith) (by linarith) le_rfl)).symm
      have ha3 := (intervalIntegral.integral_add_adjacent_intervals (hsub (-ε) ε (by linarith) (by linarith) (by linarith))
        (hsub ε 2 (by linarith) (by linarith) le_rfl)).symm
      have ha4 := (intervalIntegral.integral_add_adjacent_intervals (hsub ε (3 / 2) (by linarith) hε_lt.le (by norm_num))
        (hsub (3 / 2) 2 (by norm_num) (by norm_num) le_rfl)).symm
      have hz1 : ∫ u in (-2 : ℝ)..(-(3 / 2 : ℝ)), f3 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by norm_num)] at hu
          exact (hzero_out u (by rw [abs_of_neg (by linarith [hu.2])]; linarith [hu.2])).2.2.2,
          intervalIntegral.integral_zero]
      have hz2 : ∫ u in (-ε)..ε, f3 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by linarith)] at hu
          have hSy : |S * u| ≤ 1 := by
            rw [abs_mul, abs_of_pos hS_pos]
            have hu' : |u| ≤ ε := abs_le.mpr hu
            dsimp [ε] at hu'
            have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * S)).mp hu'
            linarith
          simp [f3, chi0_eq_one hSy], intervalIntegral.integral_zero]
      have hz3 : ∫ u in (3 / 2 : ℝ)..(2 : ℝ), f3 u = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun u hu => by
          rw [uIcc_of_le (by norm_num)] at hu
          exact (hzero_out u (by rw [abs_of_pos (by linarith [hu.1])]; linarith [hu.1])).2.2.2,
          intervalIntegral.integral_zero]
      rw [ha1, ha2, ha3, ha4, hz1, hz2, hz3]; simp
    set M3 := 8 * (8 * (16 * Bχ) * (2 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A) * (8 * C_Y)
    have hibp_half : ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ Ioo (-2) 2 \ {0} →
        (∀ x ∈ Icc a b, ε ≤ |x| ∧ |x| ≤ 3 / 2) →
        (∀ j ≤ 2, iteratedDeriv j h3 a = 0) → (∀ j ≤ 2, iteratedDeriv j h3 b = 0) →
        ‖∫ u in a..b, f3 u‖ ≤ (104 * (8 * K_ψ) ^ 3) ^ 3 * (S / 2) ^ (-3 : ℤ) *
          ∫ u in a..b, M3 * |u| ^ α * |u| ^ (-3 : ℤ) := by
      intro a b hab hsub hrange hva hvb
      refine ibp3_interval hab (isOpen_Ioo.sdiff isClosed_singleton) hsub
        (φ := scaledPsi c L) (h := h3) (B := fun u => M3 * |u| ^ α) (w := fun u => |u|)
        (Λ := S / 2) (K := 8 * K_ψ)
        (((contDiff_scaledPsi c L).of_le (by simp)).contDiffOn)
        hh3_cd
        (fun x hx => by
          have h1 := (hψ c L x hc hS (abs_lt.mpr hx.1).le).1; linarith)
        (by positivity) (by linarith) hva hvb
        (fun x hx => lt_of_lt_of_le hε_pos (hrange x hx).1)
        (fun x _ => by positivity)
        (fun x hx => by
          have h1 := (hψ c L x hc hS (by linarith [(hrange x hx).2])).1
          rw [abs_of_pos (by linarith)]; exact h1)
        (fun x hx j hj => by
          have h1 := hψ c L x hc hS (by linarith [(hrange x hx).2])
          have hge1 : 1 ≤ |deriv (scaledPsi c L) x| := by rw [abs_of_pos (by linarith [h1.1])]; linarith [h1.1]
          have hxj : |x| ^ j ≤ 8 := by
            have hj3 : j ≤ 3 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl <;> omega
            calc |x| ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ (abs_nonneg x) (hrange x hx).2 j
              _ ≤ (3 / 2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj3
              _ ≤ 8 := by norm_num
          have hpos_x : 0 < |x| := lt_of_lt_of_le hε_pos (hrange x hx).1
          have hw_ge : 1 ≤ 8 * |x| ^ (-(j : ℤ)) := by
            rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, one_le_div (pow_pos hpos_x j)]
            exact hxj
          calc |iteratedDeriv (j + 1) (scaledPsi c L) x| ≤ K_ψ * 1 * 1 := by simpa using h1.2 j hj
            _ ≤ K_ψ * (8 * |x| ^ (-(j : ℤ))) * |deriv (scaledPsi c L) x| := by gcongr
            _ = 8 * K_ψ * |x| ^ (-(j : ℤ)) * |deriv (scaledPsi c L) x| := by ring)
        (fun x hx => hh3_bd x (lt_of_lt_of_le hε_pos (hrange x hx).1) (hrange x hx).2)
        (by
          have hcont : ContinuousOn (fun u : ℝ => M3 * |u| ^ α * |u| ^ (-3 : ℤ)) (Icc a b) := by
            refine (continuousOn_const.mul (continuous_abs.rpow_const fun _ => Or.inr hα0.le).continuousOn).mul ?_
            exact continuousOn_id.abs.zpow₀ (-3) fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε_pos (hrange x hx).1))
          exact hcont.intervalIntegrable_of_Icc hab)
    have hint_pos : ∫ u in ε..(3 / 2 : ℝ), M3 * |u| ^ α * |u| ^ (-3 : ℤ) ≤
        M3 * ((2 : ℝ) ^ (2 - α) / (2 - α) * S ^ (2 - α)) := by
      have hcongr : ∫ u in ε..(3 / 2 : ℝ), M3 * |u| ^ α * |u| ^ (-3 : ℤ) =
          M3 * ∫ u in ε..(3 / 2 : ℝ), u ^ (α - 3) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [uIcc_of_le hε_lt.le] at hu
        have hu0 : 0 < u := lt_of_lt_of_le hε_pos hu.1
        rw [abs_of_pos hu0, zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast,
          ← Real.rpow_natCast u 3, ← Real.rpow_neg hu0.le, mul_assoc, ← Real.rpow_add hu0,
          show α + -(3 : ℕ) = α - 3 by push_cast; ring]
      rw [hcongr, integral_rpow (Or.inr ⟨by linarith, fun h => by
        rw [uIcc_of_le hε_lt.le] at h; linarith [h.1]⟩)]
      have hnum : ((3 / 2 : ℝ) ^ (α - 3 + 1) - ε ^ (α - 3 + 1)) / (α - 3 + 1) ≤
          (2 : ℝ) ^ (2 - α) / (2 - α) * S ^ (2 - α) := by
        have hneg : α - 3 + 1 = -(2 - α) := by ring
        have hpos2 : 0 < 2 - α := by linarith
        rw [hneg, div_neg]
        have h1 : 0 ≤ (3 / 2 : ℝ) ^ (-(2 - α)) := Real.rpow_nonneg (by norm_num) _
        have h2 : ε ^ (-(2 - α)) = (2 : ℝ) ^ (2 - α) * S ^ (2 - α) := by
          dsimp [ε]
          rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
            Real.mul_rpow (by norm_num) hS_pos.le]
        rw [← neg_div, neg_sub, h2, sub_div, mul_div_right_comm]
        have : 0 ≤ (3 / 2 : ℝ) ^ (-(2 - α)) / (2 - α) := by positivity
        linarith
      exact mul_le_mul_of_nonneg_left hnum (by positivity)
    have hint_neg : ∫ u in (-(3 / 2 : ℝ))..(-ε), M3 * |u| ^ α * |u| ^ (-3 : ℤ) =
        ∫ u in ε..(3 / 2 : ℝ), M3 * |u| ^ α * |u| ^ (-3 : ℤ) := by
      have h := intervalIntegral.integral_comp_neg (a := ε) (b := 3 / 2)
        (f := fun u => M3 * |u| ^ α * |u| ^ (-3 : ℤ))
      simpa only [abs_neg] using h.symm
    have hpos_bd := hibp_half ε (3 / 2) hε_lt.le
      (fun x hx => ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ne_of_gt (lt_of_lt_of_le hε_pos hx.1)⟩)
      (fun x hx => by rw [abs_of_pos (lt_of_lt_of_le hε_pos hx.1)]; exact hx)
      (hvan_inner ε (by rw [abs_of_pos hε_pos]; dsimp [ε]; field_simp [hS_pos.ne']; norm_num))
      (hvan_outer (3 / 2) (by norm_num))
    have hneg_bd := hibp_half (-(3 / 2)) (-ε) (by linarith)
      (fun x hx => ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ne_of_lt (by linarith [hx.2])⟩)
      (fun x hx => by rw [abs_of_neg (by linarith [hx.2])]; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (hvan_outer (-(3 / 2)) (by norm_num))
      (hvan_inner (-ε) (by rw [abs_neg, abs_of_pos hε_pos]; dsimp [ε]; field_simp [hS_pos.ne']; norm_num))
    rw [hint_neg] at hneg_bd
    have hS_pow : (S / 2) ^ (-3 : ℤ) * S ^ (2 - α) = 8 * S ^ (-α - 1) := by
      have h1 : (S / 2) ^ (-3 : ℤ) = 8 * S ^ (-(3 : ℝ)) := by
        rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, div_pow, inv_div,
          Real.rpow_neg hS_pos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num [div_eq_mul_inv]
      rw [h1, mul_assoc, ← Real.rpow_add hS_pos]
      congr 2; ring
    rw [hsplit3]
    calc ‖(∫ u in (-(3 / 2 : ℝ))..(-ε), f3 u) + ∫ u in ε..(3 / 2 : ℝ), f3 u‖
        ≤ ‖∫ u in (-(3 / 2 : ℝ))..(-ε), f3 u‖ + ‖∫ u in ε..(3 / 2 : ℝ), f3 u‖ := norm_add_le _ _
      _ ≤ 2 * ((104 * (8 * K_ψ) ^ 3) ^ 3 * (S / 2) ^ (-3 : ℤ) *
            ∫ u in ε..(3 / 2 : ℝ), M3 * |u| ^ α * |u| ^ (-3 : ℤ)) := by linarith
      _ ≤ 2 * ((104 * (8 * K_ψ) ^ 3) ^ 3 * (S / 2) ^ (-3 : ℤ) *
            (M3 * ((2 : ℝ) ^ (2 - α) / (2 - α) * S ^ (2 - α)))) := by
          gcongr
      _ = C3 * S ^ (-α - 1) := by
          dsimp only [C3, M3]
          calc 2 * ((104 * (8 * K_ψ) ^ 3) ^ 3 * (S / 2) ^ (-3 : ℤ) *
                (8 * (8 * (16 * Bχ) * (2 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A) * (8 * C_Y) *
                ((2 : ℝ) ^ (2 - α) / (2 - α) * S ^ (2 - α))))
              = 2 * ((104 * (8 * K_ψ) ^ 3) ^ 3 *
                (8 * (8 * (16 * Bχ) * (2 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A) * (8 * C_Y)) *
                ((2 : ℝ) ^ (2 - α) / (2 - α))) * ((S / 2) ^ (-3 : ℤ) * S ^ (2 - α)) := by ring
            _ = 2 * ((104 * (8 * K_ψ) ^ 3) ^ 3 *
                (8 * (8 * (16 * Bχ) * (2 * Bχ)) * (6 * max 1 ((2 / η) ^ 3) * C_A) * (8 * C_Y)) *
                ((2 : ℝ) ^ (2 - α) / (2 - α))) * (8 * S ^ (-α - 1)) := by rw [hS_pow]
            _ = _ := by ring
  calc ‖(∫ u in (-2 : ℝ)..(2 : ℝ), f1 u) + (∫ u in (-2 : ℝ)..(2 : ℝ), f2 u) +
          ∫ u in (-2 : ℝ)..(2 : ℝ), f3 u‖
      ≤ ‖(∫ u in (-2 : ℝ)..(2 : ℝ), f1 u) + ∫ u in (-2 : ℝ)..(2 : ℝ), f2 u‖ +
          ‖∫ u in (-2 : ℝ)..(2 : ℝ), f3 u‖ := norm_add_le _ _
    _ ≤ ‖∫ u in (-2 : ℝ)..(2 : ℝ), f1 u‖ + ‖∫ u in (-2 : ℝ)..(2 : ℝ), f2 u‖ +
          ‖∫ u in (-2 : ℝ)..(2 : ℝ), f3 u‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ C1 * S ^ (-α - 1) + C2 * S ^ (-α - 1) + C3 * S ^ (-α - 1) := by linarith
    _ = (C1 + C2 + C3) * S ^ (-α - 1) := by ring

end FormalResearch.SignUncertainty.FctCuspEdge
