module

public import FormalResearch.SignUncertainty.CtOuterCutoff

/-!
# The far part of a compactly supported amplitude

**Proved.**  For `a` integrable and supported in `[-2, 2]`, `φ(τ) = ∫ a(t)/sinh(π(t-τ)) dt` extends to the holomorphic
function `Φ(z) = ∫ a(t)/sinh(π(t-z)) dt` on `Re z > 3`, with `|Φ(z)| ≤ 4 e^{2π} e^{-π Re z} ‖a‖₁`; hence
`|φ^{(n)}(τ)| ≤ K_n e^{-πτ}` for `τ ≥ 4` (Cauchy estimates).  For `τ > 2`, `F_a(τ) = φ(τ)`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- Cauchy estimate for the real iterated derivatives of a function with a holomorphic extension. -/
lemma cauchy_real {f : ℝ → ℝ} {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hfF : ∀ t : ℝ, (t : ℂ) ∈ U → F (t : ℂ) = ((f t : ℝ) : ℂ)) {t r M : ℝ} (hr : 0 < r)
    (hsub : closedBall (t : ℂ) r ⊆ U) (hM : ∀ z ∈ sphere (t : ℂ) r, ‖F z‖ ≤ M) (n : ℕ) :
    |iteratedDeriv n f t| ≤ n.factorial * M / r ^ n := by
  have htU : (t : ℂ) ∈ U := hsub (mem_closedBall_self hr.le)
  have h := iteratedDeriv_ofReal_eq hU hF hfF n t htU
  have hdc : DiffContOnCl ℂ F (ball (t : ℂ) r) := by
    have : DifferentiableOn ℂ F (closure (ball (t : ℂ) r)) := by
      rw [closure_ball _ hr.ne']
      exact hF.mono hsub
    exact this.diffContOnCl
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdc hM
  have h2 : |iteratedDeriv n f t| = ‖iteratedDeriv n F (t : ℂ)‖ := by
    rw [← h, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  exact hC

/-- `Φ(z) = ∫ a(t) / sinh(π(t - z)) dt`. -/
noncomputable def Phi0 (a : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, ((a t : ℝ) : ℂ) / Complex.sinh (π * ((t : ℂ) - z))

/-- The real-variable function. -/
noncomputable def phi0 (a : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ t : ℝ, a t / Real.sinh (π * (t - τ))

lemma norm_sinh_far {t : ℝ} (ht : |t| ≤ 2) {z : ℂ} (hz : 3 ≤ z.re) :
    Real.exp (π * (z.re - 2)) / 4 ≤ ‖Complex.sinh (π * ((t : ℂ) - z))‖ := by
  have h := norm_sinh_ge ((π : ℂ) * ((t : ℂ) - z))
  have hre : ((π : ℂ) * ((t : ℂ) - z)).re = π * (t - z.re) := by
    simp [Complex.mul_re]
  rw [hre] at h
  have ht2 := (abs_le.mp ht).2
  have hpos : π * (t - z.re) ≤ 0 := by nlinarith only [Real.pi_pos, ht2, hz]
  rw [abs_of_nonpos hpos] at h
  have h1 : 1 ≤ -(π * (t - z.re)) := by nlinarith only [Real.pi_gt_three, ht2, hz]
  have h2 := exp_div_four_le_sinh h1
  have h3 : Real.exp (π * (z.re - 2)) ≤ Real.exp (-(π * (t - z.re))) := by
    apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, ht2]
  linarith only [h, h2, h3, show Real.exp (π * (z.re - 2)) / 4 ≤ Real.exp (-(π * (t - z.re))) / 4 by linarith]

lemma term_bound {a : ℝ → ℝ} (ha : ∀ t, 2 < |t| → a t = 0) (t : ℝ) {z : ℂ} (hz : 3 ≤ z.re) :
    ‖((a t : ℝ) : ℂ) / Complex.sinh (π * ((t : ℂ) - z))‖ ≤
      (4 * Real.exp (2 * π) * Real.exp (-π * z.re)) * |a t| := by
  by_cases h0 : a t = 0
  · simp [h0]
  have ht : |t| ≤ 2 := by by_contra h; exact h0 (ha t (not_le.mp h))
  have hlow := norm_sinh_far ht hz
  have hpos : 0 < Real.exp (π * (z.re - 2)) / 4 := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [div_le_iff₀ (hpos.trans_le hlow)]
  have e : Real.exp (2 * π) * Real.exp (-π * z.re) * Real.exp (π * (z.re - 2)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; simp
  calc |a t| = (4 * Real.exp (2 * π) * Real.exp (-π * z.re)) * |a t| * (Real.exp (π * (z.re - 2)) / 4) := by
        have : 4 * Real.exp (2 * π) * Real.exp (-π * z.re) * |a t| * (Real.exp (π * (z.re - 2)) / 4) =
            (Real.exp (2 * π) * Real.exp (-π * z.re) * Real.exp (π * (z.re - 2))) * |a t| := by ring
        rw [this, e, one_mul]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hlow (by positivity)

lemma differentiableOn_Phi0 {a : ℝ → ℝ} (hm : Measurable a) (hi : Integrable a)
    (ha : ∀ t, 2 < |t| → a t = 0) : DifferentiableOn ℂ (Phi0 a) {z : ℂ | 3 < z.re} := by
  have hU : IsOpen {z : ℂ | 3 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine differentiableOn_integral_param (μ := volume)
    (Φ := fun w t => ((a t : ℝ) : ℂ) / Complex.sinh (π * ((t : ℂ) - w))) hU ?_ ?_ ?_
  · intro w _
    exact ((Complex.measurable_ofReal.comp hm).div
      (Complex.continuous_sinh.measurable.comp (by fun_prop : Measurable fun t : ℝ => (π : ℂ) * ((t : ℂ) - w)))).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    by_cases h0 : a t = 0
    · simp [h0]
    have ht : |t| ≤ 2 := by by_contra h; exact h0 (ha t (not_le.mp h))
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) (fun w hw => ?_)
    have hlow := norm_sinh_far ht (le_of_lt (show 3 < w.re from hw))
    have : 0 < ‖Complex.sinh (π * ((t : ℂ) - w))‖ := lt_of_lt_of_le (by positivity) hlow
    exact norm_pos_iff.mp this
  · intro w₀ hw₀
    have hw0 : (3 : ℝ) < w₀.re := hw₀
    refine ⟨w₀.re - 3, by linarith, fun t => (4 * Real.exp (2 * π) * Real.exp (-π * 3)) * |a t|, ?_, ?_⟩
    · exact hi.abs.const_mul _
    · refine Eventually.of_forall fun t w hw => ?_
      have hwre : 3 < w.re := by
        have := Complex.abs_re_le_norm (w - w₀)
        have hd : ‖w - w₀‖ < w₀.re - 3 := by simpa [dist_eq_norm] using hw
        simp only [Complex.sub_re] at this
        linarith [(abs_le.mp this).1]
      refine (term_bound ha t hwre.le).trans ?_
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, hwre]

lemma norm_Phi0_le {a : ℝ → ℝ} (hi : Integrable a) (ha : ∀ t, 2 < |t| → a t = 0) {z : ℂ} (hz : 3 ≤ z.re) :
    ‖Phi0 a z‖ ≤ (4 * Real.exp (2 * π) * Real.exp (-π * z.re)) * ∫ t : ℝ, |a t| := by
  unfold Phi0
  have h := norm_integral_le_of_norm_le (hi.abs.const_mul (4 * Real.exp (2 * π) * Real.exp (-π * z.re)))
    (Eventually.of_forall fun t => term_bound ha t hz)
  rwa [integral_const_mul] at h

lemma Phi0_ofReal (a : ℝ → ℝ) (τ : ℝ) : Phi0 a (τ : ℂ) = ((phi0 a τ : ℝ) : ℂ) := by
  unfold Phi0 phi0
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [Complex.ofReal_div, Complex.ofReal_sinh]
  push_cast
  rfl

theorem phi0_deriv_bound {a : ℝ → ℝ} (hm : Measurable a) (hi : Integrable a) (ha : ∀ t, 2 < |t| → a t = 0)
    (n : ℕ) : ∃ K : ℝ, ∀ τ : ℝ, 4 ≤ τ → |iteratedDeriv n (phi0 a) τ| ≤ K * Real.exp (-π * τ) := by
  set I : ℝ := ∫ t : ℝ, |a t| with hI
  have hI0 : 0 ≤ I := integral_nonneg (fun t => abs_nonneg _)
  refine ⟨n.factorial * (4 * Real.exp (2 * π) * Real.exp (π / 2) * I) / (1 / 2) ^ n, fun τ hτ => ?_⟩
  have hU : IsOpen {z : ℂ | 3 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsub : closedBall (τ : ℂ) (1 / 2) ⊆ {z : ℂ | 3 < z.re} := by
    intro z hz
    have hd : ‖z - τ‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - τ)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 3 < z.re
    linarith [(abs_le.mp (this.trans hd)).1]
  have hM : ∀ z ∈ sphere (τ : ℂ) (1 / 2), ‖Phi0 a z‖ ≤ 4 * Real.exp (2 * π) * Real.exp (π / 2) * I * Real.exp (-π * τ) := by
    intro z hz
    have hd : ‖z - τ‖ = 1 / 2 := by simpa [dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - τ)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    have hre : τ - 1 / 2 ≤ z.re := by linarith [(abs_le.mp (this.trans hd.le)).1]
    refine (norm_Phi0_le hi ha (by linarith)).trans ?_
    have : Real.exp (-π * z.re) ≤ Real.exp (π / 2) * Real.exp (-π * τ) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, hre]
    calc 4 * Real.exp (2 * π) * Real.exp (-π * z.re) * I ≤ 4 * Real.exp (2 * π) * (Real.exp (π / 2) * Real.exp (-π * τ)) * I := by
          gcongr
      _ = _ := by ring
  have h := cauchy_real (f := phi0 a) hU (differentiableOn_Phi0 hm hi ha)
    (fun t _ => Phi0_ofReal a t) (by norm_num : (0 : ℝ) < 1 / 2) hsub hM n
  refine h.trans (le_of_eq ?_)
  ring

/-- For `τ > 2`, `F_a(τ) = φ(τ)` when `a` is supported in `[-2,2]`. -/
lemma bdryF_eq_phi0 {a : ℝ → ℝ} (ha : ∀ t, 2 < |t| → a t = 0) {τ : ℝ} (hτ : 2 < τ) :
    bdryF a τ = phi0 a τ := by
  unfold bdryF phi0
  have : a τ = 0 := ha τ (by rwa [abs_of_pos (by linarith)])
  simp [this]

/-- info: 'FormalResearch.SignUncertainty.CtOuter.phi0_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phi0_deriv_bound

end FormalResearch.SignUncertainty.CtOuter
