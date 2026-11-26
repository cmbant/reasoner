module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasHankelCoeff

/-!
# `ct:boas` Step 3: the negative part of the Gaussian-windowed Hankel density

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 3 ("the negative part satisfies
`‖g₋‖₁ ≤ e^{-(L₀-L_T)²/(2W_j²)}`").  For `f` feasible at threshold `T`, `h = hankelHL c f` (the log-density in
`L = log π²ξ`) satisfies `h ≥ 0` for `L ≥ L_T` (`c e^L/π² ≥ T`) and `∫|h| = M[f]`
(`integral_abs_hankelHL`), hence, for `L₀ ≥ L_T` and `g = G_W(· - L₀) h` (normalised Gaussian),
`∫ g₋ ≤ M[f] e^{-(L₀-L_T)²/(2W²)}/(√(2π)W)` (`hankel_window_neg_le`).

**Proved**, unconditional.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

/-- `h ≥ 0` where `c e^L/π² ≥ T` (feasibility). -/
theorem hankelHL_nonneg_of_tail {c ε T : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) {L : ℝ}
    (hL : T ≤ c * (Real.exp L / π ^ 2)) : 0 ≤ hankelHL c f L := by
  unfold hankelHL
  have hφ : 0 < Real.exp L / π ^ 2 := by positivity
  have h1 := hf.tail_nonneg _ hL
  have h2 := hankelRho0_nonneg hc (by positivity : 0 ≤ c * (Real.exp L / π ^ 2))
  positivity

/-- `∫_ℝ |h| = M[f]`. -/
theorem integral_abs_hankelHL {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ∫ L, |hankelHL c f L| = hankelMass c f := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set φ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hφ
  have himg : φ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hφ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt φ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn φ univ := by
    intro a _ b _ hab
    simp only [hφ] at hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 hab)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (fun ξ : ℝ => c * (|f (c * ξ)| * hankelRho0 c (c * ξ)))
  rw [himg, setIntegral_univ] at key
  have h2 : ∫ ξ in Ioi (0 : ℝ), c * (|f (c * ξ)| * hankelRho0 c (c * ξ)) = hankelMass c f := by
    rw [integral_const_mul]
    have := integral_comp_mul_left_Ioi (fun Δ : ℝ => |f Δ| * hankelRho0 c Δ) (0 : ℝ) hc
    simp only [mul_zero, smul_eq_mul] at this
    rw [this, hankelMass]
    field_simp
  rw [← h2, key]
  refine integral_congr_ae (ae_of_all _ fun L => ?_)
  have hp : 0 ≤ Real.exp L / π ^ 2 := by positivity
  have hr := hankelRho0_nonneg hc (by positivity : 0 ≤ c * (Real.exp L / π ^ 2))
  simp only [hankelHL, hφ, smul_eq_mul, abs_of_nonneg hp]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hc.le, abs_of_nonneg hp]
  ring

/-- `∫ g₋ ≤ M[f] e^{-(L₀-L_T)²/(2W²)}/(√(2π)W)` for `L₀ ≥ L_T`, `g = G_W(· - L₀) h`. -/
theorem hankel_window_neg_le {c ε T : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) {W : ℝ}
    (hW : 0 < W) {L0 LT : ℝ} (hLT : ∀ L, LT ≤ L → T ≤ c * (Real.exp L / π ^ 2)) (hL0 : LT ≤ L0) :
    ∫ x, max (-(gaussK W (x - L0) * hankelHL c f x)) 0 ≤
      hankelMass c f * (Real.exp (-(1 / (2 * W ^ 2)) * (L0 - LT) ^ 2) / (√(2 * π) * W)) := by
  have hh := integrable_hankelHL hc hf.toIsHankelEigenfn
  have habs : Integrable (fun L => |hankelHL c f L|) := hh.abs
  set G : ℝ := Real.exp (-(1 / (2 * W ^ 2)) * (L0 - LT) ^ 2) / (√(2 * π) * W) with hG
  have hGn : 0 ≤ G := by positivity
  have hpt : ∀ x : ℝ, max (-(gaussK W (x - L0) * hankelHL c f x)) 0 ≤ G * |hankelHL c f x| := by
    intro x
    by_cases hx : LT ≤ x
    · have h0 := hankelHL_nonneg_of_tail hc hf (hLT x hx)
      have : 0 ≤ gaussK W (x - L0) * hankelHL c f x := mul_nonneg (by unfold gaussK; positivity) h0
      rw [max_eq_right (by linarith)]; positivity
    · push Not at hx
      have hg : gaussK W (x - L0) ≤ G := by
        unfold gaussK
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Real.exp_le_exp.2
        have : (L0 - LT) ^ 2 ≤ (x - L0) ^ 2 := by nlinarith
        have h1 : 0 ≤ 1 / (2 * W ^ 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h1]
      have hgn : 0 ≤ gaussK W (x - L0) := by unfold gaussK; positivity
      calc max (-(gaussK W (x - L0) * hankelHL c f x)) 0 ≤ |gaussK W (x - L0) * hankelHL c f x| := by
            rw [max_le_iff]; exact ⟨neg_le_abs _, abs_nonneg _⟩
        _ = gaussK W (x - L0) * |hankelHL c f x| := by rw [abs_mul, abs_of_nonneg hgn]
        _ ≤ G * |hankelHL c f x| := mul_le_mul_of_nonneg_right hg (abs_nonneg _)
  have hnn : ∀ x : ℝ, 0 ≤ max (-(gaussK W (x - L0) * hankelHL c f x)) 0 := fun x => le_max_right _ _
  calc ∫ x, max (-(gaussK W (x - L0) * hankelHL c f x)) 0 ≤ ∫ x, G * |hankelHL c f x| :=
        integral_mono_of_nonneg (ae_of_all _ hnn) (habs.const_mul G) (ae_of_all _ hpt)
    _ = hankelMass c f * G := by rw [integral_const_mul, integral_abs_hankelHL hc hf.toIsHankelEigenfn]; ring

/-- info: 'FormalResearch.SignUncertainty.hankel_window_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_window_neg_le

end FormalResearch.SignUncertainty
