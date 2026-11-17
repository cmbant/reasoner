module

public import FormalResearch.Special.BarnesVI

/-!
# The paper's integrand `g_θ(f(ξ))`: real part

For `f(ξ) = 1/(1+e^{πξ})` and `g_θ(t) = log[1 + (e^{iθ}-1) t] - iθ t` (principal logarithm; the
chord from `1` to `e^{iθ}` avoids `(-∞, 0]` for `|θ| < π`), the paper's `B(θ)` is
`-(1/2π) ∫ g_θ(f(ξ)) Re ψ(1/2 + iξ/2) dξ`.  This module proves the identification of the *real part*
of the integrand with the integrand of (BGreal):

`Re g_θ(f(ξ)) = (1/2) log((cosh πξ + cos θ)/(cosh πξ + 1))`   (`re_gTheta`),

hence `bgInt θ = -(1/2π) ∫ Re g_θ(f(ξ)) ρ(ξ) dξ` (`bgInt_eq_re_gTheta`).

Not formalised: that the imaginary part `Im g_θ(f(ξ))` is odd in `ξ` (so that it does not contribute
to the paper's complex integral) and that the complex integrand is integrable; this is the
"reduction to a real even integrand" paragraph of the proof of `thm:BG` and is independent of the
Gamma/Barnes content proved in `BarnesBG`.
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex MeasureTheory
open scoped Real

/-- `f(ξ) = 1/(1 + e^{πξ})`. -/
noncomputable def fLogit (ξ : ℝ) : ℝ := 1 / (1 + Real.exp (π * ξ))

/-- `g_θ(t) = log[1 + (e^{iθ} - 1) t] - iθ t`. -/
noncomputable def gTheta (θ : ℝ) (t : ℝ) : ℂ :=
  Complex.log (1 + (Complex.exp ((θ : ℂ) * I) - 1) * (t : ℂ)) - (θ : ℂ) * I * (t : ℂ)

lemma fLogit_mul_one_sub (ξ : ℝ) : fLogit ξ * (1 - fLogit ξ) = wR ξ := by
  rw [wR_eq_exp]
  unfold fLogit
  have : 0 < 1 + Real.exp (π * ξ) := by positivity
  field_simp
  ring

lemma normSq_gTheta_arg (θ t : ℝ) :
    Complex.normSq (1 + (Complex.exp ((θ : ℂ) * I) - 1) * (t : ℂ)) =
      1 - 2 * (t * (1 - t)) * (1 - Real.cos θ) := by
  rw [Complex.exp_mul_I, Complex.normSq_apply]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  linear_combination t ^ 2 * Real.sin_sq_add_cos_sq θ

/-- `Re g_θ(f(ξ)) = (1/2) log((cosh πξ + cos θ)/(cosh πξ + 1))` for `|θ| < π`. -/
theorem re_gTheta {θ : ℝ} (hθ : |θ| < π) (ξ : ℝ) :
    (gTheta θ (fLogit ξ)).re = (1 / 2) * Real.log (kerR θ ξ / kerR 0 ξ) := by
  have hk := kerR_pos hθ ξ
  have hk0 := kerR_pos (θ := 0) (by rw [abs_zero]; exact Real.pi_pos) ξ
  have hn : Complex.normSq (1 + (Complex.exp ((θ : ℂ) * I) - 1) * ((fLogit ξ : ℝ) : ℂ)) =
      kerR θ ξ / kerR 0 ξ := by
    rw [normSq_gTheta_arg, fLogit_mul_one_sub, wR_eq]
    unfold kerR
    rw [Real.cos_zero]
    have : 0 < Real.cosh (π * ξ) + 1 := by positivity
    field_simp
    ring
  unfold gTheta
  simp only [Complex.sub_re, Complex.log_re]
  have : ((θ : ℂ) * I * ((fLogit ξ : ℝ) : ℂ)).re = 0 := by simp
  rw [this, sub_zero, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), hn]
  ring

/-- Real part of the paper's `B(θ)`: `bgInt θ = -(1/2π) ∫ Re g_θ(f(ξ)) Re ψ(1/2 + iξ/2) dξ`. -/
theorem bgInt_eq_re_gTheta {θ : ℝ} (hθ : |θ| < π) :
    bgInt θ = -(1 / (2 * π)) * ∫ ξ : ℝ, (gTheta θ (fLogit ξ)).re * rhoR ξ := by
  unfold bgInt bgFun
  have : ∀ ξ : ℝ, (gTheta θ (fLogit ξ)).re * rhoR ξ =
      (1 / 2) * (Real.log (kerR θ ξ / kerR 0 ξ) * rhoR ξ) := fun ξ => by
    rw [re_gTheta hθ]; ring
  simp_rw [this]
  rw [integral_const_mul]
  field_simp
  ring


/-- info: 'FormalResearch.Special.Barnes.bgInt_eq_re_gTheta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bgInt_eq_re_gTheta

end FormalResearch.Special.Barnes
