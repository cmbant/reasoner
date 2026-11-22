module

public import FormalResearch.ModularBootstrap.Bessel.IntegralRep
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Gaussian integrals for Laplace's method

Elementary Gaussian bounds used for the `I₀` asymptotics (`Bessel.Laplace`), with no `Γ`/`rpow`:

* `gauss_interval_le`: `∫₀^a e^{-bθ²} ≤ ½√(π/b)`;
* `gauss_sub_interval_le`: `½√(π/b) - ∫₀^π e^{-bθ²} ≤ 2 e^{-bπ²}/(bπ)`;
* `moment4_interval_le`: `∫₀^1 θ⁴ e^{-bθ²} ≤ (3/(4b²)) ∫₀^1 e^{-bθ²}` (two integrations by parts).
-/

@[expose] public section

open Real MeasureTheory Set intervalIntegral

namespace FormalResearch.ModularBootstrap.Bessel

lemma gauss_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun θ : ℝ => exp (-b * θ ^ 2)) (Ioi 0) :=
  (integrable_exp_neg_mul_sq hb).integrableOn

lemma gauss_Ioi (b : ℝ) : ∫ θ in Ioi (0 : ℝ), exp (-b * θ ^ 2) = √(π / b) / 2 :=
  integral_gaussian_Ioi b

/-- `∫₀^a e^{-bθ²} dθ ≤ ½ √(π/b)`. -/
lemma gauss_interval_le {b : ℝ} (hb : 0 < b) {a : ℝ} (ha : 0 ≤ a) :
    ∫ θ in (0 : ℝ)..a, exp (-b * θ ^ 2) ≤ √(π / b) / 2 := by
  rw [intervalIntegral.integral_of_le ha, ← gauss_Ioi b]
  exact setIntegral_mono_set (gauss_integrableOn hb)
    (Filter.Eventually.of_forall fun θ => (exp_pos _).le)
    (Filter.Eventually.of_forall Ioc_subset_Ioi_self)

/-- Gaussian tail: `∫_{π}^∞ e^{-bθ²} ≤ e^{-bπ²}/(bπ)`. -/
lemma gauss_tail_le {b : ℝ} (hb : 0 < b) :
    ∫ θ in Ioi π, exp (-b * θ ^ 2) ≤ exp (-(b * π ^ 2)) / (b * π) := by
  have hbp : 0 < b * π := by positivity
  have hint := integrableOn_exp_mul_Ioi (a := -(b * π)) (by linarith) π
  have hg : IntegrableOn (fun θ : ℝ => exp (-b * θ ^ 2)) (Ioi π) :=
    (gauss_integrableOn hb).mono_set (Ioi_subset_Ioi pi_pos.le)
  calc ∫ θ in Ioi π, exp (-b * θ ^ 2) ≤ ∫ θ in Ioi π, exp (-(b * π) * θ) := by
        refine setIntegral_mono_on hg hint measurableSet_Ioi fun θ hθ => ?_
        refine exp_le_exp.mpr ?_
        have h : π < θ := hθ
        nlinarith [mul_nonneg (mul_nonneg hb.le (pi_pos.le.trans h.le)) (sub_nonneg.2 h.le)]
    _ = exp (-(b * π ^ 2)) / (b * π) := by
        rw [integral_exp_mul_Ioi (by linarith)]
        have : -(b * π) * π = -(b * π ^ 2) := by ring
        rw [this]
        field_simp

/-- `½√(π/b) - ∫₀^π e^{-bθ²} ≤ e^{-bπ²}/(bπ)`. -/
lemma gauss_sub_interval_le {b : ℝ} (hb : 0 < b) :
    √(π / b) / 2 - ∫ θ in (0 : ℝ)..π, exp (-b * θ ^ 2) ≤ exp (-(b * π ^ 2)) / (b * π) := by
  have hsplit : ∫ θ in Ioi (0 : ℝ), exp (-b * θ ^ 2) =
      (∫ θ in Ioc (0 : ℝ) π, exp (-b * θ ^ 2)) + ∫ θ in Ioi π, exp (-b * θ ^ 2) := by
    rw [← Ioc_union_Ioi_eq_Ioi pi_pos.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi ((gauss_integrableOn hb).mono_set Ioc_subset_Ioi_self)
      ((gauss_integrableOn hb).mono_set (Ioi_subset_Ioi pi_pos.le))]
  rw [gauss_Ioi b, intervalIntegral.integral_of_le pi_pos.le] at *
  have := gauss_tail_le hb
  linarith [hsplit]

lemma hasDerivAt_mul_gauss (b : ℝ) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => θ ^ (n + 1) * exp (-b * θ ^ 2))
      (((n + 1 : ℕ) : ℝ) * θ ^ n * exp (-b * θ ^ 2) - 2 * b * θ ^ (n + 2) * exp (-b * θ ^ 2)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => θ ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * θ ^ n) θ := by
    simpa using hasDerivAt_pow (n + 1) θ
  have h2 : HasDerivAt (fun θ : ℝ => exp (-b * θ ^ 2)) (exp (-b * θ ^ 2) * (-b * (2 * θ))) θ := by
    have := (((hasDerivAt_pow 2 θ).const_mul (-b)).exp)
    simpa using this
  convert h1.mul h2 using 1
  ring

/-- Integration by parts on `[0,1]`: `∫₀^1 θ^{n+2} e^{-bθ²} ≤ ((n+1)/(2b)) ∫₀^1 θ^n e^{-bθ²}`. -/
lemma moment_succ_succ_le {b : ℝ} (hb : 0 < b) (n : ℕ) :
    ∫ θ in (0 : ℝ)..1, θ ^ (n + 2) * exp (-b * θ ^ 2) ≤
      ((n : ℝ) + 1) / (2 * b) * ∫ θ in (0 : ℝ)..1, θ ^ n * exp (-b * θ ^ 2) := by
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ : ℝ => θ ^ (n + 1) * exp (-b * θ ^ 2)) (a := 0) (b := 1)
    (fun θ _ => hasDerivAt_mul_gauss b n θ)
    ((by fun_prop : Continuous fun θ : ℝ => ((n + 1 : ℕ) : ℝ) * θ ^ n * exp (-b * θ ^ 2) -
      2 * b * θ ^ (n + 2) * exp (-b * θ ^ 2)).intervalIntegrable _ _)
  have hc1 : IntervalIntegrable (fun θ : ℝ => ((n + 1 : ℕ) : ℝ) * (θ ^ n * exp (-b * θ ^ 2)))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun θ : ℝ => ((n + 1 : ℕ) : ℝ) * (θ ^ n * exp (-b * θ ^ 2))).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun θ : ℝ => 2 * b * (θ ^ (n + 2) * exp (-b * θ ^ 2)))
      MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun θ : ℝ => 2 * b * (θ ^ (n + 2) * exp (-b * θ ^ 2))).intervalIntegrable _ _
  have hsplit : ∫ θ in (0 : ℝ)..1, (((n + 1 : ℕ) : ℝ) * θ ^ n * exp (-b * θ ^ 2) -
      2 * b * θ ^ (n + 2) * exp (-b * θ ^ 2)) =
      ((n + 1 : ℕ) : ℝ) * (∫ θ in (0 : ℝ)..1, θ ^ n * exp (-b * θ ^ 2)) -
      2 * b * (∫ θ in (0 : ℝ)..1, θ ^ (n + 2) * exp (-b * θ ^ 2)) := by
    have e1 := intervalIntegral.integral_sub hc1 hc2
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at e1
    refine Eq.trans ?_ e1
    congr 1; ext θ; ring
  rw [hsplit] at hft
  simp at hft
  have hexp : 0 ≤ exp (-b) := (exp_pos _).le
  simp only [neg_mul] at hft ⊢
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  generalize (∫ θ in (0 : ℝ)..1, θ ^ n * exp (-(b * θ ^ 2))) = A at *
  generalize (∫ θ in (0 : ℝ)..1, θ ^ (n + 2) * exp (-(b * θ ^ 2))) = B at *
  nlinarith

/-- `∫₀^1 θ⁴ e^{-bθ²} ≤ (3/(4b²)) ∫₀^1 e^{-bθ²}`. -/
lemma moment4_interval_le {b : ℝ} (hb : 0 < b) :
    ∫ θ in (0 : ℝ)..1, θ ^ 4 * exp (-b * θ ^ 2) ≤
      3 / (4 * b ^ 2) * ∫ θ in (0 : ℝ)..1, exp (-b * θ ^ 2) := by
  have h2 := moment_succ_succ_le hb 0
  have h4 := moment_succ_succ_le hb 2
  simp only [pow_zero, one_mul] at h2
  norm_num at h2 h4
  have e : ∫ θ in (0 : ℝ)..1, θ ^ 4 * exp (-b * θ ^ 2) ≤
      3 / (2 * b) * ∫ θ in (0 : ℝ)..1, θ ^ 2 * exp (-b * θ ^ 2) := by
    simpa using h4
  calc ∫ θ in (0 : ℝ)..1, θ ^ 4 * exp (-b * θ ^ 2)
      ≤ 3 / (2 * b) * ∫ θ in (0 : ℝ)..1, θ ^ 2 * exp (-b * θ ^ 2) := e
    _ ≤ 3 / (2 * b) * (1 / (2 * b) * ∫ θ in (0 : ℝ)..1, exp (-b * θ ^ 2)) := by
        gcongr
        simpa using h2
    _ = 3 / (4 * b ^ 2) * ∫ θ in (0 : ℝ)..1, exp (-b * θ ^ 2) := by
        field_simp; ring

end FormalResearch.ModularBootstrap.Bessel
