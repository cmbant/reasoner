module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The normalised Bessel function of real order

For real `ν > -1` let
`besselNorm ν x = Γ(ν+1) (x/2)^{-ν} J_ν(x) = Γ(ν+1) ∑_k (-1)^k (x/2)^{2k} / (k! Γ(ν+k+1))`,
an even entire function of `x` with `besselNorm ν 0 = 1`.  The Hankel kernel of
`CFT/sign_uncertainty/paper/fourier_mellin.tex` (`eq:hankel`) is
`K^{(c)}(Δ,s) = besselNorm (c-1) (4π√(Δ s))`.

* `besselNorm_ofReal_eq`: `besselNorm ν x = Γ(ν+1) · ₀F₁-regularised` in Mathlib's normalisation;
* `besselNorm_continuous`, `besselNorm_zero`, `besselNorm_neg`;
* `besselNorm_summable`: the defining series converges absolutely;
* `besselJ_ofReal_eq_besselNorm`: for `x > 0`, `Complex.besselJ ν x = (x/2)^ν / Γ(ν+1) · besselNorm ν x`.

The bound `|besselNorm ν x| ≤ 1` for `ν > -1/2` (Poisson integral) is in
`FormalResearch/Special/BesselPoisson.lean`.
-/

@[expose] public section

open scoped Nat
open Complex

namespace FormalResearch.Special

/-- The Taylor coefficient `1 / (k! Γ(ν+k+1))`. -/
noncomputable def besselNormCoeff (ν : ℝ) (k : ℕ) : ℝ :=
  1 / ((k ! : ℝ) * Real.Gamma (ν + k + 1))

/-- The normalised Bessel function `Γ(ν+1) (x/2)^{-ν} J_ν(x)` of real order `ν` and real
argument, as the series `Γ(ν+1) ∑_k (-1)^k (x/2)^{2k} / (k! Γ(ν+k+1))`. -/
noncomputable def besselNorm (ν x : ℝ) : ℝ :=
  Real.Gamma (ν + 1) * ∑' k : ℕ, (-1) ^ k * (x / 2) ^ (2 * k) * besselNormCoeff ν k

lemma regularizedHGFun_zero_singleton' (b z : ℂ) :
    Complex.regularizedHGFun 0 {b} z =
      ∑' n : ℕ, (1 / ((n ! : ℂ) * Complex.Gamma (b + n))) * z ^ n := by
  unfold Complex.regularizedHGFun Complex.regularizedHGFunSeries
  rw [show (FormalMultilinearSeries.ofScalars ℂ (Complex.regularizedHGFunCoeff 0 {b})).sum z =
    FormalMultilinearSeries.ofScalarsSum (Complex.regularizedHGFunCoeff 0 {b}) z from rfl,
    FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp [Complex.regularizedHGFunCoeff]

lemma besselNorm_term_cast (ν x : ℝ) (k : ℕ) :
    (((-1) ^ k * (x / 2) ^ (2 * k) * besselNormCoeff ν k : ℝ) : ℂ) =
      (1 / ((k ! : ℂ) * Complex.Gamma ((ν : ℂ) + 1 + k))) * (-((x : ℂ) / 2) ^ 2) ^ k := by
  have hG : Complex.Gamma ((ν : ℂ) + 1 + k) = ((Real.Gamma (ν + k + 1) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_add, Complex.Gamma_ofReal]
    ring_nf
  rw [hG, besselNormCoeff]
  push_cast
  rw [show (-((x : ℂ) / 2) ^ 2) ^ k = (-1) ^ k * ((x : ℂ) / 2) ^ (2 * k) by
    rw [neg_pow, pow_mul]]
  ring

/-- The series, in Mathlib's regularised `₀F₁`, for every real `ν`. -/
theorem besselNorm_ofReal_eq (ν x : ℝ) :
    ((besselNorm ν x : ℝ) : ℂ) =
      (Real.Gamma (ν + 1) : ℂ) *
        Complex.regularizedHGFun 0 {((ν : ℂ) + 1)} (-((x : ℂ) / 2) ^ 2) := by
  unfold besselNorm
  rw [Complex.ofReal_mul, Complex.ofReal_tsum, regularizedHGFun_zero_singleton']
  exact congrArg _ (tsum_congr fun k => besselNorm_term_cast ν x k)

/-- The defining series converges absolutely (for every real `ν`). -/
theorem besselNorm_summable (ν x : ℝ) :
    Summable fun k : ℕ => (-1) ^ k * (x / 2) ^ (2 * k) * besselNormCoeff ν k := by
  have h := (Complex.regularizedHGFunSeries 0 {((ν : ℂ) + 1)}).summable
    (x := -((x : ℂ) / 2) ^ 2)
    (by simp [Complex.radius_regularizedHGFunSeries_zero_eq_top])
  rw [← Complex.summable_ofReal]
  refine (summable_congr fun k => ?_).mpr h
  rw [besselNorm_term_cast]
  unfold Complex.regularizedHGFunSeries
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  simp [Complex.regularizedHGFunCoeff]

/-- `besselNorm ν` is continuous (indeed entire). -/
theorem besselNorm_continuous (ν : ℝ) : Continuous (besselNorm ν) := by
  have hc : Continuous fun z : ℂ => Complex.regularizedHGFun 0 {((ν : ℂ) + 1)} z :=
    continuous_iff_continuousAt.mpr fun z =>
      (Complex.analyticAt_regularizedHGFun_zero z).continuousAt
  have : besselNorm ν = fun x : ℝ => (((Real.Gamma (ν + 1) : ℂ)) *
      Complex.regularizedHGFun 0 {((ν : ℂ) + 1)} (-((x : ℂ) / 2) ^ 2)).re := by
    funext x
    rw [← besselNorm_ofReal_eq, Complex.ofReal_re]
  rw [this]
  exact Complex.continuous_re.comp (continuous_const.mul (hc.comp (by fun_prop)))

/-- `besselNorm ν 0 = 1` for `ν > -1`. -/
theorem besselNorm_zero {ν : ℝ} (hν : -1 < ν) : besselNorm ν 0 = 1 := by
  have hG : 0 < Real.Gamma (ν + 1) := Real.Gamma_pos_of_pos (by linarith)
  unfold besselNorm
  rw [tsum_eq_single 0]
  · simp [besselNormCoeff]
    field_simp
  · intro k hk
    simp [hk]

/-- `besselNorm ν` is even. -/
theorem besselNorm_neg (ν x : ℝ) : besselNorm ν (-x) = besselNorm ν x := by
  unfold besselNorm
  congr 1
  refine tsum_congr fun k => ?_
  rw [neg_div, (even_two_mul k).neg_pow]

/-- **Link to Mathlib's `Complex.besselJ`** (`ν > -1`, `x ≥ 0`):
`J_ν(x) = (x/2)^ν / Γ(ν+1) · besselNorm ν x`. -/
theorem besselJ_ofReal_eq_besselNorm {ν : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 0 ≤ x) :
    Complex.besselJ (ν : ℂ) (x : ℂ) = (((x / 2) ^ ν / Real.Gamma (ν + 1) * besselNorm ν x : ℝ) : ℂ) := by
  have hG : (Real.Gamma (ν + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos (by linarith : 0 < ν + 1)).ne'
  rw [Complex.besselJ_def]
  simp only
  rw [Complex.ofReal_mul, besselNorm_ofReal_eq]
  have h1 : ((x : ℂ) / 2) ^ (ν : ℂ) = (((x / 2) ^ ν : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [h1, Complex.ofReal_div]
  field_simp

/-- The real-order series `∑_k (-1)^k (x/2)^{2k}/(k! Γ(ν+k+1))` is `(x/2)^{-ν} J_ν(x)`. -/
theorem besselNorm_eq_gamma_mul_rpow_neg_besselJ {ν : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 0 < x) :
    (besselNorm ν x : ℂ) = (Real.Gamma (ν + 1) : ℂ) * (((x / 2) ^ (-ν) : ℝ) : ℂ) *
      Complex.besselJ (ν : ℂ) (x : ℂ) := by
  rw [besselJ_ofReal_eq_besselNorm hν hx.le]
  have hG : Real.Gamma (ν + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < ν + 1)).ne'
  have hp : (x / 2) ^ (-ν) * (x / 2) ^ ν = 1 := by
    rw [← Real.rpow_add (by positivity)]; simp
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp
  calc besselNorm ν x = ((x / 2) ^ (-ν) * (x / 2) ^ ν) * besselNorm ν x := by rw [hp, one_mul]
    _ = _ := by ring

/-! ### Axiom guards -/

/-- info: 'FormalResearch.Special.besselNorm_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselNorm_continuous

/-- info: 'FormalResearch.Special.besselNorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselNorm_zero

/-- info: 'FormalResearch.Special.besselJ_ofReal_eq_besselNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselJ_ofReal_eq_besselNorm

/-- info: 'FormalResearch.Special.besselNorm_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselNorm_summable

end FormalResearch.Special
