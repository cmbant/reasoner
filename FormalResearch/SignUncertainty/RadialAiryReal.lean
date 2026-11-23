module

public import FormalResearch.SignUncertainty.RadialShift
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# The Gaussian line-integral bound and the real optimisation (`lem:radial-compactness`, Step 4)

* `norm_XiL_le`: for any `u > 0`, `‖Ξ_W(s)‖ ≤ (π/2) M₀ e^{π²(u³/36 + σu)} · e^{(π²τ)²/(4c)} √(π/c)`,
  `c = π²u/12` (contour shift to `Re w = u`, then the exact Gaussian integral).
* `airy_choice`: for `ζ = p + iq`, `p ≥ 0`, there is `a ≥ 1/(1+|ζ|²)` with
  `a³/12 - (p²-q²)a + (2pq)²/a ≤ 4 - (4/3) Re ζ³`.
* `hankelBeta1_pow_three`: `β₁³ = 3π⁴`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma hankelBeta1_pow_three : hankelBeta1 ^ 3 = 3 * Real.pi ^ 4 := by
  have h := hankelBeta1_rpow_three_halves
  have h2 : (hankelBeta1 ^ (3 / 2 : ℝ)) ^ 2 = hankelBeta1 ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hankelBeta1_pos.le]
    norm_num
  rw [← h2, h, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

lemma integral_gauss_lin {c d : ℝ} (hc : 0 < c) :
    ∫ v : ℝ, Real.exp (-c * v ^ 2 + d * v) = Real.exp (d ^ 2 / (4 * c)) * Real.sqrt (Real.pi / c) := by
  have e : ∀ v : ℝ, Real.exp (-c * v ^ 2 + d * v) =
      Real.exp (d ^ 2 / (4 * c)) * Real.exp (-c * (v - d / (2 * c)) ^ 2) := by
    intro v
    rw [← Real.exp_add]; congr 1; field_simp; ring
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  have := integral_sub_right_eq_self (μ := volume) (fun v : ℝ => Real.exp (-c * v ^ 2)) (d / (2 * c))
  rw [this]
  exact integral_gaussian c

theorem norm_XiL_le {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀)
    (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ‖XiL W s‖ ≤ Real.pi / 2 * (M₀ * Real.exp (Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u)) *
      (Real.exp ((-(Real.pi ^ 2 * s.im)) ^ 2 / (4 * (Real.pi ^ 2 * u / 12))) *
        Real.sqrt (Real.pi / (Real.pi ^ 2 * u / 12))) := by
  have hc : 0 < Real.pi ^ 2 * u / 12 := by positivity
  have hX : XiL W s = ((Real.pi / 2 : ℝ) : ℂ) * ∫ v : ℝ, limInt W u v s := by
    unfold XiL
    rw [integral_const_mul, limInt_integral_shift hW hWd one_pos hu s]
  rw [hX, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hgi := (gauss_lin_integrable (d := -(Real.pi ^ 2 * s.im)) hc).const_mul
    (M₀ * Real.exp (Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u))
  have h1 := norm_integral_le_of_norm_le hgi (ae_of_all _ fun v => norm_limInt_le_gauss hW hu v s)
  rw [integral_const_mul, integral_gauss_lin hc] at h1
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

lemma airy_choice (p q : ℝ) (hp : 0 ≤ p) :
    ∃ a : ℝ, 0 < a ∧ 1 / (1 + (p ^ 2 + q ^ 2)) ≤ a ∧
      a ^ 3 / 12 - (p ^ 2 - q ^ 2) * a + (2 * p * q) ^ 2 / a ≤ 4 - 4 / 3 * (p ^ 3 - 3 * p * q ^ 2) := by
  set ρ : ℝ := 1 / (1 + (p ^ 2 + q ^ 2)) with hρ
  have hD : 0 < 1 + (p ^ 2 + q ^ 2) := by positivity
  have hρ0 : 0 < ρ := by positivity
  have hρD : ρ * (1 + (p ^ 2 + q ^ 2)) = 1 := by rw [hρ]; field_simp
  have hρ1 : ρ ≤ 1 := by nlinarith [sq_nonneg p, sq_nonneg q]
  have hq : ρ * q ^ 2 ≤ 1 := by nlinarith [sq_nonneg p, sq_nonneg q, mul_nonneg hρ0.le (sq_nonneg p)]
  by_cases h : ρ ≤ 2 * p
  · have hp0 : p ≠ 0 := by intro h0; rw [h0] at h; linarith
    refine ⟨2 * p, by linarith, h, ?_⟩
    have : (2 * p) ^ 3 / 12 - (p ^ 2 - q ^ 2) * (2 * p) + (2 * p * q) ^ 2 / (2 * p) =
        -(4 / 3 * (p ^ 3 - 3 * p * q ^ 2)) := by
      field_simp
      ring
    linarith
  · rw [not_le] at h
    refine ⟨ρ, hρ0, le_rfl, ?_⟩
    have hp2 : p ^ 2 ≤ ρ ^ 2 / 4 := by nlinarith
    have h4 : (2 * p * q) ^ 2 / ρ ≤ ρ * q ^ 2 := by
      rw [div_le_iff₀ hρ0]
      nlinarith [sq_nonneg q, mul_le_mul_of_nonneg_right hp2 (sq_nonneg q)]
    have hp3 : p ^ 3 ≤ 1 / 8 := by
      have : p ≤ 1 / 2 := by linarith
      calc p ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hp this 3
        _ = 1 / 8 := by norm_num
    have h5 : ρ ^ 3 / 12 ≤ 1 / 12 := by
      have : ρ ^ 3 ≤ 1 := pow_le_one₀ hρ0.le hρ1
      linarith
    have h6 : -(p ^ 2 - q ^ 2) * ρ ≤ ρ * q ^ 2 := by nlinarith [mul_nonneg hρ0.le (sq_nonneg p)]
    have h7 : 0 ≤ p * q ^ 2 := mul_nonneg hp (sq_nonneg q)
    nlinarith

/-- info: 'FormalResearch.SignUncertainty.norm_XiL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_XiL_le

/-- info: 'FormalResearch.SignUncertainty.airy_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_choice

end FormalResearch.SignUncertainty
