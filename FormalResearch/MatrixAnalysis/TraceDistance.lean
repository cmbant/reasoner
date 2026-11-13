module

public import FormalResearch.MatrixAnalysis.TraceNorm

/-!
# Trace-distance estimates from a witness

* `tnorm_real_smul`: homogeneity of the Hermitian trace norm;
* `distance_lower_bound`: if `-L ≤ W ≤ L + Λ`, `tr(Wρ) = -g` and `tr(Wσ) ≥ 0` for density matrices
  `ρ, σ`, then `½‖ρ - σ‖₁ ≥ g / (2L + Λ)`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix
open scoped ComplexOrder

noncomputable section



/-- Homogeneity of the Hermitian trace norm for non-negative real scalars. -/
theorem tnorm_real_smul {n : Type*} [Fintype n] [DecidableEq n] {D : Matrix n n ℂ}
    (hD : D.IsHermitian) {c : ℝ} (hc : 0 ≤ c) : tnorm (c • D) = c * tnorm D := by
  have hcD : (c • D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, hD.eq]; simp
  rcases hc.eq_or_lt with rfl | hpos
  · simp only [zero_smul, zero_mul]
    exact (tnorm_eq_zero_iff (Matrix.isHermitian_zero)).2 rfl
  obtain ⟨E, hE, hEq⟩ := exists_effect_trace_mul_eq hD
  obtain ⟨E', hE', hEq'⟩ := exists_effect_trace_mul_eq hcD
  have h1 := trace_mul_ge hcD hE
  have h2 := trace_mul_ge hD hE'
  have tr1 : (E * (c • D)).trace.re = c * (E * D).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]; simp
  have tr2 : (E' * (c • D)).trace.re = c * (E' * D).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]; simp
  have trc : (c • D).trace.re = c * D.trace.re := by rw [Matrix.trace_smul]; simp
  rw [tr1, hEq, trc] at h1
  rw [tr2, trc] at hEq'
  apply le_antisymm
  · nlinarith
  · nlinarith

section Witness
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Witness distance bound** (`eq:ppt3-stability`, used in `eq:ppt3-dist-lift`).  If `-L ≤ W ≤ L + Λ`,
`tr(Wρ) = -g` and `tr(Wσ) ≥ 0` for density matrices `ρ, σ`, then `½‖ρ - σ‖₁ ≥ g / (2L + Λ)`. -/
theorem distance_lower_bound {W ρ σ : Matrix n n ℂ} {L Λ g : ℝ} (_hL : 0 ≤ L) (_hΛ : 0 ≤ Λ)
    (hLΛ : 0 < 2 * L + Λ) (hlo : (W + (L : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hhi : (((L + Λ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - W).PosSemidef)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρt : ρ.trace.re = 1) (hσt : σ.trace.re = 1)
    (hρW : (W * ρ).trace.re = -g) (hσW : 0 ≤ (W * σ).trace.re) :
    g / (2 * L + Λ) ≤ (1 / 2) * tnorm (ρ - σ) := by
  set c : ℝ := 2 * L + Λ with hc
  have hD : (ρ - σ).IsHermitian := hρ.sub hσ
  have hE : IsEffect ((1 / c : ℝ) • (W + (L : ℂ) • (1 : Matrix n n ℂ))) := by
    refine ⟨hlo.smul (by positivity), ?_⟩
    have : (1 : Matrix n n ℂ) - (1 / c : ℝ) • (W + (L : ℂ) • (1 : Matrix n n ℂ)) =
        (1 / c : ℝ) • (((L + Λ : ℝ) : ℂ) • (1 : Matrix n n ℂ) - W) := by
      have hcpos : 0 < c := hLΛ
      have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
      have hcC' : (2 * (L : ℂ) + (Λ : ℂ)) ≠ 0 := by
        rw [hc] at hcC; push_cast at hcC; exact hcC
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
        Complex.real_smul, smul_eq_mul]
      split_ifs <;> (try rw [hc]) <;> push_cast <;> field_simp <;> ring
    rw [this]
    exact hhi.smul (by positivity)
  have h := trace_mul_ge hD hE
  have htr : (ρ - σ).trace.re = 0 := by
    rw [Matrix.trace_sub]; simp [hρt, hσt]
  have hmul : (((1 / c : ℝ) • (W + (L : ℂ) • (1 : Matrix n n ℂ))) * (ρ - σ)).trace.re =
      (1 / c) * ((W * ρ).trace.re - (W * σ).trace.re + L * (ρ - σ).trace.re) := by
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub]
    simp
    ring
  rw [hmul, htr, hρW] at h
  have h' : (1 / c) * (-g - (W * σ).trace.re + L * 0) ≥ (1 / 2) * (0 - tnorm (ρ - σ)) := by
    simpa using h
  have hcpos : 0 < c := hLΛ
  have : -g / c ≥ -(tnorm (ρ - σ) / 2) := by
    have e : (1 / c) * (-g - (W * σ).trace.re + L * 0) ≤ -g / c := by
      rw [show -g / c = (1 / c) * (-g) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  have : g / c ≤ tnorm (ρ - σ) / 2 := by
    have : -(g / c) ≥ -(tnorm (ρ - σ) / 2) := by simpa [neg_div] using this
    linarith
  linarith

end Witness

/-- info: 'FormalResearch.MatrixAnalysis.distance_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms distance_lower_bound

/-- info: 'FormalResearch.MatrixAnalysis.tnorm_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tnorm_real_smul

end

end FormalResearch.MatrixAnalysis
