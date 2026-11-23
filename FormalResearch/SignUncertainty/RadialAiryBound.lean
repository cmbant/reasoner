module

public import FormalResearch.SignUncertainty.RadialAiryReal
public import FormalResearch.Special.AiryEnvelope

/-!
# The Airy-class bound for the limit function (`lem:radial-compactness`, Step 4)

`radialF W z = β₁⁻¹ Ξ_W(-z/β₁)`. For `W` holomorphic with `‖W‖ ≤ M₀` on `Re w > 0`,
`‖radialF W z‖ ≤ C (1+|z|)^{1/2} exp(-(4/3) Re z^{3/2})` (`radialF_airy_bound`): the contour `Re w = u`
is chosen with `a = λu = max (1/(1+|z|), 2 Re √z)` (`airy_choice`), `λ = π²/β₁`, `λ³ = π²/3`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- `F(z) = β₁⁻¹ Ξ_W(-z/β₁)`. -/
noncomputable def radialF (W : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((hankelBeta1⁻¹ : ℝ) : ℂ) * XiL W (-z / (hankelBeta1 : ℂ))

lemma sqrt_facts (z : ℂ) : ∃ p q : ℝ, 0 ≤ p ∧ z.re = p ^ 2 - q ^ 2 ∧ z.im = 2 * p * q ∧
    ‖z‖ = p ^ 2 + q ^ 2 ∧ (z ^ (3 / 2 : ℂ)).re = p ^ 3 - 3 * p * q ^ 2 := by
  set ζ : ℂ := z ^ (1 / 2 : ℂ) with hζ
  have h2 : ζ ^ 2 = z := by
    have := Complex.cpow_nat_mul z 2 (1 / 2 : ℂ)
    rw [show ((2 : ℕ) : ℂ) * (1 / 2 : ℂ) = 1 by norm_num, Complex.cpow_one] at this
    exact this.symm
  have h3 : z ^ (3 / 2 : ℂ) = ζ ^ 3 := by
    have := Complex.cpow_nat_mul z 3 (1 / 2 : ℂ)
    rw [show ((3 : ℕ) : ℂ) * (1 / 2 : ℂ) = 3 / 2 by norm_num] at this
    exact this
  have hre : 0 ≤ ζ.re := by
    by_cases hz : z = 0
    · simp [hζ, hz]
    · rw [hζ, Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
      refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
      all_goals
        simp only [Complex.mul_im, Complex.log_re, Complex.log_im, one_div]
        have h1 := Complex.neg_pi_lt_arg z
        have h2 := Complex.arg_le_pi z
        simp
        linarith
  refine ⟨ζ.re, ζ.im, hre, ?_, ?_, ?_, ?_⟩
  · rw [← h2]; simp [sq]
  · rw [← h2]; simp [sq]; ring
  · have : ‖z‖ = ‖ζ‖ ^ 2 := by rw [← h2, norm_pow]
    rw [this, Complex.sq_norm, Complex.normSq_apply]; ring
  · rw [h3]; simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

theorem radialF_airy_bound {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀)
    (hWd : DifferentiableOn ℂ W {w | 0 < w.re}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖radialF W z‖ ≤ C * (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := by
  have hM0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hW 1 (by simp))
  have hβ := hankelBeta1_pos
  have hb3 := hankelBeta1_pow_three
  set β := hankelBeta1 with hβdef
  have hπ := Real.pi_pos
  refine ⟨β⁻¹ * (Real.pi / 2) * M₀ * Real.exp 4 * Real.sqrt (12 * Real.pi / β), by positivity, fun z => ?_⟩
  obtain ⟨p, q, hp, hx, hy, hz, h32⟩ := sqrt_facts z
  obtain ⟨a, ha, haρ, hE⟩ := airy_choice p q hp
  set u : ℝ := a * β / Real.pi ^ 2 with hu
  have hu0 : 0 < u := by positivity
  set s : ℂ := -z / (β : ℂ) with hs
  have hsre : s.re = -z.re / β := by
    rw [hs, Complex.div_ofReal_re, Complex.neg_re]
  have hsim : s.im = -z.im / β := by
    rw [hs, Complex.div_ofReal_im, Complex.neg_im]
  have hX := norm_XiL_le hW hWd hu0 s
  -- the exponent identity
  have hc : Real.pi ^ 2 * u / 12 = a * β / 12 := by rw [hu]; field_simp
  have hexp : Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u +
      (-(Real.pi ^ 2 * s.im)) ^ 2 / (4 * (Real.pi ^ 2 * u / 12)) =
      a ^ 3 / 12 - z.re * a + z.im ^ 2 / a := by
    rw [hsre, hsim, hc, hu]
    field_simp
    rw [hb3]
    ring
  have hD : 0 < 1 + (p ^ 2 + q ^ 2) := by positivity
  have h1a : 1 / a ≤ 1 + ‖z‖ := by
    rw [hz, div_le_iff₀ ha]
    have := (div_le_iff₀ hD).mp haρ
    linarith
  have hsq : Real.sqrt (Real.pi / (Real.pi ^ 2 * u / 12)) ≤
      Real.sqrt (12 * Real.pi / β) * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
    rw [hc, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : Real.pi / (a * β / 12) = 12 * Real.pi / β * (1 / a) := by field_simp
    rw [this]
    gcongr
  have hE' : a ^ 3 / 12 - z.re * a + z.im ^ 2 / a ≤ 4 - 4 / 3 * (z ^ (3 / 2 : ℂ)).re := by
    rw [hx, hy, h32]; exact hE
  have hexp2 : Real.exp (a ^ 3 / 12 - z.re * a + z.im ^ 2 / a) ≤ Real.exp 4 * airyEnv z := by
    unfold airyEnv
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hN : ‖radialF W z‖ = β⁻¹ * ‖XiL W s‖ := by
    unfold radialF
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hN]
  have hAE := airyEnv_pos z
  have hX' : ‖XiL W s‖ ≤ Real.pi / 2 * M₀ * Real.exp (a ^ 3 / 12 - z.re * a + z.im ^ 2 / a) *
      Real.sqrt (Real.pi / (Real.pi ^ 2 * u / 12)) := by
    refine hX.trans (le_of_eq ?_)
    rw [← hexp, Real.exp_add (Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u)]
    ring
  calc β⁻¹ * ‖XiL W s‖
      ≤ β⁻¹ * (Real.pi / 2 * M₀ * (Real.exp 4 * airyEnv z) *
          (Real.sqrt (12 * Real.pi / β) * (1 + ‖z‖) ^ (1 / 2 : ℝ))) := by
        gcongr
        refine hX'.trans ?_
        gcongr
    _ = _ := by ring

end FormalResearch.SignUncertainty
