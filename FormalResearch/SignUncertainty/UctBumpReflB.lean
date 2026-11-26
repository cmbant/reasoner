module

public import FormalResearch.SignUncertainty.UctBumpMain
public import FormalResearch.SignUncertainty.UctEnvHolo

/-!
# `C²` envelope of `τ ↦ B̂(c(1 - iτ))` (F2a helper for `uct:bump-symbol`, reflected density)

`bump_refl_env2`: for a bump profile `B` (`BumpProfile b δ M α β K B`, `β ≥ 3/2`), `c > 0`, `0 < δ ≤ 1`, `bδ ≤ 1`,
`τ ↦ B̂(c(1 - iτ))` has the `Env2` envelope `C M Λ_α(δ) (1+cδ)² e^{-3bcδ/4} (1+cδ|τ|)^{-6}`.
Proof: Cauchy estimates on discs of radius `R = 1/(4(1+cδ))` (`env2_holo_line`) and `bump_laplace_decay` (`r = 6`) on the discs
(`Re ≥ 3/4`, `cδ|Im| ≥ cδ|τ| - 1/4`).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

theorem bump_refl_env2 {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 0 < c →
      BumpProfile b δ M α β K B →
        Env2 (fun τ : ℝ => bumpLaplace B ((c : ℂ) * (1 + (-Complex.I) * (τ : ℂ))))
          (fun τ => C * M * bumpLambda α δ * (1 + c * δ) ^ 2 * Real.exp (-(3 / 4 * b * c * δ)) /
            (1 + c * δ * |τ|) ^ 6) := by
  obtain ⟨C6, hC6, hdecay⟩ := bump_laplace_decay (α := α) hb hβ K 6
  refine ⟨37 * C6 * (4 / 3) ^ 6, by positivity, fun B δ M c hδ0 hδ1 hbδ hM hc h => ?_⟩
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  set a : ℝ := c * δ with ha
  have ha0 : 0 < a := mul_pos hc hδ0
  set R : ℝ := 1 / (4 * (1 + a)) with hR
  have hR0 : 0 < R := by positivity
  have hRa : a * R ≤ 1 / 4 := by
    rw [hR, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hR4 : R ≤ 1 / 4 := by
    rw [hR, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set F : ℂ → ℂ := fun ζ => bumpLaplace B ((c : ℂ) * ζ) with hF
  set U : Set ℂ := {ζ : ℂ | 0 < ζ.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hFd : DifferentiableOn ℂ F U := by
    refine (h.differentiableOn_laplace hb0 hbδ hβ1).comp (differentiableOn_const _ |>.mul differentiableOn_id) (fun ζ hζ => ?_)
    show 0 < ((c : ℂ) * ζ).re
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos hc hζ
  have hnd : ‖(-Complex.I)‖ = 1 := by simp
  have hball : ∀ τ : ℝ, closedBall ((1 : ℂ) + (-Complex.I) * (τ : ℂ)) R ⊆ U := by
    intro τ z hz
    have h1 : ‖z - ((1 : ℂ) + (-Complex.I) * (τ : ℂ))‖ ≤ R := by simpa [dist_eq_norm] using hz
    have h2 := Complex.abs_re_le_norm (z - ((1 : ℂ) + (-Complex.I) * (τ : ℂ)))
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.I_re,
      Complex.neg_im, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero, add_zero] at h2
    rw [abs_le] at h2
    show 0 < z.re
    nlinarith [h2.1]
  -- the common bound
  set Bd : ℝ → ℝ := fun τ => C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * (4 / 3) ^ 6 / (1 + a * |τ|) ^ 6 with hBd
  have hP0 : ∀ τ : ℝ, ‖F ((1 : ℂ) + (-Complex.I) * (τ : ℂ))‖ ≤ Bd τ := by
    intro τ
    have hcast : (c : ℂ) * ((1 : ℂ) + (-Complex.I) * (τ : ℂ)) = (c : ℂ) * (((1 : ℝ) : ℂ) + (((-τ : ℝ)) : ℂ) * Complex.I) := by
      push_cast; ring
    have := hdecay B δ M c 1 (-τ) hδ0 hδ1 hbδ hM hc zero_le_one h
    show ‖bumpLaplace B ((c : ℂ) * ((1 : ℂ) + (-Complex.I) * (τ : ℂ)))‖ ≤ _
    rw [hcast]
    refine this.trans ?_
    rw [abs_neg]
    have hΛ := one_le_bumpLambda (α := α) hδ0 hδ1
    have e1 : Real.exp (-(b * c * 1 * δ)) ≤ Real.exp (-(3 / 4 * b * c * δ)) := by
      apply Real.exp_le_exp.mpr; nlinarith [mul_pos (mul_pos hb hc) hδ0]
    have hden : 0 < (1 + a * |τ|) ^ 6 := by positivity
    rw [hBd]
    show C6 * M * bumpLambda α δ * Real.exp (-(b * c * 1 * δ)) / (1 + c * δ * |τ|) ^ 6 ≤ _
    rw [← ha]
    rw [div_le_div_iff_of_pos_right hden]
    have h46 : (1 : ℝ) ≤ (4 / 3) ^ 6 := one_le_pow₀ (by norm_num)
    have hpos : 0 ≤ C6 * M * bumpLambda α δ := by
      have : 0 ≤ bumpLambda α δ := by linarith
      positivity
    calc C6 * M * bumpLambda α δ * Real.exp (-(b * c * 1 * δ)) ≤ C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) :=
          mul_le_mul_of_nonneg_left e1 hpos
      _ ≤ C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * (4 / 3) ^ 6 := by
          have := mul_nonneg hpos (Real.exp_pos (-(3 / 4 * b * c * δ))).le
          nlinarith
  have hM' : ∀ τ : ℝ, ∀ z ∈ sphere ((1 : ℂ) + (-Complex.I) * (τ : ℂ)) R, ‖F z‖ ≤ Bd τ := by
    intro τ z hz
    have h1 : ‖z - ((1 : ℂ) + (-Complex.I) * (τ : ℂ))‖ = R := by simpa [dist_eq_norm] using hz
    have hre := Complex.abs_re_le_norm (z - ((1 : ℂ) + (-Complex.I) * (τ : ℂ)))
    have him := Complex.abs_im_le_norm (z - ((1 : ℂ) + (-Complex.I) * (τ : ℂ)))
    rw [h1] at hre him
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.I_re,
      Complex.neg_im, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.sub_im, Complex.add_im, Complex.one_im, Complex.mul_im, zero_add, neg_mul, one_mul, mul_one, zero_sub] at hre him
    rw [abs_le] at hre
    have hzre : 3 / 4 ≤ z.re := by nlinarith [hre.1]
    have hzim : |τ| - R ≤ |z.im| := by
      have : |z.im + τ| ≤ R := by
        have := him; rw [show z.im - -τ = z.im + τ by ring] at this; exact this
      have h3 := abs_sub_abs_le_abs_sub τ (-z.im)
      rw [abs_neg] at h3
      have : |τ - -z.im| = |z.im + τ| := by rw [sub_neg_eq_add, add_comm]
      linarith
    have hcz : (c : ℂ) * z = (c : ℂ) * ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      rw [Complex.re_add_im]
    have hdec := hdecay B δ M c z.re z.im hδ0 hδ1 hbδ hM hc (by linarith) h
    show ‖bumpLaplace B ((c : ℂ) * z)‖ ≤ _
    rw [hcz]
    refine hdec.trans ?_
    have hΛ := one_le_bumpLambda (α := α) hδ0 hδ1
    have e1 : Real.exp (-(b * c * z.re * δ)) ≤ Real.exp (-(3 / 4 * b * c * δ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_pos (mul_pos hb hc) hδ0]
    have hlow : 3 / 4 * (1 + a * |τ|) ≤ 1 + c * δ * |z.im| := by
      rw [← ha]
      have : a * (|τ| - R) ≤ a * |z.im| := mul_le_mul_of_nonneg_left hzim ha0.le
      rw [mul_sub] at this
      nlinarith [hRa, mul_nonneg ha0.le (abs_nonneg τ)]
    have hden : 0 < (1 + a * |τ|) ^ 6 := by positivity
    have hden2 : 0 < (1 + c * δ * |z.im|) ^ 6 := by
      have : 0 < 1 + c * δ * |z.im| := by positivity
      positivity
    have hpow : (3 / 4) ^ 6 * (1 + a * |τ|) ^ 6 ≤ (1 + c * δ * |z.im|) ^ 6 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hlow 6
    have hpos : 0 ≤ C6 * M * bumpLambda α δ := by
      have : 0 ≤ bumpLambda α δ := by linarith
      positivity
    rw [hBd]
    show C6 * M * bumpLambda α δ * Real.exp (-(b * c * z.re * δ)) / (1 + c * δ * |z.im|) ^ 6 ≤ _
    rw [div_le_div_iff₀ hden2 hden]
    have hnum : C6 * M * bumpLambda α δ * Real.exp (-(b * c * z.re * δ)) ≤ C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) :=
      mul_le_mul_of_nonneg_left e1 hpos
    have hE0 := Real.exp_pos (-(3 / 4 * b * c * δ))
    have h1' : (4 / 3 : ℝ) ^ 6 * (3 / 4) ^ 6 = 1 := by norm_num
    calc C6 * M * bumpLambda α δ * Real.exp (-(b * c * z.re * δ)) * (1 + a * |τ|) ^ 6
        ≤ C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * (1 + a * |τ|) ^ 6 := by gcongr
      _ = C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * ((4 / 3) ^ 6 * ((3 / 4) ^ 6 * (1 + a * |τ|) ^ 6)) := by
          rw [← mul_assoc ((4 / 3 : ℝ) ^ 6), h1', one_mul]
      _ ≤ C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * ((4 / 3) ^ 6 * (1 + c * δ * |z.im|) ^ 6) := by
          gcongr
      _ = _ := by ring
  have hEnv := env2_holo_line hUo hFd (c₀ := 1) (d := -Complex.I) hnd hR0 hball Bd (fun τ => Bd τ) (fun τ => hP0 τ) hM'
  refine hEnv.mono fun τ => ?_
  have hBd0 : 0 ≤ Bd τ := by
    have : 0 ≤ bumpLambda α δ := by linarith [one_le_bumpLambda (α := α) hδ0 hδ1]
    rw [hBd]; positivity
  have h1R : 1 / R = 4 * (1 + a) := by rw [hR]; field_simp
  have e1 : Bd τ + Bd τ / R + 2 * Bd τ / R ^ 2 = Bd τ * (1 + 4 * (1 + a) + 32 * (1 + a) ^ 2) := by
    have : 2 * Bd τ / R ^ 2 = 2 * Bd τ * (1 / R) ^ 2 := by field_simp
    rw [this, div_eq_mul_one_div (Bd τ) R, h1R]; ring
  show Bd τ + Bd τ / R + 2 * Bd τ / R ^ 2 ≤ _
  rw [e1, hBd]
  have : 1 + 4 * (1 + a) + 32 * (1 + a) ^ 2 ≤ 37 * (1 + a) ^ 2 := by nlinarith [ha0]
  have hden : 0 < (1 + a * |τ|) ^ 6 := by positivity
  calc C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * (4 / 3) ^ 6 / (1 + a * |τ|) ^ 6 *
        (1 + 4 * (1 + a) + 32 * (1 + a) ^ 2)
      ≤ C6 * M * bumpLambda α δ * Real.exp (-(3 / 4 * b * c * δ)) * (4 / 3) ^ 6 / (1 + a * |τ|) ^ 6 * (37 * (1 + a) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith [ha0]) hBd0
    _ = _ := by rw [ha]; ring

/-- info: 'FormalResearch.SignUncertainty.bump_refl_env2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_refl_env2

end FormalResearch.SignUncertainty
