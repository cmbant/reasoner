module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasConcrete

/-!
# `ct:boas-ineq`: the total error is `O(c^{-4/3} log c)`

`constant_terms_lower.tex`, end of the proof of `ct:boas`: the sum of the Step 1, 3, 4, 5 errors
`ε_far + 3ε_hi + 3ε_lo + Pb·(hi - lo) + K_*K₀ε_e + 3ε_s + Jκ` of `boas_ineq_assembled`, with the bounds proved in `CtBoasRates`,
`CtBoasConcrete`, is `≤ C₀ c^{-4/3} log c` for large `c` (`boasErrTotal_le`).  **Proved**, unconditional.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The total error bound (all constants as in `CtBoasConcrete`; `κ₀` is the constant of `L_min ≥ κ₀c^{-2/21}`). -/
noncomputable def boasErrTotal (c₁ K Cθ κ₀ c : ℝ) : ℝ :=
  60 * c ^ (-(2 : ℝ)) + 3 * (2 * c ^ (-(2 : ℝ))) + 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ)) +
    30 * (c ^ 4)⁻¹ * Real.log c + boasKstarC Cθ * 7 * (boasCe c₁ K * (c ^ (-(4 / 3) : ℝ) * Real.log c)) +
    3 * (7 * (Real.exp (-(Real.log c ^ 2)) +
      2000 * Real.log c / c * ((2 * K / c₁ ^ 2 + K) * c ^ (-(1 / 3) : ℝ)))) +
    400 * Real.log c * (15552000000 * Real.log c / ((κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c ^ 2))

lemma boasKstarC_nonneg {Cθ : ℝ} (hCθ : 0 ≤ Cθ) : 0 ≤ boasKstarC Cθ := by
  have h1 := taperKw_nonneg 2
  have h2 : 0 ≤ taperK0 2 := by unfold taperK0; positivity
  unfold boasKstarC; positivity

/-- **The total error is `O(c^{-4/3} log c)`.** -/
theorem boasErrTotal_le {c₁ K κ₀ : ℝ} (Cθ : ℝ) (hCθ : 0 ≤ Cθ) (hc₁ : 0 < c₁) (hK : 0 ≤ K) (hκ₀ : 0 < κ₀) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ c : ℝ in atTop, boasErrTotal c₁ K Cθ κ₀ c ≤ C₀ * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
  set C7 : ℝ := 400 * 15552000000 / κ₀ ^ 3 with hC7
  set B2c : ℝ := 2 * K / c₁ ^ 2 + K with hB2c
  have hB2c0 : 0 ≤ B2c := by rw [hB2c]; positivity
  refine ⟨60 + 6 + 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24) + 30 + boasKstarC Cθ * 7 * boasCe c₁ K + (21 + 42000 * B2c) + C7,
    ?_, ?_⟩
  · have := boasCe_nonneg hc₁ hK
    have hK0 := boasKstarC_nonneg hCθ
    positivity
  filter_upwards [eventually_ge_atTop (Real.exp 7), eventually_log_le_rpow (8 / 21) (by norm_num)] with c hc hlogc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc
  have hlog7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc
  set L := Real.log c with hL
  have hL1 : 1 ≤ L := by linarith
  have h43 : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  set X : ℝ := c ^ (-(4 / 3) : ℝ) * L with hX
  have hX0 : 0 < X := by positivity
  have hmon : ∀ a b : ℝ, a ≤ b → c ^ a ≤ c ^ b := fun a b hab => Real.rpow_le_rpow_of_exponent_le hc1.le hab
  have hcX : ∀ q : ℝ, q ≤ -(4 / 3) → c ^ q ≤ X := fun q hq => by
    have := hmon q (-(4 / 3)) hq
    rw [hX]; nlinarith [Real.rpow_pos_of_pos hc0 q]
  have p1 : 60 * c ^ (-(2 : ℝ)) ≤ 60 * X := by have := hcX (-2) (by norm_num); linarith
  have p2 : 3 * (2 * c ^ (-(2 : ℝ))) ≤ 6 * X := by have := hcX (-2) (by norm_num); linarith
  have p3 : 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ)) ≤ 3 * (2 ^ 12 * (K + 1) / c₁ ^ 24) * X := by
    have := hcX (-(29 / 21)) (by norm_num)
    have h0 : 0 ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  have p4 : 30 * (c ^ 4)⁻¹ * L ≤ 30 * X := by
    have h1 : (c ^ 4)⁻¹ = c ^ (-(4 : ℝ)) := by
      rw [Real.rpow_neg hc0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2 : c ^ (-(4 : ℝ)) ≤ c ^ (-(4 / 3) : ℝ) := hmon _ _ (by norm_num)
    rw [h1, hX]; nlinarith
  have p5 : boasKstarC Cθ * 7 * (boasCe c₁ K * (c ^ (-(4 / 3) : ℝ) * L)) = boasKstarC Cθ * 7 * boasCe c₁ K * X := by
    rw [hX]; ring
  have p6 : 3 * (7 * (Real.exp (-(L ^ 2)) + 2000 * L / c * (B2c * c ^ (-(1 / 3) : ℝ)))) ≤ (21 + 42000 * B2c) * X := by
    have h1 : Real.exp (-(L ^ 2)) ≤ c ^ (-(7 : ℝ)) := exp_neg_log_sq_le hc1 hlog7
    have h2 := hcX (-7) (by norm_num)
    have e : 2000 * L / c * (B2c * c ^ (-(1 / 3) : ℝ)) = 2000 * B2c * X := by
      have : c⁻¹ * c ^ (-(1 / 3) : ℝ) = c ^ (-(4 / 3) : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
      rw [hX, ← this]; field_simp
    rw [e]
    nlinarith
  have p7 : 400 * L * (15552000000 * L / ((κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c ^ 2)) ≤ C7 * X := by
    have e1 : (κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c ^ 2 = κ₀ ^ 3 * c ^ (12 / 7 : ℝ) := by
      have h27 : (c ^ (-(2 / 21) : ℝ)) ^ 3 = c ^ (-(2 / 7) : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      have h2 : c ^ 2 = c ^ (2 : ℝ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [mul_pow, h27, h2, mul_assoc, ← Real.rpow_add hc0]; norm_num
    have hp : 0 < c ^ (12 / 7 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [e1]
    have h3 : L / c ^ (12 / 7 : ℝ) ≤ c ^ (-(4 / 3) : ℝ) := by
      rw [div_le_iff₀ hp]
      have : c ^ (-(4 / 3) : ℝ) * c ^ (12 / 7 : ℝ) = c ^ (8 / 21 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
      rw [this]; exact hlogc
    have : 400 * L * (15552000000 * L / (κ₀ ^ 3 * c ^ (12 / 7 : ℝ))) =
        C7 * (L / c ^ (12 / 7 : ℝ)) * L := by rw [hC7]; field_simp
    rw [this, hX]
    nlinarith [mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ L), mul_nonneg (by positivity : 0 ≤ C7) (by linarith : (0 : ℝ) ≤ L)]
  unfold boasErrTotal
  rw [← hL] at *
  nlinarith [p1, p2, p3, p4, p5, p6, p7]

/-- info: 'FormalResearch.SignUncertainty.boasErrTotal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boasErrTotal_le

end FormalResearch.SignUncertainty
