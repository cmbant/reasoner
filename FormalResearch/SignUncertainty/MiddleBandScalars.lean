module

public import FormalResearch.SignUncertainty.MiddleBandNumerics
public import FormalResearch.SignUncertainty.MiddleBandPowers

/-!
# Scalar lemmas for the middle-band region estimates and two finite power integrals (GT.2a)

Notation: `u₀ = 2 √(3 κ₀ S)`, `1 ≤ κ₀ ≤ 2`, `S ≥ 100` where stated, `L = π² ε² S`, `ε > 0`.

* `mb_eps_sq_u0_le` (a): `ε²(2u₀)² ≤ 10 L`, since `(2u₀)² = 48 κ₀ S` and `48 κ₀ ≤ 96 < 10 π²`
  (`π² > 9.8` from `Real.pi_gt_d4`). Proved, for `κ₀ ≤ 2`.
* `mb_L_le_far` (b): `L ≤ ε² u² π²/27` on `|u| ≥ 3u₀/2`, since `u² ≥ (3u₀/2)² = 27 κ₀ S ≥ 27 S`.
  Proved.
* `mb_u0_rpow_neg_eleven_halves` (c) and `mb_threeEighths_rpow` (d): `u₀ ≥ √S` and `3u₀/8 ≥ √S`
  (from `u₀² = 12 κ₀ S`), then monotonicity of `x ↦ x^z` for `z ≤ 0`
  (`Real.rpow_le_rpow_of_nonpos`). Proved.
* `mb_sqrt_vdc_lower` (e): `√(π² (3u₀/8)/6) = (π/4) √u₀ ≥ (3/4) √u₀` (`π > 3`). Proved.
  Remark (not a claim): the bound with `u₀^{1/2}` replaced by `u₀` is false for large `u₀`, not small:
  `(3/4) u₀ ≤ (π/4) √u₀` iff `u₀ ≤ π²/9 ≈ 1.1`, so it fails e.g. at `u₀ = 4`. The stated
  `u₀^{1/2}` form is the correct one and is what is proved.
* `mb_div_eps_rpow` (f): `(0.135/ε)^{-s} = 0.135^{-s} ε^{s}` for `ε > 0`. Proved.
* `mb_psi2_le` (g): `|π² x/6| ≤ π² β/6` for `|x| ≤ β`. Proved. (The brief's second clause
  `π²/6 ≤ π²/6` is trivial and not a separate statement.)
* `mb_int_sqrt_small` (h1): `∫₀^{1/S} v^{1/2} dv = (2/3) S^{-3/2}` for `S > 0`. Proved from
  `integral_rpow` (exponent `1/2 > -1`).
* `mb_int_neg_three_halves` (h2): `∫_{1/S}^{2} v^{-3/2} dv = 2 √S - √2 ≤ 2 S^{1/2}` for `S ≥ 1/2`.
  The antiderivative is `-2 v^{-1/2}`; the bound uses only `2^{-1/2} ≥ 0`. Proved from
  `integral_rpow` (with `r = -3/2 ≠ -1` and `0 ∉ [[1/S, 2]]`).

All statements are proved (classification: proved, unconditionally in the stated hypotheses).
Numerical constants enter only through `Real.pi_gt_d4` and `Real.pi_gt_three`.
-/

@[expose] public section

open scoped Real

namespace FormalResearch.SignUncertainty

/-- Helper: `u₀ > 0` for `u₀ = 2 √(3 κ₀ S)`, `κ₀ ≥ 1`, `S > 0`. -/
lemma mbs_u0_pos {κ₀ S u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 0 < S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S)) :
    0 < u₀ := by
  have h3 : 0 < 3 * κ₀ * S := by nlinarith
  rw [hu₀]
  exact mul_pos two_pos (Real.sqrt_pos.2 h3)

/-- Helper: `u₀² = 12 κ₀ S`. -/
lemma mbs_u0_sq {κ₀ S u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 0 < S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S)) :
    u₀ ^ 2 = 12 * κ₀ * S := by
  have h3 : 0 ≤ 3 * κ₀ * S := by nlinarith
  rw [hu₀, mul_pow, Real.sq_sqrt h3]
  ring

/-- (a) `ε²(2u₀)² ≤ 10 L`, with `(2u₀)² = 48 κ₀ S` and `48 κ₀ ≤ 96 < 10 π²`. -/
theorem mb_eps_sq_u0_le {κ₀ S L ε u₀ : ℝ} (hκ : 1 ≤ κ₀) (hκ' : κ₀ ≤ 2) (hS : 0 < S)
    (hL : L = Real.pi ^ 2 * ε ^ 2 * S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S)) :
    ε ^ 2 * (2 * u₀) ^ 2 ≤ 10 * L := by
  have hu2 := mbs_u0_sq hκ hS hu₀
  have h48 : (2 * u₀) ^ 2 = 48 * κ₀ * S := by
    rw [mul_pow, hu2]; ring
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hπ2 : (9.8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hc : 0 ≤ 10 * Real.pi ^ 2 - 48 * κ₀ := by nlinarith
  rw [hL, h48]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ε) hS.le) hc]

/-- (b) `L ≤ ε² u² π²/27` on `|u| ≥ 3u₀/2`, since `u² ≥ 27 κ₀ S ≥ 27 S`. -/
theorem mb_L_le_far {κ₀ S L ε u u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 0 < S)
    (hL : L = Real.pi ^ 2 * ε ^ 2 * S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S))
    (hu : 3 * u₀ / 2 ≤ |u|) : L ≤ ε ^ 2 * u ^ 2 * Real.pi ^ 2 / 27 := by
  have hu2 := mbs_u0_sq hκ hS hu₀
  have hpos := mbs_u0_pos hκ hS hu₀
  have h0 : 0 ≤ 3 * u₀ / 2 := by linarith
  have hsq : (3 * u₀ / 2) ^ 2 ≤ u ^ 2 := by
    nlinarith [sq_abs u, mul_nonneg (sub_nonneg.2 hu) (by linarith [abs_nonneg u] : (0:ℝ) ≤ |u| + 3 * u₀ / 2)]
  have h27 : 27 * S ≤ u ^ 2 := by nlinarith
  rw [hL]
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ ε ^ 2 * Real.pi ^ 2) (sub_nonneg.2 h27)]

/-- Helper: `S^{1/2} ≤ u₀` for `u₀ = 2 √(3 κ₀ S)`, `κ₀ ≥ 1`, `S > 0`. -/
lemma mbs_sqrt_le_u0 {κ₀ S u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 0 < S) (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S)) :
    Real.sqrt S ≤ u₀ := by
  have hu2 := mbs_u0_sq hκ hS hu₀
  have hpos := mbs_u0_pos hκ hS hu₀
  have h : S ≤ u₀ ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hpos.le] at this

/-- (c) `u₀^{-11/2} ≤ S^{-11/4}`, from `u₀ ≥ √S`. -/
theorem mb_u0_rpow_neg_eleven_halves {κ₀ S u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 0 < S)
    (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S)) :
    u₀ ^ (-(11 / 2 : ℝ)) ≤ S ^ (-(11 / 4 : ℝ)) := by
  have key : S ^ (-(11 / 4 : ℝ)) = (Real.sqrt S) ^ (-(11 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le]
    congr 1
    norm_num
  rw [key]
  exact Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hS) (mbs_sqrt_le_u0 hκ hS hu₀) (by norm_num)

/-- (d) `(3u₀/8)^{-5/2} ≤ S^{-5/4}`, from `3u₀/8 ≥ √S` (since `u₀² = 12 κ₀ S ≥ (64/9) S`). -/
theorem mb_threeEighths_rpow {κ₀ S u₀ : ℝ} (hκ : 1 ≤ κ₀) (hS : 0 < S)
    (hu₀ : u₀ = 2 * Real.sqrt (3 * κ₀ * S)) :
    (3 * u₀ / 8) ^ (-(5 / 2 : ℝ)) ≤ S ^ (-(5 / 4 : ℝ)) := by
  have hu2 := mbs_u0_sq hκ hS hu₀
  have h : S ≤ (3 * u₀ / 8) ^ 2 := by
    have : (3 * u₀ / 8) ^ 2 = 9 / 64 * u₀ ^ 2 := by ring
    rw [this, hu2]
    nlinarith
  have hle : Real.sqrt S ≤ 3 * u₀ / 8 := by
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (by linarith [mbs_u0_pos hκ hS hu₀])] at this
  have key : S ^ (-(5 / 4 : ℝ)) = (Real.sqrt S) ^ (-(5 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le]
    congr 1
    norm_num
  rw [key]
  exact Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.2 hS) hle (by norm_num)

/-- (e) `(3/4) u₀^{1/2} ≤ √(π² (3u₀/8)/6)`; the right side is `(π/4) u₀^{1/2}` and `π > 3`.
Remark (elementary, not a separate claim): with `u₀^{1/2}` replaced by `u₀` the bound fails for
large `u₀` (`(3/4) u₀ ≤ (π/4) √u₀` iff `u₀ ≤ π²/9`, false at `u₀ = 4`), so the square-root form is
the one stated and proved. -/
theorem mb_sqrt_vdc_lower {u₀ : ℝ} (hu₀ : 0 < u₀) :
    (3 / 4 : ℝ) * u₀ ^ (1 / 2 : ℝ) ≤ Real.sqrt (Real.pi ^ 2 * (3 * u₀ / 8) / 6) := by
  rw [← Real.sqrt_eq_rpow]
  have hs : Real.sqrt u₀ ^ 2 = u₀ := Real.sq_sqrt hu₀.le
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hsq : 0 ≤ Real.sqrt u₀ := Real.sqrt_nonneg u₀
  rw [Real.le_sqrt (by positivity) (by positivity)]
  nlinarith [mul_nonneg hu₀.le (sub_nonneg.2 hπ2)]

/-- (f) `(0.135/ε)^{-s} = 0.135^{-s} ε^{s}` for `ε > 0`. -/
theorem mb_div_eps_rpow {ε s : ℝ} (hε : 0 < ε) :
    ((0.135 : ℝ) / ε) ^ (-s) = (0.135 : ℝ) ^ (-s) * ε ^ s := by
  rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 0.135) hε.le, Real.rpow_neg hε.le s, div_inv_eq_mul]

/-- (g) `|ψ''(x)| = π² |x|/6 ≤ π² β/6` on `|x| ≤ β`. -/
theorem mb_psi2_le {x β : ℝ} (hx : |x| ≤ β) : |Real.pi ^ 2 * x / 6| ≤ Real.pi ^ 2 * β / 6 := by
  have h1 : Real.pi ^ 2 * |x| ≤ Real.pi ^ 2 * β := mul_le_mul_of_nonneg_left hx (by positivity)
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg Real.pi), abs_of_pos (by norm_num : (0:ℝ) < 6)]
  linarith

/-- (h1) `∫₀^{1/S} v^{1/2} dv = (2/3) S^{-3/2}` for `S > 0`. -/
theorem mb_int_sqrt_small {S : ℝ} (hS : 0 < S) :
    ∫ v in (0 : ℝ)..(1 / S), v ^ (1 / 2 : ℝ) = (2 / 3) * S ^ (-(3 / 2 : ℝ)) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  have e1 : (1 / S) ^ (3 / 2 : ℝ) = S ^ (-(3 / 2 : ℝ)) := by
    rw [one_div, Real.inv_rpow hS.le, Real.rpow_neg hS.le]
  rw [hexp, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), e1]
  ring

/-- (h2) `∫_{1/S}^{2} v^{-3/2} dv ≤ 2 S^{1/2}` for `S ≥ 1/2`; the exact value is `2√S - √2`. -/
theorem mb_int_neg_three_halves {S : ℝ} (hS : 1 / 2 ≤ S) :
    ∫ v in (1 / S)..(2 : ℝ), v ^ (-(3 / 2 : ℝ)) ≤ 2 * S ^ (1 / 2 : ℝ) := by
  have hSpos : 0 < S := by linarith
  have hinv : 0 < 1 / S := one_div_pos.2 hSpos
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 / S) (2 : ℝ) := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
  have e3 : (-(3 / 2 : ℝ)) + 1 = -(1 / 2) := by norm_num
  have e2 : (1 / S) ^ (-(1 / 2 : ℝ)) = S ^ (1 / 2 : ℝ) := by
    rw [one_div, Real.inv_rpow hSpos.le, Real.rpow_neg hSpos.le, inv_inv]
  rw [e3, e2]
  have hp : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have : ((2 : ℝ) ^ (-(1 / 2 : ℝ)) - S ^ (1 / 2 : ℝ)) / (-(1 / 2))
      = -2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) + 2 * S ^ (1 / 2 : ℝ) := by ring
  rw [this]
  linarith

/-- info: 'FormalResearch.SignUncertainty.mb_eps_sq_u0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_eps_sq_u0_le

/-- info: 'FormalResearch.SignUncertainty.mb_L_le_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_L_le_far

/-- info: 'FormalResearch.SignUncertainty.mb_u0_rpow_neg_eleven_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_u0_rpow_neg_eleven_halves

/-- info: 'FormalResearch.SignUncertainty.mb_threeEighths_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_threeEighths_rpow

/-- info: 'FormalResearch.SignUncertainty.mb_sqrt_vdc_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_sqrt_vdc_lower

/-- info: 'FormalResearch.SignUncertainty.mb_div_eps_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_div_eps_rpow

/-- info: 'FormalResearch.SignUncertainty.mb_psi2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_psi2_le

/-- info: 'FormalResearch.SignUncertainty.mb_int_sqrt_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_int_sqrt_small

/-- info: 'FormalResearch.SignUncertainty.mb_int_neg_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_int_neg_three_halves

end FormalResearch.SignUncertainty
