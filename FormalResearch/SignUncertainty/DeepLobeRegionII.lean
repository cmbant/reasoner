module

public import FormalResearch.SignUncertainty.DeepLobePointwise
public import FormalResearch.SignUncertainty.DeepLobeNumerics

/-!
# Deep lobe, region `ξ ≤ 1/π² - 1/48` (`lem:radial-compactness`, Step 2)

For `c ≥ 56`: `∫_0^{c(1/π² - 1/48)} |f| ρ₀ ≤ 8 M[f] e^{-c/25}` (`deepLobe_regionII`), from the pointwise bound at
`s = 1/2`: `ρ₀|f|(Δ) ≤ B Δ^{c/2-1}`, `∫_0^{Δ₁} Δ^{c/2-1} = Δ₁^{c/2}/(c/2)` and `π² Δ₁/c = 1 - π²/48`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

lemma exp_le_of_small {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 50) : Real.exp x ≤ 11 / 10 := by
  have h : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x, mul_le_mul_of_nonneg_left h (Real.exp_pos x).le]

/-- The pointwise bound at `s = 1/2`: `ρ₀|f|(Δ) ≤ B Δ^{c/2-1}`. -/
lemma regionII_pointwise {c ε : ℝ} (hc : 56 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {Δ : ℝ} (hΔ : 0 < Δ) :
    |f Δ| * hankelRho0 c Δ ≤
      (18 * hankelMass c f * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
          Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) * ((c / (2 * Real.pi)) * (Real.pi ^ 2 / c) ^ (c / 2))) *
        Δ ^ (c / 2 - 1) := by
  have hc0 : 0 < c := by linarith
  have hξ : 0 < Δ / c := div_pos hΔ hc0
  have hcξ : c * (Δ / c) = Δ := by field_simp
  have h := rho0_abs_f_le (by linarith : 3 / 2 < c) hf hε (s := 1 / 2) (ξ := Δ / c) (by norm_num)
    le_rfl (by linarith) hξ
  rw [hcξ] at h
  rw [mul_comm]
  refine h.trans (le_of_eq ?_)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpow : (Real.pi ^ 2 * (Δ / c)) ^ (c / 2) = (Real.pi ^ 2 / c) ^ (c / 2) * Δ ^ (c / 2) := by
    rw [show Real.pi ^ 2 * (Δ / c) = (Real.pi ^ 2 / c) * Δ by ring, Real.mul_rpow (by positivity) hΔ.le]
  have hexp : Real.exp (c * ((4 / 9 : ℝ) * (1 / 2) ^ 3 + (1 / 2) * Real.log (Real.pi ^ 2 * (Δ / c)))) =
      Real.exp (c / 18) * (Real.pi ^ 2 * (Δ / c)) ^ (c / 2) := by
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]; congr 1; ring
  have hΔr : Δ ^ (c / 2 - 1) = Δ ^ (c / 2) / Δ := Real.rpow_sub_one hΔ.ne' _
  rw [hexp, hpow, hΔr]
  have hs : 0 < Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) := Real.sqrt_pos.mpr (by positivity)
  field_simp

theorem deepLobe_regionII {c ε : ℝ} (hc : 56 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) :
    ∫ Δ in Ioc (0 : ℝ) (c * (1 / Real.pi ^ 2 - 1 / 48)), |f Δ| * hankelRho0 c Δ ≤
      8 * hankelMass c f * Real.exp (-(c / 25)) := by
  have hc0 : 0 < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 48 := by nlinarith [Real.pi_lt_d2]
  have hpi2' : 9.869 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d4]
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  have hΔ₁pos : 0 < Δ₁ := by
    rw [hΔ₁]; refine mul_pos hc0 ?_
    rw [sub_pos, div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  set M := hankelMass c f with hM
  have hM0 : 0 ≤ M := hankelMass_nonneg hc0 f
  set B : ℝ := 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
      Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) * ((c / (2 * Real.pi)) * (Real.pi ^ 2 / c) ^ (c / 2))
    with hB
  have hr : -1 < c / 2 - 1 := by linarith
  have hRint : IntervalIntegrable (fun Δ : ℝ => B * Δ ^ (c / 2 - 1)) volume 0 Δ₁ :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul B
  have hLint : IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioc 0 Δ₁) :=
    (abs_mul_rho0_integrableOn hc0 hf.int).mono_set Ioc_subset_Ioi_self
  have hmono : ∫ Δ in Ioc (0 : ℝ) Δ₁, |f Δ| * hankelRho0 c Δ ≤
      ∫ Δ in Ioc (0 : ℝ) Δ₁, B * Δ ^ (c / 2 - 1) :=
    setIntegral_mono_on hLint ((intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ₁pos.le).mp hRint)
      measurableSet_Ioc (fun Δ hΔ => regionII_pointwise hc hf hε hΔ.1)
  refine hmono.trans ?_
  rw [← intervalIntegral.integral_of_le hΔ₁pos.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hr)]
  rw [show c / 2 - 1 + 1 = c / 2 by ring, Real.zero_rpow (by linarith), sub_zero]
  -- algebra: B * (Δ₁^{c/2} / (c/2)) = Q/π * (1 - π²/48)^{c/2}
  have hΔ₁c : Real.pi ^ 2 / c * Δ₁ = 1 - Real.pi ^ 2 / 48 := by
    rw [hΔ₁]; field_simp
  have hpowx : (Real.pi ^ 2 / c) ^ (c / 2) * Δ₁ ^ (c / 2) = (1 - Real.pi ^ 2 / 48) ^ (c / 2) := by
    rw [← Real.mul_rpow (by positivity) hΔ₁pos.le, hΔ₁c]
  have hx0 : 0 < 1 - Real.pi ^ 2 / 48 := by linarith
  have hxexp : (1 - Real.pi ^ 2 / 48) ^ (c / 2) ≤ Real.exp (-(Real.pi ^ 2 * c / 96)) := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    have := Real.log_le_sub_one_of_pos hx0
    nlinarith [this]
  have hsq : 0 < Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) := Real.sqrt_pos.mpr (by positivity)
  have hsq3 : Real.sqrt 3 ≤ Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hs3 : 1.732 < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have e1 : Real.exp (1 / (6 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have e2 : Real.exp (1 / (4 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have e3 : Real.exp (c / 18) * Real.exp (-(Real.pi ^ 2 * c / 96)) ≤ Real.exp (-(c / 25)) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    nlinarith [deep_lobe_num3, mul_le_mul_of_nonneg_left deep_lobe_num3 hc0.le]
  have hmain : B * ((Δ₁ ^ (c / 2)) / (c / 2)) =
      18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi *
          ((Real.pi ^ 2 / c) ^ (c / 2) * Δ₁ ^ (c / 2)) := by
    rw [hB]; field_simp
  rw [hmain, hpowx]
  have hpos1 : 0 ≤ 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi := by positivity
  calc 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi * (1 - Real.pi ^ 2 / 48) ^ (c / 2)
      ≤ 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) * Real.exp (c / 18) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi * Real.exp (-(Real.pi ^ 2 * c / 96)) :=
        mul_le_mul_of_nonneg_left hxexp hpos1
    _ = (18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) /
          Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi) *
        (Real.exp (c / 18) * Real.exp (-(Real.pi ^ 2 * c / 96))) := by ring
    _ ≤ (8 * M) * Real.exp (-(c / 25)) := by
        have hcoef : 18 * M * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) /
            Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) / Real.pi ≤ 8 * M := by
          rw [div_div, div_le_iff₀ (by positivity)]
          have : Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) ≤ 11 / 10 * (11 / 10) :=
            mul_le_mul e1 e2 (Real.exp_pos _).le (by norm_num)
          have hden : 1.732 * 3.14 ≤ Real.sqrt (c * (2 * (3 / 56 : ℝ) * (1 / 2))) * Real.pi := by
            have := mul_le_mul (hs3.le.trans hsq3) Real.pi_gt_d2.le (by norm_num) hsq.le
            linarith
          have h18 : 18 * M * (Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c))) ≤ 18 * M * (11 / 10 * (11 / 10)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hden hM0]
        exact mul_le_mul (by simpa [mul_assoc] using hcoef) e3 (by positivity) (by positivity)
    _ = 8 * M * Real.exp (-(c / 25)) := by ring

/-- info: 'FormalResearch.SignUncertainty.deepLobe_regionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deepLobe_regionII

/-- info: 'FormalResearch.SignUncertainty.deep_lobe_num1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deep_lobe_num1

end FormalResearch.SignUncertainty
