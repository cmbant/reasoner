module

public import FormalResearch.SignUncertainty.DeepLobeRegionII

/-!
# Deep lobe, region `1/π² - 1/48 < ξ < 1/π² - R c^{-2/3}` (`lem:radial-compactness`, Step 2)

With `t = c^{1/3}`, `a = 1/π² - Δ/c ∈ (R/t², 1/48)` and `s = 2 √(3a)` the pointwise bound of
`rho0_abs_f_le` gives `ρ₀|f|(Δ) ≤ (80 M/t) e^{-5R^{3/2}} e^{-10 (c/π² - Δ)/t}`; integrating the exponential
gives `∫ ≤ 8 M e^{-5R^{3/2}}` (`deepLobe_regionI`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

set_option maxHeartbeats 1600000 in
lemma regionI_pointwise {c ε : ℝ} (hc : 56 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {t R Δ : ℝ} (ht0 : 0 < t) (htc : t ^ 3 = c) (hR : 1 ≤ R)
    (hΔ1 : c * (1 / Real.pi ^ 2 - 1 / 48) < Δ) (hΔ2 : Δ < c / Real.pi ^ 2 - R * t) :
    |f Δ| * hankelRho0 c Δ ≤ (80 * hankelMass c f / t) * Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) *
      Real.exp (-(10 * (c / Real.pi ^ 2 - Δ) / t)) := by
  have hc0 : 0 < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hpi2' : 9.869 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hM0 : 0 ≤ hankelMass c f := hankelMass_nonneg hc0 f
  have ht2 : 14 < t ^ 2 := by nlinarith [sq_nonneg (t - 3.8), sq_nonneg t]
  set ξ : ℝ := Δ / c with hξdef
  have hcξ : c * ξ = Δ := by rw [hξdef]; field_simp
  set a : ℝ := 1 / Real.pi ^ 2 - ξ with hadef
  have hΔpos : 0 < Δ := by
    refine lt_of_le_of_lt (mul_nonneg hc0.le ?_) hΔ1
    rw [sub_nonneg, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hξ : 0 < ξ := div_pos hΔpos hc0
  have hca : c * a = c / Real.pi ^ 2 - Δ := by rw [hadef, ← hcξ]; field_simp
  have ha : 0 < a := by
    have h1 : 0 < c * a := by rw [hca]; nlinarith [mul_pos ht0 (by linarith : (0:ℝ) < R)]
    exact (mul_pos_iff_of_pos_left hc0).mp h1
  have ha48 : a < 1 / 48 := by
    have : c * a < c * (1 / 48) := by
      rw [hca]; nlinarith
    exact lt_of_mul_lt_mul_left this hc0.le
  have hcaR : R * t < c * a := by rw [hca]; linarith
  set r : ℝ := Real.sqrt a with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr ha
  have hra : r * r = a := Real.mul_self_sqrt ha.le
  set y : ℝ := t * r with hydef
  have hy0 : 0 < y := mul_pos ht0 hr0
  have hy2 : y ^ 2 = t ^ 2 * a := by rw [hydef, ← hra]; ring
  have hca' : c * a = t ^ 3 * a := by rw [htc]
  have hyR : R ≤ y ^ 2 := by
    rw [hy2]; nlinarith [mul_pos ht0 ht0]
  have hy1 : 1 ≤ y := by nlinarith
  have hysq : Real.sqrt R ≤ y := by
    calc Real.sqrt R ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hyR
      _ = y := Real.sqrt_sq hy0.le
  have hy2' : y ^ 2 = (c / Real.pi ^ 2 - Δ) / t := by
    rw [hy2, ← hca, ← htc]; field_simp
  have hy3 : c * a * r = y ^ 3 := by rw [hca', hydef]; rw [← hra]; ring
  -- apply the pointwise bound
  set s : ℝ := 2 * Real.sqrt (3 * a) with hsdef
  have h3 : Real.sqrt (3 * a) = Real.sqrt 3 * r := Real.sqrt_mul (by norm_num) a
  have hs3 : 1.732 < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs3' : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < s := by rw [hsdef]; have := Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 3 * a); linarith
  have hs12 : s ≤ 1 / 2 := by
    rw [hsdef]
    have : Real.sqrt (3 * a) ≤ 1 / 4 := by
      calc Real.sqrt (3 * a) ≤ Real.sqrt ((1 / 4) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 1 / 4 := Real.sqrt_sq (by norm_num)
    linarith
  have hcs : c * s = 2 * Real.sqrt 3 * t ^ 2 * y := by
    rw [hsdef, h3, ← htc, hydef]; ring
  have hk : 28 ≤ c * s := by
    rw [hcs]
    nlinarith [mul_le_mul hs3.le hy1 (by norm_num) (by linarith : (0:ℝ) ≤ Real.sqrt 3), mul_pos ht0 ht0]
  have h := rho0_abs_f_le (by linarith : 3 / 2 < c) hf hε hs0 hs12 hk hξ
  rw [hcξ] at h
  rw [mul_comm]
  refine h.trans ?_
  -- exponent
  have hlog : Real.log (Real.pi ^ 2 * ξ) ≤ -(Real.pi ^ 2 * a) := by
    have hpx : 0 < Real.pi ^ 2 * ξ := by positivity
    have := Real.log_le_sub_one_of_pos hpx
    have e : Real.pi ^ 2 * ξ = 1 - Real.pi ^ 2 * a := by
      rw [hadef]; field_simp; ring
    rw [e] at this ⊢; linarith
  have hexp1 : c * ((4 / 9) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ)) ≤ -(15 * y ^ 3) := by
    have h1 : (4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ) ≤ -(15 * (a * r)) := by
      have : s * Real.log (Real.pi ^ 2 * ξ) ≤ s * (-(Real.pi ^ 2 * a)) := mul_le_mul_of_nonneg_left hlog hs0.le
      have h2 : (4 / 9 : ℝ) * s ^ 3 - Real.pi ^ 2 * a * s ≤ -15 * (a * r) := by
        have := deep_lobe_num1 ha
        rwa [← hsdef, ← hrdef] at this
      linarith
    have h3' := mul_le_mul_of_nonneg_left h1 hc0.le
    have e : c * (-(15 * (a * r))) = -(15 * y ^ 3) := by rw [← hy3]; ring
    exact h3'.trans e.le
  have hRy : R ^ ((3 : ℝ) / 2) ≤ y ^ 3 := by
    have e : R ^ ((3 : ℝ) / 2) = (Real.sqrt R) ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [e]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hysq 3
  have hy23 : y ^ 2 ≤ y ^ 3 := by nlinarith [sq_nonneg y]
  have hE : Real.exp (c * ((4 / 9) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) ≤
      Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) * Real.exp (-(10 * (c / Real.pi ^ 2 - Δ) / t)) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    have : 10 * (c / Real.pi ^ 2 - Δ) / t = 10 * y ^ 2 := by rw [hy2']; ring
    rw [this]; nlinarith
  -- denominator
  have hX : 0.6 * t ≤ Real.sqrt (c * (2 * (3 / 56 : ℝ) * s)) := by
    calc 0.6 * t = Real.sqrt ((0.6 * t) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by
        have : c * (2 * (3 / 56 : ℝ) * s) = (3 / 28) * (c * s) := by ring
        rw [this, hcs]
        nlinarith [mul_le_mul hs3.le hy1 (by norm_num) (by linarith : (0:ℝ) ≤ Real.sqrt 3),
          mul_pos ht0 ht0])
  have e1 : Real.exp (1 / (6 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have e2 : Real.exp (1 / (4 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hF : 1 / (2 * Real.pi * ξ) ≤ 2 := by
    have hxi : 1 / Real.pi ^ 2 - 1 / 48 < ξ := by
      rw [hξdef, lt_div_iff₀ hc0]; linarith
    have h1 : Real.pi ≤ 4 * Real.pi ^ 2 * ξ := by
      have : Real.pi ^ 2 * (1 / Real.pi ^ 2 - 1 / 48) < Real.pi ^ 2 * ξ :=
        mul_lt_mul_of_pos_left hxi (by positivity)
      have e : Real.pi ^ 2 * (1 / Real.pi ^ 2 - 1 / 48) = 1 - Real.pi ^ 2 / 48 := by field_simp
      nlinarith [Real.pi_lt_d4]
    have h2 : 1 ≤ 4 * Real.pi * ξ := by
      by_contra hlt; push_neg at hlt
      nlinarith [mul_lt_mul_of_pos_left hlt hpi]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  set E' := Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) * Real.exp (-(10 * (c / Real.pi ^ 2 - Δ) / t)) with hE'
  have hE'0 : 0 ≤ E' := by positivity
  have hN : 18 * hankelMass c f * Real.exp (1 / (6 * c)) * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) ≤
      18 * hankelMass c f * (11 / 10) * (11 / 10) * E' := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ 18 * hankelMass c f)) e2
      (Real.exp_pos _).le (by positivity)
    exact mul_le_mul this hE (Real.exp_pos _).le (by positivity)
  have hdiv := div_le_div₀ (by positivity : 0 ≤ 18 * hankelMass c f * (11 / 10) * (11 / 10) * E') hN
    (by positivity : 0 < 0.6 * t) hX
  refine (mul_le_mul hF hdiv (by positivity) (by norm_num)).trans ?_
  have e72 : 2 * (18 * hankelMass c f * (11 / 10) * (11 / 10) * E' / (0.6 * t)) =
      (72.6 * hankelMass c f / t) * E' := by
    field_simp; norm_num; ring
  rw [e72, mul_assoc (80 * hankelMass c f / t)]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by nlinarith) ht0.le) hE'0

end FormalResearch.SignUncertainty
