module

public import FormalResearch.SignUncertainty.CtOuterP3
public import FormalResearch.SignUncertainty.CtOuter

/-!
# `θ_1^- = -3 log 2 + I_0`, `θ_1^+ = θ_1^- - π` (`ct:outer` (2), linear Taylor coefficient)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2) ("Exact Taylor coefficients"),
`ct:theta1`.  **Proved**, from `deriv_outerTheta_zero` (`θ'_-(0) = 2π∫_0^∞ u_r cosh/sinh² - 1`), the Frullani
evaluation `integral_log_ratio_mul_cosh_div_sinh_sq`, and `integral_ctU3_mul` (Mittag-Leffler).
`ctI0` is the paper's `I_0` of `eq:ct-I0`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `ν(y) = 2 u_r(y/π) cosh y / sinh² y`. -/
noncomputable def ctNu (y : ℝ) : ℝ := 2 * uR (y / π) * (Real.cosh y / Real.sinh y ^ 2)

lemma ctNu_eq {y : ℝ} (hy : 0 < y) :
    ctNu y = (Real.log (6 * (Real.sinh y - y) / y ^ 3) + ctLogRatio y - ctU3 y) *
      (Real.cosh y / Real.sinh y ^ 2) := by
  have hpi := Real.pi_pos
  set t : ℝ := y / π with ht
  have ht0 : 0 < t := by positivity
  have hyt : y = π * t := by rw [ht]; field_simp
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have h1 := sinh_gt_self hy
  have hF : Freal t = 6 * ((Real.sinh y - y) / y ^ 3) / (Real.sinh y / y * (1 + t ^ 2)) := by
    rw [hyt]
    unfold Freal mPrime
    have hs' : Real.sinh (π * t) ≠ 0 := by rw [← hyt]; exact hs.ne'
    field_simp
  have h2 : 0 < 6 * ((Real.sinh y - y) / y ^ 3) := by
    have : 0 < Real.sinh y - y := by linarith
    positivity
  have h3 : 0 < Real.sinh y / y * (1 + t ^ 2) := by positivity
  have hlog : 2 * uR t = Real.log (6 * ((Real.sinh y - y) / y ^ 3)) - Real.log (Real.sinh y / y) -
      Real.log (1 + t ^ 2) := by
    rw [uR_eq ht0.ne', ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul, hF,
      Real.log_div h2.ne' h3.ne', Real.log_mul (x := Real.sinh y / y) (y := 1 + t ^ 2) (by positivity) (by positivity)]
    ring
  have hlb : ctLogRatio y = -Real.log (Real.sinh y / y) := by
    unfold ctLogRatio; rw [← Real.log_inv, inv_div]
  have hu3 : ctU3 y = Real.log (1 + t ^ 2) := by unfold ctU3; rw [← ht]
  unfold ctNu
  rw [← ht, hlog, hlb, hu3, show 6 * ((Real.sinh y - y) / y ^ 3) = 6 * (Real.sinh y - y) / y ^ 3 by ring]
  ring

lemma integrable_ctNu : IntegrableOn ctNu (Ioi 0) := by
  have hpi := Real.pi_pos
  rw [← mul_zero π, ← integrableOn_Ioi_comp_mul_left_iff ctNu 0 hpi]
  have hint := integrable_derivMajorant.integrableOn (s := Ioi (0 : ℝ))
  refine Integrable.mono' (hint.const_mul (2 / π)) ?_ ?_
  · have hc : Continuous fun t : ℝ => 2 * uR t * Real.cosh (π * t) := by
      have := continuous_uR; fun_prop
    have hd : Continuous fun t : ℝ => Real.sinh (π * t) ^ 2 := by fun_prop
    have : (fun t : ℝ => ctNu (π * t)) = fun t => (2 * uR t * Real.cosh (π * t)) / Real.sinh (π * t) ^ 2 := by
      funext t; unfold ctNu; rw [mul_div_cancel_left₀ _ hpi.ne']; ring
    rw [this]
    exact (hc.measurable.div hd.measurable).aestronglyMeasurable
  · filter_upwards with t
    unfold ctNu derivMajorant
    rw [mul_div_cancel_left₀ _ hpi.ne', Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (by positivity : 0 ≤ Real.cosh (π * t) / Real.sinh (π * t) ^ 2)]
    have : π * |uR t| * Real.cosh (π * t) / Real.sinh (π * t) ^ 2 =
        π * (|uR t| * (Real.cosh (π * t) / Real.sinh (π * t) ^ 2)) := by ring
    rw [this]
    have hp : (0 : ℝ) < π := hpi
    calc 2 * |uR t| * (Real.cosh (π * t) / Real.sinh (π * t) ^ 2) ≤
        2 / π * (π * (|uR t| * (Real.cosh (π * t) / Real.sinh (π * t) ^ 2))) := by
          rw [← mul_assoc, div_mul_cancel₀ _ hp.ne']; ring_nf; exact le_refl _
      _ = _ := rfl

/-- `∫_0^∞ ν = I_0 + log 2·(-1)... = I_0 - 3 log 2 + 1`. -/
theorem integral_ctNu : ∫ y in Ioi (0 : ℝ), ctNu y = ctI0 - 3 * Real.log 2 + 1 := by
  have hI1 := integrable_ctLogRatio_mul
  have hI2 := integrable_ctU3_mul
  have hI3 := integrable_ctNu
  have hla : IntegrableOn (fun y : ℝ => Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2)) (Ioi 0) := by
    refine ((hI3.sub hI1).add hI2).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have := ctNu_eq (show 0 < y from hy)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [this]; ring
  have hsum : ∫ y in Ioi (0 : ℝ), ctNu y =
      ∫ y in Ioi (0 : ℝ), (Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2) +
        ctLogRatio y * (Real.cosh y / Real.sinh y ^ 2) - ctU3 y * (Real.cosh y / Real.sinh y ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [ctNu_eq (show 0 < y from hy)]; ring
  have hAB : IntegrableOn (fun y : ℝ => Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2) +
      ctLogRatio y * (Real.cosh y / Real.sinh y ^ 2)) (Ioi 0) := hla.add hI1
  rw [hsum, integral_sub hAB hI2, integral_add hla hI1]
  have e1 : ∫ y in Ioi (0 : ℝ), ctLogRatio y * (Real.cosh y / Real.sinh y ^ 2) = -Real.log 2 :=
    integral_log_ratio_mul_cosh_div_sinh_sq
  rw [e1, integral_ctU3_mul]
  unfold ctI0
  ring

/-- `2 ∫_0^∞ π u_r(t) cosh(πt)/sinh²(πt) dt = I_0 - 3 log 2 + 1`. -/
theorem two_integral_uR : 2 * (∫ t in Ioi (0 : ℝ), π * uR t * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) =
    ctI0 - 3 * Real.log 2 + 1 := by
  have hpi := Real.pi_pos
  have h := integral_comp_mul_left_Ioi' (E := ℝ) ctNu 0 hpi
  rw [mul_zero, smul_eq_mul, integral_ctNu] at h
  rw [← h, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [ctNu]
  rw [mul_div_cancel_left₀ _ hpi.ne']
  ring

theorem deriv_outerTheta_zero_eq (ε : ℝ) :
    deriv (outerTheta ε) 0 = 2 * (∫ t in Ioi (0 : ℝ), π * uR t * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) - 1 -
      (if ε = 1 then π else 0) := by
  rw [deriv_outerTheta_zero, deriv_H0_zero]
  have hre : (∫ t : ℝ, ((uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) : ℝ) : ℂ)).re =
      ∫ t : ℝ, uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) := by
    rw [integral_complex_ofReal]; simp
  rw [hre]
  have heven : (∫ t : ℝ, uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2)) =
      2 * ∫ t in Ioi (0 : ℝ), uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) := by
    rw [← integral_comp_abs (f := fun t : ℝ => uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2))]
    congr 1
    ext t
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, uR_neg, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq]
  rw [heven]
  have hcongr : ∫ t in Ioi (0 : ℝ), uR t * (π * Real.cosh (π * t) / Real.sinh (π * t) ^ 2) =
      ∫ t in Ioi (0 : ℝ), π * uR t * Real.cosh (π * t) / Real.sinh (π * t) ^ 2 :=
    setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) (fun t _ => by ring)
  rw [hcongr]

/-- **`θ_1^- = -3 log 2 + I_0`** (`ct:theta1`). -/
theorem theta_one_minus : deriv (outerTheta (-1)) 0 = -3 * Real.log 2 + ctI0 := by
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  rw [deriv_outerTheta_zero_eq, two_integral_uR]
  simp [hne]; ring

/-- **`θ_1^+ = θ_1^- - π`** (`ct:theta1`). -/
theorem theta_one_plus : deriv (outerTheta 1) 0 = -3 * Real.log 2 + ctI0 - π := by
  rw [deriv_outerTheta_zero_eq, two_integral_uR]
  simp; ring

/-- `deriv (outerTheta ε) 0 = ctTheta1 ε` for `ε = ±1`. -/
theorem deriv_outerTheta_zero_eq_ctTheta1 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    deriv (outerTheta ε) 0 = ctTheta1 ε := by
  rcases hε with rfl | rfl
  · rw [theta_one_plus]; simp [ctTheta1]
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    rw [theta_one_minus]; simp [ctTheta1, hne]

/-- **`ct:outer` (2): `θ_ε(τ) = θ_1^ε τ + θ_3 τ³ + O(τ⁵)` with the paper's `θ_1^ε`** (`ctTheta1`) and some constant `θ₃`
(its closed form `ctTheta3` is not proved). -/
theorem ct_outer_part2_taylor_theta1 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ θ₃ C : ℝ, ∀ τ : ℝ, |τ| ≤ 1 → |outerTheta ε τ - ctTheta1 ε * τ - θ₃ * τ ^ 3| ≤ C * |τ| ^ 5 := by
  obtain ⟨C, hC⟩ := outerTheta_taylor ε
  refine ⟨iteratedDeriv 3 (outerTheta ε) 0 / 6, C, fun τ hτ => ?_⟩
  have := hC τ hτ
  rwa [deriv_outerTheta_zero_eq_ctTheta1 hε] at this

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part2_taylor_theta1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part2_taylor_theta1

/-- info: 'FormalResearch.SignUncertainty.CtOuter.theta_one_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_one_minus

/-- info: 'FormalResearch.SignUncertainty.CtOuter.theta_one_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theta_one_plus

end FormalResearch.SignUncertainty.CtOuter
