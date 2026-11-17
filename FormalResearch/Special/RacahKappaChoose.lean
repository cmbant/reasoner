module

public import Mathlib

/-!
# Choice of the zone parameter `η`

`rk_choose_eta`: for `u > 0` there is `η ∈ (0, min(r/2, 1)]` with `2√(η/q_*) ≤ u` and `4√s·A₀(η) ≤ u/2`, `A₀(η) = 2G²(√(2c₂η)/π + 2c₂(2c₂η))/c₁` (the zone coefficient of `rk_zone_abs`).

**Claim class: proved.**
-/

@[expose] public section

namespace FormalResearch.Special

lemma rk_choose_eta {c1 c2 G sq u qs r : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hG : 0 ≤ G) (hsq : 0 < sq) (hu : 0 < u) (hqs : 0 < qs)
    (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r / 2 ∧ η ≤ 1 ∧ 2 * √(η / qs) ≤ u ∧
      4 * sq * (2 * G ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1) ≤ u / 2 := by
  set Λ : ℝ := (2 * G ^ 2 / c1) * (√(2 * c2) + 4 * c2 ^ 2) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set e0 : ℝ := u / (8 * sq * Λ + 1) with he0
  have he0p : 0 < e0 := by positivity
  refine ⟨min (r / 2) (min 1 (min (u ^ 2 * qs / 4) (e0 ^ 2))), lt_min (by positivity) (lt_min one_pos (lt_min (by positivity) (by positivity))),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_, ?_⟩
  · set η := min (r / 2) (min 1 (min (u ^ 2 * qs / 4) (e0 ^ 2))) with hη
    have h1 : η ≤ u ^ 2 * qs / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : η / qs ≤ (u / 2) ^ 2 := by
      rw [div_le_iff₀ hqs]; nlinarith
    calc 2 * √(η / qs) ≤ 2 * √((u / 2) ^ 2) := by gcongr
      _ = u := by rw [Real.sqrt_sq (by positivity)]; ring
  · set η := min (r / 2) (min 1 (min (u ^ 2 * qs / 4) (e0 ^ 2))) with hη
    have hη0 : 0 < η := lt_min (by positivity) (lt_min one_pos (lt_min (by positivity) (by positivity)))
    have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hη2 : η ≤ e0 ^ 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hse : √η ≤ e0 := by
      calc √η ≤ √(e0 ^ 2) := Real.sqrt_le_sqrt hη2
        _ = e0 := Real.sqrt_sq he0p.le
    have hηs : η ≤ √η := by
      have : √η ^ 2 = η := Real.sq_sqrt hη0.le
      have h1 : √η ≤ 1 := by rw [Real.sqrt_le_one]; exact hη1
      nlinarith [Real.sqrt_nonneg η]
    have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hsq2 : √(2 * c2 * η) = √(2 * c2) * √η := Real.sqrt_mul (by positivity) _
    have hA : (2 * G ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1) ≤ Λ * √η := by
      have h1 : √(2 * c2 * η) / Real.pi ≤ √(2 * c2) * √η := by
        rw [hsq2]
        exact div_le_self (by positivity) hπ1
      have h2 : 2 * c2 * (2 * c2 * η) ≤ 4 * c2 ^ 2 * √η := by nlinarith [mul_le_mul_of_nonneg_left hηs (by positivity : (0 : ℝ) ≤ 4 * c2 ^ 2)]
      have h3 : 2 * G ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1 ≤
          2 * G ^ 2 * (√(2 * c2) * √η + 4 * c2 ^ 2 * √η) / c1 := by
        gcongr
      refine h3.trans (le_of_eq ?_)
      rw [hΛ]; ring
    calc 4 * sq * (2 * G ^ 2 * (√(2 * c2 * η) / Real.pi + 2 * c2 * (2 * c2 * η)) / c1) ≤ 4 * sq * (Λ * √η) := by gcongr
      _ ≤ 4 * sq * (Λ * e0) := by gcongr
      _ ≤ u / 2 := by
        rw [he0]
        have : 4 * sq * (Λ * (u / (8 * sq * Λ + 1))) = (4 * sq * Λ) * u / (8 * sq * Λ + 1) := by ring
        rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg hsq.le hΛ0, hu]

end FormalResearch.Special
