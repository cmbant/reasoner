module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicTaperBuild
public import FormalResearch.SignUncertainty.CtDyadicSigma

/-!
# `ct:dyadic`: the paper's regime inequalities for large `c`

`constant_terms_lower.tex`, `ct:dyadic` (4), `ct:boas` Step 5: the concrete large-`c` regime of the taper and of the block
classes, derived from `c ≥ c₀`.

* **`taperBand_regime`**: there is `γ > 0` such that for every `0 < c₁ ≤ γ` ("`c₁` small") there is `c₀` with `TaperBand ε c R`
  (hence `TaperChartInputs ε c R 2`) for all `c ≥ c₀` and all radii `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` of `ct:dyadic` (2) (`4c₁² ≤ ρ₁`
  gives `R ≤ ρ₁c^{2/3}` and `c₁²c^{2/3} ≥ 1` is `c ≥ c₁⁻³`);
* **`sigma_regime_three_le`, `sigma_regime_two_log`, `sigma_regime_reg`**: for `c ≥ e⁶`, `L_far = log(π² log c)` satisfies
  `3 ≤ L_far` and `L_far + 2 ≤ 2 log c`; and for `a ≥ κ c^{-2/21}` (`κ > 0`; `a = (5/6)L_min` with `L_min ≍ c^{-2/21}`) and
  `c ≥ c₀(κ)`, `2000 log c ≤ c√a`;
* **`boas_s_classes_large`**: `boas_s_classes` with its regime hypotheses discharged from `c ≥ c₀(κ)`.

**Proved**, unconditional.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

/-- **`TaperBand` for the radii of `ct:dyadic` (2)**: for `c₁` small and `c` large, every `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]`. -/
theorem taperBand_regime {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → ∃ c₀ : ℝ, 3 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ R : ℝ,
      c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) → TaperBand ε c R := by
  obtain ⟨ρ₁, c₀, hρ, hc₀, h⟩ := taperBand hε
  refine ⟨min 1 (ρ₁ / 4), lt_min one_pos (by positivity), fun c₁ hc₁ hγ => ?_⟩
  have hc₁1 : c₁ ≤ 1 := hγ.trans (min_le_left _ _)
  have hc₁ρ : c₁ ≤ ρ₁ / 4 := hγ.trans (min_le_right _ _)
  refine ⟨max c₀ ((c₁⁻¹) ^ 3), (hc₀.trans (le_max_left _ _)), fun c hc R hR1 hR2 => ?_⟩
  have hcc₀ : c₀ ≤ c := (le_max_left _ _).trans hc
  have hcc₁ : (c₁⁻¹) ^ 3 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hi : 0 < c₁⁻¹ := inv_pos.2 hc₁
  have h23 : (c₁⁻¹) ^ 2 ≤ c ^ (2 / 3 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hcc₁ (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have e : ((c₁⁻¹) ^ 3) ^ (2 / 3 : ℝ) = (c₁⁻¹) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hi.le]; norm_num
    rwa [e] at this
  have hR1' : 1 ≤ R := by
    have : c₁ ^ 2 * (c₁⁻¹) ^ 2 = 1 := by field_simp
    have h2 : c₁ ^ 2 * (c₁⁻¹) ^ 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left h23 (by positivity)
    linarith
  refine h c hcc₀ R hR1' ?_
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h4 : 4 * c₁ ^ 2 ≤ ρ₁ := by nlinarith
  calc R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := hR2
    _ ≤ ρ₁ * c ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_right h4 hc23.le

/-- `3 ≤ L_far = log(π² log c)` for `c ≥ e⁶`. -/
lemma sigma_regime_three_le {c : ℝ} (hc : Real.exp 6 ≤ c) : 3 ≤ Real.log (π ^ 2 * Real.log c) := by
  have ht : 6 ≤ Real.log c := (Real.le_log_iff_exp_le (by linarith [Real.exp_pos 6])).2 hc
  have hp : (9 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  rw [Real.le_log_iff_exp_le (by positivity)]
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := by gcongr
  nlinarith

/-- `L_far + 2 ≤ 2 log c` for `c ≥ e⁶`. -/
lemma sigma_regime_two_log {c : ℝ} (hc : Real.exp 6 ≤ c) : Real.log (π ^ 2 * Real.log c) + 2 ≤ 2 * Real.log c := by
  have ht : 6 ≤ Real.log c := (Real.le_log_iff_exp_le (by linarith [Real.exp_pos 6])).2 hc
  have ht0 : 0 < Real.log c := by linarith
  have hπ := Real.pi_pos
  rw [Real.log_mul (by positivity) ht0.ne', Real.log_pow]
  have h1 : Real.log π ≤ π - 1 := Real.log_le_sub_one_of_pos hπ
  have h2 : Real.log (Real.log c) ≤ Real.log c - 1 := Real.log_le_sub_one_of_pos ht0
  have := Real.pi_lt_d2
  push_cast
  linarith

/-- **`2000 log c ≤ c√a`** for `a ≥ κ c^{-2/21}` (`a = (5/6)L_min`, `L_min ≍ c^{-2/21}`) and `c ≥ max 1 (84000²/κ)`. -/
lemma sigma_regime_reg {κ c a : ℝ} (hκ : 0 < κ) (hc : max 1 (84000 ^ 2 / κ) ≤ c) (ha : κ * c ^ (-(2 / 21) : ℝ) ≤ a) :
    2000 * Real.log c ≤ c * √a := by
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hN : 84000 ^ 2 / κ ≤ c := (le_max_right _ _).trans hc
  have hlog : Real.log c ≤ c ^ (1 / 42 : ℝ) / (1 / 42) := Real.log_le_rpow_div hc0.le (by norm_num)
  have hlog0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hy : 0 < c ^ (1 / 42 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h1 : 2000 * Real.log c ≤ 84000 * c ^ (1 / 42 : ℝ) := by
    have : c ^ (1 / 42 : ℝ) / (1 / 42) = 42 * c ^ (1 / 42 : ℝ) := by field_simp
    linarith
  have hsq : (c ^ (1 / 42 : ℝ)) ^ 2 = c ^ (1 / 21 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hc2 : c ^ 2 * c ^ (-(2 / 21) : ℝ) = c ^ (1 / 21 : ℝ) * c ^ (13 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
  have h137 : c ≤ c ^ (13 / 7 : ℝ) := by
    calc c = c ^ (1 : ℝ) := (Real.rpow_one c).symm
      _ ≤ c ^ (13 / 7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hκc : 84000 ^ 2 ≤ κ * c ^ (13 / 7 : ℝ) := by
    have : 84000 ^ 2 ≤ κ * c := by
      have := (div_le_iff₀ hκ).1 hN
      linarith
    nlinarith
  have hy21 : 0 < c ^ (1 / 21 : ℝ) := Real.rpow_pos_of_pos hc0 _
  -- squares
  have hsqle : (2000 * Real.log c) ^ 2 ≤ (c * √a) ^ 2 := by
    have ha0 : 0 ≤ a := le_trans (by positivity) ha
    rw [mul_pow c, Real.sq_sqrt ha0]
    calc (2000 * Real.log c) ^ 2 ≤ (84000 * c ^ (1 / 42 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = 84000 ^ 2 * c ^ (1 / 21 : ℝ) := by rw [mul_pow, hsq]
      _ ≤ (κ * c ^ (13 / 7 : ℝ)) * c ^ (1 / 21 : ℝ) := mul_le_mul_of_nonneg_right hκc hy21.le
      _ = κ * (c ^ 2 * c ^ (-(2 / 21) : ℝ)) := by rw [hc2]; ring
      _ ≤ c ^ 2 * a := by
          have := mul_le_mul_of_nonneg_left ha (sq_nonneg c)
          nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsqle

/-- **`boas_s_classes` in the regime `c ≥ c₀(κ)`** (`ct:Bj-pointwise` (e)): for `c ≥ max (e⁶) (84000²/κ)`, `κ c^{-2/21} ≤ a ≤ 1`,
`L_far = log(π² log c)` and a block with `L_j ≤ L_far + 1`, `s_j` is in one of the two classes; no regime hypothesis remains. -/
theorem boas_s_classes_large {κ c a : ℝ} (hκ : 0 < κ) (hc : max (Real.exp 6) (max 1 (84000 ^ 2 / κ)) ≤ c)
    (ha : κ * c ^ (-(2 / 21) : ℝ) ≤ a) (ha1 : a ≤ 1) {j : ℕ}
    (hj : tentNode a (j + 1) ≤ Real.log (π ^ 2 * Real.log c) + 1) :
    tapMsig c a j * boasW c a j ≤ Real.exp (-(Real.log c ^ 2)) ∨
      (tapMsig c a j * boasW c a j ≤ 2000 * Real.log c / c ∧
        tentQ a j ⊆ Ici (Real.log (π ^ 2 * Real.log c) - 5 / 2)) := by
  have h6 : Real.exp 6 ≤ c := (le_max_left _ _).trans hc
  have hm : max 1 (84000 ^ 2 / κ) ≤ c := (le_max_right _ _).trans hc
  have hex : (3 : ℝ) ≤ c := by
    have : (3 : ℝ) ≤ Real.exp 6 := by
      have := Real.add_one_le_exp (6 : ℝ)
      linarith
    linarith
  have ht : 0 < Real.log c := Real.log_pos (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  exact boas_s_classes hex ha0 ha1 (Real.exp_log (by positivity)) (sigma_regime_three_le h6)
    (sigma_regime_two_log h6) (sigma_regime_reg hκ hm ha) hj

/-- info: 'FormalResearch.SignUncertainty.taperBand_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taperBand_regime

/-- info: 'FormalResearch.SignUncertainty.boas_s_classes_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_s_classes_large

end FormalResearch.SignUncertainty
