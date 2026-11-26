module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBandTop

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the eventual rates of the error terms of `CtRoscBook`

Elementary `c → ∞` facts used to absorb the error terms of the bookkeeping into `c^{-4/3}`:
`A r_∞ = O(c e^{-c/40000})`, `e^{-b c^{5/6}} = o(c^{-4/3})`, `e^{-c/25} = o(c^{-4/3})`, and `(K/c)^{12} = o(c^{-4/3})`.

All proved.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `3 A r_∞ ≤ c^{-4/3}` and `2 A r_∞ ≤ 1` for large `c` (`A = langerRadius c`, `r_∞ = hankelRinf c`). -/
lemma rate_Ar : ∀ᶠ c : ℝ in atTop,
    3 * (langerRadius c * hankelRinf c) ≤ c ^ (-(4 / 3) : ℝ) ∧ 2 * langerRadius c * hankelRinf c ≤ 1 := by
  have e1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (7 / 3 : ℝ) (1 / 40000) (by norm_num)
  set K : ℝ := 3 * (langerKappa * 4.94e-4) * (2 * |hankelTailI0|) with hK
  have := e1.const_mul K
  rw [mul_zero] at this
  filter_upwards [this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 1] with c hc hc1
  have hc0 : 0 < c := by linarith
  have hκ := langerKappa_pos
  have hA : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := rfl
  have h1 : c ^ (4 / 3 : ℝ) * (3 * (langerRadius c * hankelRinf c)) ≤
      K * (c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000) * c)) := by
    unfold hankelRinf
    rw [hA]
    have e : c ^ (4 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) = c ^ (7 / 3 : ℝ) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
    have e2 : Real.exp (-(c / 40000)) = Real.exp (-(1 / 40000) * c) := by congr 1; ring
    rw [e2]
    have hT : hankelTailI0 ≤ |hankelTailI0| := le_abs_self _
    have hp : 0 ≤ c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000) * c) := by positivity
    calc c ^ (4 / 3 : ℝ) * (3 * (c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 *
          (2 * hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000) * c))))
        = (3 * (langerKappa * 4.94e-4) * (2 * hankelTailI0)) *
            ((c ^ (4 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ))) * Real.exp (-(1 / 40000) * c)) := by ring
      _ = (3 * (langerKappa * 4.94e-4) * (2 * hankelTailI0)) * (c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000) * c)) := by rw [e]
      _ ≤ K * (c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000) * c)) := by
        refine mul_le_mul_of_nonneg_right ?_ hp
        rw [hK]
        have : 0 ≤ 3 * (langerKappa * 4.94e-4) := by positivity
        nlinarith
  have h2 : 3 * (langerRadius c * hankelRinf c) ≤ c ^ (-(4 / 3) : ℝ) := by
    have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [Real.rpow_neg hc0.le, ← one_div, le_div_iff₀ hpos, mul_comm]
    linarith
  refine ⟨h2, ?_⟩
  have h3 : c ^ (-(4 / 3) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1.le (by norm_num)
  have e : 2 * langerRadius c * hankelRinf c = 2 * (langerRadius c * hankelRinf c) := by ring
  rw [e]
  linarith

/-- `16 e^{-B y^{5/6}}`-type decay: `c^{4/3} e^{-B c^{5/6}} → 0`. -/
lemma tendsto_rpow_exp_rpow {B : ℝ} (hB : 0 < B) :
    Tendsto (fun c : ℝ => c ^ (4 / 3 : ℝ) * Real.exp (-B * c ^ (5 / 6 : ℝ))) atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (8 / 5 : ℝ) B hB).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 6))
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  simp only [Function.comp]
  rw [← Real.rpow_mul hc.le]; norm_num

/-- `16 e^{-B c^{5/6}} ≤ c^{-4/3}` for large `c`. -/
lemma rate_exp_rpow {B : ℝ} (hB : 0 < B) : ∀ᶠ c : ℝ in atTop, 16 * Real.exp (-B * c ^ (5 / 6 : ℝ)) ≤ c ^ (-(4 / 3) : ℝ) := by
  have := (tendsto_rpow_exp_rpow hB).const_mul 16
  rw [mul_zero] at this
  filter_upwards [this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
  have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  rw [Real.rpow_neg hc0.le, ← one_div, le_div_iff₀ hpos]
  linarith

/-- `16 e^{-c/25} ≤ c^{-4/3}` for large `c`. -/
lemma rate_exp_lin : ∀ᶠ c : ℝ in atTop, 16 * Real.exp (-(1 / 25) * c) ≤ c ^ (-(4 / 3) : ℝ) := by
  have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 / 3 : ℝ) (1 / 25) (by norm_num)).const_mul 16
  rw [mul_zero] at this
  filter_upwards [this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
  have hpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  rw [Real.rpow_neg hc0.le, ← one_div, le_div_iff₀ hpos]
  linarith

/-- `8 (K/c)^{12} ≤ c^{-4/3}` for large `c`. -/
lemma rate_pow_inv (K : ℝ) : ∀ᶠ c : ℝ in atTop, 8 * (K * c⁻¹) ^ 12 ≤ c ^ (-(4 / 3) : ℝ) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 32 / 3)).const_mul (8 * K ^ 12)
  rw [mul_zero] at h1
  filter_upwards [h1.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_gt_atTop 0] with c hc hc0
  have e : 8 * (K * c⁻¹) ^ 12 = (8 * K ^ 12) * c ^ (-(32 / 3) : ℝ) * c ^ (-(4 / 3) : ℝ) := by
    have h12 : (c⁻¹) ^ 12 = c ^ (-(32 / 3) : ℝ) * c ^ (-(4 / 3) : ℝ) := by
      rw [← Real.rpow_add hc0, ← Real.rpow_neg_one, ← Real.rpow_mul_natCast hc0.le]; norm_num
    rw [mul_pow, h12]; ring
  rw [e]
  have hp : 0 ≤ c ^ (-(4 / 3) : ℝ) := (Real.rpow_pos_of_pos hc0 _).le
  nlinarith

end FormalResearch.SignUncertainty
