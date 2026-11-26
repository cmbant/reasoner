module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasPlb

/-!
# Elementary bounds for the edge phase `m` used in the Step 4 regime check

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 4 (`Δ_{3/2}` and `τ₀`-vs-`L₀` comparisons),
from `mat:T4`(f)(M2): `t/(1+t²) ≤ m'(t) ≤ (π²/6) t/(1+t²)`.

* `hankelEdgeM_le_sq`: `m(t) ≤ (π²/12) t²`;
* `hankelEdgeM_sub_log_mono`: `½log(1+b²) - ½log(1+a²) ≤ m(b) - m(a)` for `0 ≤ a ≤ b` (so `m(t) ≥ ½log(1+t²)`);
* `hankelEdge_delta32_ge`: `Δ_{3/2} := m(3τ₀/2) - m(τ₀) ≥ (5/26) min(τ₀², 1)`;
* `hankelEdge_delta32_ge_L`: `m(τ₀) ≤ τ₀²` and `Δ_{3/2} ≥ (5/26) min(m(τ₀), 1)`.

**Proved**, unconditional.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtOuter in
lemma hankelEdgeM'_le {t : ℝ} (ht : 0 < t) : hankelEdgeM' t ≤ π ^ 2 / 6 * t := by
  have h := (mPrime_bounds ht).2
  rw [mPrime_eq_hankelEdgeM' ht] at h
  refine h.trans ?_
  have : t / (1 + t ^ 2) ≤ t := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg t, ht]
  exact mul_le_mul_of_nonneg_left this (by positivity)

open FormalResearch.SignUncertainty.CtOuter in
lemma hankelEdgeM'_ge_simple {t : ℝ} (ht : 0 < t) : t / (1 + t ^ 2) ≤ hankelEdgeM' t := by
  have h := (mPrime_bounds ht).1
  rwa [mPrime_eq_hankelEdgeM' ht] at h

/-- `m(t) ≤ (π²/12) t²` for `t ≥ 0`. -/
theorem hankelEdgeM_le_sq {t : ℝ} (ht : 0 ≤ t) : hankelEdgeM t ≤ π ^ 2 / 12 * t ^ 2 := by
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt (fun x : ℝ => π ^ 2 / 12 * x ^ 2 - hankelEdgeM x)
      (π ^ 2 / 12 * (2 * s) - hankelEdgeM' s) s := by
    intro s hs
    have := ((hasDerivAt_pow 2 s).const_mul (π ^ 2 / 12)).sub (hankelEdgeM_hasDerivAt hs)
    convert this using 1
    simp
  have hmono : MonotoneOn (fun x : ℝ => π ^ 2 / 12 * x ^ 2 - hankelEdgeM x) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuousOn_const.mul (continuousOn_id.pow 2)).sub hankelEdgeM_continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (hd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s hs).deriv]
      have := hankelEdgeM'_le hs
      nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp only [hankelEdgeM_zero] at this
  nlinarith

lemma hasDerivAt_half_log (s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.log (1 + x ^ 2) / 2) (s / (1 + s ^ 2)) s := by
  have h0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * s) s := by
    have := (hasDerivAt_pow 2 s).const_add 1
    convert this using 1; simp
  have hne : (1 + s ^ 2) ≠ 0 := by positivity
  have := (h0.log hne).div_const 2
  convert this using 1
  field_simp

/-- `½log(1+b²) - ½log(1+a²) ≤ m(b) - m(a)` for `0 ≤ a ≤ b`. -/
theorem hankelEdgeM_sub_log_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.log (1 + b ^ 2) / 2 - Real.log (1 + a ^ 2) / 2 ≤ hankelEdgeM b - hankelEdgeM a := by
  have hmono : MonotoneOn (fun x : ℝ => hankelEdgeM x - Real.log (1 + x ^ 2) / 2) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine hankelEdgeM_continuousOn.sub ?_
      exact (ContinuousOn.log (by fun_prop : ContinuousOn (fun s : ℝ => 1 + s ^ 2) (Ici 0))
        (fun s _ => by positivity)).div_const 2
    · intro s hs
      rw [interior_Ici] at hs
      exact ((hankelEdgeM_hasDerivAt hs).sub (hasDerivAt_half_log s)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hd : HasDerivAt (fun x : ℝ => hankelEdgeM x - Real.log (1 + x ^ 2) / 2)
          (hankelEdgeM' s - s / (1 + s ^ 2)) s := (hankelEdgeM_hasDerivAt hs).sub (hasDerivAt_half_log s)
      rw [hd.deriv]
      have := hankelEdgeM'_ge_simple hs
      linarith
  have := hmono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab)) hab
  simp only at this
  linarith

/-- `m(3τ₀/2) - m(τ₀) ≥ (5/4)τ₀² / (2 + (9/2)τ₀²)`. -/
theorem hankelEdge_delta32_ge_aux {τ0 : ℝ} (hτ0 : 0 < τ0) :
    5 / 4 * τ0 ^ 2 / (2 + 9 / 2 * τ0 ^ 2) ≤ hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 := by
  have h := hankelEdgeM_sub_log_mono hτ0.le (by linarith : τ0 ≤ 3 * τ0 / 2)
  refine le_trans ?_ h
  set y : ℝ := (1 + (3 * τ0 / 2) ^ 2) / (1 + τ0 ^ 2) with hy
  have hypos : 0 < y := by positivity
  have hlog : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hypos
  have e : Real.log (1 + (3 * τ0 / 2) ^ 2) / 2 - Real.log (1 + τ0 ^ 2) / 2 = Real.log y / 2 := by
    rw [hy, Real.log_div (by positivity) (by positivity)]; ring
  rw [e]
  have e2 : (1 - y⁻¹) / 2 = 5 / 4 * τ0 ^ 2 / (2 + 9 / 2 * τ0 ^ 2) := by
    rw [hy]; field_simp; ring
  rw [← e2]; linarith

/-- `Δ_{3/2} ≥ (5/26) min(τ₀², 1)`. -/
theorem hankelEdge_delta32_ge {τ0 : ℝ} (hτ0 : 0 < τ0) :
    5 / 26 * min (τ0 ^ 2) 1 ≤ hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 := by
  refine le_trans ?_ (hankelEdge_delta32_ge_aux hτ0)
  rw [le_div_iff₀ (by positivity)]
  rcases le_total (τ0 ^ 2) 1 with h | h
  · rw [min_eq_left h]; nlinarith [sq_nonneg τ0, mul_nonneg (sq_nonneg τ0) (sq_nonneg τ0)]
  · rw [min_eq_right h]; nlinarith [sq_nonneg τ0]

/-- In terms of `L₀ = m(τ₀)`: `τ₀² ≥ L₀` and `Δ_{3/2} ≥ (5/26) min(L₀, 1)`. -/
theorem hankelEdge_delta32_ge_L {τ0 : ℝ} (hτ0 : 0 < τ0) :
    hankelEdgeM τ0 ≤ τ0 ^ 2 ∧ 5 / 26 * min (hankelEdgeM τ0) 1 ≤ hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 := by
  have h1 : hankelEdgeM τ0 ≤ τ0 ^ 2 := by
    have := hankelEdgeM_le_sq hτ0.le
    have hπ : π ^ 2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith [sq_nonneg τ0]
  refine ⟨h1, le_trans ?_ (hankelEdge_delta32_ge hτ0)⟩
  exact mul_le_mul_of_nonneg_left (min_le_min h1 le_rfl) (by norm_num)

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_le_sq

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_sub_log_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_sub_log_mono

/-- info: 'FormalResearch.SignUncertainty.hankelEdge_delta32_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdge_delta32_ge

/-- info: 'FormalResearch.SignUncertainty.hankelEdge_delta32_ge_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdge_delta32_ge_L

end FormalResearch.SignUncertainty
