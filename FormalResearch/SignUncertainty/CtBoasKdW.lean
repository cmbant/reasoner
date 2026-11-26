module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFreeze

/-!
# `ct:boas-ineq`: the field `Kd_W` of `BoasInputs` (far-pair cost `K_{d,j} W_j² ≤ κ`)

`constant_terms_lower.tex`, proof of `ct:boas` Step 3/5: `W_j = N_j/(cτ_j)`, `N_j² = 10⁶(1 + L_j) log c`, `δ_j = min(L_j,1)/36`,
`K_{d,j} = 6/δ_j²`.  With `τ_j² ≥ L_j` (`m(τ) ≤ π²τ²/12 ≤ τ²`, `m(τ_j) = L_j`) and `L_j ≥ a`, `a ≤ 1`:
`K_{d,j} W_j² ≤ κ := 15552·10⁶ log c/(a³c²)`.  At `a = 5L_min/6 ≍ c^{-2/21}` this is `O(c^{-12/7} log c)`, so the total cost
`J κ M` of `boas_ineq_assembled` is `O(c^{-12/7} log² c)`.  **Proved**, unconditional.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `τ₀(L)² ≥ L` for `L > 0`. -/
lemma tau0_sq_ge {L : ℝ} (hL : 0 < L) : L ≤ tau0 L ^ 2 := by
  have h := hankelEdgeM_le_sq (tau0_pos hL).le
  rw [hankelEdgeM_tau0 hL] at h
  have : π ^ 2 / 12 ≤ 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  nlinarith [sq_nonneg (tau0 L)]

/-- **The field `Kd_W`**: `K_{d,j} W_j² ≤ κ = 15552·10⁶ log c/(a³c²)` for every block `j` of the node grid `x = tentNode a`
(`c ≥ 1`, `0 < a ≤ 1`). -/
theorem boas_Kd_W_field {c a : ℝ} (hc : 1 ≤ c) (ha : 0 < a) (ha1 : a ≤ 1) (j : ℕ) :
    boasKd a j * boasW c a j ^ 2 ≤ 15552000000 * Real.log c / (a ^ 3 * c ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hlog : 0 ≤ Real.log c := Real.log_nonneg hc
  set L := tentNode a (j + 1) with hL
  have hx := tentNode_strictMono ha
  have haL : a ≤ L := (hx.monotone (Nat.zero_le (j + 1)) : tentNode a 0 ≤ tentNode a (j + 1))
  have hL0 : 0 < L := lt_of_lt_of_le ha haL
  have hτ := tau0_pos hL0
  have hτ2 := tau0_sq_ge hL0
  have hℓ : 0 < min L 1 := lt_min hL0 one_pos
  have hW2 : boasW c a j ^ 2 = 1000000 * (1 + L) * Real.log c / (c * tau0 L) ^ 2 := by
    unfold boasW
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hδ : tentDelta a j = min L 1 / 36 := rfl
  have hKd : boasKd a j = 6 * 36 ^ 2 / min L 1 ^ 2 := by
    unfold boasKd; rw [hδ]; field_simp
  rw [hW2, hKd]
  -- key: `(1 + L) a³ ≤ 2 ℓ² τ²`
  have hkey : (1 + L) * a ^ 3 ≤ 2 * (min L 1 ^ 2 * tau0 L ^ 2) := by
    rcases le_total L 1 with h1 | h1
    · rw [min_eq_left h1]
      have h3 : a ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ ha.le haL 3
      calc (1 + L) * a ^ 3 ≤ 2 * L ^ 3 := by nlinarith [pow_pos ha 3]
        _ ≤ 2 * (L ^ 2 * tau0 L ^ 2) := by nlinarith [mul_le_mul_of_nonneg_left hτ2 (sq_nonneg L)]
    · rw [min_eq_right h1]
      have h3 : a ^ 3 ≤ 1 := pow_le_one₀ ha.le ha1
      nlinarith [mul_le_mul_of_nonneg_left hτ2 (zero_le_one' ℝ), pow_pos ha 3]
  have hpos1 : 0 < min L 1 ^ 2 * (c ^ 2 * tau0 L ^ 2) := by positivity
  have hpos2 : 0 < a ^ 3 * c ^ 2 := by positivity
  rw [show 6 * 36 ^ 2 / min L 1 ^ 2 * (1000000 * (1 + L) * Real.log c / (c * tau0 L) ^ 2) =
      (7776 * 1000000 * Real.log c * (1 + L)) / (min L 1 ^ 2 * (c ^ 2 * tau0 L ^ 2)) by
        field_simp; ring]
  rw [div_le_div_iff₀ hpos1 hpos2]
  have : 0 ≤ 7776 * 1000000 * Real.log c := by positivity
  have h2 := mul_le_mul_of_nonneg_left hkey (mul_nonneg this (sq_nonneg c))
  nlinarith [h2]

/-- info: 'FormalResearch.SignUncertainty.boas_Kd_W_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_Kd_W_field

end FormalResearch.SignUncertainty
