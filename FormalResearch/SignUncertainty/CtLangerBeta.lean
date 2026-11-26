module

public import Mathlib
public import FormalResearch.SignUncertainty.CtCfuInv
public import FormalResearch.SignUncertainty.CtLangerEdgeChart

/-!
# The `β ↔ ξ` bridge of `ct:cfu` (1): the CFU parameters at `β = τ₀(L)²` in the Langer chart

`cfu_K_airy_beta` (`CtSdMain`) is stated in the parameter `β = τ₀²` (`NF β = L`, `AF β = a`, the Langer parameter
`a = 2^{2/3} c^{-2/3} ũ` of `ct:langer-inv`).  Here, from `ct_langer_edge` (`CtLangerEdgeChart`), for the band point `L`
(`0 < L`, `e^L - 1 ≤ 5·10⁻⁴`) and `β = τ₀(L)²`:

* `ct_NF_tau0_sq`: `NF β = L`;
* `ct_AF_tau0_sq`: `AF β = -2^{2/3} κ g(L)`, i.e. `a = 2^{2/3} c^{-2/3} ũ(ξ(L))` with `ũ = -c^{2/3} κ g(L)` (`hankelBandU`, `ctChartG`).

**Proved**, unconditional.  This identifies the CFU data `(L, a)` at `β` with the Lean series chart; the remaining `window`
inputs (`Uhat ↔ û(ũ(ξ))` and the sub-chart term) are not done here.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `NF (τ₀(L)²) = L`: the CFU parameter `β = τ₀(L)²` has `L = m(√β)`. -/
theorem ct_NF_tau0_sq {L : ℝ} (hL : 0 < L) (hL5 : Real.exp L - 1 ≤ 5e-4) :
    CtCfu.NF (tau0 L ^ 2) = L := by
  obtain ⟨hτ, hτ3, hm⟩ := tau0_band hL hL5
  have hr : tau0 L ^ 2 < CtCfu.rr := by
    have : (0.03 : ℝ) ^ 2 < CtCfu.rr := by
      unfold CtCfu.rr
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith
  have := CtCfu.hankelEdgeM_eq hτ.le hr
  rw [hm] at this
  unfold CtCfu.NF
  linarith

/-- **`AF (τ₀(L)²) = -2^{2/3} κ g(L)`** (the Langer parameter `a` at `β = τ₀(L)²`, with `-a = 2^{2/3} κ g`,
`(2/3)(-a)^{3/2} = Φ(τ₀(L); L)`). -/
theorem ct_AF_tau0_sq {L : ℝ} (hL : 0 < L) (hL5 : Real.exp L - 1 ≤ 5e-4) :
    CtCfu.AF (tau0 L ^ 2) = -((2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa * ctChartG L) := by
  obtain ⟨hτ, hτ3, hm⟩ := tau0_band hL hL5
  set τ := tau0 L with hτdef
  have hr : τ ^ 2 < CtCfu.rr := by
    have : (0.03 : ℝ) ^ 2 < CtCfu.rr := by
      unfold CtCfu.rr
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith
  have hΦ := CtCfu.edgePhi_crit hτ.le hr
  rw [hm] at hΦ
  have hE := ct_langer_edge hL hL5
  have hX : 0 < langerKappa * ctChartG L := mul_pos langerKappa_pos (ctChartG_pos hL hL5)
  set X := langerKappa * ctChartG L with hXdef
  set f := CtCfu.fF (τ ^ 2) with hf
  have hΦpos : 0 < edgePhi L τ := by
    rw [hE]; positivity
  have hfpos : 0 < f := by
    have : 0 < τ ^ 3 * f := by rw [← hΦ]; exact hΦpos
    exact (pos_iff_pos_of_mul_pos this).1 (by positivity)
  set d := CtCfu.dF (τ ^ 2) with hd
  have hd0 : 0 < d := by unfold CtCfu.dF at hd; rw [hd]; positivity
  have hd3 : d ^ 3 = 3 / 2 * f := CtCfu.rpow_third_cube (by positivity)
  have hX32 : X ^ ((3 : ℝ) / 2) * 4 / 3 = τ ^ 3 * f := by rw [← hΦ, hE]; ring
  -- `(τ d)³ = 2 X^{3/2}`
  have h1 : (τ * d) ^ 3 = 2 * X ^ ((3 : ℝ) / 2) := by
    rw [mul_pow, hd3]; linarith
  have h2 : ((τ * d) ^ 2) ^ 3 = (2 ^ ((2 : ℝ) / 3) * X) ^ 3 := by
    have hX2 : (X ^ ((3 : ℝ) / 2)) ^ 2 = X ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num
    have h23 : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    calc ((τ * d) ^ 2) ^ 3 = ((τ * d) ^ 3) ^ 2 := by ring
      _ = 4 * X ^ 3 := by rw [h1, mul_pow, hX2]; ring
      _ = (2 ^ ((2 : ℝ) / 3) * X) ^ 3 := by rw [mul_pow ((2 : ℝ) ^ ((2 : ℝ) / 3)) X 3, h23]
  have h3 : (τ * d) ^ 2 = 2 ^ ((2 : ℝ) / 3) * X :=
    (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).1 h2
  unfold CtCfu.AF
  rw [← hd]
  have h4 : (τ * d) ^ 2 = τ ^ 2 * d ^ 2 := mul_pow _ _ _
  linarith

/-- info: 'FormalResearch.SignUncertainty.ct_NF_tau0_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_NF_tau0_sq

/-- info: 'FormalResearch.SignUncertainty.ct_AF_tau0_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_AF_tau0_sq

end FormalResearch.SignUncertainty
