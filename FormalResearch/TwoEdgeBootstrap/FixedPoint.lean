module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Two-Edge Bootstrap Fixed-Point Closures

Source: `CFT/common/two_edge_bootstrap.tex` (Theorem `TE.2` algebraic closures).

* `log_bootstrap_bound`: `L ≤ Cstar * (1 + Real.log L) → L ≤ 2 * Cstar * Real.log (2 * Cstar)`.
* `poly_absorption_bound_rpow`, `poly_absorption_bound`: `K ≤ A * (1 + L♯ * K ^ (-r))` absorption bounds.
-/

@[expose] public section

namespace FormalResearch.TwoEdgeBootstrap

section FixedPointClosures

/-- Explicit logarithmic fixed-point bound `L♯(C_*) = 2 C_* log(2 C_*)`. -/
noncomputable def tebLogSharp (Cstar : ℝ) : ℝ :=
  2 * Cstar * Real.log (2 * Cstar)

lemma one_le_tebLogSharp {Cstar : ℝ} (hC : 1 ≤ Cstar) : 1 ≤ tebLogSharp Cstar := by
  unfold tebLogSharp
  have h2 : (2 : ℝ) ≤ 2 * Cstar := by linarith
  have hlog : 1 / 2 ≤ Real.log (2 * Cstar) := by
    have h1 : Real.log 2 ≤ Real.log (2 * Cstar) := Real.log_le_log (by norm_num) h2
    have h2' : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    linarith
  nlinarith

/-- Theorem TE.2(2) logarithmic bootstrap closure:
if `1 ≤ Cstar`, `1 ≤ L`, and `L ≤ Cstar * (1 + log L)`, then `L ≤ tebLogSharp Cstar`. -/
theorem log_bootstrap_bound {Cstar L : ℝ} (hC : 1 ≤ Cstar) (hL : 1 ≤ L)
    (hle : L ≤ Cstar * (1 + Real.log L)) :
    L ≤ tebLogSharp Cstar := by
  unfold tebLogSharp
  have hC_pos : 0 < Cstar := by linarith
  have hL_pos : 0 < L := by linarith
  have h2C_pos : 0 < 2 * Cstar := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hL_pos h2C_pos)
  rw [Real.log_div hL_pos.ne' h2C_pos.ne'] at hlog
  have hlogL : Real.log L ≤ Real.log (2 * Cstar) + L / (2 * Cstar) - 1 := by linarith
  have h1 : L ≤ Cstar * (1 + (Real.log (2 * Cstar) + L / (2 * Cstar) - 1)) :=
    hle.trans (mul_le_mul_of_nonneg_left (by linarith) hC_pos.le)
  have h2 : Cstar * (1 + (Real.log (2 * Cstar) + L / (2 * Cstar) - 1)) =
      Cstar * Real.log (2 * Cstar) + L / 2 := by
    field_simp [hC_pos.ne']
    ring
  linarith

/-- General real-exponent polynomial absorption bound:
if `A > 0`, `L♯ ≥ 0`, `r ≥ 0`, `K > 0`, and `K ≤ A * (1 + L♯ * K ^ (-r))`, then
`K ≤ max (2 * A) ((2 * A * L♯) ^ (1 / (r + 1)))`. -/
theorem poly_absorption_bound_rpow {A Lsharp K r : ℝ} (hA : 0 < A) (hL : 0 ≤ Lsharp)
    (hr : 0 ≤ r) (hK : 0 < K) (hle : K ≤ A * (1 + Lsharp * K ^ (-r))) :
    K ≤ max (2 * A) ((2 * A * Lsharp) ^ (1 / (r + 1))) := by
  have _ := hL
  have hKr_pos : 0 < K ^ r := Real.rpow_pos_of_pos hK r
  have hmul : K ^ (r + 1) ≤ A * (K ^ r + Lsharp) := by
    calc K ^ (r + 1) = K * K ^ r := by rw [Real.rpow_add hK, Real.rpow_one, mul_comm]
      _ ≤ A * (1 + Lsharp * K ^ (-r)) * K ^ r := mul_le_mul_of_nonneg_right hle hKr_pos.le
      _ = A * (K ^ r + Lsharp * (K ^ (-r) * K ^ r)) := by ring
      _ = A * (K ^ r + Lsharp) := by
          rw [← Real.rpow_add hK, neg_add_cancel, Real.rpow_zero, mul_one]
  rcases le_or_gt Lsharp (K ^ r) with hbr | hbr
  · have h2 : K * K ^ r ≤ (2 * A) * K ^ r := by
      have : K ^ (r + 1) = K * K ^ r := by rw [Real.rpow_add hK, Real.rpow_one, mul_comm]
      linarith [mul_le_mul_of_nonneg_left (add_le_add_left hbr (K ^ r)) hA.le]
    exact le_trans (le_of_mul_le_mul_right h2 hKr_pos) (le_max_left _ _)
  · have h2 : K ^ (r + 1) ≤ 2 * A * Lsharp := by
      have : A * (K ^ r + Lsharp) ≤ A * (Lsharp + Lsharp) := by nlinarith
      linarith
    have hr1_pos : 0 < r + 1 := by linarith
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hK.le _) h2 (by positivity : 0 ≤ 1 / (r + 1))
    rw [← Real.rpow_mul hK.le, mul_one_div_cancel hr1_pos.ne', Real.rpow_one] at hpow
    exact hpow.trans (le_max_right _ _)

/-- Theorem TE.2(3) polynomial absorption bound:
if `A > 0`, `L♯ ≥ 0`, `K > 0`, and `K ≤ A * (1 + L♯ * K ^ (-(k₀ + 1/2)))`, then
`K ≤ max 1 (max (2 * A) ((2 * A * L♯) ^ (1 / (k₀ + 3/2))))`. -/
theorem poly_absorption_bound {A Lsharp K : ℝ} (k₀ : ℕ) (hA : 0 < A) (hL : 0 ≤ Lsharp)
    (hK : 0 < K) (hle : K ≤ A * (1 + Lsharp * K ^ (-((k₀ : ℝ) + 1 / 2)))) :
    K ≤ max 1 (max (2 * A) ((2 * A * Lsharp) ^ (1 / ((k₀ : ℝ) + 3 / 2)))) := by
  have h := poly_absorption_bound_rpow (r := (k₀ : ℝ) + 1 / 2) hA hL (by positivity) hK hle
  have heq : (k₀ : ℝ) + 1 / 2 + 1 = (k₀ : ℝ) + 3 / 2 := by ring
  rw [heq] at h
  exact h.trans (le_max_right _ _)

end FixedPointClosures

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.TwoEdgeBootstrap.log_bootstrap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.log_bootstrap_bound

/-- info: 'FormalResearch.TwoEdgeBootstrap.poly_absorption_bound_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.poly_absorption_bound_rpow

/-- info: 'FormalResearch.TwoEdgeBootstrap.poly_absorption_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.poly_absorption_bound


end FormalResearch.TwoEdgeBootstrap
