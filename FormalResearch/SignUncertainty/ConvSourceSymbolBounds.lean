module

public import Mathlib
public import FormalResearch.SignUncertainty.ConvSourceSymbol
public import FormalResearch.SignUncertainty.ConvSourceSymbolIBP
public import FormalResearch.SignUncertainty.ConvSourceWeightDeriv

/-!
# The uniform bounds for the Laplace transform of `w_h` (M6, Lemma `O.12(4)`, `ceo:conv.5`)

Assembly of `ConvSourceSymbol` (`lapW`, `convSD`, the `k`-free bounds), `ConvSourceSymbolIBP` (the
abstract integration-by-parts estimate) and `ConvSourceWeightDeriv` (`ceo:conv.4`, via the good
function calculus `convWdGood`).

* `convS_momentData`: for `k ≥ 1`, `F_h(y) = y^k w_h(y)` satisfies `ConvMomentData F_h K (k - 3/2) (k+1)`
  with `K` independent of `h > 0` (Leibniz rule from `convWd_mul`, class: proved).
* `convS_moment_bounds`: for `k ≥ 1`, `‖convSD w_h k z‖ ≤ C ‖z‖^{-k-1}` for every `Re z > 0` and
  `≤ C ‖z‖^{1/2-k}` for `‖z‖ ≤ 1`, with `C` independent of `h` (class: proved; all `k ≥ 1`).
* `convS_bounds`: the full statement `(ceo:conv.5)` for `1/2 < p < 1`: `‖lapW w_h z‖ ≤ 2`, the decay
  `‖z‖^{-k-1}` for `‖z‖ ≥ 1` and the bound `‖z‖^{1/2-k}` for `‖z‖ ≤ 1` for `k = 1, 2, 3`, and the Hölder
  estimate at `0` (class: proved, unconditional).

Not formalised here: the passage `δ ↓ 0` to the boundary `Re z = 0` (`ŵ_h(q) = L w_h(iq)` as a
derivative of continuous extensions), the term `γ ε/(1+iq)` of `ŵ_c` beyond `convS_lapW_exp`, and the
Leibniz combination with the seed symbol `W_{g_1}` (item (4) of `ceo:conv`).

The moments `y^k w_h` need the derivative bounds of the product, which the good-function calculus
`convWdGood` of `ConvSourceWeightDeriv` gives directly (`convS_momentData`), so the bounds do not
go through a separate hypothesis structure for `ceo:conv.4`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The `ConvMomentData` of `F_h(y) = y^k w_h(y)`, `k ≥ 1`, with `s = k - 3/2`, `m = k + 1` and a
constant independent of `h > 0`. -/
lemma convS_momentData {p : ℝ} (hp : 1 / 2 < p) (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h →
      ConvMomentData (fun y : ℝ => y ^ k * convWh p h y) K ((k : ℝ) - 3 / 2) (k + 1) := by
  obtain ⟨Cρ, hρ⟩ := convWd_rho p hp
  obtain ⟨Cη, hη⟩ := convWd_eta
  obtain ⟨Cp, hpw⟩ := convWd_pow (-(3 / 2 : ℝ))
  obtain ⟨Ck, hkk⟩ := convWd_pow (k : ℝ)
  set Cw := convWdMulSeq Ck (convWdMulSeq (convWdMulSeq Cη Cρ) Cp) with hCw
  refine ⟨∑ j ∈ Finset.range (k + 2), |Cw j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _),
    fun h hh => ?_⟩
  have hw := convWd_weight hh hη hρ hpw
  have hG := convWd_mul hkk hw
  have hG' : convWdGood (3 / 2 - (k : ℝ)) (fun y : ℝ => y ^ k * convWh p h y) Cw :=
    convWd_congr hG (fun t _ => by
      show t ^ (k : ℝ) * convWh p h t = t ^ k * convWh p h t
      rw [Real.rpow_natCast]) (by ring)
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  refine ⟨(contDiff_id.pow k).mul (convWh_contDiff hh), fun y hy => ?_,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), by linarith, ?_, ?_⟩
  · show y ^ k * convWh p h y = 0
    rw [convWh_eq_zero hy, mul_zero]
  · push_cast
    linarith
  · intro j hj y hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hb := hG'.2 j y hy0
    have hjm : j ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
    have hle : |Cw j| ≤ ∑ i ∈ Finset.range (k + 2), |Cw i| :=
      Finset.single_le_sum (f := fun i => |Cw i|) (fun _ _ => abs_nonneg _) hjm
    have hexp : -(3 / 2 - (k : ℝ)) - (j : ℝ) = (k : ℝ) - 3 / 2 - j := by ring
    rw [hexp] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hle)
      (Real.rpow_nonneg hy0.le _))

/-- The norm of the `k`-th moment transform is the norm of the Laplace integral of `y^k w`. -/
lemma convS_norm_convSD (w : ℝ → ℝ) (k : ℕ) (z : ℂ) :
    ‖convSD w k z‖
      = ‖∫ y in Ioi (0 : ℝ), ((y ^ k * w y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ)))‖ := by
  have hfun : (fun y : ℝ => (w y : ℂ) * (-(y : ℂ)) ^ k * Complex.exp (-(z * (y : ℂ))))
      = fun y : ℝ => (-1 : ℂ) ^ k * (((y ^ k * w y : ℝ) : ℂ) * Complex.exp (-(z * (y : ℂ)))) := by
    funext y
    push_cast
    rw [neg_pow]
    ring
  unfold convSD
  rw [hfun, integral_const_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-- For each `k ≥ 1`, `‖convSD w_h k z‖ ≤ C ‖z‖^{-k-1}` for all `Re z > 0` and
`≤ C ‖z‖^{1/2-k}` for `‖z‖ ≤ 1`, with `C` independent of `h > 0` (`ceo:conv.5`). -/
theorem convS_moment_bounds {p : ℝ} (hp : 1 / 2 < p) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ z : ℂ, 0 < z.re →
      ‖convSD (convWh p h) k z‖ ≤ C * ‖z‖ ^ (-(k : ℝ) - 1) ∧
      (‖z‖ ≤ 1 → ‖convSD (convWh p h) k z‖ ≤ C * ‖z‖ ^ (1 / 2 - (k : ℝ))) := by
  obtain ⟨K, hK, hd⟩ := convS_momentData hp k hk
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  have hms : ((k + 1 : ℕ) : ℝ) - ((k : ℝ) - 3 / 2) - 1 = 3 / 2 := by push_cast; ring
  have hs1 : ((k : ℝ) - 3 / 2) + 1 = (k : ℝ) - 1 / 2 := by ring
  set C1 : ℝ := K / (3 / 2) with hC1
  set C2 : ℝ := K * (1 / ((k : ℝ) - 1 / 2) + ((k + 1 : ℕ) : ℝ) + 1 / (3 / 2)) with hC2
  have hC1' : 0 ≤ C1 := div_nonneg hK (by norm_num)
  have hC2' : 0 ≤ C2 := by
    refine mul_nonneg hK ?_
    have : (0 : ℝ) < 1 / ((k : ℝ) - 1 / 2) := by
      apply one_div_pos.mpr; linarith
    have h2 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  refine ⟨C1 + C2, add_nonneg hC1' hC2', fun h hh z hz => ?_⟩
  have hdh := hd h hh
  have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [convS_norm_convSD]
  refine ⟨?_, fun hz1 => ?_⟩
  · have h1 := convS_moment_decay hdh hz
    rw [hms, ← hC1] at h1
    have he : (-(((k + 1 : ℕ) : ℝ))) = -(k : ℝ) - 1 := by push_cast; ring
    rw [he] at h1
    refine h1.trans ?_
    have : 0 ≤ C2 * ‖z‖ ^ (-(k : ℝ) - 1) := mul_nonneg hC2' (Real.rpow_nonneg hzn.le _)
    nlinarith
  · have h1 := convS_moment_small hdh hz hz1
    rw [hms, hs1, ← hC2] at h1
    have he : -((k : ℝ) - 1 / 2) = 1 / 2 - (k : ℝ) := by ring
    rw [he] at h1
    refine h1.trans ?_
    have : 0 ≤ C1 * ‖z‖ ^ (1 / 2 - (k : ℝ)) := mul_nonneg hC1' (Real.rpow_nonneg hzn.le _)
    nlinarith

/-- `(ceo:conv.5)` for the weight `w_h`, `1/2 < p < 1`, in the variable `z` with `Re z > 0`
(`z = δ + iq` of the TeX, `‖convSD w_h k z‖ = ‖∂_q^k L w_h(δ + iq)‖`): the constant `C` depends on `p`
only, not on `h > 0`, `z`, `δ`. It states `‖L w_h‖ ≤ 2` (also for `Re z ≥ 0`), the decay `‖z‖^{-k-1}` for
`‖z‖ ≥ 1` and the bound `‖z‖^{1/2-k}` for `‖z‖ ≤ 1` for `k = 1, 2, 3`, and the `1/2`-Hölder estimate
`‖L w_h(z) - L w_h(0)‖ ≤ 6 ‖z‖^{1/2}` for `‖z‖ ≤ 1` (with `L w_h(0) = ∫ w_h`). Not covered: the
boundary values on `Re z = 0` (the `δ ↓ 0` limit) and the term `γ ε/(1+iq)` of `ŵ_c`. -/
theorem convS_bounds {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ z : ℂ, 0 < z.re →
      ‖lapW (convWh p h) z‖ ≤ 2 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 → 1 ≤ ‖z‖ →
        ‖convSD (convWh p h) k z‖ ≤ C * ‖z‖ ^ (-(k : ℝ) - 1)) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 → ‖z‖ ≤ 1 →
        ‖convSD (convWh p h) k z‖ ≤ C * ‖z‖ ^ (1 / 2 - (k : ℝ))) ∧
      (‖z‖ ≤ 1 → ‖lapW (convWh p h) z - ∫ y in Ioi (0 : ℝ), convWh p h y‖
        ≤ 6 * ‖z‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨C1, hC1, h1⟩ := convS_moment_bounds hp 1 le_rfl
  obtain ⟨C2, hC2, h2⟩ := convS_moment_bounds hp 2 (by norm_num)
  obtain ⟨C3, hC3, h3⟩ := convS_moment_bounds hp 3 (by norm_num)
  refine ⟨C1 + C2 + C3, by positivity, fun h hh z hz => ⟨convS_lapW_norm_le hp hp1 hh hz.le,
    fun k hk1 hk3 hz1 => ?_, fun k hk1 hk3 hz1 => ?_, fun hz1 => convS_lapW_sub_le hp hp1 hh hz hz1⟩⟩
  · have hzn : 0 ≤ ‖z‖ ^ (-(k : ℝ) - 1) := Real.rpow_nonneg (norm_nonneg _) _
    interval_cases k
    · exact ((h1 h hh z hz).1).trans (by nlinarith)
    · exact ((h2 h hh z hz).1).trans (by nlinarith)
    · exact ((h3 h hh z hz).1).trans (by nlinarith)
  · have hzn : 0 ≤ ‖z‖ ^ (1 / 2 - (k : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    interval_cases k
    · exact ((h1 h hh z hz).2 hz1).trans (by nlinarith)
    · exact ((h2 h hh z hz).2 hz1).trans (by nlinarith)
    · exact ((h3 h hh z hz).2 hz1).trans (by nlinarith)

/-- info: 'FormalResearch.SignUncertainty.convS_momentData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_momentData

/-- info: 'FormalResearch.SignUncertainty.convS_norm_convSD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_norm_convSD

/-- info: 'FormalResearch.SignUncertainty.convS_moment_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_moment_bounds

/-- info: 'FormalResearch.SignUncertainty.convS_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convS_bounds

end FormalResearch.SignUncertainty
