module

public import FormalResearch.Special.LatticeCount

/-!
# A weighted sum over unit intervals

Elementary estimates used to turn per-unit-interval bounds into a bound with no factor `X`
(the "no factor `X`" remark in the proof of `lem:latticesum` (i)).

* `sum_exp_abs_le` : `∑_{k<2N} e^{-κ|k-N|} ≤ 2/(1-e^{-κ})`;
* `integral_exp_neg_abs_le` : `∫_{-X}^{X} e^{-κ|s|} ≤ 2/κ`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma geom_partial_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, q ^ i ≤ 1 / (1 - q) := by
  rw [geom_sum_eq hq1.ne n]
  have h1 : 0 < 1 - q := by linarith
  rw [show (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) by
    rw [← neg_sub q 1, ← neg_sub (q ^ n) 1, neg_div_neg_eq]]
  apply div_le_div_of_nonneg_right _ h1.le
  have : 0 ≤ q ^ n := by positivity
  linarith

lemma sum_exp_abs_le {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N), Real.exp (-κ * |(-(N : ℝ) + k)|) ≤ 2 / (1 - Real.exp (-κ)) := by
  set q : ℝ := Real.exp (-κ) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hpow : ∀ n : ℕ, Real.exp (-κ * (n : ℝ)) = q ^ n := fun n => by
    rw [hq, ← Real.exp_nat_mul]; ring_nf
  have h1 : 0 < 1 - q := by linarith
  rw [two_mul, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range N, Real.exp (-κ * |(-(N : ℝ) + ((N + x : ℕ) : ℝ))|) =
      ∑ x ∈ Finset.range N, q ^ x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have : (-(N : ℝ) + ((N + x : ℕ) : ℝ)) = (x : ℝ) := by push_cast; ring
    rw [this, abs_of_nonneg (Nat.cast_nonneg x), hpow]
  have e2 : ∑ k ∈ Finset.range N, Real.exp (-κ * |(-(N : ℝ) + k)|) =
      ∑ j ∈ Finset.range N, q ^ (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => q ^ (j + 1)) N]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkN : k < N := Finset.mem_range.mp hk
    have : (-(N : ℝ) + k) = -((N - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hkN.le]; ring
    rw [this, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), hpow]
    congr 1; omega
  rw [e1, e2]
  have hs : ∑ j ∈ Finset.range N, q ^ (j + 1) = q * ∑ j ∈ Finset.range N, q ^ j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hs]
  have := geom_partial_le hq0 hq1 N
  have h3 : q * ∑ j ∈ Finset.range N, q ^ j ≤ q * (1 / (1 - q)) := mul_le_mul_of_nonneg_left this hq0.le
  calc q * ∑ j ∈ Finset.range N, q ^ j + ∑ x ∈ Finset.range N, q ^ x
      ≤ q * (1 / (1 - q)) + 1 / (1 - q) := add_le_add h3 this
    _ ≤ 2 / (1 - q) := by
        rw [show 2 / (1 - q) = 1 / (1 - q) + 1 / (1 - q) by ring]
        have : q * (1 / (1 - q)) ≤ 1 / (1 - q) := by
          have : 0 ≤ 1 / (1 - q) := by positivity
          nlinarith
        linarith

end FormalResearch.Special.Lattice
