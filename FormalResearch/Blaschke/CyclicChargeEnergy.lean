import Mathlib
import FormalResearch.Blaschke.CompositionBaseline

namespace FormalResearch.Blaschke

open scoped BigOperators

lemma sum_range_cast_rat (n : Nat) :
    (∑ j ∈ Finset.range n, (j : ℚ)) =
      (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma sum_range_sq_cast_rat (n : Nat) :
    (∑ j ∈ Finset.range n, (j : ℚ) ^ 2) =
      (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Sum of the squared numerators in the symmetric-cover charge ladder. -/
lemma cyclicCharge_numerator_sq_sum (d : Nat) :
    (∑ j ∈ Finset.range d,
      ((d : ℚ) - 1 - 2 * (j : ℚ)) ^ 2) =
      (d : ℚ) * ((d : ℚ) ^ 2 - 1) / 3 := by
  calc
    (∑ j ∈ Finset.range d,
      ((d : ℚ) - 1 - 2 * (j : ℚ)) ^ 2) =
      ∑ j ∈ Finset.range d,
        (((d : ℚ) - 1) ^ 2 -
          4 * ((d : ℚ) - 1) * (j : ℚ) +
          4 * (j : ℚ) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (d : ℚ) * ((d : ℚ) - 1) ^ 2 -
          4 * ((d : ℚ) - 1) *
            (∑ j ∈ Finset.range d, (j : ℚ)) +
          4 * (∑ j ∈ Finset.range d, (j : ℚ) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
            simp [nsmul_eq_mul]
    _ = (d : ℚ) * ((d : ℚ) ^ 2 - 1) / 3 := by
          rw [sum_range_cast_rat, sum_range_sq_cast_rat]
          ring

/-- For the symmetric cover `B=z^d`, the squared norm of the complete signed
charge ladder is exactly the sharp Gate-A baseline `(d²-1)/(3d)`.  This is the
finite spectral identity behind `Tr(Q_B²)=E(P_B)` in the cyclic model. -/
theorem cyclicCharge_energy {d : Nat} (hd : 0 < d) :
    (∑ j ∈ Finset.range d, (cyclicCharge d j) ^ 2) = gateABaseline d := by
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hterm : ∀ j : Nat,
      (cyclicCharge d j) ^ 2 =
        (((d : ℚ) - 1 - 2 * (j : ℚ)) ^ 2) / (d : ℚ) ^ 2 := by
    intro j
    simp [cyclicCharge]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, cyclicCharge_numerator_sq_sum]
  simp [gateABaseline]
  field_simp [hdq]
  ring

end FormalResearch.Blaschke
