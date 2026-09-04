import Mathlib

namespace FormalResearch.Blaschke

/-- Sharp Gate-A baseline for degree `d`, as used in the finite-Blaschke
projector-energy formulation. -/
def gateABaseline (d : Nat) : ℚ := ((d : ℚ)^2 - 1) / (3 * d)

/-- The exact telescoping identity behind arbitrary composition stability:
if degrees `k,m` each meet their Gate-A baseline, the weighted composition
lower bound lands exactly on the degree `k*m` baseline. -/
theorem composition_baseline_telescope {k m : Nat} (hk : 0 < k) (hm : 0 < m) :
    (k : ℚ) * gateABaseline m + (1 / (m : ℚ)) * gateABaseline k =
      gateABaseline (k * m) := by
  simp [gateABaseline]
  field_simp [Nat.ne_of_gt hk, Nat.ne_of_gt hm]
  ring

/-- Signed charge-ladder eigenvalue for the symmetric cover `B=z^d`. -/
def cyclicCharge (d j : Nat) : ℚ :=
  ((d : ℚ) - 1 - 2 * j) / d

/-- The symmetric-cover charge ladder is exactly antisymmetric under reversal
of the basis index. -/
theorem cyclicCharge_reflection {d j : Nat} (hd : 0 < d) (hj : j < d) :
    cyclicCharge d (d - 1 - j) = - cyclicCharge d j := by
  simp [cyclicCharge]
  have hsub : ((d - 1 - j : Nat) : ℚ) = (d : ℚ) - 1 - j := by
    rw [Nat.cast_sub (by omega : j ≤ d - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  rw [hsub]
  field_simp [Nat.ne_of_gt hd]
  ring

/-- In odd dimension the central ladder value is zero. -/
theorem cyclicCharge_middle_zero (r : Nat) :
    cyclicCharge (2*r + 1) r = 0 := by
  simp [cyclicCharge]

end FormalResearch.Blaschke
