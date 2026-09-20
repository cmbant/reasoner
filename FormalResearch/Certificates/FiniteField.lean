import Mathlib

namespace FormalResearch.Certificates

theorem int_ne_zero_of_zmod_ne_zero (p : Nat) (z : Int)
    (h : (z : ZMod p) ≠ 0) : z ≠ 0 := by
  intro hz
  subst z
  exact h (by simp)

end FormalResearch.Certificates
