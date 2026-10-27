import FormalResearch.FrameFree.ScalarChirality
import FormalResearch.QIA.MultiplicityProfileDimensions

/-!
# The odd-invariant dimension of Paper P is the QI-A multiplicity odd dimension

`ScalarChirality.oddDim n` is the sum over total spins `j'` of `C(mult n j', 2)`, where `mult n j'` is the
multiplicity of spin `j'` in `(ℂ²)^{⊗n}`.  This is `QIA.multiplicityOddDimension` applied to the
multiplicity profile, so `prop:oddwords` (iii) and the QI-A memory-rate statements count the same space.
-/

namespace FormalResearch.FrameFree

open FormalResearch.FrameFree.ScalarChirality in
theorem oddDim_eq_multiplicityOddDimension (n : ℕ) :
    oddDim n = FormalResearch.QIA.multiplicityOddDimension
      (fun j : Fin (n / 2 + 1) => mult n j) := by
  unfold oddDim FormalResearch.QIA.multiplicityOddDimension
  rw [Finset.sum_range (fun j' => Nat.choose (mult n j') 2)]

end FormalResearch.FrameFree
