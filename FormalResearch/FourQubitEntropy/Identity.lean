import FormalResearch.FourQubitEntropy.Generic
import FormalResearch.FourQubitEntropy.SparsePoly

/-!
# The sextic identity as a kernel-checked polynomial identity

`1152 F = 540 n W₁ + 3 Σᵢ 36 ‖Rᵢ‖²` as an identity of polynomials in the 32 variables
`z_{abcd}`, `w_{abcd}`.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- Variable index of `z_{abcd}`; the variable of `w_{abcd}` is `16 +` this. -/
def varIdx (a b c d : Fin 2) : Fin 32 :=
  Fin.ofNat 32 (8 * a.val + 4 * b.val + 2 * c.val + d.val)

/-- The variables `z_{abcd}` and `w_{abcd}` as sparse polynomials. -/
def zSP : State SP := fun a b c d => varSP (varIdx a b c d)
def wSP : State SP := fun a b c d => varSP (Fin.ofNat 32 (16 + (varIdx a b c d).val))

theorem sexticDefect_check : sexticDefect zSP wSP = [] := by
  native_decide

end FormalResearch.FourQubitEntropy
