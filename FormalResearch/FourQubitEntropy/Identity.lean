import FormalResearch.FourQubitEntropy.Generic
import FormalResearch.FourQubitEntropy.SparsePoly

/-!
# The sextic identity as a polynomial identity

`8F = 6 n W₁ + 3 Σᵢ ‖Vᵢ - 8Uᵢ‖² + 12 Σ_{i<j} ‖(Rᵢ^{(i)} - Rⱼ^{(j)}) z‖²`, stated as
`96 F = 72 n W₁ + Σᵢ nᵢ + 144 Σ_{i<j} ‖…‖²` with `nᵢ = 36 ‖Vᵢ - 8Uᵢ‖²`, as an identity of
polynomials in the 32 variables
`z_{abcd}`, `w_{abcd}`. The sparse-polynomial normal form is evaluated by `native_decide`
(compiled code, trusted through the axiom `sexticDefect_check._native.native_decide.ax_1_1`),
not by the kernel; everything downstream of this identity is kernel-checked.
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
