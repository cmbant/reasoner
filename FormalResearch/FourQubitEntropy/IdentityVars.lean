import FormalResearch.FourQubitEntropy.Generic
import FormalResearch.FourQubitEntropy.SparsePoly

/-!
# The 32 variables of the sextic identity

`z_{abcd}` and `w_{abcd}` as sparse polynomials. Split from `Identity.lean` so that the
normal-form files `IdentityCert*.lean` can state their checks about `zSP` and `wSP` and be built in
parallel.
-/

namespace FormalResearch.FourQubitEntropy

/-- Variable index of `z_{abcd}`; the variable of `w_{abcd}` is `16 +` this. -/
def varIdx (a b c d : Fin 2) : Fin 32 :=
  Fin.ofNat 32 (8 * a.val + 4 * b.val + 2 * c.val + d.val)

/-- The variables `z_{abcd}` and `w_{abcd}` as sparse polynomials. -/
def zSP : State SP := fun a b c d => varSP (varIdx a b c d)
def wSP : State SP := fun a b c d => varSP (Fin.ofNat 32 (16 + (varIdx a b c d).val))

end FormalResearch.FourQubitEntropy
