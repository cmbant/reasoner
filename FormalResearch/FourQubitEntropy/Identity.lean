import FormalResearch.FourQubitEntropy.IdentityVars
import FormalResearch.FourQubitEntropy.IdentityCertF
import FormalResearch.FourQubitEntropy.IdentityCertNW
import FormalResearch.FourQubitEntropy.IdentityCertPair
import FormalResearch.FourQubitEntropy.IdentityCertRes0
import FormalResearch.FourQubitEntropy.IdentityCertRes1
import FormalResearch.FourQubitEntropy.IdentityCertRes2
import FormalResearch.FourQubitEntropy.IdentityCertRes3

/-!
# The sextic identity as a polynomial identity

`8F = 6 n W₁ + 3 Σᵢ ‖Vᵢ - 8Uᵢ‖² + 12 Σ_{i<j} ‖(Rᵢ^{(i)} - Rⱼ^{(j)}) z‖²`, stated as
`96 F = 72 n W₁ + Σᵢ nᵢ + 144 Σ_{i<j} ‖…‖²` with `nᵢ = 36 ‖Vᵢ - 8Uᵢ‖²`, as an identity of
polynomials in the 32 variables `z_{abcd}`, `w_{abcd}`.

**Trust: kernel only.** Every step is checked by the Lean kernel (`decide +kernel`); there is no
`native_decide`, and `#print axioms sexticDefect_check` lists only `propext`, `Classical.choice` and
`Quot.sound`. The sparse-polynomial normal form (`SparsePoly.lean`) is evaluated by the kernel in
pieces. The seven pieces `F`, `n W₁`, `pairSum` and the four residual norms `resNorm0` of
`sexticDefect zSP wSP` each have an expanded normal form, written to `IdentityCert*.lean` by
`gen_sextic_certificate.py`. The literals are untrusted data: the kernel checks `piece = literal` in
one declaration per piece, and then that `96 F - 72 n W₁ - Σ nᵢ - 144 pairSum` computed from the
literals is the empty polynomial.

**Machine requirements.** Peak kernel memory grows with the number of reduction steps and is not
freed within a declaration (a single `decide +kernel` of the whole identity needs more than 12 GB), so
the identity is split into pieces. Building the group `IdentityCert*.lean` + `Identity.lean` takes about
5 minutes on one core and a peak resident size of about 9 GB, of which about 6.4 GB is the memory-mapped
`.olean` files of `Mathlib` and the earlier modules, shared and evictable. The `IdentityCert*.lean` files
import one another in a chain, only so that `lake` builds them one at a time: do not remove the chain, or
`lake build` runs them in parallel, each with its own kernel memory. A machine with 16 GB of RAM is
comfortable; see `THEOREM_MAP.md` for the per-file measurements.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

theorem sexticDefect_check : sexticDefect zSP wSP = [] := by
  unfold sexticDefect defectG
  rw [sexticCertF_eq, sexticCertNW_eq, sexticCertPair_eq, sexticCertRes0_eq, sexticCertRes1_eq,
    sexticCertRes2_eq, sexticCertRes3_eq]
  decide +kernel

end FormalResearch.FourQubitEntropy
