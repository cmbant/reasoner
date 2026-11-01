/-!
# GO certificate: data types

`SP` is a sparse polynomial (list of `(packed monomial key, coefficient)`, see `Poly.lean`); `GBlock` is one Gram
block of the certificate (see `Block.lean`).  This module is kept minimal so that the generated data modules,
which only import it, are not rebuilt when the checker changes.
-/

namespace FormalResearch.FourQubitEntropy.GOProbe

abbrev SP := List (Nat × Int)

/-- One Gram block. `basis i` lists the atoms `(component, packed monomial, coefficient)` of the polynomial
vector entry `p_i`; `factor` is the compact factor `A`, `resid` the columns `Δ` (column `j` has `j+1` entries,
the upper triangle) and `corr` the sparse columns `C`. -/
structure GBlock where
  cid : Nat
  basis : List (List (Nat × Nat × Int))
  factor : List (List Int)
  resid : List (List Int)
  corr : List (List (Nat × Int))

end FormalResearch.FourQubitEntropy.GOProbe
