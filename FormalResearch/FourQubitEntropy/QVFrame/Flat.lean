import FormalResearch.FourQubitEntropy.QVFrame.Basic

/-!
# Absorbing coefficients into the first qubit factor

The block calculus of `QVBlock` consumes `K = ∑_k ⊗_q X k q` (no scalar coefficients); `smul_kronPi` and
`sum_smul_kronPi` rewrite `∑_i c_i • ⊗_q X_{i,q}` in that form.
-/

open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy.QVBlock

theorem smul_kronPi {R : Type*} [CommRing R] {m n : Fin 4 → Type*} (c : R) (X : ∀ q, Matrix (m q) (n q) R) :
    c • kronPi X = kronPi (fun q => if q = 0 then c • X q else X q) := by
  ext a b
  simp only [Matrix.smul_apply, kronPi_apply, smul_eq_mul, Fin.prod_univ_four]
  simp
  ring

theorem sum_smul_kronPi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (c : ι → R)
    (X : ι → Fin 4 → Matrix (Wd n) (Wd n) R) :
    ∑ i, c i • kronPi (X i) = ∑ i, kronPi (fun q => if q = 0 then c i • X i q else X i q) :=
  Finset.sum_congr rfl fun i _ => smul_kronPi (c i) (X i)

end FormalResearch.FourQubitEntropy.QVFrame
