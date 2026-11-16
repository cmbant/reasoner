module

public import Mathlib

/-!
# Determinant form of the replica trace (Weyl W1, `prop:finite`, `eq:replica`: linear-algebra half)

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `prop:finite`, last display (`eq:replica`)
`Z_{n,L}(θ) = Tr(ρ_A^n e^{iθ N_A}) = det[(1-C)^n + e^{iθ} C^n]`, and the product form
`∏_j [(1-λ_j)^n + e^{iθ} λ_j^n]` in the last line of its proof.

## Statement formalised

For a Hermitian `C` (complex matrix, eigenvalues `c_k`), every `n` and every `z : ℂ`:
`det((1-C)^n + z C^n) = ∏_k ((1-c_k)^n + z c_k^n)` (`replica_det_eq_prod`), and with `z = e^{iθ}`
(`replica_det_eq_prod_exp`); more generally `det f(C) = ∏_k f(c_k)` for `f ∈ ℂ[X]`
(`det_aeval_hermitian`).  The eigenvalues `0` and `1` give the factors `1` and `z`
(`replica_factor_zero`, `replica_factor_one`).

## What is NOT formalised

The *Fock-space side*: that for a Gaussian (Slater) state `ρ_A` with correlation matrix `C` one has
`Tr(ρ_A^n e^{iθ N_A}) = ∏_k((1-c_k)^n + e^{iθ}c_k^n)` is not formalised (no Fock space, Slater
determinants or partial traces here).  Only the determinant factorisation of a function of a
Hermitian matrix is, so `eq:replica` is *not* proved in Lean: `Z_{n,L}(θ)` is not defined here, and
the displayed identity `Z = det[…]` itself is the unformalised physical step.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by a unitary preserves the determinant. -/
theorem det_unitary_conj (U : unitaryGroup ι ℂ) (M : Matrix ι ι ℂ) :
    det ((U : Matrix ι ι ℂ) * M * star (U : Matrix ι ι ℂ)) = det M := by
  rw [det_mul, det_mul, mul_comm (det (U : Matrix ι ι ℂ)), mul_assoc, ← det_mul]
  have : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  rw [this, det_one, mul_one]

/-- `f(diag d) = diag(f(d))`. -/
theorem aeval_diagonal (d : ι → ℂ) (f : ℂ[X]) :
    aeval (diagonal d) f = diagonal (fun k => f.eval (d k)) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq, diagonal_add]
      congr 1
      funext k
      simp
  | monomial n a =>
      rw [aeval_monomial, Matrix.algebraMap_eq_diagonal, diagonal_pow, diagonal_mul_diagonal]
      congr 1
      funext k
      simp

/-- `det f(C) = ∏ f(c_k)` for a Hermitian complex matrix `C` with eigenvalues `c_k` and `f ∈ ℂ[X]`. -/
theorem det_aeval_hermitian {C : Matrix ι ι ℂ} (hC : C.IsHermitian) (f : ℂ[X]) :
    det (aeval C f) = ∏ k, f.eval (hC.eigenvalues k : ℂ) := by
  have hspec := hC.spectral_theorem
  set D : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hC.eigenvalues) with hD
  set φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hC.eigenvectorUnitary with hφ
  have h1 : aeval C f = φ.toAlgEquiv.toAlgHom (aeval D f) := by
    have hC' : C = φ.toAlgEquiv.toAlgHom D := hspec
    rw [← Polynomial.aeval_algHom_apply, ← hC']
  have h2 : aeval D f = diagonal (fun k => f.eval (hC.eigenvalues k : ℂ)) := by
    rw [hD, aeval_diagonal]
    rfl
  have h3 : ∀ M, φ.toAlgEquiv.toAlgHom M = (hC.eigenvectorUnitary : Matrix ι ι ℂ) * M *
      star (hC.eigenvectorUnitary : Matrix ι ι ℂ) := by
    intro M
    simp [hφ, Unitary.conjStarAlgAut_apply]
  rw [h1, h3, det_unitary_conj, h2, det_diagonal]

/-- **Determinant side of `eq:replica`** (paper `prop:finite`): for a Hermitian `C`,
`det[(1-C)^n + z C^n] = ∏_k ((1-c_k)^n + z c_k^n)`. -/
theorem replica_det_eq_prod {C : Matrix ι ι ℂ} (hC : C.IsHermitian) (m : ℕ) (z : ℂ) :
    det ((1 - C) ^ m + z • C ^ m) =
      ∏ k, ((1 - (hC.eigenvalues k : ℂ)) ^ m + z * (hC.eigenvalues k : ℂ) ^ m) := by
  have h := det_aeval_hermitian hC ((1 - X) ^ m + Polynomial.C z * X ^ m)
  have e : aeval C ((1 - X) ^ m + Polynomial.C z * X ^ m) = (1 - C) ^ m + z • C ^ m := by
    simp [Algebra.smul_def]
  rw [e] at h
  simpa using h

/-- The same with `z = e^{iθ}`: `det[(1-C)^n + e^{iθ} C^n] = ∏_k ((1-c_k)^n + e^{iθ} c_k^n)`. -/
theorem replica_det_eq_prod_exp {C : Matrix ι ι ℂ} (hC : C.IsHermitian) (m : ℕ) (θ : ℝ) :
    det ((1 - C) ^ m + Complex.exp (θ * Complex.I) • C ^ m) =
      ∏ k, ((1 - (hC.eigenvalues k : ℂ)) ^ m +
        Complex.exp (θ * Complex.I) * (hC.eigenvalues k : ℂ) ^ m) :=
  replica_det_eq_prod hC m _

/-- An eigenvalue `0` contributes the factor `1` (for `n ≥ 1`). -/
theorem replica_factor_zero (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    (1 - (0 : ℂ)) ^ m + z * (0 : ℂ) ^ m = 1 := by
  simp [zero_pow (by omega : m ≠ 0)]

/-- An eigenvalue `1` contributes the factor `z = e^{iθ}` (for `n ≥ 1`). -/
theorem replica_factor_one (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    (1 - (1 : ℂ)) ^ m + z * (1 : ℂ) ^ m = z := by
  simp [zero_pow (by omega : m ≠ 0)]

/-- info: 'FormalResearch.FreeFermion.replica_det_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replica_det_eq_prod

end FormalResearch.FreeFermion
