module

public import Mathlib

/-!
# Kronecker products over a finite family (QV block calculus, T6 ingredient)

`kronPi X` is the Kronecker product `⊗_q X q` of a finite family of matrices with (dependently
typed) index types, with entries `∏ q, X q (a q) (b q)`.  It is multiplicative, unital, additive,
and its trace is the product of traces.
-/

@[expose] public section


open scoped Matrix BigOperators

set_option linter.unusedSectionVars false

namespace FormalResearch.FourQubitEntropy.QVBlock

variable {𝕜 : Type*} [CommRing 𝕜]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The Kronecker product `⊗_q X q` of a finite family of matrices. -/
def kronPi {m n : Q → Type*} (X : ∀ q, Matrix (m q) (n q) 𝕜) :
    Matrix (∀ q, m q) (∀ q, n q) 𝕜 :=
  Matrix.of fun a b => ∏ q, X q (a q) (b q)

@[simp] theorem kronPi_apply {m n : Q → Type*} (X : ∀ q, Matrix (m q) (n q) 𝕜) (a b) :
    kronPi X a b = ∏ q, X q (a q) (b q) := rfl

theorem kronPi_mul {m n o : Q → Type*} [∀ q, Fintype (n q)]
    (X : ∀ q, Matrix (m q) (n q) 𝕜) (Y : ∀ q, Matrix (n q) (o q) 𝕜) :
    kronPi X * kronPi Y = kronPi (fun q => X q * Y q) := by
  ext a c
  simp only [Matrix.mul_apply, kronPi_apply]
  rw [Fintype.prod_sum (fun q (b : n q) => X q (a q) b * Y q b (c q))]
  simp [Finset.prod_mul_distrib]

theorem kronPi_one {m : Q → Type*} [∀ q, DecidableEq (m q)] :
    kronPi (fun q => (1 : Matrix (m q) (m q) 𝕜)) = 1 := by
  ext a b
  simp only [kronPi_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])]
    simp [h]

theorem trace_kronPi {m : Q → Type*} [∀ q, Fintype (m q)] (X : ∀ q, Matrix (m q) (m q) 𝕜) :
    (kronPi X).trace = ∏ q, (X q).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, kronPi_apply]
  rw [Fintype.prod_sum (fun q (b : m q) => X q b b)]

end FormalResearch.FourQubitEntropy.QVBlock
