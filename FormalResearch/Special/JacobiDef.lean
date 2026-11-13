module

public import Mathlib

/-!
# Jacobi polynomials: definition

`jacobi α β n` is the Jacobi polynomial `P_n^{(α,β)}` as a real polynomial, defined by the
explicit finite sum DLMF 18.5.7:

  `P_n^{(α,β)}(x) = ∑_{ℓ=0}^n (n+α+β+1)_ℓ (α+ℓ+1)_{n-ℓ} / (ℓ! (n-ℓ)!) · ((x-1)/2)^ℓ`.

The parameters `α β` are arbitrary reals: the explicit sum has no denominators depending on them,
so the definition is valid at the exceptional parameters where the three-term recurrence
degenerates. `(a)_k` is `(ascPochhammer ℝ k).eval a`.
-/

@[expose] public section

namespace FormalResearch.Special

open Polynomial

/-- The coefficient of `(x-1)^ℓ` in `P_n^{(α,β)}(x)` (DLMF 18.5.7, with the `2^{-ℓ}` included). -/
noncomputable def jacobiCoeff (α β : ℝ) (n ℓ : ℕ) : ℝ :=
  (ascPochhammer ℝ ℓ).eval ((n : ℝ) + α + β + 1) * (ascPochhammer ℝ (n - ℓ)).eval (α + ℓ + 1) /
    ((ℓ.factorial : ℝ) * ((n - ℓ).factorial : ℝ) * 2 ^ ℓ)

/-- The Jacobi polynomial `P_n^{(α,β)}` (DLMF 18.5.7). -/
noncomputable def jacobi (α β : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ ℓ ∈ Finset.range (n + 1), C (jacobiCoeff α β n ℓ) * (X - 1) ^ ℓ

lemma jacobi_eval (α β : ℝ) (n : ℕ) (x : ℝ) :
    (jacobi α β n).eval x = ∑ ℓ ∈ Finset.range (n + 1), jacobiCoeff α β n ℓ * (x - 1) ^ ℓ := by
  simp [jacobi, eval_finsetSum]

lemma jacobi_zero (α β : ℝ) : jacobi α β 0 = 1 := by
  simp [jacobi, jacobiCoeff]

end FormalResearch.Special
