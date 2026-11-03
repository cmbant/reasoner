module

public import ThreeCopyQutritWerner.OverlapAttain

@[expose] public section


/-!
# The PPT region `α ≤ 1/3`

At `d = 3` and `α ≤ 1/3` the Werner state has positive semidefinite partial transpose
(`partialTranspose_werner_three_posSemidef`), so `(ρ^{⊗3})^Γ = (ρ^Γ)^{⊗3}` is positive
semidefinite (`partialTranspose_tripleCopy_werner_three_posSemidef`, in `Identities`, from
`tripleCopy_posSemidef` here) and no vector of any Schmidt rank detects three copies; this module
states the rank-two consequences. Hence three-copy nondistillability and the overlap bound hold
unconditionally for `α ≤ 1/3`;
only the window `1/3 < α ≤ 1/2` depends on the endpoint inequality (manuscript Section 1 and
Corollary 2.2).
-/

noncomputable section

open scoped ComplexOrder Kronecker

namespace ThreeCopyQutritWerner

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Three copies are a reindexing of the Kronecker cube. -/
theorem tripleCopy_eq_submatrix_kronecker (M : Matrix (m × n) (m × n) ℂ) :
    tripleCopy M = (M ⊗ₖ (M ⊗ₖ M)).submatrix (copyEquiv m n) (copyEquiv m n) := by
  ext x y
  simp only [tripleCopy, Matrix.submatrix_apply, copyEquiv, Equiv.coe_fn_mk,
    Matrix.kronecker_apply]
  ring

/-- Three copies of a positive semidefinite operator are positive semidefinite. -/
theorem tripleCopy_posSemidef {M : Matrix (m × n) (m × n) ℂ} (hM : M.PosSemidef) :
    (tripleCopy M).PosSemidef := by
  rw [tripleCopy_eq_submatrix_kronecker]
  exact (hM.kronecker (hM.kronecker hM)).submatrix _

/-- For `α ≤ 1/3` the qutrit Werner state has positive semidefinite partial transpose. -/
theorem partialTranspose_werner_three_posSemidef {α : ℝ} (h : α ≤ 1 / 3) :
    (partialTranspose (werner 3 α)).PosSemidef := by
  have hn : ¬ IsNPT (werner 3 α) := by
    rw [isNPT_werner_three_iff α (by linarith)]
    exact not_lt.mpr h
  unfold IsNPT at hn
  exact not_not.mp hn

/-- For `α ≤ 1/3`, `ρ_{3,α}` is not three-copy rank-two detectable. (No vector of any Schmidt
rank detects three copies, since `(ρ^{⊗3})^Γ` is positive semidefinite:
`partialTranspose_tripleCopy_werner_three_posSemidef` in `Identities`.) -/
theorem not_isThreeCopyRankTwoDetectable_werner_three_of_le_third {α : ℝ} (h : α ≤ 1 / 3) :
    ¬ IsThreeCopyRankTwoDetectable (werner 3 α) := by
  rintro ⟨ψ, -, hneg⟩
  have hPSD := tripleCopy_posSemidef (partialTranspose_werner_three_posSemidef h)
  rw [partialTranspose_tripleCopy] at hneg
  exact (not_posSemidef_iff_exists_expectation_re_neg _ hPSD.isHermitian).mpr ⟨ψ, hneg⟩ hPSD

/-- Corollary 2.2 at `d = 3`, operational form, unconditionally for `α ≤ 1/3`: three copies
of `ρ_{3,α}` are not distillable. -/
theorem not_isThreeCopyFilterDistillable_werner_three_of_le_third {α : ℝ} (h : α ≤ 1 / 3) :
    ¬ IsThreeCopyFilterDistillable (werner 3 α) := by
  rw [isThreeCopyFilterDistillable_iff _ (werner_isHermitian 3 α)]
  exact not_isThreeCopyRankTwoDetectable_werner_three_of_le_third h

/-- Corollary 2.2, at `d = 3`, unconditionally for `α ≤ 1/3`: a trace-preserving
separable operation on three copies of `ρ_{3,α}` has overlap at most `1/2` with `Φ`. -/
theorem werner_three_maxEntOverlap_le_of_le_third {α : ℝ} (h : α ≤ 1 / 3) {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (B : Fin K → Matrix (Fin 2) (Fin 3 × Fin 3 × Fin 3) ℂ)
    (htp : ∀ u v : (Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3),
      ∑ k, (∑ i : Fin 2, star (A k i v.1) * A k i u.1) *
        (∑ j : Fin 2, star (B k j v.2) * B k j u.2) = if u = v then 1 else 0) :
    maxEntOverlap (sepOutput A B (werner 3 α)) ≤ 1 / 2 := by
  have hb := maxEntOverlap_sepOutput_le A B (werner 3 α)
    (not_isThreeCopyRankTwoDetectable_werner_three_of_le_third h)
  rw [trace_sepOutput A B _ htp, trace_tripleCopy,
    trace_werner 3 α (by norm_num) (by intro h'; norm_num at h'; linarith)] at hb
  simpa using hb

end ThreeCopyQutritWerner

end
