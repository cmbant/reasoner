module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Count
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem

/-!
# Paper J, Layer 2 (L2.C7): a zero of `casD` is an eigenvalue (the link of Step 6)

Source: app_thmA, proof of lem:tha-count and Step 6 ("the zeros of `D` are the eigenvalues").

Proved here (axiom-pinned):
* `casD_zero_eigvec`: for positive bonds and `1 <= N`, at a zero `X` of `casD F mu N` the vector `(p_0(X), ..., p_N(X))` satisfies
  `J v = X v` (the rows `0..N-1` are the recurrence `pZ_rec`, the last row is `casD = (X - B_N) p_N - A_{N-1} p_{N-1}` by `green_cas_last`).
* `casD_zero_exists_eig`: hence for every eigen-system `IsEigenSystem (F.jacobiMat mu N) Xs Um` there is an index `i` with `Xs i = X`
  (`U` is orthogonal, `p_0 = 1`, so the coordinate vector `U^T v` is nonzero and is an eigenvector of `diag Xs`).

Differences from the paper: none.  Not formalised: the converse (every eigenvalue is a zero of `casD`), not needed.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine
open scoped Matrix

variable {Par : Type*} {F : SymbolFamily Par} {μ : Par} {N : ℕ}

lemma extV_pZ (X : ℝ) (n : ℤ) (h0 : 0 ≤ n) (hn : n ≤ (N : ℤ)) :
    extV (N := N) (fun i : Fin (N + 1) => pZ F μ N X (i.val : ℤ)) n = pZ F μ N X n := by
  unfold extV
  rw [dif_pos ⟨h0, hn⟩]
  congr 1

/-- At a zero of `casD`, `(p_i(X))_{i<=N}` is an eigenvector of `J` with eigenvalue `X`. -/
theorem casD_zero_eigvec (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) {X : ℝ}
    (h0 : casD F μ N X = 0) :
    F.jacobiMat μ N *ᵥ (fun i : Fin (N + 1) => pZ F μ N X (i.val : ℤ)) = X • (fun i : Fin (N + 1) => pZ F μ N X (i.val : ℤ)) := by
  have hA1 : F.bondA μ N (-1) = 0 := by simp [SymbolFamily.bondA]
  have hAN : F.bondA μ N N = 0 := by simp [SymbolFamily.bondA]
  have hlast := green_cas_last (F.bondA μ N) (F.entryB μ N) X (N : ℤ) (by exact_mod_cast hN) hAN (pZ F μ N X) (qZ F μ N X)
    (fun i hi => Lop_pZ hpos hN X i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
    (fun i hi => Lop_qZ hpos hN X i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2) (qZ_N X)
  rw [← casD_eq_cas, h0] at hlast
  funext i
  rw [jacobiMat_mulVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hi0 : (0 : ℤ) ≤ (i.val : ℤ) := by positivity
  have hiN : (i.val : ℤ) ≤ (N : ℤ) := by have := i.isLt; omega
  have hm1 : F.bondA μ N ((i.val : ℤ) - 1) * extV (N := N) (fun i : Fin (N + 1) => pZ F μ N X (i.val : ℤ)) ((i.val : ℤ) - 1)
      = F.bondA μ N ((i.val : ℤ) - 1) * pZ F μ N X ((i.val : ℤ) - 1) := by
    by_cases h1 : 1 ≤ (i.val : ℤ)
    · rw [extV_pZ X _ (by omega) (by omega)]
    · have : (i.val : ℤ) = 0 := by omega
      rw [this]
      simp [hA1]
  rw [hm1]
  rcases (show (i.val : ℤ) ≤ (N : ℤ) - 1 ∨ (i.val : ℤ) = N by omega) with h | h
  · rw [extV_pZ X _ (by omega) (by omega)]
    have := pZ_rec hpos hN X (i.val : ℤ) hi0 h
    linarith
  · rw [extV_big (N := N) _ _ (by omega), h]
    simp only [mul_zero, add_zero]
    have hsub : F.bondA μ N ((N : ℤ) - 1) * pZ F μ N X ((N : ℤ) - 1) = (X - F.entryB μ N N) * pZ F μ N X N := by
      linarith
    linear_combination hlast

/-- **A zero of `casD` is an eigenvalue**: for every eigen-system there is `i` with `Xs i = X`. -/
theorem casD_zero_exists_eig (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) {X : ℝ}
    (h0 : casD F μ N X = 0) (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um) : ∃ i : Fin (N + 1), Xs i = X := by
  set v : Fin (N + 1) → ℝ := fun i => pZ F μ N X (i.val : ℤ) with hv
  have hJv := casD_zero_eigvec hpos hN h0
  have hUU : Um * Umᵀ = 1 := by
    have := hE.orth
    exact mul_eq_one_comm.mp this
  set c : Fin (N + 1) → ℝ := Umᵀ *ᵥ v with hc
  have hvc : Um *ᵥ c = v := by
    rw [hc, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hv0 : v 0 ≠ 0 := by
    simp only [hv, Fin.val_zero, Nat.cast_zero]
    rw [pZ_zero]
    exact one_ne_zero
  have hc0 : c ≠ 0 := by
    intro hz
    apply hv0
    rw [← hvc, hz, Matrix.mulVec_zero]
    rfl
  have hD : Matrix.diagonal Xs *ᵥ c = X • c := by
    have h1 : Um *ᵥ (Matrix.diagonal Xs *ᵥ c) = X • v := by
      rw [Matrix.mulVec_mulVec, ← hE.eig, ← Matrix.mulVec_mulVec, hvc, hJv]
    have h2 : Umᵀ *ᵥ (Um *ᵥ (Matrix.diagonal Xs *ᵥ c)) = Matrix.diagonal Xs *ᵥ c := by
      rw [Matrix.mulVec_mulVec, hE.orth, Matrix.one_mulVec]
    rw [← h2, h1, hc, Matrix.mulVec_smul]
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hc0 (funext hcon)
  refine ⟨i, ?_⟩
  have := congrFun hD i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hi this

end FormalResearch.JacobiEigenvectors.TheoremA

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.casD_zero_exists_eig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.casD_zero_exists_eig

end
