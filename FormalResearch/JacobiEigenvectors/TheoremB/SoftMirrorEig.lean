module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkEigen
public import FormalResearch.JacobiEigenvectors.TheoremA.NegTransport

/-!
# Paper J, Theorem B, L3.5b (soft halves), part 10: the mirror transport of eigen-systems

* `mirror_mirror`: `mirrorFamily (mirrorFamily F) = F`.
* `jacobiMat_mirror`: `(mirrorFamily F).jacobiMat mu N i j = F.jacobiMat mu N (rev i) (rev j)`.
* `mirrorU`, `isEigenSystem_mirror`: if the last row of every column of `U` is nonzero (`eigen_last_ne_zero`), then `(X, mirrorU U)` is an eigen-system of the mirror family, `mirrorU U i k = sign(U_{N k}) U_{N-i, k}` (the gauge
  `(Psi'_k)_0 > 0` of the mirror matrix), and `eigVec_mirrorU`: `eigVec (mirrorU U) k n = +-eigVec U k (N - n)`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA

theorem mirror_mirror {Par : Type*} (F : SymbolFamily Par) : mirrorFamily (mirrorFamily F) = F := by
  cases F
  simp [mirrorFamily]

theorem entryB_mirror {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (k : ℤ) :
    (mirrorFamily F).entryB μ N k = F.entryB μ N ((N : ℤ) - k) := by
  have h := diagQ_mirror F μ N 0 k
  unfold SymbolFamily.diagQ at h
  linarith

theorem jacobiMat_mirror {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (i j : Fin (N + 1)) :
    (mirrorFamily F).jacobiMat μ N i j = F.jacobiMat μ N (Fin.rev i) (Fin.rev j) := by
  have hri : ((Fin.rev i : Fin (N + 1)) : ℕ) = N - i := by simp [Fin.val_rev]
  have hrj : ((Fin.rev j : Fin (N + 1)) : ℕ) = N - j := by simp [Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  unfold SymbolFamily.jacobiMat
  simp only [Matrix.of_apply]
  by_cases h1 : i = j
  · subst h1
    simp only [if_true]
    rw [entryB_mirror, hri]
    congr 2
    omega
  · have h1' : Fin.rev i ≠ Fin.rev j := fun h => h1 (Fin.rev_injective h)
    rw [if_neg h1, if_neg h1']
    by_cases h2 : j.val = i.val + 1
    · have h3 : (Fin.rev i : Fin (N + 1)).val = (Fin.rev j : Fin (N + 1)).val + 1 := by omega
      rw [if_pos h2, if_neg (show ¬ (Fin.rev j : Fin (N + 1)).val = (Fin.rev i : Fin (N + 1)).val + 1 by omega), if_pos h3, bondA_mirror, hrj]
      congr 1
      omega
    · rw [if_neg h2]
      by_cases h4 : i.val = j.val + 1
      · have h5 : (Fin.rev j : Fin (N + 1)).val = (Fin.rev i : Fin (N + 1)).val + 1 := by omega
        rw [if_pos h4, if_pos h5, bondA_mirror, hri]
        congr 1
        omega
      · have h5 : ¬ (Fin.rev j : Fin (N + 1)).val = (Fin.rev i : Fin (N + 1)).val + 1 := by omega
        have h3 : ¬ (Fin.rev i : Fin (N + 1)).val = (Fin.rev j : Fin (N + 1)).val + 1 := by omega
        rw [if_neg h4, if_neg h5, if_neg h3]

/-- the reflected eigenvector matrix in the gauge `(Psi'_k)_0 > 0`. -/
def mirrorU {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i k => (if 0 < U (Fin.last N) k then (1 : ℝ) else -1) * U (Fin.rev i) k

theorem isEigenSystem_mirror {Par : Type*} {F : SymbolFamily Par} {μ : Par} {N : ℕ} {X : Fin (N + 1) → ℝ}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hE : IsEigenSystem (F.jacobiMat μ N) X U) (hne : ∀ k, U (Fin.last N) k ≠ 0) :
    IsEigenSystem ((mirrorFamily F).jacobiMat μ N) X (mirrorU U) := by
  have hs : ∀ k, ((if 0 < U (Fin.last N) k then (1 : ℝ) else -1)) ^ 2 = 1 := fun k => by split_ifs <;> norm_num
  refine ⟨?_, ?_, hE.anti, ?_⟩
  · ext a b
    have h := congrFun (congrFun hE.orth a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h ⊢
    simp only [mirrorU, Matrix.of_apply]
    have key := Equiv.sum_comp Fin.revPerm (fun i => U i a * U i b)
    simp only [Fin.revPerm_apply] at key
    have e : ∑ i : Fin (N + 1), (if 0 < U (Fin.last N) a then (1 : ℝ) else -1) * U (Fin.rev i) a *
        ((if 0 < U (Fin.last N) b then (1 : ℝ) else -1) * U (Fin.rev i) b) =
        (if 0 < U (Fin.last N) a then (1 : ℝ) else -1) * (if 0 < U (Fin.last N) b then (1 : ℝ) else -1) *
          ∑ i : Fin (N + 1), U i a * U i b := by
      rw [← key, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [e, h]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, mul_one]
      rw [← sq]; exact hs a
    · simp [hab]
  · ext i k
    have h := congrFun (congrFun hE.eig (Fin.rev i)) k
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at h
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [mirrorU, Matrix.of_apply, jacobiMat_mirror]
    have e : ∑ l : Fin (N + 1), F.jacobiMat μ N (Fin.rev i) (Fin.rev l) *
        ((if 0 < U (Fin.last N) k then (1 : ℝ) else -1) * U (Fin.rev l) k) =
        (if 0 < U (Fin.last N) k then (1 : ℝ) else -1) * ∑ l : Fin (N + 1), F.jacobiMat μ N (Fin.rev i) l * U l k := by
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp Fin.revPerm (fun l => (if 0 < U (Fin.last N) k then (1 : ℝ) else -1) * (F.jacobiMat μ N (Fin.rev i) l * U l k))]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Fin.revPerm_apply]
      ring
    rw [e, h]
    ring
  · intro k
    simp only [mirrorU, Matrix.of_apply, Fin.rev_zero]
    have := hne k
    split_ifs with hp
    · simpa using hp
    · have : U (Fin.last N) k < 0 := lt_of_le_of_ne (not_lt.mp hp) (hne k)
      linarith

theorem eigVec_mirrorU {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) (n : ℤ) :
    eigVec (mirrorU U) k n = (if 0 < U (Fin.last N) k then (1 : ℝ) else -1) * eigVec U k ((N : ℤ) - n) := by
  unfold eigVec
  by_cases hn : 0 ≤ n ∧ n ≤ (N : ℤ)
  · have hn' : 0 ≤ (N : ℤ) - n ∧ (N : ℤ) - n ≤ (N : ℤ) := by omega
    rw [dif_pos hn, dif_pos hn']
    simp only [mirrorU, Matrix.of_apply]
    congr 2
    ext
    simp [Fin.val_rev]
    omega
  · have hn' : ¬ (0 ≤ (N : ℤ) - n ∧ (N : ℤ) - n ≤ (N : ℤ)) := by omega
    rw [dif_neg hn, dif_neg hn']
    ring

end FormalResearch.JacobiEigenvectors.TheoremB

end
