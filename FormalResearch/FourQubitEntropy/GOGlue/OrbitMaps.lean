module

public import FormalResearch.FourQubitEntropy.GOGlue.Orbit
public import FormalResearch.FourQubitEntropy.GOGlue.Target

/-!
# GO glue: the 48 signed lower permutations preserve closest-point frames

The certificate symmetrises over `perms × flips` (`gen_go_cert.py`): 6 permutations of the lower indices
(with the sign of the antisymmetric coordinates `b_{jk}`) and 8 sign changes `x_i ↦ ε_i x_i`.  Each is a
conjugation `(X, Y) ↦ (R X Rᵀ, R Y Rᵀ)` of the slice matrices by `R = diag(1, O)` with `O` a signed
permutation matrix (determinant `±1`), so `frame_orth` shows that a closest-point frame at `x` gives one
at every `act g (flipPt f x)` (`frame_orbit`).  The lists below are the generated data written out
(`perms_sub`, `flips_sub` in `GOGlue/Final.lean` check `perms ⊆ permLists`, `flips ⊆ flipLists`).  Claim class: proved.
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.GO
open GOProbe CO OD

noncomputable section

/-! ### Sign changes -/

def cfList (e1 e2 e3 : ℤ) : List ℤ :=
  [1, 1, 1, 1, 1, 1, 1, e1 * e2, e1 * e3, e2 * e3, e1 * e2, e1 * e3, e2 * e3, e1, e2, e3, e1, e2, e3]

def dO (e1 e2 e3 : ℤ) : M3R := Matrix.diagonal ![(e1 : ℝ), (e2 : ℝ), (e3 : ℝ)]

theorem dO_orth (e1 e2 e3 : ℤ) (h1 : (e1 : ℝ) ^ 2 = 1) (h2 : (e2 : ℝ) ^ 2 = 1) (h3 : (e3 : ℝ) ^ 2 = 1) :
    (dO e1 e2 e3)ᵀ * dO e1 e2 e3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dO, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> nlinarith

theorem flip_X (e1 e2 e3 : ℤ) (h1 : (e1 : ℝ) ^ 2 = 1) (h2 : (e2 : ℝ) ^ 2 = 1) (h3 : (e3 : ℝ) ^ 2 = 1)
    (x : ℕ → ℝ) : sX (restr (flipPt (cfList e1 e2 e3) x)) =
      lift4 (dO e1 e2 e3) * sX (restr x) * (lift4 (dO e1 e2 e3))ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, flipPt, cfList, lift4, dO, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;>
    ring_nf <;> simp [h1, h2, h3]

theorem flip_Y (e1 e2 e3 : ℤ) (h1 : (e1 : ℝ) ^ 2 = 1) (h2 : (e2 : ℝ) ^ 2 = 1) (h3 : (e3 : ℝ) ^ 2 = 1)
    (x : ℕ → ℝ) : sY (restr (flipPt (cfList e1 e2 e3) x)) =
      lift4 (dO e1 e2 e3) * sY (restr x) * (lift4 (dO e1 e2 e3))ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, flipPt, cfList, lift4, dO, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;>
    ring_nf <;> simp [h1, h2, h3]

def flipLists : List (List ℤ) :=
  [cfList 1 1 1, cfList (-1) 1 1, cfList 1 (-1) 1, cfList (-1) (-1) 1,
   cfList 1 1 (-1), cfList (-1) 1 (-1), cfList 1 (-1) (-1), cfList (-1) (-1) (-1)]

theorem frame_flip {x : ℕ → ℝ} {h : ℝ} {f : List ℤ} (hf : f ∈ flipLists)
    (hfr : IsFrame (sState (restr x)) h) : IsFrame (sState (restr (flipPt f x))) h := by
  simp only [flipLists, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact frame_orth (dO_orth _ _ _ (by norm_num) (by norm_num) (by norm_num))
      (flip_X _ _ _ (by norm_num) (by norm_num) (by norm_num) x)
      (flip_Y _ _ _ (by norm_num) (by norm_num) (by norm_num) x) hfr

/-! ### Permutations -/

def pO0 : M3R := !![1, 0, 0; 0, 1, 0; 0, 0, 1]

theorem pO0_orth : (pO0)ᵀ * pO0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pO0, Matrix.mul_apply, Fin.sum_univ_three]

theorem pX0_eq (x : ℕ → ℝ) : sX (restr (act (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO0 * sX (restr x) * (lift4 pO0)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, act, lift4, pO0, Matrix.mul_apply, Fin.sum_univ_four]

theorem pY0_eq (x : ℕ → ℝ) : sY (restr (act (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO0 * sY (restr x) * (lift4 pO0)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, act, lift4, pO0, Matrix.mul_apply, Fin.sum_univ_four]

def pO1 : M3R := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem pO1_orth : (pO1)ᵀ * pO1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pO1, Matrix.mul_apply, Fin.sum_univ_three]

theorem pX1_eq (x : ℕ → ℝ) : sX (restr (act (([0, 1, 3, 2, 4, 6, 5, 8, 7, 9, 11, 10, 12, 13, 15, 14, 16, 18, 17],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO1 * sX (restr x) * (lift4 pO1)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, act, lift4, pO1, Matrix.mul_apply, Fin.sum_univ_four] ; ring

theorem pY1_eq (x : ℕ → ℝ) : sY (restr (act (([0, 1, 3, 2, 4, 6, 5, 8, 7, 9, 11, 10, 12, 13, 15, 14, 16, 18, 17],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO1 * sY (restr x) * (lift4 pO1)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, act, lift4, pO1, Matrix.mul_apply, Fin.sum_univ_four] ; ring

def pO2 : M3R := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem pO2_orth : (pO2)ᵀ * pO2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pO2, Matrix.mul_apply, Fin.sum_univ_three]

theorem pX2_eq (x : ℕ → ℝ) : sX (restr (act (([0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 10, 12, 11, 14, 13, 15, 17, 16, 18],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO2 * sX (restr x) * (lift4 pO2)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, act, lift4, pO2, Matrix.mul_apply, Fin.sum_univ_four] ; ring

theorem pY2_eq (x : ℕ → ℝ) : sY (restr (act (([0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 10, 12, 11, 14, 13, 15, 17, 16, 18],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO2 * sY (restr x) * (lift4 pO2)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, act, lift4, pO2, Matrix.mul_apply, Fin.sum_univ_four] ; ring

def pO3 : M3R := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem pO3_orth : (pO3)ᵀ * pO3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pO3, Matrix.mul_apply, Fin.sum_univ_three]

theorem pX3_eq (x : ℕ → ℝ) : sX (restr (act (([0, 2, 3, 1, 5, 6, 4, 9, 7, 8, 12, 10, 11, 14, 15, 13, 17, 18, 16],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO3 * sX (restr x) * (lift4 pO3)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, act, lift4, pO3, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem pY3_eq (x : ℕ → ℝ) : sY (restr (act (([0, 2, 3, 1, 5, 6, 4, 9, 7, 8, 12, 10, 11, 14, 15, 13, 17, 18, 16],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO3 * sY (restr x) * (lift4 pO3)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, act, lift4, pO3, Matrix.mul_apply, Fin.sum_univ_four] ; ring

def pO4 : M3R := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem pO4_orth : (pO4)ᵀ * pO4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pO4, Matrix.mul_apply, Fin.sum_univ_three]

theorem pX4_eq (x : ℕ → ℝ) : sX (restr (act (([0, 3, 1, 2, 6, 4, 5, 8, 9, 7, 11, 12, 10, 15, 13, 14, 18, 16, 17],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO4 * sX (restr x) * (lift4 pO4)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, act, lift4, pO4, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem pY4_eq (x : ℕ → ℝ) : sY (restr (act (([0, 3, 1, 2, 6, 4, 5, 8, 9, 7, 11, 12, 10, 15, 13, 14, 18, 16, 17],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO4 * sY (restr x) * (lift4 pO4)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, act, lift4, pO4, Matrix.mul_apply, Fin.sum_univ_four] ; ring

def pO5 : M3R := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem pO5_orth : (pO5)ᵀ * pO5 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pO5, Matrix.mul_apply, Fin.sum_univ_three]

theorem pX5_eq (x : ℕ → ℝ) : sX (restr (act (([0, 3, 2, 1, 6, 5, 4, 9, 8, 7, 12, 11, 10, 15, 14, 13, 18, 17, 16],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO5 * sX (restr x) * (lift4 pO5)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sX, restr, act, lift4, pO5, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem pY5_eq (x : ℕ → ℝ) : sY (restr (act (([0, 3, 2, 1, 6, 5, 4, 9, 8, 7, 12, 11, 10, 15, 14, 13, 18, 17, 16],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1]) : List ℕ × List ℤ) x)) =
    lift4 pO5 * sY (restr x) * (lift4 pO5)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sY, restr, act, lift4, pO5, Matrix.mul_apply, Fin.sum_univ_four] ; ring

def permLists : List (List ℕ × List ℤ) := [
  ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
  ([0, 1, 3, 2, 4, 6, 5, 8, 7, 9, 11, 10, 12, 13, 15, 14, 16, 18, 17],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1]),
  ([0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 10, 12, 11, 14, 13, 15, 17, 16, 18],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1]),
  ([0, 2, 3, 1, 5, 6, 4, 9, 7, 8, 12, 10, 11, 14, 15, 13, 17, 18, 16],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1]),
  ([0, 3, 1, 2, 6, 4, 5, 8, 9, 7, 11, 12, 10, 15, 13, 14, 18, 16, 17],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1]),
  ([0, 3, 2, 1, 6, 5, 4, 9, 8, 7, 12, 11, 10, 15, 14, 13, 18, 17, 16],
    [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, 1])]

theorem frame_perm {x : ℕ → ℝ} {h : ℝ} {g : List ℕ × List ℤ} (hg : g ∈ permLists)
    (hfr : IsFrame (sState (restr x)) h) : IsFrame (sState (restr (act g x))) h := by
  simp only [permLists, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact frame_orth pO0_orth (pX0_eq x) (pY0_eq x) hfr
  · exact frame_orth pO1_orth (pX1_eq x) (pY1_eq x) hfr
  · exact frame_orth pO2_orth (pX2_eq x) (pY2_eq x) hfr
  · exact frame_orth pO3_orth (pX3_eq x) (pY3_eq x) hfr
  · exact frame_orth pO4_orth (pX4_eq x) (pY4_eq x) hfr
  · exact frame_orth pO5_orth (pX5_eq x) (pY5_eq x) hfr

/-- **Closest-point frames are preserved by the 48 coordinate maps of the certificate.** -/
theorem frame_orbit {x : ℕ → ℝ} {h : ℝ} (hfr : IsFrame (sState (restr x)) h) {g : List ℕ × List ℤ}
    {f : List ℤ} (hg : g ∈ permLists) (hf : f ∈ flipLists) :
    IsFrame (sState (restr (act g (flipPt f x)))) h :=
  frame_perm hg (frame_flip hf hfr)

end

end FormalResearch.FourQubitEntropy.GO
