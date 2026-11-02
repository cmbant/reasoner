import FormalResearch.FourQubitEntropy.QVCheck.Tables

/-!
# Matrix identities for the coupled data (K3, K4)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem mul_nm (D1 D2 D3 : ℕ) (f g : ℕ → ℕ → ℤ) :
    nm D1 D2 f * nm D2 D3 g = nm D1 D3 (fun i k => ∑ e ∈ range D2, f i e * g e k) := by
  refine Matrix.ext fun i k => ?_
  simp only [nm, Matrix.mul_apply, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun e => f i e * g e k) D2]

theorem transpose_nm (D1 D2 : ℕ) (f : ℕ → ℕ → ℤ) : (nm D1 D2 f)ᵀ = nm D2 D1 (fun a b => f b a) := by
  refine Matrix.ext fun i k => ?_
  simp [nm]

theorem nm_apply (D1 D2 : ℕ) (f : ℕ → ℕ → ℤ) (i : Fin D1) (j : Fin D2) : nm D1 D2 f i j = f i.val j.val := rfl

theorem nm_congr (D1 D2 : ℕ) (f g : ℕ → ℕ → ℤ) (h : ∀ i < D1, ∀ j < D2, f i j = g i j) : nm D1 D2 f = nm D1 D2 g := by
  refine Matrix.ext fun i j => ?_
  exact h i.val i.2 j.val j.2

/-- `T_A P T_inv` as an `nm` matrix -/
theorem tri_nm (DA : ℕ) (t g ti : ℕ → ℕ → ℤ) :
    nm DA DA t * nm DA DA g * nm DA DA ti =
      nm DA DA (fun i k => ∑ e ∈ range DA, ∑ e' ∈ range DA, t i e * g e e' * ti e' k) := by
  rw [mul_nm, mul_nm]
  refine nm_congr _ _ _ _ fun i _ k _ => ?_
  simp only [Finset.sum_mul]
  exact Finset.sum_comm


theorem checkT_spec (h : checkT () = true) (pj : ℕ) (hpj : pj < 16) :
    delta pj ≠ 0 ∧ ∀ i j : ℕ, i < pairDim pj → j < pairDim pj →
      ∑ k ∈ range (pairDim pj), tiAt pj i k * tAt pj k j = if i = j then delta pj else 0 := by
  unfold checkT at h
  have h1 := (allTo_iff _ _).1 h pj (by rw [hide_eq]; exact hpj)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
  refine ⟨h1.1, fun i j hi hj => ?_⟩
  have h2 := (allTo_iff _ _).1 h1.2 i hi
  have h3 := (allTo_iff _ _).1 h2 j hj
  simp only [Bool.and_eq_true, beq_iff_eq, sumTo_eq] at h3
  rw [h3.2]

theorem coupledW_entry (code b i j : ℕ) (hi : i < pairDim (pA code)) (hj : j < pairDim (pB code)) :
    gt (coupledW code b) (i * pairDim (pB code) + j) =
      ∑ l ∈ range (pairDim (pB code)), (∑ k ∈ range (pairDim (pA code)),
        tiAt (pA code) k i * wAt code b (k * pairDim (pB code) + l)) * tiAt (pB code) l j := by
  unfold coupledW
  have hlt : i * pairDim (pB code) + j < pairDim (pA code) * pairDim (pB code) := by nlinarith
  rw [gt_tab, if_pos hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hlt' : i * pairDim (pB code) + l < pairDim (pA code) * pairDim (pB code) := by nlinarith
  obtain ⟨e1, e2⟩ := div_mod_aux i l (pairDim (pB code)) hl'
  rw [gt_tab, if_pos hlt', sumTo_eq]
  simp only [e1, e2]

theorem coupledV_entry (code b i j : ℕ) (hi : i < pairDim (pA code)) (hj : j < pairDim (pB code)) :
    gt (coupledV code b) (i * pairDim (pB code) + j) =
      ∑ l ∈ range (pairDim (pB code)), (∑ k ∈ range (pairDim (pA code)),
        tAt (pA code) i k * vAt code b (k * pairDim (pB code) + l)) * tAt (pB code) j l := by
  unfold coupledV
  have hlt : i * pairDim (pB code) + j < pairDim (pA code) * pairDim (pB code) := by nlinarith
  rw [gt_tab, if_pos hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hlt' : i * pairDim (pB code) + l < pairDim (pA code) * pairDim (pB code) := by nlinarith
  obtain ⟨e1, e2⟩ := div_mod_aux i l (pairDim (pB code)) hl'
  rw [gt_tab, if_pos hlt', sumTo_eq]
  simp only [e1, e2]

theorem coupledW_nm (code b : ℕ) :
    nm (pairDim (pA code)) (pairDim (pB code)) (fun i j => gt (coupledW code b) (i * pairDim (pB code) + j)) =
      (nm (pairDim (pA code)) (pairDim (pA code)) (tiAt (pA code)))ᵀ *
        nm (pairDim (pA code)) (pairDim (pB code)) (fun i j => wAt code b (i * pairDim (pB code) + j)) *
        nm (pairDim (pB code)) (pairDim (pB code)) (tiAt (pB code)) := by
  rw [transpose_nm, mul_nm, mul_nm]
  exact nm_congr _ _ _ _ fun i hi j hj => by
    rw [coupledW_entry code b i j hi hj]

theorem coupledV_nm (code b : ℕ) :
    nm (pairDim (pA code)) (pairDim (pB code)) (fun i j => gt (coupledV code b) (i * pairDim (pB code) + j)) =
      nm (pairDim (pA code)) (pairDim (pA code)) (tAt (pA code)) *
        nm (pairDim (pA code)) (pairDim (pB code)) (fun i j => vAt code b (i * pairDim (pB code) + j)) *
        (nm (pairDim (pB code)) (pairDim (pB code)) (tAt (pB code)))ᵀ := by
  rw [transpose_nm, mul_nm, mul_nm]
  exact nm_congr _ _ _ _ fun i hi j hj => by
    rw [coupledV_entry code b i j hi hj]

end QVCheck
