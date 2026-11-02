import FormalResearch.FourQubitEntropy.QVCheck.Coupled
import QVCheckImpl.Impl5

/-!
# Entries of the tables `Π[l] = T (Q0 ⊗ Q1) Tinv` (`tableLetter`)
-/

open Finset
open scoped Matrix

namespace QVCheck

/-- the `D × D` Kronecker matrix `Q0 ⊗ Q1` of a letter, at natural indices -/
def pairKron (ai sp0 sp1 pj : ℕ) (l : Letter) (e e' : ℕ) : ℤ :=
  psiAt ai sp0 (pj / 4) l.1 l.2.1 (e / mult (pj % 4)) (e' / mult (pj % 4)) *
    psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 (e % mult (pj % 4)) (e' % mult (pj % 4))

theorem gt_tabIdx (n : ℕ) (f : ℕ → ℤ) (a b D : ℕ) (hb : b < D) (hlt : a * D + b < n) :
    gt (tab n f) (a * D + b) = f (a * D + b) := by
  rw [gt_tab, if_pos hlt]

theorem tlQ0_apply (ai sp0 pj : ℕ) (l : Letter) (a b : ℕ) (ha : a < mult (pj / 4)) (hb : b < mult (pj / 4)) :
    gt (tlQ0 ai sp0 pj l) (a * mult (pj / 4) + b) = psiAt ai sp0 (pj / 4) l.1 l.2.1 a b := by
  unfold tlQ0
  have hlt : a * mult (pj / 4) + b < mult (pj / 4) * mult (pj / 4) := by nlinarith
  rw [gt_tab, if_pos hlt]
  obtain ⟨e1, e2⟩ := div_mod_aux a b (mult (pj / 4)) hb
  rw [e1, e2]

theorem tlQ1_apply (ai sp1 pj : ℕ) (l : Letter) (a b : ℕ) (ha : a < mult (pj % 4)) (hb : b < mult (pj % 4)) :
    gt (tlQ1 ai sp1 pj l) (a * mult (pj % 4) + b) = psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 a b := by
  unfold tlQ1
  have hlt : a * mult (pj % 4) + b < mult (pj % 4) * mult (pj % 4) := by nlinarith
  rw [gt_tab, if_pos hlt]
  obtain ⟨e1, e2⟩ := div_mod_aux a b (mult (pj % 4)) hb
  rw [e1, e2]

theorem tlS_apply (ai sp1 pj : ℕ) (l : Letter) (k0 i1 c : ℕ) (hk0 : k0 < mult (pj / 4)) (hi1 : i1 < mult (pj % 4))
    (hc : c < mult (pj / 4) * mult (pj % 4)) :
    gt (tlS ai sp1 pj l) ((k0 * mult (pj % 4) + i1) * (mult (pj / 4) * mult (pj % 4)) + c) =
      ∑ k1 ∈ range (mult (pj % 4)), psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 i1 k1 * tiAt pj (k0 * mult (pj % 4) + k1) c := by
  unfold tlS
  dsimp only
  have hlt : (k0 * mult (pj % 4) + i1) * (mult (pj / 4) * mult (pj % 4)) + c <
      mult (pj / 4) * mult (pj % 4) * (mult (pj / 4) * mult (pj % 4)) := by
    have : k0 * mult (pj % 4) + i1 < mult (pj / 4) * mult (pj % 4) := by nlinarith
    nlinarith
  rw [gt_tab, if_pos hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux (k0 * mult (pj % 4) + i1) c (mult (pj / 4) * mult (pj % 4)) hc
  obtain ⟨f1, f2⟩ := div_mod_aux k0 i1 (mult (pj % 4)) hi1
  simp only [d1, d2, f1, f2]
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  have hk1' := Finset.mem_range.1 hk1
  rw [tlQ1_apply ai sp1 pj l i1 k1 hi1 hk1']


theorem tlM1_apply (ai sp0 sp1 pj : ℕ) (l : Letter) (k c : ℕ) (hk : k < mult (pj / 4) * mult (pj % 4))
    (hc : c < mult (pj / 4) * mult (pj % 4)) :
    gt (tlM1 ai sp0 sp1 pj l) (k * (mult (pj / 4) * mult (pj % 4)) + c) =
      ∑ k0 ∈ range (mult (pj / 4)), psiAt ai sp0 (pj / 4) l.1 l.2.1 (k / mult (pj % 4)) k0 *
        ∑ k1 ∈ range (mult (pj % 4)), psiAt ai sp1 (pj % 4) l.2.2.1 l.2.2.2 (k % mult (pj % 4)) k1 *
          tiAt pj (k0 * mult (pj % 4) + k1) c := by
  unfold tlM1
  dsimp only
  have hlt : k * (mult (pj / 4) * mult (pj % 4)) + c < mult (pj / 4) * mult (pj % 4) * (mult (pj / 4) * mult (pj % 4)) := by
    nlinarith
  rw [gt_tab, if_pos hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux k c (mult (pj / 4) * mult (pj % 4)) hc
  simp only [d1, d2]
  have hm1 : 0 < mult (pj % 4) := by
    rcases Nat.eq_zero_or_pos (mult (pj % 4)) with h | h
    · rw [h] at hk; omega
    · exact h
  have hk1 : k % mult (pj % 4) < mult (pj % 4) := Nat.mod_lt _ hm1
  have hk2 : k / mult (pj % 4) < mult (pj / 4) := Nat.div_lt_of_lt_mul (by nlinarith)
  refine Finset.sum_congr rfl fun k0 hk0 => ?_
  have hk0' := Finset.mem_range.1 hk0
  rw [tlQ0_apply ai sp0 pj l _ k0 hk2 hk0', tlS_apply ai sp1 pj l k0 _ c hk0' hk1 hc]

theorem tableLetter_apply (ai sp0 sp1 pj : ℕ) (l : Letter) (row col : ℕ) (hr : row < mult (pj / 4) * mult (pj % 4))
    (hc : col < mult (pj / 4) * mult (pj % 4)) :
    gt (tableLetter ai sp0 sp1 pj l) (row * (mult (pj / 4) * mult (pj % 4)) + col) =
      ∑ e ∈ range (mult (pj / 4) * mult (pj % 4)), ∑ e' ∈ range (mult (pj / 4) * mult (pj % 4)),
        tAt pj row e * pairKron ai sp0 sp1 pj l e e' * tiAt pj e' col := by
  unfold tableLetter
  dsimp only
  have hlt : row * (mult (pj / 4) * mult (pj % 4)) + col < mult (pj / 4) * mult (pj % 4) * (mult (pj / 4) * mult (pj % 4)) := by
    nlinarith
  rw [gt_tab, if_pos hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux row col (mult (pj / 4) * mult (pj % 4)) hc
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := Finset.mem_range.1 he
  rw [tlM1_apply ai sp0 sp1 pj l e col he' hc]
  rw [sum_range_mul_eq _ (mult (pj / 4)) (mult (pj % 4))]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k0 hk0 => ?_
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  have hk1' := Finset.mem_range.1 hk1
  unfold pairKron
  obtain ⟨q1, q2⟩ := div_mod_aux k0 k1 (mult (pj % 4)) hk1'
  rw [q1, q2]
  ring

end QVCheck
