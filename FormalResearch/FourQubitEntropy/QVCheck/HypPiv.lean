import FormalResearch.FourQubitEntropy.QVCheck.HypVW
import FormalResearch.FourQubitEntropy.QVCheck.Coupling

/-!
# `hdetV`, `hdetW`: pivot minors from the left-inverse certificates of `checkPivots`
-/

open Finset
open scoped Matrix

namespace QVCheck

theorem exists_flatIx (m : Fin 4 → ℕ) (f : ℕ) (hf : f < m 0 * m 1 * m 2 * m 3) :
    ∃ x : ∀ q : Fin 4, Fin (m q), flatIx m x = f := by
  have p0 : 0 < m 0 := by
    rcases Nat.eq_zero_or_pos (m 0) with h | h
    · simp [h] at hf
    · exact h
  have p1 : 0 < m 1 := by
    rcases Nat.eq_zero_or_pos (m 1) with h | h
    · simp [h] at hf
    · exact h
  have p2 : 0 < m 2 := by
    rcases Nat.eq_zero_or_pos (m 2) with h | h
    · simp [h] at hf
    · exact h
  have p3 : 0 < m 3 := by
    rcases Nat.eq_zero_or_pos (m 3) with h | h
    · simp [h] at hf
    · exact h
  set f1 := f / m 3 with hf1
  set f2 := f1 / m 2 with hf2
  set a := f2 / m 1 with ha
  have e0 : f = f1 * m 3 + f % m 3 := by rw [hf1]; have := Nat.div_add_mod f (m 3); linarith [Nat.mul_comm (m 3) (f / m 3)]
  have e1 : f1 = f2 * m 2 + f1 % m 2 := by rw [hf2]; have := Nat.div_add_mod f1 (m 2); linarith [Nat.mul_comm (m 2) (f1 / m 2)]
  have e2 : f2 = a * m 1 + f2 % m 1 := by rw [ha]; have := Nat.div_add_mod f2 (m 1); linarith [Nat.mul_comm (m 1) (f2 / m 1)]
  have hlt : a < m 0 := by
    have h3 : a * m 1 ≤ f2 := by rw [e2]; omega
    have h4 : f2 * m 2 ≤ f1 := by rw [e1]; omega
    have h5 : f1 * m 3 ≤ f := by rw [e0]; omega
    have : a * m 1 * m 2 * m 3 < m 0 * m 1 * m 2 * m 3 := by
      calc a * m 1 * m 2 * m 3 ≤ f2 * m 2 * m 3 := by
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact h3
        _ ≤ f1 * m 3 := Nat.mul_le_mul_right _ h4
        _ ≤ f := h5
        _ < _ := hf
    have h6 := Nat.lt_of_mul_lt_mul_right this
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_right (Nat.lt_of_mul_lt_mul_right (a := m 3) (by
      calc _ = a * m 1 * m 2 * m 3 := by ring
        _ < _ := this)))
  refine ⟨fun q => match q with
    | ⟨0, _⟩ => ⟨a, hlt⟩
    | ⟨1, _⟩ => ⟨f2 % m 1, Nat.mod_lt _ p1⟩
    | ⟨2, _⟩ => ⟨f1 % m 2, Nat.mod_lt _ p2⟩
    | ⟨3, _⟩ => ⟨f % m 3, Nat.mod_lt _ p3⟩, ?_⟩
  show flat4 (m 1) (m 2) (m 3) a (f2 % m 1) (f1 % m 2) (f % m 3) = f
  unfold flat4
  rw [← e2, ← e1, ← e0]


theorem pivCheck_det (X piv U cs : Array Int) (h : pivCheck X piv U cs = true) (p : Fin 4 → Spin)
    (M : Matrix (∀ q, Fin (multF (p q))) (Fin (nnF p)) ℤ)
    (hM : ∀ x b, M x b = gt X (vOff (pcode p) + b.val * sdim (pcode p) + flatIx (radix p) x)) :
    ∃ pv : Fin (nnF p) → (∀ q, Fin (multF (p q))), (M.submatrix pv id).det ≠ 0 := by
  by_cases hn : nnF p = 0
  · have : IsEmpty (Fin (nnF p)) := ⟨fun r => by have := r.2; omega⟩
    refine ⟨fun r => isEmptyElim r, ?_⟩
    rw [Matrix.det_isEmpty]; exact one_ne_zero
  · have hn' : 0 < nnF p := Nat.pos_of_ne_zero hn
    unfold pivCheck at h
    rw [allTo_iff] at h
    have h1 := h (pcode p) (pcode_lt p)
    have hall : ∀ i b : ℕ, i < nnF p → b < nnF p →
        ((gt cs (secRank (pcode p)) != 0 &&
          allTo (nn (pcode p)) (fun r => 0 ≤ gt piv (nOff (pcode p) + r) &&
            (gt piv (nOff (pcode p) + r)).toNat < sdim (pcode p)) &&
          sumTo (nn (pcode p)) (fun r => gt U (nnOff (pcode p) + i * nn (pcode p) + r) *
            gt X (vOff (pcode p) + b * sdim (pcode p) + (gt piv (nOff (pcode p) + r)).toNat)) ==
            (if i == b then gt cs (secRank (pcode p)) else 0)) = true) := by
      intro i b hi hb
      have h2 := (allTo_iff _ _).1 h1 i hi
      exact (allTo_iff _ _).1 h2 b hb
    have h00 := hall 0 0 hn' hn'
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h00
    obtain ⟨⟨hcs, hrng⟩, _⟩ := h00
    have hrng' := (allTo_iff _ _).1 hrng
    have hex : ∀ r : Fin (nnF p), ∃ x : (∀ q, Fin (multF (p q))),
        flatIx (radix p) x = (gt piv (nOff (pcode p) + r.val)).toNat := by
      intro r
      refine exists_flatIx (radix p) _ ?_
      rw [← sdim_pcode]
      have := hrng' r.val r.2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    choose pv hpv using hex
    refine ⟨pv, ?_⟩
    refine det_ne_zero_of_left_inv (M.submatrix pv id) (Matrix.of fun (i r : Fin (nnF p)) =>
      gt U (nnOff (pcode p) + i.val * nn (pcode p) + r.val)) (gt cs (secRank (pcode p))) hcs ?_
    ext i b
    rw [Matrix.mul_apply]
    have h3 := hall i.val b.val i.2 b.2
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    have h4 := h3.2
    rw [sumTo_eq] at h4
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, hM, hpv]
    rw [Fin.sum_univ_eq_sum_range (fun r => gt U (nnOff (pcode p) + i.val * nn (pcode p) + r) *
      gt X (vOff (pcode p) + b.val * sdim (pcode p) + (gt piv (nOff (pcode p) + r)).toNat)) (nnF p)]
    have h4' : ∑ r ∈ range (nnF p), gt U (nnOff (pcode p) + i.val * nn (pcode p) + r) *
        gt X (vOff (pcode p) + b.val * sdim (pcode p) + (gt piv (nOff (pcode p) + r)).toNat) =
        (if i.val = b.val then gt cs (secRank (pcode p)) else 0) := h4
    rw [h4']
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hib : i = b
    · subst hib; simp
    · have : i.val ≠ b.val := fun e => hib (Fin.ext e)
      simp [hib, this]

theorem hdetV_of_check (h : checkPivots true = true) (p : Fin 4 → Spin) :
    ∃ pv : Fin (nnF p) → (∀ q, Fin (multF (p q))), ((Vmat p).submatrix pv id).det ≠ 0 :=
  pivCheck_det vArr pivVArr uVArr cVArr (show pivCheck _ _ _ _ = true from h) p (Vmat p)
    (fun x b => Matrix.of_apply _ _ _)

theorem hdetW_of_check (h : checkPivots false = true) (p : Fin 4 → Spin) :
    ∃ pv : Fin (nnF p) → (∀ q, Fin (multF (p q))), ((Wmat p).submatrix pv id).det ≠ 0 :=
  pivCheck_det wArr pivWArr uWArr cWArr (show pivCheck _ _ _ _ = true from h) p (Wmat p)
    (fun x b => Matrix.of_apply _ _ _)

#print axioms hdetV_of_check

end QVCheck
