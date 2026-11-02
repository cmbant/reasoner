import FormalResearch.FourQubitEntropy.QVCheck.Contr

/-!
# The coupled contraction of one pair of letters (K4 core)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem nm_hat (DA DB d : ℕ) (iA jB : ℕ → ℕ) (hi : ∀ x < d, iA x < DA) (hj : ∀ x < d, jB x < DB) (c : ℕ → ℤ) :
    nm DA DB (fun i j => ∑ x ∈ range d, if i = iA x ∧ j = jB x then c x else 0) =
      ∑ x : Fin d, c x.val • (Matrix.single (⟨iA x.val, hi x.val x.2⟩ : Fin DA) (⟨jB x.val, hj x.val x.2⟩ : Fin DB) (1 : ℤ)) := by
  refine Matrix.ext fun i j => ?_
  simp only [nm, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun x => if i.val = iA x ∧ j.val = jB x then c x else 0) d]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : i.val = iA x.val ∧ j.val = jB x.val
  · have h' : (⟨iA x.val, hi x.val x.2⟩ : Fin DA) = i ∧ (⟨jB x.val, hj x.val x.2⟩ : Fin DB) = j :=
      ⟨Fin.ext h.1.symm, Fin.ext h.2.symm⟩
    rw [if_pos h, if_pos h', mul_one]
  · have h' : ¬((⟨iA x.val, hi x.val x.2⟩ : Fin DA) = i ∧ (⟨jB x.val, hj x.val x.2⟩ : Fin DB) = j) :=
      fun hh => h ⟨(congrArg Fin.val hh.1).symm, (congrArg Fin.val hh.2).symm⟩
    rw [if_neg h, if_neg h', mul_zero]

theorem S4_hat (DA DB d d' : ℕ) (iA jB kA lB : ℕ → ℕ) (hi : ∀ x < d, iA x < DA) (hj : ∀ x < d, jB x < DB)
    (hk : ∀ y < d', kA y < DA) (hl : ∀ y < d', lB y < DB) (c c' : ℕ → ℤ)
    (P : Matrix (Fin DA) (Fin DA) ℤ) (R' : Matrix (Fin DB) (Fin DB) ℤ) :
    S4 (nm DA DB fun i j => ∑ x ∈ range d, if i = iA x ∧ j = jB x then c x else 0) P
      (nm DA DB fun k l => ∑ y ∈ range d', if k = kA y ∧ l = lB y then c' y else 0) R' =
      ∑ x ∈ range d, ∑ y ∈ range d', c x * c' y * qe P (iA x) (kA y) * qe R' (jB x) (lB y) := by
  rw [nm_hat DA DB d iA jB hi hj c, nm_hat DA DB d' kA lB hk hl c']
  rw [S4_sum_left]
  rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ y ∈ range d', c x * c' y * qe P (iA x) (kA y) * qe R' (jB x) (lB y)) d]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [S4_smul_left, S4_sum_right]
  rw [← Fin.sum_univ_eq_sum_range (fun y => c x.val * c' y * qe P (iA x.val) (kA y) * qe R' (jB x.val) (lB y)) d',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [S4_smul_right, S4_single]
  have e1 : qe P (iA x.val) (kA y.val) = P ⟨iA x.val, hi x.val x.2⟩ ⟨kA y.val, hk y.val y.2⟩ := by
    unfold qe; rw [dif_pos ⟨hi x.val x.2, hk y.val y.2⟩]
  have e2 : qe R' (jB x.val) (lB y.val) = R' ⟨jB x.val, hj x.val x.2⟩ ⟨lB y.val, hl y.val y.2⟩ := by
    unfold qe; rw [dif_pos ⟨hj x.val x.2, hl y.val y.2⟩]
  rw [e1, e2]; ring

end QVCheck
