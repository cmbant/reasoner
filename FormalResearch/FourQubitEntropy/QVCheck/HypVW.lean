import FormalResearch.FourQubitEntropy.QVCheck.Invariance

/-!
# `hV`, `hW`: invariance of the invariant bases from `checkInvariant`
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem gt_slice (A : Array Int) (o n k : Nat) : gt (slice A o n) k = if k < n then gt A (o + k) else 0 :=
  gt_tab n _ k

theorem slice_size (A : Array Int) (o n : Nat) : (slice A o n).size = n := tab_size _ _

/-- the common entry formula for `V` and `W` -/
theorem kron_apply_slice (p : Fin 4 → Spin) (i : Fin 5) (tr : Bool) (X : Array Int) (hX : X.size = sdim (pcode p))
    (x : ∀ q, Fin (multF (p q))) :
    gt (kronGen (pcode p) i.val tr X) (flatIx (radix p) x) =
      ∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, (if tr then rhoAt (p q).val i.val (y q).val (x q).val else rhoAt (p q).val i.val (x q).val (y q).val)) *
          gt X (flatIx (radix p) y) := by
  have hd0 : spinDigit (pcode p) 0 = (p 0).val := spinDigit_pcode p 0
  have hd1 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  have hd2 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have hd3 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  rw [kronGen_eq_kron4, hd0, hd1, hd2, hd3]
  have hX' : X.size = radix p 0 * radix p 1 * radix p 2 * radix p 3 := by rw [hX, sdim_pcode]
  have := kron4_eq_sum (radix p) (fun q => genMat (p q).val i.val) tr X hX' x
  refine Eq.trans this (Finset.sum_congr rfl fun y _ => ?_)
  have hp : ∏ q, mEnt tr (genMat (p q).val i.val) (mult (p q).val) (x q).val (y q).val =
      ∏ q, (if tr then rhoAt (p q).val i.val (y q).val (x q).val else rhoAt (p q).val i.val (x q).val (y q).val) :=
    Finset.prod_congr rfl fun q _ => by
      have := mEnt_genMat tr (p q).val i.val (x q).val (y q).val (x q).2 (y q).2
      rw [this]
  exact congrArg (· * gt X (flatIx (radix p) y)) hp

theorem pcode_lt (p : Fin 4 → Spin) : pcode p < 256 := by
  have h0 := (p 0).2; have h1 := (p 1).2; have h2 := (p 2).2; have h3 := (p 3).2
  unfold pcode; omega

theorem check_inv_aux (h : checkInvariant () = true) (p : Fin 4 → Spin) (i : Fin 5) (b : Fin (nnF p)) :
    kronGen (pcode p) i.val false (slice vArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p))) =
        slice vArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p)) ∧
    kronGen (pcode p) i.val true (slice wArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p))) =
        slice wArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p)) := by
  unfold checkInvariant at h
  rw [allTo_iff] at h
  have h1 := h (pcode p) (by rw [hide_eq]; exact pcode_lt p)
  rw [allTo_iff] at h1
  have h2 := h1 b.val b.2
  rw [allTo_iff] at h2
  have h3 := h2 i.val i.2
  obtain ⟨h4, h5⟩ := Bool.and_eq_true_iff.mp h3
  exact ⟨eq_of_beq h4, eq_of_beq h5⟩

theorem gt_flat_slice (A : Array Int) (p : Fin 4 → Spin) (o : Nat) (x : ∀ q, Fin (multF (p q))) :
    gt (slice A o (sdim (pcode p))) (flatIx (radix p) x) = gt A (o + flatIx (radix p) x) := by
  rw [gt_slice, if_pos]
  rw [sdim_pcode]; exact flatIx_lt (radix p) x

theorem kron_mul_Vmat_apply (p : Fin 4 → Spin) (i : Fin 5) (x : ∀ q, Fin (multF (p q))) (b : Fin (nnF p)) :
    ((kronPi (fun q => rho0 i (p q))) * Vmat p) x b =
      ∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, rhoAt (p q).val i.val (x q).val (y q).val) * vAt (pcode p) b.val (flatIx (radix p) y) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [kronPi_apply]
  have h1 : Vmat p y b = vAt (pcode p) b.val (flatIx (radix p) y) := Matrix.of_apply _ _ _
  have h2 : ∀ q, rho0 i (p q) (x q) (y q) = rhoAt (p q).val i.val (x q).val (y q).val :=
    fun q => Matrix.of_apply _ _ _
  rw [h1]
  exact congrArg (· * _) (Finset.prod_congr rfl fun q _ => h2 q)

theorem kron_mulT_Wmat_apply (p : Fin 4 → Spin) (i : Fin 5) (x : ∀ q, Fin (multF (p q))) (b : Fin (nnF p)) :
    ((kronPi (fun q => rho0 i (p q)))ᵀ * Wmat p) x b =
      ∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, rhoAt (p q).val i.val (y q).val (x q).val) * wAt (pcode p) b.val (flatIx (radix p) y) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.transpose_apply, kronPi_apply]
  have h1 : Wmat p y b = wAt (pcode p) b.val (flatIx (radix p) y) := Matrix.of_apply _ _ _
  have h2 : ∀ q, rho0 i (p q) (y q) (x q) = rhoAt (p q).val i.val (y q).val (x q).val :=
    fun q => Matrix.of_apply _ _ _
  rw [h1]
  exact congrArg (· * _) (Finset.prod_congr rfl fun q _ => h2 q)

theorem hV_of_check (h : checkInvariant () = true) (p : Fin 4 → Spin) (i : Fin 5) :
    kronPi (fun q => rho0 i (p q)) * Vmat p = Vmat p := by
  ext x b
  have h1 := (check_inv_aux h p i b).1
  have hsz : (slice vArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p))).size = sdim (pcode p) :=
    slice_size _ _ _
  have e := kron_apply_slice p i false _ hsz x
  rw [h1, gt_flat_slice] at e
  rw [kron_mul_Vmat_apply]
  have e2 : (∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, if false = true then rhoAt (p q).val i.val (y q).val (x q).val else rhoAt (p q).val i.val (x q).val (y q).val) *
          gt (slice vArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p))) (flatIx (radix p) y)) =
      ∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, rhoAt (p q).val i.val (x q).val (y q).val) * vAt (pcode p) b.val (flatIx (radix p) y) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [gt_flat_slice]
    simp only [Bool.false_eq_true, ite_false]
    rfl
  have e3 : Vmat p x b = vAt (pcode p) b.val (flatIx (radix p) x) := Matrix.of_apply _ _ _
  rw [e3]
  exact e2.symm.trans e.symm

theorem hW_of_check (h : checkInvariant () = true) (p : Fin 4 → Spin) (i : Fin 5) :
    (kronPi (fun q => rho0 i (p q)))ᵀ * Wmat p = Wmat p := by
  ext x b
  have h1 := (check_inv_aux h p i b).2
  have hsz : (slice wArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p))).size = sdim (pcode p) :=
    slice_size _ _ _
  have e := kron_apply_slice p i true _ hsz x
  rw [h1, gt_flat_slice] at e
  rw [kron_mulT_Wmat_apply]
  have e2 : (∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, if true = true then rhoAt (p q).val i.val (y q).val (x q).val else rhoAt (p q).val i.val (x q).val (y q).val) *
          gt (slice wArr (vOff (pcode p) + b.val * sdim (pcode p)) (sdim (pcode p))) (flatIx (radix p) y)) =
      ∑ y : (∀ q, Fin (multF (p q))),
        (∏ q, rhoAt (p q).val i.val (y q).val (x q).val) * wAt (pcode p) b.val (flatIx (radix p) y) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [gt_flat_slice]
    simp only [ite_true]
    rfl
  have e3 : Wmat p x b = wAt (pcode p) b.val (flatIx (radix p) x) := Matrix.of_apply _ _ _
  rw [e3]
  exact e2.symm.trans e.symm

#print axioms hV_of_check
#print axioms hW_of_check

end QVCheck
