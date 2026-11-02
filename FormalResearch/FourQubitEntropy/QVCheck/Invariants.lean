import FormalResearch.FourQubitEntropy.QVBlock.Kron
import FormalResearch.FourQubitEntropy.QVCheck.Arrays
import FormalResearch.FourQubitEntropy.QVCheck.Coupling

/-!
# Invariant bases of the checker

The sectors of the checker as `QVBlock` data: `Spin`, `multF`, the generators `rho0` and the invariant bases `Vmat`, `Wmat`
as integer matrices.  From the array checks `checkInvariant` and `checkPivots` we get the invariance hypotheses `hV`, `hW`
and the pivot-minor hypotheses `hdetV`, `hdetW` of `QVBlock.quad_eq_zero_of_int_certificate`.
-/

open Finset FormalResearch.FourQubitEntropy.QVBlock
open scoped Matrix

namespace QVCheck

/-!
## From the array checks to the invariance hypotheses `hV`, `hW` of `QVBlock.quad_eq_zero_of_int_certificate`

Spins are `Fin 4` (twice the spin over two), `multF j = mult j`; `rho0 i j` is the generator matrix; `Vmat p`, `Wmat p` are the
invariant bases of the checker as matrices on `∀ q, Fin (multF (p q))`.
-/

/-- spin labels -/
abbrev Spin := Fin 4

def multF (j : Spin) : ℕ := mult j.val

theorem multF_pos (j : Spin) : 0 < multF j := by
  unfold multF mult; fin_cases j <;> simp

/-- `ρ_j(s_i)` -/
def rho0 (i : Fin 5) (j : Spin) : Matrix (Fin (multF j)) (Fin (multF j)) ℤ :=
  Matrix.of fun a b => rhoAt j.val i.val a.val b.val

/-- code of a spin tuple -/
def pcode (p : Fin 4 → Spin) : ℕ := (((p 0).val * 4 + (p 1).val) * 4 + (p 2).val) * 4 + (p 3).val

theorem spinDigit_pcode (p : Fin 4 → Spin) (q : Fin 4) : spinDigit (pcode p) q.val = (p q).val := by
  have h0 := (p 0).2; have h1 := (p 1).2; have h2 := (p 2).2; have h3 := (p 3).2
  unfold spinDigit pcode
  fin_cases q <;> simp <;> omega

def nnF (p : Fin 4 → Spin) : ℕ := nn (pcode p)

/-- the radices of the multiplicity space of the sector `p` -/
abbrev radix (p : Fin 4 → Spin) : Fin 4 → ℕ := fun q => multF (p q)

theorem sdim_pcode (p : Fin 4 → Spin) : sdim (pcode p) = radix p 0 * radix p 1 * radix p 2 * radix p 3 := by
  have h0 : spinDigit (pcode p) 0 = (p 0).val := spinDigit_pcode p 0
  have h1 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  have h2 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have h3 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  unfold sdim radix multF
  rw [h0, h1, h2, h3]

/-- right invariants of the checker as a matrix -/
def Vmat (p : Fin 4 → Spin) : Matrix (∀ q, Fin (multF (p q))) (Fin (nnF p)) ℤ :=
  Matrix.of fun x b => vAt (pcode p) b.val (flatIx (radix p) x)

def Wmat (p : Fin 4 → Spin) : Matrix (∀ q, Fin (multF (p q))) (Fin (nnF p)) ℤ :=
  Matrix.of fun x b => wAt (pcode p) b.val (flatIx (radix p) x)

theorem stride_eq (code : ℕ) :
    stride code 0 = mult (spinDigit code 1) * mult (spinDigit code 2) * mult (spinDigit code 3) ∧
    stride code 1 = mult (spinDigit code 2) * mult (spinDigit code 3) ∧
    stride code 2 = mult (spinDigit code 3) ∧ stride code 3 = 1 := by
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [stride, hr, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem kronGen_eq_kron4 (code i : ℕ) (tr : Bool) (X : Array Int) :
    kronGen code i tr X =
      kron4 (genMat (spinDigit code 0) i) (genMat (spinDigit code 1) i) (genMat (spinDigit code 2) i)
        (genMat (spinDigit code 3) i) (mult (spinDigit code 0)) (mult (spinDigit code 1)) (mult (spinDigit code 2))
        (mult (spinDigit code 3)) tr X := by
  obtain ⟨h0, h1, h2, h3⟩ := stride_eq code
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  unfold kronGen kron4
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h0, h1, h2, h3]

theorem genMat_apply (j i a b : ℕ) (ha : a < mult j) (hb : b < mult j) :
    gt (genMat j i) (a * mult j + b) = rhoAt j i a b := by
  have hlt : a * mult j + b < mult j * mult j := by nlinarith [ha, hb]
  unfold genMat rhoAt
  rw [gt_tab, ite_eq_left hlt, Nat.add_assoc]

theorem mEnt_genMat (tr : Bool) (j i a b : ℕ) (ha : a < mult j) (hb : b < mult j) :
    mEnt tr (genMat j i) (mult j) a b = if tr then rhoAt j i b a else rhoAt j i a b := by
  unfold mEnt
  cases tr
  · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, genMat_apply j i a b ha hb]
  · rw [ite_eq_left rfl, ite_eq_left rfl, genMat_apply j i b a hb ha]

/-!
## `hV`, `hW`: invariance of the invariant bases from `checkInvariant`
-/

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
  rw [gt_slice, ite_eq_left]
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

/-!
## `hdetV`, `hdetW`: pivot minors from the left-inverse certificates of `checkPivots`
-/

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
    (fun _ _ => Matrix.of_apply _ _ _)

theorem hdetW_of_check (h : checkPivots false = true) (p : Fin 4 → Spin) :
    ∃ pv : Fin (nnF p) → (∀ q, Fin (multF (p q))), ((Wmat p).submatrix pv id).det ≠ 0 :=
  pivCheck_det wArr pivWArr uWArr cWArr (show pivCheck _ _ _ _ = true from h) p (Wmat p)
    (fun _ _ => Matrix.of_apply _ _ _)

end QVCheck
