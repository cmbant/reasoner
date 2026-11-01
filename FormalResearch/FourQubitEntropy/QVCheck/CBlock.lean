import FormalResearch.FourQubitEntropy.QVCheck.HypPiv
import FormalResearch.FourQubitEntropy.QVFrame.Basic
import FormalResearch.FourQubitEntropy.QVBlock.Blk

/-!
# The matrix `C` of the checker as the `QVBlock` hypotheses `hCi`, `hiC`, `hρ0`

`rowNum ⟨j, k, μ⟩ = off j + k * mult j + μ` identifies the per-qubit index `Idx dimF multF` with `Fin 64`; the column index is
`numOf w` (bit convention of `QVFrame.Basic`).
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

/-- twice the spin plus one -/
def dimF (j : Spin) : ℕ := 2 * j.val + 1

/-- the per-qubit row index of `C` -/
abbrev IdxF : Type := Idx dimF multF

def rowNum (r : IdxF) : ℕ := off r.1.val + r.2.1.val * multF r.1 + r.2.2.val

theorem rowNum_lt (r : IdxF) : rowNum r < 64 := by
  revert r; decide +kernel

theorem rowNum_inj : Function.Injective rowNum := by
  decide +kernel

theorem card_idx : Fintype.card IdxF = 64 := by
  decide +kernel

/-- `Idx ≃ Fin 64` -/
noncomputable def rowEquiv : IdxF ≃ Fin 64 :=
  Equiv.ofBijective (fun r => ⟨rowNum r, rowNum_lt r⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => rowNum_inj (congrArg Fin.val h), by rw [card_idx]; simp⟩)

theorem sum_idx (f : ℕ → ℤ) : ∑ r : IdxF, f (rowNum r) = ∑ k ∈ range 64, f k := by
  rw [← Fin.sum_univ_eq_sum_range f 64]
  exact Fintype.sum_equiv rowEquiv _ _ (fun r => rfl)

theorem sum_wd (f : ℕ → ℤ) : ∑ w : Wd 6, f (numOf w) = ∑ k ∈ range 64, f k := by
  rw [← Fin.sum_univ_eq_sum_range f 64]
  exact (Fintype.sum_equiv wordEquiv (fun k : Fin 64 => f k) (fun w : Wd 6 => f (numOf w))
    (fun k => by rw [wordEquiv_apply]; simp [numOf_bitsOf])).symm

theorem numOf_inj {w w' : Wd 6} (h : numOf w = numOf w') : w = w' := by
  have := congrArg bitsOf h
  rwa [bitsOf_numOf, bitsOf_numOf] at this

/-- `C` -/
def Cmat : Matrix IdxF (Wd 6) ℤ := Matrix.of fun r w => gt cArr (rowNum r * 64 + numOf w)

/-- `Cinv` -/
def CinvMat : Matrix (Wd 6) IdxF ℤ := Matrix.of fun w r => gt cinvArr (numOf w * 64 + rowNum r)


theorem numOf_lt64 (w : Wd 6) : numOf w < 64 := numOf_lt w

theorem checkInv_spec (h : checkInv () = true) (i j : ℕ) (hi : i < 64) (hj : j < 64) :
    (∑ k ∈ range 64, gt cArr (i * 64 + k) * gt cinvArr (k * 64 + j) = if i = j then DataStr.cDen else 0) ∧
    (∑ k ∈ range 64, gt cinvArr (i * 64 + k) * gt cArr (k * 64 + j) = if i = j then DataStr.cDen else 0) := by
  unfold checkInv at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  have h1 := (allTo_iff _ _).1 h.2 i (by rw [hide_eq]; exact hi)
  have h2 := (allTo_iff _ _).1 h1 j hj
  simp only [Bool.and_eq_true, beq_iff_eq, sumTo_eq] at h2
  have e1 := h2.1
  have e2 := h2.2
  refine ⟨?_, ?_⟩
  · exact e1
  · exact e2

theorem hCi_of_check (h : checkInv () = true) : CinvMat * Cmat = DataStr.cDen • (1 : Matrix (Wd 6) (Wd 6) ℤ) := by
  ext w w'
  have key : (CinvMat * Cmat) w w' = ∑ k ∈ range 64, gt cinvArr (numOf w * 64 + k) * gt cArr (k * 64 + numOf w') := by
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun r _ => rfl).trans
      (sum_idx (fun k => gt cinvArr (numOf w * 64 + k) * gt cArr (k * 64 + numOf w')))
  rw [key, (checkInv_spec h (numOf w) (numOf w') (numOf_lt64 w) (numOf_lt64 w')).2]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hww : w = w'
  · subst hww; rw [if_pos rfl, if_pos rfl, mul_one]
  · have : numOf w ≠ numOf w' := fun e => hww (numOf_inj e)
    rw [if_neg this, if_neg hww, mul_zero]

theorem hiC_of_check (h : checkInv () = true) : Cmat * CinvMat = DataStr.cDen • (1 : Matrix IdxF IdxF ℤ) := by
  ext r r'
  have key : (Cmat * CinvMat) r r' = ∑ k ∈ range 64, gt cArr (rowNum r * 64 + k) * gt cinvArr (k * 64 + rowNum r') := by
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun w _ => rfl).trans
      (sum_wd (fun k => gt cArr (rowNum r * 64 + k) * gt cinvArr (k * 64 + rowNum r')))
  rw [key, (checkInv_spec h (rowNum r) (rowNum r') (by have := rowNum_lt r; omega) (by have := rowNum_lt r'; omega)).1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hrr : r = r'
  · subst hrr; rw [if_pos rfl, if_pos rfl, mul_one]
  · have : rowNum r ≠ rowNum r' := fun e => hrr (rowNum_inj e)
    rw [if_neg this, if_neg hrr, mul_zero]

theorem cDen_ne : DataStr.cDen ≠ 0 := by
  unfold DataStr.cDen; norm_num


/-- the five adjacent transpositions -/
def gens (i : Fin 5) : Equiv.Perm (Fin 6) := Equiv.swap i.castSucc i.succ

theorem numOf_slotAct : ∀ (i : Fin 5) (w : Wd 6), numOf (slotAct (gens i) w) = swapIdx i.val (numOf w) := by
  decide +kernel

theorem rowSpin_rowNum : ∀ r : IdxF, rowSpin (rowNum r) = r.1.val ∧ rowMu (rowNum r) = r.2.2.val ∧
    rowNum r - r.2.2.val = off r.1.val + r.2.1.val * multF r.1 := by
  decide +kernel

theorem blk_mul_apply {β : Type*} [Fintype β] (X : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)
    (M : Matrix IdxF β ℤ) (j : Spin) (k : Fin (dimF j)) (μ : Fin (multF j)) (b : β) :
    (blk dimF X * M) ⟨j, (k, μ)⟩ b = ∑ μ' : Fin (multF j), X j μ μ' * M ⟨j, (k, μ')⟩ b := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k]
    · refine Finset.sum_congr rfl fun μ' _ => ?_
      rw [blk_same]; simp
    · intro k' _ hk'
      refine Finset.sum_eq_zero fun μ' _ => ?_
      rw [blk_same, if_neg (Ne.symm hk'), zero_mul, zero_mul]
    · simp
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [blk_ne dimF X (Ne.symm hj'), zero_mul]
  · simp


theorem checkSlots_spec (h : checkSlots () = true) (i r c : ℕ) (hi : i < 5) (hr : r < 64) (hc : c < 64) :
    gt cArr (r * 64 + swapIdx i c) =
      ∑ m' ∈ range (mult (rowSpin r)), rhoAt (rowSpin r) i (rowMu r) m' * gt cArr ((r - rowMu r + m') * 64 + c) := by
  unfold checkSlots at h
  have h1 := (allTo_iff _ _).1 h i (by rw [hide_eq]; exact hi)
  have h2 := (allTo_iff _ _).1 h1 r hr
  have h3 := (allTo_iff _ _).1 h2 c hc
  have := of_decide_eq_true (by simpa using h3)
  rw [← sumTo_eq]
  exact this

theorem hrho0_of_check (h : checkSlots () = true) (i : Fin 5) :
    Cmat * (slotPerm ℤ (gens i) : Matrix (Wd 6) (Wd 6) ℤ) = blk dimF (rho0 i) * Cmat := by
  refine Matrix.ext fun r w => ?_
  obtain ⟨j, k, μ⟩ := r
  rw [blk_mul_apply]
  have hL : (Cmat * (slotPerm ℤ (gens i) : Matrix (Wd 6) (Wd 6) ℤ)) ⟨j, (k, μ)⟩ w =
      Cmat ⟨j, (k, μ)⟩ (slotAct (gens i) w) := by
    have e : ∀ a, (slotPerm ℤ (gens i) : Matrix (Wd 6) (Wd 6) ℤ) a w = if a = slotAct (gens i) w then 1 else 0 :=
      fun a => rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single (slotAct (gens i) w)]
    · rw [e, if_pos rfl, mul_one]
    · intro a _ ha
      rw [e, if_neg ha, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL]
  have hr := rowNum_lt ⟨j, (k, μ)⟩
  have hspec := checkSlots_spec h i.val (rowNum ⟨j, (k, μ)⟩) (numOf w) i.2 hr (numOf_lt64 w)
  obtain ⟨e1, e2, e3⟩ := rowSpin_rowNum ⟨j, (k, μ)⟩
  rw [e1, e2] at hspec
  have hsw := numOf_slotAct i w
  show gt cArr (rowNum ⟨j, (k, μ)⟩ * 64 + numOf (slotAct (gens i) w)) = _
  rw [hsw, hspec]
  have hm : multF j = mult j.val := rfl
  rw [← Fin.sum_univ_eq_sum_range (fun m' => rhoAt j.val i.val μ.val m' *
    gt cArr ((rowNum ⟨j, (k, μ)⟩ - μ.val + m') * 64 + numOf w)) (mult j.val)]
  refine Finset.sum_congr rfl fun μ' _ => ?_
  have h1 : rho0 i j μ μ' = rhoAt j.val i.val μ.val μ'.val := rfl
  have h2 : Cmat ⟨j, (k, μ')⟩ w = gt cArr (rowNum ⟨j, (k, μ')⟩ * 64 + numOf w) := rfl
  rw [h1, h2]
  congr 3
  unfold rowNum at e3 ⊢
  simp only at e3 ⊢
  omega


theorem blk_Cmat_apply (X : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ) (Xf : Spin → ℕ → ℕ → ℤ)
    (hX : ∀ j μ μ', X j μ μ' = Xf j μ.val μ'.val) (j : Spin) (k : Fin (dimF j)) (μ : Fin (multF j)) (w : Wd 6) :
    (blk dimF X * Cmat) ⟨j, (k, μ)⟩ w =
      ∑ m' ∈ range (mult j.val), Xf j μ.val m' * gt cArr ((rowNum ⟨j, (k, μ)⟩ - μ.val + m') * 64 + numOf w) := by
  rw [blk_mul_apply]
  obtain ⟨e1, e2, e3⟩ := rowSpin_rowNum ⟨j, (k, μ)⟩
  rw [← Fin.sum_univ_eq_sum_range (fun m' => Xf j μ.val m' *
    gt cArr ((rowNum ⟨j, (k, μ)⟩ - μ.val + m') * 64 + numOf w)) (mult j.val)]
  refine Finset.sum_congr rfl fun μ' _ => ?_
  have h2 : Cmat ⟨j, (k, μ')⟩ w = gt cArr (rowNum ⟨j, (k, μ')⟩ * 64 + numOf w) := rfl
  rw [hX, h2]
  congr 3
  unfold rowNum at e3 ⊢
  simp only at e3 ⊢
  omega

end QVCheck
