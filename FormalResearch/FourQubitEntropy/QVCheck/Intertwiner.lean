module

public import FormalResearch.FourQubitEntropy.QVBlock.Blk
public import FormalResearch.FourQubitEntropy.QVCheck.Invariants
meta import QVCheckImpl.Impl1
public import FormalResearch.FourQubitEntropy.QVFrame.Basic
public import FormalResearch.FourQubitEntropy.QVFrame.Gram
public import FormalResearch.FourQubitEntropy.QVFrame.Twist

/-!
# The intertwiner `C`, the characters and the frame tables

The checker's `C`, `Cinv`, slot generators, character counts and `Ψ` tables as the `QVBlock` hypotheses `hCi`, `hiC`,
`hρ0`, `hw`, `hchar` and the per-covariant hypothesis `hX` for the twisted Gram operators (`hPsi_of_check`).
Facts relating the data array `cArr` to the Lean definition `QVCert.rowC` use `native_decide` (`cArr_rowC`, the only
`native_decide` besides `checkAll_true`).
-/

@[expose] public section


open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame
open scoped Matrix

namespace QVCheck

/-!
## The matrix `C` of the checker as the `QVBlock` hypotheses `hCi`, `hiC`, `hρ0`

`rowNum ⟨j, k, μ⟩ = off j + k * mult j + μ` identifies the per-qubit index `Idx dimF multF` with `Fin 64`; the column index is
`numOf w` (bit convention of `QVFrame.Basic`).
-/

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
  · subst hww; rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
  · have : numOf w ≠ numOf w' := fun e => hww (numOf_inj e)
    rw [ite_eq_right this, ite_eq_right hww, mul_zero]

theorem hiC_of_check (h : checkInv () = true) : Cmat * CinvMat = DataStr.cDen • (1 : Matrix IdxF IdxF ℤ) := by
  ext r r'
  have key : (Cmat * CinvMat) r r' = ∑ k ∈ range 64, gt cArr (rowNum r * 64 + k) * gt cinvArr (k * 64 + rowNum r') := by
    rw [Matrix.mul_apply]
    exact (Finset.sum_congr rfl fun w _ => rfl).trans
      (sum_wd (fun k => gt cArr (rowNum r * 64 + k) * gt cinvArr (k * 64 + rowNum r')))
  rw [key, (checkInv_spec h (rowNum r) (rowNum r') (by have := rowNum_lt r; omega) (by have := rowNum_lt r'; omega)).1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hrr : r = r'
  · subst hrr; rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
  · have : rowNum r ≠ rowNum r' := fun e => hrr (rowNum_inj e)
    rw [ite_eq_right this, ite_eq_right hrr, mul_zero]

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
      rw [blk_same, ite_eq_right (Ne.symm hk'), zero_mul, zero_mul]
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
    · rw [e, ite_eq_left rfl, mul_one]
    · intro a _ ha
      rw [e, ite_eq_right ha, mul_zero]
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

/-!
## `hchar`: the character count of the checker (`nn p`) as the hypothesis of `QVBlock.quad_eq_zero_of_int_certificate`
-/

/-- flat `m × m` array as a matrix -/
def ofMat (m : ℕ) (A : Array Int) : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun a b => gt A (a.val * m + b.val)

theorem gt_mmul (m : ℕ) (A B : Array Int) (a b : ℕ) (ha : a < m) (hb : b < m) :
    gt (mmul m A B) (a * m + b) = ∑ k ∈ range m, gt A (a * m + k) * gt B (k * m + b) := by
  unfold mmul
  have hlt : a * m + b < m * m := by nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  have hm : 0 < m := by omega
  have e1 : (a * m + b) / m = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt hb]; simp
  have e2 : (a * m + b) % m = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [e1, e2]

theorem ofMat_mmul (m : ℕ) (A B : Array Int) : ofMat m (mmul m A B) = ofMat m A * ofMat m B := by
  refine Matrix.ext fun a b => ?_
  have h1 : ofMat m (mmul m A B) a b = gt (mmul m A B) (a.val * m + b.val) := Matrix.of_apply _ _ _
  rw [h1, gt_mmul m A B a.val b.val a.2 b.2, Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range
    (fun k => gt A (a.val * m + k) * gt B (k * m + b.val)) m]
  rfl

theorem ofMat_idMat (m : ℕ) : ofMat m (idMat m) = 1 := by
  refine Matrix.ext fun a b => ?_
  have h1 : ofMat m (idMat m) a b = gt (idMat m) (a.val * m + b.val) := Matrix.of_apply _ _ _
  have hlt : a.val * m + b.val < m * m := by have := a.2; have := b.2; nlinarith
  have hm : 0 < m := by have := a.2; omega
  have e1 : (a.val * m + b.val) / m = a.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt b.2]; simp
  have e2 : (a.val * m + b.val) % m = b.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b.2]
  rw [h1]
  unfold idMat
  rw [gt_tab, ite_eq_left hlt, e1, e2, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · have : a.val ≠ b.val := fun e => hab (Fin.ext e)
    simp [hab, this]

theorem ofMat_genMat (j : Spin) (i : Fin 5) : ofMat (multF j) (genMat j.val i.val) = rho0 i j := by
  refine Matrix.ext fun a b => ?_
  have h1 : ofMat (multF j) (genMat j.val i.val) a b = gt (genMat j.val i.val) (a.val * multF j + b.val) :=
    Matrix.of_apply _ _ _
  rw [h1]
  exact genMat_apply j.val i.val a.val b.val a.2 b.2

theorem repProd_foldl (j : Spin) (l : List (Fin 5)) (A : Array Int) :
    ofMat (multF j) (l.foldl (fun acc i => mmul (mult j.val) acc (genMat j.val i.val)) A) =
      ofMat (multF j) A * (l.map (fun i => rho0 i j)).prod := by
  induction l generalizing A with
  | nil => simp
  | cons i t ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih]
    have : ofMat (multF j) (mmul (mult j.val) A (genMat j.val i.val)) = ofMat (multF j) A * rho0 i j := by
      rw [← ofMat_genMat j i]; exact ofMat_mmul (multF j) A _
    rw [this, Matrix.mul_assoc]


theorem ofMat_repProd (j : Spin) (l : List (Fin 5)) :
    ofMat (multF j) (repProd j.val (l.map Fin.val)) = (l.map (fun i => rho0 i j)).prod := by
  unfold repProd
  rw [List.foldl_map, repProd_foldl]
  have h : ofMat (multF j) (idMat (mult j.val)) = 1 := ofMat_idMat (multF j)
  rw [h, one_mul]

theorem trace_ofMat (m : ℕ) (A : Array Int) : (ofMat m A).trace = traceMat m A := by
  unfold traceMat
  rw [sumTo_eq, Matrix.trace, ← Fin.sum_univ_eq_sum_range (fun i => gt A (i * m + i)) m]
  rfl

/-- the words as lists of generators -/
def wordsF : List (List (Fin 5)) := words.map (List.map fun n => (⟨n % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5))

theorem wordsF_val : wordsF.map (List.map Fin.val) = words := by decide +kernel

theorem wordsF_length : wordsF.length = 720 := by decide +kernel

/-- `true` iff the keys are pairwise distinct (a bitmask of the keys seen so far: linear time in the kernel) -/
def distinctAux : List ℕ → ℕ → Bool
  | [], _ => true
  | k :: ks, m => !m.testBit k && distinctAux ks (m ||| 1 <<< k)

theorem distinctAux_spec : ∀ (L : List ℕ) (m : ℕ), distinctAux L m = true →
    L.Nodup ∧ ∀ k ∈ L, m.testBit k = false
  | [], m, _ => ⟨List.nodup_nil, by simp⟩
  | k :: ks, m, h => by
    simp only [distinctAux, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hk, h2⟩ := h
    obtain ⟨hnd, hmask⟩ := distinctAux_spec ks _ h2
    refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, hnd⟩, ?_⟩
    · have := hmask k hmem
      simp [Nat.testBit_or, Nat.testBit_shiftLeft] at this
    · intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hk
      · have := hmask j hj
        simp [Nat.testBit_or, Nat.testBit_shiftLeft] at this
        exact this.1

/-- the image of a permutation of `Fin 6` as a number in base `6` -/
def permKey (g : Equiv.Perm (Fin 6)) : ℕ := (List.finRange 6).foldl (fun acc i => acc * 6 + (g i).val) 0

theorem wordsF_nodup : (wordsF.map fun l => (l.map gens).prod).Nodup := by
  have h : distinctAux ((wordsF.map fun l => (l.map gens).prod).map permKey) 0 = true := by decide +kernel
  exact List.Nodup.of_map _ (distinctAux_spec _ _ h).1


/-- the word of a permutation: the first listed word with that product -/
def wF (g : Equiv.Perm (Fin 6)) : List (Fin 5) :=
  (wordsF.find? fun l => decide ((l.map gens).prod = g)).getD []

theorem card_perm6 : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Fintype.card_perm, Fintype.card_fin]; rfl

theorem phi_surj : ∀ g : Equiv.Perm (Fin 6), ∃ l ∈ wordsF, (l.map gens).prod = g := by
  have hcard : (wordsF.map fun l => (l.map gens).prod).toFinset.card = Fintype.card (Equiv.Perm (Fin 6)) := by
    rw [List.toFinset_card_of_nodup wordsF_nodup, List.length_map, wordsF_length, card_perm6]
  have huniv := Finset.eq_univ_of_card _ hcard
  intro g
  have : g ∈ (wordsF.map fun l => (l.map gens).prod).toFinset := by rw [huniv]; exact Finset.mem_univ g
  simpa using this

theorem wF_spec (g : Equiv.Perm (Fin 6)) : wF g ∈ wordsF ∧ ((wF g).map gens).prod = g := by
  obtain ⟨l, hl, hg⟩ := phi_surj g
  have hs : (wordsF.find? fun l => decide ((l.map gens).prod = g)).isSome := by
    rw [List.find?_isSome]; exact ⟨l, hl, by simpa using hg⟩
  obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 hs
  unfold wF
  rw [hl']
  simp only [Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some hl', by simpa using List.find?_some hl'⟩

theorem hw_of (g : Equiv.Perm (Fin 6)) : ((wF g).map gens).prod = g := (wF_spec g).2

theorem wF_phi (l : List (Fin 5)) (hl : l ∈ wordsF) : wF ((l.map gens).prod) = l := by
  obtain ⟨h1, h2⟩ := wF_spec ((l.map gens).prod)
  exact List.inj_on_of_nodup_map wordsF_nodup h1 hl h2

theorem sum_perm_words (F : List (Fin 5) → ℤ) : ∑ g : Equiv.Perm (Fin 6), F (wF g) = (wordsF.map F).sum := by
  have hnd : wordsF.Nodup := List.Nodup.of_map _ wordsF_nodup
  rw [← List.sum_toFinset F hnd]
  refine Finset.sum_bij (fun g _ => wF g) (fun g _ => List.mem_toFinset.2 (wF_spec g).1) ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ h
    rw [← hw_of a, ← hw_of b, h]
  · intro l hl
    have hl' := List.mem_toFinset.1 hl
    exact ⟨(l.map gens).prod, Finset.mem_univ _, wF_phi l hl'⟩


theorem sum_range_getD {α : Type*} (L : List α) (f : α → ℤ) (d : α) :
    ∑ i ∈ range L.length, f (L.getD i d) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih]; ring

theorem charArr_apply (j : Spin) (w : ℕ) (hw : w < 720) :
    gt charArr (j.val * 720 + w) = traceMat (mult j.val) (repProd j.val (words.getD w [])) := by
  unfold charArr
  have hj := j.2
  have hlt : j.val * 720 + w < 2880 := by omega
  rw [gt_tab, ite_eq_left hlt]
  have e1 : (j.val * 720 + w) / 720 = j.val := by omega
  have e2 : (j.val * 720 + w) % 720 = w := by omega
  rw [e1, e2]

theorem checkChars_spec (h : checkChars () = true) (code : ℕ) (hc : code < 256) :
    charSum code = 720 * ((nnArr.getD code 0 : ℕ) : ℤ) := by
  unfold checkChars at h
  have := (allTo_iff _ _).1 h code (by rw [hide_eq]; exact hc)
  simpa using this

theorem getD_wordsF (w : ℕ) (hw : w < 720) :
    words.getD w [] = (wordsF.getD w []).map Fin.val := by
  have hl : w < wordsF.length := by rw [wordsF_length]; exact hw
  have := congrArg (fun L => L.getD w []) wordsF_val
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
  rw [← this]
  cases hh : wordsF[w]? <;> simp

theorem hchar_of_check (h : checkChars () = true) (p : Fin 4 → Spin) :
    (Fintype.card (Equiv.Perm (Fin 6)) : ℤ) * (nnF p : ℤ) =
      ∑ g : Equiv.Perm (Fin 6), ∏ q, (((wF g).map (fun i => rho0 i (p q))).prod).trace := by
  rw [card_perm6]
  rw [sum_perm_words (fun l => ∏ q, ((l.map (fun i => rho0 i (p q))).prod).trace)]
  have hc := checkChars_spec h (pcode p) (pcode_lt p)
  have hn : nn (pcode p) = nnArr.getD (pcode p) 0 := rfl
  have e1 : (720 : ℤ) * (nnF p : ℤ) = charSum (pcode p) := by
    rw [hc]; rfl
  push_cast
  rw [e1]
  unfold charSum
  rw [sumTo_eq]
  rw [← wordsF_length, ← sum_range_getD wordsF _ []]
  rw [wordsF_length]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' := Finset.mem_range.1 hw
  have hfold : ∀ f : ℕ → ℤ, (List.range 4).foldl (fun acc q => acc * f q) 1 = ∏ q : Fin 4, f q.val := by
    intro f
    have hr : List.range 4 = [0, 1, 2, 3] := rfl
    rw [hr]; simp [Fin.prod_univ_four]
  rw [hfold (fun q => gt charArr (spinDigit (pcode p) q * 720 + w))]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [spinDigit_pcode p q, charArr_apply (p q) w hw', getD_wordsF w hw', ← trace_ofMat]
  exact congrArg Matrix.trace (ofMat_repProd (p q) (wordsF.getD w []))

/-!
## The frame tables `Ψ`: `hX` for the twisted covariant atoms

`C τ_a(E^j_{μμ'}) = Blk(Ψ^{(a)}_{j,·}[μ][μ']) C` for `a ∈ {3, 4}` (`hPsi_of_check`, from `checkPsi`); `cArr_rowC` identifies the checker's
rows of `C` with `QVCert.rowC` and `weight_omega` its weights `ω` with `QVCert.weight`.
-/

/-- the checker's `C` rows are the six-copy intertwiner `rowC` of `QVCert` -/
theorem cArr_rowC : ∀ j < 4, ∀ k ≤ 2 * j, ∀ μ < mult j, ∀ w < 64,
    gt cArr ((off j + k * mult j + μ) * 64 + w) = QVCert.rowC (2 * j) k μ w := by
  native_decide


theorem weight_omega : ∀ j < 4, ∀ k ≤ 2 * j, (QVCert.weight (2 * j) k : ℤ) = omegaT j k := by
  decide +kernel

theorem numOf_revW : ∀ α : Wd 6, numOf (revW α) = 63 - numOf α := by decide +kernel

theorem numOf_mixW : ∀ a ∈ ({3, 4} : Finset ℕ), ∀ u v : Wd 6, numOf (mixW a u v) = mixIdx a (numOf u) (numOf v) := by
  decide +kernel

theorem tauSgn_eq : ∀ a ∈ ({3, 4} : Finset ℕ), ∀ α β : Wd 6,
    tauSgn a α β = if (popPar (numOf α &&& ((1 <<< (6 - a)) - 1)) + popPar (numOf β &&& ((1 <<< (6 - a)) - 1))) % 2 = 0
      then 1 else -1 := by
  decide +kernel


theorem gt_eMat (j mu mup : ℕ) (β α : ℕ) (hβ : β < 64) (hα : α < 64) :
    gt (eMat j mu mup) (β * 64 + α) =
      ∑ k ∈ range (2 * j + 1), omegaT j k * gt cArr ((off j + k * mult j + mu) * 64 + β) *
        gt cArr ((off j + k * mult j + mup) * 64 + α) := by
  unfold eMat
  rw [gt_tab, ite_eq_left (by omega), sumTo_eq]
  have e1 : (β * 64 + α) / 64 = β := by omega
  have e2 : (β * 64 + α) % 64 = α := by omega
  rw [e1, e2]

theorem Eop_entry (jx : Spin) (mu mup : ℕ) (hmu : mu < mult jx.val) (hmup : mup < mult jx.val) (w w' : Wd 6) :
    Eop (2 * jx.val) mu mup w w' = gt (eMat jx.val mu mup) (numOf w * 64 + numOf w') := by
  rw [gt_eMat _ _ _ _ _ (numOf_lt64 w) (numOf_lt64 w')]
  have h2 : 2 * jx.val + 1 = (2 * jx.val) + 1 := rfl
  show ∑ m ∈ range (2 * jx.val + 1), (QVCert.weight (2 * jx.val) m : ℤ) * rowW (2 * jx.val) m mu w *
      rowW (2 * jx.val) m mup w' = _
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ 2 * jx.val := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hj := jx.2
  rw [weight_omega jx.val hj m hm']
  have e1 := cArr_rowC jx.val hj m hm' mu hmu (numOf w) (numOf_lt64 w)
  have e2 := cArr_rowC jx.val hj m hm' mup hmup (numOf w') (numOf_lt64 w')
  unfold rowW
  rw [← e1, ← e2]


theorem tau_Eop_entry (a : ℕ) (ha : a ∈ ({3, 4} : Finset ℕ)) (jx : Spin) (mu mup : ℕ) (hmu : mu < mult jx.val)
    (hmup : mup < mult jx.val) (β α : Wd 6) :
    tau a (Eop (2 * jx.val) mu mup) β α = gt (tauMat a (eMat jx.val mu mup)) (numOf β * 64 + numOf α) := by
  rw [tau_apply, Eop_entry jx mu mup hmu hmup, tauSgn_eq a ha]
  unfold tauMat
  have hlt : numOf β * 64 + numOf α < 4096 := by have := numOf_lt64 β; have := numOf_lt64 α; omega
  rw [gt_tab, ite_eq_left hlt]
  have e1 : (numOf β * 64 + numOf α) / 64 = numOf β := by have := numOf_lt64 α; omega
  have e2 : (numOf β * 64 + numOf α) % 64 = numOf α := by have := numOf_lt64 α; omega
  simp only [e1, e2]
  rw [numOf_mixW a ha, numOf_mixW a ha, numOf_revW, numOf_revW]
  have hb := numOf_lt64 β
  have hα := numOf_lt64 α
  generalize popPar (numOf α &&& 1 <<< (6 - a) - 1) + popPar (numOf β &&& 1 <<< (6 - a) - 1) = S
  by_cases hc : S % 2 = 0
  · simp [hc]
  · simp [hc]


/-- the block of `Ψ` as a matrix -/
def psiMat (a : ℕ) (jx j' : Spin) (mu mup : ℕ) : Matrix (Fin (multF j')) (Fin (multF j')) ℤ :=
  Matrix.of fun ν ν' => psiAt (a - 3) jx.val j'.val mu mup ν.val ν'.val

theorem checkPsiOne_spec (h : checkPsi () = true) (ai : ℕ) (hai : ai < 2) (j mu mup : ℕ) (hj : j < 4)
    (hmu : mu < mult j) (hmup : mup < mult j) : checkPsiOne ai j mu mup = true := by
  unfold checkPsi at h
  have h1 := (allTo_iff _ _).1 h ai (by rw [hide_eq]; exact hai)
  have h2 := (allTo_iff _ _).1 h1 j hj
  have h3 := (allTo_iff _ _).1 h2 mu hmu
  exact (allTo_iff _ _).1 h3 mup hmup


theorem hPsi_of_check (h : checkPsi () = true) (a : ℕ) (ha : a ∈ ({3, 4} : Finset ℕ)) (jx : Spin) (mu mup : ℕ)
    (hmu : mu < mult jx.val) (hmup : mup < mult jx.val) :
    Cmat * tau a (Eop (2 * jx.val) mu mup) = blk dimF (fun j' => psiMat a jx j' mu mup) * Cmat := by
  refine Matrix.ext fun r w => ?_
  obtain ⟨j, k, ν⟩ := r
  rw [blk_Cmat_apply (fun j' => psiMat a jx j' mu mup) (fun j' ν ν' => psiAt (a - 3) jx.val j'.val mu mup ν ν') (fun _ _ _ => rfl)]
  have hai : a - 3 < 2 := by simp at ha; omega
  have hspec := checkPsiOne_spec h (a - 3) hai jx.val mu mup jx.2 hmu hmup
  have ha3 : 3 + (a - 3) = a := by simp at ha; omega
  unfold checkPsiOne at hspec
  rw [ha3] at hspec
  have hr := rowNum_lt ⟨j, (k, ν)⟩
  have h1 := (allTo_iff _ _).1 hspec (rowNum ⟨j, (k, ν)⟩) hr
  have h2 := (allTo_iff _ _).1 h1 (numOf w) (numOf_lt64 w)
  simp only [beq_iff_eq, sumTo_eq] at h2
  obtain ⟨e1, e2, e3⟩ := rowSpin_rowNum ⟨j, (k, ν)⟩
  rw [e1, e2] at h2
  have hL : (Cmat * tau a (Eop (2 * jx.val) mu mup)) ⟨j, (k, ν)⟩ w =
      ∑ x ∈ range 64, gt cArr (rowNum ⟨j, (k, ν)⟩ * 64 + x) *
        gt (tauMat a (eMat jx.val mu mup)) (x * 64 + numOf w) := by
    rw [Matrix.mul_apply]
    refine (Finset.sum_congr rfl fun w' _ => ?_).trans
      (sum_wd (fun x => gt cArr (rowNum ⟨j, (k, ν)⟩ * 64 + x) * gt (tauMat a (eMat jx.val mu mup)) (x * 64 + numOf w)))
    rw [tau_Eop_entry a ha jx mu mup hmu hmup]
    rfl
  rw [hL, h2]

end QVCheck
