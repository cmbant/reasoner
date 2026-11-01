import FormalResearch.FourQubitEntropy.QVCheck.CBlock
import FormalResearch.FourQubitEntropy.QVCheck.HypVW

/-!
# `hchar`: the character count of the checker (`nn p`) as the hypothesis of `QVBlock.quad_eq_zero_of_int_certificate`
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- flat `m × m` array as a matrix -/
def ofMat (m : ℕ) (A : Array Int) : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun a b => gt A (a.val * m + b.val)

theorem gt_mmul (m : ℕ) (A B : Array Int) (a b : ℕ) (ha : a < m) (hb : b < m) :
    gt (mmul m A B) (a * m + b) = ∑ k ∈ range m, gt A (a * m + k) * gt B (k * m + b) := by
  unfold mmul
  have hlt : a * m + b < m * m := by nlinarith
  rw [gt_tab, if_pos hlt, sumTo_eq]
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
  rw [gt_tab, if_pos hlt, e1, e2, Matrix.one_apply]
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

theorem wordsF_val : wordsF.map (List.map Fin.val) = words := by
  native_decide

theorem wordsF_length : wordsF.length = 720 := by native_decide

theorem wordsF_nodup : (wordsF.map fun l => (l.map gens).prod).Nodup := by
  native_decide


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
  rw [gt_tab, if_pos hlt]
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

end QVCheck
