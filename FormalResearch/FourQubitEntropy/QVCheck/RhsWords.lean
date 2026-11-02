import FormalResearch.FourQubitEntropy.QVCheck.Bridge
import FormalResearch.FourQubitEntropy.QVFrame.Defect

/-!
# Words for the right-hand side permutations
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

def bubbleStep (st : List ℕ × List (Fin 5)) (i : Fin 5) : List ℕ × List (Fin 5) :=
  if st.1.getD (i.val + 1) 0 < st.1.getD i.val 0 then
    ((st.1.set i.val (st.1.getD (i.val + 1) 0)).set (i.val + 1) (st.1.getD i.val 0), i :: st.2)
  else st

def bubblePass (st : List ℕ × List (Fin 5)) : List ℕ × List (Fin 5) := (List.finRange 5).foldl bubbleStep st

/-- a word in the adjacent transpositions for the permutation with image list `l` (bubble sort) -/
def bubbleWord (l : List ℕ) : List (Fin 5) := ((List.range 6).foldl (fun st _ => bubblePass st) (l, [])).2

def wordOf (π : Equiv.Perm (Fin 6)) : List (Fin 5) := bubbleWord ((List.finRange 6).map fun t => (π t).val)

theorem wordOf_spec : ∀ i : RhsIdx, ∀ q : Fin 4, ((wordOf (rhsPerm i q)).map gens).prod = rhsPerm i q := by
  native_decide

def rhsIdxList : List RhsIdx :=
  (List.finRange 7).flatMap fun a => (List.finRange 3).flatMap fun b => (List.finRange 3).map fun c => (a, b, c)

/-- the right-hand-side term of an index: coefficient and one word per qubit -/
def rhsTermOf (i : RhsIdx) : RhsTerm :=
  (rhsCoef i, ((List.finRange 4).map fun q => (wordOf (rhsPerm i q)).map Fin.val).toArray)

/-- the terms handed to the checker -/
def rhsTermsQ : Array RhsTerm := (rhsIdxList.map rhsTermOf).toArray

theorem sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (h : β → ℤ) :
    ((L.flatMap g).map h).sum = (L.map fun a => ((g a).map h).sum).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem sum_rhsIdxList (h : RhsIdx → ℤ) : (rhsIdxList.map h).sum = ∑ i : RhsIdx, h i := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_def]
  unfold rhsIdxList
  rw [sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  rw [Fintype.sum_prod_type, Fin.sum_univ_def, sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  rw [Fin.sum_univ_def, List.map_map]
  rfl

theorem slotPermZ_apply (π : Equiv.Perm (Fin 6)) (a c : Wd 6) :
    (slotPerm ℤ π : Matrix (Wd 6) (Wd 6) ℤ) a c = if a = slotAct π c then 1 else 0 := rfl

theorem slotPermZ_mul (π τ : Equiv.Perm (Fin 6)) :
    (slotPerm ℤ (π * τ) : Matrix (Wd 6) (Wd 6) ℤ) = (slotPerm ℤ π * slotPerm ℤ τ : Matrix (Wd 6) (Wd 6) ℤ) := by
  ext a c
  simp only [slotPermZ_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (slotAct τ c)]
  · have : slotAct (π * τ) c = slotAct π (slotAct τ c) := rfl
    simp [this]
  · intro b _ hb
    simp [hb]
  · simp

theorem slotPermZ_one : (slotPerm ℤ (1 : Equiv.Perm (Fin 6)) : Matrix (Wd 6) (Wd 6) ℤ) = 1 := by
  ext a c
  have h : slotAct (1 : Equiv.Perm (Fin 6)) c = c := rfl
  simp [slotPermZ_apply, h, Matrix.one_apply]

theorem blk_word (hS : checkSlots () = true) (l : List (Fin 5)) :
    Cmat * (slotPerm ℤ ((l.map gens).prod) : Matrix (Wd 6) (Wd 6) ℤ) =
      blk dimF ((l.map fun i => (fun j => rho0 i j : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)).prod) * Cmat := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [slotPermZ_one, blk_one, Matrix.mul_one, Matrix.one_mul]
  | cons i t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [slotPermZ_mul, ← Matrix.mul_assoc, hrho0_of_check hS i, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      ← blk_mul]

theorem blk_word_apply (l : List (Fin 5)) (j : Spin) :
    ((l.map fun i => (fun j => rho0 i j : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)).prod) j =
      (l.map fun i => rho0 i j).prod := by
  rw [Pi.list_prod_apply, List.map_map]
  rfl

theorem rhsKron_term (p : Fin 4 → Spin) (i : RhsIdx) :
    rhsKron p (rhsTermOf i) = kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod) := by
  unfold rhsKron
  refine congrArg kronPi (funext fun q => ?_)
  have : (rhsTermOf i).2.getD q.val [] = (wordOf (rhsPerm i q)).map Fin.val := by
    unfold rhsTermOf
    simp [Array.getD, List.getElem?_map]
  rw [this, ofMat_repProd]

theorem rhs_sum (p : Fin 4 → Spin) (A B : ℕ) :
    ∑ ti ∈ range rhsTermsQ.size, (rhsTermsQ.getD ti default).1 * bilN p (rhsKron p (rhsTermsQ.getD ti default)) A B =
      ∑ i : RhsIdx, rhsCoef i * bilN p (kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod)) A B := by
  unfold rhsTermsQ
  rw [arr_sum rhsIdxList rhsTermOf (fun t => t.1 * bilN p (rhsKron p t) A B) default, sum_rhsIdxList]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rhsKron_term]
  rfl

end QVCheck
