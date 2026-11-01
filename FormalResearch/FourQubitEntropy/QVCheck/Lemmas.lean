import Mathlib
import QVCheckImpl.Basic

/-!
# Semantics of the loop combinators of `QVCheck.Basic`

* `sumTo n f = ∑ i < n, f i`, `allTo n p = true ↔ ∀ i < n, p i = true`,
* `(tab n f).getD i 0 = if i < n then f i else 0`, `(tab n f).size = n`.
-/

open Finset

namespace QVCheck

theorem hide_eq (u : Unit) (n : Nat) : hide u n = n := rfl

theorem sumAux_eq (f : Nat → Int) (n : Nat) (acc : Int) :
    sumAux f n acc = acc + ∑ i ∈ range n, f i := by
  induction n generalizing acc with
  | zero => simp [sumAux]
  | succ k ih => rw [sumAux, ih, Finset.sum_range_succ]; ring

theorem sumTo_eq (n : Nat) (f : Nat → Int) : sumTo n f = ∑ i ∈ range n, f i := by
  simp [sumTo, sumAux_eq]

theorem allAux_iff (p : Nat → Bool) (n : Nat) : allAux p n = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allAux]
  | succ k ih =>
    rw [allAux, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · subst h; exact h1
    · intro h; exact ⟨h k (Nat.lt_succ_self k), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allTo_iff (n : Nat) (p : Nat → Bool) : allTo n p = true ↔ ∀ i < n, p i = true :=
  allAux_iff p n

theorem tabAux_eq (f : Nat → Int) (n : Nat) :
    ∀ (k : Nat), k ≤ n → ∀ (acc : Array Int),
      tabAux f n k acc = acc ++ ((List.range' (n - k) k).map f).toArray := by
  intro k
  induction k with
  | zero => intro _ acc; simp [tabAux]
  | succ k ih =>
    intro hk acc
    rw [tabAux, ih (by omega)]
    have h1 : n - (k + 1) + 1 = n - k := by omega
    have h2 : n - (k + 1) = n - 1 - k := by omega
    rw [List.range'_succ, h1, h2]
    simp

theorem tab_toList (n : Nat) (f : Nat → Int) : tab n f = ((List.range n).map f).toArray := by
  unfold tab
  rw [tabAux_eq f n n le_rfl]
  simp [List.range_eq_range']

theorem tab_size (n : Nat) (f : Nat → Int) : (tab n f).size = n := by
  rw [tab_toList]; simp

theorem tab_getD (n : Nat) (f : Nat → Int) (i : Nat) :
    (tab n f).getD i 0 = if i < n then f i else 0 := by
  rw [tab_toList]
  by_cases h : i < n
  · simp [h, Array.getD]
  · simp [h, Array.getD]

theorem gt_tab (n : Nat) (f : Nat → Int) (i : Nat) : gt (tab n f) i = if i < n then f i else 0 :=
  tab_getD n f i

end QVCheck
