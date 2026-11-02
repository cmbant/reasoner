import FormalResearch.FourQubitEntropy.QVCheck.Sector

/-!
# K7: the final comparison, semantically
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem foldl_add_range (f : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp

theorem dvd_lcmAll_aux (xs : List ℕ) (a : ℕ) : a ∣ xs.foldl Nat.lcm a := by
  induction xs generalizing a with
  | nil => exact dvd_rfl
  | cons x t ih => exact (Nat.dvd_lcm_left a x).trans (ih _)

theorem dvd_lcmAll (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x ∣ lcmAll xs := by
  unfold lcmAll
  induction xs generalizing x with
  | nil => simp at hx
  | cons y t ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | h
    · exact (Nat.dvd_lcm_right 1 x).trans (dvd_lcmAll_aux t _)
    · -- fold starting from lcm 1 y
      have : ∀ (t : List ℕ) (a : ℕ) (x : ℕ), x ∈ t → x ∣ t.foldl Nat.lcm a := by
        intro t
        induction t with
        | nil => intro a x hx; simp at hx
        | cons y t ih2 =>
          intro a x hx
          rw [List.foldl_cons]
          rcases List.mem_cons.1 hx with rfl | h
          · exact (Nat.dvd_lcm_right a x).trans (dvd_lcmAll_aux t _)
          · exact ih2 _ _ h
      exact this t _ x h

theorem lcmAll_ne_zero_aux (xs : List ℕ) (a : ℕ) (ha : a ≠ 0) (hx : ∀ x ∈ xs, x ≠ 0) : xs.foldl Nat.lcm a ≠ 0 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x t ih =>
    rw [List.foldl_cons]
    exact ih _ (Nat.lcm_ne_zero ha (hx x (List.mem_cons_self))) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem lcmAll_ne_zero (xs : List ℕ) (hx : ∀ x ∈ xs, x ≠ 0) : lcmAll xs ≠ 0 :=
  lcmAll_ne_zero_aux xs 1 one_ne_zero hx

/-- K7, semantically: for every sector and basis pair the right-hand side coordinate equals the sum over the
`24` placements of the `Q`-coordinates, transported to the sector by the placement matrices. -/
theorem checkFinal_spec (rhs : Array RhsTerm) (Q : Array (Array Int)) (Dnum : Int)
    (hok : checkFinal rhs Q Dnum = true) (hP : checkPlacements () = true)
    (p : Fin 4 → Spin) (hn : 0 < nn (pcode p)) (A B : ℕ) (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    ∃ Dn : ℤ, Dn ≠ 0 ∧ (∀ pii : Fin 24, pden (pcode p) pii.val * pden (pcode p) pii.val ∣ Dn) ∧
      Dn * 2 * Dnum * gt (rhsCoords rhs (pcode p)) (A * nn (pcode p) + B) =
        ∑ pii : Fin 24, (Dn / (pden (pcode p) pii.val * pden (pcode p) pii.val)) *
          ∑ A' ∈ range (nn (pcode p)), ∑ B' ∈ range (nn (pcode p)),
            pSW (pcode p) pii.val A A' *
              gt (Q.getD (pcode (fun r => p (sg pii r))) #[]) (A' * nn (pcode p) + B') *
              pSV (pcode p) pii.val B B' := by
  unfold checkFinal at hok
  have h1 := (allTo_iff _ _).1 hok (pcode p) (pcode_lt p)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · omega
  have hlt : A * nn (pcode p) + B < nn (pcode p) * nn (pcode p) := by nlinarith
  have h2 := (allTo_iff _ _).1 h1 (A * nn (pcode p) + B) hlt
  simp only [beq_iff_eq] at h2
  obtain ⟨d1, d2⟩ := div_mod_aux A B (nn (pcode p)) hB
  simp only [d1, d2] at h2
  rw [foldl_add_range] at h2
  have hpd : ∀ pii : Fin 24, pden (pcode p) pii.val ≠ 0 := fun pii =>
    (checkPlacements_spec hP p pii hn).2.1
  refine ⟨(lcmAll ((List.range 24).map fun pii => (pden (pcode p) pii * pden (pcode p) pii).toNat) : ℤ), ?_, ?_, ?_⟩
  · have := lcmAll_ne_zero ((List.range 24).map fun pii => (pden (pcode p) pii * pden (pcode p) pii).toNat) ?_
    · exact_mod_cast this
    · intro x hx
      obtain ⟨pii, hpii, rfl⟩ := List.mem_map.1 hx
      have := hpd ⟨pii, List.mem_range.1 hpii⟩
      have h3 : pden (pcode p) pii * pden (pcode p) pii ≠ 0 := mul_ne_zero this this
      have h4 : 0 ≤ pden (pcode p) pii * pden (pcode p) pii := mul_self_nonneg _
      omega
  · intro pii
    have h4 : 0 ≤ pden (pcode p) pii.val * pden (pcode p) pii.val := mul_self_nonneg _
    have h5 := dvd_lcmAll ((List.range 24).map fun pii => (pden (pcode p) pii * pden (pcode p) pii).toNat)
      (pden (pcode p) pii.val * pden (pcode p) pii.val).toNat
      (List.mem_map.2 ⟨pii.val, List.mem_range.2 pii.2, rfl⟩)
    have h6 := Int.natCast_dvd_natCast.2 h5
    rwa [Int.toNat_of_nonneg h4] at h6
  · simp only [sumTo_eq] at h2
    rw [Finset.sum_range] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun pii _ => ?_
    rw [placed_eq]

end QVCheck
