import FormalResearch.FourQubitEntropy.PurityLPShadow
import FormalResearch.FourQubitEntropy.PurityLPDefs

/-!
# The Rains-LP dual certificate lemma (Stage 3)

Source: `ResearchNotes/QI/seven_qubit_entanglement/even_qubit_purity_minima.tex`, proof of `thm:lptable`(1),
`thm:fourteenfifteen`, `thm:sixteenseventeen`, `balanced_purity_18.tex` `thm:eighteen`.

A *certificate* for `n` is `(L, es, ys)` with `es = [(s, e_s)]` (`e_s ∈ ℚ`, `s ≤ n`) and `ys = [(i, y_i)]`
(`y_i ≥ 0`).  Its *residual* is the linear form `w` in `A` with
`a_k - L A_0 - Σ_s e_s (a_s - a_{n-s}) - Σ_i y_i S_i = Σ_j w_j A_j`, `k = ⌊n/2⌋`; `wCoef` computes `w_j` exactly in
`ℚ` from the true coefficient functions `aQ` (`eq:as`) and `shQ` (the shadow coefficients).  `lpCheck` is the
decidable test `y_i ≥ 0 ∧ w_j ≥ 0 ∀ j ≤ n`.

* `lp_bound`: if `lpCheck n L es ys = true` then **for every unit vector `ψ` of `n` qubits `L ≤ π_k(ψ)`**
  (`SpinFlip.purMean`; `piMean_eq_purMean` identifies it with the mean of the `tr ρ_S²`), using only the proved
  facts `A_0 = 1`, `A_j ≥ 0` (`SpinFlip.A_nonneg`), `a_s = a_{n-s}` (`purMean_compl`) and the shadow inequalities
  (`shadow_nonneg`).  Claim class: proved.
-/

open scoped BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FourQubitEntropy.SpinFlip

/-- The linear form `A ↦ Σ_{j ≤ n} c_j A_j`. -/
def lin (n : ℕ) (A : ℕ → ℝ) (c : ℕ → ℚ) : ℝ := ∑ j ∈ Finset.range (n + 1), (c j : ℝ) * A j

theorem lin_sub (n : ℕ) (A : ℕ → ℝ) (c₁ c₂ : ℕ → ℚ) :
    lin n A (fun j => c₁ j - c₂ j) = lin n A c₁ - lin n A c₂ := by
  unfold lin
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem lin_add (n : ℕ) (A : ℕ → ℝ) (c₁ c₂ : ℕ → ℚ) :
    lin n A (fun j => c₁ j + c₂ j) = lin n A c₁ + lin n A c₂ := by
  unfold lin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem lin_zero (n : ℕ) (A : ℕ → ℝ) : lin n A (fun _ => 0) = 0 := by simp [lin]

theorem lin_mul (n : ℕ) (A : ℕ → ℝ) (r : ℚ) (c : ℕ → ℚ) :
    lin n A (fun j => r * c j) = r * lin n A c := by
  unfold lin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

theorem lin_list (n : ℕ) (A : ℕ → ℝ) (F : ℕ → ℕ → ℚ) (l : List (ℕ × ℚ)) :
    lin n A (fun j => (l.map fun p => p.2 * F p.1 j).sum)
      = (l.map fun p => (p.2 : ℝ) * lin n A (F p.1)).sum := by
  induction l with
  | nil => simp [lin]
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [lin_add, lin_mul, ih]

theorem lin_ind (n : ℕ) (A : ℕ → ℝ) (L : ℚ) :
    lin n A (fun j => if j = 0 then L else 0) = L * A 0 := by
  unfold lin
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; simp at h

/-- The residual coefficient `w_j` of a certificate. -/
def wCoef (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) (j : ℕ) : ℚ :=
  aQ n (n / 2) j - (if j = 0 then L else 0)
    - (es.map fun p => p.2 * (aQ n p.1 j - aQ n (n - p.1) j)).sum
    - (ys.map fun p => p.2 * shQ n p.1 j).sum

/-- The decidable check of a certificate. -/
def lpCheck (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) : Bool :=
  es.all (fun p => decide (p.1 ≤ n)) && ys.all (fun p => decide (0 ≤ p.2)) &&
    (List.range (n + 1)).all fun j => decide (0 ≤ wCoef n L es ys j)

theorem lin_wCoef (n : ℕ) (A : ℕ → ℝ) (L : ℚ) (es ys : List (ℕ × ℚ)) :
    lin n A (wCoef n L es ys)
      = lin n A (aQ n (n / 2)) - L * A 0
        - (es.map fun p => (p.2 : ℝ) * (lin n A (aQ n p.1) - lin n A (aQ n (n - p.1)))).sum
        - (ys.map fun p => (p.2 : ℝ) * lin n A (shQ n p.1)).sum := by
  unfold wCoef
  rw [lin_sub, lin_sub, lin_sub, lin_ind]
  have h1 := lin_list n A (fun s j => aQ n s j - aQ n (n - s) j) es
  have h2 := lin_list n A (shQ n) ys
  simp only [lin_sub] at h1
  rw [h1, h2]

/-- **The LP step.** A passing certificate bounds the mean balanced purity of every unit `n`-qubit vector. -/
theorem lp_bound (n : ℕ) (L : ℚ) (es ys : List (ℕ × ℚ)) (h : lpCheck n L es ys = true)
    (ψ : Ψ n) (hψ : nsq ψ = 1) : (L : ℝ) ≤ purMean ψ (n / 2) := by
  simp only [lpCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨hes, hys⟩, hw⟩ := h
  set A' : ℕ → ℝ := fun j => A ψ j with hA'
  have hk : n / 2 ≤ n := Nat.div_le_self n 2
  have hlin : ∀ s, s ≤ n → lin n A' (aQ n s) = purMean ψ s := fun s hs =>
    (purMean_eq_lin ψ hs).symm
  have hw' : 0 ≤ lin n A' (wCoef n L es ys) := by
    unfold lin
    refine Finset.sum_nonneg fun j hj => mul_nonneg ?_ (A_nonneg ψ j)
    exact_mod_cast hw j (Finset.mem_range.mp hj)
  rw [lin_wCoef] at hw'
  have hes0 : (es.map fun p => (p.2 : ℝ) * (lin n A' (aQ n p.1) - lin n A' (aQ n (n - p.1)))).sum
      = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hp1 := hes p hp
    rw [hlin p.1 hp1, hlin (n - p.1) (Nat.sub_le _ _), purMean_compl ψ hp1]
    ring
  have hys0 : 0 ≤ (ys.map fun p => (p.2 : ℝ) * lin n A' (shQ n p.1)).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have : lin n A' (shQ n p.1) = shadowCoeff ψ p.1 := by
      rw [shadowCoeff_eq_lin]; rfl
    rw [this]
    exact mul_nonneg (by exact_mod_cast hys p hp) (shadow_nonneg ψ p.1)
  rw [hes0, hlin (n / 2) hk] at hw'
  have hA0 : A' 0 = 1 := A_zero ψ hψ
  rw [hA0] at hw'
  linarith

end FormalResearch.FourQubitEntropy.PurityLP
