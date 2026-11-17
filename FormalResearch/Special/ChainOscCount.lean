module

public import FormalResearch.Jacobi.Oscillation

/-!
# Chain oscillation, part 1: counting zeros of interlacing families

Pure counting lemmas used by the nodal (sign-change) form of Sturm oscillation for Jacobi
eigenvectors, `FormalResearch.Special.ChainOscNodal`.

* `cho_cnt f n x` : the number of `i < n` with `x < f i`.
* `cho_count_step` : if `θ_0 < μ_0 < θ_1 < ⋯ < μ_{j-1} < θ_j` (`Interlaces j μ θ`), then for every real
  `x`, with `C_θ = #{i ≤ j : x < θ_i}` and `C_μ = #{i < j : x < μ_i}`:
  `C_μ ≤ C_θ ≤ C_μ + 1`; if `x` is one of the `μ_i` then `C_θ = C_μ + 1`; if `x` is one of the `θ_i`
  then `C_θ = C_μ`.
* `cho_sign_prod` : `0 < (-1)^{#{i : x < μ_i}} ∏ (x - μ_i)` when `x` is not one of the `μ_i`.

Claim class: proved (elementary).  Not formalised: nothing beyond the statements above.
-/

@[expose] public section

namespace FormalResearch.Special

open FormalResearch.Jacobi Finset Polynomial

theorem cho_if_pos {α : Type*} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := by simp [h]

theorem cho_if_neg {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := by simp [h]

/-- `#{i < n : x < f i}`. -/
noncomputable def cho_cnt (f : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℕ := ((range n).filter (fun i => x < f i)).card

theorem cho_cnt_zero (f : ℕ → ℝ) (x : ℝ) : cho_cnt f 0 x = 0 := by simp [cho_cnt]

theorem cho_cnt_succ (f : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    cho_cnt f (n + 1) x = cho_cnt f n x + if x < f n then 1 else 0 := by
  unfold cho_cnt
  rw [Finset.range_add_one, filter_insert]
  by_cases h : x < f n
  · rw [cho_if_pos h, cho_if_pos h, card_insert_of_notMem (by simp)]
  · rw [cho_if_neg h, cho_if_neg h]; simp

theorem cho_cnt_eq_zero {f : ℕ → ℝ} {n : ℕ} {x : ℝ} (h : ∀ i, i < n → f i ≤ x) :
    cho_cnt f n x = 0 := by
  unfold cho_cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i hi
  exact not_lt.mpr (h i (mem_range.mp hi))

theorem cho_count_step {μ θ : ℕ → ℝ} (x : ℝ) :
    ∀ j : ℕ, Interlaces j μ θ →
      cho_cnt μ j x ≤ cho_cnt θ (j + 1) x ∧ cho_cnt θ (j + 1) x ≤ cho_cnt μ j x + 1 ∧
      ((∃ i, i < j ∧ μ i = x) → cho_cnt θ (j + 1) x = cho_cnt μ j x + 1) ∧
      ((∃ i, i < j + 1 ∧ θ i = x) → cho_cnt θ (j + 1) x = cho_cnt μ j x) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [cho_cnt_zero]
    · rw [cho_cnt_succ, cho_cnt_zero, cho_cnt_zero]; split_ifs <;> simp
    · rintro ⟨i, hi, _⟩; omega
    · rintro ⟨i, hi, hx⟩
      have : i = 0 := by omega
      subst this
      rw [cho_cnt_succ, cho_cnt_zero, cho_cnt_zero, cho_if_neg (by rw [hx]; exact lt_irrefl _)]
  | succ j ih =>
    intro hI
    have hI0 : Interlaces j μ θ := fun k hk => hI k (by omega)
    obtain ⟨F1, F2, F3, F4⟩ := ih hI0
    have hj := hI j (by omega)
    have hmono : ∀ i, i ≤ j → θ i ≤ θ j := fun i hi => hI.theta_mono hi (by omega)
    rw [cho_cnt_succ θ (j + 1), cho_cnt_succ μ j]
    have key : x < θ (j + 1) ∨ θ (j + 1) ≤ x := lt_or_ge _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases h1 : x < μ j
      · rw [cho_if_pos h1, cho_if_pos (h1.trans hj.2)]; omega
      · rw [cho_if_neg h1]
        by_cases h2 : x < θ (j + 1)
        · rw [cho_if_pos h2]; omega
        · rw [cho_if_neg h2]; omega
    · by_cases h1 : x < μ j
      · rw [cho_if_pos h1, cho_if_pos (h1.trans hj.2)]; omega
      · rw [cho_if_neg h1]
        by_cases h2 : x < θ (j + 1)
        · rw [cho_if_pos h2]
          have h0 : cho_cnt θ (j + 1) x = 0 :=
            cho_cnt_eq_zero fun i hi => by
              have := hmono i (by omega); rw [not_lt] at h1; linarith [hj.1]
          omega
        · rw [cho_if_neg h2]; omega
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · have h1 : x < μ j := by
          rw [← hx]; exact hI.mu_strictMono hlt (by omega)
        rw [cho_if_pos h1, cho_if_pos (h1.trans hj.2)]
        have := F3 ⟨i, hlt, hx⟩; omega
      · rw [heq] at hx
        rw [cho_if_pos (hx ▸ hj.2), cho_if_neg (by rw [← hx]; exact lt_irrefl _)]
        have h0 : cho_cnt θ (j + 1) x = 0 :=
          cho_cnt_eq_zero fun i hi => by
            have := hmono i (by omega); linarith [hj.1]
        have := F1; omega
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · have hle := hmono i (by omega)
        have h1 : x < μ j := by rw [← hx]; linarith [hj.1]
        rw [cho_if_pos h1, cho_if_pos (h1.trans hj.2)]
        have := F4 ⟨i, by omega, hx⟩; omega
      · rw [heq] at hx
        have h1 : ¬ x < μ j := by rw [← hx]; exact not_lt.mpr hj.2.le
        rw [cho_if_neg h1, cho_if_neg (by rw [hx]; exact lt_irrefl _)]
        have h0 : cho_cnt θ (j + 1) x = 0 :=
          cho_cnt_eq_zero fun i hi => by
            have := hmono i (by omega); rw [← hx]; linarith [hj.2, hj.1]
        have := F1; omega

/-- Sign of `∏_{i<n} (x - f i)` is `(-1)^{#{i : x < f i}}` when no `f i` equals `x`. -/
theorem cho_sign_prod (f : ℕ → ℝ) (x : ℝ) :
    ∀ n : ℕ, (∀ i, i < n → f i ≠ x) → 0 < (-1 : ℝ) ^ cho_cnt f n x * ∏ i ∈ range n, (x - f i) := by
  intro n
  induction n with
  | zero => intro _; simp [cho_cnt_zero]
  | succ n ih =>
    intro h
    have ih' := ih fun i hi => h i (by omega)
    have hn : f n ≠ x := h n (by omega)
    rw [cho_cnt_succ, prod_range_succ]
    by_cases hx : x < f n
    · rw [cho_if_pos hx, pow_succ]
      have : (-1 : ℝ) ^ cho_cnt f n x * (-1) * ((∏ i ∈ range n, (x - f i)) * (x - f n)) =
          ((-1 : ℝ) ^ cho_cnt f n x * ∏ i ∈ range n, (x - f i)) * (f n - x) := by ring
      rw [this]; exact mul_pos ih' (by linarith)
    · rw [cho_if_neg hx, add_zero]
      have : (-1 : ℝ) ^ cho_cnt f n x * ((∏ i ∈ range n, (x - f i)) * (x - f n)) =
          ((-1 : ℝ) ^ cho_cnt f n x * ∏ i ∈ range n, (x - f i)) * (x - f n) := by ring
      rw [this]
      exact mul_pos ih' (by have := lt_of_le_of_ne (not_lt.mp hx) hn; linarith)

/-- info: 'FormalResearch.Special.cho_count_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cho_count_step

end FormalResearch.Special
