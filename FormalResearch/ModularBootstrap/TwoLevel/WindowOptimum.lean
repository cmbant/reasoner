module

public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumFunction

/-!
# The window optimum `u₂*(K)` as a weighted mean of Clark nodes (`virasoro_two_level.tex`, Proposition 2.3 `gt:2.3`)

`∫ f_K` is affine in `u₂`, and the Clark-Airy summation exhibits it as
`∫ f_K = Σ_n w_n (u₂ - z_n)` with positive weights `w_n` supported on `n = 2` and `n > K`.  Hence
`u₂*(K) = Σ w_n z_n / Σ w_n` (`windowOptimum_eq`), strictly below `z₂` (`windowOptimum_lt`) and with
`z₂ - u₂*(K) ≤ Σ_{n>K} w_n (z₂ - z_n) / w₂` (`windowOptimum_sub_le`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

/-- `∫_ℝ f_K` for the window function with second simple zero `u₂`. -/
noncomputable def windowInt (α : ℝ) (K : ℕ) (u₂ : ℝ) : ℝ := ∫ x : ℝ, (windowF α K u₂ (x : ℂ)).re

/-- `u₂*(K)`: the largest `u₂` with `∫ f_K ≤ 0`. -/
noncomputable def windowOptimum (α : ℝ) (K : ℕ) : ℝ := sSup {u₂ : ℝ | windowInt α K u₂ ≤ 0}

/-- The weight `w_n ≥ 0` carried by the node `z_n`: positive exactly for `n = 2` and `n > K`. -/
noncomputable def windowWeight (α : ℝ) (K n : ℕ) : ℝ :=
  if n = 2 ∨ K < n then
    -((clarkNode α n - clarkNode α 1) * ∏ k ∈ Finset.Icc 3 K, (clarkNode α n - clarkNode α k) ^ 2) /
      (windowDr K (clarkNode α n) ^ 2 * (cotC α ^ 2 - clarkNode α n))
  else 0

lemma cot_sq_sub_pos (α : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < cotC α ^ 2 - clarkNode α n := by
  have h := airyKer_pos' (clarkNode α n)
  have hd := clarkNode_airyAi' (α := α) hn
  have hA := clarkNode_airyAi_ne (α := α) hn
  rw [hd] at h
  have hA2 : 0 < airyAi (clarkNode α n) ^ 2 := by positivity
  have h' : 0 < airyAi (clarkNode α n) ^ 2 * (cotC α ^ 2 - clarkNode α n) := by
    have e : (cotC α * airyAi (clarkNode α n)) ^ 2 - clarkNode α n * airyAi (clarkNode α n) ^ 2 =
        airyAi (clarkNode α n) ^ 2 * (cotC α ^ 2 - clarkNode α n) := by ring
    linarith
  exact (mul_pos_iff_of_pos_left hA2).mp h'

lemma windowTerm_eq (α : ℝ) {K : ℕ} (_hK : 3 ≤ K) (u₂ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    windowTerm α K u₂ n = windowWeight α K n * (u₂ - clarkNode α n) := by
  unfold windowTerm windowWeight windowNr
  by_cases hS : n = 2 ∨ K < n
  · rw [ite_eq_left hS]; field_simp; ring
  · rw [ite_eq_right hS, zero_mul]
    have : (clarkNode α n - clarkNode α 1) * (clarkNode α n - u₂) *
        ∏ k ∈ Finset.Icc 3 K, (clarkNode α n - clarkNode α k) ^ 2 = 0 := by
      push Not at hS
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · have : n = 1 := by omega
        subst this; simp
      · have hmem : n ∈ Finset.Icc 3 K := Finset.mem_Icc.mpr ⟨h3, hS.2⟩
        rw [Finset.prod_eq_zero hmem (by simp), mul_zero]
    rw [this, zero_div]

lemma windowWeight_pos (α : ℝ) {K : ℕ} (hK : 3 ≤ K) {n : ℕ} (hS : n = 2 ∨ K < n) :
    0 < windowWeight α K n := by
  have hn : 1 ≤ n := by rcases hS with h | h <;> omega
  unfold windowWeight
  rw [ite_eq_left hS]
  have h1 : clarkNode α n < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by omega) α
  have hP : 0 < ∏ k ∈ Finset.Icc 3 K, (clarkNode α n - clarkNode α k) ^ 2 := by
    refine Finset.prod_pos (fun k hk => ?_)
    have hk3 := (Finset.mem_Icc.mp hk)
    have hne : clarkNode α n ≠ clarkNode α k := by
      intro h
      rcases hS with rfl | hlt
      · have := clarkNode_lt_of_lt (n := 2) (m := k) (by norm_num) (by omega) α; linarith
      · have := clarkNode_lt_of_lt (n := k) (m := n) (by omega) (by omega) α; linarith
    have := sub_ne_zero.mpr hne
    positivity
  have hD : 0 < windowDr K (clarkNode α n) ^ 2 := by
    have := windowDr_node_ne α K hn
    positivity
  have hc := cot_sq_sub_pos α hn
  apply div_pos
  · have : (clarkNode α n - clarkNode α 1) * ∏ k ∈ Finset.Icc 3 K, (clarkNode α n - clarkNode α k) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hP
    linarith
  · positivity

lemma windowWeight_nonneg (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (n : ℕ) : 0 ≤ windowWeight α K n := by
  by_cases hS : n = 2 ∨ K < n
  · exact (windowWeight_pos α hK hS).le
  · unfold windowWeight; rw [ite_eq_right hS]


/-- `Σ_n w_n (z₂ - z_n)`, the first moment of the weights about `z₂` (all terms `≥ 0`). -/
noncomputable def windowTail (α : ℝ) (K : ℕ) : ℝ :=
  ∑' n : ℕ, windowWeight α K (n + 1) * (clarkNode α 2 - clarkNode α (n + 1))

lemma windowInt_hasSum {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    HasSum (fun n : ℕ => windowWeight α K (n + 1) * (u₂ - clarkNode α (n + 1))) (windowInt α K u₂) := by
  have h := windowF_hasSum hα hK u₂
  have e : (fun n : ℕ => windowWeight α K (n + 1) * (u₂ - clarkNode α (n + 1))) =
      fun n : ℕ => windowTerm α K u₂ (n + 1) :=
    funext fun n => (windowTerm_eq α hK u₂ (by omega : 1 ≤ n + 1)).symm
  rw [e]; exact h

/-- The weights are summable, with sum `W = ∫ f_K|_{u₂=1} - ∫ f_K|_{u₂=0}`, and the first moment is `-∫ f_K|_{u₂=0}`. -/
lemma windowWeight_hasSum {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    HasSum (fun n : ℕ => windowWeight α K (n + 1)) (windowInt α K 1 - windowInt α K 0) := by
  have h := (windowInt_hasSum hα hK 1).sub (windowInt_hasSum hα hK 0)
  convert h using 1
  funext n; ring

lemma windowMoment_hasSum {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    HasSum (fun n : ℕ => windowWeight α K (n + 1) * clarkNode α (n + 1)) (-windowInt α K 0) := by
  have h := (windowInt_hasSum hα hK 0).neg
  convert h using 1
  funext n; ring

/-- `∫ f_K` is affine in `u₂`: `∫ f_K = ∫ f_K|_{u₂=0} + u₂ W`. -/
lemma windowInt_affine {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    windowInt α K u₂ = windowInt α K 0 + u₂ * (windowInt α K 1 - windowInt α K 0) := by
  have h := ((windowWeight_hasSum hα hK).mul_left u₂).sub (windowMoment_hasSum hα hK)
  have h2 : HasSum (fun n : ℕ => windowWeight α K (n + 1) * (u₂ - clarkNode α (n + 1)))
      (u₂ * (windowInt α K 1 - windowInt α K 0) - -windowInt α K 0) := by
    convert h using 1
    funext n; ring
  have := (windowInt_hasSum hα hK u₂).unique h2
  linarith

lemma windowSlope_pos {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    0 < windowInt α K 1 - windowInt α K 0 := by
  have h := windowWeight_hasSum hα hK
  have := le_hasSum h 1 (fun n _ => windowWeight_nonneg α hK (n + 1))
  exact lt_of_lt_of_le (windowWeight_pos α hK (Or.inl rfl)) this

/-- **`u₂*(K)` is the largest `u₂` with `∫ f_K ≤ 0`**, and equals the weighted mean `Σ w_n z_n / Σ w_n`. -/
theorem windowOptimum_isGreatest {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    IsGreatest {u₂ : ℝ | windowInt α K u₂ ≤ 0} (windowOptimum α K) := by
  have hW := windowSlope_pos hα hK
  set W := windowInt α K 1 - windowInt α K 0 with hWdef
  have hset : {u₂ : ℝ | windowInt α K u₂ ≤ 0} = Set.Iic (-windowInt α K 0 / W) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [windowInt_affine hα hK u, le_div_iff₀ hW]
    constructor <;> intro h <;> linarith
  have : windowOptimum α K = -windowInt α K 0 / W := by
    unfold windowOptimum; rw [hset]; exact csSup_Iic
  rw [this, hset]
  exact isGreatest_Iic

theorem windowOptimum_eq {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    windowOptimum α K = (∑' n : ℕ, windowWeight α K (n + 1) * clarkNode α (n + 1)) /
      ∑' n : ℕ, windowWeight α K (n + 1) := by
  have hW := windowSlope_pos hα hK
  have h1 := (windowMoment_hasSum hα hK).tsum_eq
  have h2 := (windowWeight_hasSum hα hK).tsum_eq
  rw [h1, h2]
  have hset : {u₂ : ℝ | windowInt α K u₂ ≤ 0} = Set.Iic (-windowInt α K 0 / (windowInt α K 1 - windowInt α K 0)) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [windowInt_affine hα hK u, le_div_iff₀ hW]
    constructor <;> intro h <;> linarith
  unfold windowOptimum; rw [hset]; exact csSup_Iic

lemma windowTail_hasSum {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    HasSum (fun n : ℕ => windowWeight α K (n + 1) * (clarkNode α 2 - clarkNode α (n + 1)))
      (windowTail α K) := by
  have h := ((windowWeight_hasSum hα hK).mul_left (clarkNode α 2)).sub (windowMoment_hasSum hα hK)
  have h2 : HasSum (fun n : ℕ => windowWeight α K (n + 1) * (clarkNode α 2 - clarkNode α (n + 1)))
      (clarkNode α 2 * (windowInt α K 1 - windowInt α K 0) - -windowInt α K 0) := by
    convert h using 1
    funext n; ring
  unfold windowTail
  rw [h2.tsum_eq]; exact h2

lemma windowTail_term_nonneg (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (n : ℕ) :
    0 ≤ windowWeight α K (n + 1) * (clarkNode α 2 - clarkNode α (n + 1)) := by
  by_cases hS : n + 1 = 2 ∨ K < n + 1
  · refine mul_nonneg (windowWeight_pos α hK hS).le ?_
    rcases hS with h | h
    · rw [h]; simp
    · have := clarkNode_lt_of_lt (n := 2) (m := n + 1) (by norm_num) (by omega) α
      linarith
  · unfold windowWeight; rw [ite_eq_right hS]; simp

lemma windowOptimum_sub_eq {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    clarkNode α 2 - windowOptimum α K = windowTail α K / ∑' n : ℕ, windowWeight α K (n + 1) := by
  have hW := windowSlope_pos hα hK
  have h2 := (windowWeight_hasSum hα hK).tsum_eq
  have hZ := (windowMoment_hasSum hα hK).tsum_eq
  have h3 := ((windowWeight_hasSum hα hK).mul_left (clarkNode α 2)).sub (windowMoment_hasSum hα hK)
  have h4 : HasSum (fun n : ℕ => windowWeight α K (n + 1) * (clarkNode α 2 - clarkNode α (n + 1)))
      (clarkNode α 2 * (windowInt α K 1 - windowInt α K 0) - -windowInt α K 0) := by
    convert h3 using 1
    funext n; ring
  have hT : windowTail α K = clarkNode α 2 * (windowInt α K 1 - windowInt α K 0) - -windowInt α K 0 :=
    h4.tsum_eq
  rw [windowOptimum_eq hα hK, h2, hZ, hT]
  field_simp

/-- **`u₂*(K) < z₂`.** -/
theorem windowOptimum_lt {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    windowOptimum α K < clarkNode α 2 := by
  have hW := windowSlope_pos hα hK
  have h2 := (windowWeight_hasSum hα hK).tsum_eq
  have hTpos : 0 < windowTail α K := by
    have := le_hasSum (windowTail_hasSum hα hK) K (fun n _ => windowTail_term_nonneg α hK n)
    refine lt_of_lt_of_le (mul_pos (windowWeight_pos α hK (Or.inr (by omega))) ?_) this
    have := clarkNode_lt_of_lt (n := 2) (m := K + 1) (by norm_num) (by omega) α
    linarith
  have := windowOptimum_sub_eq hα hK
  rw [h2] at this
  have : 0 < clarkNode α 2 - windowOptimum α K := by rw [this]; exact div_pos hTpos hW
  linarith

/-- `z₂ - u₂*(K) ≤ (Σ_{n>K} w_n (z₂ - z_n)) / w₂`. -/
theorem windowOptimum_sub_le {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    clarkNode α 2 - windowOptimum α K ≤ windowTail α K / windowWeight α K 2 := by
  have hW := windowSlope_pos hα hK
  have h2 := (windowWeight_hasSum hα hK).tsum_eq
  have hw2 := windowWeight_pos α hK (Or.inl rfl : (2 : ℕ) = 2 ∨ K < 2)
  have hle : windowWeight α K 2 ≤ windowInt α K 1 - windowInt α K 0 :=
    le_hasSum (windowWeight_hasSum hα hK) 1 (fun n _ => windowWeight_nonneg α hK (n + 1))
  have hT : 0 ≤ windowTail α K := (windowTail_hasSum hα hK).nonneg (windowTail_term_nonneg α hK)
  rw [windowOptimum_sub_eq hα hK, h2]
  exact div_le_div_of_nonneg_left hT hw2 hle

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.windowOptimum_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowOptimum_isGreatest

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.windowOptimum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowOptimum_eq

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.windowOptimum_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowOptimum_lt

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.windowOptimum_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowOptimum_sub_le

end FormalResearch.ModularBootstrap.TwoLevel
