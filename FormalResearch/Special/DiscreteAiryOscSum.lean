module

public import Mathlib

/-!
# A lattice sum of `(2+|X|)^{-1/2}`

Airy-free.  For a sequence `X : ℤ → ℝ` with steps `g ≤ X_{i+1} - X_i ≤ 1` (`g > 0`) on `Ico a b`,
`Σ_{i ∈ Ico a b} (√(2+|X_i|))⁻¹ ≤ (4/g) (√(2+|X_a|) + √(2+|X_b|))`
(`dao_sum_p`): the lattice sum of the amplitude-squared `(2+|X|)^{-1/2}` of the Airy pair on both sides of the
turn.  Proof: with the continuous antiderivative `F(x) = sgn(x) · 2(√(2+|x|) - √2)` of `(2+|x|)^{-1/2}`
(`daoF`), each term satisfies `(√(2+|x|))⁻¹ (y - x) ≤ 2 (F y - F x)` for `0 < y - x ≤ 1` (`dao_p_step`, by cases on the signs),
and the right side telescopes.  In the Airy application `g = c₁ δ`, `|X| ≤ M δ⁻²`: the sum is `≤ 8 √(2+M)/(c₁ δ²)`,
i.e. `O(h^{-2/3})` (`airyWt_sq_lattice_sum` of `AiryWt` is the analogous bound for `airyWt²`, which carries the extra
factor `e^{-2ξ}` and is not what the Grönwall sums of the `Ai`/`Bi` pair need).

**Claim class: proved.**
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- Upward induction on an integer half-line. -/
lemma dao_int_up_induction {P : ℤ → Prop} (m : ℤ) (h0 : P m) (step : ∀ k, m ≤ k → P k → P (k + 1)) :
    ∀ k, m ≤ k → P k := by
  have key : ∀ n : ℕ, P (m + n) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have := step (m + n) (by omega) ih
      simpa [add_assoc] using this
  intro k hk
  have := key (k - m).toNat
  have e : m + ((k - m).toNat : ℤ) = k := by omega
  rwa [e] at this

/-- The continuous antiderivative `F(x) = sgn(x) 2(√(2+|x|) - √2)` of `(2+|x|)^{-1/2}`. -/
noncomputable def daoF (x : ℝ) : ℝ :=
  if 0 ≤ x then 2 * (√(2 + x) - √2) else -(2 * (√(2 - x) - √2))

lemma daoF_abs_le (x : ℝ) : |daoF x| ≤ 2 * √(2 + |x|) := by
  have h2 : 0 ≤ √2 := Real.sqrt_nonneg 2
  unfold daoF
  split_ifs with h
  · rw [abs_of_nonneg h]
    have : √2 ≤ √(2 + x) := Real.sqrt_le_sqrt (by linarith)
    rw [abs_of_nonneg (by linarith)]
    nlinarith [Real.sqrt_nonneg (2 + x)]
  · rw [not_le] at h
    rw [abs_of_neg h]
    have : √2 ≤ √(2 + -x) := Real.sqrt_le_sqrt (by linarith)
    have e : (2 - x) = 2 + -x := by ring
    rw [e, abs_neg, abs_of_nonneg (by linarith)]
    nlinarith [Real.sqrt_nonneg (2 + -x)]

/-- The single-step inequality `(√(2+|x|))⁻¹ (y - x) ≤ 2 (F y - F x)` for `0 < y - x ≤ 1`. -/
lemma dao_p_step {x y : ℝ} (h0 : 0 < y - x) (h1 : y - x ≤ 1) :
    (√(2 + |x|))⁻¹ * (y - x) ≤ 2 * (daoF y - daoF x) := by
  have s2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have s2sq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hx : 0 ≤ x
  · -- both nonnegative
    have hy : 0 ≤ y := by linarith
    have e : daoF y - daoF x = 2 * (√(2 + y) - √(2 + x)) := by
      unfold daoF; split_ifs; ring
    rw [e, abs_of_nonneg hx]
    have ha : 0 < √(2 + x) := Real.sqrt_pos.2 (by linarith)
    have hb : 0 < √(2 + y) := Real.sqrt_pos.2 (by linarith)
    have ha2 : √(2 + x) * √(2 + x) = 2 + x := Real.mul_self_sqrt (by linarith)
    have hb2 : √(2 + y) * √(2 + y) = 2 + y := Real.mul_self_sqrt (by linarith)
    have hb3 : √(2 + y) ≤ 3 * √(2 + x) := by
      have : (√(2 + y)) ^ 2 ≤ (3 * √(2 + x)) ^ 2 := by nlinarith
      exact abs_le_of_sq_le_sq' this (by positivity) |>.2
    rw [inv_mul_le_iff₀ ha]
    have hab : √(2 + x) ≤ √(2 + y) := Real.sqrt_le_sqrt (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 hb3)]
  · rw [not_le] at hx
    by_cases hy : 0 ≤ y
    · -- crossing step: `-x, y ∈ (0, 1]`
      have hxy1 : -x ≤ 1 := by linarith
      have hyy1 : y ≤ 1 := by linarith
      have e : daoF y - daoF x = 2 * (√(2 + y) - √2) + 2 * (√(2 - x) - √2) := by
        unfold daoF; split_ifs <;> first | (exfalso; linarith) | ring1
      rw [e, abs_of_neg hx]
      have h3 : √(2 + y) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; nlinarith
      have h3' : √(2 - x) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; nlinarith
      have h2' : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hA : y ≤ 4 * (√(2 + y) - √2) := by
        have hb2 : √(2 + y) * √(2 + y) = 2 + y := Real.mul_self_sqrt (by linarith)
        have : √2 ≤ √(2 + y) := Real.sqrt_le_sqrt (by linarith)
        nlinarith [mul_nonneg (sub_nonneg.2 this) (by linarith : (0 : ℝ) ≤ √(2 + y) + √2)]
      have hB : -x ≤ 4 * (√(2 - x) - √2) := by
        have hb2 : √(2 - x) * √(2 - x) = 2 - x := Real.mul_self_sqrt (by linarith)
        have : √2 ≤ √(2 - x) := Real.sqrt_le_sqrt (by linarith)
        nlinarith [mul_nonneg (sub_nonneg.2 this) (by linarith : (0 : ℝ) ≤ √(2 - x) + √2)]
      have hi : (√(2 + -x))⁻¹ ≤ 1 := by
        apply inv_le_one_of_one_le₀
        rw [Real.one_le_sqrt]; linarith
      calc (√(2 + -x))⁻¹ * (y - x) ≤ 1 * (y - x) := mul_le_mul_of_nonneg_right hi (by linarith)
        _ ≤ _ := by nlinarith
    · rw [not_le] at hy
      have e : daoF y - daoF x = 2 * (√(2 - x) - √(2 - y)) := by
        unfold daoF; split_ifs <;> first | (exfalso; linarith) | ring1
      rw [e, abs_of_neg hx]
      have ha : 0 < √(2 - y) := Real.sqrt_pos.2 (by linarith)
      have hb : 0 < √(2 + -x) := Real.sqrt_pos.2 (by linarith)
      have ha2 : √(2 - y) * √(2 - y) = 2 - y := Real.mul_self_sqrt (by linarith)
      have hb2 : √(2 + -x) * √(2 + -x) = 2 + -x := Real.mul_self_sqrt (by linarith)
      have hab : √(2 - y) ≤ √(2 + -x) := Real.sqrt_le_sqrt (by linarith)
      have e2 : √(2 - x) = √(2 + -x) := by ring_nf
      rw [e2, inv_mul_le_iff₀ hb]
      nlinarith [mul_nonneg (sub_nonneg.2 hab) hb.le]

/-- **The lattice sum.**  `Σ_{i ∈ Ico a b} (√(2+|X_i|))⁻¹ ≤ (4/g)(√(2+|X_a|) + √(2+|X_b|))`. -/
theorem dao_sum_p {X : ℤ → ℝ} {a b : ℤ} {g : ℝ} (hg : 0 < g)
    (hgap : ∀ i ∈ Ico a b, g ≤ X (i + 1) - X i ∧ X (i + 1) - X i ≤ 1) :
    ∑ i ∈ Ico a b, (√(2 + |X i|))⁻¹ ≤ 4 / g * (√(2 + |X a|) + √(2 + |X b|)) := by
  have tele : ∀ n : ℤ, a ≤ n → n ≤ b →
      g * ∑ i ∈ Ico a n, (√(2 + |X i|))⁻¹ ≤ 2 * (daoF (X n) - daoF (X a)) := by
    intro n hn
    refine dao_int_up_induction (P := fun n => n ≤ b → g * ∑ i ∈ Ico a n, (√(2 + |X i|))⁻¹ ≤
      2 * (daoF (X n) - daoF (X a))) a ?_ ?_ n hn
    · intro _; simp
    · intro n hn ih hn1
      have hI : Ico a (n + 1) = insert n (Ico a n) := by
        ext i; simp only [mem_Ico, mem_insert]; omega
      rw [hI, sum_insert (by simp)]
      have := ih (by omega)
      obtain ⟨hg1, hg2⟩ := hgap n (by rw [mem_Ico]; omega)
      have hst := dao_p_step (x := X n) (y := X (n + 1)) (by linarith) hg2
      have hp : 0 ≤ (√(2 + |X n|))⁻¹ := by positivity
      have : g * (√(2 + |X n|))⁻¹ ≤ (√(2 + |X n|))⁻¹ * (X (n + 1) - X n) := by
        nlinarith
      nlinarith
  rcases le_or_gt a b with hab | hab
  · have h := tele b hab le_rfl
    have h1 := daoF_abs_le (X b)
    have h2 := daoF_abs_le (X a)
    have h3 := (abs_le.1 h1).2
    have h4 := (abs_le.1 h2).1
    rw [div_mul_eq_mul_div, le_div_iff₀ hg]
    nlinarith
  · have : Ico a b = ∅ := by ext i; simp only [mem_Ico]; simp; omega
    rw [this]; simp only [sum_empty]
    have := Real.sqrt_nonneg (2 + |X a|)
    have := Real.sqrt_nonneg (2 + |X b|)
    positivity

/-- info: 'FormalResearch.Special.dao_sum_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_sum_p

end FormalResearch.Special
