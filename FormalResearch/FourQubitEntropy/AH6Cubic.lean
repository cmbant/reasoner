import Mathlib

/-!
# A cubic with negative discriminant, positive leading coefficient and nonnegative constant term is nonnegative on `[0,∞)`

`ResearchNotes/QI/seven_qubit_entanglement/joint_entropy_analytic_proof.tex`, section "Completion and equality":
for `e ≠ e₀` the discriminant of `F(e,·)` is negative, so the cubic has exactly one real root, which is nonpositive.
Here: if `p(v₁) < 0` for some `v₁ ≥ 0`, then `p` has a root in `[0,v₁)` (since `p(0) ≥ 0`) and one in `(v₁,∞)`, hence
three real roots and a nonnegative discriminant (`disc_of_roots`).
-/

namespace FormalResearch.FourQubitEntropy.AH6

/-- The discriminant of `a v³ + b v² + c v + d`. -/
def disc3 (a b c d : ℝ) : ℝ := b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- A cubic with two distinct real roots has nonnegative discriminant. -/
theorem disc_of_roots {a b c d r1 r2 : ℝ} (ha : a ≠ 0) (hr : r1 ≠ r2)
    (h1 : a * r1 ^ 3 + b * r1 ^ 2 + c * r1 + d = 0) (h2 : a * r2 ^ 3 + b * r2 ^ 2 + c * r2 + d = 0) :
    0 ≤ disc3 a b c d := by
  set r3 : ℝ := -b / a - r1 - r2 with hr3
  have hb : b = -a * (r1 + r2 + r3) := by rw [hr3]; field_simp; ring
  have hsub : (r1 - r2) * (a * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + b * (r1 + r2) + c) = 0 := by
    linear_combination h1 - h2
  have hc' : a * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + b * (r1 + r2) + c = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hr
    · exact h
  have hc : c = a * (r1 * r2 + r1 * r3 + r2 * r3) := by
    have : c = -(a * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + b * (r1 + r2)) := by linarith
    rw [this, hb]; ring
  have hd : d = -a * (r1 * r2 * r3) := by
    have : d = -(a * r1 ^ 3 + b * r1 ^ 2 + c * r1) := by linarith
    rw [this, hb, hc]; ring
  have : disc3 a b c d = a ^ 4 * ((r1 - r2) ^ 2 * (r1 - r3) ^ 2 * (r2 - r3) ^ 2) := by
    unfold disc3; rw [hb, hc, hd]; ring
  rw [this]; positivity

/-- **Cubic lemma.** -/
theorem cubic_nonneg {a b c d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hdisc : disc3 a b c d < 0) :
    ∀ v : ℝ, 0 ≤ v → 0 ≤ a * v ^ 3 + b * v ^ 2 + c * v + d := by
  intro v1 hv1
  by_contra hneg
  push Not at hneg
  set p : ℝ → ℝ := fun v => a * v ^ 3 + b * v ^ 2 + c * v + d with hp
  have hcont : Continuous p := by rw [hp]; fun_prop
  have hv1pos : 0 < v1 := by
    rcases hv1.eq_or_lt with h | h
    · rw [← h] at hneg; simp at hneg; linarith
    · exact h
  -- a root in [0, v1)
  have hp0 : 0 ≤ p 0 := by simp [hp]; exact hd
  have hpv1 : p v1 < 0 := hneg
  obtain ⟨r1, hr1, hr10⟩ : ∃ r1 ∈ Set.Icc (0 : ℝ) v1, p r1 = 0 := by
    have := intermediate_value_Icc' hv1pos.le hcont.continuousOn
    exact this ⟨hpv1.le, hp0⟩
  have hr1lt : r1 < v1 := by
    rcases hr1.2.eq_or_lt with h | h
    · rw [h] at hr10; linarith
    · exact h
  -- a root in (v1, M]
  set M : ℝ := (|b| + |c| + |d|) / a + v1 + 1 with hM
  have hM1 : v1 < M := by
    have : 0 ≤ (|b| + |c| + |d|) / a := by positivity
    linarith
  have hM1' : 1 ≤ M := by
    have : 0 ≤ (|b| + |c| + |d|) / a := by positivity
    linarith
  have hpM : 0 ≤ p M := by
    have hM0 : 0 < M := by linarith
    have h1 : a * M ≥ |b| + |c| + |d| + a := by
      have : (|b| + |c| + |d|) / a * a = |b| + |c| + |d| := by field_simp
      nlinarith
    have hb : -|b| ≤ b := neg_abs_le b
    have hc : -|c| ≤ c := neg_abs_le c
    have hd' : -|d| ≤ d := neg_abs_le d
    have hM2 : M ≤ M ^ 2 := by nlinarith
    have hM22 : 1 ≤ M ^ 2 := by nlinarith
    have e1 : -|b| * M ^ 2 ≤ b * M ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg M)
    have e2 : -|c| * M ≤ c * M := mul_le_mul_of_nonneg_right hc hM0.le
    have e3 : -|c| * M ^ 2 ≤ -|c| * M := by nlinarith [abs_nonneg c]
    have e4 : -|d| * M ^ 2 ≤ -|d| := by nlinarith [abs_nonneg d]
    have e5 : -|d| ≤ d := hd'
    have e6 : M ^ 2 * (a * M - (|b| + |c| + |d|)) ≥ 0 :=
      mul_nonneg (sq_nonneg M) (by linarith)
    simp only [hp]
    nlinarith [e1, e2, e3, e4, e5, e6]

  obtain ⟨r2, hr2, hr20⟩ : ∃ r2 ∈ Set.Icc v1 M, p r2 = 0 :=
    intermediate_value_Icc hM1.le hcont.continuousOn ⟨hpv1.le, hpM⟩
  have hr2gt : v1 < r2 := by
    rcases hr2.1.eq_or_lt with h | h
    · rw [← h] at hr20; linarith
    · exact h
  have := disc_of_roots ha.ne' (ne_of_lt (hr1lt.trans hr2gt)) hr10 hr20
  linarith

end FormalResearch.FourQubitEntropy.AH6
