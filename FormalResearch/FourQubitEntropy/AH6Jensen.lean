import FormalResearch.FourQubitEntropy.AH6StieltjesInt

/-!
# The Jensen lower bound for the Stieltjes kernel

`K̃(e) = ∫₀¹ w(r)/D_r(e) dr` with `w ≥ 0` (`wt`).  Put `a(r) = w(r)/D_r(e₀)`, `y(r) = (1-r)/D_r(e₀)`, so that
`1/D_r(e) = (1/D_r(e₀)) / (1 + δ y)` with `δ = e - e₀`.  For the number `c = ∫ a y / ∫ a ∈ [0, 1/e₀]` (the mean
of `y`) the tangent line inequality for the convex function `y ↦ 1/(1+δy)` gives
`K̃(e)(1 + c(e - e₀)) ≥ K̃(e₀)` (`jensen_kint`), the paper's `eq:seven-joint-kernel-jensen`
(`K(e) ≥ k₀/L(e)`).  The paper normalises the integrand to a probability measure; here the same argument is
integrated directly.
-/

namespace FormalResearch.FourQubitEntropy.AH6

open MeasureTheory intervalIntegral Set

/-- Tangent line inequality for `1/(1+δy)`. -/
theorem tangent_inv {A B y c δ : ℝ} (hA : 0 < A) (hB : 0 < B) (hAy : A = 1 + δ * y)
    (hBc : B = 1 + δ * c) : 1 / B - δ * (y - c) / B ^ 2 ≤ 1 / A := by
  have : 1 / A - (1 / B - δ * (y - c) / B ^ 2) = (A - B) ^ 2 / (A * B ^ 2) := by
    have hδ : δ * (y - c) = A - B := by rw [hAy, hBc]; ring
    rw [hδ]; field_simp; ring
  have h2 : 0 ≤ (A - B) ^ 2 / (A * B ^ 2) := by positivity
  linarith

section

variable {n1 n2 n3 : ℝ}

theorem jensen_kint (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3) {e0 : ℝ} (he0 : 0 < e0) :
    0 < Kint n1 n2 n3 e0 ∧ ∃ c : ℝ, 0 ≤ c ∧ c * e0 ≤ 1 ∧
      ∀ e : ℝ, 0 < e → Kint n1 n2 n3 e0 ≤ Kint n1 n2 n3 e * (1 + c * (e - e0)) := by
  set a : ℝ → ℝ := fun r => wt n1 n2 n3 r / Dr r e0 with ha
  set y : ℝ → ℝ := fun r => (1 - r) / Dr r e0 with hy
  have hDpos : ∀ r ∈ Icc (0 : ℝ) 1, 0 < Dr r e0 := fun r hr => Dr_pos he0 hr.1 hr.2
  have haC : ContinuousOn a (Icc 0 1) := wtD_contOn h1 h2 h3 he0
  have hyC : ContinuousOn y (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by unfold Dr; fun_prop)
    intro r hr; exact (hDpos r hr).ne'
  have haI : IntervalIntegrable a volume 0 1 := haC.intervalIntegrable_of_Icc zero_le_one
  have hayC : ContinuousOn (fun r => a r * y r) (Icc 0 1) := haC.mul hyC
  have hayI : IntervalIntegrable (fun r => a r * y r) volume 0 1 :=
    hayC.intervalIntegrable_of_Icc zero_le_one
  have ha0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ a r := fun r hr =>
    div_nonneg (wt_nonneg hr.1 hr.2) (hDpos r hr).le
  have hy0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ y r := fun r hr =>
    div_nonneg (by linarith [hr.2]) (hDpos r hr).le
  have hye : ∀ r ∈ Icc (0 : ℝ) 1, y r * e0 ≤ 1 := by
    intro r hr
    have hD := hDpos r hr
    show (1 - r) / Dr r e0 * e0 ≤ 1
    rw [div_mul_eq_mul_div, div_le_one hD]
    unfold Dr; nlinarith [hr.1]
  -- W1 > 0
  have hW1 : 0 < ∫ r in (0 : ℝ)..1, a r := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on haI _ zero_lt_one
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    have : 0 < wt n1 n2 n3 r := by
      unfold wt
      have a1 := Dr_pos h1 hr'.1 hr'.2
      have a2 := Dr_pos h2 hr'.1 hr'.2
      have a3 := Dr_pos h3 hr'.1 hr'.2
      have h1r : 0 < 1 - r := by linarith [hr.2]
      have hr0 : 0 < r := hr.1
      positivity
    exact div_pos this (hDpos r hr')
  have hKint : Kint n1 n2 n3 e0 = ∫ r in (0 : ℝ)..1, a r := rfl
  refine ⟨by rw [hKint]; exact hW1, ?_⟩
  set W1 := ∫ r in (0 : ℝ)..1, a r with hW1def
  set W2 := ∫ r in (0 : ℝ)..1, a r * y r with hW2def
  have hW2nn : 0 ≤ W2 := intervalIntegral.integral_nonneg zero_le_one (fun r hr => mul_nonneg (ha0 r hr) (hy0 r hr))
  have hW2le : W2 ≤ W1 / e0 := by
    rw [le_div_iff₀ he0]
    have : W2 * e0 = ∫ r in (0 : ℝ)..1, a r * y r * e0 := by
      rw [intervalIntegral.integral_mul_const]
    rw [this]
    apply intervalIntegral.integral_mono_on zero_le_one (hayI.mul_const e0) haI
    intro r hr
    have := ha0 r hr
    have := hye r hr
    nlinarith
  set c := W2 / W1 with hc
  have hc0 : 0 ≤ c := div_nonneg hW2nn hW1.le
  have hce : c * e0 ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one hW1]
    rw [le_div_iff₀ he0] at hW2le; linarith
  refine ⟨c, hc0, hce, ?_⟩
  intro e he
  set δ := e - e0 with hδ
  have hB : 0 < 1 + δ * c := by
    rcases le_total 0 δ with h | h
    · nlinarith
    · have : e0 * (1 + δ * c) = e0 + δ * (c * e0) := by ring
      have h2 : e0 + δ * (c * e0) ≥ e0 + δ * 1 := by nlinarith
      have h3 : e0 + δ * 1 = e := by rw [hδ]; ring
      have : 0 < e0 * (1 + δ * c) := by nlinarith
      exact (pos_iff_pos_of_mul_pos this).1 he0
  -- the pointwise tangent bound
  have hpt : ∀ r ∈ Icc (0 : ℝ) 1,
      a r / (1 + δ * c) - δ / (1 + δ * c) ^ 2 * (a r * (y r - c)) ≤ wt n1 n2 n3 r / Dr r e := by
    intro r hr
    have hD0 := hDpos r hr
    have hDe := Dr_pos he hr.1 hr.2
    have hAy : Dr r e / Dr r e0 = 1 + δ * y r := by
      show _ = 1 + δ * ((1 - r) / Dr r e0)
      field_simp
      unfold Dr; rw [hδ]; ring
    have hApos : 0 < 1 + δ * y r := by rw [← hAy]; exact div_pos hDe hD0
    have ht := tangent_inv hApos hB rfl rfl (y := y r) (c := c) (δ := δ)
    have hw0 := wt_nonneg (n1 := n1) (n2 := n2) (n3 := n3) hr.1 hr.2
    have e1 : wt n1 n2 n3 r / Dr r e = a r * (1 / (1 + δ * y r)) := by
      rw [← hAy]; show _ = wt n1 n2 n3 r / Dr r e0 * (1 / (Dr r e / Dr r e0))
      field_simp
    rw [e1]
    have := mul_le_mul_of_nonneg_left ht (ha0 r hr)
    calc a r / (1 + δ * c) - δ / (1 + δ * c) ^ 2 * (a r * (y r - c))
        = a r * (1 / (1 + δ * c) - δ * (y r - c) / (1 + δ * c) ^ 2) := by field_simp
      _ ≤ _ := this
  have hint1 : IntervalIntegrable (fun r => a r / (1 + δ * c) - δ / (1 + δ * c) ^ 2 * (a r * (y r - c)))
      volume 0 1 := by
    apply IntervalIntegrable.sub (haI.div_const _)
    apply IntervalIntegrable.const_mul
    have : (fun r => a r * (y r - c)) = fun r => a r * y r - c * a r := by funext r; ring
    rw [this]; exact hayI.sub (haI.const_mul c)
  have hintK : IntervalIntegrable (fun r => wt n1 n2 n3 r / Dr r e) volume 0 1 :=
    (wtD_contOn h1 h2 h3 he).intervalIntegrable_of_Icc zero_le_one
  have hle := intervalIntegral.integral_mono_on zero_le_one hint1 hintK hpt
  have hlhs : ∫ r in (0 : ℝ)..1, (a r / (1 + δ * c) - δ / (1 + δ * c) ^ 2 * (a r * (y r - c))) =
      W1 / (1 + δ * c) := by
    have hfun : (fun r => a r / (1 + δ * c) - δ / (1 + δ * c) ^ 2 * (a r * (y r - c))) =
        fun r => (1 / (1 + δ * c) + δ * c / (1 + δ * c) ^ 2) * a r -
          δ / (1 + δ * c) ^ 2 * (a r * y r) := by funext r; ring
    rw [hfun, integral_sub ((haI.const_mul _)) (hayI.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hW2c : W2 = c * W1 := by rw [hc]; field_simp
    show ((1 / (1 + δ * c) + δ * c / (1 + δ * c) ^ 2) * W1) - δ / (1 + δ * c) ^ 2 * W2 =
      W1 / (1 + δ * c)
    rw [hW2c]
    field_simp
    ring
  rw [hlhs] at hle
  have hKe : Kint n1 n2 n3 e = ∫ r in (0 : ℝ)..1, wt n1 n2 n3 r / Dr r e := rfl
  rw [← hKe] at hle
  rw [hKint]
  rw [div_le_iff₀ hB] at hle
  linarith

end

end FormalResearch.FourQubitEntropy.AH6
