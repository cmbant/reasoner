module

public import FormalResearch.SignUncertainty.CtOuterBdd

/-!
# Uniform bound for the outer-band integral over all `L` (`ct:dual-id` (2), uniform bound)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (2), the bound `|K_ε(ξ;c)| ≤ C√c` (here in
the stronger form `√c‖I‖ ≤ K_b`, i.e. `|K_ε| ≤ K_b'`) uniform in `ξ > 0`, `c ≥ 2` and over all amplitudes with the same `AmpBd`
constant.  **Proved.**  Cases: `L ≤ 0` and `μ₀ < 1` (`bdd_tiny`), `1 ≤ μ₀ < M₀` (`bdd_small_final`, `bdd_large`),
`μ₀ ≥ M₀` (`outer_band`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtOsc

/-- The leading stationary-phase term is `O(c^{-1/2})`. -/
theorem outer_band_sqrt (C0 CA : ℝ) (hC0 : 0 < C0) (hCA : 0 ≤ CA) :
    ∃ M0 Kb : ℝ, 0 < M0 ∧ 0 ≤ Kb ∧
      ∀ {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {τ0 c : ℝ},
        MData C0 m m1 m2 m3 → AmpBd CA A A1 A2 → 0 < τ0 → 0 < c →
        (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) → M0 ≤ c * min 1 (τ0 ^ 3) →
        ∃ I : ℂ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
          Real.sqrt c * ‖I‖ ≤ Kb := by
  obtain ⟨M0, K, hM0, hK, H⟩ := outer_band C0 CA hC0 hCA
  have hpi := Real.pi_pos
  refine ⟨M0, Real.sqrt (2 * π) * CA + K / M0, hM0, by positivity, ?_⟩
  intro m m1 m2 m3 A A1 A2 ϕ τ0 c hM hA hτ0 hc hϕ hμ
  obtain ⟨I, hI, hb⟩ := H hM hA hτ0 hc hϕ hμ
  refine ⟨I, hI, ?_⟩
  set lead : ℂ := Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * m1 τ0)) : ℝ) : ℂ) * A τ0 *
    Complex.exp (Complex.I * c * (ϕ τ0 : ℂ)) with hlead
  have hs1 : τ0 / (1 + τ0 ^ 2) ≤ m1 τ0 := hM.lo τ0 hτ0
  have hs0 : 0 < m1 τ0 := lt_of_lt_of_le (by positivity) hs1
  have hn1 : ‖Complex.exp ((π : ℂ) / 4 * Complex.I)‖ = 1 := by
    rw [show (π : ℂ) / 4 * Complex.I = ((π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hn2 : ‖Complex.exp (Complex.I * c * (ϕ τ0 : ℂ))‖ = 1 := by
    rw [show Complex.I * (c : ℂ) * (ϕ τ0 : ℂ) = ((c * ϕ τ0 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hlead_norm : ‖lead‖ = Real.sqrt (2 * π / (c * m1 τ0)) * ‖A τ0‖ := by
    rw [hlead, norm_mul, norm_mul, norm_mul, hn1, hn2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    ring
  have hA0 := hA.b0 τ0 hτ0
  obtain ⟨r1, -, -, -, -⟩ := rp_all hτ0
  have hq : Real.sqrt c * ‖lead‖ ≤ Real.sqrt (2 * π) * CA := by
    rw [hlead_norm]
    have e1 : Real.sqrt c * Real.sqrt (2 * π / (c * m1 τ0)) = Real.sqrt (2 * π / m1 τ0) := by
      rw [← Real.sqrt_mul hc.le]
      congr 1
      field_simp
    rw [← mul_assoc, e1]
    have e2 : ‖A τ0‖ ≤ CA * Real.sqrt τ0 / (1 + τ0) := by rwa [r1] at hA0
    have hsq : Real.sqrt (2 * π / m1 τ0) * Real.sqrt τ0 ≤ Real.sqrt (2 * π) * (1 + τ0) := by
      rw [← Real.sqrt_mul (by positivity)]
      have : Real.sqrt (2 * π) * (1 + τ0) = Real.sqrt (2 * π * (1 + τ0) ^ 2) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π) ((1 + τ0) ^ 2), Real.sqrt_sq (by linarith)]
      rw [this]
      apply Real.sqrt_le_sqrt
      rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
      have : τ0 ≤ (1 + τ0 ^ 2) * m1 τ0 := by
        have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 1 + τ0 ^ 2)
        rwa [mul_div_cancel₀ _ (by positivity)] at this
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * π), sq_nonneg τ0,
        mul_pos hs0 hτ0, mul_pos hs0 (mul_pos hτ0 hτ0)]
    calc Real.sqrt (2 * π / m1 τ0) * ‖A τ0‖ ≤ Real.sqrt (2 * π / m1 τ0) * (CA * Real.sqrt τ0 / (1 + τ0)) :=
          mul_le_mul_of_nonneg_left e2 (Real.sqrt_nonneg _)
      _ = CA * (Real.sqrt (2 * π / m1 τ0) * Real.sqrt τ0) / (1 + τ0) := by ring
      _ ≤ CA * (Real.sqrt (2 * π) * (1 + τ0)) / (1 + τ0) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsq hCA
      _ = Real.sqrt (2 * π) * CA := by field_simp
  have hmin0 : 0 < min 1 (τ0 ^ 3) := lt_min one_pos (by positivity)
  have hcm : 0 < c * min 1 (τ0 ^ 3) := by positivity
  have hrem : Real.sqrt c * (K / (c * Real.sqrt c * min 1 (τ0 ^ 3))) ≤ K / M0 := by
    have : Real.sqrt c * (K / (c * Real.sqrt c * min 1 (τ0 ^ 3))) = K / (c * min 1 (τ0 ^ 3)) := by
      have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_left hK hM0 hμ
  have hI : ‖I‖ ≤ ‖lead‖ + K / (c * Real.sqrt c * min 1 (τ0 ^ 3)) := by
    have := norm_sub_norm_le I lead
    linarith only [this, hb]
  have hsc0 := Real.sqrt_nonneg c
  calc Real.sqrt c * ‖I‖ ≤ Real.sqrt c * (‖lead‖ + K / (c * Real.sqrt c * min 1 (τ0 ^ 3))) :=
        mul_le_mul_of_nonneg_left hI hsc0
    _ = Real.sqrt c * ‖lead‖ + Real.sqrt c * (K / (c * Real.sqrt c * min 1 (τ0 ^ 3))) := by ring
    _ ≤ _ := by linarith only [hq, hrem]

/-- **Uniform bound over all `L`.**  For `c ≥ 2` and every real `L` (with `m ≥ 0` and every positive level `L` attained by `m`),
the improper integral `I = ∫₀^∞ A e^{icϕ}` (`ϕ' = m - L`) exists and `√c ‖I‖ ≤ K_b`, with `K_b` depending only on
`C0, CA`. -/
theorem uniform_L (C0 CA : ℝ) (hC0 : 0 < C0) (hCA : 0 ≤ CA) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {c L : ℝ},
      MData C0 m m1 m2 m3 → AmpBd CA A A1 A2 → 2 ≤ c → (∀ τ : ℝ, 0 < τ → 0 ≤ m τ) →
      (0 < L → ∃ τ0 : ℝ, 0 < τ0 ∧ m τ0 = L) → (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ) →
      ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
        Real.sqrt c * ‖I‖ ≤ Kb := by
  obtain ⟨M0, Kb1, hM0, hKb1, H1⟩ := outer_band_sqrt C0 CA hC0 hCA
  obtain ⟨Cs, hCs, Hs⟩ := bdd_small_final C0 CA hC0 hCA
  obtain ⟨Cl, hCl, Hl⟩ := bdd_large C0 CA hC0 hCA
  obtain ⟨Ct, hCt, Ht⟩ := bdd_tiny C0 CA hC0 hCA
  have hsM : 0 ≤ Real.sqrt M0 := Real.sqrt_nonneg _
  have n1 : 0 ≤ Cs * (1 + Real.sqrt M0) := by positivity
  have n2 : 0 ≤ Real.sqrt M0 * Cl := by positivity
  refine ⟨Ct + Kb1 + Cs * (1 + Real.sqrt M0) + Real.sqrt M0 * Cl, by positivity, ?_⟩
  intro m m1 m2 m3 A A1 A2 ϕ c L hM hA hc hm0 hroot hϕ
  have hc0 : 0 < c := by linarith
  set lam : ℝ := c ^ (-(1 / 3 : ℝ)) with hlamdef
  have hlam : 0 < lam := Real.rpow_pos_of_pos hc0 _
  have hcl : c * lam ^ 3 = 1 := by
    have : lam ^ 3 = c ^ (-1 : ℝ) := by
      rw [hlamdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      norm_num
    rw [this, Real.rpow_neg_one]
    field_simp
  by_cases hL : L ≤ 0
  · obtain ⟨I, hI, hb⟩ := Ht hM hA hc hlam hcl hϕ (fun τ hτ => by
      have hτp : 0 < τ := by linarith
      have h1 := hM.step (κ := 1 / 2) (by norm_num) (by norm_num) hτp
      have h2 := hm0 (1 / 2 * τ) (by positivity)
      have h3 : (1 / 4 : ℝ) * sg τ ≤ m τ - L := by linarith
      exact h3.trans (le_abs_self _))
    exact ⟨I, hI, hb.trans (by linarith only [hKb1, n1, n2])⟩
  · push_neg at hL
    obtain ⟨τ0, hτ0, rfl⟩ := hroot hL
    by_cases hμ : c * min 1 (τ0 ^ 3) < 1
    · have hτ1 : τ0 < 1 := by
        by_contra h
        push_neg at h
        rw [min_eq_left (one_le_pow₀ h)] at hμ
        linarith
      rw [min_eq_right (pow_le_one₀ hτ0.le hτ1.le)] at hμ
      have hτl : τ0 < lam := by
        refine lt_of_pow_lt_pow_left₀ 3 hlam.le ?_
        have : c * τ0 ^ 3 < c * lam ^ 3 := by rw [hcl]; exact hμ
        exact lt_of_mul_lt_mul_left this hc0.le
      obtain ⟨I, hI, hb⟩ := Ht hM hA hc hlam hcl hϕ (fun τ hτ => hp_two hM hτ0 (by linarith))
      exact ⟨I, hI, hb.trans (by linarith only [hKb1, n1, n2])⟩
    · push_neg at hμ
      by_cases hMM : M0 ≤ c * min 1 (τ0 ^ 3)
      · obtain ⟨I, hI, hb⟩ := H1 hM hA hτ0 hc0 hϕ hMM
        exact ⟨I, hI, hb.trans (by linarith only [hCt, n1, n2])⟩
      · push_neg at hMM
        by_cases h1 : τ0 ≤ 1
        · have hmin : min 1 (τ0 ^ 3) = τ0 ^ 3 := min_eq_right (pow_le_one₀ hτ0.le h1)
          rw [hmin] at hμ hMM
          obtain ⟨I, hI, hb⟩ := Hs hM hA hc0 hτ0 h1 hμ hϕ
          refine ⟨I, hI, hb.trans ?_⟩
          have hsq : Real.sqrt (c * τ0 ^ 3) ≤ Real.sqrt M0 := Real.sqrt_le_sqrt hMM.le
          have := mul_le_mul_of_nonneg_left hsq hCs
          nlinarith only [this, hCt, hKb1, n2]
        · push_neg at h1
          have hmin : min 1 (τ0 ^ 3) = 1 := min_eq_left (one_le_pow₀ h1.le)
          rw [hmin, mul_one] at hMM
          obtain ⟨I, hI, hb⟩ := Hl hM hA hc h1.le hϕ
          refine ⟨I, hI, ?_⟩
          have h2 : Real.sqrt c * ‖I‖ ≤ Real.sqrt M0 * Cl :=
            mul_le_mul (Real.sqrt_le_sqrt hMM.le) hb (norm_nonneg _) hsM
          linarith only [h2, hCt, hKb1, n1]

/-- info: 'FormalResearch.SignUncertainty.CtOsc.uniform_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform_L

/-- info: 'FormalResearch.SignUncertainty.CtOsc.outer_band_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outer_band_sqrt

end FormalResearch.SignUncertainty.CtOsc
