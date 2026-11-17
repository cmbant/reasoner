module

public import Mathlib
public import FormalResearch.Special.TraceAdmissible

/-!
# Power-of-`L` bookkeeping for `thm:tracecore`

With `ρ = 2 L^{-a}` and `b_h' = σ a/3`:

* `asym_E1` : `C_h (1 + 12/σ)(2ρ)^{5σ/12} · Q log L ≤ C L^{-σ a/3}`;
* `asym_E2` : `Λ₁(ρ) · L^{-a}(1 + Q log L) ≤ C L^{-σ a/3}` (for `L^a ≥ 16`, `log L ≥ 1`), where
  `Λ₁(ρ) = C_h ρ^{σ-1}(1+|log ρ|) + C_h (2ρ)^σ (1+|log ρ|)/ρ`.

`log L ≤ L^ε/ε` (`Real.log_le_rpow_div`) turns every logarithm into a small power.
-/

@[expose] public section

namespace FormalResearch.Special.TraceCore

open Filter Topology Set

lemma log_le_pow {L ε : ℝ} (hL : 1 < L) (hε : 0 < ε) : Real.log L ≤ L ^ ε / ε :=
  Real.log_le_rpow_div (by linarith) hε

lemma asym_E1 {σ a Ch Q : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hCh : 0 ≤ Ch) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 < L →
      Ch * ((1 + 12 / σ) * (2 * (2 * L ^ (-a))) ^ (5 * σ / 12)) * (Q * Real.log L) ≤
        C * L ^ (-(σ * a / 3)) := by
  refine ⟨Ch * (1 + 12 / σ) * 4 ^ (5 * σ / 12) * Q * (12 / (σ * a)) + 1, by positivity, ?_⟩
  intro L hL
  have hL0 : 0 < L := by linarith
  have hlog := log_le_pow hL (show 0 < σ * a / 12 by positivity)
  have hP : 0 < L ^ (-(σ * a / 3)) := Real.rpow_pos_of_pos hL0 _
  have e1 : (2 * (2 * L ^ (-a))) ^ (5 * σ / 12) = 4 ^ (5 * σ / 12) * L ^ (-(5 * σ * a / 12)) := by
    rw [show 2 * (2 * L ^ (-a)) = 4 * L ^ (-a) by ring, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul hL0.le]
    congr 2; ring
  have e2 : L ^ (-(5 * σ * a / 12)) * L ^ (σ * a / 12) = L ^ (-(σ * a / 3)) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  have hlogn : 0 ≤ Real.log L := Real.log_nonneg hL.le
  have h4 : 0 ≤ (4 : ℝ) ^ (5 * σ / 12) := by positivity
  have hLp : 0 ≤ L ^ (-(5 * σ * a / 12)) := by positivity
  rw [e1]
  have h1 : Real.log L * L ^ (-(5 * σ * a / 12)) ≤ 12 / (σ * a) * L ^ (-(σ * a / 3)) := by
    calc Real.log L * L ^ (-(5 * σ * a / 12)) ≤ (L ^ (σ * a / 12) / (σ * a / 12)) * L ^ (-(5 * σ * a / 12)) :=
          mul_le_mul_of_nonneg_right hlog hLp
      _ = 12 / (σ * a) * (L ^ (-(5 * σ * a / 12)) * L ^ (σ * a / 12)) := by field_simp
      _ = _ := by rw [e2]
  have hc : 0 ≤ Ch * (1 + 12 / σ) * 4 ^ (5 * σ / 12) * Q := by positivity
  calc Ch * ((1 + 12 / σ) * (4 ^ (5 * σ / 12) * L ^ (-(5 * σ * a / 12)))) * (Q * Real.log L)
      = (Ch * (1 + 12 / σ) * 4 ^ (5 * σ / 12) * Q) * (Real.log L * L ^ (-(5 * σ * a / 12))) := by ring
    _ ≤ (Ch * (1 + 12 / σ) * 4 ^ (5 * σ / 12) * Q) * (12 / (σ * a) * L ^ (-(σ * a / 3))) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = (Ch * (1 + 12 / σ) * 4 ^ (5 * σ / 12) * Q * (12 / (σ * a))) * L ^ (-(σ * a / 3)) := by ring
    _ ≤ _ := by nlinarith [mul_nonneg hc (show 0 ≤ 12 / (σ * a) by positivity)]

lemma asym_E2 {σ a Ch Q : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ha : 0 < a) (hCh : 0 ≤ Ch) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 < L → 1 ≤ Real.log L → 16 ≤ L ^ a →
      (Ch * (2 * L ^ (-a)) ^ (σ - 1) * (1 + |Real.log (2 * L ^ (-a))|) +
          Ch * (2 * (2 * L ^ (-a))) ^ σ * (1 + |Real.log (2 * L ^ (-a))|) * (1 / (2 * L ^ (-a)))) *
        (L ^ (-a) * (1 + Q * Real.log L)) ≤ C * L ^ (-(σ * a / 3)) := by
  refine ⟨3 * Ch * (1 + a) * (1 + Q) * (9 / (σ * a) ^ 2) + 1, by positivity, ?_⟩
  intro L hL hlog1 hLa
  have hL0 : 0 < L := by linarith
  have hlogn : 0 ≤ Real.log L := by linarith
  have hLa0 : 0 < L ^ a := by positivity
  have hLna : L ^ (-a) = (L ^ a)⁻¹ := Real.rpow_neg hL0.le a
  have hLna_pos : 0 < L ^ (-a) := Real.rpow_pos_of_pos hL0 _
  have hρ1 : 2 * L ^ (-a) ≤ 1 := by
    rw [hLna]; have : (L ^ a)⁻¹ ≤ 1 / 16 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hLa
    linarith
  set ρ : ℝ := 2 * L ^ (-a) with hρ
  have hρ0 : 0 < ρ := by positivity
  -- `1 + |log ρ| ≤ (1 + a) log L`
  have hlogρ : 1 + |Real.log ρ| ≤ (1 + a) * Real.log L := by
    have h1 : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    rw [abs_of_nonpos h1, hρ, Real.log_mul (by norm_num) hLna_pos.ne', Real.log_rpow hL0]
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  -- `ρ^{σ-1} L^{-a} = 2^{σ-1} L^{-σ a}`
  have e1 : ρ ^ (σ - 1) * L ^ (-a) = 2 ^ (σ - 1) * L ^ (-(σ * a)) := by
    rw [hρ, Real.mul_rpow (by norm_num) hLna_pos.le, ← Real.rpow_mul hL0.le,
      mul_assoc, ← Real.rpow_add hL0]
    congr 2; ring
  have e2 : (2 * ρ) ^ σ * (1 / ρ) = 2 ^ σ * ρ ^ (σ - 1) := by
    rw [Real.mul_rpow (by norm_num) hρ0.le, Real.rpow_sub_one hρ0.ne']
    field_simp
  have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
    calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
      _ = 2 := by simp
  have h2σ1 : (2 : ℝ) ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2pos : 0 < (2 : ℝ) ^ σ := by positivity
  -- `Λ ≤ 3 C_h ρ^{σ-1}(1+|log ρ|)`
  have hΛ : Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) +
      Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ) ≤ 3 * (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|)) := by
    have : Ch * (2 * ρ) ^ σ * (1 + |Real.log ρ|) * (1 / ρ) =
        Ch * ((2 * ρ) ^ σ * (1 / ρ)) * (1 + |Real.log ρ|) := by ring
    rw [this, e2]
    have h0 : 0 ≤ Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|) := by positivity
    have : Ch * (2 ^ σ * ρ ^ (σ - 1)) * (1 + |Real.log ρ|) =
        2 ^ σ * (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|)) := by ring
    rw [this]
    nlinarith
  have hQl : 1 + Q * Real.log L ≤ (1 + Q) * Real.log L := by nlinarith
  have hΛ0 : 0 ≤ 3 * (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|)) := by positivity
  have hP : 0 < L ^ (-(σ * a / 3)) := Real.rpow_pos_of_pos hL0 _
  -- main chain
  calc _ ≤ (3 * (Ch * ρ ^ (σ - 1) * (1 + |Real.log ρ|))) * (L ^ (-a) * (1 + Q * Real.log L)) :=
        mul_le_mul_of_nonneg_right hΛ (by positivity)
    _ ≤ (3 * (Ch * ρ ^ (σ - 1) * ((1 + a) * Real.log L))) * (L ^ (-a) * ((1 + Q) * Real.log L)) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlogρ (by positivity)) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hQl hLna_pos.le
    _ = 3 * Ch * (1 + a) * (1 + Q) * (2 ^ (σ - 1) * L ^ (-(σ * a))) * (Real.log L) ^ 2 := by
        rw [← e1]; ring
    _ ≤ 3 * Ch * (1 + a) * (1 + Q) * (L ^ (-(σ * a))) * (Real.log L) ^ 2 := by
        have : 0 ≤ 3 * Ch * (1 + a) * (1 + Q) * L ^ (-(σ * a)) * Real.log L ^ 2 := by positivity
        nlinarith [mul_nonneg this (show 0 ≤ 1 - (2 : ℝ) ^ (σ - 1) by linarith)]
    _ ≤ 3 * Ch * (1 + a) * (1 + Q) * (L ^ (-(σ * a))) * (9 / (σ * a) ^ 2 * L ^ (2 * σ * a / 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h3 := log_le_pow hL (show 0 < σ * a / 3 by positivity)
        have h4 : (Real.log L) ^ 2 ≤ (L ^ (σ * a / 3) / (σ * a / 3)) ^ 2 :=
          pow_le_pow_left₀ hlogn h3 2
        refine h4.trans (le_of_eq ?_)
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        field_simp
        norm_num
    _ = (3 * Ch * (1 + a) * (1 + Q) * (9 / (σ * a) ^ 2)) * L ^ (-(σ * a / 3)) := by
        have : L ^ (-(σ * a)) * L ^ (2 * σ * a / 3) = L ^ (-(σ * a / 3)) := by
          rw [← Real.rpow_add hL0]; congr 1; ring
        calc _ = (3 * Ch * (1 + a) * (1 + Q) * (9 / (σ * a) ^ 2)) * (L ^ (-(σ * a)) * L ^ (2 * σ * a / 3)) := by ring
          _ = _ := by rw [this]
    _ ≤ _ := by nlinarith

end FormalResearch.Special.TraceCore
