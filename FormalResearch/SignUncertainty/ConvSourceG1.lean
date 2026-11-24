module

public import FormalResearch.SignUncertainty.ConvSourceDefs
public import FormalResearch.Special.AiryKernelOpSharp
public import FormalResearch.Special.AiryRankDecayTail

/-!
# Global bounds and positivity of `g₁ = ceG1 (airyZero 1)` (M6)

With `a₁ = airyZero 1 < 0` and `g₁(u) = (Ai(u) / (u - a₁))²` (away from `a₁`), this module proves
the three facts about `g₁` used in the proof of Lemma `O.12` (`ceo:conv`):

* `g₁ ≥ 0` everywhere and `g₁ > 0` on `[a₁, ∞)`;
* the global polynomial bound `g₁(u) ≤ C (1 + |u|)^(-5/2)` on `ℝ`;
* the moment `u ↦ |u| g₁(u)` is integrable.

The left tail uses `|Ai u| ≤ 3 (1 + |u|)^(-1/4)` for `u ≤ 0`, the right tail uses
`Ai(u)² ≤ 9 e⁴ e^{-u}` for `u ≥ 0`, and the window `[a₁ - 1, 1]` is compact.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `g₁ = ceG1 (airyZero 1)` is nonnegative, being a square. -/
lemma convG1_nonneg (u : ℝ) : 0 ≤ ceG1 (airyZero 1) u := by
  unfold ceG1; exact sq_nonneg _

/-- Away from `a₁`, `g₁(u) = Ai(u)² / (u - a₁)²`. -/
lemma convG1_eq_div {u : ℝ} (hu : u ≠ airyZero 1) :
    ceG1 (airyZero 1) u = airyAi u ^ 2 / (u - airyZero 1) ^ 2 := by
  unfold ceG1
  rw [dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero, div_pow]

/-- `Ai'(a₁) ≠ 0`, since `a₁` is a simple zero of `Ai`. -/
lemma convG1_airyDeriv_ne : airyAi' (airyZero 1) ≠ 0 :=
  fun h => airyAi_ne_zero_of_deriv_zero h (airyAi_airyZero 1)

/-- `g₁(u) > 0` for `u ≥ a₁` (at `a₁`, `g₁ = Ai'(a₁)²`). -/
lemma convG1_pos_of_ge {u : ℝ} (hu : airyZero 1 ≤ u) : 0 < ceG1 (airyZero 1) u := by
  rcases eq_or_lt_of_le hu with h | h
  · subst h
    unfold ceG1
    rw [dslope_same, (hasDerivAt_airyAi _).deriv]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 convG1_airyDeriv_ne))
  · rw [convG1_eq_div h.ne']
    exact div_pos (pow_pos (airyAi_pos_of_gt_first h) 2) (pow_pos (sub_pos.mpr h) 2)

/-- `x ^ (-5/2) = x ^ (-1/2) · (x²)⁻¹` for `x > 0`. -/
lemma convG1_rpow_split {x : ℝ} (hx : 0 < x) :
    x ^ (-(5 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * (x ^ 2)⁻¹ := by
  rw [show (-(5 / 2 : ℝ)) = -(1 / 2 : ℝ) + -(2 : ℝ) by norm_num, Real.rpow_add hx,
    Real.rpow_neg hx.le (2 : ℝ), Real.rpow_two]

/-- `Ai(u)² ≤ 9 (1 + |u|)^(-1/2)` for `u ≤ 0`. -/
lemma convG1_sq_airyAi_le {u : ℝ} (hu : u ≤ 0) :
    airyAi u ^ 2 ≤ 9 * (1 + |u|) ^ (-(1 / 2 : ℝ)) := by
  have h := abs_airyAi_le_of_nonpos hu
  have hx : 0 < 1 + |u| := by positivity
  have hpow : ((1 + |u|) ^ (-(1 / 4 : ℝ))) ^ 2 = (1 + |u|) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hnn : 0 ≤ |airyAi u| := abs_nonneg _
  have hsq : |airyAi u| ^ 2 ≤ (3 * (1 + |u|) ^ (-(1 / 4 : ℝ))) ^ 2 := by
    nlinarith [h, hnn]
  rw [sq_abs, mul_pow, hpow] at hsq
  nlinarith [hsq]

/-- Quotient bound: if `N ≤ c P`, `x² ≤ K D`, `D > 0`, then `N / D ≤ c K (P (x²)⁻¹)`. -/
lemma convG1_div_bound {N c P D x K : ℝ} (hN : N ≤ c * P) (hP : 0 ≤ P) (hc : 0 ≤ c)
    (hD : 0 < D) (hx : 0 < x) (hK : x ^ 2 ≤ K * D) :
    N / D ≤ c * K * (P * (x ^ 2)⁻¹) := by
  have hq : x ^ 2 * (x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_pos hx 2).ne'
  have hKq : 1 ≤ K * D * (x ^ 2)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hK (inv_nonneg.mpr (sq_nonneg x))
    linarith
  have h1 : c * P ≤ c * P * (K * D * (x ^ 2)⁻¹) := by
    have h := mul_le_mul_of_nonneg_left hKq (mul_nonneg hc hP)
    linarith
  rw [div_le_iff₀ hD]
  nlinarith [h1, hN]

/-- Left tail: for `u ≤ a₁ - 1`, `g₁(u) ≤ 9 (2 + |a₁|)² (1 + |u|)^(-5/2)`. -/
lemma convG1_left {u : ℝ} (hu : u ≤ airyZero 1 - 1) :
    ceG1 (airyZero 1) u ≤ 9 * (2 + |airyZero 1|) ^ 2 * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
  have ha : airyZero 1 < 0 := airyZero_neg 1
  have hne : u ≠ airyZero 1 := by intro h; linarith
  have hu0 : u ≤ 0 := by linarith
  have hD : 0 < (u - airyZero 1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
  have hx : 0 < 1 + |u| := by positivity
  have hxle : 1 + |u| ≤ (2 + |airyZero 1|) * (airyZero 1 - u) := by
    rw [abs_of_nonpos hu0, abs_of_neg ha]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - airyZero 1)
      (by linarith : (0 : ℝ) ≤ airyZero 1 - u - 1)]
  have hK : (1 + |u|) ^ 2 ≤ (2 + |airyZero 1|) ^ 2 * (u - airyZero 1) ^ 2 := by
    have h := mul_le_mul hxle hxle hx.le (le_trans hx.le hxle)
    nlinarith [h]
  rw [convG1_eq_div hne, convG1_rpow_split hx]
  exact convG1_div_bound (convG1_sq_airyAi_le hu0) (Real.rpow_nonneg hx.le _) (by norm_num)
    hD hx hK

/-- `e^{-u} ≤ (1 + u)^(-1/2)` for `u ≥ 0`. -/
lemma convG1_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ (1 + u) ^ (-(1 / 2 : ℝ)) := by
  have hx : 0 < 1 + u := by linarith
  have hs : 0 < (1 + u) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hr : (1 + u) ^ (1 / 2 : ℝ) ≤ 1 + u := by
    calc (1 + u) ^ (1 / 2 : ℝ) ≤ (1 + u) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 1 + u := Real.rpow_one _
  have hxe : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hmul : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hE : Real.exp (-u) * (1 + u) ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 : (1 + u) * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hxe (Real.exp_pos _).le
    have h2 : Real.exp (-u) * (1 + u) ^ (1 / 2 : ℝ) ≤ Real.exp (-u) * (1 + u) :=
      mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
    nlinarith [h1, h2, hmul]
  have hinv := mul_inv_cancel₀ hs.ne'
  rw [Real.rpow_neg hx.le]
  calc Real.exp (-u) = Real.exp (-u) * ((1 + u) ^ (1 / 2 : ℝ) * ((1 + u) ^ (1 / 2 : ℝ))⁻¹) := by
        rw [hinv, mul_one]
    _ = (Real.exp (-u) * (1 + u) ^ (1 / 2 : ℝ)) * ((1 + u) ^ (1 / 2 : ℝ))⁻¹ := by ring
    _ ≤ 1 * ((1 + u) ^ (1 / 2 : ℝ))⁻¹ := mul_le_mul_of_nonneg_right hE (inv_nonneg.mpr hs.le)
    _ = ((1 + u) ^ (1 / 2 : ℝ))⁻¹ := one_mul _

/-- Right tail: for `u ≥ 1`, `g₁(u) ≤ 9 e⁴ · 4 · (1 + |u|)^(-5/2)`. -/
lemma convG1_right {u : ℝ} (hu : 1 ≤ u) :
    ceG1 (airyZero 1) u ≤ 9 * Real.exp 4 * 4 * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
  have ha : airyZero 1 < 0 := airyZero_neg 1
  have h0 : 0 ≤ u := by linarith
  rw [abs_of_nonneg h0]
  have hne : u ≠ airyZero 1 := by intro h; linarith
  have hD : 0 < (u - airyZero 1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
  have hx : 0 < 1 + u := by linarith
  have hN : airyAi u ^ 2 ≤ 9 * Real.exp 4 * (1 + u) ^ (-(1 / 2 : ℝ)) := by
    have h1 := airyAi_sq_le_exp u
    have h2 := convG1_exp_neg_le h0
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hK : (1 + u) ^ 2 ≤ 4 * (u - airyZero 1) ^ 2 := by
    have h : 1 + u ≤ 2 * (u - airyZero 1) := by linarith
    have h' := mul_le_mul h h hx.le (by linarith)
    nlinarith [h']
  rw [convG1_eq_div hne, convG1_rpow_split hx]
  exact convG1_div_bound hN (Real.rpow_nonneg hx.le _) (by positivity) hD hx hK

/-- Middle window: `g ≤ M₀` and `x ≤ L` give `g ≤ M₀ L^(5/2) x^(-5/2)`. -/
lemma convG1_middle {x L M₀ g : ℝ} (hx : 0 < x) (hxL : x ≤ L) (hM₀ : 0 ≤ M₀)
    (hg : g ≤ M₀) : g ≤ M₀ * L ^ (5 / 2 : ℝ) * x ^ (-(5 / 2 : ℝ)) := by
  have hz : x ^ (5 / 2 : ℝ) ≤ L ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hx.le hxL (by norm_num)
  have hyz : x ^ (-(5 / 2 : ℝ)) * x ^ (5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx]; norm_num
  have hP : 0 ≤ x ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  have h3 : M₀ * x ^ (-(5 / 2 : ℝ)) * x ^ (5 / 2 : ℝ) ≤ M₀ * x ^ (-(5 / 2 : ℝ)) * L ^ (5 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hz (mul_nonneg hM₀ hP)
  have h4 : M₀ * x ^ (-(5 / 2 : ℝ)) * x ^ (5 / 2 : ℝ) = M₀ := by
    rw [mul_assoc, hyz, mul_one]
  calc g ≤ M₀ := hg
    _ = M₀ * x ^ (-(5 / 2 : ℝ)) * x ^ (5 / 2 : ℝ) := h4.symm
    _ ≤ M₀ * x ^ (-(5 / 2 : ℝ)) * L ^ (5 / 2 : ℝ) := h3
    _ = M₀ * L ^ (5 / 2 : ℝ) * x ^ (-(5 / 2 : ℝ)) := by ring

/-- **Global polynomial bound:** `g₁(u) ≤ C (1 + |u|)^(-5/2)` for all `u ∈ ℝ`. -/
theorem convG1_le_poly : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, ceG1 (airyZero 1) u ≤ C * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
  have ha : airyZero 1 < 0 := airyZero_neg 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := airyZero 1 - 1) (b := 1)).exists_bound_of_continuousOn
    (continuous_ceG1 (airyZero 1)).continuousOn
  have hM₀ : 0 ≤ |M| := abs_nonneg M
  have hD1 : 0 ≤ 9 * (2 + |airyZero 1|) ^ 2 := by positivity
  have hD2 : 0 ≤ 9 * Real.exp 4 * 4 := by positivity
  have hD3 : 0 ≤ |M| * (2 + |airyZero 1|) ^ (5 / 2 : ℝ) := by positivity
  refine ⟨9 * (2 + |airyZero 1|) ^ 2 + 9 * Real.exp 4 * 4 + |M| * (2 + |airyZero 1|) ^ (5 / 2 : ℝ) + 1,
    by linarith, fun u => ?_⟩
  have hP : 0 ≤ (1 + |u|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  rcases le_or_gt u (airyZero 1 - 1) with h1 | h1
  · exact le_trans (convG1_left h1) (mul_le_mul_of_nonneg_right (by linarith) hP)
  rcases le_or_gt 1 u with h2 | h2
  · exact le_trans (convG1_right h2) (mul_le_mul_of_nonneg_right (by linarith) hP)
  · have hg : ceG1 (airyZero 1) u ≤ |M| := by
      have h := hM u ⟨h1.le, h2.le⟩
      rw [Real.norm_of_nonneg (convG1_nonneg u)] at h
      exact h.trans (le_abs_self M)
    have hab : |airyZero 1| = -airyZero 1 := abs_of_neg ha
    have hxL : 1 + |u| ≤ 2 + |airyZero 1| := by
      have hu' : |u| ≤ |airyZero 1| + 1 := by
        rw [abs_le, hab]; constructor <;> linarith
      linarith
    have hx : 0 < 1 + |u| := by positivity
    exact le_trans (convG1_middle hx hxL hM₀ hg) (mul_le_mul_of_nonneg_right (by linarith) hP)

/-- **Moment:** `u ↦ |u| g₁(u)` is integrable. -/
theorem convG1_moment_integrable : Integrable (fun u : ℝ => |u| * ceG1 (airyZero 1) u) := by
  obtain ⟨C, hCpos, hC⟩ := convG1_le_poly
  have hint : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)
  refine Integrable.mono' (hint.const_mul C)
    (continuous_abs.mul (continuous_ceG1 (airyZero 1))).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  show ‖|u| * ceG1 (airyZero 1) u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ))
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (abs_nonneg u) (convG1_nonneg u))]
  have hx : 0 < 1 + |u| := by positivity
  have hsplit : (1 + |u|) ^ (-(3 / 2 : ℝ)) = (1 + |u|) * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
    rw [show (-(3 / 2 : ℝ)) = 1 + -(5 / 2 : ℝ) by norm_num, Real.rpow_add hx, Real.rpow_one]
  rw [hsplit]
  calc |u| * ceG1 (airyZero 1) u ≤ (1 + |u|) * (C * (1 + |u|) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (by linarith [abs_nonneg u]) (hC u) (convG1_nonneg u) hx.le
    _ = C * ((1 + |u|) * (1 + |u|) ^ (-(5 / 2 : ℝ))) := by ring

/-- info: 'FormalResearch.SignUncertainty.convG1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_nonneg

/-- info: 'FormalResearch.SignUncertainty.convG1_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_eq_div

/-- info: 'FormalResearch.SignUncertainty.convG1_airyDeriv_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_airyDeriv_ne

/-- info: 'FormalResearch.SignUncertainty.convG1_pos_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_pos_of_ge

/-- info: 'FormalResearch.SignUncertainty.convG1_rpow_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_rpow_split

/-- info: 'FormalResearch.SignUncertainty.convG1_sq_airyAi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_sq_airyAi_le

/-- info: 'FormalResearch.SignUncertainty.convG1_div_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_div_bound

/-- info: 'FormalResearch.SignUncertainty.convG1_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_left

/-- info: 'FormalResearch.SignUncertainty.convG1_exp_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_exp_neg_le

/-- info: 'FormalResearch.SignUncertainty.convG1_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_right

/-- info: 'FormalResearch.SignUncertainty.convG1_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_middle

/-- info: 'FormalResearch.SignUncertainty.convG1_le_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_le_poly

/-- info: 'FormalResearch.SignUncertainty.convG1_moment_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convG1_moment_integrable

end FormalResearch.SignUncertainty
