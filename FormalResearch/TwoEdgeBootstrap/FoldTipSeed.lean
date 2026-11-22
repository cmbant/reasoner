module

public import FormalResearch.Special.AiryClarkLabel
public import FormalResearch.Special.AiryCftQNCUnc
public import FormalResearch.Special.AiryCft2FirstDerivZero
public import FormalResearch.Special.AiryCftSignUncertainty
public import FormalResearch.Special.AiryCftSignEqualityDiv
public import FormalResearch.Special.AiryCftSignEqualityMain
public import FormalResearch.Special.AiryThm47Liouville
public import FormalResearch.Special.AiryThm47Div
public import FormalResearch.Special.AiryThm47Poly
public import FormalResearch.Special.AiryKernelOpSharp
public import FormalResearch.Special.AiryFirstZeros


/-!
# Fold-Tip Seed Lemma (`fold_tip_theorem.tex`, Lemma `ft:seed`)

For `0 < δ ≤ 1/2` and `0 < η < δ / |a₁'|` (where `a₁'` = `airyFirstDerivZero` is the largest zero
of `Ai'`), defines `F_{δ,η}(u) = Ai(u)² (a₁ - δ - u) / (u - a₁)² + η · Ai'(u)² / (u - a₁')²`
(`foldTipSeed δ η`) and proves `fold_tip_seed_lemma`: `F_{δ,η} ∈ 𝒢_{-3/2}`, `∫ F_{δ,η} = -δ + η |a₁'| < 0`,
and `c (1 + |u|)^(-3/2) ≤ F_{δ,η}(u)` on `(-∞, a₁ - δ]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.TwoEdgeBootstrap

open FormalResearch.Special

private lemma norm_sub_ofReal_ge {t : ℝ} {u : ℂ} (hu : |t| + 1 ≤ ‖u‖) :
    1 + ‖u‖ ≤ (2 + |t|) * ‖u - (t : ℂ)‖ ∧ u ≠ (t : ℂ) := by
  have ht : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : 1 ≤ ‖u - (t : ℂ)‖ := by
    have := norm_sub_norm_le u (t : ℂ)
    rw [ht] at this
    linarith
  have hne : u ≠ (t : ℂ) := fun h => by rw [h, sub_self, norm_zero] at h1; linarith
  have h2 : ‖u‖ ≤ ‖u - (t : ℂ)‖ + |t| := by
    have := norm_add_le (u - (t : ℂ)) (t : ℂ)
    rw [sub_add_cancel, ht] at this
    exact this
  refine ⟨?_, hne⟩
  nlinarith [abs_nonneg t]


/-! ### Part 2: Fold-tip Seed Lemma (`fold_tip_theorem.tex`, `ft:seed`) -/

/-- The largest zero `a₁'` of `Ai'` (`a₁ < a₁' < 0`, `a₁' ≈ -1.0188`). -/
noncomputable def airyFirstDerivZero : ℝ := Classical.choose airyDeriv_largest_zero

lemma airyZero_lt_airyFirstDerivZero : airyZero 1 < airyFirstDerivZero :=
  (Classical.choose_spec airyDeriv_largest_zero).1

lemma airyFirstDerivZero_neg : airyFirstDerivZero < 0 :=
  (Classical.choose_spec airyDeriv_largest_zero).2.1

lemma airyAi'_airyFirstDerivZero : airyAi' airyFirstDerivZero = 0 :=
  (Classical.choose_spec airyDeriv_largest_zero).2.2.1

lemma le_airyFirstDerivZero {y : ℝ} (hy : airyAi' y = 0) : y ≤ airyFirstDerivZero :=
  (Classical.choose_spec airyDeriv_largest_zero).2.2.2 y hy

lemma airyFirstDerivZero_sum_sq :
    HasSum (fun n : ℕ => ((airyZero (n + 1) - airyFirstDerivZero) ^ 2)⁻¹) |airyFirstDerivZero| := by
  have h := airyZero_sum_sq_of_deriv_zero airyAi'_airyFirstDerivZero
  rw [abs_of_neg airyFirstDerivZero_neg]
  convert h using 2 with n
  rw [← neg_sub, neg_sq]

/-- The entire complex fold-tip seed function
`F_{δ,η}(u) = Ai(u)² (a₁ - δ - u) / (u - a₁)² + η · Ai'(u)² / (u - a₁')²`,
defined via `dslope` so `Differentiable ℂ` holds directly. -/
noncomputable def foldTipSeed (δ η : ℝ) (u : ℂ) : ℂ :=
  dslope airyAiC (airyZero 1 : ℂ) u ^ 2 * (((airyZero 1 - δ : ℝ) : ℂ) - u) +
    (η : ℂ) * dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) u ^ 2

theorem differentiable_foldTipSeed (δ η : ℝ) : Differentiable ℂ (foldTipSeed δ η) := by
  unfold foldTipSeed
  have hd1 := EntireDiv.differentiable_dslope_entire differentiable_airyAiC (airyZero 1 : ℂ)
  have hd2 := EntireDiv.differentiable_dslope_entire differentiable_airyAiC.deriv (airyFirstDerivZero : ℂ)
  exact ((hd1.pow 2).mul (differentiable_const _ |>.sub differentiable_id)).add ((hd2.pow 2).const_mul _)

lemma foldTipSeed_eq (δ η : ℝ) {u : ℂ} (h1 : u ≠ (airyZero 1 : ℂ))
    (h2 : u ≠ (airyFirstDerivZero : ℂ)) :
    foldTipSeed δ η u =
      airyAiC u ^ 2 * (((airyZero 1 - δ : ℝ) : ℂ) - u) / (u - (airyZero 1 : ℂ)) ^ 2 +
        (η : ℂ) * (deriv airyAiC u ^ 2 / (u - (airyFirstDerivZero : ℂ)) ^ 2) := by
  have ha1 : airyAiC (airyZero 1 : ℂ) = 0 := by rw [airyAiC_ofReal, airyAi_airyZero]; simp
  have ha1' : deriv airyAiC (airyFirstDerivZero : ℂ) = 0 := by
    rw [deriv_airyAiC_ofReal, airyAi'_airyFirstDerivZero]; simp
  unfold foldTipSeed
  have hd1 : u - (airyZero 1 : ℂ) ≠ 0 := sub_ne_zero.mpr h1
  have hd2 : u - (airyFirstDerivZero : ℂ) ≠ 0 := sub_ne_zero.mpr h2
  rw [dslope_of_ne _ h1, dslope_of_ne _ h2, slope_def_field, slope_def_field, ha1, ha1',
    sub_zero, sub_zero]
  field_simp

lemma foldTipSeed_ofReal_im (δ η x : ℝ) : (foldTipSeed δ η (x : ℂ)).im = 0 := by
  have h1r : (dslope airyAiC (airyZero 1 : ℂ) (x : ℂ)).im = 0 := by
    by_cases hx : x = airyZero 1
    · rw [hx, dslope_same, deriv_airyAiC_ofReal, Complex.ofReal_im]
    · have hxc : (x : ℂ) ≠ (airyZero 1 : ℂ) := fun h => hx (Complex.ofReal_injective h)
      have ha1 : airyAiC (airyZero 1 : ℂ) = 0 := by rw [airyAiC_ofReal, airyAi_airyZero]; simp
      rw [dslope_of_ne _ hxc, slope_def_field, ha1, sub_zero, airyAiC_ofReal,
        ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_im]
  have h2r : (dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) (x : ℂ)).im = 0 := by
    by_cases hx : x = airyFirstDerivZero
    · rw [hx, dslope_same]
      have hd2 : deriv (deriv airyAiC) (airyFirstDerivZero : ℂ) =
          (airyFirstDerivZero : ℂ) * airyAiC (airyFirstDerivZero : ℂ) :=
        (hasDerivAt_deriv_airyAiC (airyFirstDerivZero : ℂ)).deriv
      rw [hd2, airyAiC_ofReal, ← Complex.ofReal_mul, Complex.ofReal_im]
    · have hxc : (x : ℂ) ≠ (airyFirstDerivZero : ℂ) := fun h => hx (Complex.ofReal_injective h)
      have ha1' : deriv airyAiC (airyFirstDerivZero : ℂ) = 0 := by
        rw [deriv_airyAiC_ofReal, airyAi'_airyFirstDerivZero]; simp
      rw [dslope_of_ne _ hxc, slope_def_field, ha1', sub_zero, deriv_airyAiC_ofReal,
        ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_im]
  have e1 : dslope airyAiC (airyZero 1 : ℂ) (x : ℂ) =
      (((dslope airyAiC (airyZero 1 : ℂ) (x : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl h1r
  have e2 : dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) (x : ℂ) =
      (((dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) (x : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext rfl h2r
  unfold foldTipSeed
  rw [e1, e2]
  have ec : (((((dslope airyAiC (airyZero 1 : ℂ) (x : ℂ)).re : ℝ) : ℂ) ^ 2 *
        (((airyZero 1 - δ : ℝ) : ℂ) - (x : ℂ)) +
      (η : ℂ) * (((dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) (x : ℂ)).re : ℝ) : ℂ) ^ 2)) =
      ((((dslope airyAiC (airyZero 1 : ℂ) (x : ℂ)).re ^ 2 * (airyZero 1 - δ - x) +
        η * (dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) (x : ℂ)).re ^ 2 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [ec, Complex.ofReal_im]

lemma foldTipSeed_re_of_ne (δ η : ℝ) {x : ℝ} (h1 : x ≠ airyZero 1)
    (h2 : x ≠ airyFirstDerivZero) :
    (foldTipSeed δ η (x : ℂ)).re =
      airyAi x ^ 2 * (airyZero 1 - δ - x) / (x - airyZero 1) ^ 2 +
        η * (airyAi' x ^ 2 / (x - airyFirstDerivZero) ^ 2) := by
  have h1c : (x : ℂ) ≠ (airyZero 1 : ℂ) := fun h => h1 (Complex.ofReal_injective h)
  have h2c : (x : ℂ) ≠ (airyFirstDerivZero : ℂ) := fun h => h2 (Complex.ofReal_injective h)
  rw [foldTipSeed_eq δ η h1c h2c, airyAiC_ofReal, deriv_airyAiC_ofReal]
  have e : ((((airyAi x : ℝ) : ℂ) ^ 2 * (((airyZero 1 - δ : ℝ) : ℂ) - (x : ℂ)) /
          ((x : ℂ) - (airyZero 1 : ℂ)) ^ 2 +
        (η : ℂ) * (((airyAi' x : ℝ) : ℂ) ^ 2 / ((x : ℂ) - (airyFirstDerivZero : ℂ)) ^ 2))) =
      (((airyAi x ^ 2 * (airyZero 1 - δ - x) / (x - airyZero 1) ^ 2 +
          η * (airyAi' x ^ 2 / (x - airyFirstDerivZero) ^ 2) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_re]

/-- **Class membership `F_{δ,η} ∈ 𝒢_{-3/2}`**: `‖F_{δ,η}(u)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)` on `ℂ`. -/
theorem foldTipSeed_bound (δ η : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖foldTipSeed δ η u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by
  set a₁ := airyZero 1 with ha₁
  set a₁' := airyFirstDerivZero with ha₁'
  set B : ℝ := max (|a₁| + 1) (|a₁'| + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn
    (differentiable_foldTipSeed δ η).continuous.continuousOn
  set e0 : ℝ := Real.exp (-(4 / 3) * B ^ (3 / 2 : ℝ)) with he0
  set m1 : ℝ := min 1 ((1 + B) ^ (-(3 / 2) : ℝ)) with hm1
  have he0p : 0 < e0 := Real.exp_pos _
  have hm1p : 0 < m1 := lt_min one_pos (Real.rpow_pos_of_pos (by linarith) _)
  set C₀ : ℝ := 9 * (1 + |a₁ - δ|) * (2 + |a₁|) ^ 2 + |η| * 25 * (2 + |a₁'|) ^ 2 with hC₀
  refine ⟨max C₀ (|M| / (m1 * e0)), by positivity, fun u => ?_⟩
  by_cases hu : ‖u‖ ≤ B
  · have h1 : ‖foldTipSeed δ η u‖ ≤ |M| := (hM u (by simpa using hu)).trans (le_abs_self _)
    have h2 : m1 * e0 ≤ (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u :=
      mul_le_mul (at47_rpow_lower hu) (at47_env_lower hu hB0) he0p.le
        (Real.rpow_nonneg (by linarith [norm_nonneg u]) _)
    have h3 : |M| ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    calc ‖foldTipSeed δ η u‖ ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) :=
          h1.trans h3
      _ ≤ max C₀ (|M| / (m1 * e0)) * ((1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg (Real.rpow_nonneg (by positivity) _) (airyEnv_pos u).le)
      _ = _ := by ring
  · replace hu := not_le.mp hu
    obtain ⟨hg1, hne1⟩ := norm_sub_ofReal_ge (t := a₁) (u := u)
      (by linarith [le_max_left (|a₁| + 1) (|a₁'| + 1)])
    obtain ⟨hg2, hne2⟩ := norm_sub_ofReal_ge (t := a₁') (u := u)
      (by linarith [le_max_right (|a₁| + 1) (|a₁'| + 1)])
    rw [foldTipSeed_eq δ η hne1 hne2]
    have he_pos : 0 ≤ airyEnv u := (airyEnv_pos u).le
    have hx : 0 < 1 + ‖u‖ := by positivity
    have hden1 : 0 < ‖u - (a₁ : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne1)
    have hden2 : 0 < ‖u - (a₁' : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne2)
    have hinv1 : (‖u - (a₁ : ℂ)‖ ^ 2)⁻¹ ≤ (2 + |a₁|) ^ 2 * (1 + ‖u‖) ^ (-2 : ℝ) := by
      have hsq : (1 + ‖u‖) ^ 2 ≤ (2 + |a₁|) ^ 2 * ‖u - (a₁ : ℂ)‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hx.le hg1 2
      have hpow2 : (1 + ‖u‖) ^ (-2 : ℝ) = ((1 + ‖u‖) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hpow2, ← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hinv2 : (‖u - (a₁' : ℂ)‖ ^ 2)⁻¹ ≤ (2 + |a₁'|) ^ 2 * (1 + ‖u‖) ^ (-2 : ℝ) := by
      have hsq : (1 + ‖u‖) ^ 2 ≤ (2 + |a₁'|) ^ 2 * ‖u - (a₁' : ℂ)‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hx.le hg2 2
      have hpow2 : (1 + ‖u‖) ^ (-2 : ℝ) = ((1 + ‖u‖) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hpow2, ← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hlin : ‖((a₁ - δ : ℝ) : ℂ) - u‖ ≤ (1 + |a₁ - δ|) * (1 + ‖u‖) := by
      calc ‖((a₁ - δ : ℝ) : ℂ) - u‖ ≤ ‖((a₁ - δ : ℝ) : ℂ)‖ + ‖u‖ := norm_sub_le _ _
        _ = |a₁ - δ| + ‖u‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (1 + |a₁ - δ|) * (1 + ‖u‖) := by nlinarith [abs_nonneg (a₁ - δ), norm_nonneg u]
    have hA : ‖airyAiC u‖ ^ 2 ≤ 9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u := airyAiC_norm_sq_le u
    have hD : ‖deriv airyAiC u‖ ^ 2 ≤ 25 * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
      have hd := airyAiC_deriv_envelope u
      have hdsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
      refine hdsq.trans (le_of_eq ?_)
      have e1 : ((1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 = (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
      have e2 : (Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) ^ 2 = airyEnv u := by
        rw [airyEnv, ← Real.exp_nat_mul]; norm_num; ring_nf
      calc (5 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) ^ 2
          = 25 * ((1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 * (Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) ^ 2 := by
            ring
        _ = _ := by rw [e1, e2]
    have hp1 : (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (1 + ‖u‖) * (1 + ‖u‖) ^ (-2 : ℝ) =
        (1 + ‖u‖) ^ (-(3 / 2) : ℝ) := by
      calc (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (1 + ‖u‖) * (1 + ‖u‖) ^ (-2 : ℝ)
          = (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (1 + ‖u‖) ^ (1 : ℝ) * (1 + ‖u‖) ^ (-2 : ℝ) := by
            rw [Real.rpow_one]
        _ = (1 + ‖u‖) ^ (-(1 / 2) + 1 + (-2 : ℝ)) := by
            rw [← Real.rpow_add hx, ← Real.rpow_add hx]
        _ = (1 + ‖u‖) ^ (-(3 / 2) : ℝ) := by norm_num
    have hp2 : (1 + ‖u‖) ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (-2 : ℝ) = (1 + ‖u‖) ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    have hT1 : ‖airyAiC u ^ 2 * (((a₁ - δ : ℝ) : ℂ) - u) / (u - (a₁ : ℂ)) ^ 2‖ ≤
        9 * (1 + |a₁ - δ|) * (2 + |a₁|) ^ 2 * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by
      rw [norm_div, norm_mul, norm_pow, norm_pow, div_eq_mul_inv]
      calc ‖airyAiC u‖ ^ 2 * ‖((a₁ - δ : ℝ) : ℂ) - u‖ * (‖u - (a₁ : ℂ)‖ ^ 2)⁻¹
          ≤ ((9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u) * ((1 + |a₁ - δ|) * (1 + ‖u‖))) *
              ((2 + |a₁|) ^ 2 * (1 + ‖u‖) ^ (-2 : ℝ)) :=
            mul_le_mul (mul_le_mul hA hlin (norm_nonneg _) (by positivity)) hinv1 (by positivity)
              (by positivity)
        _ = 9 * (1 + |a₁ - δ|) * (2 + |a₁|) ^ 2 *
              ((1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (1 + ‖u‖) * (1 + ‖u‖) ^ (-2 : ℝ)) * airyEnv u := by ring
        _ = _ := by rw [hp1]
    have hT2 : ‖(η : ℂ) * (deriv airyAiC u ^ 2 / (u - (a₁' : ℂ)) ^ 2)‖ ≤
        |η| * 25 * (2 + |a₁'|) ^ 2 * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by
      rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
      calc |η| * (‖deriv airyAiC u‖ ^ 2 * (‖u - (a₁' : ℂ)‖ ^ 2)⁻¹)
          ≤ |η| * ((25 * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u) *
              ((2 + |a₁'|) ^ 2 * (1 + ‖u‖) ^ (-2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hD hinv2 (by positivity) (by positivity))
              (abs_nonneg _)
        _ = |η| * 25 * (2 + |a₁'|) ^ 2 * ((1 + ‖u‖) ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (-2 : ℝ)) *
              airyEnv u := by ring
        _ = _ := by rw [hp2]
    calc ‖airyAiC u ^ 2 * (((a₁ - δ : ℝ) : ℂ) - u) / (u - (a₁ : ℂ)) ^ 2 +
            (η : ℂ) * (deriv airyAiC u ^ 2 / (u - (a₁' : ℂ)) ^ 2)‖
        ≤ ‖airyAiC u ^ 2 * (((a₁ - δ : ℝ) : ℂ) - u) / (u - (a₁ : ℂ)) ^ 2‖ +
            ‖(η : ℂ) * (deriv airyAiC u ^ 2 / (u - (a₁' : ℂ)) ^ 2)‖ := norm_add_le _ _
      _ ≤ 9 * (1 + |a₁ - δ|) * (2 + |a₁|) ^ 2 * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u +
            |η| * 25 * (2 + |a₁'|) ^ 2 * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := add_le_add hT1 hT2
      _ = C₀ * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by rw [hC₀]; ring
      _ ≤ max C₀ (|M| / (m1 * e0)) * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _)) he_pos

theorem foldTipSeed_integrable (δ η : ℝ) : Integrable (fun x : ℝ => foldTipSeed δ η (x : ℂ)) := by
  obtain ⟨C, hC, hb⟩ := foldTipSeed_bound δ η
  exact airy_integrable_real (differentiable_foldTipSeed δ η) hC (by norm_num) hb

/-- **Exact integral of the seed**: `∫_ℝ F_{δ,η} = -δ + η |a₁'|`. -/
theorem foldTipSeed_integral (δ η : ℝ) :
    (∫ x : ℝ, foldTipSeed δ η (x : ℂ)) = ((-δ + η * |airyFirstDerivZero| : ℝ) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := foldTipSeed_bound δ η
  have hsum := airyQ_hasSum_unc (differentiable_foldTipSeed δ η) (foldTipSeed_integrable δ η) hC hb
  have hterm : ∀ n : ℕ,
      foldTipSeed δ η (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 =
        (if n = 0 then (-δ : ℂ) else 0) +
          (η : ℂ) * (((((airyZero (n + 1) - airyFirstDerivZero) ^ 2)⁻¹ : ℝ) : ℂ)) := by
    intro n
    have ha1' : deriv airyAiC (airyFirstDerivZero : ℂ) = 0 := by
      rw [deriv_airyAiC_ofReal, airyAi'_airyFirstDerivZero]; simp
    have hne' : (airyZero (n + 1) : ℂ) ≠ (airyFirstDerivZero : ℂ) := by
      intro h
      have := Complex.ofReal_injective h
      have hle : airyZero (n + 1) ≤ airyZero 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | hp
        · exact le_rfl
        · exact (airyZero_lt_of_lt le_rfl (by omega)).le
      linarith [airyZero_lt_airyFirstDerivZero]
    have hdne : deriv airyAiC (airyZero (n + 1) : ℂ) ≠ 0 := airyZero_deriv_ne_zero (n + 1)
    have hT2 : (η : ℂ) * dslope (deriv airyAiC) (airyFirstDerivZero : ℂ) (airyZero (n + 1) : ℂ) ^ 2 /
          (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 =
        (η : ℂ) * (((((airyZero (n + 1) - airyFirstDerivZero) ^ 2)⁻¹ : ℝ) : ℂ)) := by
      rw [dslope_of_ne _ hne', slope_def_field, ha1', sub_zero]
      push_cast
      field_simp
    have hT1 : dslope airyAiC (airyZero 1 : ℂ) (airyZero (n + 1) : ℂ) ^ 2 *
          (((airyZero 1 - δ : ℝ) : ℂ) - (airyZero (n + 1) : ℂ)) /
          (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 =
        if n = 0 then (-δ : ℂ) else 0 := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp only [zero_add, ↓reduceIte, dslope_same]
        have : (((airyZero 1 - δ : ℝ) : ℂ) - (airyZero 1 : ℂ)) = (-δ : ℂ) := by push_cast; ring
        rw [this]
        field_simp
      · have hne0 : n ≠ 0 := hp.ne'
        have hne1 : (airyZero (n + 1) : ℂ) ≠ (airyZero 1 : ℂ) := by
          intro h
          have := Complex.ofReal_injective h
          have := airyZero_lt_of_lt le_rfl (by omega : 1 < n + 1)
          linarith
        have ha0 : airyAiC (airyZero (n + 1) : ℂ) = 0 := by rw [airyAiC_ofReal, airyAi_airyZero]; simp
        have ha1 : airyAiC (airyZero 1 : ℂ) = 0 := by rw [airyAiC_ofReal, airyAi_airyZero]; simp
        simp only [hne0, ↓reduceIte]
        rw [dslope_of_ne _ hne1, slope_def_field, ha0, ha1]
        simp
    unfold foldTipSeed
    rw [add_div, hT1, hT2]
  simp_rw [hterm] at hsum
  have hs1 : HasSum (fun n : ℕ => if n = 0 then (-δ : ℂ) else 0) (-δ : ℂ) :=
    hasSum_single 0 (fun b hb => by simp [hb])
  have hs2 : HasSum (fun n : ℕ => (η : ℂ) * (((((airyZero (n + 1) - airyFirstDerivZero) ^ 2)⁻¹ : ℝ) : ℂ)))
      ((η : ℂ) * ((|airyFirstDerivZero| : ℝ) : ℂ)) := by
    have h := Complex.ofRealCLM.hasSum airyFirstDerivZero_sum_sq
    exact h.mul_left (η : ℂ)
  have htot := hs1.add hs2
  have heq : (∫ x : ℝ, foldTipSeed δ η (x : ℂ)) =
      (-δ : ℂ) + (η : ℂ) * ((|airyFirstDerivZero| : ℝ) : ℂ) :=
    hsum.unique htot
  rw [heq]
  push_cast
  ring

/-- `Ai'(-2.89) > 0` (rigorous asymptotic check at `r = 1.7`), used to exclude `a₂'` from `[a₁ - 1/2, a₁]`. -/
private lemma airyAi'_neg_289_pos : 0 < airyAi' (-2.89) := by
  have h := airyAi'_neg_sq_asymptotic (r := 17 / 10) (by norm_num)
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  set θ : ℝ := 2 / 3 * (17 / 10 : ℝ) ^ 3 - π / 4 with hθ
  set v : ℝ := π - θ with hv
  have hv_lo : 0.65 < v := by rw [hv, hθ]; linarith
  have hv_hi : v < 0.66 := by rw [hv, hθ]; linarith
  have hsin_v := Real.sin_gt_sub_cube (by linarith : 0 < v)
  have hv3 : v ^ 3 ≤ 0.66 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hsin_θ : 0.57 < Real.sin θ := by
    have : Real.sin θ = Real.sin v := by rw [hv, Real.sin_pi_sub]
    rw [this]
    nlinarith [sq_nonneg v, hv3]
  have hr_lo : 1.3 < √(17 / 10 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi_hi : √π < 1.78 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  have hpi_pos : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hr_pos : 0 < √(17 / 10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hmain : 0.41 < √(17 / 10 : ℝ) * Real.sin θ / √π := by
    rw [lt_div_iff₀ hpi_pos]
    nlinarith
  have herr : 2 / (5 * (√(17 / 10 : ℝ) * (17 / 10 : ℝ) ^ 2)) < 0.11 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have h' := (abs_le.mp h).1
  have e289 : -((17 / 10 : ℝ) ^ 2) = -2.89 := by norm_num
  rw [e289] at h'
  linarith

/-- On `[a₁ - 1/2, a₁]`, `Ai'(x) > 0` (since `a₂ < -4 < -2.89 < a₁ - 1/2`, `Ai < 0` on `(a₂, a₁)`,
so `Ai'' = x Ai > 0` and `Ai'` increases from `Ai'(-2.89) > 0`). -/
private lemma airyAi'_pos_on_band_tip {x : ℝ} (hx1 : airyZero 1 - 1 / 2 ≤ x) (hx2 : x ≤ airyZero 1) :
    0 < airyAi' x := by
  have ha1 := airyZero_one
  have ha2 := airyZero_two
  have h289 : -2.89 ≤ x := by linarith
  have h289_lt : (-2.89 : ℝ) < airyZero 1 := by linarith
  -- `Ai < 0` on `(a₂, a₁)`
  have hAi_neg : ∀ t : ℝ, airyZero 2 < t → t < airyZero 1 → airyAi t < 0 := by
    have hne : ∀ t ∈ Set.Ioo (airyZero 2) (airyZero 1), airyAi t ≠ 0 := by
      intro t ht h0
      have := airyZero_next (n := 1) le_rfl h0 ht.2
      linarith [ht.1]
    -- near `a₁` from the left, `Ai < 0` because `Ai(a₁) = 0` and `Ai'(a₁) > 0`
    have hslope := (hasDerivAt_airyAi (airyZero 1)).tendsto_slope_zero_left
    have hev : ∀ᶠ h : ℝ in 𝓝[<] 0, 0 < airyAi (airyZero 1 + h) / h := by
      have := hslope.eventually (lt_mem_nhds airyAi'_first_pos)
      filter_upwards [this, self_mem_nhdsWithin] with h hh _
      simp only [airyAi_airyZero, sub_zero, smul_eq_mul] at hh
      rwa [div_eq_inv_mul]
    obtain ⟨h, hdiv, hh⟩ :=
      (hev.and (Ioo_mem_nhdsLT (by linarith [ha1.1, ha2.2] : airyZero 2 - airyZero 1 < 0))).exists
    have hneg_pt : airyAi (airyZero 1 + h) < 0 := by
      have : airyAi (airyZero 1 + h) = (airyAi (airyZero 1 + h) / h) * h := by field_simp [hh.2.ne]
      rw [this]
      exact mul_neg_of_pos_of_neg hdiv hh.2
    intro t ht2 ht1
    by_contra hge
    push Not at hge
    have h0 : (0 : ℝ) ∈ Set.uIcc (airyAi (airyZero 1 + h)) (airyAi t) := by
      rw [Set.mem_uIcc]; left; exact ⟨hneg_pt.le, hge⟩
    obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc continuous_airyAi.continuousOn h0
    have hy' : y ∈ Set.Ioo (airyZero 2) (airyZero 1) := by
      have hsub : Set.uIcc (airyZero 1 + h) t ⊆ Set.Ioo (airyZero 2) (airyZero 1) :=
        Set.ordConnected_Ioo.uIcc_subset ⟨by linarith [hh.1], by linarith [hh.2]⟩ ⟨ht2, ht1⟩
      exact hsub hy
    exact hne y hy' hy0
  -- `Ai'` is monotone increasing on `[-2.89, a₁]`
  have hmono : MonotoneOn airyAi' (Set.Icc (-2.89) (airyZero 1)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) continuous_airyAi'.continuousOn
      (fun t _ => (hasDerivAt_airyAi' t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_airyAi' t).deriv]
    have ht2 : airyZero 2 < t := by linarith [ht.1, ha2.2]
    have htneg : t < 0 := ht.2.trans (airyZero_neg 1)
    have hAneg := hAi_neg t ht2 ht.2
    exact mul_nonneg_of_nonpos_of_nonpos htneg.le hAneg.le
  exact lt_of_lt_of_le airyAi'_neg_289_pos
    (hmono ⟨le_rfl, h289_lt.le⟩ ⟨h289, hx2⟩ h289)

theorem foldTipSeed_pos_band {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη0 : 0 < η)
    {u : ℝ} (hu : u ≤ airyZero 1 - δ) :
    0 < (foldTipSeed δ η (u : ℂ)).re := by
  have hne1 : u ≠ airyZero 1 := by linarith
  have hne2 : u ≠ airyFirstDerivZero := by linarith [airyZero_lt_airyFirstDerivZero]
  rw [foldTipSeed_re_of_ne δ η hne1 hne2]
  have ht1_nn : 0 ≤ airyAi u ^ 2 * (airyZero 1 - δ - u) / (u - airyZero 1) ^ 2 :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _)
  have ht2_nn : 0 ≤ η * (airyAi' u ^ 2 / (u - airyFirstDerivZero) ^ 2) :=
    mul_nonneg hη0.le (div_nonneg (sq_nonneg _) (sq_nonneg _))
  rcases hu.eq_or_lt with rfl | hlt
  · have hAp : 0 < airyAi' (airyZero 1 - δ) :=
      airyAi'_pos_on_band_tip (by linarith) (by linarith)
    have hden : 0 < ((airyZero 1 - δ) - airyFirstDerivZero) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne2)
    have ht2_pos : 0 < η * (airyAi' (airyZero 1 - δ) ^ 2 / ((airyZero 1 - δ) - airyFirstDerivZero) ^ 2) :=
      mul_pos hη0 (div_pos (sq_pos_of_ne_zero hAp.ne') hden)
    linarith
  · by_cases hA0 : airyAi u = 0
    · have hAp : airyAi' u ≠ 0 := by
        intro h0
        have := airyKer_pos' u
        rw [hA0, h0] at this
        simp at this
      have hden : 0 < (u - airyFirstDerivZero) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne2)
      have ht2_pos : 0 < η * (airyAi' u ^ 2 / (u - airyFirstDerivZero) ^ 2) :=
        mul_pos hη0 (div_pos (sq_pos_of_ne_zero hAp) hden)
      linarith
    · have hden : 0 < (u - airyZero 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne1)
      have ht1_pos : 0 < airyAi u ^ 2 * (airyZero 1 - δ - u) / (u - airyZero 1) ^ 2 :=
        div_pos (mul_pos (sq_pos_of_ne_zero hA0) (by linarith)) hden
      linarith

/-- Quantitative band lower bound: `c (1 + |u|)^{-3/2} ≤ F_{δ,η}(u)` on `(-∞, a₁ - δ]`. -/
theorem foldTipSeed_band_lower {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη0 : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, u ≤ airyZero 1 - δ →
      c * (1 + |u|) ^ (-(3 / 2) : ℝ) ≤ (foldTipSeed δ η (u : ℂ)).re := by
  set a₁ := airyZero 1 with ha₁
  set a₁' := airyFirstDerivZero with ha₁'
  set Y₀ : ℝ := max 4 (2 * |a₁| + 2 * |a₁'| + 2) with hY₀
  have hY0_ge4 : 4 ≤ Y₀ := le_max_left _ _
  have hY0_big : 2 * |a₁| + 2 * |a₁'| + 2 ≤ Y₀ := le_max_right _ _
  have hle_end : -Y₀ ≤ a₁ - δ := by
    have : 2 * |a₁| + 2 ≤ Y₀ := by linarith [abs_nonneg a₁']
    linarith [neg_abs_le a₁]
  -- 1. Compact piece `[-Y₀, a₁ - δ]`
  have hcont : Continuous (fun u : ℝ => (foldTipSeed δ η (u : ℂ)).re) :=
    Complex.continuous_re.comp ((differentiable_foldTipSeed δ η).continuous.comp Complex.continuous_ofReal)
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hle_end) hcont.continuousOn
  set m : ℝ := (foldTipSeed δ η (u₀ : ℂ)).re with hm
  have hm_pos : 0 < m := foldTipSeed_pos_band hδ0 hδ1 hη0 hu₀.2
  -- 2. Asymptotic piece `u ≤ -Y₀`
  set c₀ : ℝ := min (1 / 8) η with hc₀
  have hc₀_pos : 0 < c₀ := lt_min (by norm_num) hη0
  set c₁ : ℝ := (c₀ / (2 * π)) * (2 : ℝ) ^ (-(3 / 2) : ℝ) with hc₁
  have hc₁_pos : 0 < c₁ := by positivity
  refine ⟨min c₁ m, lt_min hc₁_pos hm_pos, fun u hu => ?_⟩
  by_cases huY : u ≤ -Y₀
  · set y := -u with hy
    have hy4 : 4 ≤ y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hy0 : 0 < y := by linarith
    have hy_big : 2 * |a₁| + 2 * |a₁'| + 2 ≤ y := by linarith
    have hne1 : u ≠ a₁ := by linarith [neg_abs_le a₁, abs_nonneg a₁', hy]
    have hne2 : u ≠ a₁' := by linarith [neg_abs_le a₁', abs_nonneg a₁, hy]
    rw [foldTipSeed_re_of_ne δ η hne1 hne2]
    have hnum1 : y / 2 ≤ a₁ - δ - u := by
      linarith [neg_abs_le a₁, abs_nonneg a₁', hy]
    have hden1 : (u - a₁) ^ 2 ≤ 4 * y ^ 2 := by
      have h1 : 0 ≤ a₁ - u := by linarith [neg_abs_le a₁, abs_nonneg a₁', hy]
      have h2 : a₁ - u ≤ 2 * y := by linarith [le_abs_self a₁, abs_nonneg a₁', hy]
      nlinarith [sq_nonneg (a₁ - u), show (u - a₁) ^ 2 = (a₁ - u) ^ 2 by ring]
    have hden1_pos : 0 < (u - a₁) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne1)
    have hT1 : (1 / 8) * (y * airyAi (-y) ^ 2) / y ^ 2 ≤
        airyAi u ^ 2 * (a₁ - δ - u) / (u - a₁) ^ 2 := by
      have e : u = -y := by rw [hy]; ring
      rw [← e]
      have hA : (y / 2) * airyAi u ^ 2 ≤ airyAi u ^ 2 * (a₁ - δ - u) := by
        have := mul_le_mul_of_nonneg_left hnum1 (sq_nonneg (airyAi u))
        linarith
      calc (1 / 8) * (y * airyAi u ^ 2) / y ^ 2
          = ((y / 2) * airyAi u ^ 2) / (4 * y ^ 2) := by field_simp; ring
        _ ≤ (airyAi u ^ 2 * (a₁ - δ - u)) / (4 * y ^ 2) := by
            exact div_le_div_of_nonneg_right hA (by positivity)
        _ ≤ airyAi u ^ 2 * (a₁ - δ - u) / (u - a₁) ^ 2 := by
            exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (by linarith)) hden1_pos hden1
    have hden2 : (u - a₁') ^ 2 ≤ y ^ 2 := by
      have h1 : 0 ≤ a₁' - u := by linarith [neg_abs_le a₁', abs_nonneg a₁, hy]
      have h2 : a₁' - u ≤ y := by linarith [airyFirstDerivZero_neg, hy]
      nlinarith [show (u - a₁') ^ 2 = (a₁' - u) ^ 2 by ring]
    have hden2_pos : 0 < (u - a₁') ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne2)
    have hT2 : η * airyAi' (-y) ^ 2 / y ^ 2 ≤ η * (airyAi' u ^ 2 / (u - a₁') ^ 2) := by
      have e : u = -y := by rw [hy]; ring
      have hinv_T2 : airyAi' u ^ 2 / y ^ 2 ≤ airyAi' u ^ 2 / (u - a₁') ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hden2_pos hden2
      calc η * airyAi' (-y) ^ 2 / y ^ 2
          = η * (airyAi' u ^ 2 / y ^ 2) := by rw [← e]; ring
        _ ≤ η * (airyAi' u ^ 2 / (u - a₁') ^ 2) := mul_le_mul_of_nonneg_left hinv_T2 hη0.le
    have hcomb : c₀ * airyKer (-y) (-y) / y ^ 2 ≤
        airyAi u ^ 2 * (a₁ - δ - u) / (u - a₁) ^ 2 + η * (airyAi' u ^ 2 / (u - a₁') ^ 2) := by
      have hc1' : c₀ ≤ 1 / 8 := min_le_left _ _
      have hc2' : c₀ ≤ η := min_le_right _ _
      have hK : c₀ * airyKer (-y) (-y) / y ^ 2 ≤
          (1 / 8) * (y * airyAi (-y) ^ 2) / y ^ 2 + η * airyAi' (-y) ^ 2 / y ^ 2 := by
        rw [airyKer_self]
        have e : -(-y) * airyAi (-y) ^ 2 = y * airyAi (-y) ^ 2 := by ring
        rw [show airyAi' (-y) ^ 2 - (-y) * airyAi (-y) ^ 2 = y * airyAi (-y) ^ 2 + airyAi' (-y) ^ 2 by ring]
        rw [← add_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h1 : c₀ * (y * airyAi (-y) ^ 2) ≤ (1 / 8) * (y * airyAi (-y) ^ 2) :=
          mul_le_mul_of_nonneg_right hc1' (mul_nonneg hy0.le (sq_nonneg _))
        have h2 : c₀ * airyAi' (-y) ^ 2 ≤ η * airyAi' (-y) ^ 2 :=
          mul_le_mul_of_nonneg_right hc2' (sq_nonneg _)
        linarith
      linarith
    have hKlow : √y / (2 * π) ≤ airyKer (-y) (-y) := by
      have h := (abs_le.mp (airyKer_diag_neg hy1)).1
      have hsy : 2 ≤ √y := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hy4
      have hpi4 : π < 4 := Real.pi_lt_four
      have h1y : 1 / y ≤ √y / (2 * π) := by
        rw [div_le_div_iff₀ hy0 (by positivity)]
        have : 2 * π < 2 * 4 := by linarith
        nlinarith
      have : √y / π - √y / (2 * π) = √y / (2 * π) := by field_simp; ring
      linarith
    have hpow_y : √y / y ^ 2 = y ^ (-(3 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast y 2, div_eq_mul_inv, ← Real.rpow_neg hy0.le,
        ← Real.rpow_add hy0]
      norm_num
    have hpow_u : (2 : ℝ) ^ (-(3 / 2) : ℝ) * (1 + |u|) ^ (-(3 / 2) : ℝ) ≤ y ^ (-(3 / 2) : ℝ) := by
      have habs : |u| = y := by
        have e : u = -y := by rw [hy]; ring
        rw [e, abs_neg, abs_of_pos hy0]
      rw [habs]
      have hr2 : (1 + y) ^ (-(3 / 2) : ℝ) ≤ y ^ (-(3 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by norm_num)
      have h2le : (2 : ℝ) ^ (-(3 / 2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      calc (2 : ℝ) ^ (-(3 / 2) : ℝ) * (1 + y) ^ (-(3 / 2) : ℝ)
          ≤ 1 * (1 + y) ^ (-(3 / 2) : ℝ) := by gcongr
        _ = (1 + y) ^ (-(3 / 2) : ℝ) := one_mul _
        _ ≤ y ^ (-(3 / 2) : ℝ) := hr2
    have hlow_c1 : c₁ * (1 + |u|) ^ (-(3 / 2) : ℝ) ≤ c₀ * airyKer (-y) (-y) / y ^ 2 := by
      calc c₁ * (1 + |u|) ^ (-(3 / 2) : ℝ)
          = (c₀ / (2 * π)) * ((2 : ℝ) ^ (-(3 / 2) : ℝ) * (1 + |u|) ^ (-(3 / 2) : ℝ)) := by
            rw [hc₁]; ring
        _ ≤ (c₀ / (2 * π)) * y ^ (-(3 / 2) : ℝ) := by gcongr
        _ = c₀ * (√y / (2 * π)) / y ^ 2 := by rw [← hpow_y]; ring
        _ ≤ c₀ * airyKer (-y) (-y) / y ^ 2 := by gcongr
    have hcmin : min c₁ m * (1 + |u|) ^ (-(3 / 2) : ℝ) ≤ c₁ * (1 + |u|) ^ (-(3 / 2) : ℝ) := by
      gcongr; exact min_le_left _ _
    exact hcmin.trans (hlow_c1.trans hcomb)
  · push Not at huY
    have hum : m ≤ (foldTipSeed δ η (u : ℂ)).re := hmin ⟨huY.le, hu⟩
    have hpow_le : (1 + |u|) ^ (-(3 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg u]) (by norm_num)
    calc min c₁ m * (1 + |u|) ^ (-(3 / 2) : ℝ)
        ≤ m * (1 + |u|) ^ (-(3 / 2) : ℝ) := by gcongr; exact min_le_right _ _
      _ ≤ m * 1 := by gcongr
      _ = m := mul_one _
      _ ≤ (foldTipSeed δ η (u : ℂ)).re := hum

/-- **Fold-tip seed lemma** (`fold_tip_theorem.tex`, Lemma `ft:seed`):
for `0 < δ ≤ 1/2` and `0 < η < δ / |a₁'|`, `F_{δ,η}` is entire, real on `ℝ`, lies in `𝒢_{-3/2}`
(`‖F(u)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)` and `F ∈ L¹(ℝ)`), has `∫_ℝ F_{δ,η} = -δ + η |a₁'| < 0`, and
satisfies `F_{δ,η}(u) > 0` and `F_{δ,η}(u) ≥ c (1 + |u|)^{-3/2}` on `(-∞, a₁ - δ]`. -/
theorem fold_tip_seed_lemma {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη0 : 0 < η)
    (hη : η < δ / |airyFirstDerivZero|) :
    Differentiable ℂ (foldTipSeed δ η) ∧
      (∀ x : ℝ, (foldTipSeed δ η (x : ℂ)).im = 0) ∧
      Integrable (fun x : ℝ => foldTipSeed δ η (x : ℂ)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖foldTipSeed δ η u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) ∧
      (∫ x : ℝ, foldTipSeed δ η (x : ℂ)) = ((-δ + η * |airyFirstDerivZero| : ℝ) : ℂ) ∧
      (∫ x : ℝ, (foldTipSeed δ η (x : ℂ)).re) = -δ + η * |airyFirstDerivZero| ∧
      (∫ x : ℝ, (foldTipSeed δ η (x : ℂ)).re) < 0 ∧
      (∀ u : ℝ, u ≤ airyZero 1 - δ → 0 < (foldTipSeed δ η (u : ℂ)).re) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, u ≤ airyZero 1 - δ →
        c * (1 + |u|) ^ (-(3 / 2) : ℝ) ≤ (foldTipSeed δ η (u : ℂ)).re) := by
  have ha1'_pos : 0 < |airyFirstDerivZero| := abs_pos.mpr airyFirstDerivZero_neg.ne
  have hint_eq := foldTipSeed_integral δ η
  have hint_re : (∫ x : ℝ, (foldTipSeed δ η (x : ℂ)).re) = -δ + η * |airyFirstDerivZero| := by
    have h := integral_re (foldTipSeed_integrable δ η)
    have h' : (∫ x : ℝ, (foldTipSeed δ η (x : ℂ)).re) = (∫ x : ℝ, foldTipSeed δ η (x : ℂ)).re := by
      simpa using h
    rw [h', hint_eq, Complex.ofReal_re]
  have hint_neg : (∫ x : ℝ, (foldTipSeed δ η (x : ℂ)).re) < 0 := by
    rw [hint_re]
    have hmul : η * |airyFirstDerivZero| < δ := (lt_div_iff₀ ha1'_pos).mp hη
    linarith
  exact ⟨differentiable_foldTipSeed δ η, foldTipSeed_ofReal_im δ η, foldTipSeed_integrable δ η,
    foldTipSeed_bound δ η, hint_eq, hint_re, hint_neg,
    fun _ hu => foldTipSeed_pos_band hδ0 hδ1 hη0 hu,
    foldTipSeed_band_lower hδ0 hδ1 hη0⟩

/-- info: 'FormalResearch.TwoEdgeBootstrap.foldTipSeed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.foldTipSeed_bound

/-- info: 'FormalResearch.TwoEdgeBootstrap.foldTipSeed_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.foldTipSeed_integral

/-- info: 'FormalResearch.TwoEdgeBootstrap.foldTipSeed_band_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.foldTipSeed_band_lower

/-- info: 'FormalResearch.TwoEdgeBootstrap.fold_tip_seed_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.fold_tip_seed_lemma

end FormalResearch.TwoEdgeBootstrap
