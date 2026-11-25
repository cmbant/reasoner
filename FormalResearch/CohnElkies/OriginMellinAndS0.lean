module

public import FormalResearch.CohnElkies.AiryTwistedLaplace
public import FormalResearch.Special.AiryAsymPos
public import FormalResearch.Special.AiryCft2FirstDerivZero
public import FormalResearch.Special.AiryAsymNeg
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Positive Source `S₀` Floor and Origin Mellin Kernel Bounds (`ce_rate.tex` Lemmas P.1(2), P.2(1))

Source: `CFT/sign_uncertainty/paper/ce_rate.tex` (PR 240), Lemma `P.1(2)` and Lemma `P.2(1)`
(`cel:L3a`, `(cel:4.6)`).

## Main definitions
* `ceG1`, `ceG1Deriv`, `ceS0`: the smooth positive Airy basis seeds `g₁`, `g₁'`, and `S₀ = g₁ + g₁'`.
* `airyDerivFirstZero`: the largest real zero `a₁'` of `Ai'`.
* `originPsi`, `hB`: the origin Mellin phase `ψ_c(y)` and Binet-strip exponent `h_B(ν)`.

## Main results
* `ceS0_pos`, `ceS0_integrable`, `ceS0_pos_tail`, `positive_source_S0_floor`: Lemma `P.1(2)`.
* `originPsi_zero`, `hasDerivAt_originPsi`, `originPsi_ge_linear`, `exp_neg_originPsi_le`,
  `norm_gamma_pure_imag_sq`, `norm_gamma_pure_imag_le_small`, `norm_gamma_pure_imag_le_large`,
  `originPsi_eq_sub_hB`, `norm_gamma_mul_exp_hB_le`: Lemma `P.2(1)` (`(cel:4.6)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Part 1(2): Positive-source instantiation `S₀ = g₁ + g₁'` (`ce_rate.tex` Lemma P.1(2)) -/

/-- Smooth positive-axis basis seed `g₁(u) = (Ai(u) / (u - a₁))²`, extended smoothly at `a₁`. -/
noncomputable def ceG1 (a1 u : ℝ) : ℝ := dslope airyAi a1 u ^ 2

/-- Smooth positive-axis basis seed `g₁'(u) = (Ai'(u) / (u - a₁'))²`, extended smoothly at `a₁'`. -/
noncomputable def ceG1Deriv (a1' u : ℝ) : ℝ := dslope airyAi' a1' u ^ 2

/-- Positive source seed `S₀ = g₁ + g₁'`. -/
noncomputable def ceS0 (a1 a1' u : ℝ) : ℝ := ceG1 a1 u + ceG1Deriv a1' u

/-- The largest real zero `a₁'` of `Ai'` (`AiryCft2FirstDerivZero.lean`). -/
noncomputable def airyDerivFirstZero : ℝ := Classical.choose airyDeriv_largest_zero

lemma airyDerivFirstZero_spec :
    airyZero 1 < airyDerivFirstZero ∧ airyDerivFirstZero < 0 ∧ airyAi' airyDerivFirstZero = 0 := by
  have h := Classical.choose_spec airyDeriv_largest_zero
  exact ⟨h.1, h.2.1, h.2.2.1⟩

lemma continuous_ceS0 (a1 a1' : ℝ) : Continuous (ceS0 a1 a1') := by
  have hd1 : Differentiable ℝ airyAi := differentiable_airyAi
  have hd2 : Differentiable ℝ airyAi' := fun x => (hasDerivAt_airyAi' x).differentiableAt
  have hc1 : Continuous (dslope airyAi a1) := by
    rw [← continuousOn_univ, continuousOn_dslope univ_mem]
    exact ⟨hd1.continuous.continuousOn, hd1 a1⟩
  have hc2 : Continuous (dslope airyAi' a1') := by
    rw [← continuousOn_univ, continuousOn_dslope univ_mem]
    exact ⟨hd2.continuous.continuousOn, hd2 a1'⟩
  exact (hc1.pow 2).add (hc2.pow 2)

/-- `S₀(u) > 0` everywhere on `ℝ` (`ce_rate.tex` Lemma P.1(2)). -/
theorem ceS0_pos (a1 a1' : ℝ) (ha1 : airyAi a1 = 0) (ha1' : airyAi' a1' = 0) (u : ℝ) :
    0 < ceS0 a1 a1' u := by
  have ha1'_neg : a1' < 0 := by
    by_contra h; have := airyAi'_neg (not_lt.mp h); linarith
  have h_nz : dslope airyAi a1 u ≠ 0 ∨ dslope airyAi' a1' u ≠ 0 := by
    by_cases h1 : u = a1
    · subst h1; left
      rw [dslope_same, (hasDerivAt_airyAi u).deriv]
      exact fun h0 => airyAi_ne_zero_of_deriv_zero h0 ha1
    · by_cases h2 : u = a1'
      · subst h2; right
        rw [dslope_same, (hasDerivAt_airyAi' u).deriv]
        exact mul_ne_zero ha1'_neg.ne (airyAi_ne_zero_of_deriv_zero ha1')
      · rw [dslope_of_ne _ h1, slope_def_field, ha1, sub_zero,
          dslope_of_ne _ h2, slope_def_field, ha1', sub_zero]
        by_contra hc; push Not at hc
        exact airyAi_ne_zero_of_deriv_zero
          ((div_eq_zero_iff.mp hc.2).resolve_right (sub_ne_zero.mpr h2))
          ((div_eq_zero_iff.mp hc.1).resolve_right (sub_ne_zero.mpr h1))
  unfold ceS0 ceG1 ceG1Deriv
  rcases h_nz with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)

private lemma rat_div_diff_sq_sub_inv_le {s a : ℝ} (hs : 1 ≤ s) (ha : a < 0) :
    |s ^ 2 / (s ^ 2 - a) ^ 2 - (s ^ 2)⁻¹| ≤ (2 * |a| + a ^ 2) * (s ^ 4)⁻¹ := by
  have hs2_pos : 0 < s ^ 2 := by positivity
  have hden : s ^ 2 ≤ s ^ 2 - a := by linarith
  have hden_pos : 0 < s ^ 2 - a := by linarith
  have hden_ne : (s ^ 2 - a) ^ 2 ≠ 0 := by positivity
  have hdiff : s ^ 2 / (s ^ 2 - a) ^ 2 - (s ^ 2)⁻¹ =
      (2 * a * s ^ 2 - a ^ 2) / (s ^ 2 * (s ^ 2 - a) ^ 2) := by
    field_simp [hs2_pos.ne', hden_ne]; ring
  rw [hdiff, abs_div, abs_of_pos (by positivity : 0 < s ^ 2 * (s ^ 2 - a) ^ 2)]
  have hnum : |2 * a * s ^ 2 - a ^ 2| ≤ (2 * |a| + a ^ 2) * s ^ 2 := by
    have h1 : |2 * a * s ^ 2| = 2 * |a| * s ^ 2 := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hs2_pos]
    have h2 : |a ^ 2| ≤ a ^ 2 * s ^ 2 := by
      rw [abs_sq]; exact le_mul_of_one_le_right (sq_nonneg _) (by nlinarith only [hs])
    calc |2 * a * s ^ 2 - a ^ 2| ≤ |2 * a * s ^ 2| + |a ^ 2| := abs_sub _ _
      _ ≤ 2 * |a| * s ^ 2 + a ^ 2 * s ^ 2 := add_le_add h1.le h2
      _ = (2 * |a| + a ^ 2) * s ^ 2 := by ring
  have hden_ge : s ^ 6 ≤ s ^ 2 * (s ^ 2 - a) ^ 2 := by
    have h4 : s ^ 4 ≤ (s ^ 2 - a) ^ 2 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ hs2_pos.le hden 2
    calc s ^ 6 = s ^ 2 * s ^ 4 := by ring
      _ ≤ s ^ 2 * (s ^ 2 - a) ^ 2 := mul_le_mul_of_nonneg_left h4 hs2_pos.le
  calc |2 * a * s ^ 2 - a ^ 2| / (s ^ 2 * (s ^ 2 - a) ^ 2)
      ≤ ((2 * |a| + a ^ 2) * s ^ 2) / s ^ 6 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden_ge
    _ = (2 * |a| + a ^ 2) * (s ^ 4)⁻¹ := by field_simp [hs2_pos.ne']

/-- Positive-axis tail expansion of `S₀(s²)` for `s ≥ 1`, with `β_+(S₀) = 1` (`ce_rate.tex` Lemma P.1(2)). -/
theorem ceS0_pos_tail {a1 a1' : ℝ} (ha1 : airyAi a1 = 0) (ha1' : airyAi' a1' = 0) :
    ∃ R_plus : ℝ → ℝ, ∃ C_tl ≥ 0,
      (∀ s ≥ 1, 2 * s * ceS0 a1 a1' (s ^ 2) =
        (1 / (2 * π) * s ^ (-2 : ℝ) + R_plus s) * Real.exp (-(4 / 3 : ℝ) * s ^ 3)) ∧
      (∀ s ≥ 1, |R_plus s| ≤ C_tl * s ^ (-4 : ℝ)) := by
  have ha1_neg : a1 < 0 := by by_contra h; have := airyAi_pos (not_lt.mp h); linarith
  have ha1'_neg : a1' < 0 := by by_contra h; have := airyAi'_neg (not_lt.mp h); linarith
  let R_plus : ℝ → ℝ := fun s =>
    (2 * s * ceS0 a1 a1' (s ^ 2)) * Real.exp ((4 / 3 : ℝ) * s ^ 3) - 1 / (2 * π) * s ^ (-2 : ℝ)
  let C1 : ℝ := 17 / (96 * π) + (17 / (96 * √π)) ^ 2
  let C_tl : ℝ := 1 / (2 * π) + (1 / (2 * π)) * (2 * |a1'| + a1' ^ 2) + 2 * C1
  refine ⟨R_plus, C_tl, by positivity, ?_, ?_⟩
  · intro s _
    dsimp [R_plus]
    rw [add_sub_cancel]
    calc 2 * s * ceS0 a1 a1' (s ^ 2)
        = 2 * s * ceS0 a1 a1' (s ^ 2) *
            (Real.exp ((4 / 3 : ℝ) * s ^ 3) * Real.exp (-(4 / 3 : ℝ) * s ^ 3)) := by
          rw [← Real.exp_add, show (4 / 3 : ℝ) * s ^ 3 + -(4 / 3 : ℝ) * s ^ 3 = 0 by ring,
            Real.exp_zero, mul_one]
      _ = 2 * s * ceS0 a1 a1' (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3) *
            Real.exp (-(4 / 3 : ℝ) * s ^ 3) := by ring
  · intro s hs
    have hs_pos : 0 < s := by linarith
    have hs2_pos : 0 < s ^ 2 := sq_pos_of_pos hs_pos
    have hne1 : s ^ 2 ≠ a1 := by linarith
    have hne2 : s ^ 2 ≠ a1' := by linarith
    have hs4 : s ^ (-4 : ℝ) = (s ^ 4)⁻¹ := by rw [Real.rpow_neg hs_pos.le]; norm_cast
    have hs2 : s ^ (-2 : ℝ) = (s ^ 2)⁻¹ := by rw [Real.rpow_neg hs_pos.le]; norm_cast
    have hg1_eq : ceG1 a1 (s ^ 2) = airyAi (s ^ 2) ^ 2 / (s ^ 2 - a1) ^ 2 := by
      rw [ceG1, dslope_of_ne _ hne1, slope_def_field, ha1, sub_zero, div_pow]
    have hg1d_eq : ceG1Deriv a1' (s ^ 2) = airyAi' (s ^ 2) ^ 2 / (s ^ 2 - a1') ^ 2 := by
      rw [ceG1Deriv, dslope_of_ne _ hne2, slope_def_field, ha1', sub_zero, div_pow]
    have hπ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
    have hexp2 : Real.exp (-(2 / 3 : ℝ) * s ^ 3) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have h0 : (2 : ℕ) * (-(2 / 3 : ℝ) * s ^ 3) + 4 / 3 * s ^ 3 = 0 := by norm_cast; ring
      rw [h0, Real.exp_zero]
    -- Bound on `g₁(s²)`
    have hAi_bd := airyAi_abs_le hs2_pos
    have hAi_pow : (s ^ 2) ^ (-(1 / 4) : ℝ) = s ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs_pos.le]; norm_num
    have hAi_exp : (s ^ 2) ^ (3 / 2 : ℝ) = s ^ 3 := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs_pos.le]; norm_num
    rw [hAi_pow, hAi_exp] at hAi_bd
    have hAi_sq : airyAi (s ^ 2) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3) ≤ (4 * π * s)⁻¹ := by
      have hsq : airyAi (s ^ 2) ^ 2 ≤
          (1 / (2 * √π) * s ^ (-(1 / 2) : ℝ) * Real.exp (-(2 / 3) * s ^ 3)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hAi_bd 2
      have hsr : (s ^ (-(1 / 2) : ℝ)) ^ 2 = s⁻¹ := by
        rw [← Real.rpow_natCast (s ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hs_pos.le]; norm_num
        rw [Real.rpow_neg_one]
      calc airyAi (s ^ 2) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3)
          ≤ (1 / (2 * √π) * s ^ (-(1 / 2) : ℝ) * Real.exp (-(2 / 3) * s ^ 3)) ^ 2 *
              Real.exp ((4 / 3 : ℝ) * s ^ 3) := by gcongr
        _ = (1 / (4 * (√π * √π)) * (s ^ (-(1 / 2) : ℝ)) ^ 2) *
              (Real.exp (-(2 / 3 : ℝ) * s ^ 3) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3)) := by ring
        _ = (1 / (4 * π) * s⁻¹) * 1 := by rw [hπ, hsr, hexp2]
        _ = (4 * π * s)⁻¹ := by field_simp
    have hg1_bd : |2 * s * ceG1 a1 (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3)| ≤
        1 / (2 * π) * s ^ (-4 : ℝ) := by
      rw [abs_of_nonneg (by unfold ceG1; positivity), hg1_eq, hs4]
      have hden_sq : s ^ 4 ≤ (s ^ 2 - a1) ^ 2 := by
        rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]
        exact pow_le_pow_left₀ hs2_pos.le (by linarith : s ^ 2 ≤ s ^ 2 - a1) 2
      have hfrac1 : 2 * s / (s ^ 2 - a1) ^ 2 ≤ 2 * s / s ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden_sq
      calc 2 * s * (airyAi (s ^ 2) ^ 2 / (s ^ 2 - a1) ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3)
          = (2 * s / (s ^ 2 - a1) ^ 2) * (airyAi (s ^ 2) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3)) := by ring
        _ ≤ (2 * s / s ^ 4) * (4 * π * s)⁻¹ :=
            mul_le_mul hfrac1 hAi_sq (by positivity) (by positivity)
        _ = 1 / (2 * π) * (s ^ 4)⁻¹ := by field_simp; ring
    -- Expansion of `Ai'(s²)²`
    have hAi'_bd := airyAi'_sq_add_leading_le hs_pos
    set E1 : ℝ := (airyAi' (s ^ 2) + √s * Real.exp (-(2 / 3) * s ^ 3) / (2 * √π)) *
      Real.exp ((2 / 3) * s ^ 3)
    have hE1_bd : |E1| ≤ 17 / (96 * √π) / (√s * s ^ 2) := by
      dsimp [E1]
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := mul_le_mul_of_nonneg_right hAi'_bd (Real.exp_pos ((2 / 3 : ℝ) * s ^ 3)).le
      have hexp1 : Real.exp (-(2 / 3) * s ^ 3) * Real.exp ((2 / 3) * s ^ 3) = 1 := by
        rw [← Real.exp_add]; simp
      calc |airyAi' (s ^ 2) + √s * Real.exp (-(2 / 3) * s ^ 3) / (2 * √π)| * Real.exp ((2 / 3) * s ^ 3)
          ≤ 17 / (96 * √π) * Real.exp (-(2 / 3) * s ^ 3) / (√s * s ^ 2) * Real.exp ((2 / 3) * s ^ 3) := h1
        _ = 17 / (96 * √π) / (√s * s ^ 2) *
              (Real.exp (-(2 / 3) * s ^ 3) * Real.exp ((2 / 3) * s ^ 3)) := by ring
        _ = 17 / (96 * √π) / (√s * s ^ 2) := by rw [hexp1, mul_one]
    have hAi'_eq : airyAi' (s ^ 2) = (-(√s / (2 * √π)) + E1) * Real.exp (-(2 / 3) * s ^ 3) := by
      have hexp1 : Real.exp ((2 / 3) * s ^ 3) * Real.exp (-(2 / 3) * s ^ 3) = 1 := by
        rw [← Real.exp_add]; simp
      dsimp [E1]
      calc airyAi' (s ^ 2)
          = -(√s * Real.exp (-(2 / 3) * s ^ 3) / (2 * √π)) +
              (airyAi' (s ^ 2) + √s * Real.exp (-(2 / 3) * s ^ 3) / (2 * √π)) *
                (Real.exp ((2 / 3) * s ^ 3) * Real.exp (-(2 / 3) * s ^ 3)) := by
            rw [hexp1, mul_one]; ring
        _ = _ := by ring
    have hAi'_sq_eq : airyAi' (s ^ 2) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3) =
        s / (4 * π) + (-(√s / √π * E1) + E1 ^ 2) := by
      have hL_sq : (√s / (2 * √π)) ^ 2 = s / (4 * π) := by
        rw [div_pow, Real.sq_sqrt hs_pos.le, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
      rw [hAi'_eq, mul_pow, mul_assoc, hexp2, mul_one]
      calc (-(√s / (2 * √π)) + E1) ^ 2
          = (√s / (2 * √π)) ^ 2 + (-(√s / √π * E1) + E1 ^ 2) := by ring
        _ = s / (4 * π) + (-(√s / √π * E1) + E1 ^ 2) := by rw [hL_sq]
    have hE_rem_bd : |-(√s / √π * E1) + E1 ^ 2| ≤ C1 * (s ^ 2)⁻¹ := by
      have hsr_pos : 0 < √s := Real.sqrt_pos.mpr hs_pos
      have hT_pos : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
      have h1 : |√s / √π * E1| ≤ 17 / (96 * π) * (s ^ 2)⁻¹ := by
        rw [abs_mul, abs_of_pos (div_pos hsr_pos hT_pos)]
        calc √s / √π * |E1|
            ≤ √s / √π * (17 / (96 * √π) / (√s * s ^ 2)) := by gcongr
          _ = 17 / (96 * (√π * √π)) * (s ^ 2)⁻¹ := by field_simp
          _ = 17 / (96 * π) * (s ^ 2)⁻¹ := by rw [hπ]
      have h2 : |E1 ^ 2| ≤ (17 / (96 * √π)) ^ 2 * (s ^ 2)⁻¹ := by
        rw [abs_pow]
        have hsq := pow_le_pow_left₀ (abs_nonneg E1) hE1_bd 2
        have hpow_s : s ^ 2 ≤ s * s ^ 4 := by have : 1 ≤ s ^ 3 := one_le_pow₀ hs; nlinarith
        calc |E1| ^ 2 ≤ (17 / (96 * √π) / (√s * s ^ 2)) ^ 2 := hsq
          _ = (17 / (96 * √π)) ^ 2 / (s * s ^ 4) := by
              rw [div_pow, mul_pow, Real.sq_sqrt hs_pos.le]; ring
          _ ≤ (17 / (96 * √π)) ^ 2 / s ^ 2 := by gcongr
          _ = (17 / (96 * √π)) ^ 2 * (s ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      calc |-(√s / √π * E1) + E1 ^ 2| ≤ |-(√s / √π * E1)| + |E1 ^ 2| := abs_add_le _ _
        _ = |√s / √π * E1| + |E1 ^ 2| := by rw [abs_neg]
        _ ≤ 17 / (96 * π) * (s ^ 2)⁻¹ + (17 / (96 * √π)) ^ 2 * (s ^ 2)⁻¹ := add_le_add h1 h2
        _ = C1 * (s ^ 2)⁻¹ := by dsimp [C1]; ring
    have hg1d_split : 2 * s * ceG1Deriv a1' (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3) -
        1 / (2 * π) * s ^ (-2 : ℝ) =
        1 / (2 * π) * (s ^ 2 / (s ^ 2 - a1') ^ 2 - (s ^ 2)⁻¹) +
          2 * s / (s ^ 2 - a1') ^ 2 * (-(√s / √π * E1) + E1 ^ 2) := by
      rw [hg1d_eq, hs2]
      have heq : 2 * s * (airyAi' (s ^ 2) ^ 2 / (s ^ 2 - a1') ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3) =
          2 * s / (s ^ 2 - a1') ^ 2 * (airyAi' (s ^ 2) ^ 2 * Real.exp ((4 / 3 : ℝ) * s ^ 3)) := by ring
      rw [heq, hAi'_sq_eq]; ring
    have hg1d_bd1 := rat_div_diff_sq_sub_inv_le hs ha1'_neg
    have hg1d_bd2 : |2 * s / (s ^ 2 - a1') ^ 2 * (-(√s / √π * E1) + E1 ^ 2)| ≤
        2 * C1 * (s ^ 4)⁻¹ := by
      have hden_ge : s ^ 4 ≤ (s ^ 2 - a1') ^ 2 := by
        rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]
        exact pow_le_pow_left₀ hs2_pos.le (by linarith : s ^ 2 ≤ s ^ 2 - a1') 2
      have hden_pos : 0 < (s ^ 2 - a1') ^ 2 := by positivity
      have hfrac : 2 * s / (s ^ 2 - a1') ^ 2 ≤ 2 * s / s ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      rw [abs_mul, abs_of_pos (div_pos (by linarith) hden_pos)]
      calc 2 * s / (s ^ 2 - a1') ^ 2 * |-(√s / √π * E1) + E1 ^ 2|
          ≤ (2 * s / s ^ 4) * (C1 * (s ^ 2)⁻¹) :=
            mul_le_mul hfrac hE_rem_bd (abs_nonneg _) (by positivity)
        _ = 2 * C1 * (s ^ 5)⁻¹ := by field_simp
        _ ≤ 2 * C1 * (s ^ 4)⁻¹ := by
            have : s ^ 4 ≤ s ^ 5 := by
              calc s ^ 4 = s ^ 4 * 1 := by ring
                _ ≤ s ^ 4 * s := mul_le_mul_of_nonneg_left hs (by positivity)
                _ = s ^ 5 := by ring
            exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) this) (by positivity)
    have hR_eq : R_plus s =
        2 * s * ceG1 a1 (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3) +
          (2 * s * ceG1Deriv a1' (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3) -
            1 / (2 * π) * s ^ (-2 : ℝ)) := by dsimp [R_plus, ceS0]; ring
    rw [hR_eq, hg1d_split]
    have hg1_bd' : |2 * s * ceG1 a1 (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3)| ≤
        1 / (2 * π) * (s ^ 4)⁻¹ := by
      simpa [hs4] using hg1_bd
    have hg1d_bd1' : |1 / (2 * π) * (s ^ 2 / (s ^ 2 - a1') ^ 2 - (s ^ 2)⁻¹)| ≤
        1 / (2 * π) * ((2 * |a1'| + a1' ^ 2) * (s ^ 4)⁻¹) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
      exact mul_le_mul_of_nonneg_left hg1d_bd1 (by positivity)
    let t1 := 2 * s * ceG1 a1 (s ^ 2) * Real.exp ((4 / 3 : ℝ) * s ^ 3)
    let t2 := 1 / (2 * π) * (s ^ 2 / (s ^ 2 - a1') ^ 2 - (s ^ 2)⁻¹)
    let t3 := 2 * s / (s ^ 2 - a1') ^ 2 * (-(√s / √π * E1) + E1 ^ 2)
    have htri : |t1 + (t2 + t3)| ≤ |t1| + (|t2| + |t3|) :=
      (abs_add_le t1 (t2 + t3)).trans (add_le_add le_rfl (abs_add_le t2 t3))
    have hsum : |t1| + (|t2| + |t3|) ≤
        1 / (2 * π) * (s ^ 4)⁻¹ +
          (1 / (2 * π) * ((2 * |a1'| + a1' ^ 2) * (s ^ 4)⁻¹) + 2 * C1 * (s ^ 4)⁻¹) :=
      add_le_add hg1_bd' (add_le_add hg1d_bd1' hg1d_bd2)
    have hrhs : 1 / (2 * π) * (s ^ 4)⁻¹ +
          (1 / (2 * π) * ((2 * |a1'| + a1' ^ 2) * (s ^ 4)⁻¹) + 2 * C1 * (s ^ 4)⁻¹) =
        C_tl * s ^ (-4 : ℝ) := by rw [hs4]; dsimp [C_tl]; ring
    exact htri.trans (hsum.trans_eq hrhs)

/-- `S₀` is integrable on `ℝ` (`ce_rate.tex` Lemma P.1(2)). -/
theorem ceS0_integrable {a1 a1' : ℝ} (ha1 : airyAi a1 = 0) (ha1' : airyAi' a1' = 0) :
    Integrable (ceS0 a1 a1') := by
  let R : ℝ := 2 * max |a1| |a1'| + 2
  have hR2 : 2 ≤ R := by dsimp [R]; linarith [le_max_left |a1| |a1'|, abs_nonneg a1]
  have ha1_R : 2 * |a1| ≤ R := by dsimp [R]; linarith [le_max_left |a1| |a1'|]
  have ha1'_R : 2 * |a1'| ≤ R := by dsimp [R]; linarith [le_max_right |a1| |a1'|]
  -- 1. `Iio (-R)`: `O((-u)^(-3/2))`
  have h_neg : IntegrableOn (ceS0 a1 a1') (Iio (-R)) := by
    have h_rpow : IntegrableOn (fun u : ℝ => 32 * (-u) ^ (-(3 / 2) : ℝ)) (Iio (-R)) := by
      have h1 : IntegrableOn (fun y : ℝ => 32 * y ^ (-(3 / 2) : ℝ)) (Ioi R) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)).const_mul 32
      have h2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iio
        (f := fun u : ℝ => -u) (f' := fun _ => -1)
        (fun u _ => (hasDerivAt_neg u).hasDerivWithinAt) (fun _ _ _ _ h => by linarith)
        (fun y : ℝ => 32 * y ^ (-(3 / 2) : ℝ))).mp (by
          have : (fun u : ℝ => -u) '' Iio (-R) = Ioi R := by
            ext y; simp only [mem_image, mem_Iio, mem_Ioi]
            exact ⟨fun ⟨u, hu, heq⟩ => by linarith, fun hy => ⟨-y, by linarith, by ring⟩⟩
          rwa [this])
      simpa using h2
    refine h_rpow.mono' (continuous_ceS0 a1 a1').aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    have hu_lt : u < -R := hu
    set y := -u
    have hy_gt : R < y := by dsimp [y]; linarith
    have hy1 : 1 ≤ y := by linarith
    have hy_pos : 0 < y := by linarith
    have hu_eq : u = -y := by dsimp [y]; ring
    have h_sep1 : y / 2 ≤ |u - a1| := by
      have : |-a1| ≤ y / 2 := by rw [abs_neg]; linarith
      calc y / 2 ≤ y - |-a1| := by linarith
        _ = |y| - |-a1| := by rw [abs_of_pos hy_pos]
        _ ≤ |y - (-a1)| := abs_sub_abs_le_abs_sub y (-a1)
        _ = |u - a1| := by rw [← abs_neg (u - a1)]; congr 1; dsimp [y]; ring
    have h_sep2 : y / 2 ≤ |u - a1'| := by
      have : |-a1'| ≤ y / 2 := by rw [abs_neg]; linarith
      calc y / 2 ≤ y - |-a1'| := by linarith
        _ = |y| - |-a1'| := by rw [abs_of_pos hy_pos]
        _ ≤ |y - (-a1')| := abs_sub_abs_le_abs_sub y (-a1')
        _ = |u - a1'| := by rw [← abs_neg (u - a1')]; congr 1; dsimp [y]; ring
    have hne1 : u ≠ a1 := fun h => by rw [h, sub_self, abs_zero] at h_sep1; linarith
    have hne2 : u ≠ a1' := fun h => by rw [h, sub_self, abs_zero] at h_sep2; linarith
    have hT_gt : 1 ≤ √π := by rw [Real.one_le_sqrt]; linarith [Real.two_le_pi]
    have h1T : 1 / √π ≤ 1 := div_le_one_of_le₀ hT_gt (by positivity)
    have hAi_bd : |airyAi (-y)| ≤ 2 * y ^ (-(1 / 4) : ℝ) := by
      have hAi := airyAi_neg_asymptotic hy_pos
      have h1 : (1 / 8 : ℝ) * y ^ (-(7 / 4) : ℝ) ≤ (1 / 8 : ℝ) * y ^ (-(1 / 4) : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)) (by norm_num)
      have hcos : |1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
          1 * y ^ (-(1 / 4) : ℝ) := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / √π),
          abs_of_nonneg (Real.rpow_nonneg hy_pos.le _)]
        calc 1 / √π * y ^ (-(1 / 4) : ℝ) * |Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)|
            ≤ 1 * y ^ (-(1 / 4) : ℝ) * 1 := by gcongr; exact Real.abs_cos_le_one _
          _ = 1 * y ^ (-(1 / 4) : ℝ) := by ring
      have htri := abs_add_le
        (airyAi (-y) - 1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
        (1 / √π * y ^ (-(1 / 4) : ℝ) * Real.cos (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
      rw [sub_add_cancel] at htri
      linarith [Real.rpow_nonneg hy_pos.le (-(1 / 4) : ℝ)]
    have hAi'_bd : |airyAi' (-y)| ≤ 2 * y ^ (1 / 4 : ℝ) := by
      have hAi' := airyAi'_neg_asymptotic hy_pos
      have h1 : (2 / 5 : ℝ) * y ^ (-(5 / 4) : ℝ) ≤ (2 / 5 : ℝ) * y ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)) (by norm_num)
      have hsin : |1 / √π * y ^ (1 / 4 : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)| ≤
          1 * y ^ (1 / 4 : ℝ) := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / √π),
          abs_of_nonneg (Real.rpow_nonneg hy_pos.le _)]
        calc 1 / √π * y ^ (1 / 4 : ℝ) * |Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4)|
            ≤ 1 * y ^ (1 / 4 : ℝ) * 1 := by gcongr; exact Real.abs_sin_le_one _
          _ = 1 * y ^ (1 / 4 : ℝ) := by ring
      have htri := abs_add_le
        (airyAi' (-y) - 1 / √π * y ^ (1 / 4 : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
        (1 / √π * y ^ (1 / 4 : ℝ) * Real.sin (2 / 3 * y ^ (3 / 2 : ℝ) - π / 4))
      rw [sub_add_cancel] at htri
      linarith [Real.rpow_nonneg hy_pos.le (1 / 4 : ℝ)]
    have hg1_bd : ceG1 a1 u ≤ 16 * y ^ (-(3 / 2) : ℝ) := by
      rw [ceG1, dslope_of_ne _ hne1, slope_def_field, ha1, sub_zero, div_pow, hu_eq]
      have hsq1 : airyAi (-y) ^ 2 ≤ 4 * y ^ (-(1 / 2) : ℝ) := by
        calc airyAi (-y) ^ 2 = |airyAi (-y)| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * y ^ (-(1 / 4) : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAi_bd 2
          _ = 4 * (y ^ (-(1 / 4) : ℝ)) ^ 2 := by ring
          _ = 4 * y ^ (-(1 / 2) : ℝ) := by
              rw [← Real.rpow_natCast (y ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hy_pos.le]; norm_num
      have hsq2 : (y / 2) ^ 2 ≤ (-y - a1) ^ 2 := by
        rw [← hu_eq, ← sq_abs (u - a1)]; exact pow_le_pow_left₀ (by linarith) h_sep1 2
      have hy52 : y ^ (-(5 / 2) : ℝ) ≤ y ^ (-(3 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
      have hy_div : y ^ (-(1 / 2) : ℝ) / y ^ 2 = y ^ (-(5 / 2) : ℝ) := by
        rw [← Real.rpow_natCast y 2, ← Real.rpow_sub hy_pos]; norm_num
      calc airyAi (-y) ^ 2 / (-y - a1) ^ 2 ≤ (4 * y ^ (-(1 / 2) : ℝ)) / (y / 2) ^ 2 :=
            div_le_div₀ (by positivity) hsq1 (by positivity) hsq2
        _ = 16 * (y ^ (-(1 / 2) : ℝ) / y ^ 2) := by ring
        _ = 16 * y ^ (-(5 / 2) : ℝ) := by rw [hy_div]
        _ ≤ 16 * y ^ (-(3 / 2) : ℝ) := mul_le_mul_of_nonneg_left hy52 (by norm_num)
    have hg1d_bd : ceG1Deriv a1' u ≤ 16 * y ^ (-(3 / 2) : ℝ) := by
      rw [ceG1Deriv, dslope_of_ne _ hne2, slope_def_field, ha1', sub_zero, div_pow, hu_eq]
      have hsq1 : airyAi' (-y) ^ 2 ≤ 4 * y ^ (1 / 2 : ℝ) := by
        calc airyAi' (-y) ^ 2 = |airyAi' (-y)| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * y ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAi'_bd 2
          _ = 4 * (y ^ (1 / 4 : ℝ)) ^ 2 := by ring
          _ = 4 * y ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_natCast (y ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hy_pos.le]; norm_num
      have hsq2 : (y / 2) ^ 2 ≤ (-y - a1') ^ 2 := by
        rw [← hu_eq, ← sq_abs (u - a1')]; exact pow_le_pow_left₀ (by linarith) h_sep2 2
      have hy_div : y ^ (1 / 2 : ℝ) / y ^ 2 = y ^ (-(3 / 2) : ℝ) := by
        rw [show y ^ 2 = y ^ (2 : ℝ) by norm_cast, ← Real.rpow_sub hy_pos,
          show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num]
      calc airyAi' (-y) ^ 2 / (-y - a1') ^ 2 ≤ (4 * y ^ (1 / 2 : ℝ)) / (y / 2) ^ 2 :=
            div_le_div₀ (by positivity) hsq1 (by positivity) hsq2
        _ = 16 * (y ^ (1 / 2 : ℝ) / y ^ 2) := by ring
        _ = 16 * y ^ (-(3 / 2) : ℝ) := by rw [hy_div]
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold ceS0 ceG1 ceG1Deriv; positivity)]
    dsimp [ceS0]
    linarith
  -- 2. `Icc (-R) 1`
  have h_mid : IntegrableOn (ceS0 a1 a1') (Icc (-R) 1) :=
    (continuous_ceS0 a1 a1').continuousOn.integrableOn_Icc
  -- 3. `Ioi 1`
  have h_pos : IntegrableOn (ceS0 a1 a1') (Ioi 1) := by
    obtain ⟨R_plus, C_tl, hC_tl, htail, hR_bd⟩ := ceS0_pos_tail ha1 ha1'
    have hch := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (f := fun s : ℝ => s ^ 2) (f' := fun s : ℝ => 2 * s)
      (fun s _ => by simpa using (hasDerivAt_pow 2 s).hasDerivWithinAt) sq_injOn_Ioi_one
      (ceS0 a1 a1')).mpr ?_
    · rwa [sq_image_Ioi_one] at hch
    · have hint_exp : IntegrableOn (fun s : ℝ => (1 / (2 * π) + C_tl) * Real.exp (-s)) (Ioi 1) :=
        (integrableOn_exp_neg_Ioi 1).const_mul _
      have hmeas : AEStronglyMeasurable (fun s : ℝ => |2 * s| • ceS0 a1 a1' (s ^ 2))
          (volume.restrict (Ioi 1)) :=
        (((continuous_const.mul continuous_id).abs).mul
          ((continuous_ceS0 a1 a1').comp (continuous_pow 2))).aestronglyMeasurable.restrict
      refine hint_exp.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs1 : 1 ≤ s := (mem_Ioi.mp hs).le
      have hs2 : s ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
      have hs4 : s ^ (-4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
      have hexp : -(4 / 3 : ℝ) * s ^ 3 ≤ -s := by
        have : s ≤ s ^ 3 := le_self_pow₀ hs1 (by norm_num); linarith
      rw [Real.norm_eq_abs, smul_eq_mul, abs_of_pos (by linarith : 0 < 2 * s),
        abs_of_nonneg (by unfold ceS0 ceG1 ceG1Deriv; positivity), htail s hs1]
      have hcoef : 1 / (2 * π) * s ^ (-2 : ℝ) + R_plus s ≤ 1 / (2 * π) + C_tl := by
        have h1 : 1 / (2 * π) * s ^ (-2 : ℝ) ≤ 1 / (2 * π) :=
          mul_le_of_le_one_right (by positivity) hs2
        have h2 : R_plus s ≤ C_tl :=
          (abs_le.mp (hR_bd s hs1)).2.trans (mul_le_of_le_one_right hC_tl hs4)
        linarith
      exact mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
  have huniv : (Iio (-R) ∪ Icc (-R) 1) ∪ Ioi 1 = (univ : Set ℝ) := by
    ext u
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    rcases lt_or_ge u (-R) with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt u 1 with h1 | h1
      · exact Or.inl (Or.inr ⟨h, h1⟩)
      · exact Or.inr h1
  rw [← integrableOn_univ, ← huniv]
  exact (h_neg.union h_mid).union h_pos

/-- **Positive-source floor** (`ce_rate.tex` Lemma P.1(2)): for `a₁ = airyZero 1` and
`a₁' = airyDerivFirstZero`, `S₀ = g₁ + g₁'` satisfies the rescaled Laplace asymptotic with
`β_+(S₀) = 1`, strict positivity on `[0, ∞)`, and global two-sided `(1 + x)^{-5/2}` bounds. -/
theorem positive_source_S0_floor :
    let a1 := airyZero 1
    let a1' := airyDerivFirstZero
    Filter.Tendsto (fun x => x ^ (5 / 2 : ℝ) * airyTwistedLaplace (ceS0 a1 a1') (ceCs * x))
      Filter.atTop (𝓝 (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π)) ∧
    (∀ x ≥ 0, 0 < airyTwistedLaplace (ceS0 a1 a1') (ceCs * x)) ∧
    (∃ c_lo C_hi : ℝ, 0 < c_lo ∧ c_lo ≤ C_hi ∧ ∀ x ≥ 0,
      c_lo * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) ∧
      airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) ≤ C_hi * (1 + x) ^ (-(5 / 2 : ℝ))) := by
  intro a1 a1'
  have ha1 : airyAi a1 = 0 := airyAi_airyZero 1
  have ha1' : airyAi' a1' = 0 := airyDerivFirstZero_spec.2.2
  have hS_int : Integrable (ceS0 a1 a1') := ceS0_integrable ha1 ha1'
  obtain ⟨R_plus, C_tl, hC_tl, htail, hR_bd⟩ := ceS0_pos_tail ha1 ha1'
  have htend : Filter.Tendsto
      (fun x => x ^ (5 / 2 : ℝ) * airyTwistedLaplace (ceS0 a1 a1') (ceCs * x))
      Filter.atTop (𝓝 (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π)) := by
    simpa using airyTwistedLaplace_rescaled_tendsto hS_int htail hC_tl hR_bd
  have hpos : ∀ x ≥ 0, 0 < airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) := by
    intro x hx
    have hint := tail_integrable hS_int htail hC_tl hR_bd (mul_nonneg ceCs_pos.le hx)
    have hcont : Continuous (fun u => ceS0 a1 a1' u * Real.exp (ceCs * x * u)) :=
      (continuous_ceS0 a1 a1').mul (by fun_prop)
    have hnn : 0 ≤ fun u => ceS0 a1 a1' u * Real.exp (ceCs * x * u) := fun u =>
      mul_nonneg (ceS0_pos a1 a1' ha1 ha1' u).le (Real.exp_pos _).le
    have hnz : ceS0 a1 a1' 0 * Real.exp (ceCs * x * 0) ≠ 0 :=
      mul_ne_zero (ceS0_pos a1 a1' ha1 ha1' 0).ne' (Real.exp_pos _).ne'
    unfold airyTwistedLaplace
    exact mul_pos (mul_pos ceK_pos (Real.exp_pos _))
      (MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero hcont hint hnn hnz)
  refine ⟨htend, hpos, ?_⟩
  set L : ℝ := 2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π
  have hL_pos : 0 < L := div_pos (mul_pos (mul_pos two_pos ceK_pos) (Real.rpow_pos_of_pos ceCs_pos _))
    (Real.sqrt_pos.mpr Real.pi_pos)
  obtain ⟨X0, hX0⟩ := Metric.tendsto_atTop.mp htend (L / 2) (by linarith)
  set X := max X0 1
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX_pos : 0 ≤ X := by linarith
  have h_lap_cont : ContinuousOn (fun x => airyTwistedLaplace (ceS0 a1 a1') (ceCs * x)) (Icc 0 X) := by
    let bound : ℝ → ℝ := fun u => ceS0 a1 a1' u + ceS0 a1 a1' u * Real.exp (ceCs * X * u)
    have hbound_int : Integrable bound :=
      hS_int.add (tail_integrable hS_int htail hC_tl hR_bd (mul_nonneg ceCs_pos.le hX_pos))
    have h_int_cont : ContinuousOn (fun x => ∫ u : ℝ, ceS0 a1 a1' u * Real.exp (ceCs * x * u))
        (Icc 0 X) := by
      refine continuousOn_of_dominated (s := Icc 0 X) (bound := bound) ?_ ?_ hbound_int ?_
      · intro x _
        exact ((continuous_ceS0 a1 a1').mul (by fun_prop)).aestronglyMeasurable
      · intro x hx
        refine ae_of_all _ fun u => ?_
        have hS0_pos := (ceS0_pos a1 a1' ha1 ha1' u).le
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hS0_pos, abs_of_pos (Real.exp_pos _)]
        rcases le_or_gt u 0 with hu | hu
        · have h1 : Real.exp (ceCs * x * u) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ceCs_pos.le hx.1) hu
          have h2 : ceS0 a1 a1' u * Real.exp (ceCs * x * u) ≤ ceS0 a1 a1' u := by
            simpa using mul_le_mul_of_nonneg_left h1 hS0_pos
          have h3 : 0 ≤ ceS0 a1 a1' u * Real.exp (ceCs * X * u) := by positivity
          dsimp [bound]; linarith
        · have h1 : Real.exp (ceCs * x * u) ≤ Real.exp (ceCs * X * u) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hx.2 ceCs_pos.le) hu.le)
          have h2 : ceS0 a1 a1' u * Real.exp (ceCs * x * u) ≤
              ceS0 a1 a1' u * Real.exp (ceCs * X * u) := mul_le_mul_of_nonneg_left h1 hS0_pos
          dsimp [bound]; linarith
      · refine ae_of_all _ fun u => Continuous.continuousOn (by fun_prop)
    exact (by fun_prop : Continuous (fun x : ℝ => ceK * Real.exp (-((ceCs * x) ^ 3) / 12))).continuousOn.mul
      h_int_cont
  let φ : ℝ → ℝ := fun x => airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) * (1 + x) ^ (5 / 2 : ℝ)
  have hφ_cont : ContinuousOn φ (Icc 0 X) :=
    h_lap_cont.mul ((continuousOn_const.add continuousOn_id).rpow_const fun _ _ => Or.inr (by norm_num))
  have hne : (Icc (0 : ℝ) X).Nonempty := ⟨0, le_rfl, hX_pos⟩
  obtain ⟨x_min, hx_min_mem, hx_min⟩ := isCompact_Icc.exists_isMinOn hne hφ_cont
  obtain ⟨x_max, hx_max_mem, hx_max⟩ := isCompact_Icc.exists_isMaxOn hne hφ_cont
  have hmin_pos : 0 < φ x_min :=
    mul_pos (hpos x_min hx_min_mem.1) (Real.rpow_pos_of_pos (by linarith [hx_min_mem.1]) _)
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (5 / 2 : ℝ) := by positivity
  refine ⟨min (φ x_min) (L / 2), max (φ x_max) (3 * L / 2 * (2 : ℝ) ^ (5 / 2 : ℝ)),
    lt_min hmin_pos (by linarith), le_trans (min_le_left _ _) (le_trans (hx_min hx_max_mem) (le_max_left _ _)),
    ?_⟩
  intro x hx0
  have h1x_pos : 0 < 1 + x := by linarith
  have hrpow_inv : (1 + x) ^ (-(5 / 2 : ℝ)) = ((1 + x) ^ (5 / 2 : ℝ))⁻¹ :=
    Real.rpow_neg h1x_pos.le (5 / 2)
  have hrpow_pos : 0 < (1 + x) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos h1x_pos _
  rcases le_or_gt x X with hle | hgt
  · have hmem : x ∈ Icc 0 X := ⟨hx0, hle⟩
    constructor
    · calc min (φ x_min) (L / 2) * (1 + x) ^ (-(5 / 2 : ℝ))
          ≤ φ x_min * (1 + x) ^ (-(5 / 2 : ℝ)) := by gcongr; exact min_le_left _ _
        _ ≤ φ x * (1 + x) ^ (-(5 / 2 : ℝ)) := by gcongr; exact hx_min hmem
        _ = airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) := by
            dsimp [φ]; rw [hrpow_inv, mul_assoc, mul_inv_cancel₀ hrpow_pos.ne', mul_one]
    · calc airyTwistedLaplace (ceS0 a1 a1') (ceCs * x)
          = φ x * (1 + x) ^ (-(5 / 2 : ℝ)) := by
            dsimp [φ]; rw [hrpow_inv, mul_assoc, mul_inv_cancel₀ hrpow_pos.ne', mul_one]
        _ ≤ φ x_max * (1 + x) ^ (-(5 / 2 : ℝ)) := by gcongr; exact hx_max hmem
        _ ≤ max (φ x_max) (3 * L / 2 * (2 : ℝ) ^ (5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
            gcongr; exact le_max_left _ _
  · have hxX0 : X0 ≤ x := le_trans (le_max_left _ _) hgt.le
    have hx1 : 1 ≤ x := le_trans hX1 hgt.le
    have hx_pos : 0 < x := by linarith
    have hdist := abs_lt.mp (by simpa [Real.dist_eq] using hX0 x hxX0)
    have h_tail_lo : L / 2 ≤ x ^ (5 / 2 : ℝ) * airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) := by linarith
    have h_tail_hi : x ^ (5 / 2 : ℝ) * airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) ≤ 3 * L / 2 := by linarith
    have hxr_pos : 0 < x ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hx_pos _
    have hxr_inv : x ^ (-(5 / 2 : ℝ)) = (x ^ (5 / 2 : ℝ))⁻¹ := Real.rpow_neg hx_pos.le (5 / 2)
    have h_inv1 : (1 + x) ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx_pos (by linarith) (by norm_num)
    have h_inv2 : x ^ (-(5 / 2 : ℝ)) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
      have h2x : (2 * x) ^ (-(5 / 2 : ℝ)) = (2 : ℝ) ^ (-(5 / 2 : ℝ)) * x ^ (-(5 / 2 : ℝ)) :=
        Real.mul_rpow (by norm_num) hx_pos.le
      have hle : (2 * x) ^ (-(5 / 2 : ℝ)) ≤ (1 + x) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos h1x_pos (by linarith) (by norm_num)
      rw [h2x] at hle
      have hmul := mul_le_mul_of_nonneg_left hle h2pow.le
      rwa [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel,
        Real.rpow_zero, one_mul] at hmul
    constructor
    · calc min (φ x_min) (L / 2) * (1 + x) ^ (-(5 / 2 : ℝ))
          ≤ (L / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) := by gcongr; exact min_le_right _ _
        _ ≤ (L / 2) * x ^ (-(5 / 2 : ℝ)) := by gcongr
        _ ≤ (x ^ (5 / 2 : ℝ) * airyTwistedLaplace (ceS0 a1 a1') (ceCs * x)) * x ^ (-(5 / 2 : ℝ)) := by
            gcongr
        _ = airyTwistedLaplace (ceS0 a1 a1') (ceCs * x) := by
            rw [mul_comm (x ^ (5 / 2 : ℝ)), mul_assoc, hxr_inv,
              mul_inv_cancel₀ hxr_pos.ne', mul_one]
    · calc airyTwistedLaplace (ceS0 a1 a1') (ceCs * x)
          = (x ^ (5 / 2 : ℝ) * airyTwistedLaplace (ceS0 a1 a1') (ceCs * x)) * x ^ (-(5 / 2 : ℝ)) := by
            rw [mul_comm (x ^ (5 / 2 : ℝ)), mul_assoc, hxr_inv,
              mul_inv_cancel₀ hxr_pos.ne', mul_one]
        _ ≤ (3 * L / 2) * x ^ (-(5 / 2 : ℝ)) := by gcongr
        _ ≤ (3 * L / 2) * ((2 : ℝ) ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = (3 * L / 2 * (2 : ℝ) ^ (5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)) := by ring
        _ ≤ max (φ x_max) (3 * L / 2 * (2 : ℝ) ^ (5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
            gcongr; exact le_max_right _ _

/-! ### Part 2: Origin Mellin kernel bounds (`ce_rate.tex` Lemma P.2(1), `cel:L3a`, `(cel:4.6)`) -/

/-- Origin Mellin phase `ψ_c(y) = y (π/2 - arctan(y/c)) + (c/2) log(1 + (y/c)²)`. -/
noncomputable def originPsi (c y : ℝ) : ℝ :=
  y * (π / 2 - Real.arctan (y / c)) + (c / 2) * Real.log (1 + (y / c) ^ 2)

/-- Binet-strip exponent `h_B(ν) = ν arctan ν - (1/2) log(1 + ν²)`. -/
noncomputable def hB (ν : ℝ) : ℝ :=
  ν * Real.arctan ν - (1 / 2 : ℝ) * Real.log (1 + ν ^ 2)

/-- `ψ_c(0) = 0` (`(cel:4.6)`). -/
@[simp]
theorem originPsi_zero (c : ℝ) : originPsi c 0 = 0 := by
  simp [originPsi]

/-- Derivative of `ψ_c`: `ψ_c'(y) = π/2 - arctan(y/c)` (`(cel:4.6)`). -/
theorem hasDerivAt_originPsi {c : ℝ} (hc : 0 < c) (y : ℝ) :
    HasDerivAt (originPsi c) (π / 2 - Real.arctan (y / c)) y := by
  have h_div : HasDerivAt (fun t : ℝ => t / c) (1 / c) y := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id y).mul_const c⁻¹
  have h_atan : HasDerivAt (fun t : ℝ => Real.arctan (t / c))
      (1 / (1 + (y / c) ^ 2) * (1 / c)) y := by
    simpa [Function.comp_def] using (Real.hasDerivAt_arctan (y / c)).comp y h_div
  have h_sub : HasDerivAt (fun t : ℝ => π / 2 - Real.arctan (t / c))
      (-(1 / (1 + (y / c) ^ 2) * (1 / c))) y := by
    convert (hasDerivAt_const y (π / 2)).sub h_atan using 1; ring
  have h_first : HasDerivAt (fun t : ℝ => t * (π / 2 - Real.arctan (t / c)))
      (1 * (π / 2 - Real.arctan (y / c)) + y * -(1 / (1 + (y / c) ^ 2) * (1 / c))) y :=
    (hasDerivAt_id y).mul h_sub
  have h_arg_pos : 0 < 1 + (y / c) ^ 2 := by positivity
  have h_arg : HasDerivAt (fun t : ℝ => 1 + (t / c) ^ 2) (2 * (y / c) * (1 / c)) y := by
    convert (hasDerivAt_const y (1 : ℝ)).add (h_div.pow 2) using 1; ring
  have h_log : HasDerivAt (fun t : ℝ => (c / 2) * Real.log (1 + (t / c) ^ 2))
      ((c / 2) * ((2 * (y / c) * (1 / c)) / (1 + (y / c) ^ 2))) y :=
    (h_arg.log h_arg_pos.ne').const_mul (c / 2)
  refine (h_first.add h_log).congr_deriv ?_
  field_simp [hc.ne', h_arg_pos.ne']
  ring

/-- `ψ_c'(y) = π/2 - arctan(y/c) > 0` (`(cel:4.6)`). -/
theorem originPsi_deriv_pos (c y : ℝ) : 0 < π / 2 - Real.arctan (y / c) :=
  sub_pos.mpr (Real.arctan_lt_pi_div_two (y / c))

/-- Linear lower bound `ψ_c(y) ≥ (π/4) y` on `0 ≤ y ≤ c` (`(cel:4.6)`). -/
theorem originPsi_ge_linear {c y : ℝ} (hc : 0 < c) (hy0 : 0 ≤ y) (hyc : y ≤ c) :
    (π / 4) * y ≤ originPsi c y := by
  let f : ℝ → ℝ := fun t => originPsi c t - (π / 4) * t
  have hd : ∀ t : ℝ, HasDerivAt f (π / 2 - Real.arctan (t / c) - π / 4) t := fun t =>
    (hasDerivAt_originPsi hc t).sub (by simpa using (hasDerivAt_id t).const_mul (π / 4))
  have hmono : MonotoneOn f (Icc 0 c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 c) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
    · intro t _; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      have hat : Real.arctan (t / c) ≤ π / 4 :=
        (Real.arctan_mono ((div_le_one hc).mpr ht.2.le)).trans Real.arctan_one.le
      linarith
  have hf0 : f 0 = 0 := by simp [f]
  have hle := hmono ⟨le_rfl, hc.le⟩ ⟨hy0, hyc⟩ hy0
  rw [hf0] at hle
  dsimp [f] at hle
  linarith

/-- Exponential decay bound `e^{-ψ_c(y)} ≤ 2^{-(c - 4)/2} (y/c)^{-4}` for `4 ≤ c ≤ y` (`(cel:4.6)`). -/
theorem exp_neg_originPsi_le {c y : ℝ} (hc : 4 ≤ c) (hcy : c ≤ y) :
    Real.exp (-originPsi c y) ≤ (2 : ℝ) ^ (-((c - 4) / 2)) * (y / c) ^ (-4 : ℝ) := by
  have hc_pos : 0 < c := by linarith
  have hy_pos : 0 < y := by linarith
  have hyc : 1 ≤ y / c := (one_le_div hc_pos).mpr hcy
  have h1 : 0 ≤ y * (π / 2 - Real.arctan (y / c)) :=
    mul_nonneg hy_pos.le (originPsi_deriv_pos c y).le
  have hpsi_ge : (c / 2) * Real.log (1 + (y / c) ^ 2) ≤ originPsi c y := by
    unfold originPsi; linarith
  have hbase_pos : 0 < 1 + (y / c) ^ 2 := by positivity
  have hexp1 : Real.exp (-originPsi c y) ≤ (1 + (y / c) ^ 2) ^ (-(c / 2)) := by
    calc Real.exp (-originPsi c y)
        ≤ Real.exp (-((c / 2) * Real.log (1 + (y / c) ^ 2))) :=
          Real.exp_le_exp.mpr (neg_le_neg hpsi_ge)
      _ = (1 + (y / c) ^ 2) ^ (-(c / 2)) := by
          rw [Real.rpow_def_of_pos hbase_pos]; congr 1; ring
  have hsplit : (1 + (y / c) ^ 2) ^ (-(c / 2)) =
      (1 + (y / c) ^ 2) ^ (-((c - 4) / 2)) * (1 + (y / c) ^ 2) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hbase_pos]; congr 1; ring
  have h_2le : 2 ≤ 1 + (y / c) ^ 2 := by nlinarith
  have h_pow1 : (1 + (y / c) ^ 2) ^ (-((c - 4) / 2)) ≤ (2 : ℝ) ^ (-((c - 4) / 2)) :=
    Real.rpow_le_rpow_of_nonpos zero_lt_two h_2le (by linarith)
  have h_pow2 : (1 + (y / c) ^ 2) ^ (-2 : ℝ) ≤ ((y / c) ^ 2) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have h_pow2' : ((y / c) ^ 2) ^ (-2 : ℝ) = (y / c) ^ (-4 : ℝ) := by
    rw [← Real.rpow_natCast (y / c) 2, ← Real.rpow_mul (by positivity)]; norm_num
  calc Real.exp (-originPsi c y)
      ≤ (1 + (y / c) ^ 2) ^ (-(c / 2)) := hexp1
    _ = (1 + (y / c) ^ 2) ^ (-((c - 4) / 2)) * (1 + (y / c) ^ 2) ^ (-2 : ℝ) := hsplit
    _ ≤ (2 : ℝ) ^ (-((c - 4) / 2)) * ((y / c) ^ 2) ^ (-2 : ℝ) := by gcongr
    _ = (2 : ℝ) ^ (-((c - 4) / 2)) * (y / c) ^ (-4 : ℝ) := by rw [h_pow2']

/-- Exact formula `‖Γ(i y)‖² = π / (y sinh(π y))` for `y > 0` (`ce_rate.tex` Lemma P.2(1)). -/
theorem norm_gamma_pure_imag_sq {y : ℝ} (hy : 0 < y) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2 = π / (y * Real.sinh (π * y)) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz_ne : z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') Complex.I_ne_zero
  have hconj_z : (starRingEnd ℂ) z = -z := by
    dsimp [z]; rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have h_normsq : z * (Complex.Gamma z * Complex.Gamma (-z)) =
      z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj_z, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h_rec : Complex.Gamma (1 - z) = (-z) * Complex.Gamma (-z) := by
    rw [show (1 : ℂ) - z = -z + 1 by ring]
    exact Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz_ne)
  have h_refl := Complex.Gamma_mul_Gamma_one_sub z
  have h_sin : Complex.sin ((π : ℂ) * z) = ((Real.sinh (π * y) : ℝ) : ℂ) * Complex.I := by
    have harg : (π : ℂ) * z = (((π * y : ℝ) : ℂ)) * Complex.I := by dsimp [z]; push_cast; ring
    rw [harg, Complex.sin_mul_I]
    congr 1; rw [← Complex.ofReal_sinh]
  have h_mul_eq : -(z * (Complex.Gamma z * Complex.Gamma (-z))) =
      Complex.Gamma z * Complex.Gamma (1 - z) := by rw [h_rec]; ring
  have h_eq : -(z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ)) =
      ((π : ℂ) / (((Real.sinh (π * y) : ℝ) : ℂ) * Complex.I)) := by
    rw [← h_normsq, h_mul_eq, h_refl, h_sin]
  have h_lhs : -(z * ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ)) =
      ((-(y * ‖Complex.Gamma z‖ ^ 2) : ℝ) : ℂ) * Complex.I := by
    dsimp [z]; push_cast; ring
  have h_rhs : ((π : ℂ) / (((Real.sinh (π * y) : ℝ) : ℂ) * Complex.I)) =
      ((-(π / Real.sinh (π * y)) : ℝ) : ℂ) * Complex.I := by
    rw [div_mul_eq_div_div, div_I]; push_cast; ring
  rw [h_lhs, h_rhs] at h_eq
  have him := congr_arg Complex.im h_eq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero] at him
  have h_eq' : y * ‖Complex.Gamma z‖ ^ 2 = π / Real.sinh (π * y) := by linarith
  calc ‖Complex.Gamma z‖ ^ 2 = (y * ‖Complex.Gamma z‖ ^ 2) / y := by field_simp [hy.ne']
    _ = (π / Real.sinh (π * y)) / y := by rw [h_eq']
    _ = π / (y * Real.sinh (π * y)) := by ring

private lemma self_le_sinh_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  let f : ℝ → ℝ := fun t => Real.sinh t - t
  have hd : ∀ t : ℝ, HasDerivAt f (Real.cosh t - 1) t := fun t =>
    (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
    · intro t _; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t _; rw [(hd t).deriv]; linarith [Real.one_le_cosh t]
  have hf0 : f 0 = 0 := by simp [f]
  have := hmono le_rfl hx hx
  rw [hf0] at this; dsimp [f] at this; linarith

/-- Small-`y` bound `‖Γ(i y)‖ ≤ 1 / y` for `0 < y ≤ 1` (`ce_rate.tex` Lemma P.2(1)). -/
theorem norm_gamma_pure_imag_le_small {y : ℝ} (hy0 : 0 < y) (_hy1 : y ≤ 1) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ 1 / y := by
  have hsq := norm_gamma_pure_imag_sq hy0
  have hsinh : π * y ≤ Real.sinh (π * y) := self_le_sinh_of_nonneg (mul_pos Real.pi_pos hy0).le
  have hle : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2 ≤ (1 / y) ^ 2 := by
    rw [hsq]
    calc π / (y * Real.sinh (π * y))
        ≤ π / (y * (π * y)) := by gcongr
      _ = (1 / y) ^ 2 := by field_simp [Real.pi_ne_zero, hy0.ne']
  exact le_of_sq_le_sq hle (by positivity)

/-- Large-`y` bound `‖Γ(i y)‖ ≤ √(3π) y^{-1/2} e^{-π y / 2}` for `1 ≤ y` (`ce_rate.tex` Lemma P.2(1)). -/
theorem norm_gamma_pure_imag_le_large {y : ℝ} (hy1 : 1 ≤ y) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤
      √(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * y) := by
  have hy0 : 0 < y := by linarith
  have hsq := norm_gamma_pure_imag_sq hy0
  have hpiy1 : 1 ≤ π * y := by nlinarith [Real.pi_gt_three]
  have hexp2 : 3 ≤ Real.exp (2 * (π * y)) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith
    have h3 : Real.exp 2 ≤ Real.exp (2 * (π * y)) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsinh : Real.exp (π * y) / 3 ≤ Real.sinh (π * y) := by
    rw [Real.sinh_eq]
    have hneg : Real.exp (-(π * y)) ≤ Real.exp (π * y) / 3 := by
      have he : Real.exp (π * y) = Real.exp (-(π * y)) * Real.exp (2 * (π * y)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [le_div_iff₀ (by norm_num), he]; gcongr
    linarith
  have hle : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ^ 2 ≤
      (√(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * y)) ^ 2 := by
    rw [hsq]
    have h_rhs : (√(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * y)) ^ 2 =
        3 * π / (y * Real.exp (π * y)) := by
      have hsr : √(3 * π) ^ 2 = 3 * π := Real.sq_sqrt (by positivity)
      have hyr : (y ^ (-(1 / 2 : ℝ))) ^ 2 = y⁻¹ := by
        rw [← Real.rpow_natCast (y ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hy0.le]; norm_num
        rw [Real.rpow_neg_one]
      have hexp_sq : Real.exp (-(π / 2) * y) ^ 2 = (Real.exp (π * y))⁻¹ := by
        rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
      rw [mul_pow, mul_pow, hsr, hyr, hexp_sq]
      field_simp [hy0.ne', (Real.exp_pos (π * y)).ne']
    rw [h_rhs]
    calc π / (y * Real.sinh (π * y))
        ≤ π / (y * (Real.exp (π * y) / 3)) := by gcongr
      _ = 3 * π / (y * Real.exp (π * y)) := by ring
  exact le_of_sq_le_sq hle (by positivity)

/-- Identity `(π/2) y - c h_B(y/c) = ψ_c(y)` (`ce_rate.tex` Lemma P.2(1)). -/
theorem originPsi_eq_sub_hB {c : ℝ} (hc : 0 < c) (y : ℝ) :
    (π / 2) * y - c * hB (y / c) = originPsi c y := by
  unfold hB originPsi
  field_simp [hc.ne']
  ring

/-- Combined Mellin boundary integrand bound on `[1, ∞)` (`ce_rate.tex` Lemma P.2(1)). -/
theorem norm_gamma_mul_exp_hB_le {c y : ℝ} (hc : 0 < c) (hy1 : 1 ≤ y) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * Real.exp (c * hB (y / c)) ≤
      √(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-originPsi c y) := by
  have h1 := mul_le_mul_of_nonneg_right (norm_gamma_pure_imag_le_large hy1)
    (Real.exp_pos (c * hB (y / c))).le
  refine h1.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add, ← originPsi_eq_sub_hB hc y]
  congr 2; ring

/-! ### Axiom audit -/

/-- info: 'FormalResearch.CohnElkies.ceS0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.ceS0_pos

/-- info: 'FormalResearch.CohnElkies.positive_source_S0_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.positive_source_S0_floor

/-- info: 'FormalResearch.CohnElkies.originPsi_ge_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.originPsi_ge_linear

/-- info: 'FormalResearch.CohnElkies.exp_neg_originPsi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.exp_neg_originPsi_le

/-- info: 'FormalResearch.CohnElkies.norm_gamma_pure_imag_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_gamma_pure_imag_sq

/-- info: 'FormalResearch.CohnElkies.norm_gamma_pure_imag_le_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_gamma_pure_imag_le_small

/-- info: 'FormalResearch.CohnElkies.norm_gamma_pure_imag_le_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_gamma_pure_imag_le_large

/-- info: 'FormalResearch.CohnElkies.norm_gamma_mul_exp_hB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.norm_gamma_mul_exp_hB_le

end FormalResearch.CohnElkies
