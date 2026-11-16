module

public import FormalResearch.Special.AiryBound
public import FormalResearch.Special.AiryReal

/-!
# `Ai` on `ℂ`: the free-parameter bound

For every `c > 0` and every `z ∈ ℂ`, completing the square in `s` in the modulus
`|K| = exp(c³/3 - c Re z + Im z · s - c s²)` of the kernel (`norm_airyKernel`) gives

`‖Ai(z)‖ ≤ (1/(2√(π c))) exp(c³/3 - c Re z + (Im z)²/(4c))`   (`airy_norm_le_free_param`),

and the analogous bound for `Ai'` (`airy_deriv_norm_le_free_param`), with the polynomial factor
`(c + |Im z|/(2c)) √(π/c) + 1/c` from `|t| ≤ c + |s|`.  These hold on all of `ℂ`; the choice of `c`
that turns them into the envelope `exp(-(2/3) Re z^{3/2})` is made in `AiryEnvelope`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The exponent `c³/3 - c Re z + (Im z)²/(4c)` of the free-parameter bound. -/
noncomputable def airyParamExp (c : ℝ) (z : ℂ) : ℝ := c ^ 3 / 3 - z.re * c + z.im ^ 2 / (4 * c)

lemma airyParamExp_complete_square {c : ℝ} (hc : 0 < c) (z : ℂ) (s : ℝ) :
    c ^ 3 / 3 - z.re * c + z.im * s - c * s ^ 2 =
      airyParamExp c z - c * (s - z.im / (2 * c)) ^ 2 := by
  unfold airyParamExp
  field_simp
  ring

lemma integral_gauss_shift {c : ℝ} (s₀ : ℝ) :
    ∫ s : ℝ, Real.exp (-c * (s - s₀) ^ 2) = √(π / c) := by
  rw [integral_sub_right_eq_self (fun s : ℝ => Real.exp (-c * s ^ 2)) s₀]
  exact integral_gaussian c

lemma integral_abs_gauss_shift {c : ℝ} (hc : 0 < c) (s₀ : ℝ) :
    ∫ s : ℝ, |s - s₀| * Real.exp (-c * (s - s₀) ^ 2) = 1 / c := by
  rw [integral_sub_right_eq_self (fun s : ℝ => |s| * Real.exp (-c * s ^ 2)) s₀]
  exact integral_abs_gauss hc

lemma integrable_gauss_shift {c : ℝ} (hc : 0 < c) (s₀ : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-c * (s - s₀) ^ 2)) :=
  (integrable_exp_neg_mul_sq hc).comp_sub_right s₀

lemma integrable_abs_gauss_shift {c : ℝ} (hc : 0 < c) (s₀ : ℝ) :
    Integrable (fun s : ℝ => |s - s₀| * Real.exp (-c * (s - s₀) ^ 2)) := by
  have h : Integrable (fun s : ℝ => |s| * Real.exp (-c * s ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hc (s := (1 : ℝ)) (by norm_num)
    have h2 := this.norm
    refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact h.comp_sub_right s₀

lemma norm_airyPoly_zero_eq {c : ℝ} (hc : 0 < c) (z : ℂ) (s : ℝ) :
    ‖airyPoly 0 c z s‖ =
      Real.exp (airyParamExp c z) * Real.exp (-c * (s - z.im / (2 * c)) ^ 2) := by
  rw [norm_airyPoly, ← Real.exp_add, airyParamExp_complete_square hc]
  simp only [pow_zero, one_mul]
  congr 1; ring

lemma norm_airyPoly_one_eq {c : ℝ} (hc : 0 < c) (z : ℂ) (s : ℝ) :
    ‖airyPoly 1 c z s‖ =
      ‖airyLine c s‖ * (Real.exp (airyParamExp c z) *
        Real.exp (-c * (s - z.im / (2 * c)) ^ 2)) := by
  rw [norm_airyPoly, ← Real.exp_add, airyParamExp_complete_square hc]
  simp only [pow_one]
  congr 2; ring

/-- **Free-parameter bound for `Ai`**: for every `c > 0` and `z ∈ ℂ`,
`‖Ai(z)‖ ≤ (1/(2π)) √(π/c) exp(c³/3 - c Re z + (Im z)²/(4c))`. -/
theorem airy_norm_le_free_param {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ‖airyAiC z‖ ≤ 1 / (2 * π) * (Real.exp (airyParamExp c z) * √(π / c)) := by
  rw [airyAiC_eq_airyMom hc]
  refine (norm_airyMom_le_integral 0 c z).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity))
  simp_rw [norm_airyPoly_zero_eq hc]
  rw [integral_const_mul, integral_gauss_shift]

/-- **Free-parameter bound for `Ai'`**: for every `c > 0` and `z ∈ ℂ`,
`‖Ai'(z)‖ ≤ (1/(2π)) exp(c³/3 - c Re z + (Im z)²/(4c)) · ((c + |Im z|/(2c)) √(π/c) + 1/c)`. -/
theorem airy_deriv_norm_le_free_param {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ‖deriv airyAiC z‖ ≤ 1 / (2 * π) * (Real.exp (airyParamExp c z) *
      ((c + |z.im| / (2 * c)) * √(π / c) + 1 / c)) := by
  rw [deriv_airyAiC hc]
  refine (norm_airyMom_le_integral 1 c z).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  set s₀ := z.im / (2 * c) with hs₀
  have hs₀' : |s₀| = |z.im| / (2 * c) := by
    rw [hs₀, abs_div, abs_of_pos (by positivity : 0 < 2 * c)]
  set M := Real.exp (airyParamExp c z)
  have hMpos : 0 < M := Real.exp_pos _
  have hbound : ∀ s : ℝ, ‖airyPoly 1 c z s‖ ≤
      M * ((c + |s₀|) * Real.exp (-c * (s - s₀) ^ 2) + |s - s₀| * Real.exp (-c * (s - s₀) ^ 2)) := by
    intro s
    rw [norm_airyPoly_one_eq hc]
    have h1 : ‖airyLine c s‖ ≤ (c + |s₀|) + |s - s₀| := by
      refine (norm_airyLine_le c s).trans ?_
      have : |s| ≤ |s - s₀| + |s₀| := by
        simpa using abs_add_le (s - s₀) s₀
      rw [abs_of_pos hc]; linarith
    have hE : 0 ≤ M * Real.exp (-c * (s - s₀) ^ 2) := by positivity
    calc ‖airyLine c s‖ * (M * Real.exp (-c * (s - s₀) ^ 2))
        ≤ ((c + |s₀|) + |s - s₀|) * (M * Real.exp (-c * (s - s₀) ^ 2)) :=
          mul_le_mul_of_nonneg_right h1 hE
      _ = _ := by ring
  have hint1 : Integrable (fun s => ‖airyPoly 1 c z s‖) := (integrable_airyPoly hc 1 z).norm
  have hint2 : Integrable (fun s : ℝ => M * ((c + |s₀|) * Real.exp (-c * (s - s₀) ^ 2) +
      |s - s₀| * Real.exp (-c * (s - s₀) ^ 2))) :=
    (((integrable_gauss_shift hc s₀).const_mul (c + |s₀|)).add (integrable_abs_gauss_shift hc s₀)).const_mul M
  calc ∫ s, ‖airyPoly 1 c z s‖
      ≤ ∫ s : ℝ, M * ((c + |s₀|) * Real.exp (-c * (s - s₀) ^ 2) +
          |s - s₀| * Real.exp (-c * (s - s₀) ^ 2)) := integral_mono hint1 hint2 hbound
    _ = M * ((c + |z.im| / (2 * c)) * √(π / c) + 1 / c) := by
        rw [integral_const_mul, integral_add ((integrable_gauss_shift hc s₀).const_mul _)
          (integrable_abs_gauss_shift hc s₀), integral_const_mul, integral_gauss_shift,
          integral_abs_gauss_shift hc, hs₀']

end FormalResearch.Special
