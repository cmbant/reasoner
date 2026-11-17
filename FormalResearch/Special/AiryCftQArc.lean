module

public import FormalResearch.Special.AiryCftQUnfold
public import FormalResearch.Special.AiryCftQDefect

/-!
# Theorem D against the Hardy arc integral: `|P_R - I_R| ≤ 30√π · a ∫_0^π |G(ae^{iφ})| dφ`, `R = a²`

On a good circle `|u| = R = a²` (zero-free for `Ai`, ratio bounds `|R_±| e ≤ 30√π`), the integral form of Theorem D
(`airyQ_defect_bound_int`) is bounded, after the unfolding `u = -z²`, `z = a e^{iφ}` (`φ ∈ [0,π]`; the upper half circle
is `φ ∈ [π/2,π]`, the lower one `φ ∈ [0,π/2]`) and `|f R_±| ≤ 30√π |f|/e = 30√π |G(z)|/|z|` (Lemma U), by

`|Σ_{n ≤ N} f(a_n)/Ai'(a_n)² - ∫_{-R}^{R} f| ≤ 30√π · a ∫_0^π |G(a e^{iφ})| dφ`  (`airyQ_defect_le_arc`),

with `G = airyQG f` (`AiryCftQUnfold`).  The right side is `30√π` times the `ℍ`-semicircle integral `∫_{S_a} |G||dz|`, which the
Hardy-space Fejér–Riesz bound (`FormalResearch.Hardy.hardy_arc_le_poly`, `hardy_arc_tendsto_zero`) bounds by `(1/2)‖f‖_b` and sends to
`0`.  All **proved**; `f` entire.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

lemma circleMap_sq_neg (a φ : ℝ) :
    circleMap 0 (a ^ 2) (2 * φ - π) = -(circleMap 0 a φ) ^ 2 := by
  simp only [circleMap, zero_add]
  have h1 : Complex.exp (((2 * φ - π : ℝ) : ℂ) * I) = -Complex.exp ((φ : ℂ) * I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    have : ((2 * φ - π : ℝ) : ℂ) * I = ((2 : ℕ) : ℂ) * ((φ : ℂ) * I) - π * I := by push_cast; ring
    rw [this, Complex.exp_sub, Complex.exp_pi_mul_I]; simp [div_neg]
  rw [h1, mul_pow]; push_cast; ring

lemma circleMap_sq_neg' (a φ : ℝ) :
    circleMap 0 (a ^ 2) (2 * φ + π) = -(circleMap 0 a φ) ^ 2 := by
  have := circleMap_sq_neg a φ
  rw [← this, show 2 * φ + π = 2 * φ - π + 2 * π by ring, periodic_circleMap]

lemma integral_upper_unfold (F : ℝ → ℝ) :
    ∫ θ in (0 : ℝ)..π, F θ = 2 * ∫ φ in (π / 2)..π, F (2 * φ - π) := by
  have := intervalIntegral.integral_comp_mul_sub (a := π / 2) (b := π) F (two_ne_zero) π
  rw [smul_eq_mul] at this
  have e1 : (2 : ℝ) * (π / 2) - π = 0 := by ring
  have e2 : (2 : ℝ) * π - π = π := by ring
  rw [e1, e2] at this
  rw [this]; field_simp

lemma integral_lower_unfold (F : ℝ → ℝ) :
    ∫ θ in π..(2 * π), F θ = 2 * ∫ φ in (0 : ℝ)..(π / 2), F (2 * φ + π) := by
  have := intervalIntegral.integral_comp_mul_add (a := 0) (b := π / 2) F (two_ne_zero) π
  rw [smul_eq_mul] at this
  have e1 : (2 : ℝ) * 0 + π = π := by ring
  have e2 : (2 : ℝ) * (π / 2) + π = 2 * π := by ring
  rw [e1, e2] at this
  rw [this]; field_simp

/-- Both parametrisations of the upper (`φ ∈ [π/2,π]`) and lower (`φ ∈ [0,π/2]`) half circle unfold to one arc integral. -/
theorem airyQ_defect_le_arc {N : ℕ} {a : ℝ} (ha : 0 < a)
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) (a ^ 2))
    (hup : ∀ u : ℂ, ‖u‖ = a ^ 2 → 0 ≤ u.im →
      ‖(airyBiC u - I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π)
    (hlo : ∀ u : ℂ, ‖u‖ = a ^ 2 → u.im ≤ 0 →
      ‖(airyBiC u + I * airyAiC u) / airyAiC u‖ * airyEnv u ≤ 30 * √π)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ‖(∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-(a ^ 2))..(a ^ 2), f (x : ℂ)‖ ≤
      30 * √π * (a * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 a φ)‖) := by
  have hb := airyQ_defect_bound_int hD hf
  have hR : 0 < a ^ 2 := by positivity
  set w : ℝ → ℂ := circleMap 0 (a ^ 2) with hw
  have hGc : Continuous (fun φ : ℝ => ‖airyQG f (circleMap 0 a φ)‖) :=
    ((airyQ_differentiable_G hf).continuous.comp (continuous_circleMap 0 a)).norm
  have hnn : ∀ φ : ℝ, 0 ≤ ‖airyQG f (circleMap 0 a φ)‖ := fun φ => norm_nonneg _
  -- generic monotonicity (the left integrand is continuous, but we do not need it)
  have hmono : ∀ (F g : ℝ → ℝ) (x y : ℝ), x ≤ y → (∀ φ ∈ Icc x y, 0 ≤ F φ ∧ F φ ≤ g φ) →
      IntervalIntegrable g volume x y → ∫ φ in x..y, F φ ≤ ∫ φ in x..y, g φ := by
    intro F g x y hxy h hg
    by_cases hF : IntervalIntegrable F volume x y
    · exact intervalIntegral.integral_mono_on hxy hF hg (fun φ hφ => (h φ hφ).2)
    · rw [intervalIntegral.integral_undef hF]
      exact intervalIntegral.integral_nonneg hxy (fun φ hφ => (h φ hφ).1.trans (h φ hφ).2)
  have hz : ∀ φ : ℝ, φ ∈ Icc (0 : ℝ) π → 0 ≤ (circleMap 0 a φ).im := fun φ hφ =>
    FormalResearch.Hardy.circleMap_im_nonneg ha.le hφ
  have hnorm : ∀ φ : ℝ, ‖circleMap 0 a φ‖ = a := fun φ => by rw [norm_circleMap_zero, abs_of_pos ha]
  -- pointwise bound for the upper half
  have hpt_up : ∀ φ ∈ Icc (π / 2) π,
      0 ≤ ‖f (w (2 * φ - π)) * ((airyBiC (w (2 * φ - π)) - I * airyAiC (w (2 * φ - π))) /
          airyAiC (w (2 * φ - π)))‖ ∧
      ‖f (w (2 * φ - π)) * ((airyBiC (w (2 * φ - π)) - I * airyAiC (w (2 * φ - π))) /
          airyAiC (w (2 * φ - π)))‖ ≤ 30 * √π / a * ‖airyQG f (circleMap 0 a φ)‖ := by
    intro φ hφ
    refine ⟨norm_nonneg _, ?_⟩
    have hφ0 : φ ∈ Icc (0 : ℝ) π := ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
    have hu : w (2 * φ - π) = -(circleMap 0 a φ) ^ 2 := circleMap_sq_neg a φ
    have hun : ‖w (2 * φ - π)‖ = a ^ 2 := by rw [hw, norm_circleMap_zero, abs_of_pos hR]
    have huim : 0 ≤ (w (2 * φ - π)).im :=
      FormalResearch.Hardy.circleMap_im_nonneg hR.le ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
    have h1 := hup _ hun huim
    have he := airyEnv_pos (w (2 * φ - π))
    have hG := airyQ_norm_G f (hz φ hφ0)
    rw [hnorm, ← hu] at hG
    rw [hG, norm_mul]
    have hR' : ‖(airyBiC (w (2 * φ - π)) - I * airyAiC (w (2 * φ - π))) / airyAiC (w (2 * φ - π))‖ ≤
        30 * √π / airyEnv (w (2 * φ - π)) := by rw [le_div_iff₀ he]; exact h1
    calc ‖f (w (2 * φ - π))‖ * ‖(airyBiC (w (2 * φ - π)) - I * airyAiC (w (2 * φ - π))) /
          airyAiC (w (2 * φ - π))‖
        ≤ ‖f (w (2 * φ - π))‖ * (30 * √π / airyEnv (w (2 * φ - π))) := by gcongr
      _ = 30 * √π / a * (a * (‖f (w (2 * φ - π))‖ / airyEnv (w (2 * φ - π)))) := by field_simp
  have hpt_lo : ∀ φ ∈ Icc (0 : ℝ) (π / 2),
      0 ≤ ‖f (w (2 * φ + π)) * ((airyBiC (w (2 * φ + π)) + I * airyAiC (w (2 * φ + π))) /
          airyAiC (w (2 * φ + π)))‖ ∧
      ‖f (w (2 * φ + π)) * ((airyBiC (w (2 * φ + π)) + I * airyAiC (w (2 * φ + π))) /
          airyAiC (w (2 * φ + π)))‖ ≤ 30 * √π / a * ‖airyQG f (circleMap 0 a φ)‖ := by
    intro φ hφ
    refine ⟨norm_nonneg _, ?_⟩
    have hφ0 : φ ∈ Icc (0 : ℝ) π := ⟨hφ.1, by linarith [hφ.2, Real.pi_pos]⟩
    have hu : w (2 * φ + π) = -(circleMap 0 a φ) ^ 2 := circleMap_sq_neg' a φ
    have hun : ‖w (2 * φ + π)‖ = a ^ 2 := by rw [hw, norm_circleMap_zero, abs_of_pos hR]
    have huim : (w (2 * φ + π)).im ≤ 0 := by
      simp only [hw, circleMap, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      have : Real.sin (2 * φ + π) = -Real.sin (2 * φ) := Real.sin_add_pi _
      rw [this]
      have : 0 ≤ Real.sin (2 * φ) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1]) (by linarith [hφ.2])
      nlinarith [sq_nonneg a]
    have h1 := hlo _ hun huim
    have he := airyEnv_pos (w (2 * φ + π))
    have hG := airyQ_norm_G f (hz φ hφ0)
    rw [hnorm, ← hu] at hG
    rw [hG, norm_mul]
    have hR' : ‖(airyBiC (w (2 * φ + π)) + I * airyAiC (w (2 * φ + π))) / airyAiC (w (2 * φ + π))‖ ≤
        30 * √π / airyEnv (w (2 * φ + π)) := by rw [le_div_iff₀ he]; exact h1
    calc ‖f (w (2 * φ + π))‖ * ‖(airyBiC (w (2 * φ + π)) + I * airyAiC (w (2 * φ + π))) /
          airyAiC (w (2 * φ + π))‖
        ≤ ‖f (w (2 * φ + π))‖ * (30 * √π / airyEnv (w (2 * φ + π))) := by gcongr
      _ = 30 * √π / a * (a * (‖f (w (2 * φ + π))‖ / airyEnv (w (2 * φ + π)))) := by field_simp
  rw [integral_upper_unfold, integral_lower_unfold] at hb
  have hup' := hmono _ _ (π / 2) π (by linarith [Real.pi_pos]) hpt_up
    ((hGc.const_mul (30 * √π / a)).intervalIntegrable _ _)
  have hlo' := hmono _ _ 0 (π / 2) (by linarith [Real.pi_pos]) hpt_lo
    ((hGc.const_mul (30 * √π / a)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at hup' hlo'
  have hsplit : ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 a φ)‖ =
      (∫ φ in (0 : ℝ)..(π / 2), ‖airyQG f (circleMap 0 a φ)‖) +
        ∫ φ in (π / 2)..π, ‖airyQG f (circleMap 0 a φ)‖ :=
    (intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)).symm
  rw [hsplit]
  refine hb.trans ?_
  have hsq : (a ^ 2 / 2) * (2 * (30 * √π / a) * ((∫ φ in (0 : ℝ)..(π / 2), ‖airyQG f (circleMap 0 a φ)‖) +
      ∫ φ in (π / 2)..π, ‖airyQG f (circleMap 0 a φ)‖)) =
      30 * √π * (a * ((∫ φ in (0 : ℝ)..(π / 2), ‖airyQG f (circleMap 0 a φ)‖) +
      ∫ φ in (π / 2)..π, ‖airyQG f (circleMap 0 a φ)‖)) := by field_simp
  rw [← hsq]
  have hc : 0 ≤ a ^ 2 / 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hc
  nlinarith [hup', hlo']

/-- info: 'FormalResearch.Special.airyQ_defect_le_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_defect_le_arc

end FormalResearch.Special
