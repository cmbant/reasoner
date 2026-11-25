module

public import FormalResearch.SignUncertainty.CtOuterRatInt

/-!
# Rational integrals for the `ζ(3)` evaluation of `c_{3,1t2}`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (2) ("`c_{3,1t2} = ½ζ(3) - 1/3`").  **Proved**:
for every real `m ≥ 1`,
`∫_0^∞ (6 - 2t²)/(1+t²)³ · 2t²/(m²+t²) dt = 2π/(m+1)³` (partial fractions with explicit antiderivatives; the
degenerate case `m = 1` is a separate antiderivative), and `∫_0^∞ (6-2t²)/(1+t²)³ dt = π`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `r(t) = (6 - 2t²)/(1+t²)³`. -/
noncomputable def rG (t : ℝ) : ℝ := (6 - 2 * t ^ 2) / (1 + t ^ 2) ^ 3

/-- The integrand `r(t) · 2t²/(m²+t²)`. -/
noncomputable def rP (m t : ℝ) : ℝ := rG t * (2 * t ^ 2 / (m ^ 2 + t ^ 2))

lemma hasDerivAt_rat1 (t : ℝ) :
    HasDerivAt (fun t : ℝ => t / (1 + t ^ 2)) ((1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
  have h4 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).const_add 1)
  exact ((hasDerivAt_id t).div h4 (by positivity)).congr_deriv (by simp only [id]; field_simp; ring)

lemma hasDerivAt_rat2 (t : ℝ) :
    HasDerivAt (fun t : ℝ => t / (1 + t ^ 2) ^ 2) ((1 - 3 * t ^ 2) / (1 + t ^ 2) ^ 3) t := by
  have h4 : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ 2) (2 * (1 + t ^ 2) * (2 * t)) t := by
    have := (((hasDerivAt_pow 2 t).const_add 1).pow 2)
    refine this.congr_deriv ?_
    simp
  exact ((hasDerivAt_id t).div h4 (by positivity)).congr_deriv (by simp only [id]; field_simp; ring)

/-- Antiderivative for `m ≠ 1`. -/
noncomputable def Fm (m t : ℝ) : ℝ :=
  4 * m * (m ^ 2 + 3) / (m ^ 2 - 1) ^ 3 * Real.arctan (t / m) -
    4 * (3 * m ^ 2 + 1) / (m ^ 2 - 1) ^ 3 * Real.arctan t +
    (2 * (5 * m ^ 2 - 1) / (m ^ 2 - 1) ^ 2 * (t / (1 + t ^ 2)) -
      8 / (m ^ 2 - 1) * (t / (2 * (1 + t ^ 2) ^ 2) + 3 * t / (4 * (1 + t ^ 2))))

lemma hasDerivAt_Fm {m : ℝ} (hm : 0 < m) (hm1 : m ≠ 1) (t : ℝ) : HasDerivAt (Fm m) (rP m t) t := by
  have hM : m ^ 2 - 1 ≠ 0 := by
    intro h
    have : (m - 1) * (m + 1) = 0 := by linarith only [h, show (m - 1) * (m + 1) = m ^ 2 - 1 by ring]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hm1 (by linarith)
    · linarith
  have h1 := (hasDerivAt_arctan_div hm t).const_mul (4 * m * (m ^ 2 + 3) / (m ^ 2 - 1) ^ 3)
  have h2 := (Real.hasDerivAt_arctan t).const_mul (4 * (3 * m ^ 2 + 1) / (m ^ 2 - 1) ^ 3)
  have h3 := (hasDerivAt_rat1 t).const_mul (2 * (5 * m ^ 2 - 1) / (m ^ 2 - 1) ^ 2)
  have h4 := (((hasDerivAt_rat2 t).div_const 2).add ((hasDerivAt_rat1 t).const_mul 3 |>.div_const 4)).const_mul
    (8 / (m ^ 2 - 1))
  have h5 := ((h1.sub h2).add (h3.sub h4))
  convert h5 using 1
  · funext y
    simp only [Fm, Pi.add_apply, Pi.sub_apply]
    have e1 : (1 + y ^ 2) ≠ 0 := by positivity
    field_simp
  · unfold rP rG
    have e1 : (1 + t ^ 2) ≠ 0 := by positivity
    have e2 : (m ^ 2 + t ^ 2) ≠ 0 := by positivity
    field_simp
    ring


lemma tendsto_t_div_pow : ∀ k : ℕ, 1 ≤ k → Tendsto (fun t : ℝ => t / (1 + t ^ 2) ^ k) atTop (𝓝 0) := by
  intro k hk
  refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop 0] with t ht using by positivity
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 + t ^ 2 ≤ (1 + t ^ 2) ^ k := by
      have : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
      calc 1 + t ^ 2 = (1 + t ^ 2) ^ 1 := (pow_one _).symm
        _ ≤ (1 + t ^ 2) ^ k := pow_le_pow_right₀ this hk
    have e : t⁻¹ * (1 + t ^ 2) = t⁻¹ + t := by field_simp
    have h2 : t⁻¹ * (1 + t ^ 2) ≤ t⁻¹ * (1 + t ^ 2) ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)
    have : 0 < t⁻¹ := by positivity
    linarith only [e, h2, this]

lemma hasDerivAt_rat3 (t : ℝ) :
    HasDerivAt (fun t : ℝ => t / (1 + t ^ 2) ^ 3) ((1 - 5 * t ^ 2) / (1 + t ^ 2) ^ 4) t := by
  have h4 : HasDerivAt (fun s : ℝ => (1 + s ^ 2) ^ 3) (3 * (1 + t ^ 2) ^ 2 * (2 * t)) t := by
    have := (((hasDerivAt_pow 2 t).const_add 1).pow 3)
    refine this.congr_deriv ?_
    simp
  exact ((hasDerivAt_id t).div h4 (by positivity)).congr_deriv (by simp only [id]; field_simp; ring)

/-- `A₂ = ∫ (1+t²)^{-2}`, `A₃`, `A₄`. -/
noncomputable def A2 (t : ℝ) : ℝ := t / (1 + t ^ 2) / 2 + Real.arctan t / 2
noncomputable def A3 (t : ℝ) : ℝ := t / (1 + t ^ 2) ^ 2 / 4 + 3 / 4 * A2 t
noncomputable def A4 (t : ℝ) : ℝ := t / (1 + t ^ 2) ^ 3 / 6 + 5 / 6 * A3 t

lemma hasDerivAt_A2 (t : ℝ) : HasDerivAt A2 (1 / (1 + t ^ 2) ^ 2) t := by
  have h1 := ((hasDerivAt_rat1 t).div_const 2).add ((Real.hasDerivAt_arctan t).div_const 2)
  refine h1.congr_deriv ?_
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  ring

lemma hasDerivAt_A3 (t : ℝ) : HasDerivAt A3 (1 / (1 + t ^ 2) ^ 3) t := by
  have h1 := ((hasDerivAt_rat2 t).div_const 4).add ((hasDerivAt_A2 t).const_mul (3 / 4))
  refine h1.congr_deriv ?_
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  ring

lemma hasDerivAt_A4 (t : ℝ) : HasDerivAt A4 (1 / (1 + t ^ 2) ^ 4) t := by
  have h1 := ((hasDerivAt_rat3 t).div_const 6).add ((hasDerivAt_A3 t).const_mul (5 / 6))
  refine h1.congr_deriv ?_
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  ring

lemma A2_zero : A2 0 = 0 := by simp [A2]
lemma A3_zero : A3 0 = 0 := by simp [A3, A2_zero]
lemma A4_zero : A4 0 = 0 := by simp [A4, A3_zero]

lemma tendsto_A2 : Tendsto A2 atTop (𝓝 (π / 4)) := by
  have h0 : Tendsto (fun t : ℝ => t / (1 + t ^ 2) / 2) atTop (𝓝 0) := by
    have := (tendsto_t_div_pow 1 le_rfl).div_const 2
    simpa using this
  have h1 : Tendsto (fun t : ℝ => Real.arctan t / 2) atTop (𝓝 (π / 4)) := by
    have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).div_const 2
    convert this using 2; ring
  have := h0.add h1
  rw [zero_add] at this
  exact this

lemma tendsto_A3 : Tendsto A3 atTop (𝓝 (3 * π / 16)) := by
  have h0 : Tendsto (fun t : ℝ => t / (1 + t ^ 2) ^ 2 / 4) atTop (𝓝 0) := by
    have := (tendsto_t_div_pow 2 (by norm_num)).div_const 4
    simpa using this
  have := h0.add (tendsto_A2.const_mul (3 / 4))
  unfold A3
  convert this using 2; ring

lemma tendsto_A4 : Tendsto A4 atTop (𝓝 (5 * π / 32)) := by
  have h0 : Tendsto (fun t : ℝ => t / (1 + t ^ 2) ^ 3 / 6) atTop (𝓝 0) := by
    have := (tendsto_t_div_pow 3 (by norm_num)).div_const 6
    simpa using this
  have := h0.add (tendsto_A3.const_mul (5 / 6))
  unfold A4
  convert this using 2; ring

lemma integrableOn_inv_pow (k : ℕ) (hk : 1 ≤ k) : IntegrableOn (fun t : ℝ => 1 / (1 + t ^ 2) ^ k) (Ioi 0) := by
  refine Integrable.mono' integrableOn_inv_one_add_sq ?_ ?_
  · exact (Continuous.div continuous_const (by fun_prop) (fun t => by positivity)).aestronglyMeasurable
  · filter_upwards with t
    have h1 : 0 < 1 + t ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left (by norm_num) h1
    calc 1 + t ^ 2 = (1 + t ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ (1 + t ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith only [sq_nonneg t]) hk

lemma abs_rG_le (t : ℝ) : |rG t| ≤ 6 / (1 + t ^ 2) := by
  unfold rG
  have h1 : 0 < 1 + t ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + t ^ 2) ^ 3), div_le_div_iff₀ (by positivity) h1]
  have : |6 - 2 * t ^ 2| ≤ 6 * (1 + t ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith only [sq_nonneg t]
  have h2 : 1 ≤ (1 + t ^ 2) ^ 2 := by nlinarith only [sq_nonneg t]
  calc |6 - 2 * t ^ 2| * (1 + t ^ 2) ≤ 6 * (1 + t ^ 2) * (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right this h1.le
    _ = 6 * (1 + t ^ 2) ^ 2 := by ring
    _ ≤ 6 * (1 + t ^ 2) ^ 3 := by
        have : (1 + t ^ 2) ^ 2 ≤ (1 + t ^ 2) ^ 3 := pow_le_pow_right₀ (by nlinarith only [sq_nonneg t]) (by norm_num)
        linarith only [this]

lemma integrableOn_rG : IntegrableOn rG (Ioi 0) := by
  have h := integrableOn_inv_one_add_sq.const_mul 6
  refine Integrable.mono' h ?_ ?_
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs]
    refine (abs_rG_le t).trans (le_of_eq ?_)
    ring

lemma integrableOn_rP {m : ℝ} (hm : 0 < m) : IntegrableOn (rP m) (Ioi 0) := by
  have h := integrableOn_inv_one_add_sq.const_mul 12
  refine Integrable.mono' h ?_ ?_
  · unfold rP rG
    exact (Continuous.mul (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity))
      (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity))).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs]
    unfold rP
    rw [abs_mul]
    have h2 : |2 * t ^ 2 / (m ^ 2 + t ^ 2)| ≤ 2 := by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      nlinarith only [sq_nonneg m, sq_nonneg t]
    calc |rG t| * |2 * t ^ 2 / (m ^ 2 + t ^ 2)| ≤ (6 / (1 + t ^ 2)) * 2 :=
          mul_le_mul (abs_rG_le t) h2 (abs_nonneg _) (by positivity)
      _ = 12 * (1 / (1 + t ^ 2)) := by ring

/-- `∫_0^∞ r = π`. -/
theorem integral_rG : ∫ t in Ioi (0 : ℝ), rG t = π := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t => 8 * A3 t - 2 * A2 t) (rG x) x := fun x _ => by
    have := ((hasDerivAt_A3 x).const_mul 8).sub ((hasDerivAt_A2 x).const_mul 2)
    refine this.congr_deriv ?_
    unfold rG
    have : (1 + x ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hl : Tendsto (fun t => 8 * A3 t - 2 * A2 t) atTop (𝓝 π) := by
    have := (tendsto_A3.const_mul 8).sub (tendsto_A2.const_mul 2)
    convert this using 2; ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd integrableOn_rG hl]
  simp [A2_zero, A3_zero]

/-- `m = 1`: `∫_0^∞ r(t) · 2t²/(1+t²) dt = π/4`. -/
theorem integral_rP_one : ∫ t in Ioi (0 : ℝ), rP 1 t = 2 * π / (1 + 1) ^ 3 := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun t => 2 * (-2 * A2 t + 10 * A3 t - 8 * A4 t)) (rP 1 x) x := fun x _ => by
    have := ((((hasDerivAt_A2 x).const_mul (-2)).add ((hasDerivAt_A3 x).const_mul 10)).sub
      ((hasDerivAt_A4 x).const_mul 8)).const_mul 2
    refine this.congr_deriv ?_
    unfold rP rG
    have : (1 + x ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hl : Tendsto (fun t => 2 * (-2 * A2 t + 10 * A3 t - 8 * A4 t)) atTop (𝓝 (2 * π / (1 + 1) ^ 3)) := by
    have := (((tendsto_A2.const_mul (-2)).add (tendsto_A3.const_mul 10)).sub (tendsto_A4.const_mul 8)).const_mul 2
    convert this using 2; ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_rP one_pos) hl]
  simp [A2_zero, A3_zero, A4_zero]


theorem integral_rP_gt {m : ℝ} (hm : 1 < m) : ∫ t in Ioi (0 : ℝ), rP m t = 2 * π / (m + 1) ^ 3 := by
  have hm0 : 0 < m := by linarith
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (Fm m) (rP m x) x := fun x _ =>
    hasDerivAt_Fm hm0 hm.ne' x
  have hA1 : Tendsto (fun t : ℝ => Real.arctan (t / m)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_div_const hm0)
  have hA2 : Tendsto Real.arctan atTop (𝓝 (π / 2)) := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have hR1 : Tendsto (fun t : ℝ => t / (1 + t ^ 2)) atTop (𝓝 0) := by
    simpa using tendsto_t_div_pow 1 le_rfl
  have hR2 : Tendsto (fun t : ℝ => t / (2 * (1 + t ^ 2) ^ 2)) atTop (𝓝 0) := by
    have := (tendsto_t_div_pow 2 (by norm_num)).div_const 2
    simp only [zero_div] at this
    refine this.congr (fun t => ?_)
    have : (1 + t ^ 2) ≠ 0 := by positivity
    field_simp
  have hR3 : Tendsto (fun t : ℝ => 3 * t / (4 * (1 + t ^ 2))) atTop (𝓝 0) := by
    have := ((tendsto_t_div_pow 1 le_rfl).const_mul 3).div_const 4
    simp only [pow_one, mul_zero, zero_div] at this
    refine this.congr (fun t => ?_)
    have : (1 + t ^ 2) ≠ 0 := by positivity
    field_simp
  have hl : Tendsto (Fm m) atTop (𝓝 (4 * m * (m ^ 2 + 3) / (m ^ 2 - 1) ^ 3 * (π / 2) -
      4 * (3 * m ^ 2 + 1) / (m ^ 2 - 1) ^ 3 * (π / 2) +
      (2 * (5 * m ^ 2 - 1) / (m ^ 2 - 1) ^ 2 * 0 - 8 / (m ^ 2 - 1) * (0 + 0)))) := by
    unfold Fm
    exact (((hA1.const_mul _).sub (hA2.const_mul _)).add
      ((hR1.const_mul _).sub ((hR2.add hR3).const_mul _)))
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_rP hm0) hl]
  have h0 : Fm m 0 = 0 := by simp [Fm]
  rw [h0]
  have e1 : m - 1 ≠ 0 := by linarith
  have e2 : m + 1 ≠ 0 := by linarith
  have e3 : m ^ 2 - 1 ≠ 0 := by
    have : m ^ 2 - 1 = (m - 1) * (m + 1) := by ring
    rw [this]; exact mul_ne_zero e1 e2
  field_simp
  ring

/-- **`∫_0^∞ r(t) · 2t²/(m²+t²) dt = 2π/(m+1)³` for `m ≥ 1`.** -/
theorem integral_rP {m : ℝ} (hm : 1 ≤ m) : ∫ t in Ioi (0 : ℝ), rP m t = 2 * π / (m + 1) ^ 3 := by
  rcases hm.eq_or_lt with h | h
  · rw [← h]; exact integral_rP_one
  · exact integral_rP_gt h

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_rG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_rG

/-- info: 'FormalResearch.SignUncertainty.CtOuter.integral_rP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_rP

end FormalResearch.SignUncertainty.CtOuter
