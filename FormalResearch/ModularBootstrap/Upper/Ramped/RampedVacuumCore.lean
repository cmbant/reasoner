module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumProfile

/-!
# The window integral estimate for an integrable profile (`rem:thmU` Step (5), Langer window)

Pure real analysis.  For `w : ℝ → ℝ` continuous and integrable with `|w(u)| ≤ C_w (1 + |u|)^{-3/2}`,

`∫_{-A}^{b} [w(-κσ) + |w(-κσ)| (E₁|σ| + E₂)] dσ ≤ κ⁻¹ ∫ w + (2C_w/κ)((κb)^{-1/2} + (κA)^{-1/2})
  + 2 E₁ C_w κ^{-3/2} (A^{1/2} + b^{1/2}) + (E₂/κ) ∫|w|`  (`window_core`),

the form used for the Airy window `w(σ) = Re W_D(-κσ)` with `A, b ≍ λ^{-1}`, `E₁ ≍ λ`, `E₂ ≍ c'^{-2/3}`: the
truncation of `∫ w` at `-κb`, `κA` costs the tails `(κb)^{-1/2}`, `(κA)^{-1/2}` (`tail_Ioi_le`, `tail_Iic_le`,
`setInt_Ioc_le`), the weight error costs `E₁ (A^{1/2} + b^{1/2})` (`int_g_le`) and the pointwise
`c'^{-2/3}` error costs `E₂ ‖w‖₁`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

lemma tail_Ioi_le {w : ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw) (hint : Integrable w)
    (hbd : ∀ u, |w u| ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ))) {U : ℝ} (hU : 0 < U) :
    ∫ u in Ioi U, |w u| ≤ 2 * Cw * U ^ (-(1 / 2 : ℝ)) := by
  have hI : IntegrableOn (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (Ioi U) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hU
  have h1 : ∫ u in Ioi U, |w u| ≤ ∫ u in Ioi U, Cw * u ^ (-(3 / 2 : ℝ)) := by
    refine setIntegral_mono_on hint.abs.integrableOn (hI.const_mul Cw) measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hU.trans hu
    refine (hbd u).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCw
    rw [abs_of_pos hu0]
    exact Real.rpow_le_rpow_of_nonpos hu0 (by linarith) (by norm_num)
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hU]
  norm_num
  ring

lemma tail_Iic_le {w : ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw) (hint : Integrable w)
    (hbd : ∀ u, |w u| ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ))) {U : ℝ} (hU : 0 < U) :
    ∫ u in Iic (-U), |w u| ≤ 2 * Cw * U ^ (-(1 / 2 : ℝ)) := by
  have h := tail_Ioi_le (w := fun u => w (-u)) hCw (hint.comp_neg)
    (fun u => by simpa using hbd (-u)) hU
  rw [← integral_comp_neg_Ioi U (fun y => |w y|)]
  exact h

lemma setInt_Ioc_le {w : ℝ → ℝ} (hint : Integrable w) {a b : ℝ} (hab : a ≤ b) :
    ∫ u in Ioc a b, w u ≤ (∫ u, w u) + (∫ u in Iic a, |w u|) + ∫ u in Ioi b, |w u| := by
  have h1 := integral_add_compl (measurableSet_Ioc (a := a) (b := b)) hint
  have hc : (Ioc a b)ᶜ = Iic a ∪ Ioi b := Set.compl_Ioc
  have h2 : |∫ u in (Ioc a b)ᶜ, w u| ≤ ∫ u in (Ioc a b)ᶜ, |w u| := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict (Ioc a b)ᶜ) w
  rw [hc] at h2
  have h3 : ∫ u in Iic a ∪ Ioi b, |w u| = (∫ u in Iic a, |w u|) + ∫ u in Ioi b, |w u| :=
    setIntegral_union (Set.Iic_disjoint_Ioi hab) measurableSet_Ioi hint.abs.integrableOn
      hint.abs.integrableOn
  rw [h3] at h2
  rw [hc] at h1
  have := (abs_le.1 h2).1
  linarith

lemma int_inv_sqrt_le {κ : ℝ} (hκ : 0 < κ) {A : ℝ} (hA : 0 ≤ A) :
    ∫ σ in (0 : ℝ)..A, (1 + κ * σ) ^ (-(1 / 2 : ℝ)) ≤ 2 * κ ^ (-(1 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_of_le hA]
  have hc : IntegrableOn (fun σ : ℝ => (1 + κ * σ) ^ (-(1 / 2 : ℝ))) (Ioc 0 A) := by
    have : ContinuousOn (fun σ : ℝ => (1 + κ * σ) ^ (-(1 / 2 : ℝ))) (Icc 0 A) := by
      apply ContinuousOn.rpow_const (by fun_prop)
      intro σ hσ; left; have := hσ.1; positivity
    exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hr : IntegrableOn (fun σ : ℝ => κ ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ))) (Ioc 0 A) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := A) (r := -(1 / 2 : ℝ))
      (by norm_num))
    exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le hA).1 this).const_mul _)
  have h1 : ∫ σ in Ioc 0 A, (1 + κ * σ) ^ (-(1 / 2 : ℝ)) ≤
      ∫ σ in Ioc 0 A, κ ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ)) := by
    refine setIntegral_mono_on hc hr measurableSet_Ioc fun σ hσ => ?_
    have hσ0 : 0 < σ := hσ.1
    rw [← Real.mul_rpow hκ.le hσ0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [mul_pos hκ hσ0]) (by norm_num)
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hA,
    integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

lemma int_sub_window {g : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ) (A b : ℝ) :
    ∫ σ in (-A)..b, g (-κ * σ) = κ⁻¹ * ∫ u in (-κ * b)..(κ * A), g u := by
  rw [intervalIntegral.integral_comp_mul_left (fun u => g u) (by linarith : (-κ) ≠ 0)]
  rw [show -κ * -A = κ * A by ring, intervalIntegral.integral_symm (-κ * b) (κ * A)]
  simp only [smul_eq_mul, inv_neg]
  ring

lemma int_g_le {κ : ℝ} (hκ : 0 < κ) {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    ∫ σ in (-A)..b, (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) ≤
      2 * κ ^ (-(1 / 2 : ℝ)) * (A ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) := by
  have hc : Continuous fun σ : ℝ => (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) := by
    apply Continuous.rpow_const (by fun_prop)
    intro σ; left; positivity
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ σ in (-A)..0, (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) =
      ∫ σ in (0 : ℝ)..A, (1 + κ * σ) ^ (-(1 / 2 : ℝ)) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := A)
      (fun σ : ℝ => (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)))
    simp only [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hA] at hσ
    simp only [abs_neg, abs_of_nonneg hσ.1]
  have h2 : ∫ σ in (0 : ℝ)..b, (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) =
      ∫ σ in (0 : ℝ)..b, (1 + κ * σ) ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hb] at hσ
    simp only [abs_of_nonneg hσ.1]
  rw [h1, h2]
  have := int_inv_sqrt_le hκ hA
  have := int_inv_sqrt_le hκ hb
  nlinarith

/-- The window core: for `w` continuous, integrable with `|w(u)| ≤ C_w (1 + |u|)^{-3/2}`, and `A, b > 0`,
`∫_{-A}^{b} [w(-κσ) + |w(-κσ)| (E₁|σ| + E₂)] dσ ≤ κ⁻¹ ∫ w + (2C_w/κ)((κb)^{-1/2} + (κA)^{-1/2})
  + 2 E₁ C_w κ^{-3/2} (A^{1/2} + b^{1/2}) + (E₂/κ) ∫|w|`. -/
theorem window_core {w : ℝ → ℝ} (hw : Continuous w) (hint : Integrable w) {Cw κ E1 E2 A b : ℝ}
    (hCw : 0 ≤ Cw) (hκ : 0 < κ) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hA : 0 < A) (hb : 0 < b)
    (hbd : ∀ u, |w u| ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ))) :
    ∫ σ in (-A)..b, (w (-κ * σ) + |w (-κ * σ)| * (E1 * |σ| + E2)) ≤
      κ⁻¹ * (∫ u, w u) + (2 * Cw / κ) * ((κ * b) ^ (-(1 / 2 : ℝ)) + (κ * A) ^ (-(1 / 2 : ℝ))) +
        2 * E1 * Cw * κ ^ (-(3 / 2 : ℝ)) * (A ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) +
        E2 / κ * ∫ u, |w u| := by
  have hwc : Continuous fun σ : ℝ => w (-κ * σ) := hw.comp (by fun_prop)
  have hwa : Continuous fun σ : ℝ => |w (-κ * σ)| := hwc.abs
  have hAb : -A ≤ b := by linarith
  -- pointwise bound of the error integrand
  have hpt : ∀ σ : ℝ, |w (-κ * σ)| * (E1 * |σ| + E2) ≤
      E1 * Cw * κ⁻¹ * (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) + E2 * |w (-κ * σ)| := by
    intro σ
    have hσ : 0 ≤ |σ| := abs_nonneg _
    have hb1 := hbd (-κ * σ)
    have habs : |(-κ * σ)| = κ * |σ| := by rw [abs_mul, abs_neg, abs_of_pos hκ]
    rw [habs] at hb1
    have hpos : 0 < 1 + κ * |σ| := by positivity
    have e1 : (1 + κ * |σ|) ^ (-(3 / 2 : ℝ)) * (κ * |σ|) ≤ (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) := by
      calc (1 + κ * |σ|) ^ (-(3 / 2 : ℝ)) * (κ * |σ|) ≤ (1 + κ * |σ|) ^ (-(3 / 2 : ℝ)) * (1 + κ * |σ|) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) := by
            rw [← Real.rpow_add_one hpos.ne']; norm_num
    have h3 : |w (-κ * σ)| * |σ| ≤ Cw * κ⁻¹ * (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) := by
      calc |w (-κ * σ)| * |σ| ≤ (Cw * (1 + κ * |σ|) ^ (-(3 / 2 : ℝ))) * |σ| :=
            mul_le_mul_of_nonneg_right hb1 hσ
        _ = Cw * κ⁻¹ * ((1 + κ * |σ|) ^ (-(3 / 2 : ℝ)) * (κ * |σ|)) := by field_simp
        _ ≤ Cw * κ⁻¹ * (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h3 hE1]
  -- integrate
  have hg : Continuous fun σ : ℝ => (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) := by
    apply Continuous.rpow_const (by fun_prop)
    intro σ; left; positivity
  have hsplit : ∫ σ in (-A)..b, (w (-κ * σ) +
        (E1 * Cw * κ⁻¹ * (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)) + E2 * |w (-κ * σ)|)) =
      (∫ σ in (-A)..b, w (-κ * σ)) +
        (E1 * Cw * κ⁻¹ * (∫ σ in (-A)..b, (1 + κ * |σ|) ^ (-(1 / 2 : ℝ))) +
          E2 * (∫ σ in (-A)..b, |w (-κ * σ)|)) := by
    have hi1 : IntervalIntegrable (fun σ : ℝ => E1 * Cw * κ⁻¹ * (1 + κ * |σ|) ^ (-(1 / 2 : ℝ)))
        volume (-A) b := (hg.const_mul _).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun σ : ℝ => E2 * |w (-κ * σ)|) volume (-A) b :=
      (hwa.const_mul _).intervalIntegrable _ _
    have hi0 : IntervalIntegrable (fun σ : ℝ => w (-κ * σ)) volume (-A) b :=
      hwc.intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi0 (hi1.add hi2), intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hmain : ∫ σ in (-A)..b, (w (-κ * σ) + |w (-κ * σ)| * (E1 * |σ| + E2)) ≤
      (∫ σ in (-A)..b, w (-κ * σ)) +
        (E1 * Cw * κ⁻¹ * (∫ σ in (-A)..b, (1 + κ * |σ|) ^ (-(1 / 2 : ℝ))) +
          E2 * (∫ σ in (-A)..b, |w (-κ * σ)|)) := by
    rw [← hsplit]
    refine intervalIntegral.integral_mono_on hAb
      ((hwc.add (hwa.mul (by fun_prop))).intervalIntegrable _ _)
      ((hwc.add ((hg.const_mul _).add (hwa.const_mul _))).intervalIntegrable _ _) fun σ _ => ?_
    have := hpt σ
    linarith
  -- the three terms
  have T1 : ∫ σ in (-A)..b, w (-κ * σ) ≤
      κ⁻¹ * (∫ u, w u) + (2 * Cw / κ) * ((κ * b) ^ (-(1 / 2 : ℝ)) + (κ * A) ^ (-(1 / 2 : ℝ))) := by
    rw [int_sub_window (g := w) hκ, intervalIntegral.integral_of_le (by nlinarith [mul_pos hκ hA, mul_pos hκ hb])]
    rw [show -κ * b = -(κ * b) by ring]
    have h1 := setInt_Ioc_le hint (a := -κ * b) (b := κ * A) (by nlinarith [mul_pos hκ hA, mul_pos hκ hb])
    have h2 := tail_Iic_le hCw hint hbd (U := κ * b) (by positivity)
    have h3 := tail_Ioi_le hCw hint hbd (U := κ * A) (by positivity)
    rw [show -κ * b = -(κ * b) by ring] at h1
    have h5 : κ⁻¹ * ∫ u in Ioc (-(κ * b)) (κ * A), w u ≤
        κ⁻¹ * ((∫ u, w u) + 2 * Cw * (κ * b) ^ (-(1 / 2 : ℝ)) + 2 * Cw * (κ * A) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine h5.trans (le_of_eq ?_)
    ring
  have T2 := int_g_le hκ hA.le hb.le
  have T3 : ∫ σ in (-A)..b, |w (-κ * σ)| ≤ κ⁻¹ * ∫ u, |w u| := by
    rw [int_sub_window (g := fun u => |w u|) hκ,
      intervalIntegral.integral_of_le (by nlinarith [mul_pos hκ hA, mul_pos hκ hb])]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_le_integral hint.abs (Eventually.of_forall fun u => abs_nonneg _)
  have hkpow : κ ^ (-(3 / 2 : ℝ)) = κ⁻¹ * κ ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hκ]; norm_num
  have hE1' : E1 * Cw * κ⁻¹ * (2 * κ ^ (-(1 / 2 : ℝ)) * (A ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ))) =
      2 * E1 * Cw * κ ^ (-(3 / 2 : ℝ)) * (A ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) := by
    rw [hkpow]; ring
  have h6 := mul_le_mul_of_nonneg_left T2 (by positivity : 0 ≤ E1 * Cw * κ⁻¹)
  have h4 := mul_le_mul_of_nonneg_left T3 hE2
  have h7 : E2 / κ * ∫ u, |w u| = E2 * (κ⁻¹ * ∫ u, |w u|) := by field_simp
  refine hmain.trans ?_
  have hsum := add_le_add T1 (add_le_add (h6.trans_eq hE1') (h4.trans_eq h7.symm))
  refine hsum.trans_eq ?_
  ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.window_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_core

end FormalResearch.ModularBootstrap.Upper.Ramped
