module

public import FormalResearch.ModularBootstrap.Crossing.MehlerOddClosure

/-!
# Proof of `MehlerOddMomentInput` and Unconditional Crossing Sum Rules

Proves `MehlerOddMomentInput w` (`mehlerOddMomentInput`) for all `w : ℕ`, discharging the sole
remaining hypothesis of `FormalResearch.ModularBootstrap.Crossing.SumRule`:
1. Exact Gaussian action of the Mehler kernel: `A_r` maps `exp(-2πβt)` to a scalar multiple of
   `exp(-2πβ't)` and maps `thermalDiff w β` to a scalar multiple of `thermalDiff w β'`.
2. `L²` Hilbert–Schmidt bound: `‖K_r(x, ·)‖_{L²} = (1 - r²)^{-w/2} exp(-π ((1-r)/(1+r)) ‖x‖²)`.
3. Combining with `exists_thermalDiff_approx_L2` yields `∫ A_r f dν = ∫ A_r f dρ` for every
   Fourier-odd radial `L¹` function `f = radialLiftReal w g`.
4. Unconditional corollaries (`_unconditional`) of `lemma_fwA_part1`–`3`, `lemma_fwX_one_sided`,
   `lemma_fwX_equality`, `theorem_fwC`, and `theorem_fwC_le_T_V`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace ENNReal

namespace FormalResearch.ModularBootstrap.Crossing

section MehlerGaussianAction

private lemma mehlerKernel_exp_quad_identity {w : ℕ} {r β : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 < β) (x y : RadialSpace w) :
    ((1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y) / (1 - r) +
        β * ‖y‖ ^ 2 =
      ((1 + r + β * (1 - r)) / (1 - r)) *
          ‖y - (2 * Real.sqrt r / (1 + r + β * (1 - r))) • x‖ ^ 2 +
        ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2 := by
  have h1r : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  have hden : 1 + r + β * (1 - r) ≠ 0 := by
    have : 0 < 1 + r + β * (1 - r) := by nlinarith [sub_pos.mpr hr1]
    exact this.ne'
  rw [norm_sub_sq_real, norm_smul,
    Real.norm_of_nonneg (div_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg r))
      (by nlinarith [sub_pos.mpr hr1])),
    inner_smul_right, real_inner_comm]
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hr0]
  field_simp [h1r, hden]
  ring

/-- Exact action of the Mehler operator `A_r` (`0 ≤ r < 1`) on radial Gaussians
`x ↦ exp(-π β ‖x‖²)` (`β > 0`). -/
lemma mehlerMean_exp_radial (w : ℕ) {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 < β)
    (x : RadialSpace w) :
    mehlerMean w r (radialLiftReal w (fun t => Real.exp (-2 * π * β * t))) x =
      (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
        radialLiftReal w (fun t => Real.exp (-2 * π *
          ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * t)) x := by
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have hden_pos : 0 < 1 + r + β * (1 - r) := by nlinarith
  have hc_pos : 0 < (1 + r + β * (1 - r)) / (1 - r) := div_pos hden_pos h1r_pos
  let x₀ : RadialSpace w := (2 * Real.sqrt r / (1 + r + β * (1 - r))) • x
  let β' : ℝ := (1 - r + β * (1 + r)) / (1 + r + β * (1 - r))
  let C₀ : ℝ := ((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * β' * ‖x‖ ^ 2)
  have heq : ∀ y : RadialSpace w,
      mehlerKernel w r x y * radialLiftReal w (fun t => Real.exp (-2 * π * β * t)) y =
        C₀ * Real.exp (-π * ((1 + r + β * (1 - r)) / (1 - r)) * ‖y - x₀‖ ^ 2) := fun y => by
    unfold mehlerKernel radialLiftReal
    dsimp only
    rw [mul_assoc (((1 - r) / 2) ^ (-(w : ℝ)))]
    rw [← Real.exp_add]
    have hexp_eq :
        -π * ((1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y) / (1 - r) +
          -2 * π * β * (‖y‖ ^ 2 / 2) =
        (-π * β' * ‖x‖ ^ 2) +
          (-π * ((1 + r + β * (1 - r)) / (1 - r)) * ‖y - x₀‖ ^ 2) := by
      have hid := congrArg (fun z => -π * z) (mehlerKernel_exp_quad_identity hr0 hr1 hβ x y)
      dsimp [β', x₀]
      calc -π * ((1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y) / (1 - r) +
            -2 * π * β * (‖y‖ ^ 2 / 2)
          = -π * (((1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y) / (1 - r) +
              β * ‖y‖ ^ 2) := by ring
        _ = -π * (((1 + r + β * (1 - r)) / (1 - r)) *
              ‖y - (2 * Real.sqrt r / (1 + r + β * (1 - r))) • x‖ ^ 2 +
            ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2) := hid
        _ = (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2) +
              (-π * ((1 + r + β * (1 - r)) / (1 - r)) *
                ‖y - (2 * Real.sqrt r / (1 + r + β * (1 - r))) • x‖ ^ 2) := by ring
    rw [hexp_eq, Real.exp_add]
    dsimp [C₀]; ring
  have hg := integral_exp_neg_pi_mul_norm_sq w hc_pos
  unfold mehlerMean
  simp_rw [heq]
  rw [integral_const_mul]
  change C₀ * ∫ y : RadialSpace w,
      (fun u : RadialSpace w => Real.exp (-π * ((1 + r + β * (1 - r)) / (1 - r)) * ‖u‖ ^ 2)) (y - x₀) = _
  rw [integral_sub_right_eq_self
    (fun u : RadialSpace w => Real.exp (-π * ((1 + r + β * (1 - r)) / (1 - r)) * ‖u‖ ^ 2)) x₀, hg.2]
  have hpow : ((1 - r) / 2) ^ (-(w : ℝ)) * ((1 + r + β * (1 - r)) / (1 - r)) ^ (-(w : ℝ)) =
      (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have hsimp : (1 - r) / 2 * ((1 + r + β * (1 - r)) / (1 - r)) =
        (2 / (1 + r + β * (1 - r)))⁻¹ := by
      field_simp [h1r_pos.ne']
    rw [hsimp, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  dsimp [C₀, radialLiftReal, β']
  have hexp_x : Real.exp (-2 * π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * (‖x‖ ^ 2 / 2)) =
      Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2) := by
    congr 1; ring
  rw [hexp_x]
  calc (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2)) *
        ((1 + r + β * (1 - r)) / (1 - r)) ^ (-(w : ℝ))
      = (((1 - r) / 2) ^ (-(w : ℝ)) * ((1 + r + β * (1 - r)) / (1 - r)) ^ (-(w : ℝ))) *
          Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2) := by ring
    _ = (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
          Real.exp (-π * ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r))) * ‖x‖ ^ 2) := by rw [hpow]

/-- Exact action of the Mehler operator `A_r` (`0 ≤ r < 1`) on thermal differences `thermalDiff w β`
(`β > 0`): `A_r` maps `thermalDiff w β` to a scalar multiple of `thermalDiff w β'` for
`β' = (1 - r + β(1 + r)) / (1 + r + β(1 - r)) > 0`. -/
lemma mehlerMean_thermalDiff (w : ℕ) {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hβ : 0 < β)
    (x : RadialSpace w) :
    mehlerMean w r (radialLiftReal w (thermalDiff w β)) x =
      (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
        radialLiftReal w (thermalDiff w ((1 - r + β * (1 + r)) / (1 + r + β * (1 - r)))) x := by
  have hk_int := (integral_mehlerKernel w hr0 hr1 x).1
  have h1_int : Integrable (fun y : RadialSpace w =>
      mehlerKernel w r x y * radialLiftReal w (fun t => Real.exp (-2 * π * β * t)) y) := by
    refine hk_int.mono'
      (((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)).mul
        (by unfold radialLiftReal; fun_prop)).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
    unfold radialLiftReal
    have hle : |Real.exp (-2 * π * β * (‖y‖ ^ 2 / 2))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      have hpos_arg : 0 ≤ 2 * π * β * (‖y‖ ^ 2 / 2) := by positivity
      exact Real.exp_le_one_iff.mpr (by linarith)
    exact mul_le_of_le_one_right (mehlerKernel_nonneg w hr1 x y) hle
  have h2_int : Integrable (fun y : RadialSpace w =>
      mehlerKernel w r x y *
        (β ^ (-(w : ℝ)) * radialLiftReal w (fun t => Real.exp (-2 * π * β⁻¹ * t)) y)) := by
    refine (hk_int.const_mul (β ^ (-(w : ℝ)))).mono'
      (((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)).mul
        (continuous_const.mul (by unfold radialLiftReal; fun_prop))).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y),
      abs_mul, abs_of_pos (Real.rpow_pos_of_pos hβ _)]
    unfold radialLiftReal
    have hle : |Real.exp (-2 * π * β⁻¹ * (‖y‖ ^ 2 / 2))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      have hpos_arg : 0 ≤ 2 * π * β⁻¹ * (‖y‖ ^ 2 / 2) := by positivity
      exact Real.exp_le_one_iff.mpr (by linarith)
    calc mehlerKernel w r x y * (β ^ (-(w : ℝ)) * |Real.exp (-2 * π * β⁻¹ * (‖y‖ ^ 2 / 2))|)
        ≤ mehlerKernel w r x y * (β ^ (-(w : ℝ)) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos hβ _).le)
            (mehlerKernel_nonneg w hr1 x y)
      _ = β ^ (-(w : ℝ)) * mehlerKernel w r x y := by ring
  have hsplit : (fun y : RadialSpace w =>
      mehlerKernel w r x y * radialLiftReal w (thermalDiff w β) y) =
      fun y => mehlerKernel w r x y * radialLiftReal w (fun t => Real.exp (-2 * π * β * t)) y -
        mehlerKernel w r x y *
          (β ^ (-(w : ℝ)) * radialLiftReal w (fun t => Real.exp (-2 * π * β⁻¹ * t)) y) := by
    ext y
    simp only [radialLiftReal, thermalDiff, div_eq_mul_inv]
    rw [mul_sub, mul_assoc]
    congr 4; ring
  have h2_const : (fun y : RadialSpace w =>
      mehlerKernel w r x y *
        (β ^ (-(w : ℝ)) * radialLiftReal w (fun t => Real.exp (-2 * π * β⁻¹ * t)) y)) =
      fun y => β ^ (-(w : ℝ)) *
        (mehlerKernel w r x y * radialLiftReal w (fun t => Real.exp (-2 * π * β⁻¹ * t)) y) := by
    ext y; ring
  unfold mehlerMean
  rw [hsplit, integral_sub h1_int h2_int, h2_const, integral_const_mul]
  change mehlerMean w r (radialLiftReal w (fun t => Real.exp (-2 * π * β * t))) x -
      β ^ (-(w : ℝ)) *
        mehlerMean w r (radialLiftReal w (fun t => Real.exp (-2 * π * β⁻¹ * t))) x = _
  rw [mehlerMean_exp_radial w hr0 hr1 hβ x, mehlerMean_exp_radial w hr0 hr1 (inv_pos.mpr hβ) x]
  have h1r_nn : 0 ≤ 1 - r := (sub_pos.mpr hr1).le
  have hden1_pos : 0 < 1 + r + β * (1 - r) := by nlinarith
  have hden2_pos : 0 < 1 + r + β⁻¹ * (1 - r) := by nlinarith [inv_pos.mpr hβ]
  have hnum1_pos : 0 < 1 - r + β * (1 + r) := by nlinarith
  let β' : ℝ := (1 - r + β * (1 + r)) / (1 + r + β * (1 - r))
  have hβ'_pos : 0 < β' := div_pos hnum1_pos hden1_pos
  have hpref : β ^ (-(w : ℝ)) * (2 / (1 + r + β⁻¹ * (1 - r))) ^ (w : ℝ) =
      (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) * β' ^ (-(w : ℝ)) := by
    rw [Real.rpow_neg hβ.le, Real.rpow_neg hβ'_pos.le,
      ← Real.inv_rpow hβ.le, ← Real.inv_rpow hβ'_pos.le,
      ← Real.mul_rpow (inv_nonneg.mpr hβ.le) (by positivity),
      ← Real.mul_rpow (by positivity) (inv_nonneg.mpr hβ'_pos.le)]
    congr 1
    dsimp [β']
    field_simp [hβ.ne', hden1_pos.ne', hnum1_pos.ne']
    ring
  have hexp_inv : (1 - r + β⁻¹ * (1 + r)) / (1 + r + β⁻¹ * (1 - r)) = β'⁻¹ := by
    dsimp [β']
    field_simp [hβ.ne', hden1_pos.ne', hnum1_pos.ne']
    ring
  calc (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
        radialLiftReal w (fun t => Real.exp (-2 * π * β' * t)) x -
      β ^ (-(w : ℝ)) * ((2 / (1 + r + β⁻¹ * (1 - r))) ^ (w : ℝ) *
        radialLiftReal w (fun t => Real.exp (-2 * π * ((1 - r + β⁻¹ * (1 + r)) /
          (1 + r + β⁻¹ * (1 - r))) * t)) x)
      = (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
          radialLiftReal w (fun t => Real.exp (-2 * π * β' * t)) x -
        (β ^ (-(w : ℝ)) * (2 / (1 + r + β⁻¹ * (1 - r))) ^ (w : ℝ)) *
          radialLiftReal w (fun t => Real.exp (-2 * π * ((1 - r + β⁻¹ * (1 + r)) /
            (1 + r + β⁻¹ * (1 - r))) * t)) x := by ring
    _ = (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
          radialLiftReal w (fun t => Real.exp (-2 * π * β' * t)) x -
        ((2 / (1 + r + β * (1 - r))) ^ (w : ℝ) * β' ^ (-(w : ℝ))) *
          radialLiftReal w (fun t => Real.exp (-2 * π * β'⁻¹ * t)) x := by rw [hpref, hexp_inv]
    _ = (2 / (1 + r + β * (1 - r))) ^ (w : ℝ) *
          radialLiftReal w (thermalDiff w β') x := by
        simp only [radialLiftReal, thermalDiff, div_eq_mul_inv]
        rw [mul_sub, mul_assoc]
        ring_nf

end MehlerGaussianAction

section MehlerL2Bound

/-- Exact `L²` norm squared of the Mehler kernel `y ↦ K_r(x, y)`:
`∫ y, K_r(x, y)² dy = ((1 - r²) / 2)^{-w} exp(-2π ((1-r)/(1+r)) ‖x‖²)`. -/
lemma integral_mehlerKernel_sq (w : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : RadialSpace w) :
    Integrable (fun y => mehlerKernel w r x y ^ 2) ∧
      ∫ y : RadialSpace w, mehlerKernel w r x y ^ 2 =
        ((1 - r ^ 2) / 2) ^ (-(w : ℝ)) * Real.exp (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1pr_pos : 0 < 1 + r := by linarith
  have hc_pos : 0 < 2 * (1 + r) / (1 - r) := div_pos (by linarith) h1r_pos
  let x₀ : RadialSpace w := (2 * Real.sqrt r / (1 + r)) • x
  let C₀ : ℝ := ((1 - r) / 2) ^ (-(2 * (w : ℝ))) *
    Real.exp (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)
  have heq : ∀ y : RadialSpace w, mehlerKernel w r x y ^ 2 =
      C₀ * Real.exp (-π * (2 * (1 + r) / (1 - r)) * ‖y - x₀‖ ^ 2) := fun y => by
    unfold mehlerKernel
    rw [mehlerKernel_shift_identity hr0 hr1 x y, mul_pow, ← Real.exp_nat_mul]
    have hrp : (((1 - r) / 2) ^ (-(w : ℝ))) ^ 2 = ((1 - r) / 2) ^ (-(2 * (w : ℝ))) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    have hexp_eq : (2 : ℕ) * (-π * ((1 + r) * ‖y - x₀‖ ^ 2 + (1 - r) ^ 2 / (1 + r) * ‖x‖ ^ 2) /
          (1 - r)) =
        (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) +
          (-π * (2 * (1 + r) / (1 - r)) * ‖y - x₀‖ ^ 2) := by
      push_cast
      field_simp [h1r_pos.ne', h1pr_pos.ne']
      ring
    rw [hrp, hexp_eq, Real.exp_add]
    dsimp [C₀]; ring
  have hg := integral_exp_neg_pi_mul_norm_sq w hc_pos
  have hint : Integrable (fun y : RadialSpace w => mehlerKernel w r x y ^ 2) := by
    simp_rw [heq]
    exact (hg.1.comp_sub_right x₀).const_mul C₀
  refine ⟨hint, ?_⟩
  simp_rw [heq]
  rw [integral_const_mul]
  change C₀ * ∫ y : RadialSpace w,
      (fun u : RadialSpace w => Real.exp (-π * (2 * (1 + r) / (1 - r)) * ‖u‖ ^ 2)) (y - x₀) = _
  rw [integral_sub_right_eq_self
    (fun u : RadialSpace w => Real.exp (-π * (2 * (1 + r) / (1 - r)) * ‖u‖ ^ 2)) x₀, hg.2]
  have h1r2_pos : 0 < (1 - r ^ 2) / 2 := by nlinarith
  have hpow : ((1 - r) / 2) ^ (-(2 * (w : ℝ))) * (2 * (1 + r) / (1 - r)) ^ (-(w : ℝ)) =
      ((1 - r ^ 2) / 2) ^ (-(w : ℝ)) := by
    have hsplit : ((1 - r) / 2) ^ (-(2 * (w : ℝ))) =
        (((1 - r) / 2) ^ 2) ^ (-(w : ℝ)) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    rw [hsplit, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp [h1r_pos.ne']
    ring
  dsimp [C₀]
  calc (((1 - r) / 2) ^ (-(2 * (w : ℝ))) * Real.exp (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)) *
        (2 * (1 + r) / (1 - r)) ^ (-(w : ℝ))
      = (((1 - r) / 2) ^ (-(2 * (w : ℝ))) * (2 * (1 + r) / (1 - r)) ^ (-(w : ℝ))) *
          Real.exp (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by ring
    _ = ((1 - r ^ 2) / 2) ^ (-(w : ℝ)) * Real.exp (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
        rw [hpow]

/-- Cauchy–Schwarz bound for `mehlerMean w r`: if `∫ (h - f)² ≤ δ²`, then
`|mehlerMean w r h x - mehlerMean w r f x| ≤ ((1 - r²)/2)^{-w/2} exp(-π ((1-r)/(1+r)) ‖x‖²) δ`. -/
lemma abs_mehlerMean_sub_le_of_L2 {w : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h f : RadialSpace w → ℝ} (hh_cont : Continuous h) (hf_cont : Continuous f)
    {Bh Bf : ℝ} (hh_bd : ∀ y, |h y| ≤ Bh) (hf_bd : ∀ y, |f y| ≤ Bf)
    {δ : ℝ} (hδ : 0 ≤ δ) (hL2_int : Integrable (fun y => (h y - f y) ^ 2))
    (hL2_le : ∫ y : RadialSpace w, (h y - f y) ^ 2 ≤ δ ^ 2) (x : RadialSpace w) :
    |mehlerMean w r h x - mehlerMean w r f x| ≤
      ((1 - r ^ 2) / 2) ^ (-(w : ℝ) / 2) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) * δ := by
  have hk_int := (integral_mehlerKernel w hr0 hr1 x).1
  have hBh_nn : 0 ≤ Bh := (abs_nonneg _).trans (hh_bd 0)
  have hBf_nn : 0 ≤ Bf := (abs_nonneg _).trans (hf_bd 0)
  have hkh_int : Integrable (fun y => mehlerKernel w r x y * h y) :=
    (hk_int.const_mul Bh).mono'
      (((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)).mul
        hh_cont).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm Bh]
        exact mul_le_mul_of_nonneg_left (hh_bd y) (mehlerKernel_nonneg w hr1 x y))
  have hkf_int : Integrable (fun y => mehlerKernel w r x y * f y) :=
    (hk_int.const_mul Bf).mono'
      (((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)).mul
        hf_cont).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm Bf]
        exact mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y))
  have hdiff_eq : mehlerMean w r h x - mehlerMean w r f x =
      ∫ y : RadialSpace w, mehlerKernel w r x y * (h y - f y) := by
    unfold mehlerMean
    rw [← integral_sub hkh_int hkf_int]
    refine integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [hdiff_eq]
  have hksq := integral_mehlerKernel_sq w hr0 hr1 x
  have hmem_k : MemLp (mehlerKernel w r x) 2 volume := by
    refine memLp_two_iff_integrable_sq_norm
      ((continuous_mehlerKernel w r).comp
        (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable |>.mpr ?_
    simpa [Real.norm_eq_abs, sq_abs] using hksq.1
  have hmem_d : MemLp (fun y => h y - f y) 2 volume := by
    refine memLp_two_iff_integrable_sq_norm (hh_cont.sub hf_cont).aestronglyMeasurable |>.mpr ?_
    simpa [Real.norm_eq_abs, sq_abs] using hL2_int
  let kLp : Lp ℝ 2 (volume : Measure (RadialSpace w)) := hmem_k.toLp (mehlerKernel w r x)
  let dLp : Lp ℝ 2 (volume : Measure (RadialSpace w)) := hmem_d.toLp (fun y => h y - f y)
  have hinner_eq : ∫ y : RadialSpace w, mehlerKernel w r x y * (h y - f y) =
      @inner ℝ _ _ kLp dLp := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem_k.coeFn_toLp, hmem_d.coeFn_toLp] with y hyk hyd
    rw [hyk, hyd, real_inner_eq_re_inner, mul_comm]
    rfl
  have hk_norm_sq : ‖kLp‖ ^ 2 =
      ((1 - r ^ 2) / 2) ^ (-(w : ℝ)) * Real.exp (-2 * π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
    have hin : ‖kLp‖ ^ 2 = @inner ℝ _ _ kLp kLp := (real_inner_self_eq_norm_sq kLp).symm
    rw [hin, L2.inner_def]
    have heq : (fun y => @inner ℝ _ _ (kLp y) (kLp y)) =ᵐ[volume]
        fun y => mehlerKernel w r x y ^ 2 := by
      filter_upwards [hmem_k.coeFn_toLp] with y hy
      rw [hy, RCLike.inner_apply, conj_trivial, sq]
    rw [integral_congr_ae heq, hksq.2]
  have hd_norm_sq : ‖dLp‖ ^ 2 ≤ δ ^ 2 := by
    have hin : ‖dLp‖ ^ 2 = @inner ℝ _ _ dLp dLp := (real_inner_self_eq_norm_sq dLp).symm
    rw [hin, L2.inner_def]
    have heq : (fun y => @inner ℝ _ _ (dLp y) (dLp y)) =ᵐ[volume]
        fun y => (h y - f y) ^ 2 := by
      filter_upwards [hmem_d.coeFn_toLp] with y hy
      rw [hy, RCLike.inner_apply, conj_trivial, sq]
    rw [integral_congr_ae heq]
    exact hL2_le
  have hk_norm : ‖kLp‖ =
      ((1 - r ^ 2) / 2) ^ (-(w : ℝ) / 2) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
    have h1r2_pos : 0 < (1 - r ^ 2) / 2 := by nlinarith
    have hrhs_nn : 0 ≤ ((1 - r ^ 2) / 2) ^ (-(w : ℝ) / 2) *
        Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by positivity
    rw [← Real.sqrt_sq (norm_nonneg kLp), hk_norm_sq,
      ← Real.sqrt_sq hrhs_nn]
    congr 1
    rw [mul_pow, ← Real.rpow_natCast (((1 - r ^ 2) / 2) ^ (-(w : ℝ) / 2)) 2,
      ← Real.rpow_mul h1r2_pos.le, ← Real.exp_nat_mul]
    congr 2 <;> ring
  have hd_norm : ‖dLp‖ ≤ δ := by
    rw [← Real.sqrt_sq (norm_nonneg dLp), ← Real.sqrt_sq hδ]
    exact Real.sqrt_le_sqrt hd_norm_sq
  have hcs : |@inner ℝ _ _ kLp dLp| ≤ ‖kLp‖ * ‖dLp‖ := abs_real_inner_le_norm kLp dLp
  rw [hinner_eq]
  calc |@inner ℝ _ _ kLp dLp| ≤ ‖kLp‖ * ‖dLp‖ := hcs
    _ ≤ ‖kLp‖ * δ := mul_le_mul_of_nonneg_left hd_norm (norm_nonneg _)
    _ = ((1 - r ^ 2) / 2) ^ (-(w : ℝ) / 2) *
          Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) * δ := by
        rw [hk_norm]

end MehlerL2Bound

section MainTheorem

private lemma abs_radialLiftReal_thermalDiff_le {w : ℕ} {β : ℝ} (hβ : 0 < β)
    (y : RadialSpace w) :
    |radialLiftReal w (thermalDiff w β) y| ≤ 1 + β ^ (-(w : ℝ)) := by
  unfold radialLiftReal thermalDiff
  have h1 : |Real.exp (-2 * π * β * (‖y‖ ^ 2 / 2))| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    have hpos_arg : 0 ≤ 2 * π * β * (‖y‖ ^ 2 / 2) := by positivity
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h2 : |β ^ (-(w : ℝ)) * Real.exp (-2 * π * (‖y‖ ^ 2 / 2) / β)| ≤ β ^ (-(w : ℝ)) := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hβ _), abs_of_pos (Real.exp_pos _)]
    have hpos_arg : 0 ≤ 2 * π * (‖y‖ ^ 2 / 2) := by positivity
    exact mul_le_of_le_one_right (Real.rpow_pos_of_pos hβ _).le
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hβ.le))
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- Proof of `MehlerOddMomentInput w` for all `w : ℕ`: thermal crossing equality for positive
measures integrating `exp(-ε‖x‖²)` implies `∫ A_r f dν = ∫ A_r f dρ` for every `0 < r < 1` and
every continuous radial `L¹` Fourier-odd test `f = radialLiftReal w g`. -/
theorem mehlerOddMomentInput (w : ℕ) : MehlerOddMomentInput w := by
  intro ν ρ _ _ hν_gauss hρ_gauss h_thermal g hg_cont hg_int hg_odd r hr
  obtain ⟨hf_cont, hf_bd⟩ := radialLift_bounded_continuous_of_fourier_odd hg_int hg_odd
  let B_f : ℝ := ∫ y : RadialSpace w, ‖radialLift w g y‖
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r < 1 := hr.2
  have hf_int_ν : Integrable (fun x => mehlerMean w r (radialLiftReal w g) x) ν :=
    integrable_mehlerMean_of_bounded hν_gauss hf_cont hf_bd hr0 hr1
  have hf_int_ρ : Integrable (fun x => mehlerMean w r (radialLiftReal w g) x) ρ :=
    integrable_mehlerMean_of_bounded hρ_gauss hf_cont hf_bd hr0 hr1
  let ε_r : ℝ := π * ((1 - r) / (1 + r))
  have hε_r : 0 < ε_r := mul_pos Real.pi_pos (div_pos (sub_pos.mpr hr1) (by linarith))
  let C_r : ℝ := ((1 - r ^ 2) / 2) ^ (-(w : ℝ) / 2)
  have hC_r_nn : 0 ≤ C_r := Real.rpow_nonneg (by nlinarith) _
  let M_ν : ℝ := ∫ x : RadialSpace w, Real.exp (-ε_r * ‖x‖ ^ 2) ∂ν
  let M_ρ : ℝ := ∫ x : RadialSpace w, Real.exp (-ε_r * ‖x‖ ^ 2) ∂ρ
  have hM_ν_nn : 0 ≤ M_ν := integral_nonneg fun _ => (Real.exp_pos _).le
  have hM_ρ_nn : 0 ≤ M_ρ := integral_nonneg fun _ => (Real.exp_pos _).le
  have hdiff_le : ∀ δ : ℝ, 0 < δ →
      |(∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν) -
        (∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)| ≤
        C_r * (M_ν + M_ρ) * δ := by
    intro δ hδ
    obtain ⟨N, c, β, hβ_pos, hL2_int, hL2_le⟩ :=
      exists_thermalDiff_approx_L2 w hg_cont hg_int hg_odd hδ
    let h : RadialSpace w → ℝ := fun x =>
      ∑ i : Fin N, c i * radialLiftReal w (thermalDiff w (β i)) x
    have hh_cont : Continuous h := by
      dsimp [h]; unfold radialLiftReal thermalDiff; fun_prop
    let Bh : ℝ := ∑ i : Fin N, |c i| * (1 + β i ^ (-(w : ℝ)))
    have hh_bd : ∀ y : RadialSpace w, |h y| ≤ Bh := fun y => by
      dsimp [h, Bh]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_radialLiftReal_thermalDiff_le (hβ_pos i) y) (abs_nonneg _)
    have hh_int_ν : Integrable (fun x => mehlerMean w r h x) ν :=
      integrable_mehlerMean_of_bounded hν_gauss hh_cont hh_bd hr0 hr1
    have hh_int_ρ : Integrable (fun x => mehlerMean w r h x) ρ :=
      integrable_mehlerMean_of_bounded hρ_gauss hh_cont hh_bd hr0 hr1
    have hAr_h_eq : ∀ x : RadialSpace w,
        mehlerMean w r h x = ∑ i : Fin N,
          c i * (2 / (1 + r + β i * (1 - r))) ^ (w : ℝ) *
            radialLiftReal w (thermalDiff w
              ((1 - r + β i * (1 + r)) / (1 + r + β i * (1 - r)))) x := by
      intro x
      have hk_int := (integral_mehlerKernel w hr0 hr1 x).1
      have hterm_int : ∀ i : Fin N, Integrable (fun y =>
          mehlerKernel w r x y * (c i * radialLiftReal w (thermalDiff w (β i)) y)) := by
        intro i
        refine (hk_int.const_mul (|c i| * (1 + β i ^ (-(w : ℝ))))).mono'
          (((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)).mul
            (continuous_const.mul (by unfold radialLiftReal thermalDiff; fun_prop))).aestronglyMeasurable ?_
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), abs_mul]
        rw [mul_comm (|c i| * (1 + β i ^ (-(w : ℝ))))]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (abs_radialLiftReal_thermalDiff_le (hβ_pos i) y) (abs_nonneg _))
          (mehlerKernel_nonneg w hr1 x y)
      unfold mehlerMean
      have heq_sum : (fun y : RadialSpace w => mehlerKernel w r x y * h y) =
          fun y => ∑ i : Fin N, mehlerKernel w r x y *
            (c i * radialLiftReal w (thermalDiff w (β i)) y) := by
        ext y; dsimp [h]; rw [Finset.mul_sum]
      rw [heq_sum, integral_finsetSum _ fun i _ => hterm_int i]
      refine Finset.sum_congr rfl fun i _ => ?_
      have heq_mul : (fun y : RadialSpace w =>
          mehlerKernel w r x y * (c i * radialLiftReal w (thermalDiff w (β i)) y)) =
          fun y => c i * (mehlerKernel w r x y * radialLiftReal w (thermalDiff w (β i)) y) := by
        ext y; ring
      rw [heq_mul, integral_const_mul]
      change c i * mehlerMean w r (radialLiftReal w (thermalDiff w (β i))) x = _
      rw [mehlerMean_thermalDiff w hr0 hr1 (hβ_pos i) x, mul_assoc]
    have htherm_int : ∀ (μ : Measure (RadialSpace w)),
        (∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) μ) →
        ∀ {β₀ : ℝ}, 0 < β₀ →
          Integrable (fun x : RadialSpace w => radialLiftReal w (thermalDiff w β₀) x) μ := by
      intro μ hμ_gauss β₀ hβ₀
      have h1 : Integrable (fun x : RadialSpace w => Real.exp (-(π * β₀) * ‖x‖ ^ 2)) μ :=
        hμ_gauss (mul_pos Real.pi_pos hβ₀)
      have h2 : Integrable (fun x : RadialSpace w =>
          β₀ ^ (-(w : ℝ)) * Real.exp (-(π / β₀) * ‖x‖ ^ 2)) μ :=
        (hμ_gauss (div_pos Real.pi_pos hβ₀)).const_mul _
      refine (h1.sub h2).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.sub_apply, radialLiftReal, thermalDiff]
      congr 1
      · congr 1; ring
      · congr 2; ring
    have h_eq_h : ∫ x : RadialSpace w, mehlerMean w r h x ∂ν =
        ∫ x : RadialSpace w, mehlerMean w r h x ∂ρ := by
      simp_rw [hAr_h_eq]
      have hterm_ν : ∀ i : Fin N, Integrable (fun x : RadialSpace w =>
          c i * (2 / (1 + r + β i * (1 - r))) ^ (w : ℝ) *
            radialLiftReal w (thermalDiff w
              ((1 - r + β i * (1 + r)) / (1 + r + β i * (1 - r)))) x) ν := fun i => by
        have hβ'_pos : 0 < (1 - r + β i * (1 + r)) / (1 + r + β i * (1 - r)) :=
          div_pos (by nlinarith [hβ_pos i]) (by nlinarith [hβ_pos i])
        exact (htherm_int ν hν_gauss hβ'_pos).const_mul _
      have hterm_ρ : ∀ i : Fin N, Integrable (fun x : RadialSpace w =>
          c i * (2 / (1 + r + β i * (1 - r))) ^ (w : ℝ) *
            radialLiftReal w (thermalDiff w
              ((1 - r + β i * (1 + r)) / (1 + r + β i * (1 - r)))) x) ρ := fun i => by
        have hβ'_pos : 0 < (1 - r + β i * (1 + r)) / (1 + r + β i * (1 - r)) :=
          div_pos (by nlinarith [hβ_pos i]) (by nlinarith [hβ_pos i])
        exact (htherm_int ρ hρ_gauss hβ'_pos).const_mul _
      rw [integral_finsetSum _ fun i _ => hterm_ν i,
        integral_finsetSum _ fun i _ => hterm_ρ i]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hβ'_pos : 0 < (1 - r + β i * (1 + r)) / (1 + r + β i * (1 - r)) :=
        div_pos (by nlinarith [hβ_pos i]) (by nlinarith [hβ_pos i])
      rw [integral_const_mul, integral_const_mul, h_thermal hβ'_pos]
    have hpt_bound : ∀ x : RadialSpace w,
        ‖mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x‖ ≤
          (C_r * δ) * Real.exp (-ε_r * ‖x‖ ^ 2) := fun x => by
      rw [Real.norm_eq_abs, abs_sub_comm]
      have hcs := abs_mehlerMean_sub_le_of_L2 hr0 hr1 hh_cont hf_cont hh_bd hf_bd hδ.le
        hL2_int hL2_le x
      dsimp [C_r, ε_r]
      have hexp : Real.exp (-(π * ((1 - r) / (1 + r))) * ‖x‖ ^ 2) =
          Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
        congr 1; ring
      rw [hexp]
      exact hcs.trans_eq (by ring)
    have hν_err : |∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν -
        ∫ x : RadialSpace w, mehlerMean w r h x ∂ν| ≤ C_r * M_ν * δ := by
      rw [← integral_sub hf_int_ν hh_int_ν]
      calc |∫ x : RadialSpace w, (mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x) ∂ν|
          = ‖∫ x : RadialSpace w, (mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x) ∂ν‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ x : RadialSpace w, ‖mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x‖ ∂ν :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x : RadialSpace w, (C_r * δ) * Real.exp (-ε_r * ‖x‖ ^ 2) ∂ν :=
            integral_mono (hf_int_ν.sub hh_int_ν).norm ((hν_gauss hε_r).const_mul (C_r * δ))
              hpt_bound
        _ = C_r * M_ν * δ := by
            rw [integral_const_mul]; dsimp [M_ν]; ring
    have hρ_err : |∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ -
        ∫ x : RadialSpace w, mehlerMean w r h x ∂ρ| ≤ C_r * M_ρ * δ := by
      rw [← integral_sub hf_int_ρ hh_int_ρ]
      calc |∫ x : RadialSpace w, (mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x) ∂ρ|
          = ‖∫ x : RadialSpace w, (mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x) ∂ρ‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ x : RadialSpace w, ‖mehlerMean w r (radialLiftReal w g) x - mehlerMean w r h x‖ ∂ρ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x : RadialSpace w, (C_r * δ) * Real.exp (-ε_r * ‖x‖ ^ 2) ∂ρ :=
            integral_mono (hf_int_ρ.sub hh_int_ρ).norm ((hρ_gauss hε_r).const_mul (C_r * δ))
              hpt_bound
        _ = C_r * M_ρ * δ := by
            rw [integral_const_mul]; dsimp [M_ρ]; ring
    have htri : |(∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν) -
          (∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)| ≤
        |∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν -
          ∫ x : RadialSpace w, mehlerMean w r h x ∂ν| +
        |∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ -
          ∫ x : RadialSpace w, mehlerMean w r h x ∂ρ| := by
      rw [h_eq_h]
      have h1 := abs_sub_le
        (∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν)
        (∫ x : RadialSpace w, mehlerMean w r h x ∂ρ)
        (∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)
      rwa [abs_sub_comm (∫ x : RadialSpace w, mehlerMean w r h x ∂ρ)] at h1
    linarith
  by_contra hne
  have hpos : 0 < |(∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν) -
      (∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)| :=
    abs_sub_pos.mpr hne
  let D := |(∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν) -
    (∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)|
  let δ := D / (2 * (C_r * (M_ν + M_ρ) + 1))
  have hδ : 0 < δ := div_pos hpos (by positivity)
  have hle := hdiff_le δ hδ
  have hlt : C_r * (M_ν + M_ρ) * δ < D := by
    dsimp [δ, D]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_irrefl _ (lt_of_le_of_lt hle hlt)

end MainTheorem

section UnconditionalCorollaries

/-- Unconditional Lemma FW-A (1) (`crossing_sum_rule.tex`, `fw:abel`). -/
theorem lemma_fwA_part1_unconditional {w : ℕ}
    (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ]
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    (hρ_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ)
    (h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun x => mehlerMean w r (radialLiftReal w g) x) ν ∧
      Integrable (fun x => mehlerMean w r (radialLiftReal w g) x) ρ ∧
      ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν =
        ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ :=
  lemma_fwA_part1 (mehlerOddMomentInput w) ν ρ hν_gauss hρ_gauss h_thermal hg_cont hg_int hg_odd hr

/-- Unconditional Lemma FW-A (2) (`crossing_sum_rule.tex`, `fw:abel`). -/
theorem lemma_fwA_part2_unconditional {w : ℕ}
    (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ]
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    (hρ_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ)
    (h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g))
    (hf_rho : Integrable (radialLiftReal w g) ρ)
    {R : ℝ} (hR : 0 ≤ R) (hneg_supp : ∀ y : RadialSpace w, R < ‖y‖ → max (-radialLiftReal w g y) 0 = 0)
    (htend_rho : Tendsto (fun r => ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace w, radialLiftReal w g x ∂ρ))) :
    Integrable (radialLiftReal w g) ν ∧
      ∫ x : RadialSpace w, radialLiftReal w g x ∂ν ≤
        ∫ x : RadialSpace w, radialLiftReal w g x ∂ρ :=
  lemma_fwA_part2 (mehlerOddMomentInput w) ν ρ hν_gauss hρ_gauss h_thermal hg_cont hg_int hg_odd
    hf_rho hR hneg_supp htend_rho

/-- Unconditional Lemma FW-A (3) (`crossing_sum_rule.tex`, `fw:abel`). -/
theorem lemma_fwA_part3_unconditional {w : ℕ}
    (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ]
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    (hρ_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ)
    (h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g))
    {C b d : ℝ} (hC : 0 ≤ C) (hb : ∀ x : RadialSpace w, |radialLiftReal w g x| ≤ C * euclideanWeight b d x)
    (hWν : Integrable (euclideanWeight b d) ν) (hWρ : Integrable (euclideanWeight b d) ρ) :
    Integrable (radialLiftReal w g) ν ∧
      Integrable (radialLiftReal w g) ρ ∧
      ∫ x : RadialSpace w, radialLiftReal w g x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w g x ∂ρ :=
  lemma_fwA_part3 (mehlerOddMomentInput w) ν ρ hν_gauss hρ_gauss h_thermal hg_cont hg_int hg_odd
    hC hb hWν hWρ

/-- Unconditional Lemma FW-X (1) (`crossing_sum_rule.tex`, `fw:crossing`): one-sided crossing inequality. -/
theorem lemma_fwX_one_sided_unconditional (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a)
    (meas : AdmissibleCrossingMeasure prob a)
    {g : ℝ → ℝ} (hg : TestClass prob a g) {T : ℝ} (hT_nn : ∀ t, T ≤ t → 0 ≤ g t) :
    IntegrableOn g (Ici 0) meas.ν ∧
      prob.gVac a g + ∫ t in Ici 0, g t ∂meas.ν ≤ 0 :=
  lemma_fwX_one_sided prob (mehlerOddMomentInput prob.w) ha ha_pos meas hg hT_nn

/-- Unconditional Lemma FW-X (2) (`crossing_sum_rule.tex`, `fw:crossing`): exact crossing equality. -/
theorem lemma_fwX_equality_unconditional (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a)
    (meas : AdmissibleCrossingMeasure prob a)
    {g : ℝ → ℝ} (hg : TestClass prob a g) {q C_g : ℝ}
    (hq : (prob.w + 1 : ℝ) / 2 < q) (hC_g : 0 ≤ C_g)
    (hdecay : ∀ t, 0 ≤ t → |g t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) :
    IntegrableOn g (Ici 0) meas.ν ∧
      prob.gVac a g + ∫ t in Ici 0, g t ∂meas.ν = 0 :=
  lemma_fwX_equality prob (mehlerOddMomentInput prob.w) ha ha_pos meas hg hq hC_g hdecay

/-- Unconditional Theorem FW-C (`crossing_sum_rule.tex`, `fw:FWC`): crossing certification. -/
theorem theorem_fwC_unconditional (prob : FixedWeightProblem)
    {a T : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) (hT : 0 < T)
    {g : ℝ → ℝ} (hg : prob.IsFeasible a T g) (spec : AdmissibleSpectrum prob a) :
    ∃ n : spec.ι, spec.t n < T :=
  theorem_fwC prob (mehlerOddMomentInput prob.w) ha ha_pos hT hg spec

/-- Unconditional spectral gap bound via `T_V`. -/
theorem theorem_fwC_le_T_V_unconditional (prob : FixedWeightProblem)
    {cTilde T_gap : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) (hc_pos : 0 < cTilde)
    (spec : AdmissibleSpectrum prob (cTilde / 12)) (hgap : ∀ n : spec.ι, T_gap ≤ spec.t n) :
    T_gap ≤ prob.T_V cTilde :=
  theorem_fwC_le_T_V prob (mehlerOddMomentInput prob.w) hc hc_pos spec hgap

end UnconditionalCorollaries

section AxiomChecks

/-- info: 'FormalResearch.ModularBootstrap.Crossing.mehlerOddMomentInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.mehlerOddMomentInput

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part1_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part1_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part2_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part2_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part3_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part3_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwX_one_sided_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwX_one_sided_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwX_equality_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwX_equality_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_fwC_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_fwC_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_fwC_le_T_V_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_fwC_le_T_V_unconditional

end AxiomChecks

end FormalResearch.ModularBootstrap.Crossing
