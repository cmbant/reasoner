module

public import FormalResearch.ModularBootstrap.Spin.Statements
public import FormalResearch.ModularBootstrap.Spin.SpinS22Strip
public import FormalResearch.ModularBootstrap.Spin.SpinS22Outward
public import FormalResearch.ModularBootstrap.Spin.SpinS2xS21

/-!
# Lemma S2.3 (`spinnotes:S23`): Longitudinal scalar reduction

Proves the unconditional parts of `SpinS23` (`spinning_foundations.tex`, lines 310–393):
1. `spinGeff_neg`: `spinGeff a Φ (-b) = spinGeff a Φ b` for all `b : ℂ`.
2. `spinGeff_real_re_nonneg`: for real `b = x` with `|x| ≥ x₁`, if `spinG a Φ (ξ + d) (ξ - d) ≥ 0`
   on `ξ² + d² ≥ x₁²`, then `(spinGeff a Φ (x : ℂ)).re ≥ 0`.
3. `spinGeff_weighted_L1`: for `c ≥ 40` (`n = c - 1`, `a = n / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
   `x ↦ ‖spinGeff a Φ (x : ℂ)‖ * a * exp(n * spinL x)` is integrable on `ℝ` with integral
   `≤ C₁ * spinM2 a Φ` for an explicit absolute constant `C₁ > 0`.

Also proves the remaining two clauses (strip holomorphy on `spinStrip (1 / 2)` and the
`O(n² M_2[Φ])` uniform bound on `spinStrip (1 / 2)`) conditionally on the sub-bistrip
weighted `L^1` finiteness `I_θ[Φ] < ∞` for `0 < θ < 1/2` (which is `SpinS24(1)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

/-! ### Section 1: Evenness of `spinGeff` -/

lemma spinHb_neg_neg (b : ℂ) (d : ℝ) : spinHb (-b) (-d) = spinHb b d := by
  unfold spinHb
  have h1 : (-b) ^ 2 = b ^ 2 := by ring
  have h2 : (-b + ((-d : ℝ) : ℂ)) / 2 = -((b + (d : ℂ)) / 2) := by push_cast; ring
  have h3 : (-b - ((-d : ℝ) : ℂ)) / 2 = -((b - (d : ℂ)) / 2) := by push_cast; ring
  have h4 : ((-d) ^ 2 / spinSigma0 ^ 2 : ℝ) = d ^ 2 / spinSigma0 ^ 2 := by ring
  rw [h1, h2, h3, h4, Complex.tanh_neg, Complex.tanh_neg, neg_sq, neg_sq]

lemma spinGC_neg_neg (a : ℝ) (Φ : ℝ × ℝ → ℝ) (bL bR : ℂ) :
    spinGC a Φ (-bL) (-bR) = spinGC a Φ bL bR := by
  unfold spinGC
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [mul_neg, mul_neg, Complex.cos_neg, Complex.cos_neg]

theorem spinGeff_neg (a : ℝ) (Φ : ℝ × ℝ → ℝ) (b : ℂ) :
    spinGeff a Φ (-b) = spinGeff a Φ b := by
  unfold spinGeff
  congr 1
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun d => ?_)
  have h1 : (-b + ((-d : ℝ) : ℂ)) = -(b + (d : ℂ)) := by push_cast; ring
  have h2 : (-b - ((-d : ℝ) : ℂ)) = -(b - (d : ℂ)) := by push_cast; ring
  change spinHb (-b) (-d) * spinGC a Φ (-b + ((-d : ℝ) : ℂ)) (-b - ((-d : ℝ) : ℂ)) =
    spinHb b d * spinGC a Φ (b + (d : ℂ)) (b - (d : ℂ))
  rw [spinHb_neg_neg, h1, h2, spinGC_neg_neg]

/-! ### Section 2: Real-axis formula and sign preservation -/

private lemma complex_tanh_ofReal (r : ℝ) : Complex.tanh (r : ℂ) = ((Real.tanh r : ℝ) : ℂ) := by
  rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  push_cast
  rfl

private noncomputable def spinHbReal (x d : ℝ) : ℝ :=
  (1 + xiStar ^ 2) / (1 + x ^ 2) *
    (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) /
    (Real.tanh (xiStar / 2) ^ 4) *
    Real.exp (-(d ^ 2 / spinSigma0 ^ 2))

private lemma spinHb_ofReal (x d : ℝ) : spinHb (x : ℂ) d = ((spinHbReal x d : ℝ) : ℂ) := by
  unfold spinHb spinHbReal
  have h1 : (((x : ℂ) + (d : ℂ)) / 2) = (((x + d) / 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (((x : ℂ) - (d : ℂ)) / 2) = (((x - d) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, complex_tanh_ofReal, complex_tanh_ofReal]
  push_cast
  rfl

private lemma spinHbReal_nonneg (x d : ℝ) : 0 ≤ spinHbReal x d := by
  unfold spinHbReal
  have h1 : 0 ≤ 1 + xiStar ^ 2 := by positivity
  have h2 : 0 ≤ 1 + x ^ 2 := by positivity
  have h3 : 0 ≤ Real.tanh (xiStar / 2) ^ 4 := by positivity
  positivity

lemma spinGC_ofReal_eq_spinG {a : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (xL xR : ℝ) :
    spinGC a Φ (xL : ℂ) (xR : ℂ) = ((spinG a Φ xL xR : ℝ) : ℂ) := by
  unfold spinGC
  exact (spinG_eq_cosine_integral ha hΦ xL xR).symm

theorem spinGeff_real_re_nonneg {a : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (x₁ : ℝ) (_hx₁ : 0 ≤ x₁)
    (hpos : ∀ ξ d : ℝ, x₁ ^ 2 ≤ ξ ^ 2 + d ^ 2 → 0 ≤ spinG a Φ (ξ + d) (ξ - d))
    (x : ℝ) (hx : x₁ ≤ |x|) :
    0 ≤ (spinGeff a Φ (x : ℂ)).re := by
  unfold spinGeff
  have hreal_int : ∀ d : ℝ,
      spinHb (x : ℂ) d * spinGC a Φ ((x : ℂ) + (d : ℂ)) ((x : ℂ) - (d : ℂ)) =
        ((spinHbReal x d * spinG a Φ (x + d) (x - d) : ℝ) : ℂ) := by
    intro d
    have hL : (x : ℂ) + (d : ℂ) = ((x + d : ℝ) : ℂ) := by push_cast; rfl
    have hR : (x : ℂ) - (d : ℂ) = ((x - d : ℝ) : ℂ) := by push_cast; rfl
    rw [spinHb_ofReal, hL, hR, spinGC_ofReal_eq_spinG ha hΦ]
    push_cast; ring
  simp_rw [hreal_int]
  simp only [← Complex.coe_algebraMap]
  rw [integral_ofReal]
  have hc_nn : 0 ≤ 1 / (Real.sqrt π * spinSigma0) := by
    have : 0 ≤ spinSigma0 := by unfold spinSigma0; norm_num
    positivity
  have hmul : (algebraMap ℝ ℂ (1 / (Real.sqrt π * spinSigma0)) *
      algebraMap ℝ ℂ (∫ d : ℝ, spinHbReal x d * spinG a Φ (x + d) (x - d))).re =
      (1 / (Real.sqrt π * spinSigma0)) * ∫ d : ℝ, spinHbReal x d * spinG a Φ (x + d) (x - d) := by
    simp [Complex.coe_algebraMap, Complex.mul_re]
  rw [hmul]
  refine mul_nonneg hc_nn (integral_nonneg fun d => ?_)
  have hrad : x₁ ^ 2 ≤ x ^ 2 + d ^ 2 := by
    have hsq : x₁ ^ 2 ≤ |x| ^ 2 := by nlinarith
    rw [sq_abs] at hsq
    nlinarith [sq_nonneg d]
  exact mul_nonneg (spinHbReal_nonneg x d) (hpos x d hrad)

/-! ### Section 3: Weighted `L^1(ℝ)` bound for `spinGeff` -/

private lemma real_tanh_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le

private lemma real_tanh_pos {y : ℝ} (hy : 0 < y) : 0 < Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hy) (Real.cosh_pos y)

private lemma real_tanh_le_one (y : ℝ) : Real.tanh y ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_one (Real.cosh_pos y)]
  exact (Real.sinh_lt_cosh y).le

private lemma tanh_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.tanh y ≤ y := by
  have htanh_eq : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  have hmono : MonotoneOn (fun t : ℝ => t - Real.tanh t) (Ici 0) := by
    rw [htanh_eq]
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
    · exact (continuous_id.sub (Real.continuous_sinh.div Real.continuous_cosh
        (fun x => (Real.cosh_pos x).ne'))).continuousOn
    · exact (differentiable_id.sub (Real.differentiable_sinh.div Real.differentiable_cosh
        (fun x => (Real.cosh_pos x).ne'))).differentiableOn
    · intro t _
      have hdt : HasDerivAt (Real.sinh / Real.cosh) ((Real.cosh t ^ 2)⁻¹) t := by
        have hd := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
        refine hd.congr_deriv ?_
        have hch := Real.cosh_sq_sub_sinh_sq t
        field_simp [(Real.cosh_pos t).ne']
        linarith
      have hd : HasDerivAt (fun s : ℝ => s - (Real.sinh / Real.cosh) s) (1 - (Real.cosh t ^ 2)⁻¹) t :=
        (hasDerivAt_id t).sub hdt
      rw [hd.deriv, sub_nonneg]
      have hc : 1 ≤ Real.cosh t ^ 2 := by nlinarith [Real.one_le_cosh t]
      exact inv_le_one_of_one_le₀ hc
  have h0 : (0 : ℝ) - Real.tanh 0 ≤ y - Real.tanh y :=
    hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy
  simp only [Real.tanh_zero, sub_zero] at h0
  linarith

private lemma tanh_sq_le_const_mul_spinCalFc {a : ℝ} (ha : 13 / 4 ≤ a) (u : ℝ) :
    Real.tanh (u / 2) ^ 2 ≤ (0.95 : ℝ)⁻¹ ^ 2 * spinCalFc a |u| := by
  have ha2 : 2 < a := by linarith
  have ha0 : 0 < a := by linarith
  -- First show `(1 - exp(-4π |u|)) ^ 2 ≤ spinCalFc a |u|`
  have hFc : (1 - Real.exp (-4 * π * |u|)) ^ 2 ≤ spinCalFc a |u| := by
    have hγ_pos : 0 < spinGamma a := spinGamma_pos ha2
    have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := spinGamma_sq ha2.le
    have h1m : 1 ≤ a * (1 - spinGamma a) := by
      have hprod : (1 - spinGamma a) * (1 + spinGamma a) = 2 / a := by linarith
      have hsum_pos : 0 < 1 + spinGamma a := by linarith
      have h1 : a * (1 - spinGamma a) = 2 / (1 + spinGamma a) := by
        have h2 : a * (1 - spinGamma a) * (1 + spinGamma a) = 2 := by
          rw [mul_assoc, hprod]; field_simp [ha0.ne']
        exact eq_div_of_mul_eq hsum_pos.ne' h2
      rw [h1, one_le_div hsum_pos]
      linarith [spinGamma_lt_one ha2]
    have h1p : 1 ≤ a * (1 + spinGamma a) := by nlinarith
    have hexp_m : Real.exp (-π * (12 * a) * (1 - spinGamma a) * |u| / 3) ≤ Real.exp (-4 * π * |u|) := by
      refine Real.exp_le_exp.mpr ?_
      have hEq : -π * (12 * a) * (1 - spinGamma a) * |u| / 3 =
          -(4 * π * (a * (1 - spinGamma a)) * |u|) := by ring
      rw [hEq]
      have hmul : 4 * π * |u| ≤ 4 * π * (a * (1 - spinGamma a)) * |u| := by
        have : 1 * |u| ≤ (a * (1 - spinGamma a)) * |u| :=
          mul_le_mul_of_nonneg_right h1m (abs_nonneg _)
        nlinarith [Real.pi_pos]
      linarith
    have hexp_p : Real.exp (-π * (12 * a) * (1 + spinGamma a) * |u| / 3) ≤ Real.exp (-4 * π * |u|) := by
      refine Real.exp_le_exp.mpr ?_
      have hEq : -π * (12 * a) * (1 + spinGamma a) * |u| / 3 =
          -(4 * π * (a * (1 + spinGamma a)) * |u|) := by ring
      rw [hEq]
      have hmul : 4 * π * |u| ≤ 4 * π * (a * (1 + spinGamma a)) * |u| := by
        have : 1 * |u| ≤ (a * (1 + spinGamma a)) * |u| :=
          mul_le_mul_of_nonneg_right h1p (abs_nonneg _)
        nlinarith [Real.pi_pos]
      linarith
    have hnn : 0 ≤ 1 - Real.exp (-4 * π * |u|) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, abs_nonneg u]))
    unfold spinCalFc
    rw [sq]
    exact mul_le_mul (by linarith) (by linarith) hnn (by linarith)
  -- Next show `|tanh(u / 2)| ≤ (0.95)⁻¹ * (1 - exp(-4π |u|))`
  have hlin : |Real.tanh (u / 2)| ≤ (0.95 : ℝ)⁻¹ * (1 - Real.exp (-4 * π * |u|)) := by
    have habs_tanh : |Real.tanh (u / 2)| = Real.tanh (|u| / 2) := by
      rcases le_total 0 u with hu | hu
      · rw [abs_of_nonneg hu, abs_of_nonneg (real_tanh_nonneg (by linarith))]
      · have h1 : Real.tanh (u / 2) ≤ 0 := by
          have := real_tanh_nonneg (show 0 ≤ -(u / 2) by linarith)
          rw [Real.tanh_neg] at this; linarith
        rw [abs_of_nonpos hu, abs_of_nonpos h1, ← Real.tanh_neg]
        congr 1; ring
    rw [habs_tanh]
    by_cases h1 : 1 ≤ 4 * π * |u|
    · by_cases h2 : 1 / 4 ≤ |u|
      · have htanh_le : Real.tanh (|u| / 2) ≤ 1 := real_tanh_le_one _
        have hexp1 : Real.exp (-4 * π * |u|) ≤ Real.exp (-3.14) := by
          refine Real.exp_le_exp.mpr ?_
          have hpi : (3.14 : ℝ) < π := by linarith [Real.pi_gt_d4]
          nlinarith
        have hexp_bound : Real.exp (-3.14) ≤ (22 : ℝ)⁻¹ := by
          rw [Real.exp_neg]
          refine inv_anti₀ (by norm_num) ?_
          have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3.14 by norm_num) 7
          norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
          linarith
        have h095 : (0.95 : ℝ) ≤ 1 - Real.exp (-4 * π * |u|) := by linarith
        have hnum : (1 : ℝ) ≤ (0.95 : ℝ)⁻¹ * 0.95 := by norm_num
        nlinarith
      · push Not at h2
        have htanh_le : Real.tanh (|u| / 2) ≤ 1 / 8 :=
          (tanh_le_self_of_nonneg (by positivity)).trans (by linarith)
        have hexp1 : Real.exp (-4 * π * |u|) ≤ Real.exp (-1) :=
          Real.exp_le_exp.mpr (by linarith)
        have hexp_bound : Real.exp (-1) ≤ (2.5 : ℝ)⁻¹ := by
          rw [Real.exp_neg]
          refine inv_anti₀ (by norm_num) ?_
          have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 3
          norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
          linarith
        have h06 : (0.6 : ℝ) ≤ 1 - Real.exp (-4 * π * |u|) := by linarith
        have hnum : (1 / 8 : ℝ) ≤ (0.95 : ℝ)⁻¹ * 0.6 := by norm_num
        have hmul := mul_le_mul_of_nonneg_left h06 (by norm_num : (0 : ℝ) ≤ (0.95 : ℝ)⁻¹)
        linarith
    · push Not at h1
      -- `4 * π * |u| < 1`
      have h2 : Real.tanh (|u| / 2) ≤ |u| / 2 := tanh_le_self_of_nonneg (by positivity)
      have h3 : 2 * π * |u| ≤ 1 - Real.exp (-4 * π * |u|) := by
        have hexp_le : Real.exp (-4 * π * |u|) ≤ (1 + 4 * π * |u|)⁻¹ := by
          rw [show -4 * π * |u| = -(4 * π * |u|) by ring, Real.exp_neg]
          exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (4 * π * |u|)])
        have hdiv : 2 * π * |u| ≤ 1 - (1 + 4 * π * |u|)⁻¹ := by
          have hpos : 0 < 1 + 4 * π * |u| := by positivity
          have h4 : 1 - (1 + 4 * π * |u|)⁻¹ = (4 * π * |u|) / (1 + 4 * π * |u|) := by
            field_simp [hpos.ne']; ring
          rw [h4, le_div_iff₀ hpos]
          have hpiu : 0 ≤ 2 * π * |u| := by positivity
          have hmul : 2 * π * |u| * (1 + 4 * π * |u|) ≤ 2 * π * |u| * 2 :=
            mul_le_mul_of_nonneg_left (by linarith) hpiu
          linarith
        linarith
      have h4 : |u| / 2 ≤ (0.95 : ℝ)⁻¹ * (2 * π * |u|) := by
        have hpi : (3.1415 : ℝ) < π := Real.pi_gt_d4
        nlinarith [abs_nonneg u]
      have h5 : (0.95 : ℝ)⁻¹ * (2 * π * |u|) ≤ (0.95 : ℝ)⁻¹ * (1 - Real.exp (-4 * π * |u|)) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
  have hsq : Real.tanh (u / 2) ^ 2 ≤ ((0.95 : ℝ)⁻¹ * (1 - Real.exp (-4 * π * |u|))) ^ 2 := by
    rw [← sq_abs (Real.tanh (u / 2))]
    exact pow_le_pow_left₀ (abs_nonneg _) hlin 2
  calc Real.tanh (u / 2) ^ 2
      ≤ ((0.95 : ℝ)⁻¹ * (1 - Real.exp (-4 * π * |u|))) ^ 2 := hsq
    _ = (0.95 : ℝ)⁻¹ ^ 2 * (1 - Real.exp (-4 * π * |u|)) ^ 2 := by ring
    _ ≤ (0.95 : ℝ)⁻¹ ^ 2 * spinCalFc a |u| := by gcongr

/-! ### Linear change of variables `(x, d) ↦ (x + d, x - d)` -/

private noncomputable def xdToUV : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun q := ((q.1 + q.2) / 2, (q.1 - q.2) / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv q := by ext <;> dsimp <;> ring
  measurable_toFun := (measurable_fst.add measurable_snd).prodMk (measurable_fst.sub measurable_snd)
  measurable_invFun :=
    ((measurable_fst.add measurable_snd).div_const 2).prodMk
      ((measurable_fst.sub measurable_snd).div_const 2)

private lemma map_volume_shear_fst :
    Measure.map (fun p : ℝ × ℝ => (p.1 + p.2, p.2)) (volume : Measure (ℝ × ℝ)) = volume := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_preimage (by fun_prop) hs),
    Measure.prod_apply_symm hs]
  refine lintegral_congr fun y => ?_
  have hpre : (fun x : ℝ => (x, y)) ⁻¹' ((fun p : ℝ × ℝ => (p.1 + p.2, p.2)) ⁻¹' s) =
      (fun x : ℝ => x + y) ⁻¹' ((fun x : ℝ => (x, y)) ⁻¹' s) := rfl
  rw [hpre]
  have hmeas : MeasurableSet ((fun x : ℝ => (x, y)) ⁻¹' s) :=
    hs.preimage (measurable_id.prodMk measurable_const)
  rw [← Measure.map_apply (measurable_add_const y) hmeas, map_add_right_eq_self]

private lemma map_volume_shear_snd :
    Measure.map (fun p : ℝ × ℝ => (p.1, p.2 + p.1)) (volume : Measure (ℝ × ℝ)) = volume := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.volume_eq_prod, Measure.prod_apply (measurableSet_preimage (by fun_prop) hs),
    Measure.prod_apply hs]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => (p.1, p.2 + p.1)) ⁻¹' s) =
      (fun y : ℝ => y + x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre]
  have hmeas : MeasurableSet (Prod.mk x ⁻¹' s) := hs.preimage (measurable_const.prodMk measurable_id)
  rw [← Measure.map_apply (measurable_add_const x) hmeas, map_add_right_eq_self]

private lemma map_volume_xdToUV :
    Measure.map xdToUV (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure (ℝ × ℝ)) := by
  let f1 : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 + p.2, p.2)
  let f2 : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, (-2 : ℝ) * p.2)
  let f3 : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + p.1)
  have hcomp : (xdToUV : ℝ × ℝ → ℝ × ℝ) = f3 ∘ f2 ∘ f1 := by
    ext p
    · simp [xdToUV, f1, f2, f3]
    · simp [xdToUV, f1, f2, f3]; ring
  have hm1 : Measurable f1 := (measurable_fst.add measurable_snd).prodMk measurable_snd
  have hm2 : Measurable f2 := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  have hm3 : Measurable f3 := measurable_fst.prodMk (measurable_snd.add measurable_fst)
  have hmap2 : Measure.map f2 (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure (ℝ × ℝ)) := by
    have hf2 : f2 = Prod.map id ((-2 : ℝ) * ·) := rfl
    rw [hf2, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ measurable_id (measurable_const_mul (-2)),
      Measure.map_id, Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0),
      Measure.prod_smul_right]
    congr 2; norm_num
  rw [hcomp, ← Measure.map_map hm3 (hm2.comp hm1), ← Measure.map_map hm2 hm1,
    map_volume_shear_fst, hmap2, Measure.map_smul, map_volume_shear_snd]
  exact hm3.aemeasurable

noncomputable def spinGeffL1Const : ℝ :=
  (1 / (Real.sqrt π * spinSigma0)) * ((1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4) *
    ((0.95 : ℝ)⁻¹ ^ 4) * (1 / 2)

private lemma xiStar_pos' : 0 < xiStar := by
  unfold xiStar
  exact div_pos (Real.arsinh_pos_iff.mpr one_pos) Real.pi_pos

lemma spinGeffL1Const_pos : 0 < spinGeffL1Const := by
  unfold spinGeffL1Const
  have h1 : 0 < spinSigma0 := by unfold spinSigma0; norm_num
  have h2 : 0 < Real.tanh (xiStar / 2) :=
    real_tanh_pos (half_pos xiStar_pos')
  positivity

theorem spinGeff_weighted_L1 {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let n := c - 1
    let a := n / 12
    Integrable (fun x : ℝ => ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) ∧
      (∫ x : ℝ, ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) ≤
        spinGeffL1Const * spinM2 a Φ := by
  intro n a
  have ha : 13 / 4 ≤ a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have ha2 : 2 ≤ a := by linarith
  have hn : n = 12 * a := by dsimp [a, n]; ring
  set C_h : ℝ := (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4
  have hCh_pos : 0 < C_h := by
    have : 0 < Real.tanh (xiStar / 2) := real_tanh_pos (half_pos xiStar_pos')
    positivity
  -- Pointwise bound on `spinHbReal x d * a * exp(n L(x))`
  have hpt_kernel : ∀ x d : ℝ,
      spinHbReal x d * a * Real.exp (n * spinL x) ≤
        C_h * (0.95 : ℝ)⁻¹ ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
          (spinWc a (x + d) * spinWc a (x - d)) := by
    intro x d
    have h1x : (1 : ℝ) ≤ 1 + x ^ 2 := by linarith [sq_nonneg x]
    have hHb_le : spinHbReal x d ≤
        C_h * (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) *
          Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
      unfold spinHbReal
      have hdiv : (1 + xiStar ^ 2) / (1 + x ^ 2) ≤ 1 + xiStar ^ 2 :=
        div_le_self (by positivity) h1x
      have hmul1 : (1 + xiStar ^ 2) / (1 + x ^ 2) *
            (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) /
            Real.tanh (xiStar / 2) ^ 4 ≤
          C_h * (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) := by
        have hth : 0 ≤ Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2 := by positivity
        have htr : 0 < Real.tanh (xiStar / 2) ^ 4 :=
          pow_pos (real_tanh_pos (half_pos xiStar_pos')) 4
        calc (1 + xiStar ^ 2) / (1 + x ^ 2) *
              (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) /
              Real.tanh (xiStar / 2) ^ 4
            = ((1 + xiStar ^ 2) / (1 + x ^ 2) / Real.tanh (xiStar / 2) ^ 4) *
                (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) := by ring
          _ ≤ ((1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4) *
                (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hdiv htr.le) hth
          _ = C_h * (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) := rfl
      exact mul_le_mul_of_nonneg_right hmul1 (Real.exp_pos _).le
    have hL_tri : 2 * spinL x ≤ spinL (x + d) + spinL (x - d) := by
      unfold spinL
      have htri : 2 * |x| ≤ |x + d| + |x - d| := by
        have := abs_add_le (x + d) (x - d)
        have hsum : (x + d) + (x - d) = 2 * x := by ring
        rw [hsum, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at this
        exact this
      nlinarith [Real.pi_pos]
    have hexp_L : Real.exp (n * spinL x) ≤
        Real.exp (4 * π * a * |x + d|) * Real.exp (4 * π * a * |x - d|) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hEq : 4 * π * a * |x + d| + 4 * π * a * |x - d| =
          (12 * a) * ((spinL (x + d) + spinL (x - d)) / 2) := by
        unfold spinL; ring
      rw [hEq, hn]
      nlinarith
    have hT1 := tanh_sq_le_const_mul_spinCalFc ha (x + d)
    have hT2 := tanh_sq_le_const_mul_spinCalFc ha (x - d)
    have hWc1 : Real.sqrt a * Real.tanh ((x + d) / 2) ^ 2 * Real.exp (4 * π * a * |x + d|) ≤
        (0.95 : ℝ)⁻¹ ^ 2 * spinWc a (x + d) := by
      rw [spinWc_factorization ha2 (x + d)]
      calc Real.sqrt a * Real.tanh ((x + d) / 2) ^ 2 * Real.exp (4 * π * a * |x + d|)
          ≤ Real.sqrt a * ((0.95 : ℝ)⁻¹ ^ 2 * spinCalFc a |x + d|) * Real.exp (4 * π * a * |x + d|) := by
            gcongr
        _ = (0.95 : ℝ)⁻¹ ^ 2 * (Real.sqrt a * Real.exp (4 * π * a * |x + d|) * spinCalFc a |x + d|) := by
            ring
    have hWc2 : Real.sqrt a * Real.tanh ((x - d) / 2) ^ 2 * Real.exp (4 * π * a * |x - d|) ≤
        (0.95 : ℝ)⁻¹ ^ 2 * spinWc a (x - d) := by
      rw [spinWc_factorization ha2 (x - d)]
      calc Real.sqrt a * Real.tanh ((x - d) / 2) ^ 2 * Real.exp (4 * π * a * |x - d|)
          ≤ Real.sqrt a * ((0.95 : ℝ)⁻¹ ^ 2 * spinCalFc a |x - d|) * Real.exp (4 * π * a * |x - d|) := by
            gcongr
        _ = (0.95 : ℝ)⁻¹ ^ 2 * (Real.sqrt a * Real.exp (4 * π * a * |x - d|) * spinCalFc a |x - d|) := by
            ring
    have hsqa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
    calc spinHbReal x d * a * Real.exp (n * spinL x)
        ≤ (C_h * (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) *
            Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * a *
            (Real.exp (4 * π * a * |x + d|) * Real.exp (4 * π * a * |x - d|)) := by
          gcongr
      _ = C_h * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
            ((Real.sqrt a * Real.tanh ((x + d) / 2) ^ 2 * Real.exp (4 * π * a * |x + d|)) *
             (Real.sqrt a * Real.tanh ((x - d) / 2) ^ 2 * Real.exp (4 * π * a * |x - d|))) := by
          calc (C_h * (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) *
                  Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * a *
                  (Real.exp (4 * π * a * |x + d|) * Real.exp (4 * π * a * |x - d|))
              = (C_h * (Real.tanh ((x + d) / 2) ^ 2 * Real.tanh ((x - d) / 2) ^ 2) *
                  Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * (Real.sqrt a * Real.sqrt a) *
                  (Real.exp (4 * π * a * |x + d|) * Real.exp (4 * π * a * |x - d|)) := by rw [hsqa]
            _ = C_h * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                  ((Real.sqrt a * Real.tanh ((x + d) / 2) ^ 2 * Real.exp (4 * π * a * |x + d|)) *
                   (Real.sqrt a * Real.tanh ((x - d) / 2) ^ 2 * Real.exp (4 * π * a * |x - d|))) := by
                ring
      _ ≤ C_h * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
            (((0.95 : ℝ)⁻¹ ^ 2 * spinWc a (x + d)) * ((0.95 : ℝ)⁻¹ ^ 2 * spinWc a (x - d))) := by
          have hnn1 : 0 ≤ C_h * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by positivity
          have hnn2 : 0 ≤ (0.95 : ℝ)⁻¹ ^ 2 * spinWc a (x + d) :=
            mul_nonneg (by positivity) (spinWc_nonneg ha2 _)
          exact mul_le_mul_of_nonneg_left (mul_le_mul hWc1 hWc2 (by positivity) hnn2) hnn1
      _ = C_h * (0.95 : ℝ)⁻¹ ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
            (spinWc a (x + d) * spinWc a (x - d)) := by ring
  -- Integrability of the majorant `|G(x+d, x-d)| * w_c(x+d) * w_c(x-d)` on `ℝ × ℝ`
  let maj : ℝ × ℝ → ℝ := fun p =>
    |spinG a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)
  have hmaj_int : Integrable maj volume := by
    have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) volume :=
      integrable_spinG_wc ha0 hΦ
    have hsm : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
        (Measure.map xdToUV volume) := by
      rw [map_volume_xdToUV]
      exact hG_int.smul_measure ENNReal.ofReal_lt_top.ne
    exact (integrable_map_measure hsm.aestronglyMeasurable xdToUV.measurable.aemeasurable).mp hsm
  have hmaj_val : ∫ p : ℝ × ℝ, maj p = (1 / 2 : ℝ) * spinM2 a Φ := by
    have h1 := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) xdToUV
      (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
    rw [map_volume_xdToUV, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul,
      ← spinM2_eq_spinWc ha0 Φ] at h1
    exact h1.symm
  -- Dominate `‖spinGeff a Φ (x : ℂ)‖ * a * exp(n L(x))` by `C_const * ∫ d, maj (x, d)`
  have hGeff_norm : ∀ x : ℝ,
      ‖spinGeff a Φ (x : ℂ)‖ ≤ (1 / (Real.sqrt π * spinSigma0)) *
        ∫ d : ℝ, spinHbReal x d * |spinG a Φ (x + d) (x - d)| := by
    intro x
    unfold spinGeff
    have hreal_int : ∀ d : ℝ,
        spinHb (x : ℂ) d * spinGC a Φ ((x : ℂ) + (d : ℂ)) ((x : ℂ) - (d : ℂ)) =
          ((spinHbReal x d * spinG a Φ (x + d) (x - d) : ℝ) : ℂ) := by
      intro d
      have hL : (x : ℂ) + (d : ℂ) = ((x + d : ℝ) : ℂ) := by push_cast; rfl
      have hR : (x : ℂ) - (d : ℂ) = ((x - d : ℝ) : ℂ) := by push_cast; rfl
      rw [spinHb_ofReal, hL, hR, spinGC_ofReal_eq_spinG ha0.le hΦ]
      push_cast; ring
    simp_rw [hreal_int]
    simp only [← Complex.coe_algebraMap]
    rw [integral_ofReal]
    simp only [Complex.coe_algebraMap]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by unfold spinSigma0; positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by unfold spinSigma0; positivity)
    refine (abs_integral_le_integral_abs).trans_eq (integral_congr_ae (Eventually.of_forall fun d => ?_))
    dsimp only
    rw [abs_mul, abs_of_nonneg (spinHbReal_nonneg x d)]
  have hmaj_prod : Integrable maj (volume.prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have hmaj_ae : ∀ᵐ x : ℝ, Integrable (fun d : ℝ => maj (x, d)) := hmaj_prod.prod_right_ae
  have hmaj_int_x : Integrable (fun x : ℝ => ∫ d : ℝ, maj (x, d)) := hmaj_prod.integral_prod_left
  have hmaj_int_eq : ∫ x : ℝ, ∫ d : ℝ, maj (x, d) = (1 / 2 : ℝ) * spinM2 a Φ := by
    rw [← integral_prod maj hmaj_prod, ← Measure.volume_eq_prod, hmaj_val]
  have hGeff_bound : ∀ᵐ x : ℝ,
      ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) ≤
        ((1 / (Real.sqrt π * spinSigma0)) * C_h * (0.95 : ℝ)⁻¹ ^ 4) * ∫ d : ℝ, maj (x, d) := by
    filter_upwards [hmaj_ae] with x hxmaj
    have h1 : ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x) ≤
        (1 / (Real.sqrt π * spinSigma0)) *
          ∫ d : ℝ, (spinHbReal x d * a * Real.exp (n * spinL x)) * |spinG a Φ (x + d) (x - d)| := by
      calc ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)
          = ‖spinGeff a Φ (x : ℂ)‖ * (a * Real.exp (n * spinL x)) := by ring
        _ ≤ ((1 / (Real.sqrt π * spinSigma0)) *
              ∫ d : ℝ, spinHbReal x d * |spinG a Φ (x + d) (x - d)|) *
              (a * Real.exp (n * spinL x)) :=
            mul_le_mul_of_nonneg_right (hGeff_norm x) (by positivity)
        _ = (1 / (Real.sqrt π * spinSigma0)) *
              ∫ d : ℝ, (spinHbReal x d * |spinG a Φ (x + d) (x - d)|) * (a * Real.exp (n * spinL x)) := by
            rw [mul_assoc, ← integral_mul_const]
        _ = (1 / (Real.sqrt π * spinSigma0)) *
              ∫ d : ℝ, (spinHbReal x d * a * Real.exp (n * spinL x)) * |spinG a Φ (x + d) (x - d)| := by
            congr 1; refine integral_congr_ae (Eventually.of_forall fun d => by ring)
    have h2 : ∫ d : ℝ, (spinHbReal x d * a * Real.exp (n * spinL x)) * |spinG a Φ (x + d) (x - d)| ≤
        ∫ d : ℝ, (C_h * (0.95 : ℝ)⁻¹ ^ 4) * maj (x, d) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun d =>
          mul_nonneg (mul_nonneg (mul_nonneg (spinHbReal_nonneg x d) ha0.le) (Real.exp_pos _).le)
            (abs_nonneg _))
        (hxmaj.const_mul _) (Eventually.of_forall fun d => ?_)
      have hpt := hpt_kernel x d
      have hexp_le : Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg d) (sq_nonneg spinSigma0)))
      have hwc_nn : 0 ≤ spinWc a (x + d) * spinWc a (x - d) :=
        mul_nonneg (spinWc_nonneg ha2 _) (spinWc_nonneg ha2 _)
      have hpt1 : spinHbReal x d * a * Real.exp (n * spinL x) ≤
          C_h * (0.95 : ℝ)⁻¹ ^ 4 * (spinWc a (x + d) * spinWc a (x - d)) := by
        calc spinHbReal x d * a * Real.exp (n * spinL x)
            ≤ C_h * (0.95 : ℝ)⁻¹ ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
                (spinWc a (x + d) * spinWc a (x - d)) := hpt
          _ ≤ C_h * (0.95 : ℝ)⁻¹ ^ 4 * 1 * (spinWc a (x + d) * spinWc a (x - d)) := by
              gcongr
          _ = C_h * (0.95 : ℝ)⁻¹ ^ 4 * (spinWc a (x + d) * spinWc a (x - d)) := by ring
      calc (spinHbReal x d * a * Real.exp (n * spinL x)) * |spinG a Φ (x + d) (x - d)|
          ≤ (C_h * (0.95 : ℝ)⁻¹ ^ 4 * (spinWc a (x + d) * spinWc a (x - d))) *
              |spinG a Φ (x + d) (x - d)| :=
            mul_le_mul_of_nonneg_right hpt1 (abs_nonneg _)
        _ = (C_h * (0.95 : ℝ)⁻¹ ^ 4) * maj (x, d) := by dsimp [maj]; ring
    rw [integral_const_mul] at h2
    calc ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)
        ≤ (1 / (Real.sqrt π * spinSigma0)) * ((C_h * (0.95 : ℝ)⁻¹ ^ 4) * ∫ d : ℝ, maj (x, d)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by unfold spinSigma0; positivity))
      _ = ((1 / (Real.sqrt π * spinSigma0)) * C_h * (0.95 : ℝ)⁻¹ ^ 4) * ∫ d : ℝ, maj (x, d) := by
          ring
  have haesm : AEStronglyMeasurable
      (fun x : ℝ => ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) volume := by
    have hcont_tanh : Continuous Real.tanh := by
      rw [show Real.tanh = Real.sinh / Real.cosh from funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
    have hcont_f : Continuous (fun p : ℝ × ℝ => spinHbReal p.1 p.2 * spinG a Φ (p.1 + p.2) (p.1 - p.2)) := by
      have h1 : Continuous (fun p : ℝ × ℝ => spinHbReal p.1 p.2) := by
        unfold spinHbReal
        refine (((continuous_const.div (continuous_const.add (continuous_fst.pow 2))
          (fun p => (add_pos_of_pos_of_nonneg one_pos (sq_nonneg p.1)).ne')).mul
          ((hcont_tanh.comp ((continuous_fst.add continuous_snd).div_const 2)).pow 2 |>.mul
          ((hcont_tanh.comp ((continuous_fst.sub continuous_snd).div_const 2)).pow 2))).div_const _).mul
          (Real.continuous_exp.comp (((continuous_snd.pow 2).div_const _).neg))
      have h2 : Continuous (fun p : ℝ × ℝ => spinG a Φ (p.1 + p.2) (p.1 - p.2)) := by
        unfold spinG
        exact hΦ.cont.comp ((continuous_const.mul (continuous_fst.add continuous_snd)).prodMk
          (continuous_const.mul (continuous_fst.sub continuous_snd)))
      exact h1.mul h2
    have haesm_geff : AEStronglyMeasurable (fun x : ℝ => spinGeff a Φ (x : ℂ)) volume := by
      have heq : (fun x : ℝ => spinGeff a Φ (x : ℂ)) =
          fun x : ℝ => ((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ) *
            ((∫ d : ℝ, spinHbReal x d * spinG a Φ (x + d) (x - d) : ℝ) : ℂ) := by
        ext x
        unfold spinGeff
        have hreal_int : ∀ d : ℝ,
            spinHb (x : ℂ) d * spinGC a Φ ((x : ℂ) + (d : ℂ)) ((x : ℂ) - (d : ℂ)) =
              ((spinHbReal x d * spinG a Φ (x + d) (x - d) : ℝ) : ℂ) := by
          intro d
          have hL : (x : ℂ) + (d : ℂ) = ((x + d : ℝ) : ℂ) := by push_cast; rfl
          have hR : (x : ℂ) - (d : ℂ) = ((x - d : ℝ) : ℂ) := by push_cast; rfl
          rw [spinHb_ofReal, hL, hR, spinGC_ofReal_eq_spinG ha0.le hΦ]
          push_cast; ring
        simp_rw [hreal_int]
        simp only [← Complex.coe_algebraMap, integral_ofReal]
      rw [heq]
      exact AEStronglyMeasurable.const_mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable
          hcont_f.aestronglyMeasurable.integral_prod_right') _
    have hcont_w : Continuous (fun x : ℝ => a * Real.exp (n * spinL x)) := by
      unfold spinL
      exact continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_const.mul continuous_abs).div_const _)))
    exact (haesm_geff.norm.mul hcont_w.aestronglyMeasurable).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hint_lhs : Integrable (fun x : ℝ => ‖spinGeff a Φ (x : ℂ)‖ * a * Real.exp (n * spinL x)) := by
    refine (hmaj_int_x.const_mul ((1 / (Real.sqrt π * spinSigma0)) * C_h * (0.95 : ℝ)⁻¹ ^ 4)).mono'
      haesm ?_
    filter_upwards [hGeff_bound] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  refine ⟨hint_lhs, ?_⟩
  have hmono := integral_mono_ae hint_lhs
    (hmaj_int_x.const_mul ((1 / (Real.sqrt π * spinSigma0)) * C_h * (0.95 : ℝ)⁻¹ ^ 4)) hGeff_bound
  rw [integral_const_mul, hmaj_int_eq] at hmono
  refine hmono.trans_eq ?_
  unfold spinGeffL1Const C_h
  ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinGeff_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinGeff_neg

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinGeff_real_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinGeff_real_re_nonneg

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinGeff_weighted_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinGeff_weighted_L1

end FormalResearch.ModularBootstrap.Spin
