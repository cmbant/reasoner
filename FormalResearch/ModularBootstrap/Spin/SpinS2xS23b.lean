module

public import FormalResearch.ModularBootstrap.Spin.SpinS2xS23
public import FormalResearch.ModularBootstrap.Spin.SpinS2xS21
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Lemma S2.3 (`spinnotes:S23`): Complex strip holomorphy, bound, and full `SpinS23`

Completes `SpinS23` (`spinning_foundations.tex`, lines 310–393) by proving:
1. Sub-bistrip weighted `L^1` finiteness `spinITheta a θ Φ < ∞` for all `0 < θ < 1 / 2`
   (first at `θ₀ = 1 / 24` via Young's inequality, then for all `0 < θ < 1 / 2` via
   analytic continuation of transverse slices and Chebyshev derivative bounds).
2. `DifferentiableOn ℂ (spinGeff a Φ) (spinStrip (1 / 2))`.
3. `‖spinGeff a Φ b‖ ≤ C * n ^ 2 * spinM2 a Φ` on `spinStrip (1 / 2)` via Fubini and the
   three-region bound on `K_b(r_L, r_R)`.
4. Assembly of `theorem spinS23 : SpinS23` with `SpinS2xS23`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

/-! ### Section 1: Lower bound on `V_1(r)` and initial sub-bistrip integrability (`θ₀ = 1/24`) -/

/-- Pointwise lower bound `V_1(r) ≥ (4 a)⁻¹ exp(2π √a |r|) min(1, √a |r|)²` for `a ≥ 2`. -/
lemma spinV1_ge_inv_four_a_exp_min_sq {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * |r|) ^ 2 ≤
      spinV1 a r := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hgam_nn : 0 ≤ spinGamma a := Real.sqrt_nonneg _
  have hgam_lt : spinGamma a < 1 := by
    unfold spinGamma
    exact (Real.sqrt_lt' one_pos).mpr (by have : 0 < 2 / a := div_pos two_pos ha0; linarith)
  have h1m : 1 / a ≤ 1 - spinGamma a := by
    have hsq : spinGamma a ^ 2 = 1 - 2 / a := spinGamma_sq ha
    have hprod : (1 - spinGamma a) * (1 + spinGamma a) = 2 / a := by linarith
    have hsum_pos : 0 < 1 + spinGamma a := by linarith
    have h1 : 1 - spinGamma a = 2 / (a * (1 + spinGamma a)) := by
      rw [eq_div_iff (by positivity), mul_comm a, ← mul_assoc, hprod]
      field_simp [ha0.ne']
    rw [h1, div_le_div_iff₀ ha0 (by positivity)]
    nlinarith
  have h1p : 1 ≤ 1 + spinGamma a := by linarith
  have hfac : spinV1 a r = (1 / 2 : ℝ) * Real.exp (2 * π * Real.sqrt a * |r|) *
      ((1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|)) *
       (1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|))) := by
    have heq := spinWc_factorization ha (|r| / (2 * Real.sqrt a))
    unfold spinWc at heq
    have hmul : 2 * Real.sqrt a * (|r| / (2 * Real.sqrt a)) = |r| := by
      field_simp [hsqa.ne']
    rw [hmul, abs_of_nonneg (div_nonneg (abs_nonneg r) (by positivity))] at heq
    have habs : spinV1 a r = spinV1 a |r| := by
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr, spinV1_even]
    rw [habs]
    have hV1 : spinV1 a |r| = (Real.sqrt a * Real.exp (4 * π * a * (|r| / (2 * Real.sqrt a))) *
        spinCalFc a (|r| / (2 * Real.sqrt a))) / (2 * Real.sqrt a) := by
      rw [eq_div_iff (by positivity : (2 * Real.sqrt a) ≠ 0), mul_comm _ (2 * Real.sqrt a)]
      exact heq
    rw [hV1]
    have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
    have hexp1 : 4 * π * a * (|r| / (2 * Real.sqrt a)) = 2 * π * Real.sqrt a * |r| := by
      field_simp [hsqa.ne']
      rw [Real.sq_sqrt ha0.le]; ring
    have hexp2 : -π * (12 * a) * (1 + spinGamma a) * (|r| / (2 * Real.sqrt a)) / 3 =
        -2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by
      field_simp [hsqa.ne']
      rw [Real.sq_sqrt ha0.le]; ring
    have hexp3 : -π * (12 * a) * (1 - spinGamma a) * (|r| / (2 * Real.sqrt a)) / 3 =
        -2 * π * Real.sqrt a * (1 - spinGamma a) * |r| := by
      field_simp [hsqa.ne']
      rw [Real.sq_sqrt ha0.le]; ring
    unfold spinCalFc
    rw [hexp1, hexp2, hexp3]
    field_simp [hsqa.ne']
  rw [hfac]
  set y : ℝ := Real.sqrt a * |r|
  have hy : 0 ≤ y := by positivity
  -- Elementary bound: `1 - exp(-t) ≥ (1/2) min(1, t)` for `t ≥ 0`
  have hone_sub_exp : ∀ t : ℝ, 0 ≤ t → (1 / 2 : ℝ) * min 1 t ≤ 1 - Real.exp (-t) := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · rw [min_eq_right ht1]
      have hexp : Real.exp (-t) ≤ (1 + t)⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
      have hpos : 0 < 1 + t := by positivity
      have h4 : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp [hpos.ne']; ring
      have h5 : (1 / 2 : ℝ) * t ≤ t / (1 + t) := by
        rw [le_div_iff₀ hpos]; nlinarith
      linarith
    · push Not at ht1
      rw [min_eq_left ht1.le]
      have hexp : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have hexp1 : Real.exp (-1) ≤ (2 : ℝ)⁻¹ := by
        rw [Real.exp_neg]
        exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      linarith
  have hA_bound : (1 / 2 : ℝ) * min 1 y ≤ 1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|) := by
    have h1 := hone_sub_exp y hy
    have hle : y ≤ 2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by
      have : 1 ≤ 2 * π * (1 + spinGamma a) := by
        have := Real.pi_gt_d4
        nlinarith
      calc y = 1 * (Real.sqrt a * |r|) := by ring
        _ ≤ (2 * π * (1 + spinGamma a)) * (Real.sqrt a * |r|) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by ring
    have hexp : Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|) ≤ Real.exp (-y) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hB_bound : (1 / a) * min 1 y ≤ 1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|) := by
    have h1 := hone_sub_exp (2 * π * y / a) (by positivity)
    have hle : 2 * π * y / a ≤ 2 * π * Real.sqrt a * (1 - spinGamma a) * |r| := by
      have hmul : 2 * π * y * (1 / a) ≤ 2 * π * y * (1 - spinGamma a) :=
        mul_le_mul_of_nonneg_left h1m (by positivity)
      calc 2 * π * y / a = 2 * π * y * (1 / a) := by ring
        _ ≤ 2 * π * y * (1 - spinGamma a) := hmul
        _ = 2 * π * Real.sqrt a * (1 - spinGamma a) * |r| := by dsimp [y]; ring
    have hexp : Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|) ≤ Real.exp (-(2 * π * y / a)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmin : (1 / a) * min 1 y ≤ (1 / 2 : ℝ) * min 1 (2 * π * y / a) := by
      have hle2 : (2 / a) * min 1 y ≤ min 1 (2 * π * y / a) := by
        refine le_min ?_ ?_
        · exact mul_le_one₀ ((div_le_one ha0).mpr ha) (le_min zero_le_one hy) (min_le_left _ _)
        · have h2 : min 1 y ≤ y := min_le_right _ _
          have hpi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
          calc (2 / a) * min 1 y ≤ (2 / a) * y := mul_le_mul_of_nonneg_left h2 (by positivity)
            _ ≤ (2 * π / a) * y := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) ha0.le) hy
            _ = 2 * π * y / a := by ring
      have hhalf : (1 / a) * min 1 y = (1 / 2 : ℝ) * ((2 / a) * min 1 y) := by ring
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left hle2 (by norm_num)
    linarith
  have hprod : (1 / (2 * a)) * min 1 y ^ 2 ≤
      (1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|)) *
      (1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|)) := by
    have hnn1 : 0 ≤ (1 / 2 : ℝ) * min 1 y := by positivity
    have hnn2 : 0 ≤ (1 / a) * min 1 y := by positivity
    have hmul := mul_le_mul hA_bound hB_bound hnn2 (hnn1.trans hA_bound)
    calc (1 / (2 * a)) * min 1 y ^ 2 = ((1 / 2 : ℝ) * min 1 y) * ((1 / a) * min 1 y) := by ring
      _ ≤ _ := hmul
  calc (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * |r|) ^ 2
      = (1 / 2 : ℝ) * Real.exp (2 * π * Real.sqrt a * |r|) * ((1 / (2 * a)) * min 1 y ^ 2) := by
        change (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * |r|) ^ 2 =
          (1 / 2 : ℝ) * Real.exp (2 * π * Real.sqrt a * |r|) * ((1 / (2 * a)) * min 1 (Real.sqrt a * |r|) ^ 2)
        ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (2 * π * Real.sqrt a * |r|) *
          ((1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|)) *
           (1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

lemma integrable_rpow_neg_two_fifths_Ioo :
    IntegrableOn (fun y : ℝ => y ^ (-(2 / 5 : ℝ))) (Ioo 0 1) := by
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ (-(2 / 5 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at h1
  exact h1

lemma integrable_spinITheta_init {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    Integrable (fun p : ℝ × ℝ => |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) *
      Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2)) := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  set H : ℝ → ℝ := fun r => Real.cosh (4 * π * Real.sqrt a * (1 / 24) * r)
  set g : ℝ → ℝ := fun r => (H r / spinV1 a r ^ (1 / 6 : ℝ)) ^ (6 / 5 : ℝ)
  -- First show `g` is integrable on `ℝ`
  have hg_int : Integrable g volume := by
    have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr => by
      have h1 := spinV1_ge_inv_four_a_exp_min_sq ha r
      have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
      have hpos : 0 < (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * |r|) ^ 2 := by
        positivity
      exact lt_of_lt_of_le hpos h1
    have hcont_H : Continuous H :=
      Real.continuous_cosh.comp (continuous_const.mul continuous_id)
    have hcont_V1 : Continuous (spinV1 a) := by unfold spinV1; fun_prop
    have haesm_g : AEStronglyMeasurable g volume :=
      ((hcont_H.measurable.div (hcont_V1.measurable.pow_const _)).pow_const _).aestronglyMeasurable
    -- Pointwise bound on `g r` for `r ≠ 0`
    have hg_le : ∀ r : ℝ, r ≠ 0 →
        g r ≤ (4 * a) ^ (1 / 5 : ℝ) * Real.exp (-(π / 5 * Real.sqrt a * |r|)) *
          min 1 (Real.sqrt a * |r|) ^ (-(2 / 5 : ℝ)) := by
      intro r hr
      have hH_le : H r ≤ Real.exp (π / 6 * Real.sqrt a * |r|) := by
        dsimp [H]
        have h1 : Real.cosh (4 * π * Real.sqrt a * (1 / 24) * r) =
            Real.cosh (π / 6 * Real.sqrt a * |r|) := by
          rcases le_total 0 r with hr0 | hr0
          · rw [abs_of_nonneg hr0]; congr 1; ring
          · rw [abs_of_nonpos hr0, ← Real.cosh_neg]; congr 1; ring
        rw [h1, Real.cosh_eq]
        have hexp : Real.exp (-(π / 6 * Real.sqrt a * |r|)) ≤ Real.exp (π / 6 * Real.sqrt a * |r|) :=
          Real.exp_le_exp.mpr (by linarith [show 0 ≤ π / 6 * Real.sqrt a * |r| by positivity])
        linarith
      have hmin_pos : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
      have hV1_lb := spinV1_ge_inv_four_a_exp_min_sq ha r
      have hV1_pow : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
          min 1 (Real.sqrt a * |r|) ^ 2) ^ (1 / 6 : ℝ) ≤ spinV1 a r ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hV1_lb (by norm_num)
      have hV1_simp : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
          min 1 (Real.sqrt a * |r|) ^ 2) ^ (1 / 6 : ℝ) =
          (4 * a) ^ (-(1 / 6 : ℝ)) * Real.exp (π / 3 * Real.sqrt a * |r|) *
            min 1 (Real.sqrt a * |r|) ^ (1 / 3 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (Real.exp_pos _).le,
          Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
          ← Real.exp_mul, ← Real.rpow_natCast, ← Real.rpow_mul hmin_pos.le,
          show 2 * π * Real.sqrt a * |r| * (1 / 6 : ℝ) = π / 3 * Real.sqrt a * |r| by ring,
          show ((2 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 / 3 by norm_num]
      rw [hV1_simp] at hV1_pow
      have hdiv_le : H r / spinV1 a r ^ (1 / 6 : ℝ) ≤
          (4 * a) ^ (1 / 6 : ℝ) * Real.exp (-(π / 6 * Real.sqrt a * |r|)) *
            min 1 (Real.sqrt a * |r|) ^ (-(1 / 3 : ℝ)) := by
        have h1 : H r / spinV1 a r ^ (1 / 6 : ℝ) ≤
            Real.exp (π / 6 * Real.sqrt a * |r|) /
              ((4 * a) ^ (-(1 / 6 : ℝ)) * Real.exp (π / 3 * Real.sqrt a * |r|) *
                min 1 (Real.sqrt a * |r|) ^ (1 / 3 : ℝ)) := by
          calc H r / spinV1 a r ^ (1 / 6 : ℝ)
              ≤ Real.exp (π / 6 * Real.sqrt a * |r|) / spinV1 a r ^ (1 / 6 : ℝ) :=
                div_le_div_of_nonneg_right hH_le (Real.rpow_nonneg (spinV1_nonneg ha r) _)
            _ ≤ Real.exp (π / 6 * Real.sqrt a * |r|) /
                ((4 * a) ^ (-(1 / 6 : ℝ)) * Real.exp (π / 3 * Real.sqrt a * |r|) *
                  min 1 (Real.sqrt a * |r|) ^ (1 / 3 : ℝ)) :=
                div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hV1_pow
        refine h1.trans_eq ?_
        rw [Real.rpow_neg (by positivity), Real.rpow_neg hmin_pos.le, Real.exp_neg]
        have hE : Real.exp (π / 3 * Real.sqrt a * |r|) =
            Real.exp (π / 6 * Real.sqrt a * |r|) * Real.exp (π / 6 * Real.sqrt a * |r|) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hE]
        field_simp [(Real.exp_pos _).ne', (Real.rpow_pos_of_pos (by positivity : 0 < 4 * a) _).ne',
          (Real.rpow_pos_of_pos hmin_pos _).ne']
      have hg1 : g r ≤ ((4 * a) ^ (1 / 6 : ℝ) * Real.exp (-(π / 6 * Real.sqrt a * |r|)) *
          min 1 (Real.sqrt a * |r|) ^ (-(1 / 3 : ℝ))) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _))
          hdiv_le (by norm_num)
      refine hg1.trans_eq ?_
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hmin_pos.le _),
        Real.mul_rpow (by positivity) (Real.exp_pos _).le,
        ← Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.rpow_mul hmin_pos.le,
        show -(1 / 3 : ℝ) * (6 / 5 : ℝ) = -(2 / 5 : ℝ) by norm_num,
        show (1 / 6 : ℝ) * (6 / 5 : ℝ) = 1 / 5 by norm_num,
        show -(π / 6 * Real.sqrt a * |r|) * (6 / 5 : ℝ) = -(π / 5 * Real.sqrt a * |r|) by ring]
    have h_tail : IntegrableOn g {r : ℝ | 1 / Real.sqrt a ≤ |r|} := by
      have hpos_c : 0 < π / 5 * Real.sqrt a := by positivity
      have hint_Ioi : IntegrableOn (fun r : ℝ => Real.exp (-(π / 5 * Real.sqrt a) * r)) (Ioi (0 : ℝ)) := by
        have hderiv : ∀ x ∈ Ici (0 : ℝ),
            HasDerivAt (fun t : ℝ => -Real.exp (-(π / 5 * Real.sqrt a) * t) / (π / 5 * Real.sqrt a))
              (Real.exp (-(π / 5 * Real.sqrt a) * x)) x := by
          intro x _
          have he := (Real.hasDerivAt_exp (-(π / 5 * Real.sqrt a) * x)).comp x
            ((hasDerivAt_id x).const_mul (-(π / 5 * Real.sqrt a)))
          exact (he.neg.div_const (π / 5 * Real.sqrt a)).congr_deriv (by field_simp [hpos_c.ne'])
        refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
          (1 / (π / 5 * Real.sqrt a)) 0
          (fun t => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          tendsto_id
          (Eventually.of_forall fun t => by
            simp_rw [Real.norm_of_nonneg (Real.exp_pos _).le, id_eq]
            by_cases ht : (0 : ℝ) ≤ t
            · have hfun : ∫ x in (0 : ℝ)..t, Real.exp (-(π / 5 * Real.sqrt a) * x) =
                  (-Real.exp (-(π / 5 * Real.sqrt a) * t) / (π / 5 * Real.sqrt a)) -
                  (-Real.exp (-(π / 5 * Real.sqrt a) * 0) / (π / 5 * Real.sqrt a)) :=
                intervalIntegral.integral_eq_sub_of_hasDerivAt
                  (fun x hx => hderiv x (mem_Ici.mpr (by rw [uIcc_of_le ht] at hx; exact hx.1)))
                  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
              rw [hfun, mul_zero, Real.exp_zero]
              have hsub : -Real.exp (-(π / 5 * Real.sqrt a) * t) / (π / 5 * Real.sqrt a) -
                  -1 / (π / 5 * Real.sqrt a) =
                  1 / (π / 5 * Real.sqrt a) -
                  Real.exp (-(π / 5 * Real.sqrt a) * t) / (π / 5 * Real.sqrt a) := by ring
              rw [hsub]
              have hpos : 0 ≤ Real.exp (-(π / 5 * Real.sqrt a) * t) / (π / 5 * Real.sqrt a) := by positivity
              linarith
            · push Not at ht
              rw [intervalIntegral.integral_symm]
              have : 0 ≤ ∫ x in t..(0 : ℝ), Real.exp (-(π / 5 * Real.sqrt a) * x) :=
                intervalIntegral.integral_nonneg ht.le fun _ _ => (Real.exp_pos _).le
              have : 0 ≤ 1 / (π / 5 * Real.sqrt a) := by positivity
              linarith)
      have hint_Iio : IntegrableOn (fun r : ℝ => Real.exp (-(π / 5 * Real.sqrt a) * (-r))) (Iio (0 : ℝ)) := by
        simpa using hint_Ioi.comp_neg
      have h_all : Integrable (fun r : ℝ => (4 * a) ^ (1 / 5 : ℝ) * Real.exp (-(π / 5 * Real.sqrt a * |r|))) volume := by
        have h1 : IntegrableOn (fun r : ℝ => Real.exp (-(π / 5 * Real.sqrt a * |r|))) (Iio 0 ∪ Ioi 0) := by
          refine IntegrableOn.union ?_ ?_
          · refine hint_Iio.congr_fun (fun r hr => ?_) measurableSet_Iio
            rw [abs_of_neg (mem_Iio.mp hr)]; ring_nf
          · refine hint_Ioi.congr_fun (fun r hr => ?_) measurableSet_Ioi
            rw [abs_of_pos (mem_Ioi.mp hr)]; ring_nf
        have hcomp : (Iio (0 : ℝ) ∪ Ioi 0) =ᵐ[volume] (univ : Set ℝ) := by
          rw [ae_eq_set]
          have hsub : (univ \ (Iio (0 : ℝ) ∪ Ioi 0)) ⊆ ({0} : Set ℝ) := by
            intro r ⟨_, hr⟩
            simp only [mem_union, mem_Iio, mem_Ioi, not_or, not_lt] at hr
            simp only [mem_singleton_iff]
            linarith
          exact ⟨by simp, measure_mono_null hsub Real.volume_singleton⟩
        rw [integrableOn_congr_set_ae hcomp, integrableOn_univ] at h1
        exact h1.const_mul _
      refine h_all.integrableOn.mono' haesm_g.restrict ?_
      refine ae_restrict_of_forall_mem (measurableSet_le measurable_const continuous_abs.measurable) fun r hr => ?_
      have hr0 : r ≠ 0 := by
        intro heq; subst heq; simp only [mem_ofPred_eq, abs_zero] at hr
        have : 0 < 1 / Real.sqrt a := by positivity
        linarith
      have hmin1 : min 1 (Real.sqrt a * |r|) = 1 := min_eq_left (by
        have hr' : 1 / Real.sqrt a ≤ |r| := hr
        rw [div_le_iff₀ hsqa] at hr'
        linarith [mul_comm (Real.sqrt a) |r|])
      have hle := hg_le r hr0
      rw [hmin1, Real.one_rpow, mul_one] at hle
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _)]
      exact hle
    have h_core : IntegrableOn g {r : ℝ | |r| < 1 / Real.sqrt a} := by
      have hrpow_pos : IntegrableOn (fun r : ℝ => r ^ (-(2 / 5 : ℝ))) (Ioo 0 (1 / Real.sqrt a)) := by
        have h1 : IntervalIntegrable (fun r : ℝ => r ^ (-(2 / 5 : ℝ))) volume 0 (1 / Real.sqrt a) :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num)
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)).mp h1
      have hrpow_neg : IntegrableOn (fun r : ℝ => (-r) ^ (-(2 / 5 : ℝ))) (Ioo (-(1 / Real.sqrt a)) 0) := by
        have h1 := hrpow_pos.comp_neg
        convert h1 using 1
        ext r; simp [mem_Ioo]
      have hrpow_abs : IntegrableOn (fun r : ℝ => |r| ^ (-(2 / 5 : ℝ))) {r : ℝ | |r| < 1 / Real.sqrt a} := by
        have hsplit : {r : ℝ | |r| < 1 / Real.sqrt a} =ᵐ[volume]
            (Ioo (-(1 / Real.sqrt a)) 0 ∪ Ioo 0 (1 / Real.sqrt a) : Set ℝ) := by
          rw [ae_eq_set]
          have hsub1 : ({r : ℝ | |r| < 1 / Real.sqrt a} \ (Ioo (-(1 / Real.sqrt a)) 0 ∪ Ioo 0 (1 / Real.sqrt a))) ⊆ ({0} : Set ℝ) := by
            intro r ⟨hr1, hr2⟩
            simp only [mem_ofPred_eq, abs_lt] at hr1
            simp only [mem_union, mem_Ioo, not_or, not_and, not_lt] at hr2
            simp only [mem_singleton_iff]
            rcases lt_trichotomy r 0 with h | rfl | h
            · exact absurd h (not_lt.mpr (hr2.1 hr1.1))
            · rfl
            · exact absurd hr1.2 (not_lt.mpr (hr2.2 h))
          have hsub2 : ((Ioo (-(1 / Real.sqrt a)) 0 ∪ Ioo 0 (1 / Real.sqrt a)) \ {r : ℝ | |r| < 1 / Real.sqrt a}) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            have hpos : 0 < 1 / Real.sqrt a := by positivity
            rintro r ⟨hr_mem, hnot⟩
            simp only [mem_ofPred_eq, abs_lt, not_and, not_lt] at hnot
            rcases hr_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · linarith [hnot h1]
            · linarith [hnot (by linarith)]
          exact ⟨measure_mono_null hsub1 Real.volume_singleton, by rw [hsub2, measure_empty]⟩
        rw [integrableOn_congr_set_ae hsplit]
        refine IntegrableOn.union ?_ ?_
        · refine hrpow_neg.congr_fun (fun r hr => ?_) measurableSet_Ioo
          rw [abs_of_neg (mem_Ioo.mp hr).2]
        · refine hrpow_pos.congr_fun (fun r hr => ?_) measurableSet_Ioo
          rw [abs_of_pos (mem_Ioo.mp hr).1]
      have hdom : IntegrableOn (fun r : ℝ => (4 * a) ^ (1 / 5 : ℝ) * (Real.sqrt a) ^ (-(2 / 5 : ℝ)) * |r| ^ (-(2 / 5 : ℝ)))
          {r : ℝ | |r| < 1 / Real.sqrt a} :=
        hrpow_abs.const_mul _
      refine hdom.mono' haesm_g.restrict ?_
      have hne0 : ∀ᵐ r ∂(volume.restrict {r : ℝ | |r| < 1 / Real.sqrt a}), r ≠ 0 := by
        rw [ae_restrict_iff' (measurableSet_lt continuous_abs.measurable measurable_const)]
        filter_upwards [ae_iff.mpr (by rw [show {x : ℝ | ¬x ≠ 0} = {0} from by ext x; simp]; exact Real.volume_singleton)] with r hr _
        exact hr
      filter_upwards [hne0, ae_restrict_mem (measurableSet_lt continuous_abs.measurable measurable_const)] with r hr0 hr
      have hmin_eq : min 1 (Real.sqrt a * |r|) = Real.sqrt a * |r| := min_eq_right (by
        have hr' : |r| < 1 / Real.sqrt a := hr
        rw [lt_div_iff₀ hsqa] at hr'
        linarith [mul_comm (Real.sqrt a) |r|])
      have hle := hg_le r hr0
      have hexp_le : Real.exp (-(π / 5 * Real.sqrt a * |r|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      rw [hmin_eq, Real.mul_rpow hsqa.le (abs_nonneg r)] at hle
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _)]
      calc g r ≤ (4 * a) ^ (1 / 5 : ℝ) * Real.exp (-(π / 5 * Real.sqrt a * |r|)) *
            ((Real.sqrt a) ^ (-(2 / 5 : ℝ)) * |r| ^ (-(2 / 5 : ℝ))) := hle
        _ ≤ (4 * a) ^ (1 / 5 : ℝ) * 1 * ((Real.sqrt a) ^ (-(2 / 5 : ℝ)) * |r| ^ (-(2 / 5 : ℝ))) := by
            gcongr
        _ = (4 * a) ^ (1 / 5 : ℝ) * (Real.sqrt a) ^ (-(2 / 5 : ℝ)) * |r| ^ (-(2 / 5 : ℝ)) := by ring
    have hcomp : {r : ℝ | |r| < 1 / Real.sqrt a}ᶜ = {r : ℝ | 1 / Real.sqrt a ≤ |r|} := by
      ext r; simp [not_lt]
    rw [← integrableOn_univ, ← union_compl_self {r : ℝ | |r| < 1 / Real.sqrt a}, hcomp]
    exact h_core.union h_tail
  -- Now use Young's inequality `x^(1/6) * y^(5/6) ≤ (1/6) * x + (5/6) * y`
  have haesm_target : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Φ p| * H p.1 * H p.2) volume := by
    have hcont_H : Continuous H :=
      Real.continuous_cosh.comp (continuous_const.mul continuous_id)
    exact ((hΦ.cont.abs.mul (hcont_H.comp continuous_fst)).mul
      (hcont_H.comp continuous_snd)).aestronglyMeasurable
  set M₀ : ℝ := ∫ q : ℝ × ℝ, |Φ q|
  have hM₀_nn : 0 ≤ M₀ := integral_nonneg fun _ => abs_nonneg _
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (1 / 6 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) +
      (5 / 6 : ℝ) * M₀ * (g p.1 * g p.2)) volume := by
    refine (hΦ.int_M2.const_mul _).add ?_
    have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * g p.2) volume := by
      rw [Measure.volume_eq_prod]
      exact hg_int.mul_prod hg_int
    simpa [mul_assoc] using hprod.const_mul ((5 / 6 : ℝ) * M₀)
  refine hdom.mono' haesm_target ?_
  -- `p.1 ≠ 0` and `p.2 ≠ 0` a.e. on `ℝ × ℝ`
  have hae_ne0 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    have h1 : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
      rw [Measure.volume_eq_prod]
      have : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ univ := by ext p; simp
      rw [this, Measure.prod_prod, measure_singleton, zero_mul]
    have h2 : volume {p : ℝ × ℝ | p.2 = 0} = 0 := by
      rw [Measure.volume_eq_prod]
      have : {p : ℝ × ℝ | p.2 = 0} = univ ×ˢ ({0} : Set ℝ) := by ext p; simp
      rw [this, Measure.prod_prod, measure_singleton, mul_zero]
    have h12 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := ae_iff.mpr (by simpa using h1)
    have h22 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := ae_iff.mpr (by simpa using h2)
    exact h12.and h22
  filter_upwards [hae_ne0] with p ⟨hp1, hp2⟩
  have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr => by
    have h1 := spinV1_ge_inv_four_a_exp_min_sq ha r
    have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
    exact lt_of_lt_of_le (by positivity) h1
  have hV1_1 := hV1_pos p.1 hp1
  have hV1_2 := hV1_pos p.2 hp2
  have hΦ_le : |Φ p| ≤ M₀ := spinTestClass_abs_le_integral_abs hΦ p
  have h1 : |Φ p| * H p.1 * H p.2 ≤
      (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) * (M₀ * (g p.1 * g p.2)) ^ (5 / 6 : ℝ) := by
    have hpow_g : (g p.1 * g p.2) ^ (5 / 6 : ℝ) =
        (H p.1 / spinV1 a p.1 ^ (1 / 6 : ℝ)) * (H p.2 / spinV1 a p.2 ^ (1 / 6 : ℝ)) := by
      dsimp only [g, H]
      rw [Real.mul_rpow (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)) _)
        (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _)) _),
        ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)),
        ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _))]
      norm_num
    have hpow_M0 : |Φ p| ^ (5 / 6 : ℝ) ≤ M₀ ^ (5 / 6 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hΦ_le (by norm_num)
    have hpow_eq : |Φ p| * H p.1 * H p.2 =
        (|Φ p| * spinV1 a p.1 * spinV1 a p.2) ^ (1 / 6 : ℝ) *
          (|Φ p| ^ (5 / 6 : ℝ) * (g p.1 * g p.2) ^ (5 / 6 : ℝ)) := by
      rw [hpow_g, Real.mul_rpow (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le,
        Real.mul_rpow (abs_nonneg _) hV1_1.le]
      have hΦ_pow : |Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ) = |Φ p| := by
        by_cases h0 : |Φ p| = 0
        · simp [h0]
        · rw [← Real.rpow_add (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0))]
          norm_num
      calc |Φ p| * H p.1 * H p.2
          = |Φ p| * (spinV1 a p.1 ^ (1 / 6 : ℝ) * (H p.1 / spinV1 a p.1 ^ (1 / 6 : ℝ))) *
              (spinV1 a p.2 ^ (1 / 6 : ℝ) * (H p.2 / spinV1 a p.2 ^ (1 / 6 : ℝ))) := by
            field_simp [(Real.rpow_pos_of_pos hV1_1 _).ne', (Real.rpow_pos_of_pos hV1_2 _).ne']
        _ = (|Φ p| ^ (1 / 6 : ℝ) * |Φ p| ^ (5 / 6 : ℝ)) *
              (spinV1 a p.1 ^ (1 / 6 : ℝ) * (H p.1 / spinV1 a p.1 ^ (1 / 6 : ℝ))) *
              (spinV1 a p.2 ^ (1 / 6 : ℝ) * (H p.2 / spinV1 a p.2 ^ (1 / 6 : ℝ))) := by
            rw [hΦ_pow]
        _ = _ := by ring
    rw [hpow_eq, Real.mul_rpow hM₀_nn (mul_nonneg (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)) _)
      (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _)) _))]
    gcongr
  have hyoung := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 1 / 6)
    (by norm_num : (0 : ℝ) ≤ 5 / 6)
    (show (0 : ℝ) ≤ |Φ p| * spinV1 a p.1 * spinV1 a p.2 by
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le)
    (show (0 : ℝ) ≤ M₀ * (g p.1 * g p.2) by
      exact mul_nonneg hM₀_nn (mul_nonneg
        (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)) _)
        (Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _)) _)))
    (by norm_num)
  have h2 : |Φ p| * H p.1 * H p.2 ≤
      1 / 6 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) + 5 / 6 * M₀ * (g p.1 * g p.2) :=
    (h1.trans hyoung).trans_eq (by ring)
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le) (Real.cosh_pos _).le)]
  dsimp only [H] at h2
  exact h2

/-! ### Section 2: Chebyshev polynomial derivative bound -/

private lemma abs_sin_nat_mul_le (k : ℕ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    |Real.sin (k * θ)| ≤ k * Real.sin θ := by
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  induction k with
  | zero => simp
  | succ k ih =>
    have hadd : ((k + 1 : ℕ) : ℝ) * θ = k * θ + θ := by push_cast; ring
    rw [hadd, Real.sin_add]
    calc |Real.sin (k * θ) * Real.cos θ + Real.cos (k * θ) * Real.sin θ|
        ≤ |Real.sin (k * θ) * Real.cos θ| + |Real.cos (k * θ) * Real.sin θ| := abs_add_le _ _
      _ = |Real.sin (k * θ)| * |Real.cos θ| + |Real.cos (k * θ)| * |Real.sin θ| := by
          rw [abs_mul, abs_mul]
      _ ≤ (k * Real.sin θ) * 1 + 1 * Real.sin θ := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
          · rw [abs_of_pos hsin_pos]
      _ = ((k + 1 : ℕ) : ℝ) * Real.sin θ := by push_cast; ring

private lemma poly_chebyshev_expansion (N : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree < N) :
    ∃ c : ℕ → ℝ, ∀ x : ℝ, P.eval x = ∑ k ∈ Finset.range N, c k * (Polynomial.Chebyshev.T ℝ k).eval x := by
  induction N generalizing P with
  | zero => simp at hdeg
  | succ N ih =>
    by_cases hlt : P.natDegree < N
    · obtain ⟨c, hc⟩ := ih P hlt
      refine ⟨fun k => if k < N then c k else 0, fun x => ?_⟩
      rw [Finset.sum_range_succ]
      simp only [lt_irrefl, ↓reduceIte, zero_mul, add_zero]
      rw [hc x]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp [hk]
    · have heq : P.natDegree = N := by omega
      cases N with
      | zero =>
        refine ⟨fun _ => P.coeff 0, fun x => ?_⟩
        rw [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero,
          Polynomial.Chebyshev.T_zero, Polynomial.eval_one, mul_one]
        simpa [Polynomial.eval_C] using
          congrArg (Polynomial.eval x) (Polynomial.eq_C_of_natDegree_eq_zero heq)
      | succ M =>
        set N := M + 1
        have hT_deg : (Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree = N :=
          Polynomial.Chebyshev.natDegree_T ℝ N
        have hT_lc : (Polynomial.Chebyshev.T ℝ (N : ℤ)).leadingCoeff ≠ 0 := by
          rw [Polynomial.leadingCoeff_ne_zero]
          intro h0
          have h1 : (Polynomial.Chebyshev.T ℝ (N : ℤ)).eval (Real.cos 0) = Real.cos ((N : ℤ) * 0) :=
            Polynomial.Chebyshev.T_real_cos 0 (N : ℤ)
          simp [h0] at h1
        set α : ℝ := P.leadingCoeff / (Polynomial.Chebyshev.T ℝ (N : ℤ)).leadingCoeff
        set Q : Polynomial ℝ := P - Polynomial.C α * Polynomial.Chebyshev.T ℝ (N : ℤ)
        have hQ_deg : Q.natDegree < N := by
          by_cases hQ0 : Q = 0
          · rw [hQ0, Polynomial.natDegree_zero]
            exact Nat.succ_pos M
          · have hsub : Q.natDegree ≤ max P.natDegree (Polynomial.C α * Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree :=
              Polynomial.natDegree_sub_le _ _
            have hP_ne : P ≠ 0 := by
              intro hP0; rw [hP0, Polynomial.natDegree_zero] at heq; omega
            have hα_ne : α ≠ 0 := by
              dsimp [α]; exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP_ne) hT_lc
            have hCT_deg : (Polynomial.C α * Polynomial.Chebyshev.T ℝ (N : ℤ)).natDegree = N := by
              rw [Polynomial.natDegree_C_mul hα_ne, hT_deg]
            have hCT_lc : (Polynomial.C α * Polynomial.Chebyshev.T ℝ (N : ℤ)).leadingCoeff = P.leadingCoeff := by
              rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
              dsimp [α]; exact div_mul_cancel₀ _ hT_lc
            have hlt_or_eq := lt_or_eq_of_le (hsub.trans (max_le heq.le hCT_deg.le))
            rcases hlt_or_eq with h | h
            · exact h
            · exfalso
              have hcoeff : Q.coeff N = 0 := by
                dsimp only [Q]
                rw [Polynomial.coeff_sub,
                  show P.coeff N = P.leadingCoeff from by rw [← heq, Polynomial.leadingCoeff],
                  Polynomial.coeff_C_mul,
                  show (Polynomial.Chebyshev.T ℝ (N : ℤ)).coeff N =
                    (Polynomial.Chebyshev.T ℝ (N : ℤ)).leadingCoeff from by
                    rw [Polynomial.leadingCoeff]; nth_rw 2 [← hT_deg]]
                dsimp only [α]
                rw [div_mul_cancel₀ _ hT_lc, sub_self]
              have hlc_Q : Q.leadingCoeff = 0 := by
                rw [Polynomial.leadingCoeff, h]; exact hcoeff
              exact hQ0 (Polynomial.leadingCoeff_eq_zero.mp hlc_Q)
        obtain ⟨c, hc⟩ := ih Q hQ_deg
        refine ⟨fun k => if k = N then α else c k, fun x => ?_⟩
        rw [Finset.sum_range_succ]
        dsimp only
        rw [if_pos rfl]
        have hsum : ∑ k ∈ Finset.range N, (if k = N then α else c k) * (Polynomial.Chebyshev.T ℝ k).eval x =
            Q.eval x := by
          rw [hc x]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          simp [hk.ne]
        rw [hsum]
        dsimp [Q]
        simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]

private lemma integral_cos_nat_mul_pi (m : ℕ) (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((m : ℝ) * θ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hd : ∀ θ ∈ uIcc (0 : ℝ) π,
      HasDerivAt (fun t : ℝ => Real.sin ((m : ℝ) * t) / m) (Real.cos ((m : ℝ) * θ)) θ := by
    intro θ _
    have h1 := (Real.hasDerivAt_sin ((m : ℝ) * θ)).comp θ ((hasDerivAt_id θ).const_mul (m : ℝ))
    exact (h1.div_const (m : ℝ)).congr_deriv (by field_simp [hm'])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Real.continuous_cos.comp (continuous_const.mul continuous_id) |>.intervalIntegrable 0 π)]
  simp [Real.sin_nat_mul_pi]

private lemma integral_cos_mul_cos_eq (j k : ℕ) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ) =
      if j = k then π / 2 else 0 := by
  have hprod : ∀ θ : ℝ, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ) =
      (Real.cos (((j + k : ℕ) : ℝ) * θ) + Real.cos ((Int.natAbs ((j : ℤ) - k) : ℝ) * θ)) / 2 := by
    intro θ
    have h1 : Real.cos (((j + k : ℕ) : ℝ) * θ) = Real.cos ((j : ℝ) * θ + (k : ℝ) * θ) := by
      congr 1; push_cast; ring
    have h2 : Real.cos ((Int.natAbs ((j : ℤ) - k) : ℝ) * θ) = Real.cos ((j : ℝ) * θ - (k : ℝ) * θ) := by
      rcases le_total j k with hjk | hjk
      · have : Int.natAbs ((j : ℤ) - k) = k - j := by omega
        rw [this, ← Real.cos_neg]; congr 1
        have : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by
          rw [Nat.cast_sub hjk]
        rw [this]; ring
      · have : Int.natAbs ((j : ℤ) - k) = j - k := by omega
        rw [this]; congr 1
        have : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by
          rw [Nat.cast_sub hjk]
        rw [this]; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hprod]
  have hcont1 : Continuous (fun θ : ℝ => Real.cos (((j + k : ℕ) : ℝ) * θ)) := by fun_prop
  have hcont2 : Continuous (fun θ : ℝ => Real.cos ((Int.natAbs ((j : ℤ) - k) : ℝ) * θ)) := by fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (hcont1.intervalIntegrable 0 π) (hcont2.intervalIntegrable 0 π)]
  have hne1 : j + k ≠ 0 := by omega
  rw [integral_cos_nat_mul_pi (j + k) hne1, zero_add]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hne2 : Int.natAbs ((j : ℤ) - k) ≠ 0 := by omega
    rw [if_neg hjk, integral_cos_nat_mul_pi _ hne2, zero_div]

private lemma poly_deriv_le_chebyshev {N : ℕ} (P : Polynomial ℝ) (hdeg : P.natDegree < N)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |P.eval x| ≤ M) :
    ∀ x ∈ Icc (-1 : ℝ) 1, |P.derivative.eval x| ≤ 2 * (N : ℝ) ^ 3 * M := by
  obtain ⟨c, hc⟩ := poly_chebyshev_expansion N P hdeg
  have hc_bound : ∀ k ∈ Finset.range N, k ≠ 0 → |c k| ≤ 2 * M := by
    intro k hk hk0
    have hcos_eq : ∀ θ : ℝ, P.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ) =
        ∑ j ∈ Finset.range N, c j * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) := by
      intro θ
      rw [hc (Real.cos θ), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hT : (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) = Real.cos ((j : ℝ) * θ) := by
        simp [Polynomial.Chebyshev.T_real_cos]
      rw [hT]; ring
    have hint_eq : ∫ θ in (0 : ℝ)..π, P.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ) = c k * (π / 2) := by
      simp_rw [hcos_eq]
      have hsum_int : ∀ s : Finset ℕ,
          ∫ θ in (0 : ℝ)..π, ∑ j ∈ s, c j * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
            ∑ j ∈ s, ∫ θ in (0 : ℝ)..π, c j * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ihs =>
          simp_rw [Finset.sum_insert ha]
          rw [intervalIntegral.integral_add _ _, ihs]
          · exact (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
              (Real.continuous_cos.comp (continuous_const.mul continuous_id))).const_mul _).intervalIntegrable 0 π
          · exact (by fun_prop : Continuous fun θ : ℝ => ∑ j ∈ s,
              c j * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ))).intervalIntegrable 0 π
      rw [hsum_int]
      have hterm : ∀ j ∈ Finset.range N,
          ∫ θ in (0 : ℝ)..π, c j * (Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
            if j = k then c k * (π / 2) else 0 := by
        intro j _
        rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos_eq j k hk0]
        split_ifs with hjk
        · subst hjk; rfl
        · ring
      rw [Finset.sum_congr rfl hterm]
      simp [hk]
    have hint_le : |∫ θ in (0 : ℝ)..π, P.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ)| ≤ π * M := by
      calc |∫ θ in (0 : ℝ)..π, P.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ)|
          ≤ ∫ θ in (0 : ℝ)..π, |P.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ)| :=
            intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le
        _ ≤ ∫ _ in (0 : ℝ)..π, M := by
            refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ (intervalIntegrable_const) fun θ _ => ?_
            · exact ((P.continuous.comp Real.continuous_cos).mul
                (Real.continuous_cos.comp (continuous_const.mul continuous_id))).abs.intervalIntegrable 0 π
            · rw [abs_mul]
              have h1 : |P.eval (Real.cos θ)| ≤ M :=
                hbound (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
              have h2 : |Real.cos ((k : ℝ) * θ)| ≤ 1 := Real.abs_cos_le_one _
              calc |P.eval (Real.cos θ)| * |Real.cos ((k : ℝ) * θ)| ≤ M * 1 :=
                  mul_le_mul h1 h2 (abs_nonneg _) hM
                _ = M := mul_one M
        _ = π * M := by simp [smul_eq_mul]
    rw [hint_eq, abs_mul, abs_of_pos (half_pos Real.pi_pos)] at hint_le
    nlinarith [Real.pi_pos]
  -- Now bound `|P.derivative.eval (cos θ)|` for `θ ∈ Ioo 0 π`
  have hderiv_Ioo : ∀ x ∈ Ioo (-1 : ℝ) 1, |P.derivative.eval x| ≤ 2 * (N : ℝ) ^ 3 * M := by
    intro x hx
    set θ : ℝ := Real.arccos x
    have hθ_Ioo : θ ∈ Ioo 0 π := by
      refine ⟨Real.arccos_pos.mpr hx.2, Real.arccos_lt_pi.mpr hx.1⟩
    have hx_cos : Real.cos θ = x := Real.cos_arccos hx.1.le hx.2.le
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_Ioo.1 hθ_Ioo.2
    -- Differentiate `fun t => P.eval (cos t)` and `fun t => ∑ k ∈ range N, c k * cos (k * t)` at `θ`
    have hd1 : HasDerivAt (fun t : ℝ => P.eval (Real.cos t))
        (P.derivative.eval (Real.cos θ) * (-Real.sin θ)) θ := by
      exact (P.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
    have hd2 : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range N, c k * Real.cos ((k : ℝ) * t))
        (∑ k ∈ Finset.range N, c k * (-((k : ℝ) * Real.sin ((k : ℝ) * θ)))) θ := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have hc1 := (Real.hasDerivAt_cos ((k : ℝ) * θ)).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))
      exact (hc1.const_mul (c k)).congr_deriv (by ring)
    have hfun_eq : (fun t : ℝ => P.eval (Real.cos t)) =
        fun t : ℝ => ∑ k ∈ Finset.range N, c k * Real.cos ((k : ℝ) * t) := by
      ext t
      rw [hc (Real.cos t)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hT : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos t) = Real.cos ((k : ℝ) * t) := by
        simpa using Polynomial.Chebyshev.T_real_cos t (k : ℤ)
      rw [hT]
    rw [hfun_eq] at hd1
    have hderiv_eq := hd1.unique hd2
    rw [hx_cos] at hderiv_eq
    have hsin_eq : |P.derivative.eval x| * Real.sin θ ≤ 2 * (N : ℝ) ^ 3 * M * Real.sin θ := by
      have h1 : P.derivative.eval x * (-Real.sin θ) =
          -(∑ k ∈ Finset.range N, c k * (k : ℝ) * Real.sin ((k : ℝ) * θ)) := by
        rw [hderiv_eq]; simp [Finset.sum_neg_distrib, mul_assoc]
      have h2 : |P.derivative.eval x| * Real.sin θ =
          |∑ k ∈ Finset.range N, c k * (k : ℝ) * Real.sin ((k : ℝ) * θ)| := by
        calc |P.derivative.eval x| * Real.sin θ
            = |P.derivative.eval x * (-Real.sin θ)| := by
              rw [abs_mul, abs_neg, abs_of_pos hsin_pos]
          _ = |-(∑ k ∈ Finset.range N, c k * (k : ℝ) * Real.sin ((k : ℝ) * θ))| := by rw [h1]
          _ = |∑ k ∈ Finset.range N, c k * (k : ℝ) * Real.sin ((k : ℝ) * θ)| := abs_neg _
      rw [h2]
      calc |∑ k ∈ Finset.range N, c k * (k : ℝ) * Real.sin ((k : ℝ) * θ)|
          ≤ ∑ k ∈ Finset.range N, |c k * (k : ℝ) * Real.sin ((k : ℝ) * θ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range N, (2 * M) * (k : ℝ) * ((k : ℝ) * Real.sin θ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            by_cases hk0 : k = 0
            · subst hk0; simp
            · rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
              have hck := hc_bound k hk hk0
              have hsin := abs_sin_nat_mul_le k hθ_Ioo
              exact mul_le_mul (mul_le_mul_of_nonneg_right hck (Nat.cast_nonneg k)) hsin
                (abs_nonneg _) (by positivity)
        _ = (∑ k ∈ Finset.range N, (k : ℝ) ^ 2) * (2 * M * Real.sin θ) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ => by ring
        _ ≤ ((N : ℝ) ^ 3) * (2 * M * Real.sin θ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            calc ∑ k ∈ Finset.range N, (k : ℝ) ^ 2
                ≤ ∑ _ ∈ Finset.range N, (N : ℝ) ^ 2 := by
                  refine Finset.sum_le_sum fun k hk => ?_
                  rw [Finset.mem_range] at hk
                  have : (k : ℝ) ≤ N := Nat.cast_le.mpr hk.le
                  nlinarith
              _ = (N : ℝ) ^ 3 := by simp [Finset.sum_const, nsmul_eq_mul]; ring
        _ = 2 * (N : ℝ) ^ 3 * M * Real.sin θ := by ring
    exact le_of_mul_le_mul_right hsin_eq hsin_pos
  -- Extend from `Ioo (-1) 1` to `Icc (-1) 1` by continuity
  intro x hx
  have hcl : x ∈ closure (Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact hx
  exact closure_minimal (fun y hy => hderiv_Ioo y hy)
    (isClosed_Iic.preimage P.derivative.continuous.abs) hcl

private lemma poly_deriv_le_chebyshev_rescaled {N : ℕ} (P : Polynomial ℝ) (hdeg : P.natDegree < N)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hbound : ∀ x ∈ Icc (-ρ) ρ, |P.eval x| ≤ M) :
    ∀ x ∈ Icc (-ρ) ρ, |P.derivative.eval x| ≤ (2 * (N : ℝ) ^ 3 / ρ) * M := by
  set Q : Polynomial ℝ := P.comp (Polynomial.C ρ * Polynomial.X)
  have hQ_deg : Q.natDegree < N := by
    have h1 : Q.natDegree ≤ P.natDegree * (Polynomial.C ρ * Polynomial.X).natDegree :=
      Polynomial.natDegree_comp_le
    have h2 : (Polynomial.C ρ * Polynomial.X).natDegree ≤ 1 := by
      have := Polynomial.natDegree_mul_le (p := Polynomial.C ρ) (q := Polynomial.X)
      simpa using this
    nlinarith
  have hQ_bound : ∀ y ∈ Icc (-1 : ℝ) 1, |Q.eval y| ≤ M := by
    intro y hy
    have hpy : ρ * y ∈ Icc (-ρ) ρ := ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
    simpa [Q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using
      hbound (ρ * y) hpy
  have hQ_deriv := poly_deriv_le_chebyshev Q hQ_deg hM hQ_bound
  intro x hx
  have hy : x / ρ ∈ Icc (-1 : ℝ) 1 := ⟨by rw [le_div_iff₀ hρ]; linarith [hx.1], by rw [div_le_iff₀ hρ]; linarith [hx.2]⟩
  have hQd : Q.derivative.eval (x / ρ) = ρ * P.derivative.eval x := by
    dsimp [Q]
    rw [Polynomial.derivative_comp, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_div_cancel₀ _ hρ.ne',
      Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      zero_mul, zero_add, mul_one, Polynomial.eval_C, mul_comm]
  have h1 := hQ_deriv (x / ρ) hy
  rw [hQd, abs_mul, abs_of_pos hρ] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀' hρ]
  linarith

private lemma intervalIntegral_sq_ge_length_cube {a b : ℝ} (hab : a ≤ b) :
    (b - a) ^ 3 / 12 ≤ ∫ x in Icc a b, x ^ 2 := by
  have h1 : ∫ x in Icc a b, x ^ 2 = ∫ x in a..b, x ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [h1]
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun t : ℝ => t ^ 3 / 3) (x ^ 2) x := fun x _ => by
    have := (hasDerivAt_pow 3 x).div_const (3 : ℝ)
    convert this using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((continuous_pow 2).intervalIntegrable a b)]
  have hid : (b ^ 3 / 3 - a ^ 3 / 3) - (b - a) ^ 3 / 12 = (b - a) * (a + b) ^ 2 / 4 := by ring
  have hnn : 0 ≤ (b - a) * (a + b) ^ 2 / 4 := by
    have : 0 ≤ b - a := sub_nonneg.mpr hab
    positivity
  linarith

private lemma poly_L1_le_L1_sq {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℝ) (hdeg : P.natDegree < N)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ x in Icc (-ρ) ρ, |P.eval x| ≤
      3072 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2 := by
  have hne : (Icc (-ρ) ρ).Nonempty := ⟨0, by linarith, by linarith⟩
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := isCompact_Icc.exists_isMaxOn hne P.continuous.abs.continuousOn
  set M : ℝ := |P.eval x₀|
  have hM_nn : 0 ≤ M := abs_nonneg _
  have hbound : ∀ x ∈ Icc (-ρ) ρ, |P.eval x| ≤ M := fun x hx => hx₀_max hx
  by_cases hM0 : M = 0
  · have hzero : ∀ x ∈ Icc (-ρ) ρ, |P.eval x| = 0 := fun x hx =>
      le_antisymm (hbound x hx |>.trans_eq hM0) (abs_nonneg _)
    have hlhs : ∫ x in Icc (-ρ) ρ, |P.eval x| = 0 := by
      rw [MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero hzero]
    have hrhs : 0 ≤ 3072 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2 := by
      refine mul_nonneg (by positivity) (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun x _ => by positivity)
    linarith
  · have hM_pos : 0 < M := lt_of_le_of_ne hM_nn (Ne.symm hM0)
    have hderiv_bd := poly_deriv_le_chebyshev_rescaled P hdeg hρ hM_nn hbound
    set δ : ℝ := ρ / (4 * (N : ℝ) ^ 3)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hδ_pos : 0 < δ := by positivity
    have hδ_le : δ ≤ ρ := by
      dsimp [δ]
      refine div_le_self hρ.le ?_
      have : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
      linarith
    -- Pick a subinterval `Icc a₀ b₀ ⊆ Icc (-ρ) ρ` of length `δ` containing `x₀`
    have hsub : ∃ a₀ b₀ : ℝ, a₀ ≤ b₀ ∧ b₀ - a₀ = δ ∧ Icc a₀ b₀ ⊆ Icc (-ρ) ρ ∧
        ∀ x ∈ Icc a₀ b₀, |x - x₀| ≤ δ := by
      rcases le_total x₀ 0 with hx₀ | hx₀
      · refine ⟨x₀, x₀ + δ, by linarith, by ring, fun x hx => ?_, fun x hx => ?_⟩
        · exact ⟨by linarith [hx.1, hx₀_mem.1], by linarith [hx.2, hx₀, hδ_le]⟩
        · rw [abs_le]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · refine ⟨x₀ - δ, x₀, by linarith, by ring, fun x hx => ?_, fun x hx => ?_⟩
        · exact ⟨by linarith [hx.1, hx₀, hδ_le], by linarith [hx.2, hx₀_mem.2]⟩
        · rw [abs_le]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨a₀, b₀, hab, hlen, hsub_Icc, hdist⟩ := hsub
    -- On `Icc a₀ b₀`, `M / 2 ≤ |P.eval x|` by MVT
    have hhalf : ∀ x ∈ Icc a₀ b₀, M / 2 ≤ |P.eval x| := by
      intro x hx
      have hdiff : |P.eval x - P.eval x₀| ≤ (2 * (N : ℝ) ^ 3 / ρ) * M * |x - x₀| := by
        rcases eq_or_ne x x₀ with rfl | hne
        · simp
        · rcases lt_or_gt_of_ne hne with hlt | hlt
          · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => P.eval t) (fun t => P.derivative.eval t)
              hlt P.continuous.continuousOn (fun t _ => P.hasDerivAt t)
            have hc_mem : c ∈ Icc (-ρ) ρ := ⟨by linarith [(hsub_Icc hx).1, hc.1], by linarith [hx₀_mem.2, hc.2]⟩
            have hc_bd := hderiv_bd c hc_mem
            have heq : P.eval x₀ - P.eval x = P.derivative.eval c * (x₀ - x) := by
              rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
            rw [← abs_neg (P.eval x - P.eval x₀), neg_sub, heq, abs_mul, abs_sub_comm x₀ x]
            exact mul_le_mul_of_nonneg_right hc_bd (abs_nonneg _)
          · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => P.eval t) (fun t => P.derivative.eval t)
              hlt P.continuous.continuousOn (fun t _ => P.hasDerivAt t)
            have hc_mem : c ∈ Icc (-ρ) ρ := ⟨by linarith [hx₀_mem.1, hc.1], by linarith [(hsub_Icc hx).2, hc.2]⟩
            have hc_bd := hderiv_bd c hc_mem
            have heq : P.eval x - P.eval x₀ = P.derivative.eval c * (x - x₀) := by
              rw [hslope, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
            rw [heq, abs_mul]
            exact mul_le_mul_of_nonneg_right hc_bd (abs_nonneg _)
      have h1 : |P.eval x - P.eval x₀| ≤ M / 2 := by
        calc |P.eval x - P.eval x₀|
            ≤ (2 * (N : ℝ) ^ 3 / ρ) * M * |x - x₀| := hdiff
          _ ≤ (2 * (N : ℝ) ^ 3 / ρ) * M * δ :=
              mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
          _ = M / 2 := by dsimp [δ]; field_simp [hρ.ne', hN1]; ring
      have htri : M - |P.eval x| ≤ |P.eval x₀ - P.eval x| := abs_sub_abs_le_abs_sub _ _
      rw [abs_sub_comm] at htri
      linarith
    have hsq_int : M / 2 * (δ ^ 3 / 12) ≤ ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2 := by
      have hint_Icc : IntegrableOn (fun x : ℝ => |P.eval x| * x ^ 2) (Icc (-ρ) ρ) :=
        (P.continuous.abs.mul (continuous_pow 2)).continuousOn.integrableOn_Icc
      have hmono1 : ∫ x in Icc a₀ b₀, (M / 2) * x ^ 2 ≤ ∫ x in Icc a₀ b₀, |P.eval x| * x ^ 2 := by
        refine MeasureTheory.setIntegral_mono_on
          ((continuous_pow 2).const_mul (M / 2) |>.continuousOn.integrableOn_Icc)
          (hint_Icc.mono_set hsub_Icc) measurableSet_Icc fun x hx => ?_
        exact mul_le_mul_of_nonneg_right (hhalf x hx) (sq_nonneg x)
      have hmono2 : ∫ x in Icc a₀ b₀, |P.eval x| * x ^ 2 ≤ ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2 :=
        MeasureTheory.setIntegral_mono_set hint_Icc
          (Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (sq_nonneg x))
          (Eventually.of_forall fun x hx => hsub_Icc hx)
      have hsq := intervalIntegral_sq_ge_length_cube hab
      rw [hlen] at hsq
      have hconst : ∫ x in Icc a₀ b₀, (M / 2) * x ^ 2 = (M / 2) * ∫ x in Icc a₀ b₀, x ^ 2 :=
        MeasureTheory.integral_const_mul _ _
      rw [hconst] at hmono1
      have hle := (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ M / 2)).trans (hmono1.trans hmono2)
      exact hle
    have hL1_le : ∫ x in Icc (-ρ) ρ, |P.eval x| ≤ 2 * ρ * M := by
      have h1 : ∫ x in Icc (-ρ) ρ, |P.eval x| ≤ ∫ _ in Icc (-ρ) ρ, M :=
        MeasureTheory.setIntegral_mono_on P.continuous.abs.continuousOn.integrableOn_Icc
          (integrableOn_const (hs := measure_Icc_lt_top.ne)) measurableSet_Icc hbound
      rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h1
      linarith
    have hcomb : (M / 2) * (δ ^ 3 / 12) = M * ρ ^ 3 / (1536 * (N : ℝ) ^ 9) := by
      dsimp [δ]; ring
    rw [hcomb] at hsq_int
    calc ∫ x in Icc (-ρ) ρ, |P.eval x|
        ≤ 2 * ρ * M := hL1_le
      _ = 3072 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * (M * ρ ^ 3 / (1536 * (N : ℝ) ^ 9)) := by
          field_simp [hρ.ne', hN1]; ring
      _ ≤ 3072 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2 := by
          gcongr

/-! ### Section 3: Transverse slice analyticity, Taylor truncation, and `integrable_spinITheta` -/

lemma norm_complex_cos_le_cosh (w : ℂ) : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
  rw [Complex.cos, Real.cosh_eq]
  have h1 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  calc ‖(Complex.exp (w * I) + Complex.exp (-w * I)) / 2‖
      = ‖Complex.exp (w * I) + Complex.exp (-w * I)‖ / 2 := by
        rw [norm_div]; norm_num
    _ ≤ (‖Complex.exp (w * I)‖ + ‖Complex.exp (-w * I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ = (Real.exp w.im + Real.exp (-w.im)) / 2 := by rw [h1, h2]; ring

private lemma norm_complex_sin_le_cosh (w : ℂ) : ‖Complex.sin w‖ ≤ Real.cosh w.im := by
  rw [Complex.sin, Real.cosh_eq]
  have h1 : ‖Complex.exp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have h2 : ‖Complex.exp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  calc ‖(Complex.exp (-w * I) - Complex.exp (w * I)) * I / 2‖
      = ‖Complex.exp (-w * I) - Complex.exp (w * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; norm_num
    _ ≤ (‖Complex.exp (-w * I)‖ + ‖Complex.exp (w * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ = (Real.exp w.im + Real.exp (-w.im)) / 2 := by rw [h1, h2]

noncomputable def spinSliceC (Φ : ℝ × ℝ → ℝ) (ξ : ℝ) (z : ℂ) : ℂ :=
  -(∫ p : ℝ × ℝ, (Φ p : ℂ) *
    Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) * Complex.cos (2 * π * (p.2 : ℂ) * z))

lemma spinSliceC_ofReal {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (ξ x : ℝ) :
    spinSliceC Φ ξ (x : ℂ) = ((Φ (ξ, x) : ℝ) : ℂ) := by
  unfold spinSliceC
  let w : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![ξ, x]
  have hfo := congrFun hΦ.fourier_odd w
  simp only [Real.fourier_eq, Pi.neg_apply, spinToEuc] at hfo
  have hw0 : w 0 = ξ := rfl
  have hw1 : w 1 = x := rfl
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have hmpe : Measure.map e (volume : Measure (EuclideanSpace ℝ (Fin 2))) = volume :=
    ((volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp
      (PiLp.volume_preserving_ofLp (Fin 2))).map_eq
  have hI_eq : ∫ v : EuclideanSpace ℝ (Fin 2), 𝐞 (-⟪v, w⟫) • ((Φ (v 0, v 1) : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, Complex.exp (-2 * π * I * ((p.1 : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ))) * (Φ p : ℂ) := by
    have h1 := integral_map_equiv (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) e
      (fun p : ℝ × ℝ => Complex.exp (-2 * π * I * ((p.1 : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ))) * (Φ p : ℂ))
    rw [hmpe] at h1
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    have hev : e v = (v 0, v 1) := rfl
    rw [hev, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    congr 1
    have hinner : ⟪v, w⟫ = v 0 * ξ + v 1 * x := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
      simp [hw0, hw1, mul_comm]
    rw [hinner]
    congr 1; push_cast; ring
  rw [hI_eq] at hfo
  let f : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (-2 * π * I * ((p.1 : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ))) * (Φ p : ℂ)
  have hf_int : Integrable f volume := by
    refine (hΦ.int.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ => Complex.exp (-2 * π * I *
          ((p.1 : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ)))) := by fun_prop
      exact (h2.mul h1).aestronglyMeasurable
    · dsimp [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hre : (-2 * π * I * ((p.1 : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im]
      rw [Complex.norm_exp, hre, Real.exp_zero, one_mul]
  have href1 : ∫ p : ℝ × ℝ, f (-p.1, p.2) = ∫ p : ℝ × ℝ, f p := by
    let s1 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
    have hm1 : Measure.map s1 (volume : Measure (ℝ × ℝ)) = volume := by
      have hs : (s1 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) id := rfl
      rw [hs, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_id,
        Measure.map_neg_eq_self, Measure.map_id]
    have h1 := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) s1 f
    rw [hm1] at h1
    exact h1.symm
  have href2 : ∫ p : ℝ × ℝ, f (p.1, -p.2) = ∫ p : ℝ × ℝ, f p := by
    let s2 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hm2 : Measure.map s2 (volume : Measure (ℝ × ℝ)) = volume := by
      have hs : (s2 : ℝ × ℝ → ℝ × ℝ) = Prod.map id (-·) := rfl
      rw [hs, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id measurable_neg,
        Measure.map_id, Measure.map_neg_eq_self]
    have h2 := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) s2 f
    rw [hm2] at h2
    exact h2.symm
  have href3 : ∫ p : ℝ × ℝ, f (-p.1, -p.2) = ∫ p : ℝ × ℝ, f p := by
    let s3 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hm3 : Measure.map s3 (volume : Measure (ℝ × ℝ)) = volume := by
      have hs : (s3 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) (-·) := rfl
      rw [hs, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_neg,
        Measure.map_neg_eq_self]
    have h3 := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) s3 f
    rw [hm3] at h3
    exact h3.symm
  have havg : 4 * ∫ p : ℝ × ℝ, f p =
      ∫ p : ℝ × ℝ, (f p + f (-p.1, p.2) + f (p.1, -p.2) + f (-p.1, -p.2)) := by
    have hf1 : Integrable (fun p : ℝ × ℝ => f (-p.1, p.2)) volume := by
      let s1 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
      have hm1 : Measure.map s1 (volume : Measure (ℝ × ℝ)) = volume := by
        have hs : (s1 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) id := rfl
        rw [hs, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_id,
          Measure.map_neg_eq_self, Measure.map_id]
      exact (⟨s1.measurable, hm1⟩ : MeasurePreserving s1 volume volume).integrable_comp_emb
        s1.measurableEmbedding |>.mpr hf_int
    have hf2 : Integrable (fun p : ℝ × ℝ => f (p.1, -p.2)) volume := by
      let s2 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
      have hm2 : Measure.map s2 (volume : Measure (ℝ × ℝ)) = volume := by
        have hs : (s2 : ℝ × ℝ → ℝ × ℝ) = Prod.map id (-·) := rfl
        rw [hs, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_id measurable_neg,
          Measure.map_id, Measure.map_neg_eq_self]
      exact (⟨s2.measurable, hm2⟩ : MeasurePreserving s2 volume volume).integrable_comp_emb
        s2.measurableEmbedding |>.mpr hf_int
    have hf3 : Integrable (fun p : ℝ × ℝ => f (-p.1, -p.2)) volume := by
      let s3 : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
      have hm3 : Measure.map s3 (volume : Measure (ℝ × ℝ)) = volume := by
        have hs : (s3 : ℝ × ℝ → ℝ × ℝ) = Prod.map (-·) (-·) := rfl
        rw [hs, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ measurable_neg measurable_neg,
          Measure.map_neg_eq_self]
      exact (⟨s3.measurable, hm3⟩ : MeasurePreserving s3 volume volume).integrable_comp_emb
        s3.measurableEmbedding |>.mpr hf_int
    have hf01 : Integrable (fun p : ℝ × ℝ => f p + f (-p.1, p.2)) volume := hf_int.add hf1
    have hf012 : Integrable (fun p : ℝ × ℝ => f p + f (-p.1, p.2) + f (p.1, -p.2)) volume :=
      hf01.add hf2
    rw [integral_add hf012 hf3, integral_add hf01 hf2, integral_add hf_int hf1,
      href1, href2, href3]
    ring
  have hpt : ∀ p : ℝ × ℝ, f p + f (-p.1, p.2) + f (p.1, -p.2) + f (-p.1, -p.2) =
      4 * ((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
        Complex.cos (2 * π * (p.2 : ℂ) * (x : ℂ))) := by
    intro p
    dsimp [f]
    rw [hΦ.d4_inv.1 p.1 p.2, hΦ.d4_inv.2.1 p.1 p.2, show Φ (-p.1, -p.2) = Φ (p.1, p.2) by
      rw [hΦ.d4_inv.1, hΦ.d4_inv.2.1]]
    set A : ℂ := 2 * π * (p.1 : ℂ) * (ξ : ℂ)
    set B : ℂ := 2 * π * (p.2 : ℂ) * (x : ℂ)
    have hcosA : Complex.cos A = (Complex.exp (I * A) + Complex.exp (-(I * A))) / 2 := by
      rw [Complex.cos]; congr 2 <;> ring
    have hcosB : Complex.cos B = (Complex.exp (I * B) + Complex.exp (-(I * B))) / 2 := by
      rw [Complex.cos]; congr 2 <;> ring
    have he1 : -2 * π * I * ((p.1 : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ)) = -(I * A) + -(I * B) := by
      dsimp [A, B]; ring
    have he2 : -2 * π * I * (((-p.1 : ℝ) : ℂ) * (ξ : ℂ) + (p.2 : ℂ) * (x : ℂ)) = I * A + -(I * B) := by
      dsimp [A, B]; push_cast; ring
    have he3 : -2 * π * I * ((p.1 : ℂ) * (ξ : ℂ) + ((-p.2 : ℝ) : ℂ) * (x : ℂ)) = -(I * A) + I * B := by
      dsimp [A, B]; push_cast; ring
    have he4 : -2 * π * I * (((-p.1 : ℝ) : ℂ) * (ξ : ℂ) + ((-p.2 : ℝ) : ℂ) * (x : ℂ)) = I * A + I * B := by
      dsimp [A, B]; push_cast; ring
    rw [he1, he2, he3, he4, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
      hcosA, hcosB]
    ring
  simp_rw [hpt, integral_const_mul] at havg
  have h4 : ∫ p : ℝ × ℝ, f p = ∫ p : ℝ × ℝ, (Φ p : ℂ) *
      Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) * Complex.cos (2 * π * (p.2 : ℂ) * (x : ℂ)) := by
    apply mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0)
    exact havg
  have hfo' : (∫ p : ℝ × ℝ, f p) = -((Φ (ξ, x) : ℝ) : ℂ) := by
    simpa [f, hw0, hw1] using hfo
  rw [h4] at hfo'
  rw [hfo', neg_neg]

private lemma spinSliceC_differentiableOn_and_bound {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (ξ : ℝ) :
    let r₀ : ℝ := Real.sqrt a / 24
    DiffContOnCl ℂ (spinSliceC Φ ξ) (Metric.ball 0 r₀) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r₀, ‖spinSliceC Φ ξ z‖ ≤ spinITheta a (1 / 24) Φ := by
  intro r₀
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hr₀ : 0 < r₀ := by positivity
  have hinit := integrable_spinITheta_init ha hΦ
  -- Bound on `closedBall 0 (3 * r₀ / 2)` (which contains `closedBall 0 r₀`)
  have hdom_ball : ∀ z : ℂ, ‖z‖ < 3 * r₀ / 2 →
      ∀ p : ℝ × ℝ, ‖(Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
          Complex.cos (2 * π * (p.2 : ℂ) * z)‖ ≤
        |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) *
          Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2) := by
    intro z hz p
    have hz_im : |z.im| ≤ 3 * r₀ / 2 := (Complex.abs_im_le_norm z).trans hz.le
    have hcos1 : ‖Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ))‖ ≤
        Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) := by
      have him : (2 * π * (p.1 : ℂ) * (ξ : ℂ)).im = 0 := by simp [Complex.mul_im]
      calc ‖Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ))‖
          ≤ Real.cosh (2 * π * (p.1 : ℂ) * (ξ : ℂ)).im := norm_complex_cos_le_cosh _
        _ = 1 := by rw [him, Real.cosh_zero]
        _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) := Real.one_le_cosh _
    have hcos2 : ‖Complex.cos (2 * π * (p.2 : ℂ) * z)‖ ≤
        Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2) := by
      have him : (2 * π * (p.2 : ℂ) * z).im = 2 * π * p.2 * z.im := by
        simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
      calc ‖Complex.cos (2 * π * (p.2 : ℂ) * z)‖
          ≤ Real.cosh (2 * π * (p.2 : ℂ) * z).im := norm_complex_cos_le_cosh _
        _ = Real.cosh (|2 * π * p.2 * z.im|) := by rw [him, Real.cosh_abs]
        _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2) := by
            rw [Real.cosh_le_cosh]
            have hle : |z.im| ≤ 4 * Real.sqrt a * (1 / 24) / 2 := by
              dsimp [r₀] at hz_im; linarith
            calc |(|2 * π * p.2 * z.im|)|
                = 2 * π * |z.im| * |p.2| := by
                  rw [abs_abs, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]; ring
              _ ≤ 2 * π * (4 * Real.sqrt a * (1 / 24) / 2) * |p.2| := by gcongr
              _ = |4 * π * Real.sqrt a * (1 / 24) * p.2| := by
                  rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * (1 / 24))]; ring
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcos1 (abs_nonneg _)) hcos2
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  -- Differentiability on `ball 0 (3 * r₀ / 2)` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  have hdiff_open : DifferentiableOn ℂ (spinSliceC Φ ξ) (Metric.ball 0 (3 * r₀ / 2)) := by
    intro z₀ hz₀
    have hz₀_norm : ‖z₀‖ < 3 * r₀ / 2 := by simpa [Metric.mem_ball] using hz₀
    set δ : ℝ := (3 * r₀ / 2 - ‖z₀‖) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    -- On `ball z₀ δ`, `|z.im| ≤ 3 * r₀ / 2 = √a / 16`, so `2π |p.2| cosh(2π p.2 z.im) ≤ C * cosh(π √a |p.2| / 6)`
    -- Actually `3 * r₀ / 2 = √a / 16`, and `2π * (√a / 16) = π √a / 8`, while `4π √a (1/24) = π √a / 6`!
    -- Since `π √a / 6 - π √a / 8 = π √a / 24`, `t ≤ (24 / (π √a)) * exp(π √a t / 24)`!
    set C_d : ℝ := 4 * π * (24 / (π * Real.sqrt a))
    let bound : ℝ × ℝ → ℝ := fun p =>
      C_d * (|Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) *
        Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2))
    have hbound_int : Integrable bound volume := hinit.const_mul C_d
    have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) * Complex.cos (2 * π * (p.2 : ℂ) * z)) volume :=
      Eventually.of_forall fun z => by
        have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
        have hc2 : Continuous (fun p : ℝ × ℝ => Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ))) := by fun_prop
        have hc3 : Continuous (fun p : ℝ × ℝ => Complex.cos (2 * π * (p.2 : ℂ) * z)) := by fun_prop
        exact ((hc1.mul hc2).mul hc3).aestronglyMeasurable
    have hF_int : Integrable (fun p : ℝ × ℝ =>
        (Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) * Complex.cos (2 * π * (p.2 : ℂ) * z₀)) volume :=
      hinit.mono' (hF_meas.self_of_nhds) (Eventually.of_forall (hdom_ball z₀ hz₀_norm))
    have hF_deriv : ∀ᵐ p ∂volume, ∀ z ∈ Metric.ball z₀ δ,
        HasDerivAt (fun w : ℂ => (Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
            Complex.cos (2 * π * (p.2 : ℂ) * w))
          (-((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
            Complex.sin (2 * π * (p.2 : ℂ) * z) * (2 * π * (p.2 : ℂ)))) z := by
      refine Eventually.of_forall fun p z _ => ?_
      have hd := (Complex.hasDerivAt_cos (2 * π * (p.2 : ℂ) * z)).comp z
        ((hasDerivAt_id z).const_mul (2 * π * (p.2 : ℂ)))
      exact (hd.const_mul ((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)))).congr_deriv (by ring)
    have hF'_meas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        -((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
          Complex.sin (2 * π * (p.2 : ℂ) * z₀) * (2 * π * (p.2 : ℂ)))) volume := by
      have hc0 : Continuous (fun p : ℝ × ℝ =>
          -((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
            Complex.sin (2 * π * (p.2 : ℂ) * z₀) * (2 * π * (p.2 : ℂ)))) := by
        have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
        fun_prop
      exact hc0.aestronglyMeasurable
    have hF'_bound : ∀ᵐ p ∂volume, ∀ z ∈ Metric.ball z₀ δ,
        ‖-((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
          Complex.sin (2 * π * (p.2 : ℂ) * z) * (2 * π * (p.2 : ℂ)))‖ ≤ bound p := by
      refine Eventually.of_forall fun p z hz => ?_
      have hz_norm : ‖z‖ < 3 * r₀ / 2 := by
        have : ‖z - z₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ < δ + ‖z₀‖ := by linarith
          _ < 3 * r₀ / 2 := by dsimp [δ]; linarith
      have hz_im : |z.im| ≤ 3 * r₀ / 2 := (Complex.abs_im_le_norm z).trans hz_norm.le
      have hcos1 : ‖Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ))‖ ≤
          Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) := by
        have him : (2 * π * (p.1 : ℂ) * (ξ : ℂ)).im = 0 := by simp [Complex.mul_im]
        calc ‖Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ))‖
            ≤ Real.cosh (2 * π * (p.1 : ℂ) * (ξ : ℂ)).im := norm_complex_cos_le_cosh _
          _ = 1 := by rw [him, Real.cosh_zero]
          _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) := Real.one_le_cosh _
      have hsin2 : ‖Complex.sin (2 * π * (p.2 : ℂ) * z) * (2 * π * (p.2 : ℂ))‖ ≤
          C_d * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2) := by
        have him : (2 * π * (p.2 : ℂ) * z).im = 2 * π * p.2 * z.im := by
          simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
        have hsin : ‖Complex.sin (2 * π * (p.2 : ℂ) * z)‖ ≤ Real.cosh (π * Real.sqrt a / 8 * |p.2|) := by
          calc ‖Complex.sin (2 * π * (p.2 : ℂ) * z)‖
              ≤ Real.cosh (2 * π * (p.2 : ℂ) * z).im := norm_complex_sin_le_cosh _
            _ = Real.cosh (|2 * π * p.2 * z.im|) := by rw [him, Real.cosh_abs]
            _ ≤ Real.cosh (π * Real.sqrt a / 8 * |p.2|) := by
                rw [Real.cosh_le_cosh]
                have hle : 2 * π * |z.im| ≤ π * Real.sqrt a / 8 := by
                  dsimp [r₀] at hz_im; nlinarith [Real.pi_pos]
                calc |(|2 * π * p.2 * z.im|)|
                    = (2 * π * |z.im|) * |p.2| := by
                      rw [abs_abs, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]; ring
                  _ ≤ (π * Real.sqrt a / 8) * |p.2| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
                  _ = |(π * Real.sqrt a / 8 * |p.2|)| := (abs_of_nonneg (by positivity)).symm
        have h2pi : ‖(2 * π * (p.2 : ℂ))‖ = 2 * π * |p.2| := by
          rw [show (2 * π * (p.2 : ℂ)) = ((2 * π * p.2 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
        have hp2_exp : |p.2| ≤ 24 / (π * Real.sqrt a) * Real.exp (π * Real.sqrt a / 24 * |p.2|) := by
          have hpos : 0 < π * Real.sqrt a / 24 := by positivity
          have hexp : π * Real.sqrt a / 24 * |p.2| + 1 ≤ Real.exp (π * Real.sqrt a / 24 * |p.2|) :=
            Real.add_one_le_exp _
          have h1 : π * Real.sqrt a / 24 * |p.2| ≤ Real.exp (π * Real.sqrt a / 24 * |p.2|) := by linarith
          calc |p.2| = 24 / (π * Real.sqrt a) * (π * Real.sqrt a / 24 * |p.2|) := by field_simp
            _ ≤ 24 / (π * Real.sqrt a) * Real.exp (π * Real.sqrt a / 24 * |p.2|) := by gcongr
        have hcosh_exp : Real.cosh (π * Real.sqrt a / 8 * |p.2|) * Real.exp (π * Real.sqrt a / 24 * |p.2|) ≤
            2 * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2) := by
          rw [← Real.cosh_abs (4 * π * Real.sqrt a * (1 / 24) * p.2),
            show |4 * π * Real.sqrt a * (1 / 24) * p.2| = π * Real.sqrt a / 6 * |p.2| by
              rw [abs_mul, abs_of_pos (by positivity)]; ring]
          set u : ℝ := π * Real.sqrt a / 8 * |p.2|
          set v : ℝ := π * Real.sqrt a / 24 * |p.2|
          have hu : 0 ≤ u := by positivity
          have huv : u + v = π * Real.sqrt a / 6 * |p.2| := by dsimp [u, v]; ring
          have hcosh_le_exp : Real.cosh u ≤ Real.exp u := by
            rw [Real.cosh_eq]
            have : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
            linarith
          have hexp_le_cosh : Real.exp (u + v) ≤ 2 * Real.cosh (u + v) := by
            rw [Real.cosh_eq]
            have : 0 < Real.exp (-(u + v)) := Real.exp_pos _
            linarith
          calc Real.cosh u * Real.exp v ≤ Real.exp u * Real.exp v := by gcongr
            _ = Real.exp (u + v) := (Real.exp_add u v).symm
            _ ≤ 2 * Real.cosh (u + v) := hexp_le_cosh
            _ = 2 * Real.cosh (π * Real.sqrt a / 6 * |p.2|) := by rw [huv]
        calc ‖Complex.sin (2 * π * (p.2 : ℂ) * z) * (2 * π * (p.2 : ℂ))‖
            = ‖Complex.sin (2 * π * (p.2 : ℂ) * z)‖ * ‖(2 * π * (p.2 : ℂ))‖ := norm_mul _ _
          _ ≤ Real.cosh (π * Real.sqrt a / 8 * |p.2|) * (2 * π * |p.2|) := by
              rw [h2pi]; exact mul_le_mul_of_nonneg_right hsin (by positivity)
          _ ≤ Real.cosh (π * Real.sqrt a / 8 * |p.2|) *
                (2 * π * (24 / (π * Real.sqrt a) * Real.exp (π * Real.sqrt a / 24 * |p.2|))) := by
              gcongr
          _ = 2 * π * (24 / (π * Real.sqrt a)) *
                (Real.cosh (π * Real.sqrt a / 8 * |p.2|) * Real.exp (π * Real.sqrt a / 24 * |p.2|)) := by ring
          _ ≤ 2 * π * (24 / (π * Real.sqrt a)) * (2 * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2)) := by
              gcongr
          _ = C_d * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2) := by
              dsimp [C_d]; ring
      calc ‖-((Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) *
              Complex.sin (2 * π * (p.2 : ℂ) * z) * (2 * π * (p.2 : ℂ)))‖
          = |Φ p| * ‖Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ))‖ *
              ‖Complex.sin (2 * π * (p.2 : ℂ) * z) * (2 * π * (p.2 : ℂ))‖ := by
            rw [norm_neg, mul_assoc ((Φ p : ℂ) * _), norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |Φ p| * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.1) *
              (C_d * Real.cosh (4 * π * Real.sqrt a * (1 / 24) * p.2)) := by
            refine mul_le_mul ?_ hsin2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
            exact mul_le_mul_of_nonneg_left hcos1 (abs_nonneg _)
        _ = bound p := by dsimp [bound]; ring
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun w p =>
        (Φ p : ℂ) * Complex.cos (2 * π * (p.1 : ℂ) * (ξ : ℂ)) * Complex.cos (2 * π * (p.2 : ℂ) * w))
      (Metric.ball_mem_nhds z₀ hδ) hF_meas hF_int hF'_meas hF'_bound hbound_int hF_deriv
    exact (hd.2.neg).differentiableAt.differentiableWithinAt
  refine ⟨?_, ?_⟩
  · refine ⟨hdiff_open.mono (Metric.ball_subset_ball (by linarith)), ?_⟩
    exact (hdiff_open.continuousOn.mono (Metric.closure_ball_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by linarith))))
  · intro z hz
    have hz_lt : ‖z‖ < 3 * r₀ / 2 := by
      have : ‖z‖ ≤ r₀ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      linarith
    unfold spinSliceC spinITheta
    rw [norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hinit
      (Eventually.of_forall (hdom_ball z hz_lt))

private lemma spin_slice_taylor_approx {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (ξ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    let ρ : ℝ := Real.sqrt a / 48
    ∃ P : Polynomial ℝ, P.natDegree < N ∧
      ∀ x ∈ Icc (-ρ) ρ, |Φ (ξ, x) - P.eval x| ≤ 2 * spinITheta a (1 / 24) Φ * (1 / 2 : ℝ) ^ N := by
  intro ρ
  set r₀ : ℝ := Real.sqrt a / 24
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hr₀ : 0 < r₀ := by positivity
  have hρ_eq : ρ = r₀ / 2 := by dsimp [ρ, r₀]; ring
  obtain ⟨hd, hbd⟩ := spinSliceC_differentiableOn_and_bound ha hΦ ξ
  let r₀_nn : NNReal := ⟨r₀, hr₀.le⟩
  have hr₀_nn : (0 : NNReal) < r₀_nn := hr₀
  have hps : HasFPowerSeriesOnBall (spinSliceC Φ ξ)
      (cauchyPowerSeries (spinSliceC Φ ξ) 0 (r₀_nn : ℝ)) 0 r₀_nn :=
    hd.hasFPowerSeriesOnBall hr₀_nn
  let c : ℕ → ℂ := fun n => cauchyPowerSeries (spinSliceC Φ ξ) 0 r₀ n (fun _ => 1)
  have hc_norm : ∀ n : ℕ, ‖c n‖ ≤ spinITheta a (1 / 24) Φ * r₀⁻¹ ^ n := by
    intro n
    have h1 : ‖c n‖ ≤ ‖cauchyPowerSeries (spinSliceC Φ ξ) 0 r₀ n‖ := by
      simpa [c] using (cauchyPowerSeries (spinSliceC Φ ξ) 0 r₀ n).le_opNorm (fun _ => (1 : ℂ))
    have h2 := norm_cauchyPowerSeries_le (spinSliceC Φ ξ) 0 r₀ n
    have hcirc : ∫ θ : ℝ in 0..2 * π, ‖spinSliceC Φ ξ (circleMap 0 r₀ θ)‖ ≤
        2 * π * spinITheta a (1 / 24) Φ := by
      have hcont : Continuous (fun θ : ℝ => ‖spinSliceC Φ ξ (circleMap 0 r₀ θ)‖) := by
        have hmem : ∀ θ : ℝ, circleMap 0 r₀ θ ∈ Metric.closedBall (0 : ℂ) r₀ := fun θ => by
          rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hr₀]
        exact ((hd.continuousOn.mono (closure_ball (0 : ℂ) hr₀.ne').symm.subset).comp_continuous
          (continuous_circleMap 0 r₀) hmem).norm
      calc ∫ θ : ℝ in 0..2 * π, ‖spinSliceC Φ ξ (circleMap 0 r₀ θ)‖
          ≤ ∫ _ : ℝ in 0..2 * π, spinITheta a (1 / 24) Φ := by
            refine intervalIntegral.integral_mono_on (by positivity)
              (hcont.intervalIntegrable 0 (2 * π)) intervalIntegrable_const fun θ _ => ?_
            exact hbd _ (by rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero,
              abs_of_pos hr₀])
        _ = 2 * π * spinITheta a (1 / 24) Φ := by simp [mul_comm]
    have h3 : (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖spinSliceC Φ ξ (circleMap 0 r₀ θ)‖ ≤
        spinITheta a (1 / 24) Φ := by
      calc (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖spinSliceC Φ ξ (circleMap 0 r₀ θ)‖
          ≤ (2 * π)⁻¹ * (2 * π * spinITheta a (1 / 24) Φ) := by gcongr
        _ = spinITheta a (1 / 24) Φ := by field_simp [Real.two_pi_pos.ne']
    calc ‖c n‖ ≤ ‖cauchyPowerSeries (spinSliceC Φ ξ) 0 r₀ n‖ := h1
      _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖spinSliceC Φ ξ (circleMap 0 r₀ θ)‖) * |r₀|⁻¹ ^ n := h2
      _ ≤ spinITheta a (1 / 24) Φ * r₀⁻¹ ^ n := by
          rw [abs_of_pos hr₀]
          exact mul_le_mul_of_nonneg_right h3 (by positivity)
  let P : Polynomial ℝ := ∑ n ∈ Finset.range N, Polynomial.C (c n).re * Polynomial.X ^ n
  refine ⟨P, ?_, ?_⟩
  · have hle : P.natDegree ≤ N - 1 := by
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      refine Finset.sup_le fun n hn => ?_
      have hn' : n < N := Finset.mem_range.mp hn
      exact (Polynomial.natDegree_C_mul_X_pow_le (c n).re n).trans (by omega)
    omega
  · intro x hx
    have hx_abs : |x| ≤ ρ := abs_le.mpr ⟨hx.1, hx.2⟩
    have hx_lt_r₀ : ‖(x : ℂ)‖ < r₀ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have hI_nn : 0 ≤ spinITheta a (1 / 24) Φ := by
      unfold spinITheta; exact integral_nonneg fun p => by positivity
    have hmem_ball : (x : ℂ) ∈ Metric.eball (0 : ℂ) (r₀_nn : ENNReal) := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_lt_ofReal_iff hr₀ |>.mpr hx_lt_r₀
    have hsumC : HasSum (fun n => c n * (x : ℂ) ^ n) (spinSliceC Φ ξ (x : ℂ)) := by
      have hs := hps.hasSum hmem_ball
      rw [zero_add] at hs
      have hr₀_coe : (r₀_nn : ℝ) = r₀ := rfl
      rw [hr₀_coe] at hs
      refine hs.congr_fun fun n => ?_
      simp only [c, cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
        smul_eq_mul, one_pow, one_mul, mul_comm]
    have hsum_norm : Summable (fun n => ‖(c n).re * x ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        ((summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
          (spinITheta a (1 / 24) Φ))
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hre : |(c n).re| ≤ ‖c n‖ := Complex.abs_re_le_norm _
      have hpow : |x| ^ n ≤ ρ ^ n := pow_le_pow_left₀ (abs_nonneg _) hx_abs n
      calc |(c n).re| * |x| ^ n
          ≤ (spinITheta a (1 / 24) Φ * r₀⁻¹ ^ n) * ρ ^ n :=
            mul_le_mul (hre.trans (hc_norm n)) hpow (by positivity)
              (mul_nonneg hI_nn (by positivity))
        _ = spinITheta a (1 / 24) Φ * (1 / 2 : ℝ) ^ n := by
            rw [hρ_eq, mul_assoc, ← mul_pow,
              show r₀⁻¹ * (r₀ / 2) = 1 / 2 by field_simp [hr₀.ne']]
    have hsumR : HasSum (fun n => (c n).re * x ^ n) (Φ (ξ, x)) := by
      have hre := Complex.reCLM.hasSum hsumC
      rw [Complex.reCLM_apply, spinSliceC_ofReal hΦ ξ x, Complex.ofReal_re] at hre
      refine hre.congr_fun fun n => ?_
      rw [← Complex.ofReal_pow, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    have htail : Φ (ξ, x) - P.eval x = ∑' k : ℕ, (c (k + N)).re * x ^ (k + N) := by
      have hsplit := hsumR.summable.sum_add_tsum_nat_add N
      rw [hsumR.tsum_eq] at hsplit
      have hP : P.eval x = ∑ n ∈ Finset.range N, (c n).re * x ^ n := by
        let e := Polynomial.evalRingHom x
        change e P = ∑ n ∈ Finset.range N, (c n).re * x ^ n
        dsimp [P]
        rw [map_sum]
        refine Finset.sum_congr rfl fun n _ => by simp [e]
      linarith
    rw [htail]
    have htsum_tail : Summable (fun k : ℕ => ‖(c (k + N)).re * x ^ (k + N)‖) :=
      (summable_nat_add_iff N).mpr hsum_norm
    calc |∑' k : ℕ, (c (k + N)).re * x ^ (k + N)|
        ≤ ∑' k : ℕ, ‖(c (k + N)).re * x ^ (k + N)‖ := norm_tsum_le_tsum_norm htsum_tail
      _ ≤ ∑' k : ℕ, (spinITheta a (1 / 24) Φ * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
          refine Summable.tsum_le_tsum (fun k => ?_) htsum_tail ?_
          · rw [Real.norm_eq_abs, abs_mul, abs_pow]
            have hre : |(c (k + N)).re| ≤ ‖c (k + N)‖ := Complex.abs_re_le_norm _
            have hpow : |x| ^ (k + N) ≤ ρ ^ (k + N) := pow_le_pow_left₀ (abs_nonneg _) hx_abs _
            calc |(c (k + N)).re| * |x| ^ (k + N)
                ≤ (spinITheta a (1 / 24) Φ * r₀⁻¹ ^ (k + N)) * ρ ^ (k + N) :=
                  mul_le_mul (hre.trans (hc_norm _)) hpow (by positivity)
                    (mul_nonneg hI_nn (by positivity))
              _ = (spinITheta a (1 / 24) Φ * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ k := by
                  rw [hρ_eq, mul_assoc, ← mul_pow,
                    show r₀⁻¹ * (r₀ / 2) = 1 / 2 by field_simp [hr₀.ne'],
                    pow_add]
                  ring
          · exact (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2)
              (by norm_num)).mul_left _
      _ = 2 * spinITheta a (1 / 24) Φ * (1 / 2 : ℝ) ^ N := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by norm_num)]
          ring

lemma spin_slice_L1_le_L1_sq {a : ℝ} (ha : 2 ≤ a)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    let ρ : ℝ := Real.sqrt a / 48
    ∃ C : ℝ, 0 < C ∧ ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → ∀ ξ : ℝ,
      ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| ≤
        C * (spinITheta a (1 / 24) Φ + 1) ^ ε *
          (∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| * x ^ 2) ^ (1 - ε) := by
  intro ρ
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hρ : 0 < ρ := by positivity
  -- Use `log(1/d) ≤ (9/ε) * (1/d)^(ε/9)` so `(log(1/d)/log 2 + 2)^9 ≤ C_log * (1/d)^ε`
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A_log : ℝ := (9 / ε) / Real.log 2 + 2
  have hA_log : 0 < A_log := by positivity
  let C_main : ℝ := 15364 * ρ⁻¹ ^ 2 * A_log ^ 9 * ρ ^ (3 * ε) + 8 * ρ⁻¹ ^ 2 * ρ ^ (3 * ε)
  refine ⟨C_main, by positivity, fun {Φ} hΦ ξ => ?_⟩
  set M₀ : ℝ := spinITheta a (1 / 24) Φ
  have hM₀_nn : 0 ≤ M₀ := by
    dsimp [M₀]; unfold spinITheta
    exact integral_nonneg fun p => by positivity
  set Q : ℝ := ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| * x ^ 2
  have hcont_Φ : Continuous (fun x : ℝ => Φ (ξ, x)) :=
    hΦ.cont.comp (continuous_const.prodMk continuous_id)
  have hint_Φ : IntegrableOn (fun x : ℝ => |Φ (ξ, x)|) (Icc (-ρ) ρ) :=
    hcont_Φ.abs.continuousOn.integrableOn_Icc
  have hint_Q : IntegrableOn (fun x : ℝ => |Φ (ξ, x)| * x ^ 2) (Icc (-ρ) ρ) :=
    (hcont_Φ.abs.mul (continuous_pow 2)).continuousOn.integrableOn_Icc
  have hQ_nn : 0 ≤ Q := setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
  have hM₀_pt : ∀ x ∈ Icc (-ρ) ρ, |Φ (ξ, x)| ≤ M₀ := fun x hx => by
    obtain ⟨_, hbd⟩ := spinSliceC_differentiableOn_and_bound ha hΦ ξ
    have h1 := hbd (x : ℂ) (by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      have : |x| ≤ ρ := abs_le.mpr ⟨hx.1, hx.2⟩
      have hρ_le : ρ ≤ Real.sqrt a / 24 := by
        change Real.sqrt a / 48 ≤ Real.sqrt a / 24; linarith
      exact this.trans hρ_le)
    rw [spinSliceC_ofReal hΦ ξ x, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1
  have hL1_M₀ : ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| ≤ 2 * ρ * M₀ := by
    calc ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)|
        ≤ ∫ _ in Icc (-ρ) ρ, M₀ := setIntegral_mono_on hint_Φ
          (integrableOn_const (hs := measure_Icc_lt_top.ne)) measurableSet_Icc hM₀_pt
      _ = 2 * ρ * M₀ := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
          ring
  by_cases hQ0 : Q = 0
  · have hae : ∀ᵐ x ∂(volume.restrict (Icc (-ρ) ρ)), |Φ (ξ, x)| * x ^ 2 = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x => by positivity) hint_Q).mp hQ0
    have hzero_on : ∀ x ∈ Icc (-ρ) ρ, |Φ (ξ, x)| = 0 := by
      have hcont_on : ContinuousOn (fun x : ℝ => |Φ (ξ, x)|) (Icc (-ρ) ρ) := hcont_Φ.abs.continuousOn
      have hsub : Icc (-ρ) ρ \ {(0 : ℝ)} ⊆ {x | |Φ (ξ, x)| = 0} := by
        intro x hx
        by_contra hne
        have hpos_f : 0 < |Φ (ξ, x)| * x ^ 2 := by
          have hx0 : x ≠ 0 := fun h => hx.2 (Set.mem_singleton_iff.mpr h)
          have h1 : 0 < |Φ (ξ, x)| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
          positivity
        have hcont_mul : Continuous (fun y : ℝ => |Φ (ξ, y)| * y ^ 2) :=
          hcont_Φ.abs.mul (continuous_pow 2)
        obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont_mul.continuousAt
          (|Φ (ξ, x)| * x ^ 2 / 2) (by positivity)
        have hpos_meas : 0 < volume (Icc (-ρ) ρ ∩ Metric.ball x δ) := by
          have hsub_int : Ioo (max (-ρ) (x - δ)) (min ρ (x + δ)) ⊆ Icc (-ρ) ρ ∩ Metric.ball x δ := by
            intro y hy
            refine ⟨⟨le_trans (le_max_left _ _) hy.1.le, le_trans hy.2.le (min_le_left _ _)⟩, ?_⟩
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith [le_max_right (-ρ) (x - δ), hy.1],
              by linarith [min_le_right ρ (x + δ), hy.2]⟩
          have hlt_max : max (-ρ) (x - δ) < min ρ (x + δ) := by
            simp only [lt_min_iff, max_lt_iff]
            exact ⟨⟨by linarith, by linarith [hx.1.2]⟩, ⟨by linarith [hx.1.1], by linarith⟩⟩
          exact lt_of_lt_of_le (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt_max))
            (measure_mono hsub_int)
        have hpos_on : ∀ y ∈ Icc (-ρ) ρ ∩ Metric.ball x δ, 0 < |Φ (ξ, y)| * y ^ 2 := fun y hy => by
          have := hball hy.2
          rw [Real.dist_eq, abs_lt] at this
          linarith
        have hmeas_zero : volume (Icc (-ρ) ρ ∩ Metric.ball x δ) = 0 := by
          have hsub_ae : Icc (-ρ) ρ ∩ Metric.ball x δ ⊆ {y | |Φ (ξ, y)| * y ^ 2 ≠ 0} ∩ Icc (-ρ) ρ :=
            fun y hy => ⟨(hpos_on y hy).ne', hy.1⟩
          refine measure_mono_null hsub_ae ?_
          rw [← Measure.restrict_apply' measurableSet_Icc]
          exact ae_iff.mp hae
        exact hpos_meas.ne' hmeas_zero
      have hcl : Icc (-ρ) ρ ⊆ closure (Icc (-ρ) ρ \ {(0 : ℝ)}) := by
        intro x hx
        by_cases hx0 : x = 0
        · subst hx0
          rw [Metric.mem_closure_iff]
          intro r hr
          refine ⟨min ρ (r / 2), ⟨⟨by have : 0 ≤ min ρ (r / 2) := le_min hρ.le (by positivity); linarith,
            min_le_left _ _⟩,
            fun h => by have : 0 < min ρ (r / 2) := lt_min hρ (by positivity); exact this.ne' (Set.mem_singleton_iff.mp h)⟩, ?_⟩
          rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (lt_min hρ (by positivity))]
          exact (min_le_right _ _).trans_lt (by linarith)
        · exact subset_closure ⟨hx, fun h => hx0 (Set.mem_singleton_iff.mp h)⟩
      exact fun x hx => closure_minimal hsub (isClosed_eq hcont_Φ.abs continuous_zero) (hcl hx)
    have hL1_zero : ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero hzero_on
    rw [hL1_zero, hQ0]
    positivity
  have hQ_pos : 0 < Q := lt_of_le_of_ne hQ_nn (Ne.symm hQ0)
  by_cases hQ_big : (M₀ + 1) * ρ ^ 3 / 2 ≤ Q
  · -- Easy branch: `M₀ + 1 ≤ 2 * Q / ρ^3`, so `2 * ρ * M₀ ≤ 4 * ρ⁻² * Q`
    have hM1_le : M₀ + 1 ≤ 2 * Q * ρ⁻¹ ^ 3 := by
      calc M₀ + 1 = ((M₀ + 1) * ρ ^ 3 / 2) * (2 * ρ⁻¹ ^ 3) := by field_simp [hρ.ne']
        _ ≤ Q * (2 * ρ⁻¹ ^ 3) := by gcongr
        _ = 2 * Q * ρ⁻¹ ^ 3 := by ring
    have hQ_le_M : Q ≤ 2 * (M₀ + 1) * ρ ^ 3 := by
      have h1 : Q ≤ 2 * ρ ^ 3 * M₀ := by
        calc Q ≤ ∫ _ in Icc (-ρ) ρ, M₀ * ρ ^ 2 := by
              refine setIntegral_mono_on hint_Q (integrableOn_const (hs := measure_Icc_lt_top.ne))
                measurableSet_Icc fun x hx => ?_
              have hx_sq : x ^ 2 ≤ ρ ^ 2 := by
                rw [sq_le_sq, abs_of_pos hρ]; exact abs_le.mpr ⟨hx.1, hx.2⟩
              exact mul_le_mul (hM₀_pt x hx) hx_sq (sq_nonneg _) hM₀_nn
          _ = 2 * ρ ^ 3 * M₀ := by
              rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]; ring
      nlinarith [show 0 ≤ ρ ^ 3 by positivity]
    calc ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)|
        ≤ 2 * ρ * M₀ := hL1_M₀
      _ ≤ 2 * ρ * (M₀ + 1) := by linarith
      _ ≤ 2 * ρ * (2 * Q * ρ⁻¹ ^ 3) := by gcongr
      _ = 4 * ρ⁻¹ ^ 2 * Q := by field_simp [hρ.ne']; ring
      _ = 4 * ρ⁻¹ ^ 2 * (Q ^ ε * Q ^ (1 - ε)) := by
          rw [← Real.rpow_add hQ_pos]; norm_num
      _ ≤ 4 * ρ⁻¹ ^ 2 * ((2 * (M₀ + 1) * ρ ^ 3) ^ ε * Q ^ (1 - ε)) := by
          gcongr
      _ ≤ C_main * (M₀ + 1) ^ ε * Q ^ (1 - ε) := by
          have h2e : (2 : ℝ) ^ ε ≤ 2 := by
            calc (2 : ℝ) ^ ε ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
          have h1 : 4 * ρ⁻¹ ^ 2 * ((2 * (M₀ + 1) * ρ ^ 3) ^ ε * Q ^ (1 - ε)) =
              (4 * (2 : ℝ) ^ ε * ρ⁻¹ ^ 2 * ρ ^ (3 * ε)) * (M₀ + 1) ^ ε * Q ^ (1 - ε) := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow (by norm_num) (by positivity),
              ← Real.rpow_natCast ρ 3, ← Real.rpow_mul hρ.le]; ring
          rw [h1]
          have h2 : 4 * (2 : ℝ) ^ ε * ρ⁻¹ ^ 2 * ρ ^ (3 * ε) ≤ C_main := by
            have h2a : 4 * (2 : ℝ) ^ ε * ρ⁻¹ ^ 2 * ρ ^ (3 * ε) ≤ 8 * ρ⁻¹ ^ 2 * ρ ^ (3 * ε) := by
              gcongr; linarith
            dsimp [C_main]
            linarith [show 0 ≤ 15364 * ρ⁻¹ ^ 2 * A_log ^ 9 * ρ ^ (3 * ε) by positivity]
          gcongr
  · push_neg at hQ_big
    set d : ℝ := Q / ((M₀ + 1) * ρ ^ 3)
    have hd_pos : 0 < d := by positivity
    have hd_lt : d < 1 / 2 := by
      dsimp [d]
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have hinv_d_gt : 2 < 1 / d := by
      rw [lt_div_iff₀ hd_pos]; linarith
    have hlog_nn : 0 ≤ Real.log (1 / d) / Real.log 2 :=
      div_nonneg (Real.log_nonneg (by linarith)) hlog2.le
    set N : ℕ := Nat.ceil (Real.log (1 / d) / Real.log 2) + 1
    have hN : 1 ≤ N := Nat.le_add_left 1 _
    have hhalf_le_d : (1 / 2 : ℝ) ^ N ≤ d := by
      have h1 : Real.log (1 / d) / Real.log 2 ≤ (N : ℝ) := by
        exact (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ _)
      have h2 : Real.log (1 / d) ≤ (N : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).mp h1
      have h3 : 1 / d ≤ (2 : ℝ) ^ N := by
        calc 1 / d = Real.exp (Real.log (1 / d)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp ((N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr h2
          _ = (2 : ℝ) ^ N := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      calc (1 / 2 : ℝ) ^ N = ((2 : ℝ) ^ N)⁻¹ := by rw [one_div, inv_pow]
        _ ≤ (1 / d)⁻¹ := inv_anti₀ (by positivity) h3
        _ = d := by rw [one_div, inv_inv]
    have hN_le : (N : ℝ) ≤ A_log * (1 / d) ^ (ε / 9) := by
      have hceil : (N : ℝ) ≤ Real.log (1 / d) / Real.log 2 + 2 := by
        have h1 : (Nat.ceil (Real.log (1 / d) / Real.log 2) : ℝ) < Real.log (1 / d) / Real.log 2 + 1 :=
          Nat.ceil_lt_add_one hlog_nn
        push_cast [N]
        linarith
      have hlog_le : Real.log (1 / d) ≤ (9 / ε) * (1 / d) ^ (ε / 9) := by
        have hpow_pos : 0 < (1 / d) ^ (ε / 9) := by positivity
        have hlog_sub := Real.log_le_sub_one_of_pos hpow_pos
        rw [Real.log_rpow (by positivity)] at hlog_sub
        have h1 : (ε / 9) * Real.log (1 / d) ≤ (1 / d) ^ (ε / 9) := by linarith
        calc Real.log (1 / d) = (9 / ε) * ((ε / 9) * Real.log (1 / d)) := by field_simp [hε0.ne']
          _ ≤ (9 / ε) * (1 / d) ^ (ε / 9) := by gcongr
      have hone_le : (1 : ℝ) ≤ (1 / d) ^ (ε / 9) :=
        Real.one_le_rpow (by linarith) (by positivity)
      calc (N : ℝ) ≤ Real.log (1 / d) / Real.log 2 + 2 := hceil
        _ ≤ ((9 / ε) * (1 / d) ^ (ε / 9)) / Real.log 2 + 2 * (1 / d) ^ (ε / 9) := by
            gcongr; linarith
        _ = A_log * (1 / d) ^ (ε / 9) := by dsimp [A_log]; ring
    have hN9_le : (N : ℝ) ^ 9 ≤ A_log ^ 9 * (1 / d) ^ ε := by
      calc (N : ℝ) ^ 9 ≤ (A_log * (1 / d) ^ (ε / 9)) ^ 9 := pow_le_pow_left₀ (by positivity) hN_le 9
        _ = A_log ^ 9 * ((1 / d) ^ (ε / 9)) ^ 9 := by ring
        _ = A_log ^ 9 * (1 / d) ^ ε := by
            rw [← Real.rpow_natCast ((1 / d) ^ (ε / 9)) 9, ← Real.rpow_mul (by positivity)]
            congr 2; ring
    obtain ⟨P, hPdeg, hPerr⟩ := spin_slice_taylor_approx ha hΦ ξ hN
    have hPerr_d : ∀ x ∈ Icc (-ρ) ρ, |Φ (ξ, x) - P.eval x| ≤ 2 * M₀ * d := fun x hx =>
      (hPerr x hx).trans (by gcongr)
    have hMd_le : M₀ * d ≤ Q * ρ⁻¹ ^ 3 := by
      dsimp [d]
      calc M₀ * (Q / ((M₀ + 1) * ρ ^ 3)) = (M₀ / (M₀ + 1)) * (Q * ρ⁻¹ ^ 3) := by
            field_simp [hρ.ne']
        _ ≤ 1 * (Q * ρ⁻¹ ^ 3) := by
            gcongr; rw [div_le_one (by linarith)]; linarith
        _ = Q * ρ⁻¹ ^ 3 := one_mul _
    have hint_P : IntegrableOn (fun x : ℝ => |P.eval x|) (Icc (-ρ) ρ) :=
      P.continuous.abs.continuousOn.integrableOn_Icc
    have hint_P_sq : IntegrableOn (fun x : ℝ => |P.eval x| * x ^ 2) (Icc (-ρ) ρ) :=
      (P.continuous.abs.mul (continuous_pow 2)).continuousOn.integrableOn_Icc
    have hQ_P : ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2 ≤ 5 * Q := by
      have hpt : ∀ x ∈ Icc (-ρ) ρ, |P.eval x| * x ^ 2 ≤ |Φ (ξ, x)| * x ^ 2 + 2 * M₀ * d * ρ ^ 2 := by
        intro x hx
        have htri : |P.eval x| ≤ |Φ (ξ, x)| + |Φ (ξ, x) - P.eval x| := by
          have h1 : |P.eval x| - |Φ (ξ, x)| ≤ |P.eval x - Φ (ξ, x)| := abs_sub_abs_le_abs_sub _ _
          rw [abs_sub_comm] at h1
          linarith
        have hx_sq : x ^ 2 ≤ ρ ^ 2 := by
          rw [sq_le_sq, abs_of_pos hρ]; exact abs_le.mpr ⟨hx.1, hx.2⟩
        calc |P.eval x| * x ^ 2
            ≤ (|Φ (ξ, x)| + |Φ (ξ, x) - P.eval x|) * x ^ 2 := by gcongr
          _ = |Φ (ξ, x)| * x ^ 2 + |Φ (ξ, x) - P.eval x| * x ^ 2 := by ring
          _ ≤ |Φ (ξ, x)| * x ^ 2 + (2 * M₀ * d) * ρ ^ 2 := by
              gcongr; exact hPerr_d x hx
          _ = |Φ (ξ, x)| * x ^ 2 + 2 * M₀ * d * ρ ^ 2 := by ring
      calc ∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2
          ≤ ∫ x in Icc (-ρ) ρ, (|Φ (ξ, x)| * x ^ 2 + 2 * M₀ * d * ρ ^ 2) :=
            setIntegral_mono_on hint_P_sq (hint_Q.add (integrableOn_const (hs := measure_Icc_lt_top.ne)))
              measurableSet_Icc hpt
        _ = Q + 4 * ρ ^ 3 * (M₀ * d) := by
            rw [integral_add hint_Q (integrableOn_const (hs := measure_Icc_lt_top.ne)),
              setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
            ring
        _ ≤ Q + 4 * ρ ^ 3 * (Q * ρ⁻¹ ^ 3) := by gcongr
        _ = 5 * Q := by field_simp [hρ.ne']; ring
    have hL1_P := poly_L1_le_L1_sq hN P hPdeg hρ
    have hL1_Φ : ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| ≤ 15364 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q := by
      have hpt : ∀ x ∈ Icc (-ρ) ρ, |Φ (ξ, x)| ≤ |P.eval x| + 2 * M₀ * d := fun x hx => by
        have h1 : |Φ (ξ, x)| - |P.eval x| ≤ |Φ (ξ, x) - P.eval x| := abs_sub_abs_le_abs_sub _ _
        linarith [hPerr_d x hx]
      have h1 : ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)| ≤
          (∫ x in Icc (-ρ) ρ, |P.eval x|) + 4 * ρ * (M₀ * d) := by
        calc ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)|
            ≤ ∫ x in Icc (-ρ) ρ, (|P.eval x| + 2 * M₀ * d) :=
              setIntegral_mono_on hint_Φ
                (hint_P.add (integrableOn_const (hs := measure_Icc_lt_top.ne))) measurableSet_Icc hpt
          _ = (∫ x in Icc (-ρ) ρ, |P.eval x|) + 4 * ρ * (M₀ * d) := by
              rw [integral_add hint_P (integrableOn_const (hs := measure_Icc_lt_top.ne)),
                setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
              ring
      have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ (by exact_mod_cast hN)
      calc ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)|
          ≤ 3072 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * (∫ x in Icc (-ρ) ρ, |P.eval x| * x ^ 2) +
              4 * ρ * (M₀ * d) := by linarith
        _ ≤ 3072 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * (5 * Q) + 4 * ρ * (Q * ρ⁻¹ ^ 3) := by gcongr
        _ = 15360 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q + 4 * ρ⁻¹ ^ 2 * Q := by
            field_simp [hρ.ne']; ring
        _ ≤ 15360 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q + 4 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q := by
            have h4 : 4 * ρ⁻¹ ^ 2 * Q ≤ 4 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q := by
              calc 4 * ρ⁻¹ ^ 2 * Q = 4 * ρ⁻¹ ^ 2 * 1 * Q := by ring
                _ ≤ 4 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q := by gcongr
            linarith
        _ = 15364 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q := by ring
    have hpow_dQ : (1 / d) ^ ε * Q = ρ ^ (3 * ε) * (M₀ + 1) ^ ε * Q ^ (1 - ε) := by
      have h1d : 1 / d = ((M₀ + 1) * ρ ^ 3) / Q := by dsimp [d]; field_simp
      rw [h1d, Real.div_rpow (by positivity) hQ_pos.le,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast ρ 3,
        ← Real.rpow_mul hρ.le]
      have hQ_div : Q / Q ^ ε = Q ^ (1 - ε) := by
        conv_lhs => lhs; rw [← Real.rpow_one Q]
        exact (Real.rpow_sub hQ_pos 1 ε).symm
      calc (M₀ + 1) ^ ε * ρ ^ (↑3 * ε) / Q ^ ε * Q
          = ρ ^ (3 * ε) * (M₀ + 1) ^ ε * (Q / Q ^ ε) := by norm_cast; ring
        _ = ρ ^ (3 * ε) * (M₀ + 1) ^ ε * Q ^ (1 - ε) := by rw [hQ_div]
    calc ∫ x in Icc (-ρ) ρ, |Φ (ξ, x)|
        ≤ 15364 * ρ⁻¹ ^ 2 * (N : ℝ) ^ 9 * Q := hL1_Φ
      _ ≤ 15364 * ρ⁻¹ ^ 2 * (A_log ^ 9 * (1 / d) ^ ε) * Q := by gcongr
      _ = 15364 * ρ⁻¹ ^ 2 * A_log ^ 9 * ((1 / d) ^ ε * Q) := by ring
      _ = (15364 * ρ⁻¹ ^ 2 * A_log ^ 9 * ρ ^ (3 * ε)) * (M₀ + 1) ^ ε * Q ^ (1 - ε) := by
          rw [hpow_dQ]; ring
      _ ≤ C_main * (M₀ + 1) ^ ε * Q ^ (1 - ε) := by
          have hle : 15364 * ρ⁻¹ ^ 2 * A_log ^ 9 * ρ ^ (3 * ε) ≤ C_main := by
            dsimp [C_main]; linarith [show 0 ≤ 8 * ρ⁻¹ ^ 2 * ρ ^ (3 * ε) by positivity]
          gcongr

lemma integrable_exp_neg_mul_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ => Real.exp (-δ * |x|)) volume := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-δ * x)) (Ioi 0) volume :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-δ * |x|)) (Ici 0) volume := by
    refine (h1.congr_set_ae Ioi_ae_eq_Ici.symm).congr_fun (fun x hx => ?_) measurableSet_Ici
    rw [abs_of_nonneg hx]
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-δ * |x|)) (Iic 0) volume := by
    have hcomp : IntegrableOn (fun x : ℝ => Real.exp (-δ * |x|)) (Ici 0) volume := hpos
    have hmap := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding (s := Ici (0 : ℝ))).mpr hcomp
    rw [show (Neg.neg : ℝ → ℝ) ⁻¹' Ici 0 = Iic 0 by ext x; simp] at hmap
    exact hmap.congr_fun (fun x _ => by simp [abs_neg]) measurableSet_Iic
  rw [← integrableOn_univ, show (Set.univ : Set ℝ) = Iic 0 ∪ Ici 0 from (Iic_union_Ici).symm]
  exact hneg.union hpos

lemma integrable_spinITheta {a : ℝ} (ha : 2 ≤ a) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) :
    Integrable (fun p : ℝ × ℝ => |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
      Real.cosh (4 * π * Real.sqrt a * θ * p.2)) volume := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  set ρ : ℝ := Real.sqrt a / 48
  have hρ : 0 < ρ := by positivity
  let f : ℝ × ℝ → ℝ := fun p =>
    |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
      Real.cosh (4 * π * Real.sqrt a * θ * p.2)
  have hf_cont : Continuous f := by
    have hc1 : Continuous (fun p : ℝ × ℝ => |Φ p|) := hΦ.cont.abs
    fun_prop
  have hf_nn : ∀ p : ℝ × ℝ, 0 ≤ f p := fun p => by dsimp [f]; positivity
  have hcosh_le : ∀ r : ℝ, Real.cosh (4 * π * Real.sqrt a * θ * r) ≤
      Real.exp (2 * π * Real.sqrt a * |r|) := fun r => by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have h1 : |4 * π * Real.sqrt a * θ * r| ≤ 2 * π * Real.sqrt a * |r| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ)]
      have h4θ : 4 * θ ≤ 2 := by linarith
      calc 4 * π * Real.sqrt a * θ * |r| = (4 * θ) * (π * Real.sqrt a * |r|) := by ring
        _ ≤ 2 * (π * Real.sqrt a * |r|) := by gcongr
        _ = 2 * π * Real.sqrt a * |r| := by ring
    have h2 : Real.exp (|4 * π * Real.sqrt a * θ * r|) ≤ Real.exp (2 * π * Real.sqrt a * |r|) :=
      Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-|4 * π * Real.sqrt a * θ * r|) ≤ Real.exp (2 * π * Real.sqrt a * |r|) :=
      Real.exp_le_exp.mpr (by linarith [abs_nonneg (4 * π * Real.sqrt a * θ * r)])
    linarith
  have hv1_tail : ∃ c_tail : ℝ, 0 < c_tail ∧ ∀ r : ℝ, ρ ≤ |r| →
      Real.exp (2 * π * Real.sqrt a * |r|) ≤ c_tail * spinV1 a r := by
    set m := min (1 : ℝ) (Real.sqrt a * ρ)
    have hm : 0 < m := lt_min one_pos (by positivity)
    refine ⟨4 * a / m ^ 2, by positivity, fun r hr => ?_⟩
    have hv := spinV1_ge_inv_four_a_exp_min_sq ha r
    have hm_le : m ≤ min (1 : ℝ) (Real.sqrt a * |r|) := by
      refine le_min (min_le_left _ _) ?_
      exact (min_le_right _ _).trans (by gcongr)
    have hm2 : m ^ 2 ≤ min (1 : ℝ) (Real.sqrt a * |r|) ^ 2 :=
      pow_le_pow_left₀ hm.le hm_le 2
    have h1 : (4 * a)⁻¹ * m ^ 2 * Real.exp (2 * π * Real.sqrt a * |r|) ≤ spinV1 a r := by
      calc (4 * a)⁻¹ * m ^ 2 * Real.exp (2 * π * Real.sqrt a * |r|)
          ≤ (4 * a)⁻¹ * min 1 (Real.sqrt a * |r|) ^ 2 * Real.exp (2 * π * Real.sqrt a * |r|) := by
            gcongr
        _ = (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * |r|) ^ 2 := by ring
        _ ≤ spinV1 a r := hv
    calc Real.exp (2 * π * Real.sqrt a * |r|)
        = (4 * a / m ^ 2) * ((4 * a)⁻¹ * m ^ 2 * Real.exp (2 * π * Real.sqrt a * |r|)) := by
          field_simp [ha0.ne', hm.ne']
      _ ≤ (4 * a / m ^ 2) * spinV1 a r := by gcongr
  obtain ⟨c_tail, hc_tail, hv1_tail⟩ := hv1_tail
  have hv1_core : ∃ c_core : ℝ, 0 < c_core ∧ ∀ y : ℝ, |y| ≤ ρ → y ^ 2 ≤ c_core * spinV1 a y := by
    set m := min (1 : ℝ) (Real.sqrt a * ρ)
    have hm : 0 < m := lt_min one_pos (by positivity)
    refine ⟨4 * a * (ρ / m) ^ 2, by positivity, fun y hy => ?_⟩
    have hv := spinV1_ge_inv_four_a_exp_min_sq ha y
    have hmy : (m / ρ) * |y| ≤ min (1 : ℝ) (Real.sqrt a * |y|) := by
      refine le_min ?_ ?_
      · calc (m / ρ) * |y| ≤ (1 / ρ) * ρ := by
              exact mul_le_mul (div_le_div_of_nonneg_right (min_le_left _ _) hρ.le) hy
                (abs_nonneg _) (by positivity)
          _ = 1 := div_mul_cancel₀ 1 hρ.ne'
      · calc (m / ρ) * |y| ≤ ((Real.sqrt a * ρ) / ρ) * |y| := by
              exact mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_right (min_le_right _ _) hρ.le) (abs_nonneg _)
          _ = Real.sqrt a * |y| := by field_simp [hρ.ne']
    have hmy2 : (m / ρ) ^ 2 * y ^ 2 ≤ min (1 : ℝ) (Real.sqrt a * |y|) ^ 2 := by
      calc (m / ρ) ^ 2 * y ^ 2 = ((m / ρ) * |y|) ^ 2 := by rw [mul_pow, sq_abs]
        _ ≤ min (1 : ℝ) (Real.sqrt a * |y|) ^ 2 := pow_le_pow_left₀ (by positivity) hmy 2
    have hexp1 : 1 ≤ Real.exp (2 * π * Real.sqrt a * |y|) := Real.one_le_exp (by positivity)
    have h1 : (4 * a)⁻¹ * (m / ρ) ^ 2 * y ^ 2 ≤ spinV1 a y := by
      calc (4 * a)⁻¹ * (m / ρ) ^ 2 * y ^ 2
          = (4 * a)⁻¹ * ((m / ρ) ^ 2 * y ^ 2) := by ring
        _ ≤ (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |y|) *
              min 1 (Real.sqrt a * |y|) ^ 2 := by
            calc (4 * a)⁻¹ * ((m / ρ) ^ 2 * y ^ 2)
                ≤ (4 * a)⁻¹ * min 1 (Real.sqrt a * |y|) ^ 2 := by gcongr
              _ = (4 * a)⁻¹ * 1 * min 1 (Real.sqrt a * |y|) ^ 2 := by ring
              _ ≤ (4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |y|) *
                    min 1 (Real.sqrt a * |y|) ^ 2 := by gcongr
        _ ≤ spinV1 a y := hv
    calc y ^ 2 = (4 * a * (ρ / m) ^ 2) * ((4 * a)⁻¹ * (m / ρ) ^ 2 * y ^ 2) := by
          field_simp [ha0.ne', hm.ne', hρ.ne']
      _ ≤ (4 * a * (ρ / m) ^ 2) * spinV1 a y := by gcongr
  obtain ⟨c_core, hc_core, hv1_core⟩ := hv1_core
  -- Region 1: compact `Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ`
  let S₁ : Set (ℝ × ℝ) := Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ
  have hS₁ : IntegrableOn f S₁ volume :=
    hf_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- Region 2: `{p | ρ ≤ |p.1| ∧ ρ ≤ |p.2|}`
  let S₂ : Set (ℝ × ℝ) := {p : ℝ × ℝ | ρ ≤ |p.1| ∧ ρ ≤ |p.2|}
  have hS₂_meas : MeasurableSet S₂ :=
    (isClosed_le continuous_const (continuous_abs.comp continuous_fst)).measurableSet.inter
      (isClosed_le continuous_const (continuous_abs.comp continuous_snd)).measurableSet
  have hS₂ : IntegrableOn f S₂ volume := by
    refine (hΦ.int_M2.const_mul (c_tail * c_tail)).integrableOn.mono' ?_ ?_
    · exact hf_cont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem hS₂_meas] with p hp
      rw [Real.norm_of_nonneg (hf_nn p)]
      have h1 : Real.cosh (4 * π * Real.sqrt a * θ * p.1) ≤ c_tail * spinV1 a p.1 :=
        (hcosh_le p.1).trans (hv1_tail p.1 hp.1)
      have h2 : Real.cosh (4 * π * Real.sqrt a * θ * p.2) ≤ c_tail * spinV1 a p.2 :=
        (hcosh_le p.2).trans (hv1_tail p.2 hp.2)
      calc |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θ * p.2)
          ≤ |Φ p| * (c_tail * spinV1 a p.1) * (c_tail * spinV1 a p.2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
              (Real.cosh_pos _).le (mul_nonneg (abs_nonneg _)
                (mul_nonneg hc_tail.le (spinV1_nonneg ha p.1)))
        _ = (c_tail * c_tail) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
  -- Region 3: `{p | ρ ≤ |p.1| ∧ |p.2| ≤ ρ}`
  let S₃ : Set (ℝ × ℝ) := {p : ℝ × ℝ | ρ ≤ |p.1| ∧ |p.2| ≤ ρ}
  have hS₃_meas : MeasurableSet S₃ :=
    (isClosed_le continuous_const (continuous_abs.comp continuous_fst)).measurableSet.inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const).measurableSet
  have hS₃ : IntegrableOn f S₃ volume := by
    rw [← integrable_indicator_iff hS₃_meas]
    let g : ℝ × ℝ → ℝ := S₃.indicator f
    change Integrable g volume
    have hg_meas : AEStronglyMeasurable g volume :=
      hf_cont.aestronglyMeasurable.indicator hS₃_meas
    rw [Measure.volume_eq_prod, integrable_prod_iff hg_meas]
    have hslice_int : ∀ x : ℝ, Integrable (fun y : ℝ => g (x, y)) volume := fun x => by
      by_cases hx : ρ ≤ |x|
      · have hcont_y : ContinuousOn (fun y : ℝ => f (x, y)) (Icc (-ρ) ρ) :=
          (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
        have hint_y : IntegrableOn (fun y : ℝ => f (x, y)) (Icc (-ρ) ρ) volume :=
          hcont_y.integrableOn_Icc
        refine hint_y.integrable_indicator measurableSet_Icc |>.congr (Eventually.of_forall fun y => ?_)
        by_cases hy : |y| ≤ ρ
        · have hy_mem : y ∈ Icc (-ρ) ρ := abs_le.mp hy
          simp [g, S₃, Set.indicator, hx, hy, hy_mem]
        · have hy_nmem : y ∉ Icc (-ρ) ρ := fun h => hy (abs_le.mpr ⟨h.1, h.2⟩)
          simp [g, S₃, Set.indicator, hx, hy, hy_nmem]
      · simp [g, S₃, Set.indicator, hx, integrable_zero]
    refine ⟨Eventually.of_forall hslice_int, ?_⟩
    -- Now bound `x ↦ ∫ y, g (x, y)` using `spin_slice_L1_le_L1_sq` and Young's inequality
    set ε : ℝ := min (1 / 2) ((1 - 2 * θ) / 2)
    have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    have hε_lt : ε ≤ (1 - 2 * θ) / 2 := min_le_right _ _
    set δ : ℝ := 2 * π * Real.sqrt a * (1 - ε) - 4 * π * Real.sqrt a * θ
    have hδ : 0 < δ := by
      have h1 : 0 < 1 - ε - 2 * θ := by linarith
      calc δ = 2 * π * Real.sqrt a * (1 - ε - 2 * θ) := by dsimp [δ]; ring
        _ > 0 := by positivity
    obtain ⟨C_s, hC_s, hslice_bd'⟩ := spin_slice_L1_le_L1_sq ha hε0 hε1
    have hslice_bd := hslice_bd' hΦ
    set M₀ : ℝ := spinITheta a (1 / 24) Φ
    have hM₀_nn : 0 ≤ M₀ := by dsimp [M₀]; unfold spinITheta; exact integral_nonneg fun p => by positivity
    set C_c : ℝ := Real.cosh (4 * π * Real.sqrt a * θ * ρ)
    have hC_c : 0 ≤ C_c := (Real.cosh_pos _).le
    have hM2_x : Integrable (fun x : ℝ => ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y) volume := by
      have h := hΦ.int_M2
      rw [Measure.volume_eq_prod] at h
      exact h.integral_prod_left
    have hM2_ae : ∀ᵐ x ∂volume, Integrable (fun y : ℝ => |Φ (x, y)| * spinV1 a x * spinV1 a y) volume := by
      have h := hΦ.int_M2
      rw [Measure.volume_eq_prod] at h
      exact h.prod_right_ae
    have hdom_x : Integrable (fun x : ℝ =>
        C_c * C_s * (ε * (M₀ + 1) * Real.exp (-δ * |x|) +
          (1 - ε) * (c_tail * c_core * ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y))) volume := by
      refine ((integrable_exp_neg_mul_abs hδ).const_mul (ε * (M₀ + 1))).add
        ((hM2_x.const_mul (c_tail * c_core)).const_mul (1 - ε)) |>.const_mul (C_c * C_s)
    refine hdom_x.mono' ?_ ?_
    · have hg_meas' : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖g p‖) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hg_meas.norm
      exact hg_meas'.integral_prod_right'
    · filter_upwards [hM2_ae] with x hint_M2y
      have hnorm_g : ∀ y : ℝ, ‖g (x, y)‖ = g (x, y) := fun y =>
        Real.norm_of_nonneg (Set.indicator_nonneg (fun p _ => hf_nn p) _)
      simp_rw [hnorm_g]
      have hg_nn : 0 ≤ ∫ y : ℝ, g (x, y) := integral_nonneg fun y =>
        Set.indicator_nonneg (fun p _ => hf_nn p) _
      rw [Real.norm_of_nonneg hg_nn]
      by_cases hx : ρ ≤ |x|
      · have hgy_eq : ∫ y : ℝ, g (x, y) = ∫ y in Icc (-ρ) ρ, f (x, y) := by
          have hind : (fun y : ℝ => g (x, y)) = (Icc (-ρ) ρ).indicator (fun y => f (x, y)) := by
            ext y
            by_cases hy : |y| ≤ ρ
            · have hy_mem : y ∈ Icc (-ρ) ρ := abs_le.mp hy
              simp [g, S₃, Set.indicator, hx, hy, hy_mem]
            · have hy_nmem : y ∉ Icc (-ρ) ρ := fun h => hy (abs_le.mpr ⟨h.1, h.2⟩)
              simp [g, S₃, Set.indicator, hx, hy, hy_nmem]
          rw [hind, integral_indicator measurableSet_Icc]
        rw [hgy_eq]
        have hcont_y : Continuous (fun y : ℝ => |Φ (x, y)|) :=
          (hΦ.cont.comp (continuous_const.prodMk continuous_id)).abs
        have hfy_le : ∫ y in Icc (-ρ) ρ, f (x, y) ≤
            Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c * ∫ y in Icc (-ρ) ρ, |Φ (x, y)| := by
          have hint_f : IntegrableOn (fun y : ℝ => f (x, y)) (Icc (-ρ) ρ) volume :=
            (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
          have hint_abs : IntegrableOn (fun y : ℝ => |Φ (x, y)|) (Icc (-ρ) ρ) volume :=
            hcont_y.continuousOn.integrableOn_Icc
          calc ∫ y in Icc (-ρ) ρ, f (x, y)
              ≤ ∫ y in Icc (-ρ) ρ, (Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c) * |Φ (x, y)| := by
                refine setIntegral_mono_on hint_f (hint_abs.const_mul _) measurableSet_Icc fun y hy => ?_
                have hcy : Real.cosh (4 * π * Real.sqrt a * θ * y) ≤ C_c := by
                  rw [← Real.cosh_abs (4 * π * Real.sqrt a * θ * y)]
                  dsimp [C_c]
                  rw [← Real.cosh_abs (4 * π * Real.sqrt a * θ * ρ), Real.cosh_le_cosh,
                    abs_of_nonneg (abs_nonneg _), abs_of_nonneg (abs_nonneg _),
                    abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ * ρ),
                    abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ)]
                  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hy.1, hy.2⟩) (by positivity)
                dsimp [f]
                calc |Φ (x, y)| * Real.cosh (4 * π * Real.sqrt a * θ * x) *
                        Real.cosh (4 * π * Real.sqrt a * θ * y)
                    ≤ |Φ (x, y)| * Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c := by
                      gcongr
                  _ = (Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c) * |Φ (x, y)| := by ring
            _ = Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c * ∫ y in Icc (-ρ) ρ, |Φ (x, y)| := by
                rw [integral_const_mul]
        set Q : ℝ := ∫ y in Icc (-ρ) ρ, |Φ (x, y)| * y ^ 2
        have hQ_nn : 0 ≤ Q := setIntegral_nonneg measurableSet_Icc fun y _ => by positivity
        have hQ_le_M2 : Real.exp (2 * π * Real.sqrt a * |x|) * Q ≤
            c_tail * c_core * ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y := by
          have hint_q : IntegrableOn (fun y : ℝ => |Φ (x, y)| * y ^ 2) (Icc (-ρ) ρ) volume :=
            (hcont_y.mul (continuous_pow 2)).continuousOn.integrableOn_Icc
          have h1 : Real.exp (2 * π * Real.sqrt a * |x|) * Q =
              ∫ y in Icc (-ρ) ρ, Real.exp (2 * π * Real.sqrt a * |x|) * (|Φ (x, y)| * y ^ 2) := by
            rw [← integral_const_mul]
          have h2 : ∫ y in Icc (-ρ) ρ, Real.exp (2 * π * Real.sqrt a * |x|) * (|Φ (x, y)| * y ^ 2) ≤
              ∫ y in Icc (-ρ) ρ, c_tail * c_core * (|Φ (x, y)| * spinV1 a x * spinV1 a y) := by
            refine setIntegral_mono_on (hint_q.const_mul _) (hint_M2y.integrableOn.const_mul _)
              measurableSet_Icc fun y hy => ?_
            have hx_v := hv1_tail x hx
            have hy_v := hv1_core y (abs_le.mpr ⟨hy.1, hy.2⟩)
            calc Real.exp (2 * π * Real.sqrt a * |x|) * (|Φ (x, y)| * y ^ 2)
                ≤ (c_tail * spinV1 a x) * (|Φ (x, y)| * (c_core * spinV1 a y)) := by
                  refine mul_le_mul hx_v (mul_le_mul_of_nonneg_left hy_v (abs_nonneg _))
                    (by positivity) (mul_nonneg hc_tail.le (spinV1_nonneg ha x))
              _ = c_tail * c_core * (|Φ (x, y)| * spinV1 a x * spinV1 a y) := by ring
          have h3 : ∫ y in Icc (-ρ) ρ, |Φ (x, y)| * spinV1 a x * spinV1 a y ≤
              ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y :=
            setIntegral_le_integral hint_M2y (Eventually.of_forall fun y =>
              mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha x)) (spinV1_nonneg ha y))
          rw [h1]
          calc ∫ y in Icc (-ρ) ρ, Real.exp (2 * π * Real.sqrt a * |x|) * (|Φ (x, y)| * y ^ 2)
              ≤ ∫ y in Icc (-ρ) ρ, c_tail * c_core * (|Φ (x, y)| * spinV1 a x * spinV1 a y) := h2
            _ = c_tail * c_core * ∫ y in Icc (-ρ) ρ, |Φ (x, y)| * spinV1 a x * spinV1 a y := by
                rw [integral_const_mul]
            _ ≤ c_tail * c_core * ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y := by gcongr
        have hcosh_split : Real.cosh (4 * π * Real.sqrt a * θ * x) ≤
            Real.exp (-δ * |x|) * (Real.exp (2 * π * Real.sqrt a * |x|)) ^ (1 - ε) := by
          have h1 : Real.cosh (4 * π * Real.sqrt a * θ * x) ≤
              Real.exp (4 * π * Real.sqrt a * θ * |x|) := by
            rw [← Real.cosh_abs, Real.cosh_eq]
            have ha1 : |4 * π * Real.sqrt a * θ * x| = 4 * π * Real.sqrt a * θ * |x| := by
              rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ)]
            rw [ha1]
            have hexp_le : Real.exp (-(4 * π * Real.sqrt a * θ * |x|)) ≤
                Real.exp (4 * π * Real.sqrt a * θ * |x|) :=
              Real.exp_le_exp.mpr (by linarith [show 0 ≤ 4 * π * Real.sqrt a * θ * |x| by positivity])
            linarith
          have h2 : Real.exp (4 * π * Real.sqrt a * θ * |x|) =
              Real.exp (-δ * |x|) * (Real.exp (2 * π * Real.sqrt a * |x|)) ^ (1 - ε) := by
            rw [← Real.exp_mul, ← Real.exp_add]
            congr 1; dsimp [δ]; ring
          exact h1.trans_eq h2
        have hyoung : (M₀ + 1) ^ ε * (Real.exp (2 * π * Real.sqrt a * |x|) * Q) ^ (1 - ε) ≤
            ε * (M₀ + 1) + (1 - ε) * (Real.exp (2 * π * Real.sqrt a * |x|) * Q) :=
          Real.geom_mean_le_arith_mean2_weighted hε0.le (by linarith) (by linarith) (by positivity)
            (by ring)
        have h1me : 0 ≤ 1 - ε := by linarith
        have hexp_le1 : Real.exp (-δ * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg x])
        calc ∫ y in Icc (-ρ) ρ, f (x, y)
            ≤ Real.cosh (4 * π * Real.sqrt a * θ * x) * C_c * ∫ y in Icc (-ρ) ρ, |Φ (x, y)| := hfy_le
          _ ≤ (Real.exp (-δ * |x|) * (Real.exp (2 * π * Real.sqrt a * |x|)) ^ (1 - ε)) * C_c *
                (C_s * (M₀ + 1) ^ ε * Q ^ (1 - ε)) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right hcosh_split hC_c) (hslice_bd x)
                (setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _)
                (mul_nonneg (by positivity) hC_c)
          _ = C_c * C_s * (Real.exp (-δ * |x|) *
                ((M₀ + 1) ^ ε * (Real.exp (2 * π * Real.sqrt a * |x|) * Q) ^ (1 - ε))) := by
              rw [Real.mul_rpow (Real.exp_pos _).le hQ_nn]; ring
          _ ≤ C_c * C_s * (Real.exp (-δ * |x|) *
                (ε * (M₀ + 1) + (1 - ε) * (Real.exp (2 * π * Real.sqrt a * |x|) * Q))) := by gcongr
          _ = C_c * C_s * (ε * (M₀ + 1) * Real.exp (-δ * |x|) +
                Real.exp (-δ * |x|) * ((1 - ε) * (Real.exp (2 * π * Real.sqrt a * |x|) * Q))) := by ring
          _ ≤ C_c * C_s * (ε * (M₀ + 1) * Real.exp (-δ * |x|) +
                1 * ((1 - ε) * (c_tail * c_core * ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y))) := by
              gcongr
          _ = C_c * C_s * (ε * (M₀ + 1) * Real.exp (-δ * |x|) +
                (1 - ε) * (c_tail * c_core * ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y)) := by ring
      · have hg0 : (fun y : ℝ => g (x, y)) = fun _ => 0 := by
          ext y; simp [g, S₃, hx]
        rw [hg0, integral_zero]
        have h1 : 0 ≤ ε * (M₀ + 1) * Real.exp (-δ * |x|) := by positivity
        have h2 : 0 ≤ ∫ y : ℝ, |Φ (x, y)| * spinV1 a x * spinV1 a y :=
          integral_nonneg fun y => mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha x))
            (spinV1_nonneg ha y)
        have h3 : 0 ≤ 1 - ε := by linarith
        refine mul_nonneg (mul_nonneg hC_c hC_s.le)
          (add_nonneg h1 (mul_nonneg h3 (mul_nonneg (mul_nonneg hc_tail.le hc_core.le) h2)))
  -- Region 4: `{p | |p.1| ≤ ρ ∧ ρ ≤ |p.2|}`, by swap symmetry from `S₃`
  let S₄ : Set (ℝ × ℝ) := {p : ℝ × ℝ | |p.1| ≤ ρ ∧ ρ ≤ |p.2|}
  have hS₄ : IntegrableOn f S₄ volume := by
    have hswap_mp : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) volume volume :=
      Measure.measurePreserving_swap
    have hpre : (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) ⁻¹' S₃ = S₄ := by
      ext p; simp [S₃, S₄, and_comm, MeasurableEquiv.prodComm]
    have hcomp := (hswap_mp.integrableOn_comp_preimage
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ).measurableEmbedding (s := S₃)).mpr hS₃
    rw [hpre] at hcomp
    refine hcomp.congr_fun (fun p _ => ?_) ?_
    · dsimp [f]
      simp only [MeasurableEquiv.prodComm, MeasurableEquiv.coe_mk, Equiv.prodComm_apply, Prod.swap]
      rw [hΦ.d4_inv.2.2 p.1 p.2]
      ring
    · exact (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).measurableSet.inter
        (isClosed_le continuous_const (continuous_abs.comp continuous_snd)).measurableSet
  -- Union of the four regions is `univ`
  have huniv : (Set.univ : Set (ℝ × ℝ)) = S₁ ∪ S₂ ∪ S₃ ∪ S₄ := by
    ext p
    simp only [Set.mem_univ, Set.mem_union, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq,
      true_iff, S₁, S₂, S₃, S₄]
    rcases le_or_gt |p.1| ρ with h1 | h1 <;> rcases le_or_gt |p.2| ρ with h2 | h2
    · left; left; left; exact ⟨abs_le.mp h1, abs_le.mp h2⟩
    · right; exact ⟨h1, h2.le⟩
    · left; right; exact ⟨h1.le, h2⟩
    · left; left; right; exact ⟨h1.le, h2.le⟩
  rw [← integrableOn_univ, huniv]
  exact ((hS₁.union hS₂).union hS₃).union hS₄

/-! ### Section 4: Analyticity of `spinGeff` on `spinStrip (1 / 2)` -/

private lemma norm_complex_cosh_ge {w : ℂ} (hw : |w.im| ≤ 1 / 4) :
    1 / Real.sqrt 2 * Real.cosh w.re ≤ ‖Complex.cosh w‖ := by
  have hcos_eq : Complex.cosh w =
      (Real.cosh w.re * Real.cos w.im : ℝ) + (Real.sinh w.re * Real.sin w.im : ℝ) * I := by
    apply Complex.ext
    · simp [Complex.cosh, Complex.exp_re, Real.cosh_eq, Real.cos_neg, -Complex.ofReal_cos]; ring
    · simp [Complex.cosh, Complex.exp_im, Real.sinh_eq, Real.sin_neg, -Complex.ofReal_sin,
        ← Complex.ofReal_exp]; ring
  have hnorm_sq : ‖Complex.cosh w‖ ^ 2 = Real.cosh w.re ^ 2 - Real.sin w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hcos_eq, Complex.normSq_add_mul_I]
    have hch : Real.cosh w.re ^ 2 - Real.sinh w.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    have hcs : Real.cos w.im ^ 2 + Real.sin w.im ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    nlinarith
  have hsin_le : Real.sin w.im ^ 2 ≤ 1 / 2 := by
    have h1 : |Real.sin w.im| ≤ 1 / 4 := (Real.abs_sin_le_abs).trans hw
    have h2 : Real.sin w.im ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      rw [← sq_abs (Real.sin w.im)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    linarith
  have hch1 : 1 ≤ Real.cosh w.re ^ 2 := one_le_pow₀ (Real.one_le_cosh _)
  have hsq : (1 / Real.sqrt 2 * Real.cosh w.re) ^ 2 ≤ ‖Complex.cosh w‖ ^ 2 := by
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num), hnorm_sq]
    linarith
  exact le_of_sq_le_sq hsq (norm_nonneg _)

private lemma norm_complex_sinh_le (w : ℂ) : ‖Complex.sinh w‖ ≤ Real.cosh w.re := by
  have hsin_eq : Complex.sinh w =
      (Real.sinh w.re * Real.cos w.im : ℝ) + (Real.cosh w.re * Real.sin w.im : ℝ) * I := by
    apply Complex.ext
    · simp [Complex.sinh, Complex.exp_re, Real.sinh_eq, Real.cos_neg, ← Complex.ofReal_cos]; ring
    · simp [Complex.sinh, Complex.exp_im, Real.cosh_eq, Real.sin_neg, ← Complex.ofReal_sin,
        ← Complex.ofReal_exp]; ring
  have hsq : ‖Complex.sinh w‖ ^ 2 ≤ Real.cosh w.re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hsin_eq, Complex.normSq_add_mul_I]
    have hch : Real.cosh w.re ^ 2 - Real.sinh w.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    have hcs : Real.cos w.im ^ 2 + Real.sin w.im ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.cosh w.re)]
  exact le_of_sq_le_sq hsq (Real.cosh_pos _).le

private lemma complex_tanh_bound_and_deriv {w : ℂ} (hw : |w.im| ≤ 1 / 4) :
    Complex.cosh w ≠ 0 ∧ ‖Complex.tanh w‖ ≤ Real.sqrt 2 ∧
      HasDerivAt Complex.tanh (1 / Complex.cosh w ^ 2) w ∧
      ‖1 / Complex.cosh w ^ 2‖ ≤ 2 := by
  have hch_ge := norm_complex_cosh_ge hw
  have hch_pos : 0 < ‖Complex.cosh w‖ := lt_of_lt_of_le (by positivity) hch_ge
  have hch_ne : Complex.cosh w ≠ 0 := norm_ne_zero_iff.mp hch_pos.ne'
  refine ⟨hch_ne, ?_, ?_, ?_⟩
  · rw [Complex.tanh_eq_sinh_div_cosh, norm_div]
    calc ‖Complex.sinh w‖ / ‖Complex.cosh w‖
        ≤ Real.cosh w.re / (1 / Real.sqrt 2 * Real.cosh w.re) :=
          div_le_div₀ (Real.cosh_pos _).le (norm_complex_sinh_le w) (by positivity) hch_ge
      _ = Real.sqrt 2 := by field_simp [(Real.cosh_pos w.re).ne']
  · have hd := (Complex.hasDerivAt_sinh w).div (Complex.hasDerivAt_cosh w) hch_ne
    have hfn : Complex.sinh / Complex.cosh = Complex.tanh := by
      ext z; exact (Complex.tanh_eq_sinh_div_cosh z).symm
    rw [hfn] at hd
    refine hd.congr_deriv ?_
    have h1 : Complex.cosh w * Complex.cosh w - Complex.sinh w * Complex.sinh w = 1 := by
      simpa [sq] using Complex.cosh_sq_sub_sinh_sq w
    rw [h1]
  · rw [norm_div, norm_one, norm_pow]
    have h1 : 1 / 2 ≤ ‖Complex.cosh w‖ ^ 2 := by
      have hsq : (1 / Real.sqrt 2 * Real.cosh w.re) ^ 2 ≤ ‖Complex.cosh w‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hch_ge 2
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)] at hsq
      have hch1 : 1 ≤ Real.cosh w.re ^ 2 := one_le_pow₀ (Real.one_le_cosh _)
      linarith
    calc 1 / ‖Complex.cosh w‖ ^ 2 ≤ 1 / (1 / 2) := div_le_div_of_nonneg_left zero_le_one (by norm_num) h1
      _ = 2 := by norm_num

private lemma spinHb_bound_and_deriv {b : ℂ} (hb : |b.im| ≤ 1 / 2) (d : ℝ) :
    ∃ f' : ℂ, HasDerivAt (fun w : ℂ => spinHb w d) f' b ∧
      ‖spinHb b d‖ ≤ 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) *
        Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) ∧
      ‖f'‖ ≤ (128 / 9 * (1 + ‖b‖) + 32 / 3 * Real.sqrt 2) *
        (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
  have hb_re : 3 / 4 ≤ (1 + b ^ 2).re := by
    simp only [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
    nlinarith [sq_nonneg b.re, sq_abs b.im, pow_le_pow_left₀ (abs_nonneg b.im) hb 2]
  have hb_norm : 3 / 4 ≤ ‖1 + b ^ 2‖ := hb_re.trans (Complex.re_le_norm _)
  have hb_ne : 1 + b ^ 2 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hw1 : |((b + (d : ℂ)) / 2).im| ≤ 1 / 4 := by
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, add_zero]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hw2 : |((b - (d : ℂ)) / 2).im| ≤ 1 / 4 := by
    simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  obtain ⟨_, ht1_bd, ht1_d, ht1_d_bd⟩ := complex_tanh_bound_and_deriv hw1
  obtain ⟨_, ht2_bd, ht2_d, ht2_d_bd⟩ := complex_tanh_bound_and_deriv hw2
  let t1 : ℂ → ℂ := fun w => Complex.tanh ((w + (d : ℂ)) / 2) ^ 2
  let t2 : ℂ → ℂ := fun w => Complex.tanh ((w - (d : ℂ)) / 2) ^ 2
  have ht1' : HasDerivAt t1 (2 * Complex.tanh ((b + (d : ℂ)) / 2) * (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2))) b := by
    have ha : HasDerivAt (fun w : ℂ => (w + (d : ℂ)) / 2) (1 / 2) b := by
      simpa using ((hasDerivAt_id b).add_const (d : ℂ)).div_const (2 : ℂ)
    refine ((ht1_d.comp b ha).pow 2).congr_deriv ?_
    simp only [Function.comp_apply, one_div]; ring
  have ht2' : HasDerivAt t2 (2 * Complex.tanh ((b - (d : ℂ)) / 2) * (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2))) b := by
    have ha : HasDerivAt (fun w : ℂ => (w - (d : ℂ)) / 2) (1 / 2) b := by
      simpa using ((hasDerivAt_id b).sub_const (d : ℂ)).div_const (2 : ℂ)
    refine ((ht2_d.comp b ha).pow 2).congr_deriv ?_
    simp only [Function.comp_apply, one_div]; ring
  have hinv' : HasDerivAt (fun w : ℂ => ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + w ^ 2))
      (-(((1 + xiStar ^ 2 : ℝ) : ℂ) * (2 * b) / (1 + b ^ 2) ^ 2)) b := by
    have hden : HasDerivAt (fun w : ℂ => 1 + w ^ 2) (2 * b) b := by
      simpa using ((hasDerivAt_pow 2 b).const_add (1 : ℂ))
    exact (hden.inv hb_ne).const_mul ((1 + xiStar ^ 2 : ℝ) : ℂ) |>.congr_deriv (by ring)
  have hprod := (hinv'.mul (ht1'.mul ht2')).div_const ((Real.tanh (xiStar / 2) ^ 4 : ℝ) : ℂ) |>.mul_const
    (Complex.exp (-(((d ^ 2 / spinSigma0 ^ 2 : ℝ) : ℂ))))
  refine ⟨_, HasDerivAt.congr_of_eventuallyEq hprod (Eventually.of_forall fun w => by
    unfold spinHb; dsimp [t1, t2]), ?_, ?_⟩
  · have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
    have hexp_n : ‖Complex.exp (-(((d ^ 2 / spinSigma0 ^ 2 : ℝ) : ℂ)))‖ =
        Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
    have hinv_n : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ ≤ (1 + xiStar ^ 2) * (4 / 3) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (1 + xiStar ^ 2) / ‖1 + b ^ 2‖ ≤ (1 + xiStar ^ 2) / (3 / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hb_norm
        _ = (1 + xiStar ^ 2) * (4 / 3) := by ring
    have ht12_n : ‖Complex.tanh ((b + (d : ℂ)) / 2) ^ 2 * Complex.tanh ((b - (d : ℂ)) / 2) ^ 2‖ ≤ 4 := by
      rw [norm_mul, norm_pow, norm_pow]
      have h1 : ‖Complex.tanh ((b + (d : ℂ)) / 2)‖ ^ 2 ≤ 2 := by
        calc ‖Complex.tanh ((b + (d : ℂ)) / 2)‖ ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ht1_bd 2
          _ = 2 := Real.sq_sqrt (by norm_num)
      have h2 : ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ ^ 2 ≤ 2 := by
        calc ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ht2_bd 2
          _ = 2 := Real.sq_sqrt (by norm_num)
      linarith [mul_le_mul h1 h2 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)]
    unfold spinHb
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi, hexp_n]
    have hmul : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ *
          ‖Complex.tanh ((b + (d : ℂ)) / 2) ^ 2 * Complex.tanh ((b - (d : ℂ)) / 2) ^ 2‖ ≤
        (1 + xiStar ^ 2) * (4 / 3) * 4 :=
      mul_le_mul hinv_n ht12_n (norm_nonneg _) (by positivity)
    calc ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ *
          ‖Complex.tanh ((b + (d : ℂ)) / 2) ^ 2 * Complex.tanh ((b - (d : ℂ)) / 2) ^ 2‖ /
          Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
        ≤ ((1 + xiStar ^ 2) * (4 / 3) * 4) / Real.tanh (xiStar / 2) ^ 4 *
            Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by gcongr
      _ = 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) *
            Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by ring
  · have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
    have hexp_n : ‖Complex.exp (-(((d ^ 2 / spinSigma0 ^ 2 : ℝ) : ℂ)))‖ =
        Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
    -- Clean norm bound on the derivative
    have h1 : ‖Complex.tanh ((b + (d : ℂ)) / 2)‖ ^ 2 ≤ 2 := by
      calc ‖Complex.tanh ((b + (d : ℂ)) / 2)‖ ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ht1_bd 2
        _ = 2 := Real.sq_sqrt (by norm_num)
    have h2 : ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ ^ 2 ≤ 2 := by
      calc ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ht2_bd 2
        _ = 2 := Real.sq_sqrt (by norm_num)
    have ht1'_bd : ‖2 * Complex.tanh ((b + (d : ℂ)) / 2) *
        (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2))‖ ≤ 2 * Real.sqrt 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc 2 * ‖Complex.tanh ((b + (d : ℂ)) / 2)‖ * (‖1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2‖ * (1 / 2))
          ≤ 2 * Real.sqrt 2 * (2 * (1 / 2)) := by gcongr
        _ = 2 * Real.sqrt 2 := by ring
    have ht2'_bd : ‖2 * Complex.tanh ((b - (d : ℂ)) / 2) *
        (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2))‖ ≤ 2 * Real.sqrt 2 := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
        show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc 2 * ‖Complex.tanh ((b - (d : ℂ)) / 2)‖ * (‖1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2‖ * (1 / 2))
          ≤ 2 * Real.sqrt 2 * (2 * (1 / 2)) := by gcongr
        _ = 2 * Real.sqrt 2 := by ring
    have hinv_bd : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ ≤ (1 + xiStar ^ 2) * (4 / 3) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (1 + xiStar ^ 2) / ‖1 + b ^ 2‖ ≤ (1 + xiStar ^ 2) / (3 / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hb_norm
        _ = (1 + xiStar ^ 2) * (4 / 3) := by ring
    have hinv'_bd : ‖-(((1 + xiStar ^ 2 : ℝ) : ℂ) * (2 * b) / (1 + b ^ 2) ^ 2)‖ ≤
        (1 + xiStar ^ 2) * (32 / 9 * ‖b‖) := by
      rw [norm_neg, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), Complex.norm_ofNat, norm_pow]
      have hden : (3 / 4 : ℝ) ^ 2 ≤ ‖1 + b ^ 2‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hb_norm 2
      calc (1 + xiStar ^ 2) * (2 * ‖b‖) / ‖1 + b ^ 2‖ ^ 2
          ≤ (1 + xiStar ^ 2) * (2 * ‖b‖) / (3 / 4 : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = (1 + xiStar ^ 2) * (32 / 9 * ‖b‖) := by ring
    have ht12_bd : ‖t1 b * t2 b‖ ≤ 4 := by
      dsimp [t1, t2]; rw [norm_mul, norm_pow, norm_pow]
      linarith [mul_le_mul h1 h2 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)]
    have ht12'_bd : ‖2 * Complex.tanh ((b + (d : ℂ)) / 2) * (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2)) * t2 b +
        t1 b * (2 * Complex.tanh ((b - (d : ℂ)) / 2) * (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2)))‖ ≤
        8 * Real.sqrt 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul _ (t2 b), norm_mul (t1 b)]
      have ht1_n : ‖t1 b‖ ≤ 2 := by dsimp [t1]; rw [norm_pow]; exact h1
      have ht2_n : ‖t2 b‖ ≤ 2 := by dsimp [t2]; rw [norm_pow]; exact h2
      have hA : ‖2 * Complex.tanh ((b + (d : ℂ)) / 2) * (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2))‖ * ‖t2 b‖ ≤
          (2 * Real.sqrt 2) * 2 := mul_le_mul ht1'_bd ht2_n (norm_nonneg _) (by positivity)
      have hB : ‖t1 b‖ * ‖2 * Complex.tanh ((b - (d : ℂ)) / 2) * (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2))‖ ≤
          2 * (2 * Real.sqrt 2) := mul_le_mul ht1_n ht2'_bd (norm_nonneg _) (by positivity)
      linarith
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi, hexp_n]
    have hnorm_sum : ‖-(((1 + xiStar ^ 2 : ℝ) : ℂ) * (2 * b) / (1 + b ^ 2) ^ 2) * (t1 b * t2 b) +
        ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2) *
          (2 * Complex.tanh ((b + (d : ℂ)) / 2) * (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2)) * t2 b +
          t1 b * (2 * Complex.tanh ((b - (d : ℂ)) / 2) * (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2))))‖ ≤
        (128 / 9 * (1 + ‖b‖) + 32 / 3 * Real.sqrt 2) * (1 + xiStar ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul _ (t1 b * t2 b), norm_mul (((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2))]
      have hA : ‖-(((1 + xiStar ^ 2 : ℝ) : ℂ) * (2 * b) / (1 + b ^ 2) ^ 2)‖ * ‖t1 b * t2 b‖ ≤
          (1 + xiStar ^ 2) * (32 / 9 * ‖b‖) * 4 :=
        mul_le_mul hinv'_bd ht12_bd (norm_nonneg _) (by positivity)
      have hB : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ *
          ‖2 * Complex.tanh ((b + (d : ℂ)) / 2) * (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2)) * t2 b +
          t1 b * (2 * Complex.tanh ((b - (d : ℂ)) / 2) * (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2)))‖ ≤
          (1 + xiStar ^ 2) * (4 / 3) * (8 * Real.sqrt 2) :=
        mul_le_mul hinv_bd ht12'_bd (norm_nonneg _) (by positivity)
      nlinarith [show (0 : ℝ) ≤ 1 + xiStar ^ 2 by positivity, norm_nonneg b]
    calc ‖-(((1 + xiStar ^ 2 : ℝ) : ℂ) * (2 * b) / (1 + b ^ 2) ^ 2) * (t1 b * t2 b) +
          ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2) *
            (2 * Complex.tanh ((b + (d : ℂ)) / 2) * (1 / Complex.cosh ((b + (d : ℂ)) / 2) ^ 2 * (1 / 2)) * t2 b +
            t1 b * (2 * Complex.tanh ((b - (d : ℂ)) / 2) * (1 / Complex.cosh ((b - (d : ℂ)) / 2) ^ 2 * (1 / 2))))‖ /
          Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
        ≤ (128 / 9 * (1 + ‖b‖) + 32 / 3 * Real.sqrt 2) * (1 + xiStar ^ 2) /
            Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by gcongr
      _ = (128 / 9 * (1 + ‖b‖) + 32 / 3 * Real.sqrt 2) * (1 + xiStar ^ 2) /
            Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := rfl

lemma cosh_mul_im_le_cosh {a θ r im : ℝ} (ha : 0 < a) (hθ : 0 ≤ θ) (him : |im| ≤ θ) :
    Real.cosh (4 * π * Real.sqrt a * r * im) ≤ Real.cosh (4 * π * Real.sqrt a * θ * r) := by
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  rw [← Real.cosh_abs (4 * π * Real.sqrt a * r * im),
    ← Real.cosh_abs (4 * π * Real.sqrt a * θ * r), Real.cosh_le_cosh,
    abs_of_nonneg (abs_nonneg _), abs_of_nonneg (abs_nonneg _),
    show |4 * π * Real.sqrt a * r * im| = 4 * π * Real.sqrt a * |im| * |r| by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]; ring,
    show |4 * π * Real.sqrt a * θ * r| = 4 * π * Real.sqrt a * θ * |r| by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * π * Real.sqrt a * θ)]]
  calc 4 * π * Real.sqrt a * |im| * |r| ≤ 4 * π * Real.sqrt a * θ * |r| := by gcongr

private lemma spinGC_diag_bound_and_deriv {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2)
    {b : ℂ} (hb : |b.im| ≤ θ) (d : ℝ) :
    ‖spinGC a Φ (b + (d : ℂ)) (b - (d : ℂ))‖ ≤ spinITheta a θ Φ ∧
      ∃ g' : ℂ, HasDerivAt (fun w : ℂ => spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ))) g' b ∧
        ∀ θ₁ : ℝ, θ < θ₁ → θ₁ < 1 / 2 →
          ‖g'‖ ≤ (16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ))) * spinITheta a θ₁ Φ := by
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hint_θ : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
      Real.cosh (4 * π * Real.sqrt a * θ * p.2)) volume :=
    integrable_spinITheta ha hθ0 hθ1 hΦ
  have hdom : ∀ (w : ℂ) (hw : |w.im| ≤ θ) (p : ℝ × ℝ),
      ‖(Φ p : ℂ) * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (d : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (d : ℂ)))‖ ≤
      |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ * p.1) *
        Real.cosh (4 * π * Real.sqrt a * θ * p.2) := by
    intro w hw p
    have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (d : ℂ))).im =
        4 * π * Real.sqrt a * p.1 * w.im := by
      simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
    have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (d : ℂ))).im =
        4 * π * Real.sqrt a * p.2 * w.im := by
      simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
    have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (d : ℂ)))‖ ≤
        Real.cosh (4 * π * Real.sqrt a * θ * p.1) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * w.im) := by
            rw [← him1]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * p.1) :=
            cosh_mul_im_le_cosh ha0 hθ0.le hw
    have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (d : ℂ)))‖ ≤
        Real.cosh (4 * π * Real.sqrt a * θ * p.2) := by
      calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * w.im) := by
            rw [← him2]; exact norm_complex_cos_le_cosh _
        _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * p.2) :=
            cosh_mul_im_le_cosh ha0 hθ0.le hw
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
  refine ⟨?_, ?_⟩
  · unfold spinGC spinITheta
    rw [norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint_θ
      (Eventually.of_forall (hdom b hb))
  · -- Differentiability at `b` using `θmid := (θ + 1 / 2) / 2`
    set θm : ℝ := (θ + 1 / 2) / 2
    have hθm0 : 0 < θm := by dsimp [θm]; linarith
    have hθm1 : θm < 1 / 2 := by dsimp [θm]; linarith
    have hθ_lt_m : θ < θm := by dsimp [θm]; linarith
    set θu : ℝ := (θm + 1 / 2) / 2
    have hθu0 : 0 < θu := by dsimp [θu, θm]; linarith
    have hθu1 : θu < 1 / 2 := by dsimp [θu, θm]; linarith
    have hθmu : 0 < θu - θm := by dsimp [θu, θm]; linarith
    have hint_u : Integrable (fun p : ℝ × ℝ => |Φ p| * Real.cosh (4 * π * Real.sqrt a * θu * p.1) *
        Real.cosh (4 * π * Real.sqrt a * θu * p.2)) volume :=
      integrable_spinITheta ha hθu0 hθu1 hΦ
    set δ : ℝ := θm - θ
    have hδ : 0 < δ := by dsimp [δ]; linarith
    let c4 : ℂ := 4 * π * (Real.sqrt a : ℂ)
    let F : ℂ → ℝ × ℝ → ℂ := fun w p =>
      (Φ p : ℂ) * Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ))) *
        Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ)))
    let F' : ℂ → ℝ × ℝ → ℂ := fun w p =>
      -((Φ p : ℂ) * (Complex.sin (c4 * (p.1 : ℂ) * (w + (d : ℂ))) * (c4 * (p.1 : ℂ)) *
          Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ))) +
        Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ))) *
          (Complex.sin (c4 * (p.2 : ℂ) * (w - (d : ℂ))) * (c4 * (p.2 : ℂ)))))
    have hF_meas : ∀ᶠ w in 𝓝 b, AEStronglyMeasurable (F w) volume :=
      Eventually.of_forall fun w => by
        have hc0 : Continuous (F w) := by
          have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
          fun_prop
        exact hc0.aestronglyMeasurable
    have hF_int : Integrable (F b) volume :=
      hint_θ.mono' hF_meas.self_of_nhds (Eventually.of_forall (hdom b hb))
    have hF'_meas : AEStronglyMeasurable (F' b) volume := by
      have hc0 : Continuous (F' b) := by
        have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
        fun_prop
      exact hc0.aestronglyMeasurable
    have hF_deriv : ∀ᵐ p ∂volume, ∀ w ∈ Metric.ball b δ, HasDerivAt (fun z => F z p) (F' w p) w := by
      refine Eventually.of_forall fun p w _ => ?_
      have hd1 : HasDerivAt (fun z : ℂ => Complex.cos (c4 * (p.1 : ℂ) * (z + (d : ℂ))))
          (-Complex.sin (c4 * (p.1 : ℂ) * (w + (d : ℂ))) * (c4 * (p.1 : ℂ))) w := by
        have hi : HasDerivAt (fun z : ℂ => c4 * (p.1 : ℂ) * (z + (d : ℂ))) (c4 * (p.1 : ℂ)) w := by
          simpa using ((hasDerivAt_id w).add_const (d : ℂ)).const_mul (c4 * (p.1 : ℂ))
        exact (Complex.hasDerivAt_cos _).comp w hi
      have hd2 : HasDerivAt (fun z : ℂ => Complex.cos (c4 * (p.2 : ℂ) * (z - (d : ℂ))))
          (-Complex.sin (c4 * (p.2 : ℂ) * (w - (d : ℂ))) * (c4 * (p.2 : ℂ))) w := by
        have hi : HasDerivAt (fun z : ℂ => c4 * (p.2 : ℂ) * (z - (d : ℂ))) (c4 * (p.2 : ℂ)) w := by
          simpa using ((hasDerivAt_id w).sub_const (d : ℂ)).const_mul (c4 * (p.2 : ℂ))
        exact (Complex.hasDerivAt_cos _).comp w hi
      exact (((hd1.mul hd2).const_mul (Φ p : ℂ)).congr_of_eventuallyEq
        (Eventually.of_forall fun z => by dsimp [F]; ring)).congr_deriv (by dsimp [F']; ring)
    set K_u : ℝ := 16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θu - θm))
    let bound : ℝ × ℝ → ℝ := fun p =>
      K_u * (|Φ p| * Real.cosh (4 * π * Real.sqrt a * θu * p.1) *
        Real.cosh (4 * π * Real.sqrt a * θu * p.2))
    have hF'_bound : ∀ᵐ p ∂volume, ∀ w ∈ Metric.ball b δ, ‖F' w p‖ ≤ bound p := by
      refine Eventually.of_forall fun p w hw => ?_
      have hw_im : |w.im| ≤ θm := by
        have h1 : |w.im - b.im| ≤ ‖w - b‖ := by
          simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - b)
        have h2 : ‖w - b‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        linarith [abs_sub_abs_le_abs_sub w.im b.im]
      -- Helper for `|r| * cosh(4π√a θm |r|) ≤ (2 / (4π√a(θu - θm))) * cosh(4π√a θu |r|)`
      have hsc_bd : ∀ (r : ℝ) (z : ℂ), |z.im| ≤ θm →
          ‖Complex.sin (c4 * (r : ℂ) * z) * (c4 * (r : ℂ))‖ ≤
            (K_u / 2) * Real.cosh (4 * π * Real.sqrt a * θu * r) := by
        intro r z hz
        have him : (c4 * (r : ℂ) * z).im = 4 * π * Real.sqrt a * r * z.im := by
          dsimp [c4]; simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
        have hsin : ‖Complex.sin (c4 * (r : ℂ) * z)‖ ≤ Real.cosh (4 * π * Real.sqrt a * θm * |r|) := by
          calc ‖Complex.sin _‖ ≤ Real.cosh (4 * π * Real.sqrt a * r * z.im) := by
                rw [← him]; exact norm_complex_sin_le_cosh _
            _ ≤ Real.cosh (4 * π * Real.sqrt a * θm * r) :=
                cosh_mul_im_le_cosh ha0 hθm0.le hz
            _ = Real.cosh (4 * π * Real.sqrt a * θm * |r|) := by
                rw [← Real.cosh_abs (4 * π * Real.sqrt a * θm * r), abs_mul,
                  abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θm)]
        have hc4r : ‖c4 * (r : ℂ)‖ = 4 * π * Real.sqrt a * |r| := by
          dsimp [c4]
          rw [show (4 * π * (Real.sqrt a : ℂ) * (r : ℂ)) = ((4 * π * Real.sqrt a * r : ℝ) : ℂ) by
              push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]
        set α : ℝ := 4 * π * Real.sqrt a * (θu - θm)
        have hα : 0 < α := by dsimp [α]; positivity
        have hr_exp : |r| ≤ α⁻¹ * Real.exp (α * |r|) := by
          have := Real.add_one_le_exp (α * |r|)
          calc |r| = α⁻¹ * (α * |r|) := by field_simp [hα.ne']
            _ ≤ α⁻¹ * Real.exp (α * |r|) := by gcongr; linarith
        have hcosh_exp : Real.cosh (4 * π * Real.sqrt a * θm * |r|) * Real.exp (α * |r|) ≤
            2 * Real.cosh (4 * π * Real.sqrt a * θu * r) := by
          rw [← Real.cosh_abs (4 * π * Real.sqrt a * θu * r),
            show |4 * π * Real.sqrt a * θu * r| = 4 * π * Real.sqrt a * θu * |r| by
              rw [abs_mul, abs_of_pos (by positivity)]]
          set u : ℝ := 4 * π * Real.sqrt a * θm * |r|
          set v : ℝ := α * |r|
          have hu : 0 ≤ u := by positivity
          have huv : u + v = 4 * π * Real.sqrt a * θu * |r| := by dsimp [u, v, α]; ring
          have h1 : Real.cosh u ≤ Real.exp u := by
            rw [Real.cosh_eq]; linarith [Real.exp_le_exp.mpr (by linarith : -u ≤ u)]
          have h2 : Real.exp (u + v) ≤ 2 * Real.cosh (u + v) := by
            rw [Real.cosh_eq]; linarith [Real.exp_pos (-(u + v))]
          calc Real.cosh u * Real.exp v ≤ Real.exp u * Real.exp v := by gcongr
            _ = Real.exp (u + v) := (Real.exp_add u v).symm
            _ ≤ 2 * Real.cosh (u + v) := h2
            _ = 2 * Real.cosh (4 * π * Real.sqrt a * θu * |r|) := by rw [huv]
        rw [norm_mul, hc4r]
        calc ‖Complex.sin (c4 * (r : ℂ) * z)‖ * (4 * π * Real.sqrt a * |r|)
            ≤ Real.cosh (4 * π * Real.sqrt a * θm * |r|) *
                (4 * π * Real.sqrt a * (α⁻¹ * Real.exp (α * |r|))) := by gcongr
          _ = 4 * π * Real.sqrt a * α⁻¹ *
                (Real.cosh (4 * π * Real.sqrt a * θm * |r|) * Real.exp (α * |r|)) := by ring
          _ ≤ 4 * π * Real.sqrt a * α⁻¹ * (2 * Real.cosh (4 * π * Real.sqrt a * θu * r)) := by
              have hK_nn : 0 ≤ 4 * π * Real.sqrt a * α⁻¹ := by positivity
              exact mul_le_mul_of_nonneg_left hcosh_exp hK_nn
          _ = (K_u / 2) * Real.cosh (4 * π * Real.sqrt a * θu * r) := by
              dsimp [K_u, α]; ring
      have hc1 : ‖Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ)))‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θu * p.1) := by
        have him : (c4 * (p.1 : ℂ) * (w + (d : ℂ))).im = 4 * π * Real.sqrt a * p.1 * w.im := by
          dsimp [c4]; simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * w.im) := by
              rw [← him]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θu * p.1) :=
              cosh_mul_im_le_cosh ha0 hθu0.le (by linarith)
      have hc2 : ‖Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ)))‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θu * p.2) := by
        have him : (c4 * (p.2 : ℂ) * (w - (d : ℂ))).im = 4 * π * Real.sqrt a * p.2 * w.im := by
          dsimp [c4]; simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * w.im) := by
              rw [← him]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θu * p.2) :=
              cosh_mul_im_le_cosh ha0 hθu0.le (by linarith)
      have hs1 := hsc_bd p.1 (w + (d : ℂ)) (by simpa using hw_im)
      have hs2 := hsc_bd p.2 (w - (d : ℂ)) (by simpa using hw_im)
      dsimp [F']
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hsum : ‖Complex.sin (c4 * (p.1 : ℂ) * (w + (d : ℂ))) * (c4 * (p.1 : ℂ)) *
            Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ))) +
          Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ))) *
            (Complex.sin (c4 * (p.2 : ℂ) * (w - (d : ℂ))) * (c4 * (p.2 : ℂ)))‖ ≤
          K_u * Real.cosh (4 * π * Real.sqrt a * θu * p.1) *
            Real.cosh (4 * π * Real.sqrt a * θu * p.2) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul _ (Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ)))),
          norm_mul (Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ))))]
        have hA : ‖Complex.sin (c4 * (p.1 : ℂ) * (w + (d : ℂ))) * (c4 * (p.1 : ℂ))‖ *
              ‖Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ)))‖ ≤
            (K_u / 2) * Real.cosh (4 * π * Real.sqrt a * θu * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θu * p.2) :=
          mul_le_mul hs1 hc2 (norm_nonneg _) (by positivity)
        have hB : ‖Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ)))‖ *
              ‖Complex.sin (c4 * (p.2 : ℂ) * (w - (d : ℂ))) * (c4 * (p.2 : ℂ))‖ ≤
            Real.cosh (4 * π * Real.sqrt a * θu * p.1) *
              ((K_u / 2) * Real.cosh (4 * π * Real.sqrt a * θu * p.2)) :=
          mul_le_mul hc1 hs2 (norm_nonneg _) (Real.cosh_pos _).le
        linarith
      calc |Φ p| * ‖Complex.sin (c4 * (p.1 : ℂ) * (w + (d : ℂ))) * (c4 * (p.1 : ℂ)) *
              Complex.cos (c4 * (p.2 : ℂ) * (w - (d : ℂ))) +
            Complex.cos (c4 * (p.1 : ℂ) * (w + (d : ℂ))) *
              (Complex.sin (c4 * (p.2 : ℂ) * (w - (d : ℂ))) * (c4 * (p.2 : ℂ)))‖
          ≤ |Φ p| * (K_u * Real.cosh (4 * π * Real.sqrt a * θu * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θu * p.2)) :=
            mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = bound p := by dsimp [bound]; ring
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b hδ)
      hF_meas hF_int hF'_meas hF'_bound (hint_u.const_mul K_u) hF_deriv
    refine ⟨-(∫ p : ℝ × ℝ, F' b p), ?_, ?_⟩
    · have hfn : (fun w : ℂ => spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ))) =
          (fun w : ℂ => -(∫ p : ℝ × ℝ, F w p)) := rfl
      rw [hfn]
      exact hd.2.neg
    · intro θ₁ hθ_lt_1 hθ1_lt
      have hθ₁_pos : 0 < θ₁ := by linarith
      have hθ1_sub : 0 < θ₁ - θ := by linarith
      have hint_1 := integrable_spinITheta ha hθ₁_pos hθ1_lt hΦ
      -- Actually, `F' b` is bounded by `K₁ * spinITheta a θ₁ Φ` by the exact same `hsc_bd`!
      rw [norm_neg]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hbound_1 : ∀ p : ℝ × ℝ, ‖F' b p‖ ≤
          (16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ))) *
            (|Φ p| * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2)) := by
        intro p
        set K₁ := 16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ))
        set α₁ := 4 * π * Real.sqrt a * (θ₁ - θ)
        have hα₁ : 0 < α₁ := by dsimp [α₁]; positivity
        have hsc1 : ∀ (r : ℝ) (z : ℂ), |z.im| ≤ θ →
            ‖Complex.sin (c4 * (r : ℂ) * z) * (c4 * (r : ℂ))‖ ≤
              (K₁ / 2) * Real.cosh (4 * π * Real.sqrt a * θ₁ * r) := by
          intro r z hz
          have him : (c4 * (r : ℂ) * z).im = 4 * π * Real.sqrt a * r * z.im := by
            dsimp [c4]; simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
          have hsin : ‖Complex.sin (c4 * (r : ℂ) * z)‖ ≤ Real.cosh (4 * π * Real.sqrt a * θ * |r|) := by
            calc ‖Complex.sin _‖ ≤ Real.cosh (4 * π * Real.sqrt a * r * z.im) := by
                  rw [← him]; exact norm_complex_sin_le_cosh _
              _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * r) :=
                  cosh_mul_im_le_cosh ha0 hθ0.le hz
              _ = Real.cosh (4 * π * Real.sqrt a * θ * |r|) := by
                  rw [← Real.cosh_abs (4 * π * Real.sqrt a * θ * r), abs_mul,
                    abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * θ)]
          have hc4r : ‖c4 * (r : ℂ)‖ = 4 * π * Real.sqrt a * |r| := by
            dsimp [c4]
            rw [show (4 * π * (Real.sqrt a : ℂ) * (r : ℂ)) = ((4 * π * Real.sqrt a * r : ℝ) : ℂ) by
                push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]
          have hr_exp : |r| ≤ α₁⁻¹ * Real.exp (α₁ * |r|) := by
            have := Real.add_one_le_exp (α₁ * |r|)
            calc |r| = α₁⁻¹ * (α₁ * |r|) := by field_simp [hα₁.ne']
              _ ≤ α₁⁻¹ * Real.exp (α₁ * |r|) := by gcongr; linarith
          have hcosh_exp : Real.cosh (4 * π * Real.sqrt a * θ * |r|) * Real.exp (α₁ * |r|) ≤
              2 * Real.cosh (4 * π * Real.sqrt a * θ₁ * r) := by
            rw [← Real.cosh_abs (4 * π * Real.sqrt a * θ₁ * r),
              show |4 * π * Real.sqrt a * θ₁ * r| = 4 * π * Real.sqrt a * θ₁ * |r| by
                rw [abs_mul, abs_of_pos (by positivity)]]
            set u : ℝ := 4 * π * Real.sqrt a * θ * |r|
            set v : ℝ := α₁ * |r|
            have hu : 0 ≤ u := by positivity
            have huv : u + v = 4 * π * Real.sqrt a * θ₁ * |r| := by dsimp [u, v, α₁]; ring
            have h1 : Real.cosh u ≤ Real.exp u := by
              rw [Real.cosh_eq]; linarith [Real.exp_le_exp.mpr (by linarith : -u ≤ u)]
            have h2 : Real.exp (u + v) ≤ 2 * Real.cosh (u + v) := by
              rw [Real.cosh_eq]; linarith [Real.exp_pos (-(u + v))]
            calc Real.cosh u * Real.exp v ≤ Real.exp u * Real.exp v := by gcongr
              _ = Real.exp (u + v) := (Real.exp_add u v).symm
              _ ≤ 2 * Real.cosh (u + v) := h2
              _ = 2 * Real.cosh (4 * π * Real.sqrt a * θ₁ * |r|) := by rw [huv]
          rw [norm_mul, hc4r]
          calc ‖Complex.sin (c4 * (r : ℂ) * z)‖ * (4 * π * Real.sqrt a * |r|)
              ≤ Real.cosh (4 * π * Real.sqrt a * θ * |r|) *
                  (4 * π * Real.sqrt a * (α₁⁻¹ * Real.exp (α₁ * |r|))) := by gcongr
            _ = 4 * π * Real.sqrt a * α₁⁻¹ *
                  (Real.cosh (4 * π * Real.sqrt a * θ * |r|) * Real.exp (α₁ * |r|)) := by ring
            _ ≤ 4 * π * Real.sqrt a * α₁⁻¹ * (2 * Real.cosh (4 * π * Real.sqrt a * θ₁ * r)) := by
                have hK_nn : 0 ≤ 4 * π * Real.sqrt a * α₁⁻¹ := by positivity
                exact mul_le_mul_of_nonneg_left hcosh_exp hK_nn
            _ = (K₁ / 2) * Real.cosh (4 * π * Real.sqrt a * θ₁ * r) := by dsimp [K₁, α₁]; ring
        have hc1 : ‖Complex.cos (c4 * (p.1 : ℂ) * (b + (d : ℂ)))‖ ≤
            Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) := by
          have him : (c4 * (p.1 : ℂ) * (b + (d : ℂ))).im = 4 * π * Real.sqrt a * p.1 * b.im := by
            dsimp [c4]; simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
          calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * b.im) := by
                rw [← him]; exact norm_complex_cos_le_cosh _
            _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) :=
                cosh_mul_im_le_cosh ha0 hθ₁_pos.le (by linarith)
        have hc2 : ‖Complex.cos (c4 * (p.2 : ℂ) * (b - (d : ℂ)))‖ ≤
            Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) := by
          have him : (c4 * (p.2 : ℂ) * (b - (d : ℂ))).im = 4 * π * Real.sqrt a * p.2 * b.im := by
            dsimp [c4]; simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
          calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * b.im) := by
                rw [← him]; exact norm_complex_cos_le_cosh _
            _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) :=
                cosh_mul_im_le_cosh ha0 hθ₁_pos.le (by linarith)
        have hs1 := hsc1 p.1 (b + (d : ℂ)) (by simpa using hb)
        have hs2 := hsc1 p.2 (b - (d : ℂ)) (by simpa using hb)
        dsimp [F']
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hsum : ‖Complex.sin (c4 * (p.1 : ℂ) * (b + (d : ℂ))) * (c4 * (p.1 : ℂ)) *
              Complex.cos (c4 * (p.2 : ℂ) * (b - (d : ℂ))) +
            Complex.cos (c4 * (p.1 : ℂ) * (b + (d : ℂ))) *
              (Complex.sin (c4 * (p.2 : ℂ) * (b - (d : ℂ))) * (c4 * (p.2 : ℂ)))‖ ≤
            K₁ * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul _ (Complex.cos (c4 * (p.2 : ℂ) * (b - (d : ℂ)))),
            norm_mul (Complex.cos (c4 * (p.1 : ℂ) * (b + (d : ℂ))))]
          have hA : ‖Complex.sin (c4 * (p.1 : ℂ) * (b + (d : ℂ))) * (c4 * (p.1 : ℂ))‖ *
                ‖Complex.cos (c4 * (p.2 : ℂ) * (b - (d : ℂ)))‖ ≤
              (K₁ / 2) * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
                Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2) :=
            mul_le_mul hs1 hc2 (norm_nonneg _) (by positivity)
          have hB : ‖Complex.cos (c4 * (p.1 : ℂ) * (b + (d : ℂ)))‖ *
                ‖Complex.sin (c4 * (p.2 : ℂ) * (b - (d : ℂ))) * (c4 * (p.2 : ℂ))‖ ≤
              Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
                ((K₁ / 2) * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2)) :=
            mul_le_mul hc1 hs2 (norm_nonneg _) (Real.cosh_pos _).le
          linarith
        calc |Φ p| * ‖Complex.sin (c4 * (p.1 : ℂ) * (b + (d : ℂ))) * (c4 * (p.1 : ℂ)) *
                Complex.cos (c4 * (p.2 : ℂ) * (b - (d : ℂ))) +
              Complex.cos (c4 * (p.1 : ℂ) * (b + (d : ℂ))) *
                (Complex.sin (c4 * (p.2 : ℂ) * (b - (d : ℂ))) * (c4 * (p.2 : ℂ)))‖
            ≤ |Φ p| * (K₁ * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
                Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2)) :=
              mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
          _ = K₁ * (|Φ p| * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
                Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2)) := by ring
      calc ∫ p : ℝ × ℝ, ‖F' b p‖
          ≤ ∫ p : ℝ × ℝ, (16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ))) *
              (|Φ p| * Real.cosh (4 * π * Real.sqrt a * θ₁ * p.1) *
                Real.cosh (4 * π * Real.sqrt a * θ₁ * p.2)) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hint_1.const_mul _) (Eventually.of_forall hbound_1)
        _ = (16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ))) * spinITheta a θ₁ Φ := by
            rw [integral_const_mul]; rfl

private lemma spinGeff_differentiableOn {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    DifferentiableOn ℂ (spinGeff a Φ) (spinStrip (1 / 2)) := by
  intro b₀ hb₀
  have ha0 : 0 < a := by linarith
  have hb₀_im : |b₀.im| < 1 / 2 := hb₀
  set θ₀ : ℝ := (|b₀.im| + 1 / 2) / 2
  have hθ₀_pos : 0 < θ₀ := by dsimp [θ₀]; positivity
  have hθ₀_lt : θ₀ < 1 / 2 := by dsimp [θ₀]; linarith
  set θ₁ : ℝ := (θ₀ + 1 / 2) / 2
  have hθ₁_pos : 0 < θ₁ := by dsimp [θ₁, θ₀]; positivity
  have hθ₁_lt : θ₁ < 1 / 2 := by dsimp [θ₁, θ₀]; linarith
  have hθ10 : 0 < θ₁ - θ₀ := by dsimp [θ₁, θ₀]; linarith
  set δ : ℝ := (θ₀ - |b₀.im|) / 2
  have hδ : 0 < δ := by dsimp [δ, θ₀]; linarith
  have hgauss_int : Integrable (fun d : ℝ => Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  have hball_im : ∀ w ∈ Metric.ball b₀ δ, |w.im| ≤ θ₀ := fun w hw => by
    have h1 : |w.im - b₀.im| ≤ ‖w - b₀‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (w - b₀)
    have h2 : ‖w - b₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    dsimp [δ, θ₀] at *; linarith [abs_sub_abs_le_abs_sub w.im b₀.im]
  have hball_norm : ∀ w ∈ Metric.ball b₀ δ, ‖w‖ ≤ ‖b₀‖ + δ := fun w hw => by
    have h2 : ‖w - b₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    calc ‖w‖ = ‖(w - b₀) + b₀‖ := by ring_nf
      _ ≤ ‖w - b₀‖ + ‖b₀‖ := norm_add_le _ _
      _ ≤ ‖b₀‖ + δ := by linarith
  let F : ℂ → ℝ → ℂ := fun w d => spinHb w d * spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w d =>
    if hw : |w.im| ≤ θ₀ then
      (spinHb_bound_and_deriv (by linarith : |w.im| ≤ 1 / 2) d).choose *
        spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ)) +
      spinHb w d *
        (spinGC_diag_bound_and_deriv ha hΦ hθ₀_pos hθ₀_lt hw d).2.choose
    else 0
  have hF_meas_ball : ∀ w ∈ Metric.ball b₀ δ, AEStronglyMeasurable (F w) volume := by
    intro w hw
    have hw_im := hball_im w hw
    have hgc_cont : Continuous (fun d : ℝ => spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ))) := by
      have h1 : ∀ d : ℝ, ContinuousAt (fun t : ℝ => ∫ p : ℝ × ℝ, (Φ p : ℂ) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (t : ℂ))) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (t : ℂ)))) d := fun d => by
        -- Continuous by dominated convergence (`integrable_spinITheta`)
        refine continuousAt_of_dominated (bound := fun p : ℝ × ℝ =>
            |Φ p| * Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) *
              Real.cosh (4 * π * Real.sqrt a * θ₀ * p.2)) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall fun t => by
            have hc0 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ) *
                Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (t : ℂ))) *
                Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (t : ℂ)))) := by
              have hc1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
              fun_prop
            exact hc0.aestronglyMeasurable
        · exact Eventually.of_forall fun t => Eventually.of_forall fun p => by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (t : ℂ))).im =
                4 * π * Real.sqrt a * p.1 * w.im := by
              simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
            have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (t : ℂ))).im =
                4 * π * Real.sqrt a * p.2 * w.im := by
              simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
            have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (w + (t : ℂ)))‖ ≤
                Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) := by
              calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * w.im) := by
                    rw [← him1]; exact norm_complex_cos_le_cosh _
                _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₀ * p.1) :=
                    cosh_mul_im_le_cosh ha0 hθ₀_pos.le hw_im
            have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (w - (t : ℂ)))‖ ≤
                Real.cosh (4 * π * Real.sqrt a * θ₀ * p.2) := by
              calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * w.im) := by
                    rw [← him2]; exact norm_complex_cos_le_cosh _
                _ ≤ Real.cosh (4 * π * Real.sqrt a * θ₀ * p.2) :=
                    cosh_mul_im_le_cosh ha0 hθ₀_pos.le hw_im
            exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
              (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)
        · exact integrable_spinITheta ha hθ₀_pos hθ₀_lt hΦ
        · refine Eventually.of_forall fun p => Continuous.continuousAt ?_
          fun_prop
      exact continuous_iff_continuousAt.mpr fun d => by
        simpa [spinGC] using (h1 d).neg
    have hhb_cont : Continuous (fun d : ℝ => spinHb w d) := by
      unfold spinHb
      have hw1_ne : ∀ d : ℝ, Complex.cosh ((w + (d : ℂ)) / 2) ≠ 0 := fun d => by
        refine (complex_tanh_bound_and_deriv ?_).1
        simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, add_zero]
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      have hw2_ne : ∀ d : ℝ, Complex.cosh ((w - (d : ℂ)) / 2) ≠ 0 := fun d => by
        refine (complex_tanh_bound_and_deriv ?_).1
        simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      have ht1 : Continuous (fun d : ℝ => Complex.tanh ((w + (d : ℂ)) / 2)) := by
        simp_rw [Complex.tanh_eq_sinh_div_cosh]
        exact Continuous.div (by fun_prop) (by fun_prop) hw1_ne
      have ht2 : Continuous (fun d : ℝ => Complex.tanh ((w - (d : ℂ)) / 2)) := by
        simp_rw [Complex.tanh_eq_sinh_div_cosh]
        exact Continuous.div (by fun_prop) (by fun_prop) hw2_ne
      exact (((continuous_const.mul ((ht1.pow 2).mul (ht2.pow 2))).div_const _).mul (by fun_prop))
    exact (hhb_cont.mul hgc_cont).aestronglyMeasurable
  have hF_meas : ∀ᶠ w in 𝓝 b₀, AEStronglyMeasurable (F w) volume :=
    Filter.Eventually.mono (Metric.ball_mem_nhds b₀ hδ) hF_meas_ball
  have hF_deriv : ∀ᵐ d ∂volume, ∀ w ∈ Metric.ball b₀ δ, HasDerivAt (fun z => F z d) (F' w d) w := by
    refine Eventually.of_forall fun d w hw => ?_
    have hw_im := hball_im w hw
    have hhb_d := (spinHb_bound_and_deriv (by linarith : |w.im| ≤ 1 / 2) d).choose_spec.1
    have hgc_d := (spinGC_diag_bound_and_deriv ha hΦ hθ₀_pos hθ₀_lt hw_im d).2.choose_spec.1
    have hF'_eq : F' w d =
        (spinHb_bound_and_deriv (by linarith : |w.im| ≤ 1 / 2) d).choose *
          spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ)) +
        spinHb w d *
          (spinGC_diag_bound_and_deriv ha hΦ hθ₀_pos hθ₀_lt hw_im d).2.choose := by
      dsimp [F']; rw [dif_pos hw_im]
    rw [hF'_eq]
    exact hhb_d.mul hgc_d
  have hF'_meas : AEStronglyMeasurable (F' b₀) volume := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hδ
    let seq : ℕ → ℝ → ℂ := fun n d =>
      ((n + N₀ + 1 : ℕ) : ℂ) * (F (b₀ + (((n + N₀ + 1 : ℕ) : ℝ)⁻¹ : ℂ)) d - F b₀ d)
    have hseq_meas : ∀ n : ℕ, AEStronglyMeasurable (seq n) volume := fun n => by
      have hw_mem : b₀ + (((n + N₀ + 1 : ℕ) : ℝ)⁻¹ : ℂ) ∈ Metric.ball b₀ δ := by
        rw [Metric.mem_ball, dist_eq_norm, show b₀ + (((n + N₀ + 1 : ℕ) : ℝ)⁻¹ : ℂ) - b₀ =
            (((n + N₀ + 1 : ℕ) : ℂ)⁻¹) by push_cast; ring,
          norm_inv, Complex.norm_natCast]
        have hle : (1 : ℝ) / ((n + N₀ + 1 : ℕ) : ℝ) ≤ 1 / ((N₀ : ℝ) + 1) := by
          gcongr
          have : (N₀ : ℝ) + 1 = ((N₀ + 1 : ℕ) : ℝ) := by push_cast; ring
          rw [this]; exact_mod_cast Nat.le_add_left (N₀ + 1) n
        simpa [one_div] using hle.trans_lt hN₀
      have h1 := hF_meas_ball _ hw_mem
      have h2 := hF_meas_ball _ (Metric.mem_ball_self hδ)
      exact (h1.sub h2).const_mul _
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop hseq_meas ?_
    filter_upwards [hF_deriv] with d hd
    have hdb₀ := hd b₀ (Metric.mem_ball_self hδ)
    have htend : Filter.Tendsto (fun h : ℂ => h⁻¹ • (F (b₀ + h) d - F b₀ d)) (𝓝[≠] 0) (𝓝 (F' b₀ d)) :=
      hdb₀.tendsto_slope_zero.congr (fun h => by simp [smul_eq_mul])
    have hinv_tend : Filter.Tendsto (fun n : ℕ => (((n + N₀ + 1 : ℕ) : ℝ)⁻¹ : ℂ)) Filter.atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hr : Filter.Tendsto (fun n : ℕ => ((n + N₀ + 1 : ℕ) : ℝ)⁻¹) Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N₀ + 1)))
        simpa [Function.comp_def, Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp hr
      · refine Eventually.of_forall fun n => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero, inv_eq_zero]
        exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (n + N₀))
    refine (htend.comp hinv_tend).congr fun n => ?_
    simp only [seq, Function.comp_apply, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast, inv_inv]
  have hF_int : Integrable (F b₀) volume := by
    have hb₀_le : |b₀.im| ≤ θ₀ := by dsimp [θ₀]; linarith
    have hbd_0 : ∀ d : ℝ, ‖F b₀ d‖ ≤
        (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) * spinITheta a θ₀ Φ) *
          Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := fun d => by
      have h1 := (spinHb_bound_and_deriv (by linarith : |b₀.im| ≤ 1 / 2) d).choose_spec.2.1
      have h2 := (spinGC_diag_bound_and_deriv ha hΦ hθ₀_pos hθ₀_lt hb₀_le d).1
      have hI0 : 0 ≤ spinITheta a θ₀ Φ := by
        unfold spinITheta; exact integral_nonneg fun p => by positivity
      have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
      dsimp [F]
      rw [norm_mul]
      calc ‖spinHb b₀ d‖ * ‖spinGC a Φ (b₀ + (d : ℂ)) (b₀ - (d : ℂ))‖
          ≤ (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) *
              Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) * spinITheta a θ₀ Φ :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) * spinITheta a θ₀ Φ) *
              Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by ring
    exact (hgauss_int.const_mul _).mono' (hF_meas_ball b₀ (Metric.mem_ball_self hδ))
      (Eventually.of_forall hbd_0)
  set C_bd : ℝ :=
    ((128 / 9 * (1 + (‖b₀‖ + δ)) + 32 / 3 * Real.sqrt 2) *
      (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * spinITheta a θ₀ Φ +
    4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) *
      ((16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ₀))) * spinITheta a θ₁ Φ))
  let bound : ℝ → ℝ := fun d => C_bd * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
  have hF'_bound : ∀ᵐ d ∂volume, ∀ w ∈ Metric.ball b₀ δ, ‖F' w d‖ ≤ bound d := by
    refine Eventually.of_forall fun d w hw => ?_
    have hw_im := hball_im w hw
    have hw_n := hball_norm w hw
    have hhb_spec := (spinHb_bound_and_deriv (by linarith : |w.im| ≤ 1 / 2) d).choose_spec
    have hgc_spec := spinGC_diag_bound_and_deriv ha hΦ hθ₀_pos hθ₀_lt hw_im d
    have hF'_eq : F' w d =
        (spinHb_bound_and_deriv (by linarith : |w.im| ≤ 1 / 2) d).choose *
          spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ)) +
        spinHb w d * hgc_spec.2.choose := by
      dsimp [F']; rw [dif_pos hw_im]
    rw [hF'_eq]
    have h1 := hhb_spec.2.2
    have h2 := hgc_spec.1
    have h3 := hhb_spec.2.1
    have h4 := hgc_spec.2.choose_spec.2 θ₁ (by dsimp [θ₁]; linarith) hθ₁_lt
    have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
    have hI0 : 0 ≤ spinITheta a θ₀ Φ := by
      unfold spinITheta; exact integral_nonneg fun p => by positivity
    have hI1 : 0 ≤ spinITheta a θ₁ Φ := by
      unfold spinITheta; exact integral_nonneg fun p => by positivity
    have hA : ‖(spinHb_bound_and_deriv (by linarith : |w.im| ≤ 1 / 2) d).choose *
          spinGC a Φ (w + (d : ℂ)) (w - (d : ℂ))‖ ≤
        (128 / 9 * (1 + (‖b₀‖ + δ)) + 32 / 3 * Real.sqrt 2) *
          (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
          spinITheta a θ₀ Φ := by
      rw [norm_mul]
      refine mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)
      gcongr
    have hB : ‖spinHb w d * hgc_spec.2.choose‖ ≤
        4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3) *
          Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) *
          ((16 * π * Real.sqrt a / (4 * π * Real.sqrt a * (θ₁ - θ₀))) * spinITheta a θ₁ Φ) := by
      rw [norm_mul]
      exact mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hA hB
      _ = bound d := by dsimp [bound, C_bd]; ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hδ)
    hF_meas hF_int hF'_meas hF'_bound (hgauss_int.const_mul C_bd) hF_deriv
  have hgeff_eq : spinGeff a Φ = fun w : ℂ =>
      ((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ) * ∫ d : ℝ, F w d := rfl
  rw [hgeff_eq]
  exact ((hd.2.const_mul ((1 / (Real.sqrt π * spinSigma0) : ℝ) : ℂ)).differentiableAt).differentiableWithinAt

/-! ### Section 5: Uniform strip bound `‖spinGeff a Φ b‖ ≤ C * n ^ 2 * spinM2 a Φ` -/

private noncomputable def spinHbC (b w : ℂ) : ℂ :=
  ((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2) *
    (Complex.tanh ((b + w) / 2) ^ 2 * Complex.tanh ((b - w) / 2) ^ 2) /
    ((Real.tanh (xiStar / 2) ^ 4 : ℝ) : ℂ) *
    Complex.exp (-(w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)))

private lemma spinHbC_ofReal (b : ℂ) (d : ℝ) : spinHbC b (d : ℂ) = spinHb b d := by
  unfold spinHbC spinHb
  congr 2
  push_cast; ring

private lemma complex_tanh_bound_strip {w : ℂ} (hw : |w.im| ≤ 5 / 4) :
    Complex.cosh w ≠ 0 ∧ ‖Complex.tanh w‖ ≤ (Real.cos (5 / 4))⁻¹ := by
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hcos_le1 : Real.cos (5 / 4) ≤ 1 := Real.cos_le_one _
  have hcos_ge : Real.cos (5 / 4) ≤ Real.cos w.im := by
    rw [← Real.cos_abs w.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw
  have hcos_sq : Real.cos (5 / 4) ^ 2 ≤ Real.cos w.im ^ 2 :=
    pow_le_pow_left₀ hcos_pos.le hcos_ge 2
  have hcos_eq : Complex.cosh w =
      (Real.cosh w.re * Real.cos w.im : ℝ) + (Real.sinh w.re * Real.sin w.im : ℝ) * I := by
    apply Complex.ext
    · simp [Complex.cosh, Complex.exp_re, Real.cosh_eq, Real.cos_neg, -Complex.ofReal_cos]; ring
    · simp [Complex.cosh, Complex.exp_im, Real.sinh_eq, Real.sin_neg, -Complex.ofReal_sin,
        ← Complex.ofReal_exp]; ring
  have hnorm_sq : ‖Complex.cosh w‖ ^ 2 = Real.sinh w.re ^ 2 + Real.cos w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hcos_eq, Complex.normSq_add_mul_I]
    have hch : Real.cosh w.re ^ 2 - Real.sinh w.re ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    have hcs : Real.cos w.im ^ 2 + Real.sin w.im ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    nlinarith
  have hcos_sq_le1 : Real.cos (5 / 4) ^ 2 ≤ 1 := by nlinarith
  have hch_ge : Real.cos (5 / 4) * Real.cosh w.re ≤ ‖Complex.cosh w‖ := by
    have hsq : (Real.cos (5 / 4) * Real.cosh w.re) ^ 2 ≤ ‖Complex.cosh w‖ ^ 2 := by
      rw [mul_pow, hnorm_sq]
      have hch : Real.cosh w.re ^ 2 = Real.sinh w.re ^ 2 + 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq w.re]
      rw [hch]
      nlinarith [sq_nonneg (Real.sinh w.re)]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have hch_ne : Complex.cosh w ≠ 0 := norm_ne_zero_iff.mp (by
    have := Real.cosh_pos w.re; nlinarith)
  refine ⟨hch_ne, ?_⟩
  rw [Complex.tanh_eq_sinh_div_cosh, norm_div]
  calc ‖Complex.sinh w‖ / ‖Complex.cosh w‖
      ≤ Real.cosh w.re / (Real.cos (5 / 4) * Real.cosh w.re) :=
        div_le_div₀ (Real.cosh_pos _).le (norm_complex_sinh_le w)
          (mul_pos hcos_pos (Real.cosh_pos _)) hch_ge
    _ = (Real.cos (5 / 4))⁻¹ := by
        field_simp [hcos_pos.ne', (Real.cosh_pos w.re).ne']

private noncomputable def spinHbWideConst : ℝ :=
  (4 / 3) * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
    Real.exp (4 / spinSigma0 ^ 2)

private lemma spinHbWideConst_pos : 0 < spinHbWideConst := by
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  unfold spinHbWideConst
  positivity

private lemma spinHbC_strip_bound_and_diff {b : ℂ} (hb : b ∈ spinStrip (1 / 2)) :
    (∀ w : ℂ, |w.im| ≤ 2 → DifferentiableAt ℂ (spinHbC b) w) ∧
      (∀ w : ℂ, |w.im| ≤ 2 →
        ‖spinHbC b w‖ ≤ spinHbWideConst * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2))) := by
  have hb_im : |b.im| < 1 / 2 := hb
  have hb_re : 3 / 4 ≤ (1 + b ^ 2).re := by
    simp only [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
    nlinarith [sq_nonneg b.re, sq_abs b.im, pow_le_pow_left₀ (abs_nonneg b.im) hb_im.le 2]
  have hb_norm : 3 / 4 ≤ ‖1 + b ^ 2‖ := hb_re.trans (Complex.re_le_norm _)
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  have hpi : (5 / 4 : ℝ) < π / 2 := by linarith [Real.pi_gt_d4]
  have hcos_pos : 0 < Real.cos (5 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi⟩
  have hw_im_bd : ∀ w : ℂ, |w.im| ≤ 2 →
      |((b + w) / 2).im| ≤ 5 / 4 ∧ |((b - w) / 2).im| ≤ 5 / 4 := fun w hw => by
    constructor
    · simp only [Complex.div_ofNat_im, Complex.add_im]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_add_le b.im w.im]
    · simp only [Complex.div_ofNat_im, Complex.sub_im]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_sub b.im w.im]
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨hw1, hw2⟩ := hw_im_bd w hw
    have hch1 := (complex_tanh_bound_strip hw1).1
    have hch2 := (complex_tanh_bound_strip hw2).1
    have hd1 : DifferentiableAt ℂ (fun z : ℂ => Complex.tanh ((b + z) / 2)) w := by
      have hfun : (fun z : ℂ => Complex.tanh ((b + z) / 2)) =
          (fun z : ℂ => Complex.sinh ((b + z) / 2) / Complex.cosh ((b + z) / 2)) := by
        ext z; exact Complex.tanh_eq_sinh_div_cosh _
      rw [hfun]
      exact (DifferentiableAt.div (by fun_prop) (by fun_prop) hch1)
    have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.tanh ((b - z) / 2)) w := by
      have hfun : (fun z : ℂ => Complex.tanh ((b - z) / 2)) =
          (fun z : ℂ => Complex.sinh ((b - z) / 2) / Complex.cosh ((b - z) / 2)) := by
        ext z; exact Complex.tanh_eq_sinh_div_cosh _
      rw [hfun]
      exact (DifferentiableAt.div (by fun_prop) (by fun_prop) hch2)
    unfold spinHbC
    exact (((((hd1.pow 2).mul (hd2.pow 2)).const_mul _).div_const _).mul (by fun_prop))
  · obtain ⟨hw1, hw2⟩ := hw_im_bd w hw
    have ht1 := (complex_tanh_bound_strip hw1).2
    have ht2 := (complex_tanh_bound_strip hw2).2
    have hinv : ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ ≤ (4 / 3) * (1 + xiStar ^ 2) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (1 + xiStar ^ 2) / ‖1 + b ^ 2‖ ≤ (1 + xiStar ^ 2) / (3 / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hb_norm
        _ = (4 / 3) * (1 + xiStar ^ 2) := by ring
    have hexp_bd : ‖Complex.exp (-(w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)))‖ ≤
        Real.exp (4 / spinSigma0 ^ 2) * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := by
      rw [Complex.norm_exp, Complex.neg_re]
      have hre : (w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)).re = (w.re ^ 2 - w.im ^ 2) / spinSigma0 ^ 2 := by
        rw [show ((spinSigma0 ^ 2 : ℝ) : ℂ) = (((spinSigma0 ^ 2 : ℝ) : ℂ)) from rfl,
          Complex.div_ofReal_re, sq, Complex.mul_re]; ring
      rw [hre]
      have him2 : w.im ^ 2 ≤ 4 := by
        have := pow_le_pow_left₀ (abs_nonneg w.im) hw 2
        rw [sq_abs] at this; linarith
      have hsig : 0 < spinSigma0 ^ 2 := by unfold spinSigma0; positivity
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hle : -((w.re ^ 2 - w.im ^ 2) / spinSigma0 ^ 2) ≤
          4 / spinSigma0 ^ 2 + -(w.re ^ 2 / spinSigma0 ^ 2) := by
        rw [show 4 / spinSigma0 ^ 2 + -(w.re ^ 2 / spinSigma0 ^ 2) =
            -((w.re ^ 2 - 4) / spinSigma0 ^ 2) by ring]
        exact neg_le_neg (div_le_div_of_nonneg_right (by linarith) hsig.le)
      exact hle
    unfold spinHbC spinHbWideConst
    rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxi]
    have h1 : ‖Complex.tanh ((b + w) / 2)‖ ^ 2 ≤ (Real.cos (5 / 4))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht1 2
    have h2 : ‖Complex.tanh ((b - w) / 2)‖ ^ 2 ≤ (Real.cos (5 / 4))⁻¹ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht2 2
    calc ‖((1 + xiStar ^ 2 : ℝ) : ℂ) / (1 + b ^ 2)‖ *
          (‖Complex.tanh ((b + w) / 2)‖ ^ 2 * ‖Complex.tanh ((b - w) / 2)‖ ^ 2) /
          Real.tanh (xiStar / 2) ^ 4 * ‖Complex.exp (-(w ^ 2 / ((spinSigma0 ^ 2 : ℝ) : ℂ)))‖
        ≤ (4 / 3 * (1 + xiStar ^ 2)) * ((Real.cos (5 / 4))⁻¹ ^ 2 * (Real.cos (5 / 4))⁻¹ ^ 2) /
            Real.tanh (xiStar / 2) ^ 4 *
            (Real.exp (4 / spinSigma0 ^ 2) * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2))) := by
          refine mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul hinv
            (mul_le_mul h1 h2 (by positivity) (by positivity))
            (by positivity) (by positivity)) hxi.le) hexp_bd (norm_nonneg _) (by positivity)
      _ = ((4 / 3) * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (Real.cos (5 / 4))⁻¹ ^ 4 *
            Real.exp (4 / spinSigma0 ^ 2)) * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := by ring

private lemma gaussian_contour_shift {b : ℂ} (hb : b ∈ spinStrip (1 / 2)) (β ω σ : ℝ)
    (hσ : |σ| ≤ 1) :
    ∫ d : ℝ, spinHb b d * Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * (d : ℂ))) =
      ∫ t : ℝ, spinHbC b ((t : ℂ) + (2 * σ : ℝ) * I) *
        Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I))) := by
  obtain ⟨hdiff, hbd⟩ := spinHbC_strip_bound_and_diff hb
  let f : ℂ → ℂ := fun w => spinHbC b w * Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * w))
  have hf_diff : ∀ w : ℂ, |w.im| ≤ 2 → DifferentiableAt ℂ f w := fun w hw =>
    (hdiff w hw).mul (by fun_prop)
  have hf_bd : ∀ w : ℂ, |w.im| ≤ 2 →
      ‖f w‖ ≤ spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
        Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := fun w hw => by
    have hb_im : |b.im| ≤ 1 / 2 := hb.le
    have him : (I * ((β : ℂ) * b + (ω : ℂ) * w)).re = -(β * b.im + ω * w.im) := by
      simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have hexp_bd : ‖Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * w))‖ ≤
        Real.exp (|β| / 2 + 2 * |ω|) := by
      rw [Complex.norm_exp, him, Real.exp_le_exp]
      have h1 : -(β * b.im) ≤ |β| / 2 := by
        calc -(β * b.im) ≤ |β * b.im| := neg_le_abs _
          _ = |β| * |b.im| := abs_mul _ _
          _ ≤ |β| * (1 / 2) := mul_le_mul_of_nonneg_left hb_im (abs_nonneg _)
          _ = |β| / 2 := by ring
      have h2 : -(ω * w.im) ≤ 2 * |ω| := by
        calc -(ω * w.im) ≤ |ω * w.im| := neg_le_abs _
          _ = |ω| * |w.im| := abs_mul _ _
          _ ≤ |ω| * 2 := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
          _ = 2 * |ω| := by ring
      linarith
    dsimp [f]
    rw [norm_mul]
    calc ‖spinHbC b w‖ * ‖Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * w))‖
        ≤ (spinHbWideConst * Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2))) *
            Real.exp (|β| / 2 + 2 * |ω|) :=
          mul_le_mul (hbd w hw) hexp_bd (norm_nonneg _) (by
            have := spinHbWideConst_pos; positivity)
      _ = spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
            Real.exp (-(w.re ^ 2 / spinSigma0 ^ 2)) := by ring
  have hgauss_int : Integrable (fun t : ℝ => Real.exp (-(t ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  have hf_int0 : Integrable (fun t : ℝ => f (t : ℂ)) volume := by
    refine (hgauss_int.const_mul (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|))).mono' ?_ ?_
    · have hcont : Continuous (fun t : ℝ => f (t : ℂ)) :=
        continuous_iff_continuousAt.mpr fun t =>
          (hf_diff (t : ℂ) (by simp)).continuousAt.comp Complex.continuous_ofReal.continuousAt
      exact hcont.aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        simpa using hf_bd (t : ℂ) (by simp)
  have hf_int1 : Integrable (fun t : ℝ => f ((t : ℂ) + (2 * σ : ℝ) * I)) volume := by
    refine (hgauss_int.const_mul (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|))).mono' ?_ ?_
    · have hcont : Continuous (fun t : ℝ => f ((t : ℂ) + (2 * σ : ℝ) * I)) :=
        continuous_iff_continuousAt.mpr fun t => by
          refine (hf_diff _ ?_).continuousAt.comp (by fun_prop)
          simp [abs_mul]; linarith
      exact hcont.aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        have him : |((t : ℂ) + (2 * σ : ℝ) * I).im| ≤ 2 := by
          simp [abs_mul]; linarith
        simpa using hf_bd _ him
  -- Apply `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` on `[-R, R] × [0, 2σ]`
  have hcauchy : ∀ R : ℕ,
      (∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ)) -
      (∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I)) +
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((R : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((-(R : ℝ) : ℂ) + (y : ℂ) * I)) = 0 := by
    intro R
    have hrect : DifferentiableOn ℂ f (Set.uIcc (-(R : ℝ)) (R : ℝ) ×ℂ Set.uIcc (0 : ℝ) (2 * σ)) := by
      intro w hw
      have hw_im : w.im ∈ Set.uIcc (0 : ℝ) (2 * σ) := hw.2
      have hw_le : |w.im| ≤ 2 := by
        rcases le_or_gt 0 (2 * σ) with hs | hs
        · rw [Set.uIcc_of_le hs] at hw_im
          exact abs_le.mpr ⟨by linarith [hw_im.1], by linarith [hw_im.2, abs_le.mp hσ]⟩
        · rw [Set.uIcc_of_ge hs.le] at hw_im
          exact abs_le.mpr ⟨by linarith [hw_im.1, abs_le.mp hσ], by linarith [hw_im.2]⟩
      exact (hf_diff w hw_le).differentiableWithinAt
    have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (-(R : ℝ) : ℂ) ((R : ℝ) + (2 * σ : ℝ) * I) (by simpa using hrect)
    simpa using hzero
  have htend0 : Filter.Tendsto (fun R : ℕ => ∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ))
      Filter.atTop (𝓝 (∫ t : ℝ, f (t : ℂ))) :=
    (intervalIntegral_tendsto_integral hf_int0 tendsto_neg_atTop_atBot tendsto_id).comp
      tendsto_natCast_atTop_atTop
  have htend1 : Filter.Tendsto (fun R : ℕ => ∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I))
      Filter.atTop (𝓝 (∫ t : ℝ, f ((t : ℂ) + (2 * σ : ℝ) * I))) :=
    (intervalIntegral_tendsto_integral hf_int1 tendsto_neg_atTop_atBot tendsto_id).comp
      tendsto_natCast_atTop_atTop
  have hside_tend : ∀ (s : ℝ) (hs : |s| = 1),
      Filter.Tendsto (fun R : ℕ => I • ∫ y in (0 : ℝ)..(2 * σ), f (((s * R : ℝ) : ℂ) + (y : ℂ) * I))
        Filter.atTop (𝓝 0) := by
    intro s hs
    have hnorm_le : ∀ R : ℕ, ‖I • ∫ y in (0 : ℝ)..(2 * σ), f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        2 * (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|)) *
          Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
      intro R
      rw [norm_smul, Complex.norm_I, one_mul]
      have hbd_y : ∀ y ∈ Set.uIcc (0 : ℝ) (2 * σ),
          ‖f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
            spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
              Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
        intro y hy
        have hy_le : |y| ≤ 2 := by
          rcases le_or_gt 0 (2 * σ) with h2 | h2
          · rw [Set.uIcc_of_le h2] at hy
            exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2, abs_le.mp hσ]⟩
          · rw [Set.uIcc_of_ge h2.le] at hy
            exact abs_le.mpr ⟨by linarith [hy.1, abs_le.mp hσ], by linarith [hy.2]⟩
        have him : |(((s * R : ℝ) : ℂ) + (y : ℂ) * I).im| ≤ 2 := by simpa using hy_le
        have hre : (((s * R : ℝ) : ℂ) + (y : ℂ) * I).re ^ 2 = (R : ℝ) ^ 2 := by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im]
          calc (s * ↑R + (y * 0 - 0 * 1)) ^ 2 = s ^ 2 * (R : ℝ) ^ 2 := by ring
            _ = |s| ^ 2 * (R : ℝ) ^ 2 := by rw [sq_abs]
            _ = (R : ℝ) ^ 2 := by rw [hs, one_pow, one_mul]
        calc ‖f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖
            ≤ spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
                Real.exp (-((((s * R : ℝ) : ℂ) + (y : ℂ) * I).re ^ 2 / spinSigma0 ^ 2)) :=
              hf_bd _ him
          _ = spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
                Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by rw [hre]
      calc ‖∫ y in (0 : ℝ)..(2 * σ), f (((s * R : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
              Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2))) * |2 * σ - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const
              (fun y hy => hbd_y y (Set.Ioc_subset_Icc_self hy))
        _ ≤ 2 * (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|)) *
              Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
            have h2s : |2 * σ - 0| ≤ 2 := by
              rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
            have hC_nn : 0 ≤ spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
                Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)) := by
              have := spinHbWideConst_pos; positivity
            calc _ ≤ (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|) *
                  Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2))) * 2 :=
                mul_le_mul_of_nonneg_left h2s hC_nn
              _ = _ := by ring
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun _ => norm_nonneg _) hnorm_le)
    have hexp_tend : Filter.Tendsto (fun R : ℕ => Real.exp (-((R : ℝ) ^ 2 / spinSigma0 ^ 2)))
        Filter.atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      refine Filter.tendsto_neg_atBot_iff.mpr ?_
      have hsq : Filter.Tendsto (fun R : ℕ => (R : ℝ) ^ 2) Filter.atTop Filter.atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
      simpa [div_eq_mul_inv] using hsq.atTop_mul_const (show (0 : ℝ) < (spinSigma0 ^ 2)⁻¹ by
        unfold spinSigma0; positivity)
    simpa using hexp_tend.const_mul (2 * (spinHbWideConst * Real.exp (|β| / 2 + 2 * |ω|)))
  have hdiff_tend : Filter.Tendsto (fun R : ℕ =>
      (∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ)) -
      (∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I)) +
      I • (∫ y in (0 : ℝ)..(2 * σ), f (((1 * (R : ℝ) : ℝ) : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((((-1 : ℝ) * (R : ℝ) : ℝ) : ℂ) + (y : ℂ) * I)))
      Filter.atTop (𝓝 ((∫ t : ℝ, f (t : ℂ)) - (∫ t : ℝ, f ((t : ℂ) + (2 * σ : ℝ) * I)) + 0 - 0)) :=
    ((htend0.sub htend1).add (hside_tend 1 (by norm_num))).sub (hside_tend (-1) (by norm_num))
  have hzero_seq : (fun R : ℕ =>
      (∫ t in -(R : ℝ)..(R : ℝ), f (t : ℂ)) -
      (∫ t in -(R : ℝ)..(R : ℝ), f ((t : ℂ) + (2 * σ : ℝ) * I)) +
      I • (∫ y in (0 : ℝ)..(2 * σ), f (((1 * (R : ℝ) : ℝ) : ℂ) + (y : ℂ) * I)) -
      I • (∫ y in (0 : ℝ)..(2 * σ), f ((((-1 : ℝ) * (R : ℝ) : ℝ) : ℂ) + (y : ℂ) * I))) = fun _ => 0 := by
    ext R; simpa [one_mul, neg_one_mul] using hcauchy R
  rw [hzero_seq] at hdiff_tend
  have heq : (∫ t : ℝ, f (t : ℂ)) - (∫ t : ℝ, f ((t : ℂ) + (2 * σ : ℝ) * I)) + 0 - 0 = 0 :=
    tendsto_nhds_unique hdiff_tend tendsto_const_nhds
  have heq2 : ∫ t : ℝ, f (t : ℂ) = ∫ t : ℝ, f ((t : ℂ) + (2 * σ : ℝ) * I) := sub_eq_zero.mp (by
    simpa using heq)
  simpa [f, spinHbC_ofReal] using heq2

private noncomputable def spinKb (a : ℝ) (b : ℂ) (rL rR : ℝ) : ℂ :=
  ∫ d : ℝ, spinHb b d *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rL : ℂ) * (b + (d : ℂ))) *
    Complex.cos (4 * π * (Real.sqrt a : ℂ) * (rR : ℂ) * (b - (d : ℂ)))

private lemma spinGeff_strip_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {c : ℝ}, 40 ≤ c →
        let n := c - 1
        let a := n / 12
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ →
          ∀ b ∈ spinStrip (1 / 2), ‖spinGeff a Φ b‖ ≤ C * n ^ 2 * spinM2 a Φ := by
  have hgauss_int : Integrable (fun d : ℝ => Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) volume := by
    have hpos : 0 < (spinSigma0 ^ 2)⁻¹ := by unfold spinSigma0; positivity
    simpa [div_eq_mul_inv, mul_comm] using integrable_exp_neg_mul_sq hpos
  set G₀ : ℝ := ∫ d : ℝ, Real.exp (-(d ^ 2 / spinSigma0 ^ 2))
  have hG₀_pos : 0 < G₀ := by
    have hlow : (0 : ℝ) < ∫ _ in Icc (0 : ℝ) 1, Real.exp (-(1 / spinSigma0 ^ 2)) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le zero_le_one]
      positivity
    have hle1 : ∫ _ in Icc (0 : ℝ) 1, Real.exp (-(1 / spinSigma0 ^ 2)) ≤
        ∫ d in Icc (0 : ℝ) 1, Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
      refine setIntegral_mono_on (integrableOn_const (hs := measure_Icc_lt_top.ne))
        (hgauss_int.integrableOn) measurableSet_Icc fun d hd => ?_
      have hd2 : d ^ 2 ≤ 1 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg d)
          (abs_le.mpr ⟨by linarith [hd.1], hd.2⟩) 2
      have hsig : 0 < spinSigma0 ^ 2 := by unfold spinSigma0; positivity
      exact Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hd2 hsig.le))
    have hle2 : ∫ d in Icc (0 : ℝ) 1, Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) ≤ G₀ :=
      setIntegral_le_integral hgauss_int (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    linarith
  have hxi : 0 < Real.tanh (xiStar / 2) ^ 4 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact pow_pos (div_pos (Real.sinh_pos_iff.mpr (half_pos xiStar_pos)) (Real.cosh_pos _)) 4
  set C_hb0 : ℝ := 4 * (1 + xiStar ^ 2) / Real.tanh (xiStar / 2) ^ 4 * (4 / 3)
  have hC_hb0 : 0 < C_hb0 := by positivity
  set C₁ : ℝ := C_hb0 * G₀ * Real.exp (2 * π)
  set C₂ : ℝ := C_hb0 * G₀ * 16 * 256
  set C₃ : ℝ := spinHbWideConst * G₀
  set C_13 : ℝ := max C₁ C₃
  set C_pref : ℝ := 1 / (Real.sqrt π * spinSigma0)
  have hC_pref : 0 < C_pref := by dsimp [C_pref]; unfold spinSigma0; positivity
  set C_main : ℝ := C_pref * (C_13 * (32 / 10) + C₂ * (1 / 144))
  refine ⟨C_main, by have := spinHbWideConst_pos; positivity, fun {c} hc => ?_⟩
  intro n a Φ hΦ b hb
  have hn_ge : 39 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha_ge : 2 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hb_im : |b.im| < 1 / 2 := hb
  set θ : ℝ := max (1 / 24) |b.im|
  have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hθ1 : θ < 1 / 2 := max_lt (by norm_num) hb_im
  have hint_θ := integrable_spinITheta ha_ge hθ0 hθ1 hΦ
  -- Fubini: `spinGeff a Φ b = -C_pref * ∫ p, (Φ p : ℂ) * spinKb a b p.1 p.2`
  have hswap : spinGeff a Φ b = -((C_pref : ℂ) * ∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKb a b p.1 p.2) := by
    let Fjoint : ℝ × (ℝ × ℝ) → ℂ := fun q =>
      spinHb b q.1 * ((Φ q.2 : ℂ) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.1 : ℂ) * (b + (q.1 : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.2 : ℂ) * (b - (q.1 : ℂ))))
    have hFjoint_meas : AEStronglyMeasurable Fjoint (volume.prod volume) := by
      have hhb_cont : Continuous (fun d : ℝ => spinHb b d) := by
        unfold spinHb
        have hw1_ne : ∀ d : ℝ, Complex.cosh ((b + (d : ℂ)) / 2) ≠ 0 := fun d => by
          refine (complex_tanh_bound_and_deriv ?_).1
          simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, add_zero]
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        have hw2_ne : ∀ d : ℝ, Complex.cosh ((b - (d : ℂ)) / 2) ≠ 0 := fun d => by
          refine (complex_tanh_bound_and_deriv ?_).1
          simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        have ht1 : Continuous (fun d : ℝ => Complex.tanh ((b + (d : ℂ)) / 2)) := by
          simp_rw [Complex.tanh_eq_sinh_div_cosh]
          exact Continuous.div (by fun_prop) (by fun_prop) hw1_ne
        have ht2 : Continuous (fun d : ℝ => Complex.tanh ((b - (d : ℂ)) / 2)) := by
          simp_rw [Complex.tanh_eq_sinh_div_cosh]
          exact Continuous.div (by fun_prop) (by fun_prop) hw2_ne
        exact (((continuous_const.mul ((ht1.pow 2).mul (ht2.pow 2))).div_const _).mul (by fun_prop))
      have hcont : Continuous Fjoint := by
        have hc1 := hhb_cont.comp (continuous_fst : Continuous (fun q : ℝ × (ℝ × ℝ) => q.1))
        have hc2 : Continuous (fun q : ℝ × (ℝ × ℝ) => (Φ q.2 : ℂ)) :=
          Complex.continuous_ofReal.comp (hΦ.cont.comp continuous_snd)
        fun_prop
      exact hcont.aestronglyMeasurable
    have hdom_prod : Integrable (fun q : ℝ × (ℝ × ℝ) =>
        (C_hb0 * Real.exp (-(q.1 ^ 2 / spinSigma0 ^ 2))) *
          (|Φ q.2| * Real.cosh (4 * π * Real.sqrt a * θ * q.2.1) *
            Real.cosh (4 * π * Real.sqrt a * θ * q.2.2))) (volume.prod volume) :=
      (hgauss_int.const_mul C_hb0).mul_prod hint_θ
    have hFjoint_int : Integrable Fjoint (volume.prod volume) := by
      refine hdom_prod.mono' hFjoint_meas (Eventually.of_forall fun q => ?_)
      have h1 := (spinHb_bound_and_deriv hb_im.le q.1).choose_spec.2.1
      have him1 : (4 * π * (Real.sqrt a : ℂ) * (q.2.1 : ℂ) * (b + (q.1 : ℂ))).im =
          4 * π * Real.sqrt a * q.2.1 * b.im := by
        simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
      have him2 : (4 * π * (Real.sqrt a : ℂ) * (q.2.2 : ℂ) * (b - (q.1 : ℂ))).im =
          4 * π * Real.sqrt a * q.2.2 * b.im := by
        simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
      have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.1 : ℂ) * (b + (q.1 : ℂ)))‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θ * q.2.1) := by
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * q.2.1 * b.im) := by
              rw [← him1]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * q.2.1) :=
              cosh_mul_im_le_cosh ha0 hθ0.le (le_max_right _ _)
      have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (q.2.2 : ℂ) * (b - (q.1 : ℂ)))‖ ≤
          Real.cosh (4 * π * Real.sqrt a * θ * q.2.2) := by
        calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * q.2.2 * b.im) := by
              rw [← him2]; exact norm_complex_cos_le_cosh _
          _ ≤ Real.cosh (4 * π * Real.sqrt a * θ * q.2.2) :=
              cosh_mul_im_le_cosh ha0 hθ0.le (le_max_right _ _)
      dsimp [Fjoint]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul h1 (mul_le_mul (mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)) hc2
        (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le)) (by positivity)
        (by positivity)
    have hfub := integral_integral_swap (f := fun d p => Fjoint (d, p)) hFjoint_int
    unfold spinGeff spinGC
    -- Rewrite LHS `∫ d, spinHb b d * -(∫ p, ...)` to `-(∫ d, ∫ p, Fjoint (d, p))`
    have hL : ∫ d : ℝ, spinHb b d * (-(∫ p : ℝ × ℝ, (Φ p : ℂ) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))) *
        Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ))))) =
        -(∫ d : ℝ, ∫ p : ℝ × ℝ, Fjoint (d, p)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun d => ?_)
      dsimp only
      rw [mul_neg, ← integral_const_mul]
    have hR : ∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKb a b p.1 p.2 =
        ∫ p : ℝ × ℝ, ∫ d : ℝ, Fjoint (d, p) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      unfold spinKb
      dsimp only
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun d => ?_)
      dsimp [Fjoint]; ring
    rw [hL, hfub, ← hR]
    ring
  -- Now bound `‖spinKb a b p.1 p.2‖` in the three regions
  have hKb_bound : ∀ p : ℝ × ℝ,
      ‖spinKb a b p.1 p.2‖ ≤ C_13 + C₂ * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 := by
    intro p
    set S : ℝ := |p.1| + |p.2|
    set D : ℝ := |(|p.1| - |p.2|)|
    have hS_nn : 0 ≤ S := by positivity
    have hD_nn : 0 ≤ D := abs_nonneg _
    have hKb_exp : ‖spinKb a b p.1 p.2‖ ≤ C_hb0 * G₀ * Real.exp (2 * π * Real.sqrt a * S) := by
      have hbd_d : ∀ d : ℝ, ‖spinHb b d *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))) *
          Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ)))‖ ≤
          (C_hb0 * Real.exp (2 * π * Real.sqrt a * S)) * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
        intro d
        have h1 := (spinHb_bound_and_deriv hb_im.le d).choose_spec.2.1
        have him1 : (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))).im =
            4 * π * Real.sqrt a * p.1 * b.im := by
          simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
        have him2 : (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ))).im =
            4 * π * Real.sqrt a * p.2 * b.im := by
          simp [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re]
        have hc1 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ)))‖ ≤
            Real.exp (2 * π * Real.sqrt a * |p.1|) := by
          calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.1 * b.im) := by
                rw [← him1]; exact norm_complex_cos_le_cosh _
            _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 2) * p.1) :=
                cosh_mul_im_le_cosh ha0 (by norm_num) hb_im.le
            _ ≤ Real.exp (2 * π * Real.sqrt a * |p.1|) := by
                rw [← Real.cosh_abs, Real.cosh_eq, abs_mul,
                  abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * (1 / 2))]
                have h2p : 4 * π * Real.sqrt a * (1 / 2) * |p.1| = 2 * π * Real.sqrt a * |p.1| := by ring
                rw [h2p]
                linarith [Real.exp_le_exp.mpr (by linarith [show 0 ≤ 2 * π * Real.sqrt a * |p.1| by positivity] :
                  -(2 * π * Real.sqrt a * |p.1|) ≤ 2 * π * Real.sqrt a * |p.1|)]
        have hc2 : ‖Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ)))‖ ≤
            Real.exp (2 * π * Real.sqrt a * |p.2|) := by
          calc ‖Complex.cos _‖ ≤ Real.cosh (4 * π * Real.sqrt a * p.2 * b.im) := by
                rw [← him2]; exact norm_complex_cos_le_cosh _
            _ ≤ Real.cosh (4 * π * Real.sqrt a * (1 / 2) * p.2) :=
                cosh_mul_im_le_cosh ha0 (by norm_num) hb_im.le
            _ ≤ Real.exp (2 * π * Real.sqrt a * |p.2|) := by
                rw [← Real.cosh_abs, Real.cosh_eq, abs_mul,
                  abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a * (1 / 2))]
                have h2p : 4 * π * Real.sqrt a * (1 / 2) * |p.2| = 2 * π * Real.sqrt a * |p.2| := by ring
                rw [h2p]
                linarith [Real.exp_le_exp.mpr (by linarith [show 0 ≤ 2 * π * Real.sqrt a * |p.2| by positivity] :
                  -(2 * π * Real.sqrt a * |p.2|) ≤ 2 * π * Real.sqrt a * |p.2|)]
        rw [norm_mul, norm_mul]
        calc ‖spinHb b d‖ * ‖Complex.cos _‖ * ‖Complex.cos _‖
            ≤ (C_hb0 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))) *
                Real.exp (2 * π * Real.sqrt a * |p.1|) *
                Real.exp (2 * π * Real.sqrt a * |p.2|) :=
              mul_le_mul (mul_le_mul h1 hc1 (norm_nonneg _) (by positivity)) hc2
                (norm_nonneg _) (by positivity)
          _ = (C_hb0 * Real.exp (2 * π * Real.sqrt a * S)) * Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) := by
              rw [mul_assoc (C_hb0 * Real.exp (-(d ^ 2 / spinSigma0 ^ 2))), ← Real.exp_add]
              dsimp [S]; ring_nf
      unfold spinKb
      refine (norm_integral_le_integral_norm _).trans ?_
      calc ∫ d : ℝ, ‖spinHb b d * Complex.cos _ * Complex.cos _‖
          ≤ ∫ d : ℝ, (C_hb0 * Real.exp (2 * π * Real.sqrt a * S)) *
              Real.exp (-(d ^ 2 / spinSigma0 ^ 2)) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hgauss_int.const_mul _) (Eventually.of_forall hbd_d)
        _ = C_hb0 * G₀ * Real.exp (2 * π * Real.sqrt a * S) := by
            rw [integral_const_mul]; dsimp [G₀]; ring
    by_cases hS_small : S ≤ (Real.sqrt a)⁻¹
    · have h1 : ‖spinKb a b p.1 p.2‖ ≤ C₁ := by
        calc ‖spinKb a b p.1 p.2‖ ≤ C_hb0 * G₀ * Real.exp (2 * π * Real.sqrt a * S) := hKb_exp
          _ ≤ C_hb0 * G₀ * Real.exp (2 * π * Real.sqrt a * (Real.sqrt a)⁻¹) := by gcongr
          _ = C₁ := by
              rw [mul_assoc (2 * π), mul_inv_cancel₀ hsqa.ne', mul_one]
      have h2 : 0 ≤ C₂ * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (spinV1_nonneg ha_ge p.1))
          (spinV1_nonneg ha_ge p.2)
      linarith [le_max_left C₁ C₃]
    · push Not at hS_small
      by_cases hD_small : D ≤ S / 2
      · -- Off-axis cone: both `|p.1|, |p.2| ≥ (S - D) / 2 ≥ S / 4 > (4 √a)⁻¹`
        have hm1 : 1 / 4 ≤ min 1 (Real.sqrt a * |p.1|) := by
          refine le_min (by norm_num) ?_
          have h1 : (Real.sqrt a)⁻¹ / 4 ≤ |p.1| := by
            have := abs_sub_abs_le_abs_sub |p.1| |p.2|
            have hle : S - D ≤ 2 * |p.1| := by
              dsimp [S, D]
              rcases le_total |p.1| |p.2| with h | h
              · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
              · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
            linarith
          calc 1 / 4 = Real.sqrt a * ((Real.sqrt a)⁻¹ / 4) := by field_simp [hsqa.ne']
            _ ≤ Real.sqrt a * |p.1| := by gcongr
        have hm2 : 1 / 4 ≤ min 1 (Real.sqrt a * |p.2|) := by
          refine le_min (by norm_num) ?_
          have h1 : (Real.sqrt a)⁻¹ / 4 ≤ |p.2| := by
            have hle : S - D ≤ 2 * |p.2| := by
              dsimp [S, D]
              rcases le_total |p.1| |p.2| with h | h
              · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith
              · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
            linarith
          calc 1 / 4 = Real.sqrt a * ((Real.sqrt a)⁻¹ / 4) := by field_simp [hsqa.ne']
            _ ≤ Real.sqrt a * |p.2| := by gcongr
        have hv1 := spinV1_ge_inv_four_a_exp_min_sq ha_ge p.1
        have hv2 := spinV1_ge_inv_four_a_exp_min_sq ha_ge p.2
        have hexp_le : Real.exp (2 * π * Real.sqrt a * S) ≤
            16 * 256 * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 := by
          have hprod : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |p.1|) * (1 / 4 : ℝ) ^ 2) *
              ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |p.2|) * (1 / 4 : ℝ) ^ 2) ≤
              spinV1 a p.1 * spinV1 a p.2 := by
            refine mul_le_mul ?_ ?_ (by positivity) (spinV1_nonneg ha_ge p.1)
            · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hm1 2) (by positivity)).trans hv1
            · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hm2 2) (by positivity)).trans hv2
          have hlhs : ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |p.1|) * (1 / 4 : ℝ) ^ 2) *
              ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |p.2|) * (1 / 4 : ℝ) ^ 2) =
              (16 * 256 * a ^ 2)⁻¹ * Real.exp (2 * π * Real.sqrt a * S) := by
            rw [show ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |p.1|) * (1 / 4 : ℝ) ^ 2) *
                ((4 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |p.2|) * (1 / 4 : ℝ) ^ 2) =
                ((4 * a)⁻¹ * (1 / 4 : ℝ) ^ 2) ^ 2 *
                  (Real.exp (2 * π * Real.sqrt a * |p.1|) * Real.exp (2 * π * Real.sqrt a * |p.2|)) by ring,
              ← Real.exp_add]
            have hex : 2 * π * Real.sqrt a * |p.1| + 2 * π * Real.sqrt a * |p.2| =
                2 * π * Real.sqrt a * S := by dsimp [S]; ring
            rw [hex]; field_simp [ha0.ne']; ring
          rw [hlhs] at hprod
          calc Real.exp (2 * π * Real.sqrt a * S)
              = (16 * 256 * a ^ 2) * ((16 * 256 * a ^ 2)⁻¹ * Real.exp (2 * π * Real.sqrt a * S)) := by
                field_simp [ha0.ne']
            _ ≤ (16 * 256 * a ^ 2) * (spinV1 a p.1 * spinV1 a p.2) := by gcongr
            _ = 16 * 256 * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 := by ring
        have hkb2 : ‖spinKb a b p.1 p.2‖ ≤ C₂ * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 := by
          calc ‖spinKb a b p.1 p.2‖ ≤ C_hb0 * G₀ * Real.exp (2 * π * Real.sqrt a * S) := hKb_exp
            _ ≤ C_hb0 * G₀ * (16 * 256 * a ^ 2 * spinV1 a p.1 * spinV1 a p.2) := by gcongr
            _ = C₂ * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 := by dsimp [C₂]; ring
        have hC13_nn : 0 ≤ C_13 := le_trans (by positivity : 0 ≤ C₁) (le_max_left _ _)
        linarith
      · push Not at hD_small
        -- Near-axis cone `D > S / 2`: expand cosines and shift `d`-contour to `±2i`
        let term : ℝ → ℝ → ℂ := fun s₁ s₂ =>
          ∫ d : ℝ, spinHb b d * Complex.exp (I *
            (((4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) : ℝ) : ℂ) * b +
              ((4 * π * Real.sqrt a * (s₁ * p.1 - s₂ * p.2) : ℝ) : ℂ) * (d : ℂ)))
        have hterm_bd : ∀ (s₁ s₂ : ℝ), |s₁| = 1 → |s₂| = 1 → ‖term s₁ s₂‖ ≤ C₃ := by
          intro s₁ s₂ hs₁ hs₂
          set β : ℝ := 4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2)
          set ω : ℝ := 4 * π * Real.sqrt a * (s₁ * p.1 - s₂ * p.2)
          set σ : ℝ := if 0 ≤ ω then 1 else -1
          have hσ : |σ| ≤ 1 := by dsimp [σ]; split_ifs <;> norm_num
          have hσω : σ * ω = |ω| := by
            dsimp [σ]
            split_ifs with h
            · rw [one_mul, abs_of_nonneg h]
            · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
          have hβ_bd : |β| ≤ 4 * π * Real.sqrt a * S := by
            dsimp [β, S]
            rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]
            have htri : |s₁ * p.1 + s₂ * p.2| ≤ |p.1| + |p.2| := by
              calc |s₁ * p.1 + s₂ * p.2| ≤ |s₁ * p.1| + |s₂ * p.2| := abs_add_le _ _
                _ = |s₁| * |p.1| + |s₂| * |p.2| := by rw [abs_mul, abs_mul]
                _ = |p.1| + |p.2| := by rw [hs₁, hs₂, one_mul, one_mul]
            exact mul_le_mul_of_nonneg_left htri (by positivity)
          have hω_bd : 4 * π * Real.sqrt a * D ≤ |ω| := by
            dsimp [ω, D]
            rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π * Real.sqrt a)]
            have hrev : |(|p.1| - |p.2|)| ≤ |s₁ * p.1 - s₂ * p.2| := by
              have h1 : |(|s₁ * p.1| - |s₂ * p.2|)| ≤ |s₁ * p.1 - s₂ * p.2| := abs_abs_sub_abs_le_abs_sub _ _
              simp only [abs_mul, hs₁, hs₂, one_mul] at h1
              exact h1
            exact mul_le_mul_of_nonneg_left hrev (by positivity)
          have hshift := gaussian_contour_shift hb β ω σ hσ
          dsimp [term]
          rw [hshift]
          have hbd_t : ∀ t : ℝ, ‖spinHbC b ((t : ℂ) + (2 * σ : ℝ) * I) *
              Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I)))‖ ≤
              spinHbWideConst * Real.exp (-(t ^ 2 / spinSigma0 ^ 2)) := by
            intro t
            have him_w : |((t : ℂ) + (2 * σ : ℝ) * I).im| ≤ 2 := by
              simp [abs_mul]; linarith
            have h1 := (spinHbC_strip_bound_and_diff hb).2 _ him_w
            rw [show ((t : ℂ) + (2 * σ : ℝ) * I).re = t by simp] at h1
            have him_exp : (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I))).re =
                -(β * b.im) - 2 * (σ * ω) := by
              simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]; ring
            have hexp_le1 : ‖Complex.exp (I * ((β : ℂ) * b + (ω : ℂ) * ((t : ℂ) + (2 * σ : ℝ) * I)))‖ ≤ 1 := by
              rw [Complex.norm_exp, him_exp, hσω, Real.exp_le_one_iff]
              have hA : -(β * b.im) ≤ 2 * π * Real.sqrt a * S := by
                calc -(β * b.im) ≤ |β * b.im| := neg_le_abs _
                  _ = |β| * |b.im| := abs_mul _ _
                  _ ≤ (4 * π * Real.sqrt a * S) * (1 / 2) :=
                      mul_le_mul hβ_bd hb_im.le (abs_nonneg _) (by positivity)
                  _ = 2 * π * Real.sqrt a * S := by ring
              have hB : 8 * π * Real.sqrt a * D ≤ 2 * |ω| := by linarith
              have hC : 2 * π * Real.sqrt a * S ≤ 8 * π * Real.sqrt a * D := by
                have : S ≤ 4 * D := by linarith
                calc 2 * π * Real.sqrt a * S ≤ 2 * π * Real.sqrt a * (4 * D) := by gcongr
                  _ = 8 * π * Real.sqrt a * D := by ring
              linarith
            rw [norm_mul]
            calc ‖spinHbC b ((t : ℂ) + (2 * σ : ℝ) * I)‖ * ‖Complex.exp _‖
                ≤ (spinHbWideConst * Real.exp (-(t ^ 2 / spinSigma0 ^ 2))) * 1 := by
                  refine mul_le_mul h1 hexp_le1 (norm_nonneg _) (by
                    have := spinHbWideConst_pos; positivity)
              _ = spinHbWideConst * Real.exp (-(t ^ 2 / spinSigma0 ^ 2)) := by
                  rw [mul_one]
          refine (norm_integral_le_integral_norm _).trans ?_
          calc ∫ t : ℝ, ‖spinHbC b ((t : ℂ) + (2 * σ : ℝ) * I) * Complex.exp _‖
              ≤ ∫ t : ℝ, spinHbWideConst * Real.exp (-(t ^ 2 / spinSigma0 ^ 2)) :=
                integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                  (hgauss_int.const_mul spinHbWideConst) (Eventually.of_forall hbd_t)
            _ = C₃ := by rw [integral_const_mul]
        have hKb_eq : spinKb a b p.1 p.2 =
            (1 / 4 : ℂ) * (term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1)) := by
          -- Each `term s₁ s₂` is integrable, and `cos A * cos B = 1/4 * ∑ exp(...)`
          have hterm_int : ∀ (s₁ s₂ : ℝ), Integrable (fun d : ℝ => spinHb b d * Complex.exp (I *
              (((4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (s₁ * p.1 - s₂ * p.2) : ℝ) : ℂ) * (d : ℂ)))) volume := by
            intro s₁ s₂
            refine (hgauss_int.const_mul (C_hb0 * Real.exp (|4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2)| / 2))).mono' ?_ ?_
            · have hcont : Continuous (fun d : ℝ => spinHb b d * Complex.exp (I *
                  (((4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) : ℝ) : ℂ) * b +
                    ((4 * π * Real.sqrt a * (s₁ * p.1 - s₂ * p.2) : ℝ) : ℂ) * (d : ℂ)))) := by
                have h1 : Continuous (fun d : ℝ => spinHb b d) := by
                  unfold spinHb
                  have hw1_ne : ∀ d : ℝ, Complex.cosh ((b + (d : ℂ)) / 2) ≠ 0 := fun d => by
                    refine (complex_tanh_bound_and_deriv ?_).1
                    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, add_zero]
                    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
                  have hw2_ne : ∀ d : ℝ, Complex.cosh ((b - (d : ℂ)) / 2) ≠ 0 := fun d => by
                    refine (complex_tanh_bound_and_deriv ?_).1
                    simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
                    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
                  have ht1 : Continuous (fun d : ℝ => Complex.tanh ((b + (d : ℂ)) / 2)) := by
                    simp_rw [Complex.tanh_eq_sinh_div_cosh]
                    exact Continuous.div (by fun_prop) (by fun_prop) hw1_ne
                  have ht2 : Continuous (fun d : ℝ => Complex.tanh ((b - (d : ℂ)) / 2)) := by
                    simp_rw [Complex.tanh_eq_sinh_div_cosh]
                    exact Continuous.div (by fun_prop) (by fun_prop) hw2_ne
                  exact (((continuous_const.mul ((ht1.pow 2).mul (ht2.pow 2))).div_const _).mul (by fun_prop))
                exact h1.mul (by fun_prop)
              exact hcont.aestronglyMeasurable
            · exact Eventually.of_forall fun d => by
                have h1 := (spinHb_bound_and_deriv hb_im.le d).choose_spec.2.1
                have him : (I * (((4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) : ℝ) : ℂ) * b +
                    ((4 * π * Real.sqrt a * (s₁ * p.1 - s₂ * p.2) : ℝ) : ℂ) * (d : ℂ))).re =
                    -(4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) * b.im) := by
                  simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
                    Complex.ofReal_re, Complex.ofReal_im]
                have hexp : ‖Complex.exp (I * (((4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) : ℝ) : ℂ) * b +
                    ((4 * π * Real.sqrt a * (s₁ * p.1 - s₂ * p.2) : ℝ) : ℂ) * (d : ℂ)))‖ ≤
                    Real.exp (|4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2)| / 2) := by
                  rw [Complex.norm_exp, him, Real.exp_le_exp]
                  calc -(4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) * b.im)
                      ≤ |4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2) * b.im| := neg_le_abs _
                    _ = |4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2)| * |b.im| := abs_mul _ _
                    _ ≤ |4 * π * Real.sqrt a * (s₁ * p.1 + s₂ * p.2)| * (1 / 2) :=
                        mul_le_mul_of_nonneg_left hb_im.le (abs_nonneg _)
                    _ = _ := by ring
                rw [norm_mul]
                exact (mul_le_mul h1 hexp (norm_nonneg _) (by positivity)).trans_eq (by
                  dsimp [C_hb0]; ring)
          have hpt : ∀ d : ℝ,
              spinHb b d * Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))) *
                Complex.cos (4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ))) =
              (1 / 4 : ℂ) * (
                spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                  ((4 * π * Real.sqrt a * (1 * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ))) +
                spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * p.1 + (-1) * p.2) : ℝ) : ℂ) * b +
                  ((4 * π * Real.sqrt a * (1 * p.1 - (-1) * p.2) : ℝ) : ℂ) * (d : ℂ))) +
                spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * ((-1) * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                  ((4 * π * Real.sqrt a * ((-1) * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ))) +
                spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * ((-1) * p.1 + (-1) * p.2) : ℝ) : ℂ) * b +
                  ((4 * π * Real.sqrt a * ((-1) * p.1 - (-1) * p.2) : ℝ) : ℂ) * (d : ℂ)))) := by
            intro d
            set A : ℂ := 4 * π * (Real.sqrt a : ℂ) * (p.1 : ℂ) * (b + (d : ℂ))
            set B : ℂ := 4 * π * (Real.sqrt a : ℂ) * (p.2 : ℂ) * (b - (d : ℂ))
            have hcosA : Complex.cos A = (Complex.exp (I * A) + Complex.exp (-(I * A))) / 2 := by
              rw [Complex.cos, mul_comm A I, mul_comm (-A) I, mul_neg]
            have hcosB : Complex.cos B = (Complex.exp (I * B) + Complex.exp (-(I * B))) / 2 := by
              rw [Complex.cos, mul_comm B I, mul_comm (-B) I, mul_neg]
            have he1 : I * (((4 * π * Real.sqrt a * (1 * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (1 * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ)) = I * A + I * B := by
              dsimp [A, B]; push_cast; ring
            have he2 : I * (((4 * π * Real.sqrt a * (1 * p.1 + (-1) * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (1 * p.1 - (-1) * p.2) : ℝ) : ℂ) * (d : ℂ)) = I * A + -(I * B) := by
              dsimp [A, B]; push_cast; ring
            have he3 : I * (((4 * π * Real.sqrt a * ((-1) * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * ((-1) * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ)) = -(I * A) + I * B := by
              dsimp [A, B]; push_cast; ring
            have he4 : I * (((4 * π * Real.sqrt a * ((-1) * p.1 + (-1) * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * ((-1) * p.1 - (-1) * p.2) : ℝ) : ℂ) * (d : ℂ)) = -(I * A) + -(I * B) := by
              dsimp [A, B]; push_cast; ring
            rw [he1, he2, he3, he4, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
              hcosA, hcosB]
            ring
          have hi12 : Integrable (fun d : ℝ =>
              spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (1 * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ))) +
              spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * p.1 + (-1) * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (1 * p.1 - (-1) * p.2) : ℝ) : ℂ) * (d : ℂ)))) volume :=
            (hterm_int 1 1).add (hterm_int 1 (-1))
          have hi123 : Integrable (fun d : ℝ =>
              spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (1 * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ))) +
              spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * (1 * p.1 + (-1) * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * (1 * p.1 - (-1) * p.2) : ℝ) : ℂ) * (d : ℂ))) +
              spinHb b d * Complex.exp (I * (((4 * π * Real.sqrt a * ((-1) * p.1 + 1 * p.2) : ℝ) : ℂ) * b +
                ((4 * π * Real.sqrt a * ((-1) * p.1 - 1 * p.2) : ℝ) : ℂ) * (d : ℂ)))) volume :=
            hi12.add (hterm_int (-1) 1)
          unfold spinKb
          simp_rw [hpt]
          rw [integral_const_mul, integral_add hi123 (hterm_int (-1) (-1)),
            integral_add hi12 (hterm_int (-1) 1), integral_add (hterm_int 1 1) (hterm_int 1 (-1))]
        have hKb3 : ‖spinKb a b p.1 p.2‖ ≤ C₃ := by
          rw [hKb_eq, norm_mul]
          have h14 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
          rw [h14]
          have hsum : ‖term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1)‖ ≤ 4 * C₃ := by
            have t1 := hterm_bd 1 1 (by norm_num) (by norm_num)
            have t2 := hterm_bd 1 (-1) (by norm_num) (by norm_num)
            have t3 := hterm_bd (-1) 1 (by norm_num) (by norm_num)
            have t4 := hterm_bd (-1) (-1) (by norm_num) (by norm_num)
            calc ‖term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1)‖
                ≤ ‖term 1 1 + term 1 (-1) + term (-1) 1‖ + ‖term (-1) (-1)‖ := norm_add_le _ _
              _ ≤ ‖term 1 1 + term 1 (-1)‖ + ‖term (-1) 1‖ + ‖term (-1) (-1)‖ := by
                  gcongr; exact norm_add_le _ _
              _ ≤ ‖term 1 1‖ + ‖term 1 (-1)‖ + ‖term (-1) 1‖ + ‖term (-1) (-1)‖ := by
                  gcongr; exact norm_add_le _ _
              _ ≤ 4 * C₃ := by linarith
          linarith
        have h2 : 0 ≤ C₂ * a ^ 2 * spinV1 a p.1 * spinV1 a p.2 :=
          mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (spinV1_nonneg ha_ge p.1))
            (spinV1_nonneg ha_ge p.2)
        linarith [le_max_right C₁ C₃]
  -- Integrate `|Φ p| * ‖spinKb a b p.1 p.2‖` using `spinS21` and `hΦ.int_M2`
  have hs21 := spinS21 hc hΦ
  have hint_abs : Integrable (fun p : ℝ × ℝ => |Φ p|) volume :=
    hΦ.int.norm.congr (Eventually.of_forall fun p => Real.norm_eq_abs _)
  have hint_dom : Integrable (fun p : ℝ × ℝ =>
      C_13 * |Φ p| + C₂ * a ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)) volume :=
    (hint_abs.const_mul C_13).add (hΦ.int_M2.const_mul (C₂ * a ^ 2))
  rw [hswap, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC_pref]
  have hint_le : ‖∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKb a b p.1 p.2‖ ≤
      C_13 * (32 / 10 * spinM2 a Φ) + C₂ * a ^ 2 * spinM2 a Φ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ p : ℝ × ℝ, ‖(Φ p : ℂ) * spinKb a b p.1 p.2‖
        ≤ ∫ p : ℝ × ℝ, (C_13 * |Φ p| + C₂ * a ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint_dom
            (Eventually.of_forall fun p => ?_)
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |Φ p| * ‖spinKb a b p.1 p.2‖
              ≤ |Φ p| * (C_13 + C₂ * a ^ 2 * spinV1 a p.1 * spinV1 a p.2) :=
                mul_le_mul_of_nonneg_left (hKb_bound p) (abs_nonneg _)
            _ = C_13 * |Φ p| + C₂ * a ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
      _ = C_13 * (∫ p : ℝ × ℝ, |Φ p|) + C₂ * a ^ 2 * spinM2 a Φ := by
          rw [integral_add (hint_abs.const_mul C_13) (hΦ.int_M2.const_mul (C₂ * a ^ 2)),
            integral_const_mul, integral_const_mul]; rfl
      _ ≤ C_13 * (32 / 10 * spinM2 a Φ) + C₂ * a ^ 2 * spinM2 a Φ := by
          have hC13_nn : 0 ≤ C_13 := le_trans (by positivity : 0 ≤ C₁) (le_max_left _ _)
          gcongr; exact hs21.2
  have ha_sq : a ^ 2 = (1 / 144 : ℝ) * n ^ 2 := by dsimp [a]; ring
  have hm2_nn : 0 ≤ spinM2 a Φ := spinM2_nonneg ha_ge Φ
  have hn_sq1 : 1 ≤ n ^ 2 := one_le_pow₀ (by linarith)
  calc C_pref * ‖∫ p : ℝ × ℝ, (Φ p : ℂ) * spinKb a b p.1 p.2‖
      ≤ C_pref * (C_13 * (32 / 10 * spinM2 a Φ) + C₂ * a ^ 2 * spinM2 a Φ) := by gcongr
    _ = C_pref * (C_13 * (32 / 10) + C₂ * (1 / 144) * n ^ 2) * spinM2 a Φ := by
        rw [ha_sq]; ring
    _ ≤ C_pref * (C_13 * (32 / 10) * n ^ 2 + C₂ * (1 / 144) * n ^ 2) * spinM2 a Φ := by
        have hC13_nn : 0 ≤ C_13 := le_trans (by positivity : 0 ≤ C₁) (le_max_left _ _)
        have h1 : C_13 * (32 / 10) ≤ C_13 * (32 / 10) * n ^ 2 :=
          le_mul_of_one_le_right (by positivity) hn_sq1
        gcongr
    _ = C_main * n ^ 2 * spinM2 a Φ := by dsimp [C_main]; ring

/-! ### Section 6: Assembly of `SpinS23` -/

theorem spinS23 : SpinS23 := by
  obtain ⟨C_strip, hC_strip, hstrip⟩ := spinGeff_strip_bound
  refine ⟨max C_strip spinGeffL1Const, lt_of_lt_of_le hC_strip (le_max_left _ _), ?_⟩
  intro c hc n a Φ hΦ
  have ha : 2 ≤ a := by dsimp [a, n]; linarith
  have hL1 := spinGeff_weighted_L1 hc hΦ
  have hm2_nn : 0 ≤ spinM2 a Φ := spinM2_nonneg ha Φ
  have hn_nn : 0 ≤ n ^ 2 := sq_nonneg n
  refine ⟨fun b => spinGeff_neg a Φ b, spinGeff_differentiableOn ha hΦ, fun b hb => ?_,
    hL1.1, ?_, fun x₁ hx₁ hpos x hx => spinGeff_real_re_nonneg (by linarith) hΦ x₁ hx₁ hpos x hx⟩
  · exact (hstrip hc hΦ b hb).trans (by gcongr; exact le_max_left _ _)
  · exact hL1.2.trans (by gcongr; exact le_max_right _ _)

#print axioms FormalResearch.ModularBootstrap.Spin.spinS23

end FormalResearch.ModularBootstrap.Spin
