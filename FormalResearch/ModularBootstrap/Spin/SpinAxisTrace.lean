module

public import FormalResearch.ModularBootstrap.Spin.SpinS2xS21

/-!
# Lemma INT-7A (`int:axis-trace`): Everywhere-positive exponential weight bound on `\overline{\mathcal A}_{\rm spin}`

Proves `int:axis-trace` (`CFT/modular_bootstrap/paper/integrality_spin.tex`):
for `c ≥ 40` (`a = (c - 1) / 12 ≥ 13 / 4`) and every `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
with `W_{1/8}(r_L, r_R) = cosh((π/2) √a r_L) cosh((π/2) √a r_R)`:
`∬_{[0,∞)^2} |Φ(r_L, r_R)| W_{1/8}(r_L, r_R) dr_L dr_R ≤ 50 a^{-1/7} M_2[Φ]`.

Follows the paper's proof directly using the sharp factorisation
`V_1(r) ≥ (2 a)⁻¹ exp(2π √a |r|) min(1, √a |r|)²` (`spinning_foundations.tex`),
weighted Hölder/Young with `θ = 1/8, p = 2/7`, and `spinS21` (`‖Φ‖_∞ ≤ ‖Φ‖_1 ≤ 3.2 M_2[Φ]`).
**Proved**, unconditional.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal Pointwise

namespace FormalResearch.ModularBootstrap.Spin

/-- Everywhere-positive exponential weight `W_{1/8}(r_L, r_R) = cosh((π/2)√a r_L) cosh((π/2)√a r_R)`
(`integrality_spin.tex`, Lemma INT-7A). -/
noncomputable def spinW18 (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.cosh (π / 2 * Real.sqrt a * p.1) * Real.cosh (π / 2 * Real.sqrt a * p.2)

lemma spinW18_nonneg (a : ℝ) (p : ℝ × ℝ) : 0 ≤ spinW18 a p := by
  unfold spinW18
  exact mul_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le

lemma spinW18_eq_four_mul (a : ℝ) (p : ℝ × ℝ) :
    spinW18 a p = Real.cosh (4 * π * Real.sqrt a * (1 / 8 : ℝ) * p.1) *
      Real.cosh (4 * π * Real.sqrt a * (1 / 8 : ℝ) * p.2) := by
  unfold spinW18
  congr 2 <;> ring

lemma spinV1_ge_inv_two_a_exp_min_sq {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    (2 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * min 1 (Real.sqrt a * |r|) ^ 2 ≤
      spinV1 a r := by
  have ha0 : 0 < a := by linarith only [ha]
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
    have hexp1 : 4 * π * a * (|r| / (2 * Real.sqrt a)) = 2 * π * Real.sqrt a * |r| := by
      field_simp [hsqa.ne']; rw [Real.sq_sqrt ha0.le]; ring
    have hexp2 : -π * (12 * a) * (1 + spinGamma a) * (|r| / (2 * Real.sqrt a)) / 3 =
        -2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by
      field_simp [hsqa.ne']; rw [Real.sq_sqrt ha0.le]; ring
    have hexp3 : -π * (12 * a) * (1 - spinGamma a) * (|r| / (2 * Real.sqrt a)) / 3 =
        -2 * π * Real.sqrt a * (1 - spinGamma a) * |r| := by
      field_simp [hsqa.ne']; rw [Real.sq_sqrt ha0.le]; ring
    unfold spinCalFc
    rw [hexp1, hexp2, hexp3]
    field_simp [hsqa.ne']
  rw [hfac]
  set y : ℝ := Real.sqrt a * |r|
  set m : ℝ := min 1 y
  have hm_nn : 0 ≤ m := le_min zero_le_one (by positivity)
  have hm_le1 : m ≤ 1 := min_le_left _ _
  have hm_ley : m ≤ y := min_le_right _ _
  have h1m_sub : ∀ {x M : ℝ}, 0 ≤ x → x ≤ M → x / (1 + M) ≤ 1 - Real.exp (-x) := by
    intro x M hx hM
    have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have h2 : Real.exp (-x) ≤ (1 + x)⁻¹ := by
      rw [Real.exp_neg]
      exact inv_anti₀ (by linarith only [hx]) (by linarith only [h1])
    have h3 : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      have : 1 + x ≠ 0 := by linarith only [hx]
      field_simp [this]; ring
    have h4 : x / (1 + M) ≤ x / (1 + x) :=
      div_le_div_of_nonneg_left hx (by linarith only [hx]) (by linarith only [hM])
    linarith only [h2, h3, h4]
  have hfac1 : (2 * π / (1 + 2 * π)) * m ≤
      1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|) := by
    have hx1 : (2 * π) * m ≤ 2 * π := by nlinarith only [pi_pos, hm_le1]
    have hx2 : (2 * π) * m ≤ 2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by
      calc (2 * π) * m ≤ (2 * π) * y := mul_le_mul_of_nonneg_left hm_ley (by positivity)
        _ = (2 * π) * 1 * y := by ring
        _ ≤ (2 * π) * (1 + spinGamma a) * y := by
            gcongr
        _ = 2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by simp [y]; ring
    calc (2 * π / (1 + 2 * π)) * m = (2 * π * m) / (1 + 2 * π) := by ring
      _ ≤ 1 - Real.exp (-(2 * π * m)) := h1m_sub (by positivity) hx1
      _ ≤ 1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|) := by
          have : -2 * π * Real.sqrt a * (1 + spinGamma a) * |r| ≤ -(2 * π * m) := by linarith only [hx2]
          linarith only [Real.exp_le_exp.mpr this]
  have hfac2 : (2 * π / ((1 + π) * a)) * m ≤
      1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|) := by
    have hx1 : (2 * π / a) * m ≤ π := by
      have h2a : 2 / a ≤ 1 := (div_le_one ha0).mpr ha
      calc (2 * π / a) * m = (2 / a) * π * m := by ring
        _ ≤ 1 * π * 1 := mul_le_mul (mul_le_mul_of_nonneg_right h2a pi_pos.le) hm_le1 hm_nn (by positivity)
        _ = π := by ring
    have hx2 : (2 * π / a) * m ≤ 2 * π * Real.sqrt a * (1 - spinGamma a) * |r| := by
      calc (2 * π / a) * m ≤ (2 * π / a) * y := mul_le_mul_of_nonneg_left hm_ley (by positivity)
        _ = 2 * π * (1 / a) * y := by ring
        _ ≤ 2 * π * (1 - spinGamma a) * y := by gcongr
        _ = 2 * π * Real.sqrt a * (1 - spinGamma a) * |r| := by simp [y]; ring
    calc (2 * π / ((1 + π) * a)) * m = ((2 * π / a) * m) / (1 + π) := by
          have h1p_ne : 1 + π ≠ 0 := by positivity
          field_simp [ha0.ne', h1p_ne]
      _ ≤ 1 - Real.exp (-((2 * π / a) * m)) := h1m_sub (by positivity) hx1
      _ ≤ 1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|) := by
          have : -2 * π * Real.sqrt a * (1 - spinGamma a) * |r| ≤ -((2 * π / a) * m) := by linarith only [hx2]
          linarith only [Real.exp_le_exp.mpr this]
  have hpi_lo : (3.14 : ℝ) < π := pi_gt_d2
  have hpi_hi : π < (3.15 : ℝ) := pi_lt_d2
  have hcoef : (1 : ℝ) ≤ (2 * π / (1 + 2 * π)) * (2 * π / (1 + π)) := by
    have hnum : (1 + 2 * π) * (1 + π) ≤ 2 * π * (2 * π) := by nlinarith only [hpi_lo, hpi_hi]
    rw [div_mul_div_comm, one_le_div (by positivity)]
    exact hnum
  have hprod_ge : a⁻¹ * m ^ 2 ≤
      (1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|)) *
      (1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|)) := by
    have h12 := mul_le_mul hfac1 hfac2 (by positivity) (by
      have : 0 ≤ 2 * π * Real.sqrt a * (1 + spinGamma a) * |r| := by positivity
      linarith only [Real.exp_le_one_iff.mpr (by linarith only [this] :
        -2 * π * Real.sqrt a * (1 + spinGamma a) * |r| ≤ 0)])
    have hle : a⁻¹ * m ^ 2 ≤ ((2 * π / (1 + 2 * π)) * m) * ((2 * π / ((1 + π) * a)) * m) := by
      have h12p_ne : 1 + 2 * π ≠ 0 := by positivity
      have h1p_ne : 1 + π ≠ 0 := by positivity
      calc a⁻¹ * m ^ 2 = 1 * (a⁻¹ * m ^ 2) := by ring
        _ ≤ ((2 * π / (1 + 2 * π)) * (2 * π / (1 + π))) * (a⁻¹ * m ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = ((2 * π / (1 + 2 * π)) * m) * ((2 * π / ((1 + π) * a)) * m) := by
            field_simp [ha0.ne', h12p_ne, h1p_ne]
    exact hle.trans h12
  calc (2 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) * m ^ 2
      = (1 / 2 : ℝ) * Real.exp (2 * π * Real.sqrt a * |r|) * (a⁻¹ * m ^ 2) := by ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (2 * π * Real.sqrt a * |r|) *
          ((1 - Real.exp (-2 * π * Real.sqrt a * (1 + spinGamma a) * |r|)) *
           (1 - Real.exp (-2 * π * Real.sqrt a * (1 - spinGamma a) * |r|))) := by gcongr

private noncomputable def axisG (a r : ℝ) : ℝ :=
  (Real.cosh (π / 2 * Real.sqrt a * r) / spinV1 a r ^ (2 / 7 : ℝ)) ^ (7 / 5 : ℝ)

private lemma axisG_nonneg {a : ℝ} (ha : 2 ≤ a) (r : ℝ) : 0 ≤ axisG a r := by
  unfold axisG
  exact Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _

private lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith only [h1, h2]

private lemma axisG_le {a : ℝ} (ha : 2 ≤ a) {r : ℝ} (hr : r ≠ 0) :
    axisG a r ≤ (2 * a) ^ (2 / 5 : ℝ) * (min 1 (Real.sqrt a * |r|)) ^ (-4 / 5 : ℝ) *
      Real.exp (-(π / 10) * Real.sqrt a * |r|) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hmin_pos : 0 < min 1 (Real.sqrt a * |r|) :=
    lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
  have hV1_lb := spinV1_ge_inv_two_a_exp_min_sq ha r
  have hV1_pos : 0 < spinV1 a r := lt_of_lt_of_le (by positivity) hV1_lb
  have hcosh_le : Real.cosh (π / 2 * Real.sqrt a * r) ≤ Real.exp (π / 2 * Real.sqrt a * |r|) := by
    calc Real.cosh (π / 2 * Real.sqrt a * r) ≤ Real.exp |π / 2 * Real.sqrt a * r| := cosh_le_exp_abs _
      _ = Real.exp (π / 2 * Real.sqrt a * |r|) := by
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < π / 2), abs_of_pos hsqa]
  have hV1_rpow : ((2 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
      min 1 (Real.sqrt a * |r|) ^ 2) ^ (2 / 7 : ℝ) ≤ spinV1 a r ^ (2 / 7 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hV1_lb (by norm_num)
  have hdiv_le : Real.cosh (π / 2 * Real.sqrt a * r) / spinV1 a r ^ (2 / 7 : ℝ) ≤
      Real.exp (π / 2 * Real.sqrt a * |r|) /
        ((2 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
          min 1 (Real.sqrt a * |r|) ^ 2) ^ (2 / 7 : ℝ) :=
    div_le_div₀ (by positivity) hcosh_le (by positivity) hV1_rpow
  have hrpow_le : axisG a r ≤
      (Real.exp (π / 2 * Real.sqrt a * |r|) /
        ((2 * a)⁻¹ * Real.exp (2 * π * Real.sqrt a * |r|) *
          min 1 (Real.sqrt a * |r|) ^ 2) ^ (2 / 7 : ℝ)) ^ (7 / 5 : ℝ) :=
    Real.rpow_le_rpow (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_pos.le _)) hdiv_le (by norm_num)
  refine hrpow_le.trans_eq ?_
  have h2a_pos : 0 < 2 * a := by positivity
  have hexp_pos : 0 < Real.exp (2 * π * Real.sqrt a * |r|) := Real.exp_pos _
  rw [Real.div_rpow (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity),
    show (2 / 7 : ℝ) * (7 / 5 : ℝ) = 2 / 5 by norm_num,
    Real.mul_rpow (mul_nonneg (inv_nonneg.mpr h2a_pos.le) hexp_pos.le) (sq_nonneg _),
    Real.mul_rpow (inv_nonneg.mpr h2a_pos.le) hexp_pos.le,
    Real.inv_rpow h2a_pos.le,
    ← Real.exp_mul, ← Real.exp_mul, div_eq_mul_inv, mul_inv, mul_inv,
    inv_inv, ← Real.exp_neg]
  have hneg_rpow : (min 1 (Real.sqrt a * |r|) ^ (2 : ℕ)) ^ (2 / 5 : ℝ) =
      (min 1 (Real.sqrt a * |r|)) ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_natCast (min 1 (Real.sqrt a * |r|)) 2, ← Real.rpow_mul hmin_pos.le]
    norm_num
  rw [hneg_rpow, ← Real.rpow_neg hmin_pos.le, show -(4 / 5 : ℝ) = -4 / 5 by norm_num]
  have hmul : Real.exp (π / 2 * Real.sqrt a * |r| * (7 / 5 : ℝ)) *
        ((2 * a) ^ (2 / 5 : ℝ) * Real.exp (-(2 * π * Real.sqrt a * |r| * (2 / 5 : ℝ))) *
          min 1 (Real.sqrt a * |r|) ^ (-4 / 5 : ℝ)) =
      (2 * a) ^ (2 / 5 : ℝ) * min 1 (Real.sqrt a * |r|) ^ (-4 / 5 : ℝ) *
        (Real.exp (π / 2 * Real.sqrt a * |r| * (7 / 5 : ℝ)) *
          Real.exp (-(2 * π * Real.sqrt a * |r| * (2 / 5 : ℝ)))) := by ring
  rw [hmul, ← Real.exp_add]
  congr 1; congr 1; ring

private lemma axisG_integrable_and_bound {a : ℝ} (ha : 2 ≤ a) :
    Integrable (axisG a) volume ∧
      0 < ∫ r : ℝ, axisG a r ∧
      ∫ r : ℝ, axisG a r ≤ 2 ^ (7 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) * (5 + 10 / π) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr =>
    lt_of_lt_of_le (by
      have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
      positivity) (spinV1_ge_inv_two_a_exp_min_sq ha r)
  have hg_nn : ∀ r : ℝ, 0 ≤ axisG a r := fun r =>
    Real.rpow_nonneg (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg (spinV1_nonneg ha r) _)) _
  have hg_cont : ContinuousOn (axisG a) ({0}ᶜ) := by
    refine ContinuousOn.rpow ?_ continuousOn_const (fun r hr => Or.inl ?_)
    · refine ContinuousOn.div (by fun_prop) ?_ (fun r hr => (Real.rpow_pos_of_pos (hV1_pos r hr) _).ne')
      exact (Continuous.rpow_const (by unfold spinV1; fun_prop) (fun _ => Or.inr (by norm_num))).continuousOn
    · exact (div_pos (Real.cosh_pos _) (Real.rpow_pos_of_pos (hV1_pos r hr) _)).ne'
  have hg_meas : AEStronglyMeasurable (axisG a) volume := by
    have hm : MeasurableSet ({0}ᶜ : Set ℝ) := (isClosed_singleton (x := (0 : ℝ))).isOpen_compl.measurableSet
    have hcomp : ({0}ᶜ : Set ℝ) =ᵐ[volume] (univ : Set ℝ) := by
      rw [ae_eq_set]; exact ⟨by simp, by simp⟩
    have hae : AEStronglyMeasurable (axisG a) (volume.restrict ({0}ᶜ)) := hg_cont.aestronglyMeasurable hm
    rwa [Measure.restrict_congr_set hcomp, Measure.restrict_univ] at hae
  let r₁ : ℝ := (Real.sqrt a)⁻¹
  have hr₁ : 0 < r₁ := inv_pos.mpr hsqa
  let C_g : ℝ := (2 * a) ^ (2 / 5 : ℝ)
  have hC_g_pos : 0 < C_g := by positivity
  let lam0 : ℝ := π / 10 * Real.sqrt a
  have hlam0 : 0 < lam0 := by positivity
  have hint_core : IntegrableOn (axisG a) (Ioo 0 r₁) volume ∧
      ∫ r in Ioo 0 r₁, axisG a r ≤ 5 * 2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) := by
    have hint_rpow : IntervalIntegrable (fun r : ℝ => r ^ (-4 / 5 : ℝ)) volume 0 r₁ :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -4 / 5)
    have hdom : IntegrableOn (fun r : ℝ => (C_g * Real.sqrt a ^ (-4 / 5 : ℝ)) * r ^ (-4 / 5 : ℝ))
        (Ioo 0 r₁) volume :=
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr₁.le).mp hint_rpow).const_mul _
    have hint : IntegrableOn (axisG a) (Ioo 0 r₁) volume := by
      refine hdom.mono' hg_meas.restrict ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun r hr => ?_
      rw [Real.norm_of_nonneg (hg_nn r)]
      have hmin : min 1 (Real.sqrt a * |r|) = Real.sqrt a * r := by
        rw [abs_of_pos hr.1, min_eq_right]
        calc Real.sqrt a * r ≤ Real.sqrt a * r₁ := mul_le_mul_of_nonneg_left hr.2.le hsqa.le
          _ = 1 := mul_inv_cancel₀ hsqa.ne'
      have hexp1 : Real.exp (-(π / 10) * Real.sqrt a * |r|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hsqa.le) (abs_nonneg r))
      have hmin_nn : 0 ≤ Real.sqrt a * r := mul_nonneg hsqa.le hr.1.le
      calc axisG a r ≤ C_g * min 1 (Real.sqrt a * |r|) ^ (-4 / 5 : ℝ) *
            Real.exp (-(π / 10) * Real.sqrt a * |r|) := axisG_le ha hr.1.ne'
        _ ≤ C_g * (Real.sqrt a * r) ^ (-4 / 5 : ℝ) * 1 := by
            rw [hmin]
            exact mul_le_mul_of_nonneg_left hexp1 (mul_nonneg hC_g_pos.le (Real.rpow_nonneg hmin_nn _))
        _ = C_g * Real.sqrt a ^ (-4 / 5 : ℝ) * r ^ (-4 / 5 : ℝ) := by
            rw [mul_one, Real.mul_rpow hsqa.le hr.1.le]; ring
    refine ⟨hint, ?_⟩
    have hmono := setIntegral_mono_on hint hdom measurableSet_Ioo fun r hr => by
      have hmin : min 1 (Real.sqrt a * |r|) = Real.sqrt a * r := by
        rw [abs_of_pos hr.1, min_eq_right]
        calc Real.sqrt a * r ≤ Real.sqrt a * r₁ := mul_le_mul_of_nonneg_left hr.2.le hsqa.le
          _ = 1 := mul_inv_cancel₀ hsqa.ne'
      have hexp1 : Real.exp (-(π / 10) * Real.sqrt a * |r|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hsqa.le) (abs_nonneg r))
      have hmin_nn : 0 ≤ Real.sqrt a * r := mul_nonneg hsqa.le hr.1.le
      calc axisG a r ≤ C_g * min 1 (Real.sqrt a * |r|) ^ (-4 / 5 : ℝ) *
            Real.exp (-(π / 10) * Real.sqrt a * |r|) := axisG_le ha hr.1.ne'
        _ ≤ C_g * (Real.sqrt a * r) ^ (-4 / 5 : ℝ) * 1 := by
            rw [hmin]
            exact mul_le_mul_of_nonneg_left hexp1 (mul_nonneg hC_g_pos.le (Real.rpow_nonneg hmin_nn _))
        _ = C_g * Real.sqrt a ^ (-4 / 5 : ℝ) * r ^ (-4 / 5 : ℝ) := by
            rw [mul_one, Real.mul_rpow hsqa.le hr.1.le]; ring
    have hIoo_eq : ∫ r in Ioo 0 r₁, r ^ (-4 / 5 : ℝ) = 5 * r₁ ^ (1 / 5 : ℝ) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr₁.le,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -4 / 5)), Real.zero_rpow (by norm_num)]
      ring
    refine hmono.trans_eq ?_
    rw [integral_const_mul, hIoo_eq]
    have hr1_eq : r₁ = a ^ (-(1 / 2 : ℝ)) := by
      dsimp [r₁]; rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ha0.le]
    have hsqa_eq : Real.sqrt a = a ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow a
    rw [hr1_eq, hsqa_eq, ← Real.rpow_mul ha0.le, ← Real.rpow_mul ha0.le]
    rw [show C_g = 2 ^ (2 / 5 : ℝ) * a ^ (2 / 5 : ℝ) from Real.mul_rpow zero_le_two ha0.le]
    have ha_comb : a ^ (2 / 5 : ℝ) * a ^ ((1 / 2 : ℝ) * (-4 / 5 : ℝ)) * a ^ (-(1 / 2 : ℝ) * (1 / 5 : ℝ)) =
        a ^ (-(1 / 10 : ℝ)) := by
      rw [← Real.rpow_add ha0, ← Real.rpow_add ha0]
      congr 1; norm_num
    calc 2 ^ (2 / 5 : ℝ) * a ^ (2 / 5 : ℝ) * a ^ ((1 / 2 : ℝ) * (-4 / 5 : ℝ)) * (5 * a ^ (-(1 / 2 : ℝ) * (1 / 5 : ℝ)))
        = 5 * 2 ^ (2 / 5 : ℝ) * (a ^ (2 / 5 : ℝ) * a ^ ((1 / 2 : ℝ) * (-4 / 5 : ℝ)) * a ^ (-(1 / 2 : ℝ) * (1 / 5 : ℝ))) := by ring
      _ = 5 * 2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) := by rw [ha_comb]
  have hint_tail : IntegrableOn (axisG a) (Ici r₁) volume ∧
      ∫ r in Ici r₁, axisG a r ≤ (10 / π) * 2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) := by
    have hdom_full : IntegrableOn (fun r : ℝ => C_g * Real.exp (-lam0 * r)) (Ioi 0) volume :=
      (integrableOn_exp_mul_Ioi (by linarith only [hlam0]) 0).const_mul C_g
    have hdom : IntegrableOn (fun r : ℝ => C_g * Real.exp (-lam0 * r)) (Ici r₁) volume :=
      hdom_full.mono_set (fun _ hr => lt_of_lt_of_le hr₁ hr)
    have hint : IntegrableOn (axisG a) (Ici r₁) volume := by
      refine hdom.mono' hg_meas.restrict ?_
      refine ae_restrict_of_forall_mem measurableSet_Ici fun r hr => ?_
      have hr0 : 0 < r := lt_of_lt_of_le hr₁ hr
      have hmin1 : min 1 (Real.sqrt a * |r|) = 1 := min_eq_left (by
        rw [abs_of_pos hr0]
        calc 1 = Real.sqrt a * r₁ := (mul_inv_cancel₀ hsqa.ne').symm
          _ ≤ Real.sqrt a * r := mul_le_mul_of_nonneg_left hr hsqa.le)
      rw [Real.norm_of_nonneg (hg_nn r)]
      calc axisG a r ≤ C_g * min 1 (Real.sqrt a * |r|) ^ (-4 / 5 : ℝ) *
            Real.exp (-(π / 10) * Real.sqrt a * |r|) := axisG_le ha hr0.ne'
        _ = C_g * Real.exp (-lam0 * r) := by
            rw [hmin1, Real.one_rpow, mul_one, abs_of_pos hr0]; simp [lam0]
    refine ⟨hint, ?_⟩
    have hmono := setIntegral_mono_on hint hdom measurableSet_Ici fun r hr => by
      have hr0 : 0 < r := lt_of_lt_of_le hr₁ hr
      have hmin1 : min 1 (Real.sqrt a * |r|) = 1 := min_eq_left (by
        rw [abs_of_pos hr0]
        calc 1 = Real.sqrt a * r₁ := (mul_inv_cancel₀ hsqa.ne').symm
          _ ≤ Real.sqrt a * r := mul_le_mul_of_nonneg_left hr hsqa.le)
      calc axisG a r ≤ C_g * min 1 (Real.sqrt a * |r|) ^ (-4 / 5 : ℝ) *
            Real.exp (-(π / 10) * Real.sqrt a * |r|) := axisG_le ha hr0.ne'
        _ = C_g * Real.exp (-lam0 * r) := by
            rw [hmin1, Real.one_rpow, mul_one, abs_of_pos hr0]; simp [lam0]
    have hle_Ioi : ∫ r in Ici r₁, C_g * Real.exp (-lam0 * r) ≤
        ∫ r in Ioi 0, C_g * Real.exp (-lam0 * r) :=
      setIntegral_mono_set hdom_full
        (ae_restrict_of_forall_mem measurableSet_Ioi fun r _ => by positivity)
        (Eventually.of_forall fun r hr => lt_of_lt_of_le hr₁ hr)
    have hval : ∫ r in Ioi 0, C_g * Real.exp (-lam0 * r) =
        (10 / π) * 2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) := by
      have hexp_int : ∫ r in Ioi (0 : ℝ), Real.exp (-lam0 * r) = lam0⁻¹ := by
        have hd : ∀ r : ℝ, HasDerivAt (fun x : ℝ => -(lam0⁻¹) * Real.exp (-lam0 * x))
            (Real.exp (-lam0 * r)) r := fun r => by
          have h1 : HasDerivAt (fun x : ℝ => -lam0 * x) (-lam0) r := by
            simpa using (hasDerivAt_id r).const_mul (-lam0)
          have h2 : HasDerivAt (fun x : ℝ => Real.exp (-lam0 * x))
              (Real.exp (-lam0 * r) * -lam0) r := (Real.hasDerivAt_exp (-lam0 * r)).comp r h1
          have h3 := h2.const_mul (-(lam0⁻¹))
          have hval : -(lam0⁻¹) * (Real.exp (-lam0 * r) * -lam0) = Real.exp (-lam0 * r) := by
            field_simp [hlam0.ne']
          rwa [hval] at h3
        have htend : Tendsto (fun x : ℝ => -(lam0⁻¹) * Real.exp (-lam0 * x)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun x : ℝ => -lam0 * x) atTop atBot :=
            tendsto_id.const_mul_atTop_of_neg (by linarith only [hlam0])
          simpa only [mul_zero, Function.comp_def] using
            (Real.tendsto_exp_atBot.comp h1).const_mul (-(lam0⁻¹))
        have hI := integral_Ioi_of_hasDerivAt_of_tendsto
          (hd 0).continuousAt.continuousWithinAt (fun r _ => hd r)
          (integrableOn_exp_mul_Ioi (by linarith only [hlam0]) 0) htend
        simpa only [mul_zero, Real.exp_zero, mul_one, zero_sub, neg_neg] using hI
      have hlam0_eq : lam0 = (π / 10) * a ^ (1 / 2 : ℝ) := by
        simp only [lam0, Real.sqrt_eq_rpow]
      rw [integral_const_mul, hexp_int, hlam0_eq]
      rw [show C_g = 2 ^ (2 / 5 : ℝ) * a ^ (2 / 5 : ℝ) from Real.mul_rpow zero_le_two ha0.le]
      rw [div_eq_mul_inv, mul_inv, ← Real.rpow_neg ha0.le]
      have ha_comb : a ^ (2 / 5 : ℝ) * a ^ (-(1 / 2 : ℝ)) = a ^ (-(1 / 10 : ℝ)) := by
        rw [← Real.rpow_add ha0]; congr 1; norm_num
      calc 2 ^ (2 / 5 : ℝ) * a ^ (2 / 5 : ℝ) * ((π / 10)⁻¹ * a ^ (-(1 / 2 : ℝ)))
          = (π / 10)⁻¹ * 2 ^ (2 / 5 : ℝ) * (a ^ (2 / 5 : ℝ) * a ^ (-(1 / 2 : ℝ))) := by ring
        _ = (10 / π) * 2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) := by rw [ha_comb, inv_div]
    exact hmono.trans (hle_Ioi.trans_eq hval)
  have hint_pos : IntegrableOn (axisG a) (Ioi 0) volume ∧
      ∫ r in Ioi 0, axisG a r ≤ 2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) * (5 + 10 / π) := by
    have hunion : Ioi (0 : ℝ) = Ioo 0 r₁ ∪ Ici r₁ := by
      ext r; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
      constructor
      · intro hr; exact lt_or_ge r r₁ |>.imp (fun h => ⟨hr, h⟩) id
      · rintro (⟨hr, _⟩ | hr); exact hr; exact lt_of_lt_of_le hr₁ hr
    have hdisj : Disjoint (Ioo 0 r₁) (Ici r₁) := by
      rw [Set.disjoint_left]; intro r h1 h2; exact not_le_of_gt h1.2 h2
    refine ⟨by rw [hunion]; exact hint_core.1.union hint_tail.1, ?_⟩
    rw [hunion, setIntegral_union hdisj measurableSet_Ici hint_core.1 hint_tail.1]
    have := add_le_add hint_core.2 hint_tail.2
    linarith only [this]
  have hint_neg : IntegrableOn (axisG a) (Iio 0) volume ∧
      ∫ r in Iio 0, axisG a r = ∫ r in Ioi 0, axisG a r := by
    have heven : ∀ r : ℝ, axisG a (-r) = axisG a r := fun r => by
      simp only [axisG, mul_neg, Real.cosh_neg, spinV1_even]
    have hcomp := hint_pos.1.comp_neg
    have hpre : -Ioi (0 : ℝ) = Iio 0 := by ext r; simp
    rw [hpre] at hcomp
    refine ⟨hcomp.congr_fun (fun r _ => heven r) measurableSet_Iio, ?_⟩
    have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume := Measure.measurePreserving_neg volume
    have h1 := hmp.setIntegral_preimage_emb (MeasurableEquiv.neg ℝ).measurableEmbedding (axisG a) (Ioi 0)
    have hpre2 : (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext x; simp
    rw [hpre2] at h1
    rw [← h1]
    exact setIntegral_congr_fun measurableSet_Iio fun r _ => (heven r).symm
  have hfull_int : Integrable (axisG a) volume := by
    have huniv : (univ : Set ℝ) = Iio 0 ∪ ({0} ∪ Ioi 0) := by
      ext r; simp only [mem_univ, mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, true_iff]
      exact lt_trichotomy r 0
    have h0 : IntegrableOn (axisG a) ({0} : Set ℝ) volume := by
      rw [IntegrableOn, Measure.restrict_eq_zero.mpr Real.volume_singleton]; exact integrable_zero_measure
    rw [← integrableOn_univ, huniv]
    exact hint_neg.1.union (h0.union hint_pos.1)
  have hfull_eq : ∫ r : ℝ, axisG a r = 2 * ∫ r in Ioi 0, axisG a r := by
    rw [← setIntegral_univ, show (univ : Set ℝ) = Iic 0 ∪ Ioi 0 from Iic_union_Ioi.symm,
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        (by
          have hset : Iic (0 : ℝ) = Iio 0 ∪ {0} := Iio_union_right.symm
          rw [hset]
          exact hint_neg.1.union (by
            rw [IntegrableOn, Measure.restrict_eq_zero.mpr Real.volume_singleton]
            exact integrable_zero_measure))
        hint_pos.1,
      integral_Iic_eq_integral_Iio, hint_neg.2, two_mul]
  have hpos_int : 0 < ∫ r : ℝ, axisG a r := by
    rw [hfull_eq]
    have hlt : 0 < ∫ r in Ioi 0, axisG a r := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (ae_restrict_of_forall_mem measurableSet_Ioi fun r _ => hg_nn r)
        hint_pos.1]
      have hsub : Ioi (0 : ℝ) ⊆ Function.support (axisG a) ∩ Ioi 0 := fun r hr => by
        refine ⟨?_, hr⟩
        unfold axisG
        have h1 : 0 < Real.cosh (π / 2 * Real.sqrt a * r) / spinV1 a r ^ (2 / 7 : ℝ) :=
          div_pos (Real.cosh_pos _) (Real.rpow_pos_of_pos (hV1_pos r hr.ne') _)
        exact (Real.rpow_pos_of_pos h1 _).ne'
      exact lt_of_lt_of_le (by simp) (measure_mono hsub)
    linarith only [hlt]
  refine ⟨hfull_int, hpos_int, ?_⟩
  rw [hfull_eq]
  have h2pow : (2 : ℝ) * 2 ^ (2 / 5 : ℝ) = 2 ^ (7 / 5 : ℝ) := by
    nth_rw 1 [← Real.rpow_one 2]
    rw [← Real.rpow_add two_pos]
    congr 1; norm_num
  calc 2 * ∫ r in Ioi 0, axisG a r
      ≤ 2 * (2 ^ (2 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) * (5 + 10 / π)) := by gcongr; exact hint_pos.2
    _ = (2 * 2 ^ (2 / 5 : ℝ)) * a ^ (-(1 / 10 : ℝ)) * (5 + 10 / π) := by ring
    _ = 2 ^ (7 / 5 : ℝ) * a ^ (-(1 / 10 : ℝ)) * (5 + 10 / π) := by rw [h2pow]

/-- **Lemma INT-7A (`int:axis-trace`)**, full `ℝ²` and quadrant forms:
for `c ≥ 40` (`a = (c - 1) / 12`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
`|Φ| * W_{1/8}` is integrable on `ℝ²`, `I_{1/8}[Φ] ≤ 200 a^{-1/7} M_2[Φ]`, and
`∬_{[0,∞)^2} |Φ(r_L, r_R)| W_{1/8}(r_L, r_R) dr_L dr_R ≤ 50 a^{-1/7} M_2[Φ]`. -/
theorem spin_axis_trace {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let a := (c - 1) / 12
    Integrable (fun p : ℝ × ℝ => |Φ p| * spinW18 a p) ∧
    ∫ p : ℝ × ℝ, |Φ p| * spinW18 a p ≤ 200 * a ^ (-(1 / 7 : ℝ)) * spinM2 a Φ ∧
    ∫ p in Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ), |Φ p| * spinW18 a p ≤
      50 * a ^ (-(1 / 7 : ℝ)) * spinM2 a Φ := by
  intro a
  have ha : 2 ≤ a := by dsimp [a]; linarith only [hc]
  have ha0 : 0 < a := by linarith only [ha]
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  obtain ⟨hS21_pt, hS21_L1⟩ := spinS21 hc hΦ
  have hM2_nn : 0 ≤ spinM2 a Φ := spinM2_nonneg ha Φ
  obtain ⟨hg_int, hIg_pos, hIg_ub⟩ := axisG_integrable_and_bound ha
  have hg_prod_int : Integrable (fun p : ℝ × ℝ => axisG a p.1 * axisG a p.2) volume :=
    hg_int.mul_prod hg_int
  have hg_prod_val : ∫ p : ℝ × ℝ, axisG a p.1 * axisG a p.2 = (∫ r : ℝ, axisG a r) ^ 2 := by
    rw [Measure.volume_eq_prod, integral_prod_mul]; ring
  set I_g : ℝ := ∫ r : ℝ, axisG a r
  set M0 : ℝ := (32 / 10 : ℝ) * spinM2 a Φ
  set M2 : ℝ := spinM2 a Φ
  have hfull_bd : Integrable (fun p : ℝ × ℝ => |Φ p| * spinW18 a p) ∧
      ∫ p : ℝ × ℝ, |Φ p| * spinW18 a p ≤ 200 * a ^ (-(1 / 7 : ℝ)) * M2 := by
    by_cases hM2_zero : M2 = 0
    · have hΦ0 : ∀ p : ℝ × ℝ, Φ p = 0 := fun p => by
        have h1 : |Φ p| ≤ (32 / 10 : ℝ) * M2 := (hS21_pt p).trans hS21_L1
        rw [hM2_zero, mul_zero] at h1
        exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
      have heq : (fun p : ℝ × ℝ => |Φ p| * spinW18 a p) = 0 := by
        ext p; simp [hΦ0 p]
      rw [heq, hM2_zero]
      exact ⟨integrable_zero _ _ _, by simp⟩
    have hM2_pos : 0 < M2 := lt_of_le_of_ne hM2_nn (Ne.symm hM2_zero)
    have hM0_pos : 0 < M0 := by positivity
    have hM0_pt : ∀ p : ℝ × ℝ, |Φ p| ≤ M0 := fun p => (hS21_pt p).trans hS21_L1
    let C_bd : ℝ := M2 ^ (2 / 7 : ℝ) * M0 ^ (5 / 7 : ℝ) * I_g ^ (10 / 7 : ℝ)
    have hC_pos : 0 < C_bd := by positivity
    have hV1_pos : ∀ r : ℝ, r ≠ 0 → 0 < spinV1 a r := fun r hr =>
      lt_of_lt_of_le (by
        have hmin : 0 < min 1 (Real.sqrt a * |r|) := lt_min one_pos (mul_pos hsqa (abs_pos.mpr hr))
        positivity) (spinV1_ge_inv_two_a_exp_min_sq ha r)
    have hpt : ∀ᵐ p : ℝ × ℝ, |Φ p| * spinW18 a p ≤
        C_bd * ((2 / 7 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) +
          (5 / 7 : ℝ) * (axisG a p.1 * axisG a p.2 / I_g ^ 2)) := by
      have haxes : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} =ᵐ[volume] (∅ : Set (ℝ × ℝ)) := by
        rw [ae_eq_set]
        refine ⟨?_, by simp⟩
        have hs : {p : ℝ × ℝ | p.1 = 0 ∨ p.2 = 0} = ({0} : Set ℝ) ×ˢ univ ∪ univ ×ˢ ({0} : Set ℝ) := by
          ext p; simp
        rw [hs, Measure.volume_eq_prod, Set.sdiff_empty]
        refine measure_union_null ?_ ?_ <;> (rw [Measure.prod_prod]; simp)
      have hne_ae : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
        filter_upwards [compl_mem_ae_iff.mpr (by simpa using haxes)] with p hp
        simpa [not_or] using hp
      filter_upwards [hne_ae] with p ⟨hp1, hp2⟩
      have hV1_1 := hV1_pos p.1 hp1
      have hV1_2 := hV1_pos p.2 hp2
      have hpow_g : (axisG a p.1 * axisG a p.2) ^ (5 / 7 : ℝ) =
          (Real.cosh (π / 2 * Real.sqrt a * p.1) / spinV1 a p.1 ^ (2 / 7 : ℝ)) *
          (Real.cosh (π / 2 * Real.sqrt a * p.2) / spinV1 a p.2 ^ (2 / 7 : ℝ)) := by
        rw [Real.mul_rpow (axisG_nonneg ha _) (axisG_nonneg ha _)]
        dsimp [axisG]
        rw [← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_1.le _)),
          ← Real.rpow_mul (div_nonneg (Real.cosh_pos _).le (Real.rpow_nonneg hV1_2.le _))]
        norm_num
      have hΦ_pow : |Φ p| ^ (2 / 7 : ℝ) * |Φ p| ^ (5 / 7 : ℝ) = |Φ p| := by
        by_cases h0 : |Φ p| = 0
        · simp [h0]
        · rw [← Real.rpow_add (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0))]; norm_num
      have hpow_M0 : (|Φ p| / M0) ^ (5 / 7 : ℝ) ≤ 1 := by
        have hdiv : |Φ p| / M0 ≤ 1 := (div_le_one hM0_pos).mpr (hM0_pt p)
        exact Real.rpow_le_one (div_nonneg (abs_nonneg _) hM0_pos.le) hdiv (by norm_num)
      have hratio_eq : (|Φ p| * spinW18 a p) / C_bd =
          (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) ^ (2 / 7 : ℝ) *
            (|Φ p| / M0) ^ (5 / 7 : ℝ) * (axisG a p.1 * axisG a p.2 / I_g ^ 2) ^ (5 / 7 : ℝ) := by
        have hI2 : (I_g ^ 2) ^ (5 / 7 : ℝ) = I_g ^ (10 / 7 : ℝ) := by
          rw [← Real.rpow_natCast I_g 2, ← Real.rpow_mul hIg_pos.le]; norm_num
        rw [Real.div_rpow (mul_nonneg (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le) hM2_pos.le,
          Real.div_rpow (abs_nonneg _) hM0_pos.le,
          Real.div_rpow (mul_nonneg (axisG_nonneg ha _) (axisG_nonneg ha _)) (sq_nonneg _),
          hI2, hpow_g, Real.mul_rpow (mul_nonneg (abs_nonneg _) hV1_1.le) hV1_2.le,
          Real.mul_rpow (abs_nonneg _) hV1_1.le]
        unfold spinW18
        rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff hC_pos.ne' (by positivity)]
        have hmain : |Φ p| * (Real.cosh (π / 2 * Real.sqrt a * p.1) * Real.cosh (π / 2 * Real.sqrt a * p.2)) *
              (M2 ^ (2 / 7 : ℝ) * (M0 ^ (5 / 7 : ℝ) * I_g ^ (10 / 7 : ℝ))) =
            (|Φ p| ^ (2 / 7 : ℝ) * |Φ p| ^ (5 / 7 : ℝ)) *
              (spinV1 a p.1 ^ (2 / 7 : ℝ) * (Real.cosh (π / 2 * Real.sqrt a * p.1) / spinV1 a p.1 ^ (2 / 7 : ℝ))) *
              (spinV1 a p.2 ^ (2 / 7 : ℝ) * (Real.cosh (π / 2 * Real.sqrt a * p.2) / spinV1 a p.2 ^ (2 / 7 : ℝ))) *
              C_bd := by
          rw [hΦ_pow]
          field_simp [(Real.rpow_pos_of_pos hV1_1 _).ne', (Real.rpow_pos_of_pos hV1_2 _).ne']
          simp [C_bd]; ring
        linarith only [hmain, show C_bd = M2 ^ (2 / 7 : ℝ) * M0 ^ (5 / 7 : ℝ) * I_g ^ (10 / 7 : ℝ) by rfl]
      have hyoung := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 2 / 7)
        (by norm_num : (0 : ℝ) ≤ 5 / 7)
        (div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg (Φ p)) hV1_1.le) hV1_2.le) hM2_pos.le)
        (div_nonneg (mul_nonneg (axisG_nonneg ha p.1) (axisG_nonneg ha p.2)) (sq_nonneg I_g))
        (by norm_num)
      have hratio_le : (|Φ p| * spinW18 a p) / C_bd ≤
          (2 / 7 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) +
            (5 / 7 : ℝ) * (axisG a p.1 * axisG a p.2 / I_g ^ 2) := by
        rw [hratio_eq]
        calc (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) ^ (2 / 7 : ℝ) *
              (|Φ p| / M0) ^ (5 / 7 : ℝ) * (axisG a p.1 * axisG a p.2 / I_g ^ 2) ^ (5 / 7 : ℝ)
            ≤ (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) ^ (2 / 7 : ℝ) * 1 *
                (axisG a p.1 * axisG a p.2 / I_g ^ 2) ^ (5 / 7 : ℝ) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow_M0 (Real.rpow_nonneg
                  (div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg (Φ p)) hV1_1.le) hV1_2.le) hM2_pos.le) _))
                (Real.rpow_nonneg (div_nonneg (mul_nonneg (axisG_nonneg ha p.1) (axisG_nonneg ha p.2)) (sq_nonneg I_g)) _)
          _ = (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) ^ (2 / 7 : ℝ) *
                (axisG a p.1 * axisG a p.2 / I_g ^ 2) ^ (5 / 7 : ℝ) := by ring
          _ ≤ _ := hyoung
      exact (div_le_iff₀ hC_pos).mp hratio_le |>.trans_eq (by ring)
    have hint_rhs : Integrable (fun p : ℝ × ℝ =>
        C_bd * ((2 / 7 : ℝ) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2 / M2) +
          (5 / 7 : ℝ) * (axisG a p.1 * axisG a p.2 / I_g ^ 2))) volume :=
      (((hΦ.int_M2.div_const M2).const_mul (2 / 7 : ℝ)).add
        ((hg_prod_int.div_const (I_g ^ 2)).const_mul (5 / 7 : ℝ))).const_mul C_bd
    have hint_lhs : Integrable (fun p : ℝ × ℝ => |Φ p| * spinW18 a p) volume := by
      refine hint_rhs.mono' ?_ (by filter_upwards [hpt] with p hp; rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (spinW18_nonneg _ _))]; exact hp)
      have hW_cont : Continuous (spinW18 a) := by unfold spinW18; fun_prop
      exact (hΦ.cont.abs.mul hW_cont).aestronglyMeasurable
    have hint_le : ∫ p : ℝ × ℝ, |Φ p| * spinW18 a p ≤ C_bd := by
      have h1 := integral_mono_ae hint_lhs hint_rhs hpt
      rw [integral_const_mul, integral_add ((hΦ.int_M2.div_const M2).const_mul _) ((hg_prod_int.div_const _).const_mul _),
        integral_const_mul, integral_const_mul, integral_div, integral_div, hg_prod_val] at h1
      have hM2_id : (∫ p : ℝ × ℝ, |Φ p| * spinV1 a p.1 * spinV1 a p.2) / M2 = 1 :=
        div_self hM2_pos.ne'
      have hIg_id : I_g ^ 2 / I_g ^ 2 = 1 := div_self (pow_ne_zero 2 hIg_pos.ne')
      rw [hM2_id, hIg_id] at h1
      linarith only [h1]
    have hC_bound : C_bd ≤ 200 * a ^ (-(1 / 7 : ℝ)) * M2 := by
      have hM2_comb : M2 ^ (2 / 7 : ℝ) * M0 ^ (5 / 7 : ℝ) = (32 / 10 : ℝ) ^ (5 / 7 : ℝ) * M2 := by
        dsimp [M0]
        rw [Real.mul_rpow (by norm_num) hM2_pos.le]
        have hadd : M2 ^ (2 / 7 : ℝ) * M2 ^ (5 / 7 : ℝ) = M2 := by
          rw [← Real.rpow_add hM2_pos]; norm_num
        calc M2 ^ (2 / 7 : ℝ) * ((32 / 10 : ℝ) ^ (5 / 7 : ℝ) * M2 ^ (5 / 7 : ℝ))
            = (32 / 10 : ℝ) ^ (5 / 7 : ℝ) * (M2 ^ (2 / 7 : ℝ) * M2 ^ (5 / 7 : ℝ)) := by ring
          _ = (32 / 10 : ℝ) ^ (5 / 7 : ℝ) * M2 := by rw [hadd]
      have hIg10 : I_g ^ (10 / 7 : ℝ) ≤
          4 * a ^ (-(1 / 7 : ℝ)) * (5 + 10 / π) ^ (10 / 7 : ℝ) := by
        have hpow := Real.rpow_le_rpow hIg_pos.le hIg_ub (by norm_num : (0 : ℝ) ≤ 10 / 7)
        refine hpow.trans_eq ?_
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul zero_le_two, ← Real.rpow_mul ha0.le]
        norm_num
      have hpi_lo : (3.14 : ℝ) < π := pi_gt_d2
      have hnum : (32 / 10 : ℝ) ^ (5 / 7 : ℝ) * (5 + 10 / π) ^ (10 / 7 : ℝ) ≤ 50 := by
        have h8 : 5 + 10 / π ≤ (5 + 10 / 3.14 : ℝ) := by gcongr
        have h7 : ((32 / 10 : ℝ) ^ (5 / 7 : ℝ) * (5 + 10 / π) ^ (10 / 7 : ℝ)) ^ 7 ≤ (50 : ℝ) ^ 7 := by
          rw [mul_pow, ← Real.rpow_natCast ((32 / 10 : ℝ) ^ _), ← Real.rpow_natCast ((5 + 10 / π) ^ _),
            ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by positivity)]
          push_cast
          rw [show (5 / 7 : ℝ) * 7 = ((5 : ℕ) : ℝ) by norm_num,
            show (10 / 7 : ℝ) * 7 = ((10 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast, Real.rpow_natCast]
          have hpow10 : (5 + 10 / π) ^ (10 : ℕ) ≤ (5 + 10 / (3.14 : ℝ)) ^ (10 : ℕ) :=
            pow_le_pow_left₀ (by positivity) h8 10
          have hrhs : (32 / 10 : ℝ) ^ (5 : ℕ) * (5 + 10 / (3.14 : ℝ)) ^ (10 : ℕ) ≤ (50 : ℝ) ^ 7 := by norm_num
          exact (mul_le_mul_of_nonneg_left hpow10 (by positivity)).trans hrhs
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h7
      calc C_bd = (32 / 10 : ℝ) ^ (5 / 7 : ℝ) * M2 * I_g ^ (10 / 7 : ℝ) := by
            dsimp [C_bd]; rw [hM2_comb]
        _ ≤ (32 / 10 : ℝ) ^ (5 / 7 : ℝ) * M2 * (4 * a ^ (-(1 / 7 : ℝ)) * (5 + 10 / π) ^ (10 / 7 : ℝ)) := by
            gcongr
        _ = (4 * ((32 / 10 : ℝ) ^ (5 / 7 : ℝ) * (5 + 10 / π) ^ (10 / 7 : ℝ))) * a ^ (-(1 / 7 : ℝ)) * M2 := by ring
        _ ≤ (4 * 50) * a ^ (-(1 / 7 : ℝ)) * M2 := by gcongr
        _ = 200 * a ^ (-(1 / 7 : ℝ)) * M2 := by ring
    exact ⟨hint_lhs, hint_le.trans hC_bound⟩
  refine ⟨hfull_bd.1, hfull_bd.2, ?_⟩
  let F : ℝ × ℝ → ℝ := fun p => |Φ p| * spinW18 a p
  have hFeven1 : ∀ rL rR : ℝ, F (-rL, rR) = F (rL, rR) := fun rL rR => by
    simp only [F, spinW18, hΦ.d4_inv.1 rL rR, mul_neg, Real.cosh_neg]
  have hFeven2 : ∀ rL rR : ℝ, F (rL, -rR) = F (rL, rR) := fun rL rR => by
    simp only [F, spinW18, hΦ.d4_inv.2.1 rL rR, mul_neg, Real.cosh_neg]
  have hI_quad : ∫ p : ℝ × ℝ, F p = 4 * ∫ p in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ), F p := by
    have h_even_split : ∀ {f : ℝ → ℝ}, Integrable f volume → (∀ r : ℝ, f (-r) = f r) →
        ∫ r : ℝ, f r = 2 * ∫ r in Ici (0 : ℝ), f r := fun {f} hf hev => by
      have hi : ∫ r in Iio (0 : ℝ), f r = ∫ r in Ioi (0 : ℝ), f r := by
        have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume := Measure.measurePreserving_neg volume
        have h1 := hmp.setIntegral_preimage_emb (MeasurableEquiv.neg ℝ).measurableEmbedding f (Ioi 0)
        have hpre2 : (fun x : ℝ => -x) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext x; simp
        rw [hpre2] at h1
        rw [← h1]
        exact setIntegral_congr_fun measurableSet_Iio fun r _ => (hev r).symm
      rw [← setIntegral_univ, show (univ : Set ℝ) = Iic 0 ∪ Ioi 0 from Iic_union_Ioi.symm,
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf.integrableOn hf.integrableOn,
        integral_Iic_eq_integral_Iio, hi, ← integral_Ici_eq_integral_Ioi, two_mul]
    let g₁ : ℝ → ℝ := fun rL => ∫ rR : ℝ, F (rL, rR)
    have hF_int : Integrable F (volume.prod volume) := by simpa [Measure.volume_eq_prod] using hfull_bd.1
    have hfull : ∫ p : ℝ × ℝ, F p = ∫ rL : ℝ, g₁ rL := by
      rw [Measure.volume_eq_prod, integral_prod F hF_int]
    have hg1_even : ∀ rL : ℝ, g₁ (-rL) = g₁ rL := fun rL =>
      integral_congr_ae (Eventually.of_forall fun rR => hFeven1 rL rR)
    have hleft_right : ∫ rL : ℝ, g₁ rL = 2 * ∫ rL in Ici (0 : ℝ), g₁ rL :=
      h_even_split hF_int.integral_prod_left hg1_even
    have hg1_ae : ∀ᵐ rL ∂(volume.restrict (Ici 0)),
        g₁ rL = 2 * ∫ rR in Ici (0 : ℝ), F (rL, rR) := by
      filter_upwards [ae_restrict_of_ae hF_int.prod_right_ae] with rL hIntR
      exact h_even_split hIntR (hFeven2 rL)
    have hprod_quad : ∫ p in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ), F p =
        ∫ rL in Ici (0 : ℝ), ∫ rR in Ici (0 : ℝ), F (rL, rR) := by
      rw [Measure.volume_eq_prod, setIntegral_prod F hF_int.integrableOn]
    rw [hfull, hleft_right, integral_congr_ae hg1_ae, integral_const_mul, hprod_quad]
    ring
  linarith only [hfull_bd.2, hI_quad]

/-- info: 'FormalResearch.ModularBootstrap.Spin.spin_axis_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spin_axis_trace

end FormalResearch.ModularBootstrap.Spin
