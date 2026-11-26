module

public import FormalResearch.SignUncertainty.FctCompDStrip
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Taylor

/-!
# `fct:comp-D` (3): Exact Cauchy phase-curvature identities `(fct:cauchy-curv)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.3 (`fct:comp-D`), part (3)
(lines 218–228 and proof lines 236–249).

For any fixed integer `m ≥ 1` and real even `v ∈ C_c^∞((-R, R))` (`0 < R ≤ 1/2`) with `v(0) = 0`
and `fctMoment k v = 0` for `0 ≤ k ≤ m` (equivalently `g_D^{(2k-1)}(0) = 0` for `1 ≤ k ≤ m + 1`):
* `fct_cauchy_curv_first`:
  `|∫_{t > 0} ϑ_D''(t) / t^{2m+1} dt - (-π / (2 (2m)!) * v^{(2m+2)}(0))| ≤ C_m * ∫ |v|`;
* `fct_cauchy_curv_second`:
  `|∫_{t > 0} (ϑ_D''(t) / t^{2m+1} - 2 ϑ_D'(t) / t^{2m+2}) dt - (-(2m-1)π / (2 (2m+1)!) * v^{(2m+2)}(0))| ≤ C_m * ∫ |v|`.

Proof route: shift `F(z) = (g_D''(z) - T_{2m-2}(z)) / z^{2m+1}` by rectangle Cauchy from `Re z = ε` to
`Re z = 1/2` (no semicircular indent needed); the `T_{2m-2}` integral on `Re z = 1/2` vanishes identically
by FTC, the `g_D''` integral on `Re z = 1/2` is `O_m(‖v‖₁)` by `norm_iteratedDeriv_stripCompG_interior`,
and as `ε ↓ 0` the `c_{2m} / (ε + i t)` term gives `π c_{2m}` via `∫_{-1}^1 ε/(ε² + t²) dt = 2 arctan(1/ε) → π`,
while the remainder and outer tail pass to the limit by dominated convergence.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCompD

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.CtOuter

/-! ### Elementary vertical-line integrals -/

/-- For `k ≥ 2`, `∫ t : ℝ, (1/2 + i t)^{-(k + 1)} = 0` by FTC on `ℝ`. -/
lemma integral_half_add_I_inv_pow_eq_zero {k : ℕ} (hk : 2 ≤ k) :
    ∫ t : ℝ, ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-(k + 1 : ℤ)) = 0 := by
  let P : ℝ → ℂ := fun t =>
    ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-(k : ℤ)) / (-(k : ℂ) * Complex.I)
  have hne : ∀ t : ℝ, (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this
  have hnorm_ge : ∀ t : ℝ, 1 / 2 ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := fun t => by
    have := Complex.abs_re_le_norm ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
    simpa using this
  have hnorm_ge_t : ∀ t : ℝ, |t| ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := fun t => by
    have := Complex.abs_im_le_norm ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
    simpa using this
  have hd : ∀ t : ℝ, HasDerivAt P (((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-(k + 1 : ℤ))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (1 / 2 : ℂ) + Complex.I * (s : ℂ)) Complex.I t := by
      have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I |>.const_add (1 / 2 : ℂ)
      simpa using this
    have h2 := hasDerivAt_zpow (-(k : ℤ)) ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) (Or.inl (hne t))
    have h3 := ((h2.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t h1).div_const (-(k : ℂ) * Complex.I)
    refine h3.congr_deriv ?_
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hexp : -(k : ℤ) - 1 = -(k + 1 : ℤ) := by omega
    rw [hexp]
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, Int.cast_neg, Int.cast_natCast]
    field_simp [hk0, Complex.I_ne_zero]
  have hint : Integrable (fun t : ℝ => ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-(k + 1 : ℤ))) := by
    have hcont : Continuous (fun t : ℝ => ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-(k + 1 : ℤ))) :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).zpow₀ _ fun t => Or.inl (hne t)
    have hdom : Integrable (fun t : ℝ => (4 * (2 : ℝ) ^ (k - 1)) * (1 + t ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul (4 * (2 : ℝ) ^ (k - 1))
    refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_zpow, zpow_neg, show (k + 1 : ℤ) = ((k + 1 : ℕ) : ℤ) by omega, zpow_natCast]
    have hsq : ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 = 1 / 4 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hnorm_pos : 0 < ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := lt_of_lt_of_le (by norm_num) (hnorm_ge t)
    have hpow_ge : (1 / 2 : ℝ) ^ (k - 1) * (1 / 4 + t ^ 2) ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (k + 1) := by
      have hk1 : k + 1 = (k - 1) + 2 := by omega
      rw [hk1, pow_add, hsq]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (hnorm_ge t) (k - 1)) (by positivity)
    have h1t : (1 + t ^ 2) / 4 ≤ 1 / 4 + t ^ 2 := by nlinarith [sq_nonneg t]
    have hlow : (1 + t ^ 2) / (4 * (2 : ℝ) ^ (k - 1)) ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (k + 1) := by
      calc (1 + t ^ 2) / (4 * (2 : ℝ) ^ (k - 1))
          = (1 / 2 : ℝ) ^ (k - 1) * ((1 + t ^ 2) / 4) := by rw [one_div, inv_pow]; ring
        _ ≤ (1 / 2 : ℝ) ^ (k - 1) * (1 / 4 + t ^ 2) := mul_le_mul_of_nonneg_left h1t (by positivity)
        _ ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (k + 1) := hpow_ge
    have hinv := inv_anti₀ (by positivity : 0 < (1 + t ^ 2) / (4 * (2 : ℝ) ^ (k - 1))) hlow
    refine hinv.trans (le_of_eq ?_)
    rw [inv_div, div_eq_mul_inv, mul_comm]
  have hlim_pos : Tendsto P atTop (𝓝 0) := by
    have hnorm : Tendsto (fun t : ℝ => ‖P t‖) atTop (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (show k ≠ 0 by omega))).div_const (k : ℝ))
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      dsimp only [P]
      rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_I, mul_one, norm_zpow,
        zpow_neg, zpow_natCast]
      have h1 : t ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := by
        simpa [abs_of_pos ht] using hnorm_ge_t t
      exact div_le_div_of_nonneg_right (inv_anti₀ (pow_pos ht k) (pow_le_pow_left₀ ht.le h1 k)) (Nat.cast_nonneg k)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hlim_neg : Tendsto P atBot (𝓝 0) := by
    have hnorm : Tendsto (fun t : ℝ => ‖P t‖) atBot (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa using (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (show k ≠ 0 by omega)).comp
          tendsto_neg_atBot_atTop)).div_const (k : ℝ))
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
      dsimp only [P]
      rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_I, mul_one, norm_zpow,
        zpow_neg, zpow_natCast]
      have h1 : -t ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := by
        simpa [abs_of_neg ht] using hnorm_ge_t t
      exact div_le_div_of_nonneg_right (inv_anti₀ (pow_pos (neg_pos.mpr ht) k) (pow_le_pow_left₀ (neg_pos.mpr ht).le h1 k))
        (Nat.cast_nonneg k)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hftc := integral_of_hasDerivAt_of_tendsto hd hint hlim_neg hlim_pos
  simpa using hftc

/-- Exact integral `∫ t in (-1)..1, 1 / (ε + i t) = 2 arctan(1/ε)` for `ε > 0`. -/
lemma integral_inv_eps_add_I {ε : ℝ} (hε : 0 < ε) :
    ∫ t in (-1 : ℝ)..(1 : ℝ), ((ε : ℂ) + Complex.I * (t : ℂ))⁻¹ = ((2 * Real.arctan (1 / ε) : ℝ) : ℂ) := by
  have hsplit : ∀ t : ℝ, ((ε : ℂ) + Complex.I * (t : ℂ))⁻¹ =
      ((ε / (ε ^ 2 + t ^ 2) : ℝ) : ℂ) + Complex.I * ((-t / (ε ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro t
    have hden : (ε ^ 2 + t ^ 2 : ℝ) ≠ 0 := by positivity
    have hne : (ε : ℂ) + Complex.I * (t : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hmul : ((ε : ℂ) + Complex.I * (t : ℂ)) * (((ε / (ε ^ 2 + t ^ 2) : ℝ) : ℂ) +
        Complex.I * ((-t / (ε ^ 2 + t ^ 2) : ℝ) : ℂ)) = 1 := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.one_re, mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add]
        field_simp [hden]; ring
      · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.one_im, mul_zero, zero_mul, one_mul, sub_zero, add_zero, zero_add]
        field_simp [hden]; ring
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  rw [intervalIntegral.integral_congr fun t _ => hsplit t]
  have hc1 : Continuous (fun t : ℝ => ((ε / (ε ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.div (continuous_const.add (continuous_id.pow 2)) fun t => by positivity)
  have hc2 : Continuous (fun t : ℝ => Complex.I * ((-t / (ε ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_neg.div (continuous_const.add (continuous_id.pow 2)) fun t => by positivity))
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  -- Real part: `∫_{-1}^1 ε / (ε² + t²) dt = [arctan(t/ε)]_{-1}^1 = 2 arctan(1/ε)`
  have hre : ∫ t in (-1 : ℝ)..(1 : ℝ), ε / (ε ^ 2 + t ^ 2) = 2 * Real.arctan (1 / ε) := by
    have hd : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => Real.arctan (s / ε)) (ε / (ε ^ 2 + t ^ 2)) t := by
      intro t _
      have h1 := (Real.hasDerivAt_arctan (t / ε)).comp t ((hasDerivAt_id t).div_const ε)
      refine h1.congr_deriv ?_
      have hden : ε ^ 2 + t ^ 2 ≠ 0 := by positivity
      field_simp [hε.ne', hden]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.div (continuous_const.add (continuous_id.pow 2)) fun t =>
        (by positivity : (0 : ℝ) < ε ^ 2 + t ^ 2).ne').intervalIntegrable _ _)]
    rw [show (-1 : ℝ) / ε = -(1 / ε) by ring, Real.arctan_neg]
    ring
  -- Imaginary part: odd integrand on `[-1, 1]` integrates to `0`
  have him : ∫ t in (-1 : ℝ)..(1 : ℝ), -t / (ε ^ 2 + t ^ 2) = 0 := by
    have hneg := intervalIntegral.integral_comp_neg (f := fun t : ℝ => -t / (ε ^ 2 + t ^ 2)) (a := -1) (b := 1)
    simp only [neg_neg, neg_sq] at hneg
    have hodd : ∫ t in (-1 : ℝ)..(1 : ℝ), t / (ε ^ 2 + t ^ 2) = -(∫ t in (-1 : ℝ)..(1 : ℝ), -t / (ε ^ 2 + t ^ 2)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => by ring
    linarith
  rw [hre, him, Complex.ofReal_zero, mul_zero, add_zero]

/-- Vertical rectangle Cauchy shift: if `F` is holomorphic on `strip`, bounded by `C / (1 + |Im z|)^2`
uniformly on `Re z ∈ [ε, 1/2]`, then `∫ t : ℝ, F (ε + i t) = ∫ t : ℝ, F (1/2 + i t)`. -/
lemma vertical_shift_strip {F : ℂ → ℂ} {ε C : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hC : 0 ≤ C)
    (hdiff : DifferentiableOn ℂ F strip)
    (hbd : ∀ z : ℂ, ε ≤ z.re → z.re ≤ 1 / 2 → ‖F z‖ ≤ C / (1 + z.im ^ 2)) :
    ∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ)) = ∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
  have hint_line : ∀ σ : ℝ, ε ≤ σ → σ ≤ 1 / 2 → Integrable (fun t : ℝ => F ((σ : ℂ) + Complex.I * (t : ℂ))) := by
    intro σ hσ1 hσ2
    have hcont : Continuous (fun t : ℝ => F ((σ : ℂ) + Complex.I * (t : ℂ))) :=
      hdiff.continuousOn.comp_continuous (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
        fun t => ⟨by simp; linarith, by simp; linarith⟩
    refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    have h := hbd ((σ : ℂ) + Complex.I * (t : ℂ)) (by simpa using hσ1) (by simpa using hσ2)
    simpa [div_eq_mul_inv] using h
  -- For each `L > 0`, `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` on `[ε, 1/2] × [-L, L]`
  have hrect : ∀ L : ℝ, 0 < L →
      (∫ t in (-L)..L, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) -
      (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ))) =
      Complex.I * ((∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))) -
        (∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (L : ℂ)))) := by
    intro L hL
    have hsub : uIcc ε (1 / 2 : ℝ) ×ℂ uIcc (-L) L ⊆ strip := by
      intro z hz
      rw [uIcc_of_le hε1.le, uIcc_of_le (by linarith)] at hz
      exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have h0 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((ε : ℂ) + Complex.I * ((-L : ℝ) : ℂ)) ((1 / 2 : ℂ) + Complex.I * (L : ℂ))
      (hdiff.mono (by
        intro z hz
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, Complex.div_ofNat_re, Complex.one_re, Complex.add_im,
          Complex.mul_im, zero_add, Complex.div_ofNat_im, Complex.one_im, zero_div,
          one_mul, zero_mul, sub_zero, add_zero] at hz
        exact hsub hz))
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, Complex.div_ofNat_re, Complex.one_re, Complex.add_im,
      Complex.mul_im, zero_add, Complex.div_ofNat_im, Complex.one_im, zero_div,
      one_mul, zero_mul, sub_zero, add_zero, smul_eq_mul] at h0
    have hrew : ∀ (a b c d : ℂ), a - b + Complex.I * c - Complex.I * d = 0 →
        c - d = Complex.I * (a - b) := by
      intro a b c d h
      have h1 : Complex.I * (c - d) = -(a - b) := by linear_combination h
      calc c - d = -Complex.I * (Complex.I * (c - d)) := by rw [← mul_assoc]; simp
        _ = -Complex.I * (-(a - b)) := by rw [h1]
        _ = Complex.I * (a - b) := by ring
    have h0' : (∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))) -
        (∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (L : ℂ))) +
        Complex.I * (∫ t in (-L)..L, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) -
        Complex.I * (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ))) = 0 := by
      have e1 : ∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ)) =
          ∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + ((-L : ℝ) : ℂ) * Complex.I) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      have e2 : ∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (L : ℂ)) =
          ∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + (L : ℂ) * Complex.I) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      have e3 : ∫ t in (-L)..L, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) =
          ∫ t in (-L)..L, F ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      have e4 : ∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ)) =
          ∫ t in (-L)..L, F ((ε : ℂ) + (t : ℂ) * Complex.I) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      rw [e1, e2, e3, e4]
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h0
    exact hrew _ _ _ _ h0'
  have htend_lhs : Tendsto (fun L : ℝ =>
      (∫ t in (-L)..L, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) -
      (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ)))) atTop
      (𝓝 ((∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) -
        (∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ))))) := by
    have h1 := intervalIntegral_tendsto_integral (hint_line (1 / 2) hε1.le le_rfl) tendsto_neg_atTop_atBot tendsto_id
    have h2 := intervalIntegral_tendsto_integral (hint_line ε le_rfl hε1.le) tendsto_neg_atTop_atBot tendsto_id
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, id_eq] using h1.sub h2
  have htend_rhs : Tendsto (fun L : ℝ =>
      (∫ t in (-L)..L, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) -
      (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ)))) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (g := fun L : ℝ => 2 * C / (1 + L ^ 2)) (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [hrect L hL, norm_mul, Complex.norm_I, one_mul]
      have hseg : ∀ (s : ℝ), |s| = L →
          ‖∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (s : ℂ))‖ ≤ C / (1 + L ^ 2) := by
        intro s hs
        calc ‖∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (s : ℂ))‖
            ≤ ∫ x in ε..(1 / 2 : ℝ), ‖F ((x : ℂ) + Complex.I * (s : ℂ))‖ :=
              intervalIntegral.norm_integral_le_integral_norm hε1.le
          _ ≤ ∫ x in ε..(1 / 2 : ℝ), C / (1 + L ^ 2) := by
              refine intervalIntegral.integral_mono_on hε1.le ?_ intervalIntegrable_const fun x hx => ?_
              · have hcont_x : ContinuousOn (fun x : ℝ => ‖F ((x : ℂ) + Complex.I * (s : ℂ))‖) (Icc ε (1 / 2)) :=
                  (hdiff.continuousOn.comp
                    ((Complex.continuous_ofReal.add continuous_const).continuousOn)
                    (fun x hx => ⟨by simp; linarith [hx.1], by simp; linarith [hx.2]⟩)).norm
                exact hcont_x.intervalIntegrable_of_Icc hε1.le
              · have := hbd ((x : ℂ) + Complex.I * (s : ℂ)) (by simpa using hx.1) (by simpa using hx.2)
                simpa [← sq_abs s, hs] using this
          _ = (1 / 2 - ε) * (C / (1 + L ^ 2)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
          _ ≤ 1 * (C / (1 + L ^ 2)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = C / (1 + L ^ 2) := one_mul _
      calc ‖(∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))) -
              ∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (L : ℂ))‖
          ≤ ‖∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))‖ +
            ‖∫ x in ε..(1 / 2 : ℝ), F ((x : ℂ) + Complex.I * (L : ℂ))‖ := norm_sub_le _ _
        _ ≤ C / (1 + L ^ 2) + C / (1 + L ^ 2) := add_le_add (hseg (-L) (by rw [abs_neg, abs_of_pos hL])) (hseg L (abs_of_pos hL))
        _ = 2 * C / (1 + L ^ 2) := by ring
    · have h1 : Tendsto (fun L : ℝ => 1 + L ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num))
      exact (tendsto_const_nhds (x := 2 * C)).div_atTop h1
  exact (sub_eq_zero.mp (tendsto_nhds_unique htend_lhs htend_rhs)).symm

/-! ### Taylor remainder along segments in `closedStrip` and Cauchy curvature identities -/

/-- Exact Taylor remainder for `g₂(z) = -stripCompGExt (v'') z` along `[0, z]` (`z ∈ strip`):
if `g₂^{(k)}(0) = c_k` for `k ≤ n` and `‖g₂^{(n+1)}‖ ≤ M` on `closedStrip`, then
`‖g₂(z) - ∑_{k ≤ n} c_k / k! * z^k‖ ≤ M / (n+1)! * ‖z‖^{n+1}`. -/
private lemma stripCompGExt_taylor_bound {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hv_supp : HasCompactSupport v) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ z ∈ closedStrip, ‖(-Complex.I) ^ (n + 3) * stripCompGExt (iteratedDeriv (n + 3) v) z‖ ≤ M)
    {z : ℂ} (hz : z ∈ strip) :
    let g₂ : ℂ → ℂ := fun w => -stripCompGExt (iteratedDeriv 2 v) w
    let coeff : ℕ → ℂ := fun k => (-Complex.I) ^ (k + 2) *
      (((iteratedDeriv (k + 2) v 0 : ℝ) : ℂ) + Complex.I * ((iteratedDeriv (k + 2) (fctThetaD v) 0 : ℝ) : ℂ))
    ‖g₂ z - ∑ k ∈ Finset.range (n + 1), coeff k / (k.factorial : ℂ) * z ^ k‖ ≤
      M / ((n + 1).factorial : ℝ) * ‖z‖ ^ (n + 1) := by
  intro g₂ coeff
  -- Apply real 1D Taylor's theorem (`taylor_mean_remainder_bound`) to `s ↦ g₂(s • z)` on `[0, 1]`!
  -- Define `γ(s) = (s : ℂ) * z` for `s ∈ [0, 1]`; for `s ∈ (0, 1]`, `γ(s) ∈ strip`.
  let φ : ℝ → ℂ := fun s => g₂ ((s : ℂ) * z)
  let φk : ℕ → ℝ → ℂ := fun k s =>
    z ^ k * ((-Complex.I) ^ (k + 2) * stripCompGExt (iteratedDeriv (k + 2) v) ((s : ℂ) * z))
  have hmem_cl : ∀ s ∈ Icc (0 : ℝ) 1, ((s : ℂ) * z) ∈ closedStrip := fun s hs => by
    simp only [closedStrip, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact ⟨mul_nonneg hs.1 hz.1.le, (mul_le_mul_of_nonneg_left hz.2.le hs.1).trans (by linarith [hs.2])⟩
  have hmem_op : ∀ s ∈ Ioo (0 : ℝ) 1, ((s : ℂ) * z) ∈ strip := fun s hs => by
    simp only [strip, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact ⟨mul_pos hs.1 hz.1, by nlinarith [hs.1, hs.2, hz.1, hz.2]⟩
  have hφ0 : ∀ s ∈ Icc (0 : ℝ) 1, φ s = φk 0 s := fun s _ => by
    dsimp only [φ, φk, g₂]; simp [pow_two]
  have hφk_cont : ∀ k, ContinuousOn (φk k) (Icc (0 : ℝ) 1) := fun k => by
    have hc : ContinuousOn (stripCompGExt (iteratedDeriv (k + 2) v)) closedStrip :=
      continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv (k + 2))
        (hasCompactSupport_iteratedDeriv hv_supp (k + 2))
    exact continuousOn_const.mul (continuousOn_const.mul
      (hc.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn hmem_cl))
  have hφk_deriv : ∀ k, ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (φk k) (φk (k + 1) s) s := by
    intro k s hs
    have hsz : (s : ℂ) * z ∈ strip := hmem_op s hs
    have hdiff_g : DifferentiableAt ℂ (stripCompG (iteratedDeriv (k + 2) v)) ((s : ℂ) * z) :=
      (differentiableOn_stripCompG (contDiff_iteratedDeriv_infty hv (k + 2)).continuous
        (hasCompactSupport_iteratedDeriv hv_supp (k + 2))).differentiableAt (isOpen_strip.mem_nhds hsz)
    have hd_g : HasDerivAt (stripCompG (iteratedDeriv (k + 2) v))
        (-Complex.I * stripCompG (iteratedDeriv (k + 3) v) ((s : ℂ) * z)) ((s : ℂ) * z) := by
      have h1 := hdiff_g.hasDerivAt
      rw [deriv_stripCompG (contDiff_iteratedDeriv_infty hv (k + 2))
        (hasCompactSupport_iteratedDeriv hv_supp (k + 2)) hsz, ← iteratedDeriv_succ] at h1
      exact h1
    have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const z
    have hcomp : HasDerivAt (fun t : ℝ => stripCompG (iteratedDeriv (k + 2) v) ((t : ℂ) * z))
        (-Complex.I * stripCompG (iteratedDeriv (k + 3) v) ((s : ℂ) * z) * z) s := by
      have h := (hd_g.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
      exact h.congr_deriv (by
        simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
        ring)
    have hev : (fun t : ℝ => stripCompGExt (iteratedDeriv (k + 2) v) ((t : ℂ) * z)) =ᶠ[𝓝 s]
        (fun t : ℝ => stripCompG (iteratedDeriv (k + 2) v) ((t : ℂ) * z)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact stripCompGExt_eq_of_mem_strip (hmem_op t ht)
    have hcomp_ext : HasDerivAt (fun t : ℝ => stripCompGExt (iteratedDeriv (k + 2) v) ((t : ℂ) * z))
        (-Complex.I * stripCompGExt (iteratedDeriv (k + 3) v) ((s : ℂ) * z) * z) s := by
      rw [stripCompGExt_eq_of_mem_strip hsz]
      exact hcomp.congr_of_eventuallyEq hev
    have hmul := (hcomp_ext.const_mul ((-Complex.I) ^ (k + 2))).const_mul (z ^ k)
    refine hmul.congr_deriv ?_
    dsimp only [φk]
    rw [pow_succ, show k + 1 + 2 = (k + 2) + 1 by omega, pow_succ]
    ring
  have hφk_zero : ∀ k, φk k 0 = coeff k * z ^ k := fun k => by
    dsimp only [φk, coeff]
    rw [Complex.ofReal_zero, zero_mul, show (0 : ℂ) = ((0 : ℝ) : ℂ) * Complex.I by simp,
      stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hv_supp (k + 2)]
    ring
  -- Prove by induction on `m` that for all `x ∈ [0, 1]`,
  -- `‖φk 0 x - ∑_{k < m} φk k 0 / k! * x^k‖ ≤ M * ‖z‖^m / m! * x^m` (via MVT on `Icc 0 x`!)
  -- Even cleaner: prove for ANY `f : ℕ → ℝ → ℂ` with `f k` continuous on `[0, 1]`, `(f k)' = f (k+1)` on `(0, 1)`,
  -- and `‖f (n+1)‖ ≤ B` on `[0, 1]`, that `‖f 0 x - ∑_{k ≤ n} f k 0 / k! * x^k‖ ≤ B / (n+1)! * x^{n+1}`!
  have hmain : ∀ (m : ℕ) (f : ℕ → ℝ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ k ≤ m, ContinuousOn (f k) (Icc (0 : ℝ) 1)) →
      (∀ k < m, ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (f k) (f (k + 1) s) s) →
      (∀ s ∈ Icc (0 : ℝ) 1, ‖f m s‖ ≤ B) →
      ∀ x ∈ Icc (0 : ℝ) 1,
        ‖f 0 x - ∑ k ∈ Finset.range m, f k 0 / (k.factorial : ℂ) * (x : ℂ) ^ k‖ ≤
          B / (m.factorial : ℝ) * x ^ m := by
    intro m
    induction m with
    | zero =>
      intro f B _ _ _ hB x hx
      simpa using hB x hx
    | succ m ih =>
      intro f B hB hcont hderiv hB_bd x hx
      let R : ℝ → ℂ := fun t => f 0 t - ∑ k ∈ Finset.range (m + 1), f k 0 / (k.factorial : ℂ) * (t : ℂ) ^ k
      let R' : ℝ → ℂ := fun t => f 1 t - ∑ k ∈ Finset.range m, f (k + 1) 0 / (k.factorial : ℂ) * (t : ℂ) ^ k
      have hR0 : R 0 = 0 := by
        dsimp only [R]
        rw [Finset.sum_range_succ']
        simp
      have hR_cont : ContinuousOn R (Icc 0 x) :=
        ((hcont 0 (by omega)).mono (Icc_subset_Icc_right hx.2)).sub (by fun_prop)
      have hR'_cont : ContinuousOn R' (Icc 0 x) :=
        ((hcont 1 (by omega)).mono (Icc_subset_Icc_right hx.2)).sub (by fun_prop)
      have hR_deriv : ∀ t ∈ Ioo 0 x, HasDerivAt R (R' t) t := by
        intro t ht
        have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩
        have h1 := hderiv 0 (by omega) t ht01
        have hsum_d : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range (m + 1), f k 0 / (k.factorial : ℂ) * (s : ℂ) ^ k)
            (∑ k ∈ Finset.range m, f (k + 1) 0 / (k.factorial : ℂ) * (t : ℂ) ^ k) t := by
          rw [show (fun s : ℝ => ∑ k ∈ Finset.range (m + 1), f k 0 / (k.factorial : ℂ) * (s : ℂ) ^ k) =
            fun s : ℝ => f 0 0 + ∑ k ∈ Finset.range m, f (k + 1) 0 / ((k + 1).factorial : ℂ) * (s : ℂ) ^ (k + 1) by
              ext s; rw [Finset.sum_range_succ']; simp [add_comm]]
          have hsum_tail : HasDerivAt
              (fun s : ℝ => ∑ k ∈ Finset.range m, f (k + 1) 0 / ((k + 1).factorial : ℂ) * (s : ℂ) ^ (k + 1))
              (∑ k ∈ Finset.range m, f (k + 1) 0 / ((k + 1).factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k)) t :=
            HasDerivAt.fun_sum fun k _ => by
              have hp : HasDerivAt (fun s : ℝ => (s : ℂ) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) t := by
                simpa using (hasDerivAt_pow (k + 1) (t : ℂ)).comp_ofReal
              exact hp.const_mul (f (k + 1) 0 / ((k + 1).factorial : ℂ))
          refine ((hasDerivAt_const t (f 0 0)).add hsum_tail).congr_deriv ?_
          rw [zero_add]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Nat.factorial_succ, Nat.cast_mul]
          have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
          field_simp [hk1]
        exact h1.sub hsum_d
      have hR'_bd : ∀ t ∈ Icc 0 x, ‖R' t‖ ≤ B / (m.factorial : ℝ) * t ^ m := by
        intro t ht
        have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, le_trans ht.2 hx.2⟩
        exact ih (fun k => f (k + 1)) B hB (fun k hk => hcont (k + 1) (by omega))
          (fun k hk => hderiv (k + 1) (by omega)) hB_bd t ht01
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hR_cont hR_deriv
        (hR'_cont.intervalIntegrable_of_Icc hx.1)
      rw [hR0, sub_zero] at hftc
      have hpow_int : ∫ t in (0 : ℝ)..x, B / (m.factorial : ℝ) * t ^ m = B / ((m + 1).factorial : ℝ) * x ^ (m + 1) := by
        rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero m), sub_zero,
          Nat.factorial_succ, Nat.cast_mul]
        have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
        field_simp [hm1]; push_cast; ring
      calc ‖R x‖ = ‖∫ t in (0 : ℝ)..x, R' t‖ := by rw [hftc]
        _ ≤ ∫ t in (0 : ℝ)..x, ‖R' t‖ := intervalIntegral.norm_integral_le_integral_norm hx.1
        _ ≤ ∫ t in (0 : ℝ)..x, B / (m.factorial : ℝ) * t ^ m :=
            intervalIntegral.integral_mono_on hx.1 (hR'_cont.norm.intervalIntegrable_of_Icc hx.1)
              ((continuous_const.mul (continuous_id.pow m)).intervalIntegrable _ _) hR'_bd
        _ = B / ((m + 1).factorial : ℝ) * x ^ (m + 1) := hpow_int
  have hres := hmain (n + 1) φk (M * ‖z‖ ^ (n + 1)) (by positivity)
    (fun k _ => hφk_cont k) (fun k _ => hφk_deriv k)
    (fun s hs => by
      dsimp only [φk]
      rw [norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (hbd _ (hmem_cl s hs)) (pow_nonneg (norm_nonneg z) _))
    1 ⟨zero_le_one, le_rfl⟩
  rw [← hφ0 1 ⟨zero_le_one, le_rfl⟩] at hres
  dsimp only [φ] at hres
  rw [Complex.ofReal_one, one_mul, one_pow, mul_one] at hres
  have hsum_eq : ∑ k ∈ Finset.range (n + 1), φk k 0 / (k.factorial : ℂ) * (1 : ℂ) ^ k =
      ∑ k ∈ Finset.range (n + 1), coeff k / (k.factorial : ℂ) * z ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hφk_zero k, one_pow, mul_one, mul_div_right_comm]
  rw [hsum_eq] at hres
  refine hres.trans (le_of_eq ?_); ring

set_option maxHeartbeats 800000 in
/-- **Lemma FCT.3 (`fct:comp-D`) part (3), first identity:**
For any fixed `m ≥ 1` and real even `v ∈ C_c^∞((-R, R))` (`0 < R ≤ 1/2`) with `v(0) = 0` and
`fctMoment k v = 0` for `0 ≤ k ≤ m`:
`|∫_{t > 0} ϑ_D''(t) / t^{2m+1} dt - (-π / (2 (2m)!) * v^{(2m+2)}(0))| ≤ C_m * ∫ |v|`. -/
theorem fct_cauchy_curv_first {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ → ℝ} {R : ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → (∀ t, v (-t) = v t) →
      0 < R → R ≤ 1 / 2 → Function.support v ⊆ Ioo (-R) R → v 0 = 0 →
      (∀ k ≤ m, fctMoment k v = 0) →
      IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) (Ioi 0) ∧
      |(∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) -
        (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| ≤
        C * (∫ t : ℝ, |v t|) := by
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := norm_iteratedDeriv_stripCompG_interior 2
  -- On `Re z = 1/2`, `‖g₂(1/2 + it) / (1/2 + it)^{2m+1}‖ ≤ C₂ * ‖v‖₁ * e^{-π|t|} * 2^{2m+1}`,
  -- integrating over `ℝ` to `(2 / π) * C₂ * 2^{2m+1} * ‖v‖₁`, and dividing by `2` gives `(C₂ * 2^{2m+1} / π) * ‖v‖₁`!
  refine ⟨C₂ * (2 : ℝ) ^ (2 * m + 1) / π, by positivity,
    fun {v R} hv hv_even hR0 hR12 hsupp hv0 hmom => ?_⟩
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      (fun t ht => Ioo_subset_Icc_self (hsupp ht))
  have hθ_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v) := contDiff_fctThetaD hv hv_supp
  have hθ_odd : ∀ t, fctThetaD v (-t) = -fctThetaD v t := fctThetaD_odd hv_even
  have hθ2_odd : ∀ t, iteratedDeriv 2 (fctThetaD v) (-t) = -iteratedDeriv 2 (fctThetaD v) t := fun t => by
    have h := iteratedDeriv_odd_fn (fctThetaD v) hθ_odd 2 t
    norm_num at h; exact h
  -- Define `g₂(z) = -stripCompGExt (v'') z`, `T(z)`, `F(z) = (g₂(z) - T(z)) / z^{2m+1}`
  let g₂ : ℂ → ℂ := fun z => -stripCompGExt (iteratedDeriv 2 v) z
  let T : ℂ → ℂ := fun z => ∑ j ∈ Finset.range m,
    ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) * z ^ (2 * j)
  let c2m : ℂ := (-1 : ℂ) ^ (m + 1) * ((iteratedDeriv (2 * m + 2) v 0 : ℝ) : ℂ) / ((2 * m).factorial : ℂ)
  let F : ℂ → ℂ := fun z => (g₂ z - T z) / z ^ (2 * m + 1)
  let Rfn : ℂ → ℂ := fun z => (g₂ z - T z - c2m * z ^ (2 * m)) / z ^ (2 * m + 1)
  -- Coefficients of `g₂` at `0` for `k ≤ 2m`
  have hcoeff_even : ∀ j ≤ m, (-Complex.I) ^ (2 * j + 2) *
      (((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) + Complex.I * ((iteratedDeriv (2 * j + 2) (fctThetaD v) 0 : ℝ) : ℂ)) =
      (-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) := by
    intro j _
    have hθ0 : iteratedDeriv (2 * j + 2) (fctThetaD v) 0 = 0 := by
      have := iteratedDeriv_even_zero_of_odd hθ_odd (j + 1)
      simpa [show 2 * (j + 1) = 2 * j + 2 by omega] using this
    have hi : (-Complex.I) ^ (2 * j + 2) = (-1 : ℂ) ^ (j + 1) := by
      rw [show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul, neg_sq, Complex.I_sq]
    rw [hθ0, Complex.ofReal_zero, mul_zero, add_zero, hi]
  have hcoeff_odd : ∀ j < m, (-Complex.I) ^ (2 * j + 1 + 2) *
      (((iteratedDeriv (2 * j + 1 + 2) v 0 : ℝ) : ℂ) + Complex.I * ((iteratedDeriv (2 * j + 1 + 2) (fctThetaD v) 0 : ℝ) : ℂ)) = 0 := by
    intro j hj
    have hv_odd : iteratedDeriv (2 * j + 1 + 2) v 0 = 0 := by
      have := iteratedDeriv_odd_zero hv_even (j + 1)
      simpa [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega] using this
    have hθ_zero : iteratedDeriv (2 * j + 1 + 2) (fctThetaD v) 0 = 0 := by
      have := iteratedDeriv_odd_fctThetaD_zero hv hv_supp hv_even (j + 1)
      rw [hmom (j + 1) (by omega), mul_zero] at this
      simpa [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega] using this
    rw [hv_odd, hθ_zero, Complex.ofReal_zero, mul_zero, add_zero, mul_zero]
  have hpoly_eq : ∀ z : ℂ,
      ∑ k ∈ Finset.range (2 * m + 1),
        ((-Complex.I) ^ (k + 2) * (((iteratedDeriv (k + 2) v 0 : ℝ) : ℂ) +
          Complex.I * ((iteratedDeriv (k + 2) (fctThetaD v) 0 : ℝ) : ℂ))) / (k.factorial : ℂ) * z ^ k =
      T z + c2m * z ^ (2 * m) := by
    intro z
    rw [Finset.sum_range_succ, hcoeff_even m le_rfl]
    congr 1
    -- Split `range (2 * m)` into even and odd indices
    have hpair : ∀ n : ℕ, ∀ f : ℕ → ℂ, (∀ j < n, f (2 * j + 1) = 0) →
        ∑ k ∈ Finset.range (2 * n), f k = ∑ j ∈ Finset.range n, f (2 * j) := by
      intro n f hf
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
          hf n (Nat.lt_succ_self n), add_zero, Finset.sum_range_succ, ih (fun j hj => hf j (Nat.lt_succ_of_lt hj))]
    rw [hpair m _ (fun j hj => by rw [hcoeff_odd j hj, zero_div, zero_mul])]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hcoeff_even j (le_of_lt (Finset.mem_range.mp hj))]
  -- Uniform global bound `M_k` on `(-i)^k stripCompGExt (v^{(k)})` on `closedStrip` for `k = 2` and `k = 2m + 3`
  have hbound_k : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedStrip,
      ‖(-Complex.I) ^ k * stripCompGExt (iteratedDeriv k v) z‖ ≤ M := by
    intro k
    obtain ⟨B1, hB1⟩ := (hasCompactSupport_iteratedDeriv hv_supp k).exists_bound_of_continuous
      (contDiff_iteratedDeriv_infty hv k).continuous
    -- `fctThetaD (v^{(k)})` is continuous and decays to `0` at `±∞`, hence bounded on `ℝ`!
    have hθk_cont : Continuous (iteratedDeriv k (fctThetaD v)) :=
      (contDiff_iteratedDeriv_infty hθ_cd k).continuous
    obtain ⟨B2_in, hB2_in⟩ := (isCompact_Icc (a := -(R + 2)) (b := R + 2)).exists_bound_of_continuousOn hθk_cont.continuousOn
    have hsupp_k : Function.support (iteratedDeriv k v) ⊆ Ioo (-(R + 1)) (R + 1) := by
      intro t ht; by_contra hnot
      have hev : v =ᶠ[𝓝 t] 0 := by
        have hmem : t ∈ (Icc (-R) R)ᶜ := fun hcc => hnot ⟨by linarith [hcc.1], by linarith [hcc.2]⟩
        filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds hmem] with s hs
        by_contra hne; exact hs (Ioo_subset_Icc_self (hsupp hne))
      exact ht (by rw [hev.iteratedDeriv_eq k, iteratedDeriv_const_zero])
    set I1k : ℝ := ∫ s : ℝ, |iteratedDeriv k v s|
    have hI1k : 0 ≤ I1k := integral_nonneg fun _ => abs_nonneg _
    set M : ℝ := max B1 0 + max (max B2_in 0) (4 * I1k)
    refine ⟨M, by positivity, fun z hz => ?_⟩
    refine norm_iteratedDeriv_stripCompGExt_le k hv hR0 (by positivity) hsupp (fun τ => ?_) hz
    have h1 : |iteratedDeriv k v τ| ≤ max B1 0 := le_trans (by simpa [Real.norm_eq_abs] using hB1 τ) (le_max_left _ _)
    have h2 : |iteratedDeriv k (fctThetaD v) τ| ≤ max (max B2_in 0) (4 * I1k) := by
      by_cases hτ : |τ| ≤ R + 2
      · exact le_trans (le_trans (by simpa [Real.norm_eq_abs] using hB2_in τ (abs_le.mp hτ)) (le_max_left _ _))
          (le_max_left _ _)
      · push Not at hτ
        have hbd := stripCompGExt_norm_le_of_large_im (contDiff_iteratedDeriv_infty hv k).continuous
          (R := R + 1) (by linarith) hsupp_k (ζ := (τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
          (by simpa using (by linarith : R + 1 + 1 ≤ |τ|))
        have hvk0 : iteratedDeriv k v τ = 0 := by
          by_contra hne; have : |τ| < R + 1 := abs_lt.mpr (hsupp_k hne); linarith
        rw [stripCompGExt_left, hvk0, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, ← iteratedDeriv_fctThetaD hv hv_supp k] at hbd
        have hexp : Real.exp (-(π * (|((τ : ℂ) * Complex.I).im| - (R + 1)))) ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
          nlinarith [Real.pi_pos]
        exact (hbd.trans (mul_le_of_le_one_right (by positivity) hexp)).trans (le_max_right _ _)
    linarith
  obtain ⟨M₂, hM₂_nn, hM₂⟩ := hbound_k 2
  obtain ⟨M_top, hM_top_nn, hM_top⟩ := hbound_k (2 * m + 3)
  -- `‖g₂(z)‖ ≤ M₂` on `closedStrip`
  have hg2_bd : ∀ z ∈ closedStrip, ‖g₂ z‖ ≤ M₂ := fun z hz => by
    have h := hM₂ z hz
    have heq : (-Complex.I) ^ 2 * stripCompGExt (iteratedDeriv 2 v) z = g₂ z := by
      dsimp only [g₂]; rw [pow_two]; simp
    rwa [heq] at h
  -- `‖T z‖ ≤ C_T * (1 + ‖z‖^{2m-2})` for all `z : ℂ`
  set C_T : ℝ := ∑ j ∈ Finset.range m,
    ‖(-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)‖
  have hCT_nn : 0 ≤ C_T := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hT_bd : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖T z‖ ≤ C_T * ‖z‖ ^ (2 * m - 2) := by
    intro z hz1
    dsimp only [T]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [norm_mul, norm_pow]
    have hj_le : 2 * j ≤ 2 * m - 2 := by have := Finset.mem_range.mp hj; omega
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 hj_le) (norm_nonneg _)
  -- Step 1: Uniform decay of `F` on `Re z ∈ [ε, 1/2]` and vertical shift `∫ F(ε + it) = ∫ F(1/2 + it)`
  have hF_shift : ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      ∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ)) = ∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    intro ε hε0 hε1
    have hF_diff : DifferentiableOn ℂ F strip := by
      have hg2_diff : DifferentiableOn ℂ g₂ strip :=
        ((differentiableOn_stripCompG (contDiff_iteratedDeriv_infty hv 2).continuous
          (hasCompactSupport_iteratedDeriv hv_supp 2)).congr
            fun z hz => stripCompGExt_eq_of_mem_strip hz).neg
      have hT_diff : DifferentiableOn ℂ T strip :=
        DifferentiableOn.fun_sum fun j _ => differentiableOn_const _ |>.mul (differentiableOn_id.pow (2 * j))
      refine (hg2_diff.sub hT_diff).div (differentiableOn_id.pow (2 * m + 1)) fun z hz => ?_
      exact pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this; linarith [hz.1])
    set C_sh : ℝ := max ((M₂ + C_T * 2 ^ (2 * m - 2)) * 2 / ε ^ (2 * m + 1)) (2 * (M₂ + C_T))
    refine vertical_shift_strip (C := C_sh) hε0 hε1 (by positivity) hF_diff fun z hz1 hz2 => ?_
    have hz_cl : z ∈ closedStrip := ⟨by linarith, by linarith⟩
    have hz_ge_eps : ε ≤ ‖z‖ := le_trans hz1 (by simpa [abs_of_pos (by linarith : 0 < z.re)] using Complex.abs_re_le_norm z)
    have hz_ge_im : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    dsimp only [F]
    rw [norm_div, norm_pow]
    by_cases him1 : |z.im| ≤ 1
    · have h1im : 1 + z.im ^ 2 ≤ 2 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
      have hz_le2 : ‖z‖ ≤ 2 := by
        calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
          _ ≤ 1 / 2 + 1 := add_le_add (by rw [abs_of_pos (by linarith)]; exact hz2) him1
          _ ≤ 2 := by norm_num
      have hT_le : ‖T z‖ ≤ C_T * 2 ^ (2 * m - 2) := by
        dsimp only [T]
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        rw [norm_mul, norm_pow]
        have hj_le : 2 * j ≤ 2 * m - 2 := by have := Finset.mem_range.mp hj; omega
        exact mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (norm_nonneg z) hz_le2 (2 * j)).trans (pow_le_pow_right₀ (by norm_num) hj_le))
          (norm_nonneg _)
      calc ‖g₂ z - T z‖ / ‖z‖ ^ (2 * m + 1)
          ≤ (M₂ + C_T * 2 ^ (2 * m - 2)) / ε ^ (2 * m + 1) :=
            div_le_div₀ (by positivity) ((norm_sub_le _ _).trans (add_le_add (hg2_bd z hz_cl) hT_le))
              (pow_pos hε0 _) (pow_le_pow_left₀ hε0.le hz_ge_eps _)
        _ ≤ ((M₂ + C_T * 2 ^ (2 * m - 2)) * 2 / ε ^ (2 * m + 1)) / (1 + z.im ^ 2) := by
            rw [div_div, div_le_div_iff₀ (pow_pos hε0 _) (by positivity)]
            nlinarith [show 0 ≤ (M₂ + C_T * 2 ^ (2 * m - 2)) * ε ^ (2 * m + 1) by positivity]
        _ ≤ C_sh / (1 + z.im ^ 2) := by
            dsimp only [C_sh]; exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    · push Not at him1
      have hz1' : 1 ≤ ‖z‖ := le_trans him1.le hz_ge_im
      have hnum : ‖g₂ z - T z‖ ≤ (M₂ + C_T) * ‖z‖ ^ (2 * m - 2) := by
        have h1 : M₂ ≤ M₂ * ‖z‖ ^ (2 * m - 2) := le_mul_of_one_le_right hM₂_nn (one_le_pow₀ hz1')
        have h2 := hT_bd z hz1'
        linarith [norm_sub_le (g₂ z) (T z), hg2_bd z hz_cl]
      have hpow_cancel : ‖z‖ ^ (2 * m - 2) / ‖z‖ ^ (2 * m + 1) = (‖z‖ ^ 3)⁻¹ := by
        have h3 : 2 * m + 1 = (2 * m - 2) + 3 := by omega
        rw [h3, pow_add]; field_simp [(lt_of_lt_of_le zero_lt_one hz1').ne']
      have h1im : 1 + z.im ^ 2 ≤ 2 * ‖z‖ ^ 3 := by
        have h2 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz_ge_im 2
        have h3 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith [sq_nonneg ‖z‖]
        nlinarith [one_le_pow₀ hz1' (n := 3)]
      calc ‖g₂ z - T z‖ / ‖z‖ ^ (2 * m + 1)
          ≤ ((M₂ + C_T) * ‖z‖ ^ (2 * m - 2)) / ‖z‖ ^ (2 * m + 1) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = (M₂ + C_T) / ‖z‖ ^ 3 := by rw [mul_div_assoc, hpow_cancel, div_eq_mul_inv]
        _ ≤ (2 * (M₂ + C_T)) / (1 + z.im ^ 2) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [show 0 ≤ M₂ + C_T by positivity]
        _ ≤ C_sh / (1 + z.im ^ 2) := by
            dsimp only [C_sh]; exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  -- Step 2: Right edge `Re z = 1/2`: `∫ T(1/2+it)/(1/2+it)^{2m+1} = 0` and `‖∫ F(1/2+it)‖ ≤ (2 C₂ * 2^{2m+1} / π) ‖v‖₁`
  have hright_bound : ‖∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (2 * C₂ * (2 : ℝ) ^ (2 * m + 1) / π) * (∫ t : ℝ, |v t|) := by
    have hg2_int : Integrable (fun t : ℝ => g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) /
        ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)) := by
      have hcont : Continuous (fun t : ℝ => g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) /
          ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)) := by
        refine ((continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
          (hasCompactSupport_iteratedDeriv hv_supp 2)).neg.comp_continuous
          (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
          (fun t => ⟨by simp, by simp; norm_num⟩)).div
          ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
          (fun t => pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this))
      refine ((integrable_exp_neg_abs' Real.pi_pos).const_mul (C₂ * (2 : ℝ) ^ (2 * m + 1) * (∫ s : ℝ, |v s|))).mono'
        hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      have hmem : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ∈ strip := ⟨by simp, by simp; norm_num⟩
      have hg2_eq : g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = iteratedDeriv 2 (stripCompG v) ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
        rw [iteratedDeriv_stripCompG 2 hv hv_supp hmem]
        dsimp only [g₂]; rw [stripCompGExt_eq_of_mem_strip hmem, pow_two]; simp
      rw [hg2_eq, norm_div, norm_pow]
      have hbd := hC₂ hv hR0 hR12 hsupp ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) (by simp; norm_num) (by simp; norm_num)
      simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, Complex.mul_im,
        Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at hbd
      have hnorm_ge : (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := by
        have := Complex.abs_re_le_norm ((1 / 2 : ℂ) + Complex.I * (t : ℂ)); simpa using this
      calc ‖iteratedDeriv 2 (stripCompG v) ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ /
              ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (2 * m + 1)
          ≤ (C₂ * (∫ s : ℝ, |v s|) * Real.exp (-(π * |t|))) / (1 / 2 : ℝ) ^ (2 * m + 1) :=
            div_le_div₀ (by positivity) hbd (by positivity) (pow_le_pow_left₀ (by norm_num) hnorm_ge _)
        _ = C₂ * (2 : ℝ) ^ (2 * m + 1) * (∫ s : ℝ, |v s|) * Real.exp (-π * |t|) := by
            rw [one_div, inv_pow, div_inv_eq_mul, neg_mul]; ring
    have hT_int_zero : ∫ t : ℝ, T ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) /
        ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1) = 0 := by
      have hterm_eq : ∀ j ∈ Finset.range m, ∀ t : ℝ,
          (((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
            ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * j)) / ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1) =
          ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
            ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ)) := by
        intro j hj t
        have hj_lt : j < m := Finset.mem_range.mp hj
        have hne : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this
        rw [mul_div_assoc]
        congr 1
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hne]
        congr 1; omega
      have hsum_eq : (fun t : ℝ => T ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) /
          ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)) =
          fun t : ℝ => ∑ j ∈ Finset.range m,
            ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
              ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ)) := by
        ext t; dsimp only [T]; rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j hj => hterm_eq j hj t
      have hint_term : ∀ j ∈ Finset.range m, Integrable (fun t : ℝ =>
          ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
            ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ))) := by
        intro j hj
        have hj_lt : j < m := Finset.mem_range.mp hj
        have hne : ∀ t : ℝ, (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := fun t h => by have := congrArg Complex.re h; simp at this
        have hcont : Continuous (fun t : ℝ => ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ))) :=
          (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).zpow₀ _ fun t => Or.inl (hne t)
        refine ((integrable_inv_one_add_sq.const_mul (4 * (2 : ℝ) ^ (2 * m - 2 * j - 1))).mono'
          hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)).const_mul _
        have hexp_n : (2 * (m : ℤ) - 2 * (j : ℤ) + 1) = ((2 * m - 2 * j + 1 : ℕ) : ℤ) := by omega
        rw [norm_zpow, zpow_neg, hexp_n, zpow_natCast]
        have hnorm_ge : (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := by
          have := Complex.abs_re_le_norm ((1 / 2 : ℂ) + Complex.I * (t : ℂ)); simpa using this
        have hsq : ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 = 1 / 4 + t ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
        have hlow : (1 + t ^ 2) / (4 * (2 : ℝ) ^ (2 * m - 2 * j - 1)) ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (2 * m - 2 * j + 1) := by
          have hk1 : 2 * m - 2 * j + 1 = (2 * m - 2 * j - 1) + 2 := by omega
          rw [hk1, pow_add, hsq]
          calc (1 + t ^ 2) / (4 * (2 : ℝ) ^ (2 * m - 2 * j - 1))
              = (1 / 2 : ℝ) ^ (2 * m - 2 * j - 1) * ((1 + t ^ 2) / 4) := by rw [one_div, inv_pow]; ring
            _ ≤ (1 / 2 : ℝ) ^ (2 * m - 2 * j - 1) * (1 / 4 + t ^ 2) :=
                mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg t]) (by positivity)
            _ ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (2 * m - 2 * j - 1) * (1 / 4 + t ^ 2) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnorm_ge _) (by positivity)
        have hinv := inv_anti₀ (by positivity : 0 < (1 + t ^ 2) / (4 * (2 : ℝ) ^ (2 * m - 2 * j - 1))) hlow
        refine hinv.trans (le_of_eq ?_); rw [inv_div, div_eq_mul_inv, mul_comm]
      rw [hsum_eq]
      have hfin_int : ∀ (s : Finset ℕ),
          (∀ j ∈ s, Integrable (fun t : ℝ =>
            ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
              ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ)))) →
          Integrable (fun t : ℝ => ∑ j ∈ s,
            ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
              ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ))) ∧
          (∫ t : ℝ, ∑ j ∈ s,
            ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
              ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ))) =
          ∑ j ∈ s, ∫ t : ℝ,
            ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
              ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (-((2 * m - 2 * j) + 1 : ℤ)) := by
        intro s
        induction s using Finset.cons_induction with
        | empty => intro _; exact ⟨by simp, by simp⟩
        | cons a s ha ih =>
          intro hs
          simp_rw [Finset.sum_cons]
          have hint_a := hs a (Finset.mem_cons_self a s)
          obtain ⟨hint_s, heq_s⟩ := ih fun j hj => hs j (Finset.mem_cons_of_mem hj)
          exact ⟨hint_a.add hint_s, by rw [integral_add hint_a hint_s, heq_s]⟩
      rw [(hfin_int (Finset.range m) hint_term).2]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt : j < m := Finset.mem_range.mp hj
      have hexp_k : -(2 * (m : ℤ) - 2 * (j : ℤ) + 1) = -(((2 * m - 2 * j : ℕ) : ℤ) + 1) := by omega
      rw [integral_const_mul]
      simp_rw [hexp_k]
      rw [integral_half_add_I_inv_pow_eq_zero (k := 2 * m - 2 * j) (by omega), mul_zero]
    have hF_split : (fun t : ℝ => F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) =
        fun t : ℝ => g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1) -
          T ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1) := by
      ext t; dsimp only [F]; rw [sub_div]
    -- Also `T(...) / (...)` is integrable (as a finite sum of integrable terms)
    have hT_int : Integrable (fun t : ℝ => T ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) /
        ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)) := by
      have hcont : Continuous (fun t : ℝ => T ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) /
          ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)) :=
        (show Continuous (fun t : ℝ => T ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) by dsimp only [T]; fun_prop).div
          ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
          (fun t => pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this))
      refine (integrable_inv_one_add_sq.const_mul (max (C_T * (2 : ℝ) ^ (4 * m) * 2) (2 * C_T))).mono'
        hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      set z : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
      have hz_ge : (1 / 2 : ℝ) ≤ ‖z‖ := by have := Complex.abs_re_le_norm z; simpa [z] using this
      have hz_im : |t| ≤ ‖z‖ := by have := Complex.abs_im_le_norm z; simpa [z] using this
      rw [norm_div, norm_pow]
      by_cases ht1 : |t| ≤ 1
      · have hz_le2 : ‖z‖ ≤ 2 := by
          calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
            _ ≤ 1 / 2 + 1 := by simp [z, ht1]
            _ ≤ 2 := by norm_num
        have hT_le : ‖T z‖ ≤ C_T * 2 ^ (2 * m - 2) := by
          dsimp only [T]; refine (norm_sum_le _ _).trans ?_; rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun j hj => ?_; rw [norm_mul, norm_pow]
          have hj_le : 2 * j ≤ 2 * m - 2 := by have := Finset.mem_range.mp hj; omega
          exact mul_le_mul_of_nonneg_left
            ((pow_le_pow_left₀ (norm_nonneg z) hz_le2 (2 * j)).trans (pow_le_pow_right₀ (by norm_num) hj_le)) (norm_nonneg _)
        have hpow_le : (2 : ℝ) ^ (2 * m - 2) / (1 / 2 : ℝ) ^ (2 * m + 1) ≤ (2 : ℝ) ^ (4 * m) := by
          rw [one_div, inv_pow, div_inv_eq_mul, ← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have h1t : 1 + t ^ 2 ≤ 2 := by nlinarith [sq_abs t, abs_nonneg t]
        calc ‖T z‖ / ‖z‖ ^ (2 * m + 1) ≤ (C_T * 2 ^ (2 * m - 2)) / (1 / 2 : ℝ) ^ (2 * m + 1) :=
              div_le_div₀ (by positivity) hT_le (by positivity) (pow_le_pow_left₀ (by norm_num) hz_ge _)
          _ = C_T * (2 ^ (2 * m - 2) / (1 / 2 : ℝ) ^ (2 * m + 1)) := by ring
          _ ≤ C_T * (2 : ℝ) ^ (4 * m) := mul_le_mul_of_nonneg_left hpow_le hCT_nn
          _ ≤ (C_T * (2 : ℝ) ^ (4 * m) * 2) * (1 + t ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; nlinarith [show 0 ≤ C_T * (2 : ℝ) ^ (4 * m) by positivity]
          _ ≤ max (C_T * (2 : ℝ) ^ (4 * m) * 2) (2 * C_T) * (1 + t ^ 2)⁻¹ := by gcongr; exact le_max_left _ _
      · push Not at ht1
        have hz1 : 1 ≤ ‖z‖ := le_trans ht1.le hz_im
        have hT_le := hT_bd z hz1
        have hpow_cancel : ‖z‖ ^ (2 * m - 2) / ‖z‖ ^ (2 * m + 1) = (‖z‖ ^ 3)⁻¹ := by
          have h3 : 2 * m + 1 = (2 * m - 2) + 3 := by omega
          rw [h3, pow_add]; field_simp [(lt_of_lt_of_le zero_lt_one hz1).ne']
        have h1t : 1 + t ^ 2 ≤ 2 * ‖z‖ ^ 3 := by
          have h2 : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz_im 2
          have h3 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith [sq_nonneg ‖z‖]
          nlinarith [one_le_pow₀ hz1 (n := 3)]
        calc ‖T z‖ / ‖z‖ ^ (2 * m + 1) ≤ (C_T * ‖z‖ ^ (2 * m - 2)) / ‖z‖ ^ (2 * m + 1) :=
              div_le_div_of_nonneg_right hT_le (by positivity)
          _ = C_T / ‖z‖ ^ 3 := by rw [mul_div_assoc, hpow_cancel, div_eq_mul_inv]
          _ ≤ (2 * C_T) * (1 + t ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
          _ ≤ max (C_T * (2 : ℝ) ^ (4 * m) * 2) (2 * C_T) * (1 + t ^ 2)⁻¹ := by gcongr; exact le_max_right _ _
    rw [hF_split, integral_sub hg2_int hT_int, hT_int_zero, sub_zero]
    -- Bound `‖∫ g₂(1/2+it)/(1/2+it)^{2m+1} dt‖ ≤ (2 C₂ 2^{2m+1} / π) ‖v‖₁`
    have hexp_int : ∫ t : ℝ, Real.exp (-π * |t|) = 2 / π := by
      have h1 : (∫ t in Iic (0 : ℝ), Real.exp (-π * |t|)) + (∫ t in Ioi (0 : ℝ), Real.exp (-π * |t|)) =
          ∫ t : ℝ, Real.exp (-π * |t|) := by
        rw [← setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [mem_Iic.mp h1, mem_Ioi.mp h2])
          measurableSet_Ioi (integrable_exp_neg_abs' Real.pi_pos).integrableOn
          (integrable_exp_neg_abs' Real.pi_pos).integrableOn, Iic_union_Ioi, setIntegral_univ]
      have hpos : ∫ t in Ioi (0 : ℝ), Real.exp (-π * |t|) = 1 / π := by
        have hcongr : EqOn (fun t : ℝ => Real.exp (-π * |t|)) (fun t => Real.exp (-π * t)) (Ioi 0) :=
          fun t ht => by dsimp only; rw [abs_of_pos ht]
        rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
          integral_exp_mul_Ioi (by linarith [Real.pi_pos]) 0]
        simp [div_neg, one_div]
        ring
      have hneg : ∫ t in Iic (0 : ℝ), Real.exp (-π * |t|) = 1 / π := by
        have hcongr : EqOn (fun t : ℝ => Real.exp (-π * |t|)) (fun t => Real.exp (π * t)) (Iic 0) :=
          fun t ht => by dsimp only; rw [abs_of_nonpos ht, neg_mul_neg]
        rw [setIntegral_congr_fun measurableSet_Iic hcongr,
          integral_exp_mul_Iic Real.pi_pos 0]
        simp [one_div]
      have hsum2 : (1 / π) + (1 / π) = 2 / π := by ring
      linarith
    calc ‖∫ t : ℝ, g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)‖
        ≤ ∫ t : ℝ, ‖g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) / ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m + 1)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, C₂ * (2 : ℝ) ^ (2 * m + 1) * (∫ s : ℝ, |v s|) * Real.exp (-π * |t|) := by
          refine integral_mono hg2_int.norm ((integrable_exp_neg_abs' Real.pi_pos).const_mul _) fun t => ?_
          have hmem : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ∈ strip := ⟨by simp, by simp; norm_num⟩
          have hg2_eq : g₂ ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = iteratedDeriv 2 (stripCompG v) ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
            rw [iteratedDeriv_stripCompG 2 hv hv_supp hmem]
            dsimp only [g₂]; rw [stripCompGExt_eq_of_mem_strip hmem, pow_two]; simp
          rw [hg2_eq, norm_div, norm_pow]
          have hbd := hC₂ hv hR0 hR12 hsupp ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) (by simp; norm_num) (by simp; norm_num)
          simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, Complex.mul_im,
            Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at hbd
          have hnorm_ge : (1 / 2 : ℝ) ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := by
            have := Complex.abs_re_le_norm ((1 / 2 : ℂ) + Complex.I * (t : ℂ)); simpa using this
          calc ‖iteratedDeriv 2 (stripCompG v) ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ /
                  ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ ^ (2 * m + 1)
              ≤ (C₂ * (∫ s : ℝ, |v s|) * Real.exp (-(π * |t|))) / (1 / 2 : ℝ) ^ (2 * m + 1) :=
                div_le_div₀ (by positivity) hbd (by positivity) (pow_le_pow_left₀ (by norm_num) hnorm_ge _)
            _ = C₂ * (2 : ℝ) ^ (2 * m + 1) * (∫ s : ℝ, |v s|) * Real.exp (-π * |t|) := by
                rw [one_div, inv_pow, div_inv_eq_mul, neg_mul]; ring
      _ = (2 * C₂ * (2 : ℝ) ^ (2 * m + 1) / π) * (∫ s : ℝ, |v s|) := by
          rw [integral_const_mul, hexp_int]; ring
  -- Step 3: Limit `ε ↓ 0` in `∫_ℝ F(ε + it) dt = ∫_ℝ F(1/2 + it) dt`
  -- Uniform bound on `Rfn z` for `z ∈ strip`: `‖Rfn z‖ ≤ M_top / (2m+1)!`
  have hRfn_bd : ∀ z ∈ strip, ‖Rfn z‖ ≤ M_top / ((2 * m + 1).factorial : ℝ) := by
    intro z hz
    have hz_ne : z ≠ 0 := fun h => by rw [h] at hz; simp [strip] at hz
    dsimp only [Rfn]
    rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz_ne) _)]
    have htay := stripCompGExt_taylor_bound hv hv_supp (2 * m) hM_top_nn hM_top hz
    dsimp only at htay
    rw [hpoly_eq z] at htay
    simpa [sub_sub] using htay
  -- Also `Rfn (i t)` is bounded by `M_top / (2m+1)!` for `t ≠ 0` (by continuity of `Rfn` from `strip` to `i t`)
  have hRfn_bd_im : ∀ t : ℝ, t ≠ 0 → ‖Rfn (Complex.I * (t : ℂ))‖ ≤ M_top / ((2 * m + 1).factorial : ℝ) := by
    intro t ht
    have hcont : ContinuousWithinAt Rfn closedStrip (Complex.I * (t : ℂ)) := by
      have hg2_c : ContinuousOn g₂ closedStrip :=
        (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
          (hasCompactSupport_iteratedDeriv hv_supp 2)).neg
      have hT_c : ContinuousOn T closedStrip := by dsimp only [T]; fun_prop
      have hc2m_c : ContinuousOn (fun z : ℂ => c2m * z ^ (2 * m)) closedStrip :=
        continuousOn_const.mul (continuousOn_id.pow _)
      have hne : (Complex.I * (t : ℂ)) ^ (2 * m + 1) ≠ 0 :=
        pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht))
      exact (((hg2_c.sub hT_c).sub hc2m_c).continuousWithinAt ⟨by simp, by simp⟩).div
        ((continuous_id.pow _).continuousWithinAt) hne
    have hseq : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 3) : ℝ) : ℂ) + Complex.I * (t : ℂ))
        atTop (𝓝[closedStrip] (Complex.I * (t : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 3) : ℝ)) atTop (𝓝 0) := by
          have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
          refine h1.congr fun n => ?_
          dsimp only [Function.comp_apply]; push_cast; ring_nf
        simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp h0).add tendsto_const_nhds
      · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
        have hlt : (1 / ((n : ℝ) + 3) : ℝ) < 1 := by
          rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
        have hre : (((1 / ((n : ℝ) + 3) : ℝ) : ℂ) + Complex.I * (t : ℂ)).re = 1 / ((n : ℝ) + 3) := by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
            Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
        exact ⟨by rw [hre]; exact hpos.le, by rw [hre]; exact hlt.le⟩
    refine le_of_tendsto (hcont.norm.tendsto.comp hseq) (Filter.Eventually.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 3) := by positivity
    have hlt : (1 / ((n : ℝ) + 3) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hre : (((1 / ((n : ℝ) + 3) : ℝ) : ℂ) + Complex.I * (t : ℂ)).re = 1 / ((n : ℝ) + 3) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
    exact hRfn_bd _ ⟨by rw [hre]; exact hpos, by rw [hre]; exact hlt⟩
  -- Integrability of `ϑ_D''(t) / t^{2m+1}` on `Ioi 0`!
  have hθ2_int : IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) (Ioi 0) := by
    -- Split `Ioi 0 = Ioc 0 1 ∪ Ioi 1`
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    constructor
    · -- On `Ioc 0 1`: `|ϑ_D''(t) / t^{2m+1}| = |Im((-i ϑ_D''(t)) / (i t)^{2m+1})| ≤ ‖Rfn (i t)‖ ≤ M_top / (2m+1)!`!
      have hcont : ContinuousOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) (Ioc 0 1) :=
        (contDiff_iteratedDeriv_infty hθ_cd 2).continuous.continuousOn.div
          (continuousOn_id.pow _) fun t ht => pow_ne_zero _ ht.1.ne'
      refine (integrableOn_const (C := M_top / ((2 * m + 1).factorial : ℝ)) (hs := measure_Ioc_lt_top.ne)).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : t ≠ 0 := ht.1.ne'
      -- Look at `Re(Rfn (i t))`! Since `g₂(i t) = -v''(t) - i ϑ_D''(t)`, `T(i t)` and `c2m (i t)^{2m}` are REAL,
      -- while `(i t)^{2m+1} = (-1)^m i t^{2m+1}` is PURELY IMAGINARY!
      -- So `Re(Rfn (i t)) = Re((-i ϑ_D''(t)) / ((-1)^m i t^{2m+1})) = (-1)^{m+1} ϑ_D''(t) / t^{2m+1}`!
      have hre_Rfn : (Rfn (Complex.I * (t : ℂ))).re = (-1 : ℝ) ^ (m + 1) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) := by
        dsimp only [Rfn, g₂, T, c2m]
        have hg2_im : stripCompGExt (iteratedDeriv 2 v) (Complex.I * (t : ℂ)) =
            ((iteratedDeriv 2 v t : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 2 (fctThetaD v) t : ℝ) : ℂ) := by
          rw [mul_comm Complex.I, stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hv_supp 2]
        have hT_re : ∃ r : ℝ, ∑ j ∈ Finset.range m,
            ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
              (Complex.I * (t : ℂ)) ^ (2 * j) = (r : ℂ) := by
          refine ⟨∑ j ∈ Finset.range m, ((-1 : ℝ) ^ (j + 1) * iteratedDeriv (2 * j + 2) v 0 / ((2 * j).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * t ^ (2 * j)), ?_⟩
          push_cast
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow, pow_mul, Complex.I_sq]
        obtain ⟨rT, hrT⟩ := hT_re
        have hc2m_re : ((-1 : ℂ) ^ (m + 1) * ((iteratedDeriv (2 * m + 2) v 0 : ℝ) : ℂ) / ((2 * m).factorial : ℂ)) *
            (Complex.I * (t : ℂ)) ^ (2 * m) =
            ((((-1 : ℝ) ^ (m + 1) * iteratedDeriv (2 * m + 2) v 0 / ((2 * m).factorial : ℝ)) *
              ((-1 : ℝ) ^ m * t ^ (2 * m)) : ℝ) : ℂ) := by
          rw [mul_pow, pow_mul, Complex.I_sq]; push_cast; ring
        have hden : (Complex.I * (t : ℂ)) ^ (2 * m + 1) = Complex.I * ((((-1 : ℝ) ^ m * t ^ (2 * m + 1) : ℝ) : ℂ)) := by
          rw [mul_pow, pow_succ, pow_mul, Complex.I_sq]; push_cast; ring
        rw [hg2_im, hrT, hc2m_re, hden]
        set A : ℝ := -iteratedDeriv 2 v t - rT -
          ((-1 : ℝ) ^ (m + 1) * iteratedDeriv (2 * m + 2) v 0 / ((2 * m).factorial : ℝ)) * ((-1 : ℝ) ^ m * t ^ (2 * m))
        set B : ℝ := -iteratedDeriv 2 (fctThetaD v) t
        set D : ℝ := (-1 : ℝ) ^ m * t ^ (2 * m + 1)
        have hnum : -(((iteratedDeriv 2 v t : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 2 (fctThetaD v) t : ℝ) : ℂ)) - (rT : ℂ) -
            ((((-1 : ℝ) ^ (m + 1) * iteratedDeriv (2 * m + 2) v 0 / ((2 * m).factorial : ℝ)) *
              ((-1 : ℝ) ^ m * t ^ (2 * m)) : ℝ) : ℂ) = (A : ℂ) + Complex.I * (B : ℂ) := by
          dsimp only [A, B]; push_cast; ring
        rw [hnum]
        have hD : D ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht0)
        have hdiv : ∀ a b d : ℝ, d ≠ 0 → ((a : ℂ) + Complex.I * (b : ℂ)) / (Complex.I * (d : ℂ)) =
            ((b / d : ℝ) : ℂ) + Complex.I * ((-a / d : ℝ) : ℂ) := fun a b d hd => by
          have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
          rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_neg]
          field_simp [Complex.I_ne_zero, hdC]; ring_nf; rw [Complex.I_sq]; ring
        rw [hdiv A B D hD]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
        dsimp only [B, D]
        rw [pow_succ (-1 : ℝ) m, show (-1 : ℝ) ^ m * -1 = -((-1 : ℝ) ^ m) by ring]
        have hsq : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        field_simp [pow_ne_zero _ ht0, pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0)]
        rw [hsq, mul_one]
      have habs : |iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)| = |(Rfn (Complex.I * (t : ℂ))).re| := by
        rw [hre_Rfn, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [Real.norm_eq_abs, habs]
      exact (Complex.abs_re_le_norm _).trans (hRfn_bd_im t ht0)
    · -- On `Ioi 1`: `|ϑ_D''(t)| ≤ M₂`, and `t^{-(2m+1)} ≤ t^{-3}` is integrable!
      have hcont : ContinuousOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) (Ioi 1) :=
        (contDiff_iteratedDeriv_infty hθ_cd 2).continuous.continuousOn.div
          (continuousOn_id.pow _) fun t ht => pow_ne_zero _ (lt_trans zero_lt_one ht).ne'
      have hdom : IntegrableOn (fun t : ℝ => M₂ * t ^ (-3 : ℝ)) (Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul M₂
      refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht1
      have hθ_bd : |iteratedDeriv 2 (fctThetaD v) t| ≤ M₂ := by
        have h1 := hg2_bd ((t : ℂ) * Complex.I) ⟨by simp, by simp⟩
        dsimp only [g₂] at h1
        rw [norm_neg, stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hv_supp 2] at h1
        have h2 := Complex.abs_im_le_norm (((iteratedDeriv 2 v t : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 2 (fctThetaD v) t : ℝ) : ℂ))
        simpa using h2.trans h1
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos ht0]
      have hpow : t ^ (3 : ℕ) ≤ t ^ (2 * m + 1) := pow_le_pow_right₀ ht1.le (by omega)
      calc |iteratedDeriv 2 (fctThetaD v) t| / t ^ (2 * m + 1)
          ≤ M₂ / t ^ (3 : ℕ) := div_le_div₀ hM₂_nn hθ_bd (pow_pos ht0 3) hpow
        _ = M₂ * t ^ (-3 : ℝ) := by
            rw [Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  -- Now take `ε ↓ 0` in `Re(∫_ℝ F(ε + it) dt) = Re(∫_ℝ F(1/2 + it) dt)`!
  -- Actually even cleaner: take `∫_ℝ F(ε + it) dt` as `ε ↓ 0` directly in `ℂ`!
  -- For `0 < ε < 1/2`, split `ℝ = Icc (-1) 1 ∪ (Icc (-1) 1)ᶜ`:
  -- On `Icc (-1) 1`: `F(ε + it) = c2m / (ε + it) + Rfn(ε + it)`.
  -- As `ε ↓ 0`:
  --   * `∫_{-1}^1 c2m / (ε + it) dt = c2m * 2 arctan(1/ε) → c2m * π`
  --   * `∫_{-1}^1 Rfn(ε + it) dt → ∫_{-1}^1 Rfn(it) dt` (dominated by `M_top / (2m+1)!`)
  --   * `∫_{[-1,1]ᶜ} F(ε + it) dt → ∫_{[-1,1]ᶜ} F(it) dt` (dominated by `(M₂ + C_T) / |t|^3`)
  -- Taking `Re` of the limit gives:
  --   `π * Re(c2m) + ∫_{-1}^1 Re(Rfn(it)) dt + ∫_{[-1,1]ᶜ} Re(F(it)) dt = Re(∫_ℝ F(1/2 + it) dt)`!
  -- And `Re(Rfn(it)) = (-1)^{m+1} ϑ_D''(t) / t^{2m+1}` on `[-1, 1] \ {0}`,
  -- while `Re(F(it)) = (-1)^{m+1} ϑ_D''(t) / t^{2m+1}` on `[-1, 1]ᶜ`!
  -- Wait: that means `Re(Rfn(it)) = Re(F(it)) = (-1)^{m+1} ϑ_D''(t) / t^{2m+1}` EVERYWHERE on `ℝ \ {0}`!!
  -- We don't even need oddness cancellation for `v''` and `T` because taking `Re` kills them POINTWISE!!
  -- OMG!! WHAT A SIMPLIFICATION!!
  have hre_F_im : ∀ t : ℝ, t ≠ 0 → (F (Complex.I * (t : ℂ))).re =
      (-1 : ℝ) ^ (m + 1) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) := by
    intro t ht0
    dsimp only [F, g₂, T]
    have hg2_im : stripCompGExt (iteratedDeriv 2 v) (Complex.I * (t : ℂ)) =
        ((iteratedDeriv 2 v t : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 2 (fctThetaD v) t : ℝ) : ℂ) := by
      rw [mul_comm Complex.I, stripCompGExt_left, ← iteratedDeriv_fctThetaD hv hv_supp 2]
    have hT_re : ∃ r : ℝ, ∑ j ∈ Finset.range m,
        ((-1 : ℂ) ^ (j + 1) * ((iteratedDeriv (2 * j + 2) v 0 : ℝ) : ℂ) / ((2 * j).factorial : ℂ)) *
          (Complex.I * (t : ℂ)) ^ (2 * j) = (r : ℂ) := by
      refine ⟨∑ j ∈ Finset.range m, ((-1 : ℝ) ^ (j + 1) * iteratedDeriv (2 * j + 2) v 0 / ((2 * j).factorial : ℝ)) *
        ((-1 : ℝ) ^ j * t ^ (2 * j)), ?_⟩
      push_cast; refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, pow_mul, Complex.I_sq]
    obtain ⟨rT, hrT⟩ := hT_re
    have hden : (Complex.I * (t : ℂ)) ^ (2 * m + 1) = Complex.I * ((((-1 : ℝ) ^ m * t ^ (2 * m + 1) : ℝ) : ℂ)) := by
      rw [mul_pow, pow_succ, pow_mul, Complex.I_sq]; push_cast; ring
    rw [hg2_im, hrT, hden]
    set A : ℝ := -iteratedDeriv 2 v t - rT
    set B : ℝ := -iteratedDeriv 2 (fctThetaD v) t
    set D : ℝ := (-1 : ℝ) ^ m * t ^ (2 * m + 1)
    have hnum : -(((iteratedDeriv 2 v t : ℝ) : ℂ) + Complex.I * ((iteratedDeriv 2 (fctThetaD v) t : ℝ) : ℂ)) - (rT : ℂ) =
        (A : ℂ) + Complex.I * (B : ℂ) := by dsimp only [A, B]; push_cast; ring
    rw [hnum]
    have hD : D ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ht0)
    have hdiv : ∀ a b d : ℝ, d ≠ 0 → ((a : ℂ) + Complex.I * (b : ℂ)) / (Complex.I * (d : ℂ)) =
        ((b / d : ℝ) : ℂ) + Complex.I * ((-a / d : ℝ) : ℂ) := fun a b d hd => by
      have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
      rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_neg]
      field_simp [Complex.I_ne_zero, hdC]; ring_nf; rw [Complex.I_sq]; ring
    rw [hdiv A B D hD]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero]
    dsimp only [B, D]
    rw [pow_succ (-1 : ℝ) m, show (-1 : ℝ) ^ m * -1 = -((-1 : ℝ) ^ m) by ring]
    have hsq : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp [pow_ne_zero _ ht0, pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0)]
    rw [hsq, mul_one]
  have hre_Rfn_im : ∀ t : ℝ, t ≠ 0 → (Rfn (Complex.I * (t : ℂ))).re = (F (Complex.I * (t : ℂ))).re := by
    intro t ht0
    have hdiff : Rfn (Complex.I * (t : ℂ)) = F (Complex.I * (t : ℂ)) - c2m / (Complex.I * (t : ℂ)) := by
      dsimp only [Rfn, F]
      have hne : Complex.I * (t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)
      rw [sub_div, pow_succ]
      congr 1
      field_simp [hne]
    rw [hdiff, Complex.sub_re]
    have hre0 : (c2m / (Complex.I * (t : ℂ))).re = 0 := by
      set r : ℝ := (-1 : ℝ) ^ (m + 1) * iteratedDeriv (2 * m + 2) v 0 / ((2 * m).factorial : ℝ)
      have hc : c2m = (r : ℂ) := by dsimp only [c2m, r]; push_cast; ring
      rw [hc]
      have hdiv : ∀ a : ℝ, (a : ℂ) / (Complex.I * (t : ℂ)) = Complex.I * ((-a / t : ℝ) : ℂ) := fun a => by
        rw [neg_div, Complex.ofReal_neg, Complex.ofReal_div]
        field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr ht0]
        rw [Complex.I_sq]; ring
      rw [hdiv r]; simp
    rw [hre0, sub_zero]
  -- Evaluate `lim_{ε ↓ 0} ∫_ℝ F(ε + it) dt` via DCT on `Icc (-1) 1` and `(Icc (-1) 1)ᶜ`
  have hlim_total : Tendsto (fun ε : ℝ => ∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (c2m * (π : ℂ) + (∫ t in Icc (-1 : ℝ) 1, Rfn (Complex.I * (t : ℂ))) +
        ∫ t in (Icc (-1 : ℝ) 1)ᶜ, F (Complex.I * (t : ℂ)))) := by
    have h1 : Tendsto (fun ε : ℝ => c2m * ((2 * Real.arctan (1 / ε) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (c2m * (π : ℂ))) := by
      have hinv : Tendsto (fun ε : ℝ => (1 / ε : ℝ)) (𝓝[>] (0 : ℝ)) atTop := by
        simpa [one_div] using tendsto_inv_nhdsGT_zero
      have harctan : Tendsto (fun ε : ℝ => Real.arctan (1 / ε)) (𝓝[>] (0 : ℝ)) (𝓝 (π / 2)) :=
        (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hinv
      have h2 : Tendsto (fun ε : ℝ => (2 * Real.arctan (1 / ε) : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 π) := by
        simpa [mul_div_cancel₀ _ (two_ne_zero' ℝ)] using harctan.const_mul 2
      exact (Complex.continuous_ofReal.tendsto π |>.comp h2).const_mul c2m
    have hae_ne : ∀ᵐ s : ℝ ∂volume, s ≠ (0 : ℝ) := by rw [ae_iff]; simp
    have h2 : Tendsto (fun ε : ℝ => ∫ t in Icc (-1 : ℝ) 1, Rfn ((ε : ℂ) + Complex.I * (t : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Icc (-1 : ℝ) 1, Rfn (Complex.I * (t : ℂ)))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => M_top / ((2 * m + 1).factorial : ℝ)) ?_ ?_
        (integrableOn_const (hs := measure_Icc_lt_top.ne)) ?_
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
        have hcont : Continuous (fun t : ℝ => Rfn ((ε : ℂ) + Complex.I * (t : ℂ))) := by
          have hg2_c : Continuous (fun t : ℝ => g₂ ((ε : ℂ) + Complex.I * (t : ℂ))) :=
            (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
              (hasCompactSupport_iteratedDeriv hv_supp 2)).neg.comp_continuous
              (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
              fun t => ⟨by simp; exact hε.1.le, by simp; linarith [hε.2]⟩
          have hT_c : Continuous (fun t : ℝ => T ((ε : ℂ) + Complex.I * (t : ℂ))) := by
            dsimp only [T]; fun_prop
          have hc_c : Continuous (fun t : ℝ => c2m * ((ε : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m)) :=
            continuous_const.mul ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
          exact ((hg2_c.sub hT_c).sub hc_c).div ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
            fun t => pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this; linarith [hε.1])
        exact hcont.aestronglyMeasurable
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
        exact Filter.Eventually.of_forall fun t => hRfn_bd _ ⟨by simp [hε.1], by simp; linarith [hε.2]⟩
      · filter_upwards [ae_restrict_of_ae hae_ne] with t ht
        have hcont : ContinuousWithinAt Rfn closedStrip (Complex.I * (t : ℂ)) := by
          have hg2_c : ContinuousOn g₂ closedStrip :=
            (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
              (hasCompactSupport_iteratedDeriv hv_supp 2)).neg
          have hT_c : ContinuousOn T closedStrip := by dsimp only [T]; fun_prop
          have hc2m_c : ContinuousOn (fun z : ℂ => c2m * z ^ (2 * m)) closedStrip :=
            continuousOn_const.mul (continuousOn_id.pow _)
          have hne : (Complex.I * (t : ℂ)) ^ (2 * m + 1) ≠ 0 :=
            pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht))
          exact (((hg2_c.sub hT_c).sub hc2m_c).continuousWithinAt ⟨by simp, by simp⟩).div
            ((continuous_id.pow _).continuousWithinAt) hne
        have hpath : Tendsto (fun ε : ℝ => (ε : ℂ) + Complex.I * (t : ℂ)) (𝓝[>] (0 : ℝ))
            (𝓝[closedStrip] (Complex.I * (t : ℂ))) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨by
            simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).add tendsto_const_nhds, ?_⟩
          filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
          exact ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
        exact hcont.tendsto.comp hpath
    have h3 : Tendsto (fun ε : ℝ => ∫ t in (Icc (-1 : ℝ) 1)ᶜ, F ((ε : ℂ) + Complex.I * (t : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in (Icc (-1 : ℝ) 1)ᶜ, F (Complex.I * (t : ℂ)))) := by
      have hdom_out : IntegrableOn (fun t : ℝ => (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹) (Icc (-1 : ℝ) 1)ᶜ :=
        (integrable_inv_one_add_sq.const_mul (2 * (M₂ + C_T))).integrableOn
      refine tendsto_integral_filter_of_dominated_convergence (fun t => (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹) ?_ ?_ hdom_out ?_
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
        have hcont : Continuous (fun t : ℝ => F ((ε : ℂ) + Complex.I * (t : ℂ))) := by
          have hg2_c : Continuous (fun t : ℝ => g₂ ((ε : ℂ) + Complex.I * (t : ℂ))) :=
            (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
              (hasCompactSupport_iteratedDeriv hv_supp 2)).neg.comp_continuous
              (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
              fun t => ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
          have hT_c : Continuous (fun t : ℝ => T ((ε : ℂ) + Complex.I * (t : ℂ))) := by
            dsimp only [T]; fun_prop
          exact (hg2_c.sub hT_c).div ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
            fun t => pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this; linarith [hε.1])
        exact hcont.aestronglyMeasurable
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
        have ht1 : 1 < |t| := by
          rw [mem_compl_iff, mem_Icc] at ht; push Not at ht
          rcases le_or_gt (-1 : ℝ) t with h | h
          · rw [abs_of_pos (by linarith [ht h])]; exact ht h
          · rw [abs_of_neg (by linarith)]; linarith
        set z : ℂ := (ε : ℂ) + Complex.I * (t : ℂ)
        have hz_cl : z ∈ closedStrip := ⟨by dsimp [z]; simp; exact hε.1.le, by dsimp [z]; simp; linarith [hε.2]⟩
        have hz_im : |t| ≤ ‖z‖ := by have := Complex.abs_im_le_norm z; simpa [z] using this
        have hz1 : 1 ≤ ‖z‖ := le_trans ht1.le hz_im
        dsimp only [F]
        rw [norm_div, norm_pow]
        have hnum : ‖g₂ z - T z‖ ≤ (M₂ + C_T) * ‖z‖ ^ (2 * m - 2) := by
          have h1 : M₂ ≤ M₂ * ‖z‖ ^ (2 * m - 2) := le_mul_of_one_le_right hM₂_nn (one_le_pow₀ hz1)
          linarith [norm_sub_le (g₂ z) (T z), hg2_bd z hz_cl, hT_bd z hz1]
        have hpow_cancel : ‖z‖ ^ (2 * m - 2) / ‖z‖ ^ (2 * m + 1) = (‖z‖ ^ 3)⁻¹ := by
          have h3' : 2 * m + 1 = (2 * m - 2) + 3 := by omega
          rw [h3', pow_add]; field_simp [(lt_of_lt_of_le zero_lt_one hz1).ne']
        have h1t : 1 + t ^ 2 ≤ 2 * ‖z‖ ^ 3 := by
          have h2 : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz_im 2
          have h3' : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith [sq_nonneg ‖z‖]
          nlinarith [one_le_pow₀ hz1 (n := 3)]
        calc ‖g₂ z - T z‖ / ‖z‖ ^ (2 * m + 1) ≤ ((M₂ + C_T) * ‖z‖ ^ (2 * m - 2)) / ‖z‖ ^ (2 * m + 1) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ = (M₂ + C_T) / ‖z‖ ^ 3 := by rw [mul_div_assoc, hpow_cancel, div_eq_mul_inv]
          _ ≤ (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹ := by
              rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [show 0 ≤ M₂ + C_T by positivity]
      · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
        have ht0 : t ≠ 0 := fun h => by subst h; exact ht (by norm_num)
        have hcont : ContinuousWithinAt F closedStrip (Complex.I * (t : ℂ)) := by
          have hg2_c : ContinuousOn g₂ closedStrip :=
            (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
              (hasCompactSupport_iteratedDeriv hv_supp 2)).neg
          have hT_c : ContinuousOn T closedStrip := by dsimp only [T]; fun_prop
          have hne : (Complex.I * (t : ℂ)) ^ (2 * m + 1) ≠ 0 :=
            pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0))
          exact ((hg2_c.sub hT_c).continuousWithinAt ⟨by simp, by simp⟩).div ((continuous_id.pow _).continuousWithinAt) hne
        have hpath : Tendsto (fun ε : ℝ => (ε : ℂ) + Complex.I * (t : ℂ)) (𝓝[>] (0 : ℝ))
            (𝓝[closedStrip] (Complex.I * (t : ℂ))) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨by
            simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).add tendsto_const_nhds, ?_⟩
          filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
          exact ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
        exact hcont.tendsto.comp hpath
    refine ((h1.add h2).add h3).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    have hF_int : Integrable (fun t : ℝ => F ((ε : ℂ) + Complex.I * (t : ℂ))) := by
      have hcont : Continuous (fun t : ℝ => F ((ε : ℂ) + Complex.I * (t : ℂ))) := by
        have hg2_c : Continuous (fun t : ℝ => g₂ ((ε : ℂ) + Complex.I * (t : ℂ))) :=
          (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
            (hasCompactSupport_iteratedDeriv hv_supp 2)).neg.comp_continuous
            (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
            fun t => ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
        have hT_c : Continuous (fun t : ℝ => T ((ε : ℂ) + Complex.I * (t : ℂ))) := by
          dsimp only [T]; fun_prop
        exact (hg2_c.sub hT_c).div ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
          fun t => pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this; linarith [hε.1])
      -- Use `hF_shift`'s domination or just split on `Icc (-1) 1` + `compl`
      rw [← integrableOn_univ, ← union_compl_self (Icc (-1 : ℝ) 1), integrableOn_union]
      refine ⟨hcont.continuousOn.integrableOn_Icc, ?_⟩
      have hdom_out : IntegrableOn (fun t : ℝ => (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹) (Icc (-1 : ℝ) 1)ᶜ :=
        (integrable_inv_one_add_sq.const_mul (2 * (M₂ + C_T))).integrableOn
      refine hdom_out.mono' hcont.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      have ht1 : 1 < |t| := by
        rw [mem_compl_iff, mem_Icc] at ht; push Not at ht
        rcases le_or_gt (-1 : ℝ) t with h | h
        · rw [abs_of_pos (by linarith [ht h])]; exact ht h
        · rw [abs_of_neg (by linarith)]; linarith
      set z : ℂ := (ε : ℂ) + Complex.I * (t : ℂ)
      have hz_cl : z ∈ closedStrip := ⟨by dsimp [z]; simp; exact hε.1.le, by dsimp [z]; simp; linarith [hε.2]⟩
      have hz_im : |t| ≤ ‖z‖ := by have := Complex.abs_im_le_norm z; simpa [z] using this
      have hz1 : 1 ≤ ‖z‖ := le_trans ht1.le hz_im
      dsimp only [F]; rw [norm_div, norm_pow]
      have hnum : ‖g₂ z - T z‖ ≤ (M₂ + C_T) * ‖z‖ ^ (2 * m - 2) := by
        have h1' : M₂ ≤ M₂ * ‖z‖ ^ (2 * m - 2) := le_mul_of_one_le_right hM₂_nn (one_le_pow₀ hz1)
        linarith [norm_sub_le (g₂ z) (T z), hg2_bd z hz_cl, hT_bd z hz1]
      have hpow_cancel : ‖z‖ ^ (2 * m - 2) / ‖z‖ ^ (2 * m + 1) = (‖z‖ ^ 3)⁻¹ := by
        have h3' : 2 * m + 1 = (2 * m - 2) + 3 := by omega
        rw [h3', pow_add]; field_simp [(lt_of_lt_of_le zero_lt_one hz1).ne']
      have h1t : 1 + t ^ 2 ≤ 2 * ‖z‖ ^ 3 := by
        have h2' : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz_im 2
        have h3' : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith [sq_nonneg ‖z‖]
        nlinarith [one_le_pow₀ hz1 (n := 3)]
      calc ‖g₂ z - T z‖ / ‖z‖ ^ (2 * m + 1) ≤ ((M₂ + C_T) * ‖z‖ ^ (2 * m - 2)) / ‖z‖ ^ (2 * m + 1) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = (M₂ + C_T) / ‖z‖ ^ 3 := by rw [mul_div_assoc, hpow_cancel, div_eq_mul_inv]
        _ ≤ (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [show 0 ≤ M₂ + C_T by positivity]
    rw [← integral_add_compl measurableSet_Icc hF_int]
    congr 1
    have hsplit_in : ∀ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ)) =
        c2m * ((ε : ℂ) + Complex.I * (t : ℂ))⁻¹ + Rfn ((ε : ℂ) + Complex.I * (t : ℂ)) := fun t => by
      dsimp only [F, Rfn]
      have hne : (ε : ℂ) + Complex.I * (t : ℂ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith [hε.1]
      rw [pow_succ]; field_simp [hne]; ring
    have hc1 : IntegrableOn (fun t : ℝ => c2m * ((ε : ℂ) + Complex.I * (t : ℂ))⁻¹) (Icc (-1 : ℝ) 1) :=
      (continuous_const.mul ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).inv₀
        fun t h => by have := congrArg Complex.re h; simp at this; linarith [hε.1])).continuousOn.integrableOn_Icc
    have hc2 : IntegrableOn (fun t : ℝ => Rfn ((ε : ℂ) + Complex.I * (t : ℂ))) (Icc (-1 : ℝ) 1) := by
      refine (integrableOn_const (C := M_top / ((2 * m + 1).factorial : ℝ)) (hs := measure_Icc_lt_top.ne)).mono' ?_
        (Filter.Eventually.of_forall fun t => hRfn_bd _ ⟨by simp [hε.1], by simp; linarith [hε.2]⟩)
      have hcont : Continuous (fun t : ℝ => Rfn ((ε : ℂ) + Complex.I * (t : ℂ))) := by
        have hg2_c : Continuous (fun t : ℝ => g₂ ((ε : ℂ) + Complex.I * (t : ℂ))) :=
          (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
            (hasCompactSupport_iteratedDeriv hv_supp 2)).neg.comp_continuous
            (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
            fun t => ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
        have hT_c : Continuous (fun t : ℝ => T ((ε : ℂ) + Complex.I * (t : ℂ))) := by
          dsimp only [T]; fun_prop
        have hc_c : Continuous (fun t : ℝ => c2m * ((ε : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m)) :=
          continuous_const.mul ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
        exact ((hg2_c.sub hT_c).sub hc_c).div ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).pow _)
          fun t => pow_ne_zero _ (fun h => by have := congrArg Complex.re h; simp at this; linarith [hε.1])
      exact hcont.aestronglyMeasurable
    rw [setIntegral_congr_fun measurableSet_Icc fun t _ => hsplit_in t, integral_add hc1 hc2]
    congr 1
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_inv_eps_add_I hε.1]
  -- By uniqueness of limits, `c2m * π + ∫_{[-1,1]} Rfn(it) + ∫_{[-1,1]ᶜ} F(it) = ∫_ℝ F(1/2 + it)`!
  have heq_lim : c2m * (π : ℂ) + (∫ t in Icc (-1 : ℝ) 1, Rfn (Complex.I * (t : ℂ))) +
      ∫ t in (Icc (-1 : ℝ) 1)ᶜ, F (Complex.I * (t : ℂ)) =
      ∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    have hconst : Tendsto (fun ε : ℝ => ∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ)))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      exact (hF_shift hε.1 hε.2).symm
    exact tendsto_nhds_unique hlim_total hconst
  -- Take real part of `heq_lim`!
  have hre_lim := congrArg Complex.re heq_lim
  have hae_ne : ∀ᵐ s : ℝ ∂volume, s ≠ (0 : ℝ) := by rw [ae_iff]; simp
  -- Compute real parts of the two integrals
  have hRfn_int_in : IntegrableOn (fun t : ℝ => Rfn (Complex.I * (t : ℂ))) (Icc (-1 : ℝ) 1) := by
    refine (integrableOn_const (C := M_top / ((2 * m + 1).factorial : ℝ)) (hs := measure_Icc_lt_top.ne)).mono' ?_ ?_
    · have hcont_on : ContinuousOn (fun t : ℝ => Rfn (Complex.I * (t : ℂ))) ({0}ᶜ) := by
        have hg2_c : ContinuousOn g₂ closedStrip :=
          (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
            (hasCompactSupport_iteratedDeriv hv_supp 2)).neg
        have hT_c : ContinuousOn T closedStrip := by dsimp only [T]; fun_prop
        have hc2m_c : ContinuousOn (fun z : ℂ => c2m * z ^ (2 * m)) closedStrip :=
          continuousOn_const.mul (continuousOn_id.pow _)
        exact (((hg2_c.sub hT_c).sub hc2m_c).comp (continuous_const.mul Complex.continuous_ofReal).continuousOn
          fun t _ => ⟨by simp, by simp⟩).div ((continuous_const.mul Complex.continuous_ofReal).pow _).continuousOn
          fun t ht => pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht))
      have hmeas : AEStronglyMeasurable (fun t : ℝ => Rfn (Complex.I * (t : ℂ))) (volume.restrict ({0}ᶜ)) :=
        hcont_on.aestronglyMeasurable isOpen_compl_singleton.measurableSet
      rw [Measure.restrict_eq_self_of_ae_mem hae_ne] at hmeas
      exact hmeas.restrict
    · filter_upwards [ae_restrict_of_ae hae_ne] with t ht using hRfn_bd_im t ht
  have hF_int_out : IntegrableOn (fun t : ℝ => F (Complex.I * (t : ℂ))) (Icc (-1 : ℝ) 1)ᶜ := by
    have hdom_out : IntegrableOn (fun t : ℝ => (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹) (Icc (-1 : ℝ) 1)ᶜ :=
      (integrable_inv_one_add_sq.const_mul (2 * (M₂ + C_T))).integrableOn
    refine hdom_out.mono' ?_ ?_
    · have hcont_on : ContinuousOn (fun t : ℝ => F (Complex.I * (t : ℂ))) (Icc (-1 : ℝ) 1)ᶜ := by
        have hg2_c : ContinuousOn g₂ closedStrip :=
          (continuousOn_stripCompGExt (contDiff_iteratedDeriv_infty hv 2)
            (hasCompactSupport_iteratedDeriv hv_supp 2)).neg
        have hT_c : ContinuousOn T closedStrip := by dsimp only [T]; fun_prop
        exact ((hg2_c.sub hT_c).comp (continuous_const.mul Complex.continuous_ofReal).continuousOn
          fun t _ => ⟨by simp, by simp⟩).div ((continuous_const.mul Complex.continuous_ofReal).pow _).continuousOn
          fun t ht => pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr
            (fun h => by subst h; exact ht (by norm_num))))
      exact hcont_on.aestronglyMeasurable measurableSet_Icc.compl
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      have ht1 : 1 < |t| := by
        rw [mem_compl_iff, mem_Icc] at ht; push Not at ht
        rcases le_or_gt (-1 : ℝ) t with h | h
        · rw [abs_of_pos (by linarith [ht h])]; exact ht h
        · rw [abs_of_neg (by linarith)]; linarith
      set z : ℂ := Complex.I * (t : ℂ)
      have hz_cl : z ∈ closedStrip := ⟨by dsimp [z]; simp, by dsimp [z]; simp⟩
      have hz_im : |t| ≤ ‖z‖ := by
        have h := Complex.abs_im_le_norm z
        simp only [z, Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
          Complex.ofReal_re, one_mul, zero_add] at h
        exact h
      have hz1 : 1 ≤ ‖z‖ := le_trans ht1.le hz_im
      dsimp only [F]; rw [norm_div, norm_pow]
      have hnum : ‖g₂ z - T z‖ ≤ (M₂ + C_T) * ‖z‖ ^ (2 * m - 2) := by
        have h1' : M₂ ≤ M₂ * ‖z‖ ^ (2 * m - 2) := le_mul_of_one_le_right hM₂_nn (one_le_pow₀ hz1)
        linarith [norm_sub_le (g₂ z) (T z), hg2_bd z hz_cl, hT_bd z hz1]
      have hpow_cancel : ‖z‖ ^ (2 * m - 2) / ‖z‖ ^ (2 * m + 1) = (‖z‖ ^ 3)⁻¹ := by
        have h3' : 2 * m + 1 = (2 * m - 2) + 3 := by omega
        rw [h3', pow_add]; field_simp [(lt_of_lt_of_le zero_lt_one hz1).ne']
      have h1t : 1 + t ^ 2 ≤ 2 * ‖z‖ ^ 3 := by
        have h2' : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz_im 2
        have h3' : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by nlinarith [sq_nonneg ‖z‖]
        nlinarith [one_le_pow₀ hz1 (n := 3)]
      calc ‖g₂ z - T z‖ / ‖z‖ ^ (2 * m + 1) ≤ ((M₂ + C_T) * ‖z‖ ^ (2 * m - 2)) / ‖z‖ ^ (2 * m + 1) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = (M₂ + C_T) / ‖z‖ ^ 3 := by rw [mul_div_assoc, hpow_cancel, div_eq_mul_inv]
        _ ≤ (2 * (M₂ + C_T)) * (1 + t ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [show 0 ≤ M₂ + C_T by positivity]
  have hθ2_int_all : Integrable (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    refine ⟨?_, hθ2_int⟩
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    have hcomp : IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) (-t) / (-t) ^ (2 * m + 1)) (Ioi 0) := by
      refine hθ2_int.congr_fun (fun t _ => ?_) measurableSet_Ioi
      rw [hθ2_odd t, Odd.neg_pow ⟨m, rfl⟩, neg_div_neg_eq]
    have hind := (hcomp.integrable_indicator measurableSet_Ioi).comp_neg
    have heq : (fun t : ℝ => (Iio (0 : ℝ)).indicator (fun s => iteratedDeriv 2 (fctThetaD v) s / s ^ (2 * m + 1)) t) =
        fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun s => iteratedDeriv 2 (fctThetaD v) (-s) / (-s) ^ (2 * m + 1)) (-t) := by
      ext t; by_cases h : t < 0
      · have h1 : t ∈ Iio (0 : ℝ) := h
        have h2 : -t ∈ Ioi (0 : ℝ) := neg_pos.mpr h
        simp [h1, h2]
      · have h1 : t ∉ Iio (0 : ℝ) := h
        have h2 : -t ∉ Ioi (0 : ℝ) := by simp [mem_Ioi]; linarith [not_lt.mp h]
        simp [h1, h2]
    exact (integrable_indicator_iff measurableSet_Iio).mp (by convert hind using 1)
  have hre_sum : (∫ t in Icc (-1 : ℝ) 1, Rfn (Complex.I * (t : ℂ))).re +
      (∫ t in (Icc (-1 : ℝ) 1)ᶜ, F (Complex.I * (t : ℂ))).re =
      2 * (-1 : ℝ) ^ (m + 1) * ∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) := by
    have hre1 := Complex.reCLM.integral_comp_comm hRfn_int_in
    have hre2 := Complex.reCLM.integral_comp_comm hF_int_out
    simp only [Complex.reCLM_apply] at hre1 hre2
    rw [← hre1, ← hre2]
    have h1 : ∫ t in Icc (-1 : ℝ) 1, (Rfn (Complex.I * (t : ℂ))).re =
        ∫ t in Icc (-1 : ℝ) 1, (-1 : ℝ) ^ (m + 1) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) := by
      refine setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [hae_ne] with t ht _
      rw [hre_Rfn_im t ht, hre_F_im t ht]
    have h2 : ∫ t in (Icc (-1 : ℝ) 1)ᶜ, (F (Complex.I * (t : ℂ))).re =
        ∫ t in (Icc (-1 : ℝ) 1)ᶜ, (-1 : ℝ) ^ (m + 1) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) := by
      refine setIntegral_congr_ae measurableSet_Icc.compl ?_
      filter_upwards [hae_ne] with t ht _
      exact hre_F_im t ht
    rw [h1, h2, integral_add_compl measurableSet_Icc (hθ2_int_all.const_mul _), integral_const_mul]
    -- Even integrand: `∫_ℝ = 2 * ∫_{Ioi 0}`
    have heven_int : ∫ t : ℝ, iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) =
        2 * ∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) := by
      have hsp : (∫ t in Iic (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) +
          (∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) =
          ∫ t : ℝ, iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) := by
        rw [← setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [mem_Iic.mp h1, mem_Ioi.mp h2])
          measurableSet_Ioi hθ2_int_all.integrableOn hθ2_int_all.integrableOn, Iic_union_Ioi, setIntegral_univ]
      have hneg_eq : ∫ t in Iio (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) =
          ∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) := by
        rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi,
          ← MeasureTheory.integral_neg_eq_self (fun t => (Ioi (0 : ℝ)).indicator (fun s => iteratedDeriv 2 (fctThetaD v) s / s ^ (2 * m + 1)) t)]
        congr 1; ext t; by_cases h : t < 0
        · have h1 : t ∈ Iio (0 : ℝ) := h
          have h2 : -t ∈ Ioi (0 : ℝ) := neg_pos.mpr h
          simp [h1, h2, hθ2_odd t, Odd.neg_pow ⟨m, rfl⟩, neg_div_neg_eq]
        · have h1 : t ∉ Iio (0 : ℝ) := h
          have h2 : -t ∉ Ioi (0 : ℝ) := by simp [mem_Ioi]; linarith [not_lt.mp h]
          simp [h1, h2]
      rw [← hsp, integral_Iic_eq_integral_Iio, hneg_eq]; ring
    rw [heven_int]; ring
  have hc2m_pi_re : (c2m * (π : ℂ)).re =
      (-1 : ℝ) ^ (m + 1) * (π * iteratedDeriv (2 * m + 2) v 0 / ((2 * m).factorial : ℝ)) := by
    dsimp only [c2m]
    set r : ℝ := (-1 : ℝ) ^ (m + 1) * iteratedDeriv (2 * m + 2) v 0 / ((2 * m).factorial : ℝ)
    have : ((-1 : ℂ) ^ (m + 1) * ((iteratedDeriv (2 * m + 2) v 0 : ℝ) : ℂ) / ((2 * m).factorial : ℂ)) * (π : ℂ) =
        ((r * π : ℝ) : ℂ) := by dsimp only [r]; push_cast; ring
    rw [this, Complex.ofReal_re]; dsimp only [r]; ring
  simp only [Complex.add_re] at hre_lim
  rw [add_assoc, hre_sum, hc2m_pi_re] at hre_lim
  refine ⟨hθ2_int, ?_⟩
  have hfactor : (-1 : ℝ) ^ (m + 1) * (2 * ((∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) -
      (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0))) =
      (∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re := by
    rw [← hre_lim]; ring
  have habs_eq : 2 * |(∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) -
      (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| =
      |(∫ t : ℝ, F ((1 / 2 : ℂ) + Complex.I * (t : ℂ))).re| := by
    rw [← hfactor, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have hbd_re := (Complex.abs_re_le_norm _).trans hright_bound
  rw [← habs_eq] at hbd_re
  have h2_eq : 2 * C₂ * (2 : ℝ) ^ (2 * m + 1) / π * (∫ t : ℝ, |v t|) =
      2 * (C₂ * (2 : ℝ) ^ (2 * m + 1) / π * (∫ t : ℝ, |v t|)) := by ring
  linarith

/-- **Lemma FCT.3 (`fct:comp-D`) part (3), second identity:**
Under the same hypotheses as `fct_cauchy_curv_first`,
`|∫_{t > 0} (ϑ_D''(t) / t^{2m+1} - 2 ϑ_D'(t) / t^{2m+2}) dt - (-(2m-1)π / (2 (2m+1)!) * v^{(2m+2)}(0))| ≤ C_m * ∫ |v|`. -/
theorem fct_cauchy_curv_second {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ → ℝ} {R : ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → (∀ t, v (-t) = v t) →
      0 < R → R ≤ 1 / 2 → Function.support v ⊆ Ioo (-R) R → v 0 = 0 →
      (∀ k ≤ m, fctMoment k v = 0) →
      IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) -
        2 * deriv (fctThetaD v) t / t ^ (2 * m + 2)) (Ioi 0) ∧
      |(∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) -
        2 * deriv (fctThetaD v) t / t ^ (2 * m + 2))) -
        (-(((2 * m - 1 : ℝ) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| ≤
        C * (∫ t : ℝ, |v t|) := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := fct_cauchy_curv_first hm
  refine ⟨C₁, hC₁_nn, fun {v R} hv hv_even hR0 hR12 hsupp hv0 hmom => ?_⟩
  obtain ⟨hθ2_int, hbd1⟩ := hC₁ hv hv_even hR0 hR12 hsupp hv0 hmom
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
      (fun t ht => Ioo_subset_Icc_self (hsupp ht))
  have hθ_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v) := contDiff_fctThetaD hv hv_supp
  have hθ_odd : ∀ t, fctThetaD v (-t) = -fctThetaD v t := fctThetaD_odd hv_even
  -- First show `ϑ_D'(t) = O(t^{2m+2})` near `0` (all derivatives of `ϑ_D` of order `≤ 2m+2` vanish at `0` except possibly `2m+2`?
  -- Wait: `ϑ_D` is odd, so `ϑ_D^{(2m+2)}(0) = 0` TOO! Thus `ϑ_D^{(j)}(0) = 0` for ALL `j ≤ 2m + 2`, so `ϑ_D'(t) = O(t^{2m+2})`!)
  have hθ1_zero_jet : ∀ j ≤ 2 * m + 1, iteratedDeriv j (deriv (fctThetaD v)) 0 = 0 := by
    intro j hj
    rw [show deriv (fctThetaD v) = iteratedDeriv 1 (fctThetaD v) from (iteratedDeriv_one).symm,
      iteratedDeriv_iteratedDeriv_eq]
    rcases Nat.even_or_odd (j + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show j + 1 = 2 * k by omega]; exact iteratedDeriv_even_zero_of_odd hθ_odd k
    · rw [hk, iteratedDeriv_odd_fctThetaD_zero hv hv_supp hv_even k, hmom k (by omega), mul_zero]
  -- By Taylor's theorem on `[0, 1]`, `|ϑ_D'(t)| ≤ B * t^{2m+2}` for `t ∈ [0, 1]`!
  obtain ⟨B_tay, hB_tay⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_iteratedDeriv_infty hθ_cd (2 * m + 3)).continuous.continuousOn
  have hB_nn : 0 ≤ max B_tay 0 := le_max_right _ _
  have hθ1_cd : ContDiff ℝ (⊤ : ℕ∞) (deriv (fctThetaD v)) := by
    rw [show deriv (fctThetaD v) = iteratedDeriv 1 (fctThetaD v) from (iteratedDeriv_one).symm]
    exact contDiff_iteratedDeriv_infty hθ_cd 1
  have hθ1_small : ∀ t ∈ Icc (0 : ℝ) 1, |deriv (fctThetaD v) t| ≤ max B_tay 0 * t ^ (2 * m + 2) := by
    intro t ht
    have h1 := taylor_mean_remainder_bound (f := deriv (fctThetaD v)) (n := 2 * m + 1) (a := 0) (b := 1)
      (C := max B_tay 0) (x := t)
      (hθ1_cd.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top))
      ht
      (fun x hx => by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
          (hθ1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) hx,
          show deriv (fctThetaD v) = iteratedDeriv 1 (fctThetaD v) from (iteratedDeriv_one).symm,
          iteratedDeriv_iteratedDeriv_eq, show 2 * m + 1 + 1 + 1 = 2 * m + 3 by omega]
        exact (hB_tay x hx).trans (le_max_left _ _))
    have hpoly0 : taylorWithinEval (deriv (fctThetaD v)) (2 * m + 1) (Icc 0 1) 0 t = 0 := by
      rw [taylor_within_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk_le : k ≤ 2 * m + 1 := Finset.mem_range_succ_iff.mp hk
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
        (hθ1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (left_mem_Icc.mpr zero_le_one),
        hθ1_zero_jet k hk_le]
      simp
    rw [hpoly0, sub_zero, Real.norm_eq_abs, sub_zero] at h1
    refine h1.trans ?_
    have hfac : (1 : ℝ) ≤ ((2 * m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * m + 1)
    have hdiv : max B_tay 0 * t ^ (2 * m + 2) / ((2 * m + 1).factorial : ℝ) ≤ max B_tay 0 * t ^ (2 * m + 2) :=
      div_le_self (mul_nonneg hB_nn (pow_nonneg ht.1 _)) hfac
    simpa [show 2 * m + 1 + 1 = 2 * m + 2 by omega] using hdiv
  -- Also `ϑ_D'(t)` is bounded on `[1, ∞)` (since `v'` has compact support)
  have hθ1_large : ∃ M₁ ≥ 0, ∀ t : ℝ, 1 ≤ t → |deriv (fctThetaD v) t| ≤ M₁ := by
    have hcont : Continuous (deriv (fctThetaD v)) := hθ1_cd.continuous
    obtain ⟨B_in, hB_in⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := R + 2)).exists_bound_of_continuousOn hcont.continuousOn
    have hsupp1 : Function.support (iteratedDeriv 1 v) ⊆ Ioo (-(R + 1)) (R + 1) := by
      intro s hs; by_contra hnot
      have hev : v =ᶠ[𝓝 s] 0 := by
        have hmem : s ∈ (Icc (-R) R)ᶜ := fun hcc => hnot ⟨by linarith [hcc.1], by linarith [hcc.2]⟩
        filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds hmem] with u hu
        by_contra hne; exact hu (Ioo_subset_Icc_self (hsupp hne))
      exact hs (by rw [hev.iteratedDeriv_eq 1, iteratedDeriv_const_zero])
    set I1 : ℝ := ∫ s : ℝ, |iteratedDeriv 1 v s|
    have hI1 : 0 ≤ I1 := integral_nonneg fun _ => abs_nonneg _
    refine ⟨max (max B_in 0) (4 * I1), by positivity, fun t ht => ?_⟩
    by_cases htR : t ≤ R + 2
    · exact le_trans (le_trans (by simpa [Real.norm_eq_abs] using hB_in t ⟨ht, htR⟩) (le_max_left _ _)) (le_max_left _ _)
    · push Not at htR
      have hbd := stripCompGExt_norm_le_of_large_im (contDiff_iteratedDeriv_infty hv 1).continuous
        (R := R + 1) (by linarith) hsupp1 (ζ := (t : ℂ) * Complex.I) ⟨by simp, by simp⟩
        (by simp [abs_of_pos (by linarith : 0 < t)]; linarith)
      have hv10 : iteratedDeriv 1 v t = 0 := by
        by_contra hne; have : |t| < R + 1 := abs_lt.mpr (hsupp1 hne); rw [abs_of_pos (by linarith)] at this; linarith
      rw [stripCompGExt_left, hv10, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, ← iteratedDeriv_fctThetaD hv hv_supp 1, iteratedDeriv_one] at hbd
      have hexp : Real.exp (-(π * (|((t : ℂ) * Complex.I).im| - (R + 1)))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
          abs_of_pos (by linarith : 0 < t)]
        nlinarith [Real.pi_pos]
      exact (hbd.trans (mul_le_of_le_one_right (by positivity) hexp)).trans (le_max_right _ _)
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := hθ1_large
  -- Integrability of `ϑ_D'(t) / t^{2m+2}` on `Ioi 0`
  have hθ1_int : IntegrableOn (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    constructor
    · have hcont : ContinuousOn (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2)) (Ioc 0 1) :=
        hθ1_cd.continuous.continuousOn.div
          (continuousOn_id.pow _) fun t ht => pow_ne_zero _ ht.1.ne'
      refine (integrableOn_const (C := max B_tay 0) (hs := measure_Ioc_lt_top.ne)).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos ht.1, div_le_iff₀ (pow_pos ht.1 _)]
      exact hθ1_small t ⟨ht.1.le, ht.2⟩
    · have hcont : ContinuousOn (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2)) (Ioi 1) :=
        hθ1_cd.continuous.continuousOn.div
          (continuousOn_id.pow _) fun t ht => pow_ne_zero _ (lt_trans zero_lt_one ht).ne'
      refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) zero_lt_one).const_mul M₁).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos ht0]
      calc |deriv (fctThetaD v) t| / t ^ (2 * m + 2)
          ≤ M₁ / t ^ (4 : ℕ) := div_le_div₀ hM₁_nn (hM₁ t (le_of_lt ht)) (pow_pos ht0 4)
            (pow_le_pow_right₀ (le_of_lt ht) (by omega))
        _ = M₁ * t ^ (-4 : ℝ) := by
            rw [Real.rpow_neg ht0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  -- Exact IBP identity: `∫_{Ioi 0} ϑ_D'(t) / t^{2m+2} dt = (1 / (2m+1)) ∫_{Ioi 0} ϑ_D''(t) / t^{2m+1} dt`
  have hibp : ∫ t in Ioi (0 : ℝ), deriv (fctThetaD v) t / t ^ (2 * m + 2) =
      (1 / ((2 * m + 1 : ℕ) : ℝ)) * ∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) := by
    -- By FTC on `[ε, R]` for `P(t) = -ϑ_D'(t) / ((2m+1) t^{2m+1})`, letting `ε ↓ 0` and `R → ∞`
    let P : ℝ → ℝ := fun t => -(deriv (fctThetaD v) t / (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m + 1)))
    have hP_deriv : ∀ t : ℝ, 0 < t →
        HasDerivAt P (deriv (fctThetaD v) t / t ^ (2 * m + 2) -
          (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))) t := by
      intro t ht
      have hd1 : HasDerivAt (deriv (fctThetaD v)) (iteratedDeriv 2 (fctThetaD v) t) t := by
        have h := ((contDiff_iteratedDeriv_infty hθ_cd 1).differentiable (by simp) t).hasDerivAt
        simpa [iteratedDeriv_succ, iteratedDeriv_one] using h
      have hd2 : HasDerivAt (fun s : ℝ => (((2 * m + 1 : ℕ) : ℝ) * s ^ (2 * m + 1)))
          (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m))) t :=
        (hasDerivAt_pow (2 * m + 1) t).const_mul _
      have hne : ((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m + 1) ≠ 0 := by positivity
      have hq := (hd1.div hd2 hne).neg
      refine hq.congr_deriv ?_
      have hm1 : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have ht0 : t ≠ 0 := ht.ne'
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ, show 2 * m + 1 = 2 * m + 1 by rfl]
      field_simp [hm1, ht0]; ring
    have hP_zero : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t => max B_tay 0 / ((2 * m + 1 : ℕ) : ℝ) * t) ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
        have ht0 : 0 < t := ht.1
        dsimp only [P]
        rw [Real.norm_eq_abs, abs_neg, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ)),
          abs_pow, abs_of_pos ht0]
        calc |deriv (fctThetaD v) t| / (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m + 1))
            ≤ (max B_tay 0 * t ^ (2 * m + 2)) / (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m + 1)) :=
              div_le_div_of_nonneg_right (hθ1_small t ⟨ht0.le, ht.2.le⟩) (by positivity)
          _ = max B_tay 0 / ((2 * m + 1 : ℕ) : ℝ) * t := by
              rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
              field_simp [ht0.ne', (show ((2 * m + 1 : ℕ) : ℝ) ≠ 0 by positivity)]
      · simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).const_mul
          (max B_tay 0 / ((2 * m + 1 : ℕ) : ℝ))
    have hP_inf : Tendsto P atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t => M₁ / ((2 * m + 1 : ℕ) : ℝ) * (t ^ (2 * m + 1))⁻¹) ?_ ?_
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
        have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
        dsimp only [P]
        rw [Real.norm_eq_abs, abs_neg, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ)),
          abs_pow, abs_of_pos ht0]
        calc |deriv (fctThetaD v) t| / (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m + 1))
            ≤ M₁ / (((2 * m + 1 : ℕ) : ℝ) * t ^ (2 * m + 1)) :=
              div_le_div_of_nonneg_right (hM₁ t ht) (by positivity)
          _ = M₁ / ((2 * m + 1 : ℕ) : ℝ) * (t ^ (2 * m + 1))⁻¹ := by ring
      · simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : 2 * m + 1 ≠ 0))).const_mul
          (M₁ / ((2 * m + 1 : ℕ) : ℝ))
    have hdiff_int : IntegrableOn (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2) -
        (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))) (Ioi 0) :=
      hθ1_int.sub (hθ2_int.const_mul _)
    have hε_eq : ∀ ε : ℝ, 0 < ε →
        ∫ t in Ioi ε, (deriv (fctThetaD v) t / t ^ (2 * m + 2) -
          (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))) = 0 - P ε := by
      intro ε hε
      exact integral_Ioi_of_hasDerivAt_of_tendsto' (fun t ht => hP_deriv t (lt_of_lt_of_le hε ht))
        (hdiff_int.mono_set (Ioi_subset_Ioi hε.le)) hP_inf
    have htend1 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, (deriv (fctThetaD v) t / t ^ (2 * m + 2) -
          (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in Ioi (0 : ℝ), (deriv (fctThetaD v) t / t ^ (2 * m + 2) -
          (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))))) := by
      have hdom : Tendsto (fun ε : ℝ => ∫ t : ℝ, (Ioi ε).indicator
          (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2) -
            (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))) t)
          (𝓝[>] (0 : ℝ))
          (𝓝 (∫ t : ℝ, (Ioi (0 : ℝ)).indicator
            (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2) -
              (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))) t)) := by
        refine tendsto_integral_filter_of_dominated_convergence
          (fun t => ‖(Ioi (0 : ℝ)).indicator (fun t : ℝ => deriv (fctThetaD v) t / t ^ (2 * m + 2) -
            (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))) t‖)
          ?_ ?_ ((integrable_indicator_iff measurableSet_Ioi).mpr hdiff_int).norm ?_
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact (((integrable_indicator_iff measurableSet_Ioi).mpr hdiff_int).aestronglyMeasurable.indicator
            (s := Ioi ε) measurableSet_Ioi).congr (Filter.Eventually.of_forall fun t => by
              by_cases h1 : t ∈ Ioi (0 : ℝ) <;> by_cases h2 : t ∈ Ioi ε <;> simp [h1, h2]
              exact absurd (lt_trans hε h2) h1)
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          refine Filter.Eventually.of_forall fun t => ?_
          by_cases h2 : t ∈ Ioi ε
          · have h1 : t ∈ Ioi (0 : ℝ) := lt_trans hε h2; simp [h1, h2]
          · simp [h2]
        · refine Filter.Eventually.of_forall fun t => ?_
          by_cases ht : 0 < t
          · refine tendsto_const_nhds.congr' ?_
            filter_upwards [Ioo_mem_nhdsGT ht] with ε hε
            have h1 : t ∈ Ioi (0 : ℝ) := ht; have h2 : t ∈ Ioi ε := hε.2; simp [h1, h2]
          · refine tendsto_const_nhds.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with ε hε
            have h1 : t ∉ Ioi (0 : ℝ) := ht
            have h2 : t ∉ Ioi ε := fun h => ht (lt_trans hε h)
            simp [h1, h2]
      simpa [integral_indicator measurableSet_Ioi] using hdom
    have htend2 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, (deriv (fctThetaD v) t / t ^ (2 * m + 2) -
          (1 / ((2 * m + 1 : ℕ) : ℝ)) * (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => 0 - P ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 - 0)) := tendsto_const_nhds.sub hP_zero
      rw [sub_self] at h0
      exact h0.congr' (eventually_nhdsWithin_of_forall fun ε hε => (hε_eq ε hε).symm)
    have h0 := tendsto_nhds_unique htend1 htend2
    rw [integral_sub hθ1_int (hθ2_int.const_mul _), integral_const_mul] at h0
    linarith
  have hθ1_int2 : IntegrableOn (fun t : ℝ => 2 * deriv (fctThetaD v) t / t ^ (2 * m + 2)) (Ioi 0) :=
    IntegrableOn.congr_fun (hθ1_int.const_mul 2) (fun t _ => by ring) measurableSet_Ioi
  refine ⟨hθ2_int.sub hθ1_int2, ?_⟩
  have hsub_eq : ∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) -
      2 * deriv (fctThetaD v) t / t ^ (2 * m + 2)) =
      ((2 * m - 1 : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) *
        ∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) := by
    have h2 : ∫ t in Ioi (0 : ℝ), 2 * deriv (fctThetaD v) t / t ^ (2 * m + 2) =
        2 * ∫ t in Ioi (0 : ℝ), deriv (fctThetaD v) t / t ^ (2 * m + 2) := by
      rw [← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    rw [integral_sub hθ2_int hθ1_int2, h2, hibp]
    have hm1 : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hm1]; ring
  rw [hsub_eq]
  have hcoeff_eq : -(((2 * m - 1 : ℝ) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0 =
      ((2 * m - 1 : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) *
        (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hm1 : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfac : ((2 * m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hm1, hfac]
  rw [hcoeff_eq, ← mul_sub, abs_mul]
  have hrat_le : |(2 * m - 1 : ℝ) / ((2 * m + 1 : ℕ) : ℝ)| ≤ 1 := by
    have hm_r : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_nonneg (div_nonneg (by linarith) (by positivity)), div_le_one (by positivity)]
    push_cast; linarith
  calc |(2 * m - 1 : ℝ) / ((2 * m + 1 : ℕ) : ℝ)| *
        |(∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) -
          (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)|
      ≤ 1 * (C₁ * ∫ t : ℝ, |v t|) := mul_le_mul hrat_le hbd1 (abs_nonneg _) zero_le_one
    _ = C₁ * ∫ t : ℝ, |v t| := one_mul _

/-- **Lemma `fct:comp-D` Part (3)** (`constant_terms_five.tex`, lines 218–228):
Exact Cauchy phase-curvature identities `(fct:cauchy-curv)` for any fixed integer `m ≥ 1` and
any real even `v ∈ C_c^∞((-R, R))` (`0 < R ≤ 1/2`) with `v(0) = 0` and `fctMoment k v = 0` for
`0 ≤ k ≤ m`:
1. General `O_m(∫ |v|)` identities (`fct_cauchy_curv_first`, `fct_cauchy_curv_second`).
2. Paper's `O_m(M τ₁³)` specialization when `Function.support v ⊆ Ioo (-10 τ₁) (10 τ₁)`
   (`0 < τ₁ ≤ 1/20`) and `∀ t, |iteratedDeriv 2 v t| ≤ M`.
3. Explicit `m = 1` leading coefficients `-(π / 4)` and `-(π / 12)`. -/
theorem fct_comp_D_part3 {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ {v : ℝ → ℝ} {R : ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → (∀ t, v (-t) = v t) →
        0 < R → R ≤ 1 / 2 → Function.support v ⊆ Ioo (-R) R → v 0 = 0 →
        (∀ k ≤ m, fctMoment k v = 0) →
        IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) (Ioi 0) ∧
        IntegrableOn (fun t : ℝ =>
          iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) -
          2 * deriv (fctThetaD v) t / t ^ (2 * m + 2)) (Ioi 0) ∧
        |(∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) -
          (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| ≤
          C * (∫ t : ℝ, |v t|) ∧
        |(∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) -
            2 * deriv (fctThetaD v) t / t ^ (2 * m + 2))) -
          (-(((2 * m - 1 : ℝ) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| ≤
          C * (∫ t : ℝ, |v t|)) ∧
      (∀ {v : ℝ → ℝ} {τ₁ M : ℝ}, ContDiff ℝ (⊤ : ℕ∞) v → (∀ t, v (-t) = v t) →
        0 < τ₁ → τ₁ ≤ 1 / 20 → Function.support v ⊆ Ioo (-(10 * τ₁)) (10 * τ₁) → v 0 = 0 →
        0 ≤ M → (∀ t, |iteratedDeriv 2 v t| ≤ M) →
        (∀ k ≤ m, fctMoment k v = 0) →
        |(∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1)) -
          (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| ≤
          C * M * τ₁ ^ 3 ∧
        |(∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v) t / t ^ (2 * m + 1) -
            2 * deriv (fctThetaD v) t / t ^ (2 * m + 2))) -
          (-(((2 * m - 1 : ℝ) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v 0)| ≤
          C * M * τ₁ ^ 3) ∧
      (m = 1 →
        (-(π / (2 * ((2 * m).factorial : ℝ))) = -(π / 4)) ∧
        (-(((2 * m - 1 : ℝ) * π) / (2 * ((2 * m + 1).factorial : ℝ))) = -(π / 12))) := by
  obtain ⟨C₁, hC₁_nn, h1⟩ := fct_cauchy_curv_first hm
  obtain ⟨C₂, hC₂_nn, h2⟩ := fct_cauchy_curv_second hm
  set C0 : ℝ := max C₁ C₂
  have hC0_nn : 0 ≤ C0 := le_trans hC₁_nn (le_max_left _ _)
  refine ⟨max C0 ((1000 / 3 : ℝ) * C0), by positivity, ?_, ?_, ?_⟩
  · intro v R hv hv_even hR0 hR12 hsupp hv0 hmom
    obtain ⟨hi1, hb1⟩ := h1 hv hv_even hR0 hR12 hsupp hv0 hmom
    obtain ⟨hi2, hb2⟩ := h2 hv hv_even hR0 hR12 hsupp hv0 hmom
    have hint_nn : 0 ≤ ∫ t : ℝ, |v t| := integral_nonneg fun _ => abs_nonneg _
    have hC1_le : C₁ ≤ max C0 ((1000 / 3 : ℝ) * C0) := (le_max_left _ _).trans (le_max_left _ _)
    have hC2_le : C₂ ≤ max C0 ((1000 / 3 : ℝ) * C0) := (le_max_right _ _).trans (le_max_left _ _)
    exact ⟨hi1, hi2,
      hb1.trans (mul_le_mul_of_nonneg_right hC1_le hint_nn),
      hb2.trans (mul_le_mul_of_nonneg_right hC2_le hint_nn)⟩
  · intro v τ₁ M hv hv_even hτ₁ hτ₁_le hsupp hv0 hM hM_bd hmom
    have hR0 : 0 < 10 * τ₁ := by positivity
    have hR12 : 10 * τ₁ ≤ 1 / 2 := by linarith
    obtain ⟨_, hb1⟩ := h1 hv hv_even hR0 hR12 hsupp hv0 hmom
    obtain ⟨_, hb2⟩ := h2 hv hv_even hR0 hR12 hsupp hv0 hmom
    -- Bound `|v(t)| ≤ (M / 2) * t²` for all `t : ℝ` via FTC from `v(0) = v'(0) = 0`
    have hv'_zero : deriv v 0 = 0 := by
      have h := iteratedDeriv_odd_zero hv_even 0
      simpa [iteratedDeriv_one] using h
    have hv_pt : ∀ t : ℝ, |v t| ≤ (M / 2) * t ^ 2 := by
      have hv_pos : ∀ t : ℝ, 0 ≤ t → |v t| ≤ (M / 2) * t ^ 2 := by
        intro t ht
        have hd1 : ∀ s : ℝ, 0 ≤ s → |deriv v s| ≤ M * s := by
          intro s hs
          have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := deriv v) (f' := iteratedDeriv 2 v) (a := 0) (b := s)
            (fun u _ => by
              have hd := (contDiff_iteratedDeriv_infty hv 1).differentiable (by simp) u
              simpa [iteratedDeriv_succ, iteratedDeriv_one] using hd.hasDerivAt)
            ((contDiff_iteratedDeriv_infty hv 2).continuous.intervalIntegrable _ _)
          rw [hv'_zero, sub_zero] at hftc
          calc |deriv v s| = ‖∫ u in (0 : ℝ)..s, iteratedDeriv 2 v u‖ := by rw [hftc, Real.norm_eq_abs]
            _ ≤ ∫ u in (0 : ℝ)..s, ‖iteratedDeriv 2 v u‖ := intervalIntegral.norm_integral_le_integral_norm hs
            _ ≤ ∫ u in (0 : ℝ)..s, M :=
                intervalIntegral.integral_mono_on hs
                  ((contDiff_iteratedDeriv_infty hv 2).continuous.norm.intervalIntegrable _ _)
                  intervalIntegrable_const (fun u _ => by simpa [Real.norm_eq_abs] using hM_bd u)
            _ = M * s := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        have hv'_cont : Continuous (deriv v) := by
          simpa [iteratedDeriv_one] using (contDiff_iteratedDeriv_infty hv 1).continuous
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := v) (f' := deriv v) (a := 0) (b := t)
          (fun s _ => (hv.differentiable (by simp) s).hasDerivAt)
          (hv'_cont.intervalIntegrable _ _)
        rw [hv0, sub_zero] at hftc
        calc |v t| = ‖∫ s in (0 : ℝ)..t, deriv v s‖ := by rw [hftc, Real.norm_eq_abs]
          _ ≤ ∫ s in (0 : ℝ)..t, ‖deriv v s‖ := intervalIntegral.norm_integral_le_integral_norm ht
          _ ≤ ∫ s in (0 : ℝ)..t, M * s :=
              intervalIntegral.integral_mono_on ht
                (hv'_cont.norm.intervalIntegrable _ _)
                ((continuous_const.mul continuous_id).intervalIntegrable _ _)
                (fun s hs => by simpa [Real.norm_eq_abs] using hd1 s hs.1)
          _ = (M / 2) * t ^ 2 := by
              rw [intervalIntegral.integral_const_mul, integral_id]; ring
      intro t
      rcases le_total 0 t with ht | ht
      · exact hv_pos t ht
      · rw [← hv_even t, ← neg_sq t]; exact hv_pos (-t) (neg_nonneg.mpr ht)
    -- Integrate `|v|` over `[-(10 τ₁), 10 τ₁]`
    have hv_L1 : (∫ t : ℝ, |v t|) ≤ (1000 / 3 : ℝ) * M * τ₁ ^ 3 := by
      have hsupp_abs : Function.support (fun t : ℝ => |v t|) ⊆ Ioc (-(10 * τ₁)) (10 * τ₁) := fun t ht => by
        have hne : v t ≠ 0 := fun h0 => ht (by simp [h0])
        exact Ioo_subset_Ioc_self (hsupp hne)
      have heq_int : (∫ t : ℝ, |v t|) = ∫ t in (-(10 * τ₁))..(10 * τ₁), |v t| := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
        congr 1; ext t; by_cases ht : t ∈ Ioc (-(10 * τ₁)) (10 * τ₁)
        · simp [ht]
        · simp only [Set.indicator_of_notMem ht]; by_contra hne
          exact ht (hsupp_abs hne)
      rw [heq_int]
      calc ∫ t in (-(10 * τ₁))..(10 * τ₁), |v t|
          ≤ ∫ t in (-(10 * τ₁))..(10 * τ₁), (M / 2) * t ^ 2 :=
            intervalIntegral.integral_mono_on (by linarith)
              (hv.continuous.abs.intervalIntegrable _ _)
              ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _)
              (fun t _ => hv_pt t)
        _ = (1000 / 3 : ℝ) * M * τ₁ ^ 3 := by
            rw [intervalIntegral.integral_const_mul, integral_pow]; ring
    have hC0_le : (1000 / 3 : ℝ) * C0 ≤ max C0 ((1000 / 3 : ℝ) * C0) := le_max_right _ _
    have h1' : C₁ * (∫ t : ℝ, |v t|) ≤ max C0 ((1000 / 3 : ℝ) * C0) * M * τ₁ ^ 3 := by
      calc C₁ * (∫ t : ℝ, |v t|)
          ≤ C0 * ((1000 / 3 : ℝ) * M * τ₁ ^ 3) :=
            mul_le_mul (le_max_left _ _) hv_L1 (integral_nonneg fun _ => abs_nonneg _) hC0_nn
        _ = ((1000 / 3 : ℝ) * C0) * M * τ₁ ^ 3 := by ring
        _ ≤ max C0 ((1000 / 3 : ℝ) * C0) * M * τ₁ ^ 3 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0_le hM) (pow_nonneg hτ₁.le 3)
    have h2' : C₂ * (∫ t : ℝ, |v t|) ≤ max C0 ((1000 / 3 : ℝ) * C0) * M * τ₁ ^ 3 := by
      calc C₂ * (∫ t : ℝ, |v t|)
          ≤ C0 * ((1000 / 3 : ℝ) * M * τ₁ ^ 3) :=
            mul_le_mul (le_max_right _ _) hv_L1 (integral_nonneg fun _ => abs_nonneg _) hC0_nn
        _ = ((1000 / 3 : ℝ) * C0) * M * τ₁ ^ 3 := by ring
        _ ≤ max C0 ((1000 / 3 : ℝ) * C0) * M * τ₁ ^ 3 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0_le hM) (pow_nonneg hτ₁.le 3)
    exact ⟨hb1.trans h1', hb2.trans h2'⟩
  · rintro rfl; constructor <;> norm_num [Nat.factorial]

/-- info: 'FormalResearch.SignUncertainty.FctCompD.fct_comp_D_part3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctCompD.fct_comp_D_part3

end FormalResearch.SignUncertainty.FctCompD

