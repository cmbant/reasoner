module

public import FormalResearch.CohnElkies.MellinT3Complete
public import FormalResearch.CohnElkies.SaddleGeometry
public import FormalResearch.SignUncertainty.HankelLangerIdentity
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Lemma T.3 (`mat:T3`), parts (1) and (2): Taylor positivity, bijection, derivative bounds, and `(e35)`

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.3 (`mat:T3`), parts (1) and (2),
equations `(cel:5.1)` and `(e35)`.

## Main declarations
* **Part (1), Taylor series with positive coefficients:**
  * `stripGCoeff k = η_D(2k + 2) / (k + 1)` with `stripGCoeff_zero : stripGCoeff 0 = π² / 12` and
    `stripGCoeff_pos : 0 < stripGCoeff k`.
  * `stripG_hasSum` / `stripG_eq_tsum`: on `‖ζ‖ < 1`,
    `stripG ζ = ∑' k : ℕ, (stripGCoeff k : ℂ) * ζ ^ (2 * k + 2)`.
  * `stripGReal_hasSum` / `stripGReal_eq_tsum`: real restriction on `|σ| < 1`.
* **Part (1), bijection and full derivative bounds `(cel:5.1)`:**
  * `stripGReal_bijOn`: `stripGReal` maps `(0, 1)` bijectively onto `(0, ∞)` (strictly increasing by
    `stripGReal_strictMonoOn`).
  * `stripGReal_deriv_bounds`: for `σ ∈ (0, 1)`,
    `(3/4) σ / (1 - σ) < deriv stripGReal σ < 2 σ / (1 - σ²) < 2 σ / (1 - σ)`.
* **Part (2), positivity bounds and equation `(e35)`:**
  * `norm_stripG_le` and `norm_log_tan_div_le`: `‖g(ζ)‖ ≤ g(‖ζ‖)` on `‖ζ‖ < 1` and
    `‖log(tan z / z)‖ ≤ log(tan ‖z‖ / ‖z‖)` on `0 < ‖z‖ < π / 2`.
  * `stripS0Tilde_hasSum` / `stripS0Tilde_eq_tsum`: on `‖ζ‖ < 1`,
    `stripS0Tilde ζ = ∑' k : ℕ, (stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)` with `stripS0Coeff k > 0`.
  * `norm_stripS0Tilde_le` and `norm_stripS0Tilde_le_mul_cube`: `‖S̃₀(ζ)‖ ≤ S̃₀(‖ζ‖)` and
    `‖S̃₀(ζ)‖ ≤ (S̃₀(R) / R³) ‖ζ‖³` for `‖ζ‖ ≤ R < 1`.
  * `norm_c_mul_stripS0Tilde_le`, `two_mul_stripS0Tilde_e35Radius_lt`, and
    `sSup_c_mul_stripS0Tilde_le`: equation `(e35)`,
    `sup_{c ≥ 2, |w| ≤ 2/√3} |c S̃₀(c^{-1/3} w)| ≤ 2 S̃₀(2^{2/3} / √3) < 1.1`.
-/

@[expose] public section

open Set Metric Filter Topology Complex Finset
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.SignUncertainty

/-! ### Part (1): Taylor series of `g = stripG` on `‖ζ‖ < 1` -/

/-- Taylor coefficient `c_{2k+2} = η_D(2k + 2) / (k + 1)` of `g(ζ) = ∑_{k≥0} c_{2k+2} ζ^{2k+2}`
(`mat:T3`(1)). -/
noncomputable def stripGCoeff (k : ℕ) : ℝ := langerc k

/-- **Lemma T.3(1) (`mat:T3`):** leading coefficient `c₂ = π² / 12`. -/
theorem stripGCoeff_zero : stripGCoeff 0 = π ^ 2 / 12 := by
  unfold stripGCoeff langerc
  rw [etaC_zero]
  norm_num

/-- **Lemma T.3(1) (`mat:T3`):** every even Taylor coefficient `c_{2k+2}` is strictly positive. -/
theorem stripGCoeff_pos (k : ℕ) : 0 < stripGCoeff k :=
  div_pos (etaC_pos k) (by positivity)

/-- `Pser` is complex differentiable on the entire open unit disk `‖y‖ < 1`, with derivative
`∑' j, 2 η_D(2j+2) y^(2j+1)`. -/
private lemma Pser_hasDerivAt_unit {y : ℂ} (hy : ‖y‖ < 1) :
    HasDerivAt Pser (∑' j : ℕ, 2 * (etaC j : ℂ) * y ^ (2 * j + 1)) y := by
  set r : ℝ := (‖y‖ + 1) / 2 with hr_def
  have hr0 : 0 < r := by linarith [norm_nonneg y]
  have hr1 : r < 1 := by linarith
  have hyr : ‖y‖ < r := by linarith
  have hr2_lt : r ^ 2 < 1 := by nlinarith
  have hu : Summable (fun j : ℕ => ((2 * j + 2 : ℕ) : ℝ) * r ^ (2 * j + 1)) := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 (r := r ^ 2)
      (by rw [Real.norm_of_nonneg (sq_nonneg r)]; exact hr2_lt)).mul_left (2 * r)
    have h2 := (summable_geometric_of_lt_one (sq_nonneg r) hr2_lt).mul_left (2 * r)
    refine (h1.add h2).congr fun j => ?_
    push_cast
    have hpow : r ^ (2 * j + 1) = r * (r ^ 2) ^ j := by
      rw [pow_succ, pow_mul]; ring
    rw [hpow]
    ring
  have hd := hasDerivAt_tsum_of_isPreconnected (t := ball (0 : ℂ) r)
    (y₀ := 0) (u := fun j : ℕ => ((2 * j + 2 : ℕ) : ℝ) * r ^ (2 * j + 1))
    (g := fun (j : ℕ) (w : ℂ) => ((langerc j : ℝ) : ℂ) * w ^ (2 * j + 2))
    (g' := fun (j : ℕ) (w : ℂ) =>
      ((langerc j : ℝ) : ℂ) * (((2 * j + 2 : ℕ) : ℂ) * w ^ (2 * j + 2 - 1)))
    hu isOpen_ball (convex_ball _ _).isPreconnected
    (fun n w _ => (hasDerivAt_pow (2 * n + 2) w).const_mul _)
    (by
      intro n w hw
      have hw' : ‖w‖ < r := mem_ball_zero_iff.mp hw
      have hw2 : ‖w‖ ^ (2 * n + 1) ≤ r ^ (2 * n + 1) :=
        pow_le_pow_left₀ (norm_nonneg _) hw'.le _
      rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (langerc_nonneg n), norm_pow, Complex.norm_natCast]
      calc langerc n * (((2 * n + 2 : ℕ) : ℝ) * ‖w‖ ^ (2 * n + 1))
          ≤ 1 * (((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1)) :=
            mul_le_mul (langerc_le_one n) (mul_le_mul_of_nonneg_left hw2 (by positivity))
              (by positivity) zero_le_one
        _ = ((2 * n + 2 : ℕ) : ℝ) * r ^ (2 * n + 1) := one_mul _)
    (mem_ball_zero_iff.mpr (by simpa using hr0))
    (by
      have : (fun n : ℕ => ((langerc n : ℝ) : ℂ) * (0 : ℂ) ^ (2 * n + 2)) = fun _ => 0 := by
        funext n
        rw [zero_pow (by omega), mul_zero]
      show Summable (fun n : ℕ => ((langerc n : ℝ) : ℂ) * (0 : ℂ) ^ (2 * n + 2))
      rw [this]
      exact summable_zero)
    (mem_ball_zero_iff.mpr hyr)
  have hval : (∑' j : ℕ, ((langerc j : ℝ) : ℂ) * (((2 * j + 2 : ℕ) : ℂ) * y ^ (2 * j + 2 - 1))) =
      ∑' j : ℕ, 2 * (etaC j : ℂ) * y ^ (2 * j + 1) := by
    congr 1
    funext j
    rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega]
    unfold langerc
    push_cast
    have hj : ((j : ℂ) + 1) ≠ 0 := by
      intro h
      have : (j : ℝ) + 1 = 0 := by exact_mod_cast h
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    field_simp
  rw [← hval]
  exact hd

/-- `stripG` agrees with `Pser` on the entire open unit disk `‖ζ‖ < 1`, by analytic continuation
from `‖ζ‖ < 1/8` (`HankelLangerIdentity.log_langerU_eq`). -/
lemma stripG_eq_Pser {ζ : ℂ} (hζ : ‖ζ‖ < 1) : stripG ζ = Pser ζ := by
  have hdiffG : DifferentiableOn ℂ stripG (ball (0 : ℂ) 1) :=
    differentiableOn_stripG.mono ball_subset_edgeStrip
  have hdiffP : DifferentiableOn ℂ Pser (ball (0 : ℂ) 1) := fun w hw =>
    (Pser_hasDerivAt_unit (mem_ball_zero_iff.mp hw)).differentiableAt.differentiableWithinAt
  have hanG : AnalyticOnNhd ℂ stripG (ball (0 : ℂ) 1) := hdiffG.analyticOnNhd isOpen_ball
  have hanP : AnalyticOnNhd ℂ Pser (ball (0 : ℂ) 1) := hdiffP.analyticOnNhd isOpen_ball
  have hev : stripG =ᶠ[𝓝 (0 : ℂ)] Pser := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
    have hw' : ‖w‖ < 1 / 8 := mem_ball_zero_iff.mp hw
    by_cases hw0 : w = 0
    · subst hw0; simp [stripG, Pser_zero]
    · simp only [stripG, hw0, ↓reduceIte]
      exact log_langerU_eq hw'
  exact hanG.eqOn_of_preconnected_of_eventuallyEq hanP (convex_ball (0 : ℂ) 1).isPreconnected
    (mem_ball_self zero_lt_one) hev (mem_ball_zero_iff.mpr hζ)

/-- **Lemma T.3(1) (`mat:T3`):** `HasSum` Taylor expansion of `g = stripG` on `‖ζ‖ < 1`,
`g(ζ) = ∑_{k≥0} c_{2k+2} ζ^{2k+2}` with `c_{2k+2} = stripGCoeff k > 0`. -/
theorem stripG_hasSum {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasSum (fun k : ℕ => (stripGCoeff k : ℂ) * ζ ^ (2 * k + 2)) (stripG ζ) := by
  rw [stripG_eq_Pser hζ]
  exact (Pser_summable hζ).hasSum

/-- **Lemma T.3(1) (`mat:T3`):** power series identity for `g = stripG` on `‖ζ‖ < 1`. -/
theorem stripG_eq_tsum {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    stripG ζ = ∑' k : ℕ, (stripGCoeff k : ℂ) * ζ ^ (2 * k + 2) :=
  (stripG_hasSum hζ).tsum_eq.symm

/-- Real-variable `HasSum` expansion of `stripGReal` on `|σ| < 1` (`mat:T3`(1)). -/
theorem stripGReal_hasSum {σ : ℝ} (hσ : |σ| < 1) :
    HasSum (fun k : ℕ => stripGCoeff k * σ ^ (2 * k + 2)) (stripGReal σ) := by
  have hnorm : ‖(σ : ℂ)‖ < 1 := by simpa [Real.norm_eq_abs] using hσ
  have hC := stripG_hasSum hnorm
  have hre : (stripG (σ : ℂ)).re = stripGReal σ := by
    rcases lt_trichotomy σ 0 with hneg | rfl | hpos
    · have hpos' : 0 < -σ := neg_pos.mpr hneg
      have hlt1 : -σ < 1 := by rwa [abs_of_neg hneg] at hσ
      have h1 : stripG (σ : ℂ) = stripG ((-σ : ℝ) : ℂ) := by
        rw [Complex.ofReal_neg, stripG_even]
      have h2 : stripGReal σ = stripGReal (-σ) := by
        simp only [stripGReal, hneg.ne, hpos'.ne', ↓reduceIte]
        congr 1
        rw [show π * -σ / 2 = -(π * σ / 2) by ring, Real.tan_neg, neg_div_neg_eq]
      rw [h1, h2, stripG_ofReal_re hpos' hlt1]
    · simp [stripG, stripGReal]
    · exact stripG_ofReal_re hpos (by rwa [abs_of_pos hpos] at hσ)
  rw [← hre]
  have hcast : (fun k : ℕ => (stripGCoeff k : ℂ) * (σ : ℂ) ^ (2 * k + 2)) =
      fun k : ℕ => ((stripGCoeff k * σ ^ (2 * k + 2) : ℝ) : ℂ) := by
    funext k; push_cast; rfl
  rw [hcast] at hC
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum hC

/-- Real-variable power series identity for `stripGReal` on `|σ| < 1` (`mat:T3`(1)). -/
theorem stripGReal_eq_tsum {σ : ℝ} (hσ : |σ| < 1) :
    stripGReal σ = ∑' k : ℕ, stripGCoeff k * σ ^ (2 * k + 2) :=
  (stripGReal_hasSum hσ).tsum_eq.symm

/-! ### Part (1): Bijectivity of `g` on `(0, 1) → (0, ∞)` and derivative bounds `(cel:5.1)` -/

/-- `g(σ) → +∞` as `σ → 1⁻` (`mat:T3`(1)). -/
theorem stripGReal_tendsto_atTop : Tendsto stripGReal (𝓝[<] (1 : ℝ)) atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  set δ : ℝ := min (1 / 2) (1 / (π ^ 2 * Real.exp M)) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_exp : δ ≤ 1 / (π ^ 2 * Real.exp M) := min_le_right _ _
  filter_upwards [Ioo_mem_nhdsLT (show 1 - δ < 1 by linarith)] with σ hσ
  have hσ_gt : 1 - δ < σ := hσ.1
  have hσ1 : σ < 1 := hσ.2
  have hσ_half : 1 / 2 < σ := by linarith
  have hσ0 : 0 < σ := by linarith
  have h1s_pos : 0 < 1 - σ := by linarith
  have h1s_lt : 1 - σ < δ := by linarith
  -- Lower bound `sin(π σ / 2) ≥ √2 / 2 > 1 / 2` since `π / 4 < π σ / 2 < π / 2`
  have hsin_ge : 1 / 2 ≤ Real.sin (π * σ / 2) := by
    have h1 : π / 4 ≤ π * σ / 2 := by nlinarith [Real.pi_pos]
    have h2 : π * σ / 2 ≤ π / 2 := by nlinarith [Real.pi_pos]
    have hmono : Real.sin (π / 4) ≤ Real.sin (π * σ / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2 h1
    rw [Real.sin_pi_div_four] at hmono
    have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  -- Upper bound `cos(π σ / 2) = sin(π (1 - σ) / 2) ≤ π (1 - σ) / 2`
  have hcos_pos : 0 < Real.cos (π * σ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hcos_le : Real.cos (π * σ / 2) ≤ π * (1 - σ) / 2 := by
    have heq : Real.cos (π * σ / 2) = Real.sin (π * (1 - σ) / 2) := by
      rw [show π * σ / 2 = π / 2 - π * (1 - σ) / 2 by ring, Real.cos_pi_div_two_sub]
    rw [heq]
    exact Real.sin_le (by positivity)
  have hpiσ_le : π * σ / 2 ≤ π / 2 := by nlinarith [Real.pi_pos]
  have hden_le : Real.cos (π * σ / 2) * (π * σ / 2) ≤ π ^ 2 * (1 - σ) / 4 := by
    calc Real.cos (π * σ / 2) * (π * σ / 2)
        ≤ (π * (1 - σ) / 2) * (π / 2) :=
          mul_le_mul hcos_le hpiσ_le (by positivity) (by positivity)
      _ = π ^ 2 * (1 - σ) / 4 := by ring
  have hratio : Real.exp M ≤ Real.tan (π * σ / 2) / (π * σ / 2) := by
    rw [Real.tan_eq_sin_div_cos, div_div, le_div_iff₀ (mul_pos hcos_pos (by positivity))]
    have h1 : Real.exp M * (π ^ 2 * (1 - σ) / 4) ≤ 1 / 4 := by
      have h2 : π ^ 2 * Real.exp M * (1 - σ) ≤ 1 := by
        have h3 : 1 - σ ≤ 1 / (π ^ 2 * Real.exp M) := h1s_lt.le.trans hδ_le_exp
        exact (le_div_iff₀' (by positivity)).mp h3
      linarith
    calc Real.exp M * (Real.cos (π * σ / 2) * (π * σ / 2))
        ≤ Real.exp M * (π ^ 2 * (1 - σ) / 4) :=
          mul_le_mul_of_nonneg_left hden_le (Real.exp_pos M).le
      _ ≤ 1 / 4 := h1
      _ ≤ 1 / 2 := by norm_num
      _ ≤ Real.sin (π * σ / 2) := hsin_ge
  simp only [stripGReal, hσ0.ne', ↓reduceIte]
  rw [← Real.log_exp M]
  exact Real.log_le_log (Real.exp_pos M) hratio

/-- **Lemma T.3(1) (`mat:T3`):** `g = stripGReal` maps `(0, 1)` bijectively onto `(0, ∞)`
(and is strictly increasing by `stripGReal_strictMonoOn`). -/
theorem stripGReal_bijOn : BijOn stripGReal (Ioo 0 1) (Ioi 0) := by
  refine ⟨fun σ hσ => stripGReal_pos hσ.1 hσ.2, stripGReal_strictMonoOn.injOn, ?_⟩
  intro y hy
  have hy0 : 0 < y := mem_Ioi.mp hy
  -- Find `a ∈ (0, 1)` with `stripGReal a < y` using continuity at `0⁺`
  have hcont0 : Tendsto stripGReal (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 := stripGReal_continuousOn 0 ⟨le_rfl, zero_lt_one⟩
    rw [ContinuousWithinAt, show stripGReal 0 = 0 by simp [stripGReal],
      nhdsWithin_Ico_eq_nhdsGE zero_lt_one] at h0
    exact h0.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  obtain ⟨a, ha_lt, ha_mem⟩ :=
    ((hcont0.eventually (Iio_mem_nhds hy0)).and (Ioo_mem_nhdsGT zero_lt_one)).exists
  -- Find `b ∈ (0, 1)` with `y < stripGReal b` and `a ≤ b`
  obtain ⟨b, hb_gt, hb_mem⟩ :=
    ((stripGReal_tendsto_atTop.eventually (Ioi_mem_atTop y)).and
      (Ioo_mem_nhdsLT ha_mem.2)).exists
  have hab : a ≤ b := hb_mem.1.le
  have hsub : Icc a b ⊆ Ioo 0 1 := fun x hx => ⟨ha_mem.1.trans_le hx.1, hx.2.trans_lt hb_mem.2⟩
  have hcont : ContinuousOn stripGReal (Icc a b) :=
    stripGReal_continuousOn.mono (hsub.trans Ioo_subset_Ico_self)
  have hmem : y ∈ Icc (stripGReal a) (stripGReal b) := ⟨ha_lt.le, hb_gt.le⟩
  obtain ⟨σ, hσ_Icc, hσ_eq⟩ := intermediate_value_Icc hab hcont hmem
  exact ⟨σ, hsub hσ_Icc, hσ_eq⟩

/-- **Lemma T.3(1) (`mat:T3`, equation `(cel:5.1)`):** for all `σ ∈ (0, 1)`,
`(3/4) σ / (1 - σ) < deriv stripGReal σ < 2 σ / (1 - σ²) < 2 σ / (1 - σ)`. -/
theorem stripGReal_deriv_bounds {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    3 / 4 * σ / (1 - σ) < deriv stripGReal σ ∧
      deriv stripGReal σ < 2 * σ / (1 - σ ^ 2) ∧
      2 * σ / (1 - σ ^ 2) < 2 * σ / (1 - σ) := by
  have hd : deriv stripGReal σ = π / Real.sin (π * σ) - 1 / σ :=
    (hasDerivAt_stripGReal h0 h1).deriv
  rw [hd]
  refine ⟨(stripG_deriv_bounds h0 h1).1, ?_, ?_⟩
  · -- Sharper middle bound `π / sin(π σ) - 1 / σ < 2 σ / (1 - σ²)` from the alternating series
    -- `csc_hasSum`: `π / sin(π σ) - 1 / σ = ∑' n, (-1)^n * (2 σ / ((n + 1)² - σ²))`
    have hnorm : ‖(σ : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; exact h1
    have hC := csc_hasSum (Complex.ofReal_ne_zero.mpr h0.ne') hnorm
    have hre : (π / Complex.sin (π * (σ : ℂ)) - 1 / (σ : ℂ)).re = π / Real.sin (π * σ) - 1 / σ := by
      have : π / Complex.sin (π * (σ : ℂ)) - 1 / (σ : ℂ) =
          ((π / Real.sin (π * σ) - 1 / σ : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_re]
    set a : ℕ → ℝ := fun n => 2 * σ / (((n : ℝ) + 1) ^ 2 - σ ^ 2) with ha_def
    have hR : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * a n) (π / Real.sin (π * σ) - 1 / σ) := by
      rw [← hre]
      have hcast : (fun n : ℕ => 2 * (-1 : ℂ) ^ n * (σ : ℂ) / (((n : ℂ) + 1) ^ 2 - (σ : ℂ) ^ 2)) =
          fun n : ℕ => (((-1 : ℝ) ^ n * a n : ℝ) : ℂ) := by
        funext n; simp only [ha_def]; push_cast; ring
      rw [hcast] at hC
      simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum hC
    have hT : Tendsto (fun N : ℕ => ∑ i ∈ range N, (-1 : ℝ) ^ i * a i)
        atTop (𝓝 (π / Real.sin (π * σ) - 1 / σ)) :=
      hR.tendsto_sum_nat
    have hA : Antitone a := by
      intro m n hmn
      simp only [ha_def]
      have hm1 : 1 ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith
      have hden_pos : 0 < ((m : ℝ) + 1) ^ 2 - σ ^ 2 := by nlinarith
      have hden_le : ((m : ℝ) + 1) ^ 2 - σ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 - σ ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
    have hle : π / Real.sin (π * σ) - 1 / σ ≤ ∑ i ∈ range 3, (-1 : ℝ) ^ i * a i := by
      have := hA.tendsto_le_alternating_series hT 1
      simpa using this
    have hsum3 : ∑ i ∈ range 3, (-1 : ℝ) ^ i * a i = a 0 - a 1 + a 2 := by
      simp [Finset.sum_range_succ]; ring
    have ha0 : a 0 = 2 * σ / (1 - σ ^ 2) := by simp [ha_def]
    have ha2_lt_a1 : a 2 < a 1 := by
      simp only [ha_def]
      refine div_lt_div_of_pos_left (by positivity) (by push_cast; nlinarith) ?_
      norm_num
    linarith
  · -- `2 σ / (1 - σ²) < 2 σ / (1 - σ)` since `1 - σ < 1 - σ²`
    refine div_lt_div_of_pos_left (by positivity) (sub_pos.mpr h1) ?_
    nlinarith

/-! ### Part (2): Positivity bounds, Taylor series of `S̃₀`, and equation `(e35)` -/

/-- **Lemma T.3(2) (`mat:T3`):** coefficient positivity gives `‖g(ζ)‖ ≤ g(‖ζ‖)` on `‖ζ‖ < 1`. -/
theorem norm_stripG_le {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ‖stripG ζ‖ ≤ stripGReal ‖ζ‖ := by
  rw [stripG_eq_tsum hζ, stripGReal_eq_tsum (by rw [abs_of_nonneg (norm_nonneg ζ)]; exact hζ)]
  have hR := (stripGReal_hasSum (σ := ‖ζ‖) (by rw [abs_of_nonneg (norm_nonneg ζ)]; exact hζ)).summable
  have hnorm_eq : (fun k : ℕ => ‖(stripGCoeff k : ℂ) * ζ ^ (2 * k + 2)‖) =
      fun k : ℕ => stripGCoeff k * ‖ζ‖ ^ (2 * k + 2) := by
    funext k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stripGCoeff_pos k)]
  have hsn : Summable (fun k : ℕ => ‖(stripGCoeff k : ℂ) * ζ ^ (2 * k + 2)‖) := by
    rw [hnorm_eq]; exact hR
  calc ‖∑' k : ℕ, (stripGCoeff k : ℂ) * ζ ^ (2 * k + 2)‖
      ≤ ∑' k : ℕ, ‖(stripGCoeff k : ℂ) * ζ ^ (2 * k + 2)‖ := norm_tsum_le_tsum_norm hsn
    _ = ∑' k : ℕ, stripGCoeff k * ‖ζ‖ ^ (2 * k + 2) := by rw [hnorm_eq]

/-- **Lemma T.3(2) (`mat:T3`):** in the variable `z = π ζ / 2`,
`‖log(tan z / z)‖ ≤ log(tan ‖z‖ / ‖z‖)` for `0 < ‖z‖ < π / 2`. -/
theorem norm_log_tan_div_le {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < π / 2) :
    ‖Complex.log (Complex.tan z / z)‖ ≤ Real.log (Real.tan ‖z‖ / ‖z‖) := by
  set ζ : ℂ := 2 * z / (π : ℂ) with hζ_def
  have hπc : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hζ0 : ζ ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hz0) hπc
  have hζ_norm : ‖ζ‖ = 2 * ‖z‖ / π := by
    rw [hζ_def, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
  have hζ_lt : ‖ζ‖ < 1 := by
    rw [hζ_norm, div_lt_one Real.pi_pos]; linarith
  have h1 : stripG ζ = Complex.log (Complex.tan z / z) := by
    simp only [stripG, hζ0, ↓reduceIte]
    have heq : (π : ℂ) * ζ / 2 = z := by rw [hζ_def]; field_simp
    rw [heq]
  have h2 : stripGReal ‖ζ‖ = Real.log (Real.tan ‖z‖ / ‖z‖) := by
    have hn0 : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ0
    simp only [stripGReal, hn0, ↓reduceIte]
    have heq : π * ‖ζ‖ / 2 = ‖z‖ := by
      rw [hζ_norm]; field_simp [Real.pi_ne_zero]
    rw [heq]
  rw [← h1, ← h2]
  exact norm_stripG_le hζ_lt

/-- Taylor coefficient `s_k = stripGCoeff k / (2k + 3) = η_D(2k + 2) / ((k + 1)(2k + 3))` of
`S̃₀(ζ) = ∑_{k≥0} s_k ζ^{2k+3}` (`mat:T3`(2)). -/
noncomputable def stripS0Coeff (k : ℕ) : ℝ := stripGCoeff k / (2 * (k : ℝ) + 3)

/-- Every Taylor coefficient `stripS0Coeff k` of `S̃₀` is strictly positive (`mat:T3`(2)). -/
theorem stripS0Coeff_pos (k : ℕ) : 0 < stripS0Coeff k :=
  div_pos (stripGCoeff_pos k) (by positivity)

private lemma stripS0Coeff_le_inv (k : ℕ) :
    stripS0Coeff k ≤ 1 / (((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) := by
  unfold stripS0Coeff stripGCoeff langerc
  rw [div_div]
  exact div_le_div_of_nonneg_right (etaC_lt_one k).le (by positivity)

private lemma stripS0Coeff_le_one (k : ℕ) : stripS0Coeff k ≤ 1 := by
  refine (stripS0Coeff_le_inv k).trans ?_
  rw [div_le_one (by positivity)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- Power series `Sser(ζ) = ∑_{k≥0} stripS0Coeff k * ζ^(2k+3)`. -/
private noncomputable def Sser (ζ : ℂ) : ℂ :=
  ∑' k : ℕ, (stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)

private lemma Sser_summable {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    Summable (fun k : ℕ => (stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)) := by
  have hz2 : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg _) hz2).mul_left (‖ζ‖ ^ 3)) fun k => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stripS0Coeff_pos k)]
  have heq : ‖ζ‖ ^ (2 * k + 3) = ‖ζ‖ ^ 3 * (‖ζ‖ ^ 2) ^ k := by ring
  rw [heq]
  exact mul_le_of_le_one_left (by positivity) (stripS0Coeff_le_one k)

private lemma Sser_hasDerivAt {y : ℂ} (hy : ‖y‖ < 1) : HasDerivAt Sser (stripG y) y := by
  set r : ℝ := (‖y‖ + 1) / 2 with hr_def
  have hr0 : 0 < r := by linarith [norm_nonneg y]
  have hr1 : r < 1 := by linarith
  have hyr : ‖y‖ < r := by linarith
  have hr2_lt : r ^ 2 < 1 := by nlinarith
  have hu : Summable (fun k : ℕ => ((2 * k + 3 : ℕ) : ℝ) * r ^ (2 * k + 2)) := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 (r := r ^ 2)
      (by rw [Real.norm_of_nonneg (sq_nonneg r)]; exact hr2_lt)).mul_left (2 * r ^ 2)
    have h2 := (summable_geometric_of_lt_one (sq_nonneg r) hr2_lt).mul_left (3 * r ^ 2)
    refine (h1.add h2).congr fun k => ?_
    push_cast
    rw [show 2 * k + 2 = 2 * k + 2 from rfl, pow_add, pow_mul]
    ring
  have hd := hasDerivAt_tsum_of_isPreconnected (t := ball (0 : ℂ) r)
    (y₀ := 0) (u := fun k : ℕ => ((2 * k + 3 : ℕ) : ℝ) * r ^ (2 * k + 2))
    (g := fun (k : ℕ) (w : ℂ) => (stripS0Coeff k : ℂ) * w ^ (2 * k + 3))
    (g' := fun (k : ℕ) (w : ℂ) =>
      (stripS0Coeff k : ℂ) * (((2 * k + 3 : ℕ) : ℂ) * w ^ (2 * k + 3 - 1)))
    hu isOpen_ball (convex_ball _ _).isPreconnected
    (fun n w _ => (hasDerivAt_pow (2 * n + 3) w).const_mul _)
    (by
      intro n w hw
      have hw' : ‖w‖ < r := mem_ball_zero_iff.mp hw
      have hw2 : ‖w‖ ^ (2 * n + 2) ≤ r ^ (2 * n + 2) :=
        pow_le_pow_left₀ (norm_nonneg _) hw'.le _
      rw [show 2 * n + 3 - 1 = 2 * n + 2 by omega]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (stripS0Coeff_pos n), norm_pow, Complex.norm_natCast]
      calc stripS0Coeff n * (((2 * n + 3 : ℕ) : ℝ) * ‖w‖ ^ (2 * n + 2))
          ≤ 1 * (((2 * n + 3 : ℕ) : ℝ) * r ^ (2 * n + 2)) :=
            mul_le_mul (stripS0Coeff_le_one n) (mul_le_mul_of_nonneg_left hw2 (by positivity))
              (by positivity) zero_le_one
        _ = ((2 * n + 3 : ℕ) : ℝ) * r ^ (2 * n + 2) := one_mul _)
    (mem_ball_zero_iff.mpr (by simpa using hr0))
    (by
      have : (fun n : ℕ => (stripS0Coeff n : ℂ) * (0 : ℂ) ^ (2 * n + 3)) = fun _ => 0 := by
        funext n
        rw [zero_pow (by omega), mul_zero]
      show Summable (fun n : ℕ => (stripS0Coeff n : ℂ) * (0 : ℂ) ^ (2 * n + 3))
      rw [this]
      exact summable_zero)
    (mem_ball_zero_iff.mpr hyr)
  have hval : (∑' k : ℕ, (stripS0Coeff k : ℂ) * (((2 * k + 3 : ℕ) : ℂ) * y ^ (2 * k + 3 - 1))) =
      stripG y := by
    rw [stripG_eq_tsum hy]
    congr 1
    funext k
    rw [show 2 * k + 3 - 1 = 2 * k + 2 by omega]
    unfold stripS0Coeff
    push_cast
    have hk : (2 * (k : ℂ) + 3) ≠ 0 := by
      intro h
      have : 2 * (k : ℝ) + 3 = 0 := by exact_mod_cast h
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    field_simp
  rw [← hval]
  exact hd

/-- **Lemma T.3(2) (`mat:T3`):** `HasSum` Taylor expansion of `S̃₀ = stripS0Tilde` on `‖ζ‖ < 1`,
`S̃₀(ζ) = ∑_{k≥0} stripS0Coeff k * ζ^{2k+3}` with strictly positive coefficients. -/
theorem stripS0Tilde_hasSum {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasSum (fun k : ℕ => (stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)) (stripS0Tilde ζ) := by
  have heq : stripS0Tilde ζ = Sser ζ := by
    have hdiff : ∀ w ∈ ball (0 : ℂ) 1, HasDerivAt (fun z => stripS0Tilde z - Sser z) 0 w := by
      intro w hw
      have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have hre : |w.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm w) hw'
      simpa using (hasDerivAt_stripS0Tilde hre).fun_sub (Sser_hasDerivAt hw')
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun w hw => (hdiff w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hdiff w hw).deriv)
      (mem_ball_zero_iff.mpr hζ) (mem_ball_self zero_lt_one)
    have h0 : stripS0Tilde 0 - Sser 0 = 0 := by
      simp [stripS0Tilde, Sser]
    exact sub_eq_zero.mp (hconst.trans h0)
  rw [heq]
  exact (Sser_summable hζ).hasSum

/-- **Lemma T.3(2) (`mat:T3`):** power series identity for `S̃₀ = stripS0Tilde` on `‖ζ‖ < 1`. -/
theorem stripS0Tilde_eq_tsum {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    stripS0Tilde ζ = ∑' k : ℕ, (stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3) :=
  (stripS0Tilde_hasSum hζ).tsum_eq.symm

/-- For real `r ∈ [0, 1)`, `stripS0Tilde (r : ℂ)` has real series
`∑' k, stripS0Coeff k * r ^ (2 * k + 3)`. -/
lemma stripS0Tilde_ofReal_hasSum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => stripS0Coeff k * r ^ (2 * k + 3)) (stripS0Tilde (r : ℂ)).re := by
  have hnorm : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hC := stripS0Tilde_hasSum hnorm
  have hcast : (fun k : ℕ => (stripS0Coeff k : ℂ) * (r : ℂ) ^ (2 * k + 3)) =
      fun k : ℕ => ((stripS0Coeff k * r ^ (2 * k + 3) : ℝ) : ℂ) := by
    funext k; push_cast; rfl
  rw [hcast] at hC
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum hC

lemma stripS0Tilde_ofReal_im {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (stripS0Tilde (r : ℂ)).im = 0 := by
  have hnorm : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hC := stripS0Tilde_hasSum hnorm
  have hcast : (fun k : ℕ => (stripS0Coeff k : ℂ) * (r : ℂ) ^ (2 * k + 3)) =
      fun k : ℕ => ((stripS0Coeff k * r ^ (2 * k + 3) : ℝ) : ℂ) := by
    funext k; push_cast; rfl
  rw [hcast] at hC
  have him : HasSum (fun _ : ℕ => (0 : ℝ)) (stripS0Tilde (r : ℂ)).im := by
    simpa only [Complex.imCLM_apply, Complex.ofReal_im] using Complex.imCLM.hasSum hC
  exact him.unique hasSum_zero

/-- **Lemma T.3(2) (`mat:T3`):** `‖S̃₀(ζ)‖ ≤ Re S̃₀(‖ζ‖)` for all `‖ζ‖ < 1`. -/
theorem norm_stripS0Tilde_le {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ‖stripS0Tilde ζ‖ ≤ (stripS0Tilde (‖ζ‖ : ℂ)).re := by
  have hR := stripS0Tilde_ofReal_hasSum (norm_nonneg ζ) hζ
  rw [stripS0Tilde_eq_tsum hζ, ← hR.tsum_eq]
  have hnorm_eq : (fun k : ℕ => ‖(stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)‖) =
      fun k : ℕ => stripS0Coeff k * ‖ζ‖ ^ (2 * k + 3) := by
    funext k
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stripS0Coeff_pos k)]
  have hsn : Summable (fun k : ℕ => ‖(stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)‖) := by
    rw [hnorm_eq]; exact hR.summable
  calc ‖∑' k : ℕ, (stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)‖
      ≤ ∑' k : ℕ, ‖(stripS0Coeff k : ℂ) * ζ ^ (2 * k + 3)‖ := norm_tsum_le_tsum_norm hsn
    _ = ∑' k : ℕ, stripS0Coeff k * ‖ζ‖ ^ (2 * k + 3) := by rw [hnorm_eq]

/-- **Lemma T.3(2) (`mat:T3`):** monotonicity of `S̃₀(r) / r³` gives
`‖S̃₀(ζ)‖ ≤ (Re S̃₀(R) / R³) ‖ζ‖³` for `‖ζ‖ ≤ R < 1`. -/
theorem norm_stripS0Tilde_le_mul_cube {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ R) :
    ‖stripS0Tilde ζ‖ ≤ ((stripS0Tilde (R : ℂ)).re / R ^ 3) * ‖ζ‖ ^ 3 := by
  have hζ1 : ‖ζ‖ < 1 := hζ.trans_lt hR1
  have h1 := norm_stripS0Tilde_le hζ1
  have hr_sum := stripS0Tilde_ofReal_hasSum (norm_nonneg ζ) hζ1
  have hR_sum := stripS0Tilde_ofReal_hasSum hR0.le hR1
  have hdivR : HasSum (fun k : ℕ => stripS0Coeff k * R ^ (2 * k))
      ((stripS0Tilde (R : ℂ)).re / R ^ 3) := by
    have h := hR_sum.div_const (R ^ 3)
    refine h.congr_fun fun k => ?_
    have hpow : R ^ (2 * k + 3) = R ^ (2 * k) * R ^ 3 := by ring
    rw [hpow, mul_div_assoc, mul_div_cancel_right₀ _ (pow_ne_zero 3 hR0.ne')]
  have hmul : HasSum (fun k : ℕ => stripS0Coeff k * R ^ (2 * k) * ‖ζ‖ ^ 3)
      (((stripS0Tilde (R : ℂ)).re / R ^ 3) * ‖ζ‖ ^ 3) :=
    hdivR.mul_right (‖ζ‖ ^ 3)
  refine h1.trans ?_
  rw [← hr_sum.tsum_eq, ← hmul.tsum_eq]
  refine hr_sum.summable.tsum_le_tsum (fun k => ?_) hmul.summable
  have hpow : ‖ζ‖ ^ (2 * k + 3) = ‖ζ‖ ^ (2 * k) * ‖ζ‖ ^ 3 := by ring
  rw [hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg ζ) hζ _) (stripS0Coeff_pos k).le)
    (pow_nonneg (norm_nonneg ζ) 3)

/-- The radius `r₀ = 2^{2/3} / √3` appearing in equation `(e35)` (`mat:T3`(2)). -/
noncomputable def e35Radius : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) / Real.sqrt 3

lemma e35Radius_pos : 0 < e35Radius := by
  unfold e35Radius; positivity

/-- `r₀ = 2^{2/3} / √3 < 0.9165` (`mat:T3`(2)). -/
theorem e35Radius_lt : e35Radius < 9165 / 10000 := by
  have hpos : 0 < e35Radius := e35Radius_pos
  have hpow : e35Radius ^ 6 = 16 / 27 := by
    unfold e35Radius
    rw [div_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 6,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : (2 / 3 : ℝ) * (6 : ℕ) = (4 : ℕ) := by norm_num
    rw [h2, Real.rpow_natCast]
    have h3 : Real.sqrt 3 ^ 6 = (Real.sqrt 3 ^ 2) ^ 3 := by ring
    rw [h3, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h6 : e35Radius ^ 6 < (9165 / 10000 : ℝ) ^ 6 := by
    rw [hpow]; norm_num
  by_contra h
  push Not at h
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9165 / 10000) h 6
  linarith

lemma e35Radius_lt_one : e35Radius < 1 := e35Radius_lt.trans (by norm_num)

/-- **Lemma T.3(2) (`mat:T3`, equation `(e35)`):** rigorous numerical enclosure
`2 Re S̃₀(2^{2/3} / √3) < 1.1`, obtained from the positive Taylor series by splitting off
`k = 0, 1` and bounding the `k ≥ 2` tail by `(1 / 21) r⁷ / (1 - r²)` at `r = 0.9165`. -/
theorem two_mul_stripS0Tilde_e35Radius_lt :
    2 * (stripS0Tilde (e35Radius : ℂ)).re < 11 / 10 := by
  set r : ℝ := 9165 / 10000 with hr_def
  have hr0 : 0 < r := by norm_num [hr_def]
  have hr1 : r < 1 := by norm_num [hr_def]
  have hr2 : r ^ 2 < 1 := by norm_num [hr_def]
  have hle : e35Radius ≤ r := e35Radius_lt.le
  have hsum := stripS0Tilde_ofReal_hasSum e35Radius_pos.le e35Radius_lt_one
  rw [← hsum.tsum_eq]
  -- Split off `k = 0` and `k = 1`, then bound `k ≥ 2` geometrically
  have hsplit : ∑' k : ℕ, stripS0Coeff k * e35Radius ^ (2 * k + 3) =
      stripS0Coeff 0 * e35Radius ^ 3 + stripS0Coeff 1 * e35Radius ^ 5 +
        ∑' j : ℕ, stripS0Coeff (j + 2) * e35Radius ^ (2 * (j + 2) + 3) := by
    have h1 := hsum.summable.sum_add_tsum_nat_add 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1
    norm_num at h1
    linarith
  have ht0 : stripS0Coeff 0 * e35Radius ^ 3 ≤ (1 / 3) * r ^ 3 := by
    have hc : stripS0Coeff 0 ≤ 1 / 3 := by
      simpa using stripS0Coeff_le_inv 0
    exact mul_le_mul hc (pow_le_pow_left₀ e35Radius_pos.le hle 3)
      (pow_nonneg e35Radius_pos.le 3) (by norm_num)
  have ht1 : stripS0Coeff 1 * e35Radius ^ 5 ≤ (1 / 10) * r ^ 5 := by
    have hc : stripS0Coeff 1 ≤ 1 / 10 := by
      have := stripS0Coeff_le_inv 1
      norm_num at this
      exact this
    exact mul_le_mul hc (pow_le_pow_left₀ e35Radius_pos.le hle 5)
      (pow_nonneg e35Radius_pos.le 5) (by norm_num)
  have htail_le : ∑' j : ℕ, stripS0Coeff (j + 2) * e35Radius ^ (2 * (j + 2) + 3) ≤
      (1 / 21) * r ^ 7 * (1 - r ^ 2)⁻¹ := by
    have hgeo : Summable (fun j : ℕ => ((1 / 21 : ℝ) * r ^ 7) * (r ^ 2) ^ j) :=
      (summable_geometric_of_lt_one (sq_nonneg r) hr2).mul_left _
    have hsub_sum : Summable (fun j : ℕ => stripS0Coeff (j + 2) * e35Radius ^ (2 * (j + 2) + 3)) :=
      (summable_nat_add_iff 2).mpr hsum.summable
    have hterm : ∀ j : ℕ,
        stripS0Coeff (j + 2) * e35Radius ^ (2 * (j + 2) + 3) ≤
          ((1 / 21 : ℝ) * r ^ 7) * (r ^ 2) ^ j := by
      intro j
      have hc : stripS0Coeff (j + 2) ≤ 1 / 21 := by
        refine (stripS0Coeff_le_inv (j + 2)).trans ?_
        rw [one_div_le_one_div (by positivity) (by norm_num)]
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        push_cast
        nlinarith
      have hp : e35Radius ^ (2 * (j + 2) + 3) ≤ r ^ 7 * (r ^ 2) ^ j := by
        calc e35Radius ^ (2 * (j + 2) + 3)
            ≤ r ^ (2 * (j + 2) + 3) := pow_le_pow_left₀ e35Radius_pos.le hle _
          _ = r ^ 7 * (r ^ 2) ^ j := by
            rw [show 2 * (j + 2) + 3 = 7 + 2 * j by omega, pow_add, pow_mul]
      calc stripS0Coeff (j + 2) * e35Radius ^ (2 * (j + 2) + 3)
          ≤ (1 / 21) * (r ^ 7 * (r ^ 2) ^ j) :=
            mul_le_mul hc hp (pow_nonneg e35Radius_pos.le _) (by norm_num)
        _ = ((1 / 21 : ℝ) * r ^ 7) * (r ^ 2) ^ j := by ring
    calc ∑' j : ℕ, stripS0Coeff (j + 2) * e35Radius ^ (2 * (j + 2) + 3)
        ≤ ∑' j : ℕ, ((1 / 21 : ℝ) * r ^ 7) * (r ^ 2) ^ j :=
          hsub_sum.tsum_le_tsum hterm hgeo
      _ = (1 / 21) * r ^ 7 * (1 - r ^ 2)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg r) hr2]
  rw [hsplit]
  have hnum : 2 * ((1 / 3) * r ^ 3 + (1 / 10) * r ^ 5 + (1 / 21) * r ^ 7 * (1 - r ^ 2)⁻¹) <
      11 / 10 := by
    rw [hr_def]; norm_num
  linarith

/-- **Lemma T.3(2) (`mat:T3`, equation `(e35)`):** pointwise uniform bound for `c ≥ 2` and
`‖w‖ ≤ 2 / √3` with `ε = c^{-1/3}`:
`‖c S̃₀(ε w)‖ ≤ 2 Re S̃₀(2^{2/3} / √3)`. -/
theorem norm_c_mul_stripS0Tilde_le {c : ℝ} (hc : 2 ≤ c) {w : ℂ} (hw : ‖w‖ ≤ 2 / Real.sqrt 3) :
    ‖(c : ℂ) * stripS0Tilde (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * w)‖ ≤
      2 * (stripS0Tilde (e35Radius : ℂ)).re := by
  have hc0 : 0 < c := by linarith
  set ε : ℝ := c ^ (-(1 / 3 : ℝ)) with hε_def
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hc0 _
  have hε_le : ε ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [hε_def, Real.rpow_neg hc0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hc (by norm_num))
  have hεw_norm : ‖((ε : ℂ) * w)‖ = ε * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
  have h2pow : (2 : ℝ) ^ (-(1 / 3 : ℝ)) * (2 / Real.sqrt 3) = e35Radius := by
    unfold e35Radius
    rw [mul_div_assoc', ← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hζ_le : ‖((ε : ℂ) * w)‖ ≤ e35Radius := by
    rw [hεw_norm, ← h2pow]
    exact mul_le_mul hε_le hw (norm_nonneg w) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcube := norm_stripS0Tilde_le_mul_cube e35Radius_pos e35Radius_lt_one hζ_le
  have hcε3 : c * ε ^ 3 = 1 := by
    rw [hε_def, ← Real.rpow_natCast (c ^ (-(1 / 3 : ℝ))) 3, ← Real.rpow_mul hc0.le]
    have : -(1 / 3 : ℝ) * (3 : ℕ) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    exact mul_inv_cancel₀ hc0.ne'
  have hr0_cube : 2 * e35Radius ^ 3 = (2 / Real.sqrt 3) ^ 3 := by
    unfold e35Radius
    rw [div_pow, div_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have : (2 / 3 : ℝ) * (3 : ℕ) = (2 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]
    ring
  have hS0_nonneg : 0 ≤ (stripS0Tilde (e35Radius : ℂ)).re := by
    have hnorm : ‖(e35Radius : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos e35Radius_pos]
      exact e35Radius_lt_one
    have hle := (norm_nonneg (stripS0Tilde (e35Radius : ℂ))).trans (norm_stripS0Tilde_le hnorm)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos e35Radius_pos] at hle
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  calc c * ‖stripS0Tilde ((ε : ℂ) * w)‖
      ≤ c * (((stripS0Tilde (e35Radius : ℂ)).re / e35Radius ^ 3) * ‖((ε : ℂ) * w)‖ ^ 3) :=
        mul_le_mul_of_nonneg_left hcube hc0.le
    _ = ((stripS0Tilde (e35Radius : ℂ)).re / e35Radius ^ 3) * ((c * ε ^ 3) * ‖w‖ ^ 3) := by
        rw [hεw_norm]; ring
    _ = ((stripS0Tilde (e35Radius : ℂ)).re / e35Radius ^ 3) * ‖w‖ ^ 3 := by rw [hcε3, one_mul]
    _ ≤ ((stripS0Tilde (e35Radius : ℂ)).re / e35Radius ^ 3) * (2 / Real.sqrt 3) ^ 3 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg w) hw 3)
          (div_nonneg hS0_nonneg (pow_nonneg e35Radius_pos.le 3))
    _ = 2 * (stripS0Tilde (e35Radius : ℂ)).re := by
        rw [← hr0_cube]; field_simp [e35Radius_pos.ne']

/-- **Lemma T.3(2) (`mat:T3`, equation `(e35)`):** supremum form
`sup_{c ≥ 2, |w| ≤ 2/√3} |c S̃₀(c^{-1/3} w)| ≤ 2 Re S̃₀(2^{2/3} / √3) < 1.1`. -/
theorem sSup_c_mul_stripS0Tilde_le :
    sSup {x : ℝ | ∃ (c : ℝ) (w : ℂ), 2 ≤ c ∧ ‖w‖ ≤ 2 / Real.sqrt 3 ∧
        x = ‖(c : ℂ) * stripS0Tilde (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * w)‖} ≤
      2 * (stripS0Tilde (e35Radius : ℂ)).re ∧
    2 * (stripS0Tilde (e35Radius : ℂ)).re < 11 / 10 := by
  refine ⟨csSup_le ?_ ?_, two_mul_stripS0Tilde_e35Radius_lt⟩
  · exact ⟨0, 2, 0, le_rfl, by simp; positivity, by simp [stripS0Tilde]⟩
  · rintro x ⟨c, w, hc, hw, rfl⟩
    exact norm_c_mul_stripS0Tilde_le hc hw

/-! ### Axiom checks -/

/-- info: 'FormalResearch.CohnElkies.stripGCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripGCoeff_zero

/-- info: 'FormalResearch.CohnElkies.stripGCoeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripGCoeff_pos

/-- info: 'FormalResearch.CohnElkies.stripG_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripG_hasSum

/-- info: 'FormalResearch.CohnElkies.stripG_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripG_eq_tsum

/-- info: 'FormalResearch.CohnElkies.stripGReal_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripGReal_bijOn

/-- info: 'FormalResearch.CohnElkies.stripGReal_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripGReal_deriv_bounds

/-- info: 'FormalResearch.CohnElkies.norm_stripG_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stripG_le

/-- info: 'FormalResearch.CohnElkies.norm_log_tan_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_log_tan_div_le

/-- info: 'FormalResearch.CohnElkies.stripS0Tilde_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripS0Tilde_hasSum

/-- info: 'FormalResearch.CohnElkies.norm_stripS0Tilde_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stripS0Tilde_le

/-- info: 'FormalResearch.CohnElkies.norm_stripS0Tilde_le_mul_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stripS0Tilde_le_mul_cube

/-- info: 'FormalResearch.CohnElkies.two_mul_stripS0Tilde_e35Radius_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_stripS0Tilde_e35Radius_lt

/-- info: 'FormalResearch.CohnElkies.norm_c_mul_stripS0Tilde_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_c_mul_stripS0Tilde_le

/-- info: 'FormalResearch.CohnElkies.sSup_c_mul_stripS0Tilde_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sSup_c_mul_stripS0Tilde_le

end FormalResearch.CohnElkies
