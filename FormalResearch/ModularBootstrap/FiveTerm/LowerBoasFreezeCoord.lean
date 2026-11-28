module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasGrowth
public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.ModularBootstrap.FiveTerm.LowerChartMain

/-!
# Smooth `C^2` bounds for `x(ζ)`, `P(ζ)`, and the taper on `[ζ_min/2, ∞)` (`ctl:freeze`)

Establishes the globally `C^1` and piecewise-`C^2` regularity and relative derivative bounds
`|P^(j)(ζ)| / P(ζ) ≤ C ζ^{-j}` (`j = 1, 2`) on `ζ ≥ ζ_min c' / 2`, together with local
comparability on Gaussian windows `|z - ζ| ≤ 8 log c' + 1`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.Bessel

noncomputable section

/-! ### 1. Real coordinate `x(ζ) = Re b(ζ)` and `ρ_U` derivative ratios -/

/-- Real slit coordinate `x(ζ) = Re bOfZeta c' (ζ : ℂ) > ξ_*` for `ζ > 0`. -/
def xOfZeta (c' ζ : ℝ) : ℝ := (bOfZeta c' (ζ : ℂ)).re

/-- Second derivative of `rhoU`: `ρ_U''(x) = -(8π/3) sinh(πx) / (sinh(πx)^2 - 1)^{3/2}`. -/
def rhoUDeriv2 (x : ℝ) : ℝ :=
  -(8 * π / 3) * Real.sinh (π * x) / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ)

private lemma sinh_pi_gt_one {x : ℝ} (hx : xiStar < x) : 1 < Real.sinh (π * x) := by
  rw [← sinh_pi_mul_xiStar]
  exact Real.sinh_lt_sinh.mpr (mul_lt_mul_of_pos_left hx Real.pi_pos)

lemma rhoU_ge_linear_of_ge {x : ℝ} (hx : xiStar ≤ x) :
    (4 / 3 : ℝ) * (x - xiStar) ≤ rhoU x := by
  rcases hx.eq_or_lt with rfl | hx_lt
  · simp [rhoU_xiStar]
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope rhoU rhoUDeriv hx_lt
    (continuousOn_rhoU.mono Icc_subset_Ici_self)
    (fun u hu => hasDerivAt_rhoU hu.1)
  have hρ := rhoUDeriv_ge hξ.1
  rw [rhoU_xiStar, sub_zero, eq_div_iff (sub_pos.mpr hx_lt).ne'] at hslope
  nlinarith only [hslope, hρ, sub_pos.mpr hx_lt]

lemma hasDerivAt_rhoUDeriv {x : ℝ} (hx : xiStar < x) :
    HasDerivAt rhoUDeriv (rhoUDeriv2 x) x := by
  have hs1 : 1 < Real.sinh (π * x) := sinh_pi_gt_one hx
  have hpi := Real.pi_pos
  have hs2_pos : 0 < Real.sinh (π * x) ^ 2 - 1 := by nlinarith
  have hnum : HasDerivAt (fun t => Real.cosh (π * t)) (π * Real.sinh (π * x)) x := by
    have h1 := (Real.hasDerivAt_cosh (π * x)).comp x (by simpa using (hasDerivAt_id x).const_mul π)
    exact h1.congr_deriv (by ring)
  have hinner : HasDerivAt (fun t => Real.sinh (π * t) ^ 2 - 1)
      (2 * π * Real.sinh (π * x) * Real.cosh (π * x)) x := by
    have h1 := (Real.hasDerivAt_sinh (π * x)).comp x (by simpa using (hasDerivAt_id x).const_mul π)
    have h2 := ((h1.pow 2).sub_const 1)
    exact h2.congr_deriv (by simp; ring)
  have hden : HasDerivAt (fun t => (Real.sinh (π * t) ^ 2 - 1) ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * (Real.sinh (π * x) ^ 2 - 1) ^ (-(3 / 2 : ℝ)) *
        (2 * π * Real.sinh (π * x) * Real.cosh (π * x))) x := by
    have hp := (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hs2_pos.ne')).comp x hinner
    refine hp.congr_deriv ?_
    rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
  have hprod : HasDerivAt (fun t => (4 / 3 : ℝ) * (Real.cosh (π * t) * (Real.sinh (π * t) ^ 2 - 1) ^ (-(1 / 2 : ℝ))))
      ((4 / 3 : ℝ) * (π * Real.sinh (π * x) * (Real.sinh (π * x) ^ 2 - 1) ^ (-(1 / 2 : ℝ)) +
        Real.cosh (π * x) * (-(1 / 2 : ℝ) * (Real.sinh (π * x) ^ 2 - 1) ^ (-(3 / 2 : ℝ)) *
          (2 * π * Real.sinh (π * x) * Real.cosh (π * x))))) x :=
    (hnum.mul hden).const_mul (4 / 3 : ℝ)
  have hev : rhoUDeriv =ᶠ[𝓝 x] fun t =>
      (4 / 3 : ℝ) * (Real.cosh (π * t) * (Real.sinh (π * t) ^ 2 - 1) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht_pos : 0 < Real.sinh (π * t) ^ 2 - 1 := by
      have := sinh_pi_gt_one ht; nlinarith
    unfold rhoUDeriv
    rw [Real.rpow_neg ht_pos.le, ← Real.sqrt_eq_rpow]
    ring
  refine (hprod.congr_of_eventuallyEq hev).congr_deriv ?_
  unfold rhoUDeriv2
  have h12 : (Real.sinh (π * x) ^ 2 - 1) ^ (-(1 / 2 : ℝ)) =
      (Real.sinh (π * x) ^ 2 - 1) / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) := by
    have hpow : (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) =
        (Real.sinh (π * x) ^ 2 - 1) * (Real.sinh (π * x) ^ 2 - 1) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs2_pos, Real.rpow_one]
    rw [Real.rpow_neg hs2_pos.le, hpow, inv_eq_one_div,
      div_eq_div_iff (Real.rpow_pos_of_pos hs2_pos _).ne' (mul_pos hs2_pos (Real.rpow_pos_of_pos hs2_pos _)).ne']
    ring
  have h32 : (Real.sinh (π * x) ^ 2 - 1) ^ (-(3 / 2 : ℝ)) =
      ((Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ))⁻¹ :=
    Real.rpow_neg hs2_pos.le (3 / 2)
  rw [h12, h32]
  have hch : Real.cosh (π * x) ^ 2 = Real.sinh (π * x) ^ 2 + 1 := by
    linarith [Real.cosh_sq_sub_sinh_sq (π * x)]
  have hdn : (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hs2_pos _).ne'
  field_simp [hdn]
  nlinarith only [hch]

lemma rhoU_deriv_ratio_bounds :
    ∃ C_ρ : ℝ, 0 < C_ρ ∧ ∀ {x : ℝ}, xiStar < x →
      rhoUDeriv x * (x - xiStar) ≤ C_ρ * rhoU x ∧
      |rhoUDeriv2 x| * (x - xiStar) ^ 2 ≤ C_ρ * rhoU x := by
  let M_ch : ℝ := Real.cosh (π * (xiStar + 1))
  let M_sh : ℝ := Real.sinh (π * (xiStar + 1))
  let C_tip1 : ℝ := (4 / 3) * M_ch / (Real.sqrt (2 * Real.sqrt 2 * π) * (3 * kTip))
  let C_tip2 : ℝ := (8 * π / 3) * M_sh / ((2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ) * (3 * kTip))
  let C_ρ : ℝ := max (max C_tip1 C_tip2) 20 + 1
  have hCρ_pos : 0 < C_ρ := by positivity
  refine ⟨C_ρ, hCρ_pos, fun {x} hx => ?_⟩
  have hr_pos : 0 < x - xiStar := sub_pos.mpr hx
  have hρ_pos : 0 < rhoU x := rhoU_pos hx
  have hs1 : 1 < Real.sinh (π * x) := sinh_pi_gt_one hx
  have hpi := Real.pi_pos
  rcases le_or_gt x (xiStar + 1) with hx1 | hx1
  · have hsq_lb : 3 * kTip * Real.sqrt (x - xiStar) ≤ rhoU x := by
      have h1 := (rhoU_sq_bounds hr_pos.le).1
      rw [show xiStar + (x - xiStar) = x by ring] at h1
      have h2 : (3 * kTip * Real.sqrt (x - xiStar)) ^ 2 = 9 * kTip ^ 2 * (x - xiStar) := by
        rw [mul_pow, Real.sq_sqrt hr_pos.le]; ring
      rw [← h2] at h1
      nlinarith [hρ_pos, Real.sqrt_nonneg (x - xiStar), kTip_pos]
    have hsh_lb : Real.sqrt 2 * π * (x - xiStar) ≤ Real.sinh (π * x) - 1 := by
      have hmvt := exists_hasDerivAt_eq_slope (fun t => Real.sinh (π * t)) (fun t => π * Real.cosh (π * t)) hx
        (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn
        (fun t _ => ((Real.hasDerivAt_sinh (π * t)).comp t
          (by simpa using (hasDerivAt_id t).const_mul π)).congr_deriv (by ring))
      obtain ⟨ξ, hξ, hslope⟩ := hmvt
      rw [sinh_pi_mul_xiStar] at hslope
      have hch_ge : Real.sqrt 2 ≤ Real.cosh (π * ξ) := by
        have hch_xi : Real.cosh (π * xiStar) = Real.sqrt 2 := by
          have h := Real.cosh_sq_sub_sinh_sq (π * xiStar)
          rw [sinh_pi_mul_xiStar, one_pow] at h
          have hp := Real.cosh_pos (π * xiStar)
          rw [← Real.sqrt_sq hp.le]
          congr 1; linarith
        rw [← hch_xi]
        exact Real.cosh_le_cosh.mpr (by
          rw [abs_of_pos (mul_pos hpi xiStar_pos), abs_of_pos (mul_pos hpi (xiStar_pos.trans hξ.1))]
          exact mul_le_mul_of_nonneg_left hξ.1.le hpi.le)
      have hpi_ch : π * Real.sqrt 2 ≤ π * Real.cosh (π * ξ) := by gcongr
      rw [eq_div_iff hr_pos.ne'] at hslope
      nlinarith only [hslope, hpi_ch, hr_pos]
    have hs2_lb : 2 * Real.sqrt 2 * π * (x - xiStar) ≤ Real.sinh (π * x) ^ 2 - 1 := by
      have hfac : Real.sinh (π * x) ^ 2 - 1 = (Real.sinh (π * x) - 1) * (Real.sinh (π * x) + 1) := by ring
      have h2 : 2 ≤ Real.sinh (π * x) + 1 := by linarith
      nlinarith only [hfac, hsh_lb, h2, hr_pos, hpi, Real.sqrt_pos.mpr zero_lt_two]
    have hch_ub : Real.cosh (π * x) ≤ M_ch := by
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_of_pos (mul_pos hpi (xiStar_pos.trans hx)), abs_of_pos (by positivity [xiStar_pos])]
      gcongr
    have hsh_ub : Real.sinh (π * x) ≤ M_sh :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hx1 hpi.le)
    have h1 : rhoUDeriv x * (x - xiStar) ≤ C_ρ * rhoU x := by
      have hden_lb : Real.sqrt (2 * Real.sqrt 2 * π) * Real.sqrt (x - xiStar) ≤
          Real.sqrt (Real.sinh (π * x) ^ 2 - 1) := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt hs2_lb
      have hden_pos : 0 < Real.sqrt (2 * Real.sqrt 2 * π) * Real.sqrt (x - xiStar) := by positivity
      have hquot : Real.cosh (π * x) / Real.sqrt (Real.sinh (π * x) ^ 2 - 1) ≤
          M_ch / (Real.sqrt (2 * Real.sqrt 2 * π) * Real.sqrt (x - xiStar)) := by
        calc Real.cosh (π * x) / Real.sqrt (Real.sinh (π * x) ^ 2 - 1)
            ≤ M_ch / Real.sqrt (Real.sinh (π * x) ^ 2 - 1) := by gcongr
          _ ≤ M_ch / (Real.sqrt (2 * Real.sqrt 2 * π) * Real.sqrt (x - xiStar)) := by
              have : 0 ≤ M_ch := (Real.cosh_pos _).le
              gcongr
      have hdiv_sq : (x - xiStar) / Real.sqrt (x - xiStar) = Real.sqrt (x - xiStar) := Real.div_sqrt
      unfold rhoUDeriv
      calc (4 / 3 : ℝ) * (Real.cosh (π * x) / Real.sqrt (Real.sinh (π * x) ^ 2 - 1)) * (x - xiStar)
          ≤ (4 / 3) * (M_ch / (Real.sqrt (2 * Real.sqrt 2 * π) * Real.sqrt (x - xiStar))) *
              (x - xiStar) := by gcongr
        _ = (4 / 3) * M_ch / Real.sqrt (2 * Real.sqrt 2 * π) * ((x - xiStar) / Real.sqrt (x - xiStar)) := by ring
        _ = (4 / 3) * M_ch / Real.sqrt (2 * Real.sqrt 2 * π) * Real.sqrt (x - xiStar) := by rw [hdiv_sq]
        _ = C_tip1 * (3 * kTip * Real.sqrt (x - xiStar)) := by
            dsimp [C_tip1]; field_simp [kTip_pos.ne']
        _ ≤ C_ρ * rhoU x := by
            apply mul_le_mul _ hsq_lb (by positivity [kTip_pos]) hCρ_pos.le
            exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_add_of_nonneg_right zero_le_one)
    have h2 : |rhoUDeriv2 x| * (x - xiStar) ^ 2 ≤ C_ρ * rhoU x := by
      have hs2_pos : 0 < Real.sinh (π * x) ^ 2 - 1 := by nlinarith
      have hden_lb : (2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (3 / 2 : ℝ) ≤
          (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) := by
        rw [← Real.mul_rpow (by positivity) hr_pos.le]
        exact Real.rpow_le_rpow (by positivity) hs2_lb (by positivity)
      have hden_pos : 0 < (2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (3 / 2 : ℝ) := by positivity
      have hpow_eq : (x - xiStar) ^ 2 / (x - xiStar) ^ (3 / 2 : ℝ) = Real.sqrt (x - xiStar) := by
        rw [div_eq_iff (Real.rpow_pos_of_pos hr_pos _).ne', Real.sqrt_eq_rpow,
          ← Real.rpow_natCast (x - xiStar) 2, ← Real.rpow_add hr_pos]
        norm_num
      have hquot : (8 * π / 3) * Real.sinh (π * x) / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) ≤
          (8 * π / 3) * M_sh / ((2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (3 / 2 : ℝ)) := by
        calc (8 * π / 3) * Real.sinh (π * x) / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ)
            ≤ (8 * π / 3) * M_sh / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) := by gcongr
          _ ≤ (8 * π / 3) * M_sh / ((2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (3 / 2 : ℝ)) := by
              have hMsh_nn : 0 ≤ M_sh := (Real.sinh_pos_iff.mpr (by positivity [xiStar_pos])).le
              have : 0 ≤ (8 * π / 3) * M_sh := mul_nonneg (by positivity) hMsh_nn
              gcongr
      unfold rhoUDeriv2
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hs2_pos _), abs_mul, abs_neg,
        abs_of_pos (by positivity), abs_of_pos (by linarith)]
      calc (8 * π / 3) * Real.sinh (π * x) / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) *
              (x - xiStar) ^ 2
          ≤ (8 * π / 3) * M_sh / ((2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (3 / 2 : ℝ)) *
              (x - xiStar) ^ 2 := mul_le_mul_of_nonneg_right hquot (sq_nonneg _)
        _ = ((8 * π / 3) * M_sh / (2 * Real.sqrt 2 * π) ^ (3 / 2 : ℝ)) *
              ((x - xiStar) ^ 2 / (x - xiStar) ^ (3 / 2 : ℝ)) := by ring
        _ = C_tip2 * (3 * kTip * Real.sqrt (x - xiStar)) := by
            rw [hpow_eq]; dsimp [C_tip2]; field_simp [kTip_pos.ne']
        _ ≤ C_ρ * rhoU x := by
            apply mul_le_mul _ hsq_lb (by positivity [kTip_pos]) hCρ_pos.le
            exact ((le_max_right _ _).trans (le_max_left _ _)).trans (le_add_of_nonneg_right zero_le_one)
    exact ⟨h1, h2⟩
  · have hρ_lin : (4 / 3 : ℝ) * (x - xiStar) ≤ rhoU x := rhoU_ge_linear_of_ge hx.le
    have hρ_43 : (4 / 3 : ℝ) ≤ rhoU x := by nlinarith
    have hpix3 : 3 ≤ π * x := by
      have := Real.pi_gt_three; nlinarith [xiStar_pos]
    have hex_ge : 19 ≤ Real.exp (π * x) := by
      have he3 : (19 : ℝ) ≤ Real.exp 1 ^ 3 := by
        have := Real.exp_one_gt_d9
        have h27 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
        linarith only [h27, (by norm_num : (19 : ℝ) ≤ (2.7 : ℝ) ^ 3)]
      rw [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] at he3
      exact he3.trans (Real.exp_le_exp.mpr (by linarith only [hpix3]))
    have hsh_eq : Real.sinh (π * x) = (Real.exp (π * x) - Real.exp (-(π * x))) / 2 :=
      Real.sinh_eq (π * x)
    have hexm : Real.exp (-(π * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hsh_ge2 : 2 ≤ Real.sinh (π * x) := by rw [hsh_eq]; linarith
    have hs2_ge : (3 / 4 : ℝ) * Real.sinh (π * x) ^ 2 ≤ Real.sinh (π * x) ^ 2 - 1 := by
      nlinarith only [hsh_ge2]
    have hch_le : Real.cosh (π * x) ^ 2 ≤ (5 / 4 : ℝ) * Real.sinh (π * x) ^ 2 := by
      have hch := Real.cosh_sq_sub_sinh_sq (π * x)
      nlinarith only [hch, hsh_ge2]
    have h1 : rhoUDeriv x * (x - xiStar) ≤ C_ρ * rhoU x := by
      have hquot_sq : (Real.cosh (π * x) / Real.sqrt (Real.sinh (π * x) ^ 2 - 1)) ^ 2 ≤ 5 / 3 := by
        have hs2_pos : 0 < Real.sinh (π * x) ^ 2 - 1 := by nlinarith
        rw [div_pow, Real.sq_sqrt hs2_pos.le, div_le_iff₀ hs2_pos]
        nlinarith only [hs2_ge, hch_le]
      have hquot : Real.cosh (π * x) / Real.sqrt (Real.sinh (π * x) ^ 2 - 1) ≤ 2 := by
        have hpos : 0 ≤ Real.cosh (π * x) / Real.sqrt (Real.sinh (π * x) ^ 2 - 1) := by positivity
        nlinarith only [hquot_sq, hpos]
      have hd_le : rhoUDeriv x ≤ 8 / 3 := by unfold rhoUDeriv; linarith
      have hC_ge2 : 2 ≤ C_ρ := ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)).trans' (by norm_num)
      calc rhoUDeriv x * (x - xiStar) ≤ (8 / 3) * (x - xiStar) := by gcongr
        _ = 2 * ((4 / 3) * (x - xiStar)) := by ring
        _ ≤ C_ρ * rhoU x := by
            refine mul_le_mul hC_ge2 hρ_lin (by positivity) hCρ_pos.le
    have h2 : |rhoUDeriv2 x| * (x - xiStar) ^ 2 ≤ C_ρ * rhoU x := by
      have hs2_pos : 0 < Real.sinh (π * x) ^ 2 - 1 := by nlinarith
      have hpow32 : (1 / 2 : ℝ) * Real.sinh (π * x) ^ 3 ≤ (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) := by
        have h1 : (3 / 4 : ℝ) ^ (3 / 2 : ℝ) * Real.sinh (π * x) ^ 3 ≤
            (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) := by
          have hs3 : (Real.sinh (π * x) ^ 2) ^ (3 / 2 : ℝ) = Real.sinh (π * x) ^ 3 := by
            rw [← Real.rpow_natCast (Real.sinh (π * x)) 2, ← Real.rpow_mul (by linarith),
              show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [← hs3, ← Real.mul_rpow (by norm_num) (sq_nonneg _)]
          exact Real.rpow_le_rpow (by positivity) hs2_ge (by positivity)
        have h34 : (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) ^ (3 / 2 : ℝ) := by
          have hsq1 : (1 / 4 : ℝ) ≤ (27 / 64 : ℝ) := by norm_num
          have hsq2 : ((3 / 4 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (27 / 64 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
          have hp : 0 ≤ (3 / 4 : ℝ) ^ (3 / 2 : ℝ) := by positivity
          nlinarith only [hsq1, hsq2, hp]
        have hs3_nn : 0 ≤ Real.sinh (π * x) ^ 3 := by positivity
        nlinarith only [h1, h34, hs3_nn]
      have hsh_ex : Real.exp (π * x) / 3 ≤ Real.sinh (π * x) := by rw [hsh_eq]; linarith
      have hr_exp : π * (x - xiStar) ≤ Real.exp (π * (x - xiStar)) := by
        linarith only [Real.add_one_le_exp (π * (x - xiStar))]
      have hr_sq : π ^ 2 * (x - xiStar) ^ 2 ≤ Real.exp (π * x) ^ 2 := by
        have h1 : (π * (x - xiStar)) ^ 2 ≤ Real.exp (π * (x - xiStar)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hr_exp 2
        have h2 : Real.exp (π * (x - xiStar)) ≤ Real.exp (π * x) :=
          Real.exp_le_exp.mpr (by nlinarith [xiStar_pos])
        have h3 : Real.exp (π * (x - xiStar)) ^ 2 ≤ Real.exp (π * x) ^ 2 :=
          pow_le_pow_left₀ (Real.exp_pos _).le h2 2
        nlinarith only [h1, h3]
      have hsh_sq : (x - xiStar) ^ 2 ≤ (9 / π ^ 2) * Real.sinh (π * x) ^ 2 := by
        have h1 : Real.exp (π * x) ^ 2 ≤ 9 * Real.sinh (π * x) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hsh_ex 2
          nlinarith only [this]
        have h2 : π ^ 2 * (x - xiStar) ^ 2 ≤ 9 * Real.sinh (π * x) ^ 2 := hr_sq.trans h1
        rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hpi 2)]
        linarith only [h2]
      unfold rhoUDeriv2
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hs2_pos _), abs_mul, abs_neg,
        abs_of_pos (by positivity), abs_of_pos (by linarith)]
      calc (8 * π / 3) * Real.sinh (π * x) / (Real.sinh (π * x) ^ 2 - 1) ^ (3 / 2 : ℝ) *
              (x - xiStar) ^ 2
          ≤ (8 * π / 3) * Real.sinh (π * x) / ((1 / 2) * Real.sinh (π * x) ^ 3) *
              ((9 / π ^ 2) * Real.sinh (π * x) ^ 2) := by gcongr
        _ = 48 / π := by
            have hsn : Real.sinh (π * x) ≠ 0 := by linarith
            field_simp [hsn, hpi.ne']; ring
        _ ≤ 16 := by
            rw [div_le_iff₀ hpi]; linarith [Real.pi_gt_three]
        _ ≤ C_ρ * rhoU x := by
            have hC_ge : 12 ≤ C_ρ := ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)).trans' (by norm_num)
            nlinarith only [hC_ge, hρ_43]
    exact ⟨h1, h2⟩

lemma xOfZeta_spec {c' ζ : ℝ} (hc0 : 0 < c') (hζ : 0 < ζ) :
    xiStar < xOfZeta c' ζ ∧ c' * cumulN (xOfZeta c' ζ) = ζ ∧
    bOfZeta c' (ζ : ℂ) = (xOfZeta c' ζ : ℂ) := by
  obtain ⟨him, hre, hcum⟩ := bOfZeta_ofReal hc0 hζ
  exact ⟨hre, hcum, Complex.ext rfl him⟩

lemma hasDerivAt_xOfZeta {c' ζ : ℝ} (hc0 : 0 < c') (hζ : 0 < ζ) :
    HasDerivAt (xOfZeta c') (2 / (c' * rhoU (xOfZeta c' ζ))) ζ := by
  have hmem : (ζ : ℂ) ∈ zetaStrip c' := by
    refine ⟨hζ, ?_⟩
    simp only [Complex.ofReal_im, abs_zero]
    positivity [xiStar_pos]
  have hb_diff := (differentiableOn_bOfZeta hc0).differentiableAt ((isOpen_zetaStrip c').mem_nhds hmem)
  have hx_diff : HasDerivAt (xOfZeta c') (deriv (bOfZeta c') (ζ : ℂ)).re ζ :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt ζ (hb_diff.hasDerivAt.comp_ofReal)
  have hcomp_id : (fun u : ℝ => c' * cumulN (xOfZeta c' u)) =ᶠ[𝓝 ζ] id := by
    filter_upwards [Ioi_mem_nhds hζ] with u hu
    exact (xOfZeta_spec hc0 hu).2.1
  have hx_gt : xiStar < xOfZeta c' ζ := (xOfZeta_spec hc0 hζ).1
  have hcum_deriv := ((hasDerivAt_cumulN hx_gt).const_mul c').comp ζ hx_diff
  have hid : HasDerivAt (fun u : ℝ => c' * cumulN (xOfZeta c' u)) 1 ζ :=
    (hasDerivAt_id ζ).congr_of_eventuallyEq hcomp_id
  have heq : (c' * (rhoU (xOfZeta c' ζ) / 2)) * (deriv (bOfZeta c') (ζ : ℂ)).re = 1 := by
    have := hcum_deriv.unique hid
    simpa [smul_eq_mul] using this
  have hρ_pos : 0 < rhoU (xOfZeta c' ζ) := rhoU_pos hx_gt
  have hval : (deriv (bOfZeta c') (ζ : ℂ)).re = 2 / (c' * rhoU (xOfZeta c' ζ)) := by
    field_simp [hc0.ne', hρ_pos.ne']
    linarith only [heq]
  rwa [hval] at hx_diff

lemma hasDerivAt_xOfZeta' {c' ζ : ℝ} (hc0 : 0 < c') (hζ : 0 < ζ) :
    HasDerivAt (fun u => 2 / (c' * rhoU (xOfZeta c' u)))
      (-(4 * rhoUDeriv (xOfZeta c' ζ) / (c' ^ 2 * rhoU (xOfZeta c' ζ) ^ 3))) ζ := by
  have hx_gt := (xOfZeta_spec hc0 hζ).1
  have hρ_pos := rhoU_pos hx_gt
  have hd_ρ := (hasDerivAt_rhoU hx_gt).comp ζ (hasDerivAt_xOfZeta hc0 hζ)
  have h_div := (hasDerivAt_const ζ (2 : ℝ)).div (hd_ρ.const_mul c') (mul_pos hc0 hρ_pos).ne'
  refine h_div.congr_deriv ?_
  have hρ_ne : rhoU (xOfZeta c' ζ) ≠ 0 := hρ_pos.ne'
  simp only [Function.comp_apply]
  field_simp [hc0.ne', hρ_ne]
  ring

private lemma cumulN_le_half_mul_local {x : ℝ} (hx : xiStar ≤ x) : cumulN x ≤ (x - xiStar) * rhoU x / 2 := by
  unfold cumulN
  have h1 : ∫ t in xiStar..x, rhoU t ≤ ∫ _ in xiStar..x, rhoU x :=
    intervalIntegral.integral_mono_on hx
      (continuousOn_rhoU.mono Icc_subset_Ici_self |>.intervalIntegrable_of_Icc hx)
      intervalIntegrable_const fun t ht =>
        rhoU_strictMonoOn.monotoneOn (Set.mem_Ici.mpr ht.1) (Set.mem_Ici.mpr hx) ht.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

lemma xOfZeta_deriv_bounds :
    ∃ C_x : ℝ, 0 < C_x ∧ ∀ {c' ζ : ℝ}, 0 < c' → 0 < ζ →
      let x := xOfZeta c' ζ
      let r := x - xiStar
      let x1 := 2 / (c' * rhoU x)
      let x2 := -(4 * rhoUDeriv x / (c' ^ 2 * rhoU x ^ 3))
      0 < x1 ∧ x1 ≤ r / ζ ∧ |x2| ≤ C_x * r / ζ ^ 2 ∧
      (xiStar + 1 ≤ x → x1 ≤ C_x / c' ∧ |x2| ≤ C_x / c' ^ 2) := by
  obtain ⟨C_ρ, hCρ_pos, hρ_ratio⟩ := rhoU_deriv_ratio_bounds
  refine ⟨max C_ρ (3 * C_ρ + 2), by positivity, fun {c' ζ} hc0 hζ => ?_⟩
  intro x r x1 x2
  obtain ⟨hx_gt, hcum, _⟩ := xOfZeta_spec hc0 hζ
  have hr_pos : 0 < r := sub_pos.mpr hx_gt
  have hρ_pos : 0 < rhoU x := rhoU_pos hx_gt
  have hx1_pos : 0 < x1 := by dsimp [x1]; positivity
  have hcum_le : cumulN x ≤ r * rhoU x / 2 := cumulN_le_half_mul_local hx_gt.le
  have hx1_le : x1 ≤ r / ζ := by
    have h1 : 2 * ζ ≤ c' * r * rhoU x := by
      calc 2 * ζ = 2 * (c' * cumulN x) := by rw [hcum]
        _ ≤ 2 * (c' * (r * rhoU x / 2)) := by gcongr
        _ = c' * r * rhoU x := by ring
    dsimp [x1]
    rw [div_le_div_iff₀ (by positivity) hζ]
    nlinarith only [h1]
  obtain ⟨hρ1, _⟩ := hρ_ratio hx_gt
  have hx2_abs : |x2| = (rhoUDeriv x / rhoU x) * x1 ^ 2 := by
    have hd_pos : 0 < rhoUDeriv x := (by norm_num : (0 : ℝ) < 4 / 3).trans (rhoUDeriv_ge hx_gt)
    dsimp [x2, x1]
    rw [abs_neg, abs_of_pos (by positivity)]
    field_simp [hc0.ne', hρ_pos.ne']; ring
  have hx2_le : |x2| ≤ max C_ρ (3 * C_ρ + 2) * r / ζ ^ 2 := by
    have hfac : rhoUDeriv x / rhoU x ≤ C_ρ / r := by
      rw [div_le_div_iff₀ hρ_pos hr_pos]; exact hρ1
    have hx1_sq : x1 ^ 2 ≤ (r / ζ) ^ 2 := pow_le_pow_left₀ hx1_pos.le hx1_le 2
    calc |x2| = (rhoUDeriv x / rhoU x) * x1 ^ 2 := hx2_abs
      _ ≤ (C_ρ / r) * (r / ζ) ^ 2 := mul_le_mul hfac hx1_sq (by positivity) (by positivity)
      _ = C_ρ * r / ζ ^ 2 := by field_simp [hr_pos.ne', hζ.ne']
      _ ≤ max C_ρ (3 * C_ρ + 2) * r / ζ ^ 2 := by gcongr; exact le_max_left _ _
  refine ⟨hx1_pos, hx1_le, hx2_le, fun hx1 => ?_⟩
  have hρ_43 : 4 / 3 ≤ rhoU x := by
    have := rhoU_ge_linear_of_ge hx_gt.le
    linarith only [this, hx1]
  have hx1_c : x1 ≤ max C_ρ (3 * C_ρ + 2) / c' := by
    dsimp [x1]
    rw [div_le_div_iff₀ (by positivity) hc0]
    have h2m : 2 ≤ max C_ρ (3 * C_ρ + 2) * (4 / 3 : ℝ) := by
      have : (2 : ℝ) ≤ max C_ρ (3 * C_ρ + 2) := (le_max_right _ _).trans' (by linarith)
      nlinarith only [this]
    have hmul : 2 ≤ max C_ρ (3 * C_ρ + 2) * rhoU x :=
      h2m.trans (mul_le_mul_of_nonneg_left hρ_43 (by positivity))
    nlinarith only [hmul, hc0]
  have hx2_c : |x2| ≤ max C_ρ (3 * C_ρ + 2) / c' ^ 2 := by
    have hd_pos : 0 < rhoUDeriv x := (by norm_num : (0 : ℝ) < 4 / 3).trans (rhoUDeriv_ge hx_gt)
    have h1r : 1 ≤ r := by linarith only [hx1]
    have hρr : rhoUDeriv x ≤ C_ρ * rhoU x := by nlinarith only [hρ1, h1r, hd_pos]
    have hx1_32 : x1 ≤ (3 / 2 : ℝ) / c' := by
      dsimp [x1]; rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith only [hρ_43, hc0]
    have hsq : x1 ^ 2 ≤ (9 / 4 : ℝ) / c' ^ 2 := by
      calc x1 ^ 2 ≤ ((3 / 2 : ℝ) / c') ^ 2 := pow_le_pow_left₀ hx1_pos.le hx1_32 2
        _ = (9 / 4 : ℝ) / c' ^ 2 := by ring
    have hquo : rhoUDeriv x / rhoU x ≤ C_ρ := (div_le_iff₀ hρ_pos).mpr hρr
    calc |x2| = (rhoUDeriv x / rhoU x) * x1 ^ 2 := hx2_abs
      _ ≤ C_ρ * ((9 / 4 : ℝ) / c' ^ 2) := mul_le_mul hquo hsq (by positivity) hCρ_pos.le
      _ = ((9 / 4 : ℝ) * C_ρ) / c' ^ 2 := by ring
      _ ≤ max C_ρ (3 * C_ρ + 2) / c' ^ 2 := by
          gcongr; exact (le_max_right _ _).trans' (by linarith only [hCρ_pos])
  exact ⟨hx1_c, hx2_c⟩

lemma xOfZeta_strictMono {c' : ℝ} (hc0 : 0 < c') : StrictMonoOn (xOfZeta c') (Ioi 0) := by
  intro ζ₁ hζ₁ ζ₂ hζ₂ hlt
  obtain ⟨hx1, hcum1, _⟩ := xOfZeta_spec hc0 hζ₁
  obtain ⟨hx2, hcum2, _⟩ := xOfZeta_spec hc0 hζ₂
  have hcm : cumulN (xOfZeta c' ζ₁) < cumulN (xOfZeta c' ζ₂) := by nlinarith only [hcum1, hcum2, hlt, hc0]
  exact (cumulN_strictMonoOn.lt_iff_lt hx1.le hx2.le).mp hcm

/-! ### 2. `lowerP0(ζ)` and its `C^2` relative derivative bounds -/

/-- Smooth Cardy/density prefactor `P₀(ζ) = 2 √x (1 - e^{-4πx})² / (√3 π √c' ρ_U(x))`. -/
def lowerP0 (c' ζ : ℝ) : ℝ :=
  2 * Real.sqrt (xOfZeta c' ζ) * (1 - Real.exp (-(4 * π * xOfZeta c' ζ))) ^ 2 /
    (Real.sqrt 3 * π * Real.sqrt c' * rhoU (xOfZeta c' ζ))

/-- `x`-logarithmic derivative of `P₀`. -/
def lowerP0LogX (x : ℝ) : ℝ :=
  1 / (2 * x) + 8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) - rhoUDeriv x / rhoU x

/-- Derivative of `lowerP0LogX` with respect to `x`. -/
def lowerP0LogX' (x : ℝ) : ℝ :=
  -(1 / (2 * x ^ 2)) - 32 * π ^ 2 * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) ^ 2 +
    (rhoUDeriv x / rhoU x) ^ 2 - rhoUDeriv2 x / rhoU x

/-- First `ζ`-derivative of `lowerP0 c'`. -/
def lowerP0Deriv1 (c' ζ : ℝ) : ℝ :=
  lowerP0 c' ζ * (lowerP0LogX (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ))))

/-- Second `ζ`-derivative of `lowerP0 c'`. -/
def lowerP0Deriv2 (c' ζ : ℝ) : ℝ :=
  lowerP0 c' ζ *
    ((lowerP0LogX' (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ))) ^ 2 +
        lowerP0LogX (xOfZeta c' ζ) *
          (-(4 * rhoUDeriv (xOfZeta c' ζ) / (c' ^ 2 * rhoU (xOfZeta c' ζ) ^ 3)))) +
      (lowerP0LogX (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ)))) ^ 2)

private lemma exp_neg_four_pi_le_half {x : ℝ} (hx : xiStar < x) :
    Real.exp (-(4 * π * x)) ≤ 1 / 2 := by
  have h1 : 3 ≤ 4 * π * x := by
    have := three_quarters_le_pi_mul_xiStar
    nlinarith only [this, hx, Real.pi_pos]
  have h2 : (2 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have h3 : 2 ≤ Real.exp (4 * π * x) := h2.trans (Real.exp_le_exp.mpr h1)
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) zero_lt_two]
  linarith only [h3]

lemma lowerP0_pos {c' ζ : ℝ} (hc0 : 0 < c') (hζ : 0 < ζ) : 0 < lowerP0 c' ζ := by
  have hx := (xOfZeta_spec hc0 hζ).1
  have hx0 : 0 < xOfZeta c' ζ := xiStar_pos.trans hx
  have hex : Real.exp (-(4 * π * xOfZeta c' ζ)) ≤ 1 / 2 := exp_neg_four_pi_le_half hx
  have h1ex : 0 < 1 - Real.exp (-(4 * π * xOfZeta c' ζ)) := by linarith
  have hρ := rhoU_pos hx
  unfold lowerP0
  positivity

private lemma lowerP0_hasDerivAt_x {x : ℝ} (hx : xiStar < x) :
    HasDerivAt (fun t => Real.sqrt t * (1 - Real.exp (-(4 * π * t))) ^ 2 / rhoU t)
      ((Real.sqrt x * (1 - Real.exp (-(4 * π * x))) ^ 2 / rhoU x) * lowerP0LogX x) x := by
  have hx0 : 0 < x := xiStar_pos.trans hx
  have hex_le : Real.exp (-(4 * π * x)) ≤ 1 / 2 := exp_neg_four_pi_le_half hx
  have hex_pos : 0 < Real.exp (-(4 * π * x)) := Real.exp_pos _
  have h1ex : 0 < 1 - Real.exp (-(4 * π * x)) := by linarith
  have hρ_pos : 0 < rhoU x := rhoU_pos hx
  have hd_sq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    (Real.hasDerivAt_sqrt hx0.ne')
  have hd_e : HasDerivAt (fun t => 1 - Real.exp (-(4 * π * t))) (4 * π * Real.exp (-(4 * π * x))) x := by
    have h1 : HasDerivAt (fun t : ℝ => -(4 * π * t)) (-(4 * π)) x :=
      ((hasDerivAt_id x).const_mul (4 * π)).neg.congr_deriv (by simp)
    exact ((hasDerivAt_const x (1 : ℝ)).sub h1.exp).congr_deriv (by simp; ring)
  have hd_e2 : HasDerivAt (fun t => (1 - Real.exp (-(4 * π * t))) ^ 2)
      (2 * (1 - Real.exp (-(4 * π * x))) * (4 * π * Real.exp (-(4 * π * x)))) x :=
    (hd_e.pow 2).congr_deriv (by simp)
  have hd_num := hd_sq.mul hd_e2
  have hd_quot := hd_num.div (hasDerivAt_rhoU hx) hρ_pos.ne'
  refine hd_quot.congr_deriv ?_
  unfold lowerP0LogX
  have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hsx_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  simp only [Pi.mul_apply]
  field_simp [hsx_ne, h1ex.ne', hρ_pos.ne']
  rw [hsqrt_sq]; ring

private lemma lowerP0LogX_hasDerivAt {x : ℝ} (hx : xiStar < x) :
    HasDerivAt lowerP0LogX (lowerP0LogX' x) x := by
  have hx0 : 0 < x := xiStar_pos.trans hx
  have hex_le : Real.exp (-(4 * π * x)) ≤ 1 / 2 := exp_neg_four_pi_le_half hx
  have h1ex : 0 < 1 - Real.exp (-(4 * π * x)) := by linarith
  have hρ_pos : 0 < rhoU x := rhoU_pos hx
  have h1 : HasDerivAt (fun t : ℝ => 1 / (2 * t)) (-(1 / (2 * x ^ 2))) x := by
    have hd := (hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).const_mul (2 : ℝ)) (by positivity : 2 * x ≠ 0)
    refine hd.congr_deriv ?_
    simp only [id_eq, zero_mul, zero_sub, mul_one]; field_simp [hx0.ne']
  have h2 : HasDerivAt (fun t : ℝ => 8 * π * Real.exp (-(4 * π * t)) / (1 - Real.exp (-(4 * π * t))))
      (-(32 * π ^ 2 * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) ^ 2)) x := by
    have hde : HasDerivAt (fun t : ℝ => Real.exp (-(4 * π * t))) (-(4 * π) * Real.exp (-(4 * π * x))) x :=
      (((hasDerivAt_id x).const_mul (4 * π)).neg).exp.congr_deriv (by simp; ring)
    have hdn : HasDerivAt (fun t : ℝ => 8 * π * Real.exp (-(4 * π * t)))
        (-(32 * π ^ 2) * Real.exp (-(4 * π * x))) x := (hde.const_mul (8 * π)).congr_deriv (by ring)
    have hdd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(4 * π * t))) (4 * π * Real.exp (-(4 * π * x))) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub hde).congr_deriv (by ring)
    refine (hdn.div hdd h1ex.ne').congr_deriv ?_
    field_simp [h1ex.ne']; ring
  have h3 : HasDerivAt (fun t : ℝ => rhoUDeriv t / rhoU t)
      (rhoUDeriv2 x / rhoU x - (rhoUDeriv x / rhoU x) ^ 2) x := by
    refine ((hasDerivAt_rhoUDeriv hx).div (hasDerivAt_rhoU hx) hρ_pos.ne').congr_deriv ?_
    field_simp [hρ_pos.ne']
  exact ((h1.add h2).sub h3).congr_deriv (by unfold lowerP0LogX'; ring)

lemma lowerP0_deriv_bounds :
    ∃ C_P0 : ℝ, 0 < C_P0 ∧ ∀ {c' ζ : ℝ}, 0 < c' → 0 < ζ →
      HasDerivAt (lowerP0 c') (lowerP0Deriv1 c' ζ) ζ ∧
      HasDerivAt (lowerP0Deriv1 c') (lowerP0Deriv2 c' ζ) ζ ∧
      |lowerP0Deriv1 c' ζ| ≤ C_P0 * lowerP0 c' ζ / ζ ∧
      |lowerP0Deriv2 c' ζ| ≤ C_P0 * lowerP0 c' ζ / ζ ^ 2 := by
  obtain ⟨C_ρ, hCρ_pos, hρ_ratio⟩ := rhoU_deriv_ratio_bounds
  obtain ⟨C_x, hCx_pos, hx_bounds⟩ := xOfZeta_deriv_bounds
  let A_log : ℝ := 1 / 2 + 4 + C_ρ
  let B_log : ℝ := 1 / 2 + 32 + C_ρ ^ 2 + C_ρ
  let C_P0 : ℝ := max A_log (B_log + A_log * C_x + A_log ^ 2)
  refine ⟨C_P0, by positivity, fun {c' ζ} hc0 hζ => ?_⟩
  obtain ⟨hx_gt, _, _⟩ := xOfZeta_spec hc0 hζ
  set x := xOfZeta c' ζ
  set r := x - xiStar
  have hr_pos : 0 < r := sub_pos.mpr hx_gt
  have hx0 : 0 < x := xiStar_pos.trans hx_gt
  have hρ_pos : 0 < rhoU x := rhoU_pos hx_gt
  have hP0_pos : 0 < lowerP0 c' ζ := lowerP0_pos hc0 hζ
  have hd_P0 : HasDerivAt (lowerP0 c') (lowerP0Deriv1 c' ζ) ζ := by
    let fac : ℝ := 2 / (Real.sqrt 3 * π * Real.sqrt c')
    have h1 := ((lowerP0_hasDerivAt_x hx_gt).comp ζ (hasDerivAt_xOfZeta hc0 hζ)).const_mul fac
    have heq : (fun y => fac * ((fun t => Real.sqrt t * (1 - Real.exp (-(4 * π * t))) ^ 2 / rhoU t) ∘
        xOfZeta c') y) = lowerP0 c' := by
      ext u; unfold lowerP0; dsimp [fac]; ring
    rw [heq] at h1
    refine h1.congr_deriv ?_
    unfold lowerP0Deriv1 lowerP0; dsimp [fac, x]; ring
  have hd_Log : HasDerivAt (fun u => lowerP0LogX (xOfZeta c' u))
      (lowerP0LogX' x * (2 / (c' * rhoU x))) ζ := by
    exact ((lowerP0LogX_hasDerivAt hx_gt).comp ζ (hasDerivAt_xOfZeta hc0 hζ) :
      HasDerivAt (lowerP0LogX ∘ xOfZeta c') _ ζ)
  have hd_g : HasDerivAt (fun u => lowerP0LogX (xOfZeta c' u) * (2 / (c' * rhoU (xOfZeta c' u))))
      (lowerP0LogX' x * (2 / (c' * rhoU x)) ^ 2 +
        lowerP0LogX x * (-(4 * rhoUDeriv x / (c' ^ 2 * rhoU x ^ 3)))) ζ := by
    have hd_x1 := hasDerivAt_xOfZeta' hc0 hζ
    refine (hd_Log.mul hd_x1).congr_deriv ?_
    dsimp [x]; ring
  have hd_P1 : HasDerivAt (lowerP0Deriv1 c') (lowerP0Deriv2 c' ζ) ζ := by
    have hmul : HasDerivAt (fun u => lowerP0 c' u *
        (lowerP0LogX (xOfZeta c' u) * (2 / (c' * rhoU (xOfZeta c' u)))))
        (lowerP0Deriv1 c' ζ * (lowerP0LogX x * (2 / (c' * rhoU x))) +
          lowerP0 c' ζ * (lowerP0LogX' x * (2 / (c' * rhoU x)) ^ 2 +
            lowerP0LogX x * (-(4 * rhoUDeriv x / (c' ^ 2 * rhoU x ^ 3))))) ζ :=
      hd_P0.mul hd_g
    refine hmul.congr_deriv ?_
    unfold lowerP0Deriv2 lowerP0Deriv1
    dsimp [x]; ring
  have hpi := Real.pi_pos
  have hex_le : Real.exp (-(4 * π * x)) ≤ 1 / 2 := exp_neg_four_pi_le_half hx_gt
  have hex_pos : 0 < Real.exp (-(4 * π * x)) := Real.exp_pos _
  have h1ex : 1 / 2 ≤ 1 - Real.exp (-(4 * π * x)) := by linarith
  have hrexp1 : r * Real.exp (-(4 * π * x)) ≤ 1 / (4 * π) := by
    have h1 : 4 * π * r ≤ Real.exp (4 * π * r) := by linarith only [Real.add_one_le_exp (4 * π * r)]
    have h2 : Real.exp (4 * π * r) ≤ Real.exp (4 * π * x) :=
      Real.exp_le_exp.mpr (by nlinarith only [xiStar_pos, hpi])
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith only [h1, h2, hpi]
  have hr2exp : r ^ 2 * Real.exp (-(4 * π * x)) ≤ 1 / (4 * π ^ 2) := by
    have h1 : 2 * π * r ≤ Real.exp (2 * π * r) := by linarith only [Real.add_one_le_exp (2 * π * r)]
    have h2 : (2 * π * r) ^ 2 ≤ Real.exp (2 * π * r) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : Real.exp (2 * π * r) ^ 2 = Real.exp (4 * π * r) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h4 : Real.exp (4 * π * r) ≤ Real.exp (4 * π * x) :=
      Real.exp_le_exp.mpr (by nlinarith only [xiStar_pos, hpi])
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith only [h2, h3, h4, hpi]
  obtain ⟨hρ1, hρ2⟩ := hρ_ratio hx_gt
  have hρd_pos : 0 < rhoUDeriv x := (by norm_num : (0 : ℝ) < 4 / 3).trans (rhoUDeriv_ge hx_gt)
  have hL_abs : |lowerP0LogX x| * r ≤ A_log := by
    have h1 : |1 / (2 * x)| * r ≤ 1 / 2 := by
      have hr_le : r ≤ x := by dsimp [r]; linarith [xiStar_pos]
      calc |1 / (2 * x)| * r = r / (2 * x) := by rw [abs_of_pos (by positivity)]; ring
        _ ≤ x / (2 * x) := by gcongr
        _ = 1 / 2 := by field_simp [hx0.ne']
    have h2 : |8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x)))| * r ≤ 4 := by
      rw [abs_of_pos (by positivity)]
      calc 8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) * r
          ≤ 8 * π * Real.exp (-(4 * π * x)) / (1 / 2) * r := by gcongr
        _ = 16 * π * (r * Real.exp (-(4 * π * x))) := by ring
        _ ≤ 16 * π * (1 / (4 * π)) := by gcongr
        _ = 4 := by field_simp [hpi.ne']; ring
    have h3 : |rhoUDeriv x / rhoU x| * r ≤ C_ρ := by
      rw [abs_of_pos (by positivity), div_mul_eq_mul_div, div_le_iff₀ hρ_pos]
      exact hρ1
    have htri : |lowerP0LogX x| ≤
        |1 / (2 * x)| + |8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x)))| +
          |rhoUDeriv x / rhoU x| := by
      unfold lowerP0LogX
      calc |1 / (2 * x) + 8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) -
            rhoUDeriv x / rhoU x|
          ≤ |1 / (2 * x) + 8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x)))| +
              |rhoUDeriv x / rhoU x| := abs_sub _ _
        _ ≤ (|1 / (2 * x)| + |8 * π * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x)))|) +
              |rhoUDeriv x / rhoU x| := by gcongr; exact abs_add_le _ _
    have hmul := mul_le_mul_of_nonneg_right htri hr_pos.le
    dsimp [A_log]
    linarith only [hmul, h1, h2, h3]
  have hL'_abs : |lowerP0LogX' x| * r ^ 2 ≤ B_log := by
    have h1 : |-(1 / (2 * x ^ 2))| * r ^ 2 ≤ 1 / 2 := by
      rw [abs_neg, abs_of_pos (by positivity), div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) zero_lt_two]
      have : r ≤ x := by dsimp [r]; linarith [xiStar_pos]
      have hsq : r ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hr_pos.le this 2
      nlinarith only [hsq]
    have h2 : |32 * π ^ 2 * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) ^ 2| * r ^ 2 ≤ 32 := by
      rw [abs_of_pos (by positivity)]
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ (1 - Real.exp (-(4 * π * x))) ^ 2 :=
        pow_le_pow_left₀ (by norm_num) h1ex 2
      calc 32 * π ^ 2 * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) ^ 2 * r ^ 2
          ≤ 32 * π ^ 2 * Real.exp (-(4 * π * x)) / (1 / 2 : ℝ) ^ 2 * r ^ 2 := by gcongr
        _ = 128 * π ^ 2 * (r ^ 2 * Real.exp (-(4 * π * x))) := by ring
        _ ≤ 128 * π ^ 2 * (1 / (4 * π ^ 2)) := by gcongr
        _ = 32 := by field_simp [hpi.ne']; ring
    have h3 : (rhoUDeriv x / rhoU x) ^ 2 * r ^ 2 ≤ C_ρ ^ 2 := by
      have hsub : rhoUDeriv x / rhoU x * r ≤ C_ρ := by rw [div_mul_eq_mul_div, div_le_iff₀ hρ_pos]; exact hρ1
      calc (rhoUDeriv x / rhoU x) ^ 2 * r ^ 2 = (rhoUDeriv x / rhoU x * r) ^ 2 := by ring
        _ ≤ C_ρ ^ 2 := pow_le_pow_left₀ (by positivity) hsub 2
    have h4 : |rhoUDeriv2 x / rhoU x| * r ^ 2 ≤ C_ρ := by
      rw [abs_div, abs_of_pos hρ_pos, div_mul_eq_mul_div, div_le_iff₀ hρ_pos]
      exact hρ2
    have htri : |lowerP0LogX' x| ≤
        |-(1 / (2 * x ^ 2))| +
          |32 * π ^ 2 * Real.exp (-(4 * π * x)) / (1 - Real.exp (-(4 * π * x))) ^ 2| +
          (rhoUDeriv x / rhoU x) ^ 2 + |rhoUDeriv2 x / rhoU x| := by
      unfold lowerP0LogX'
      have ha1 := abs_sub (-(1 / (2 * x ^ 2)) - 32 * π ^ 2 * Real.exp (-(4 * π * x)) /
        (1 - Real.exp (-(4 * π * x))) ^ 2 + (rhoUDeriv x / rhoU x) ^ 2) (rhoUDeriv2 x / rhoU x)
      have ha2 := abs_add_le (-(1 / (2 * x ^ 2)) - 32 * π ^ 2 * Real.exp (-(4 * π * x)) /
        (1 - Real.exp (-(4 * π * x))) ^ 2) ((rhoUDeriv x / rhoU x) ^ 2)
      have ha3 := abs_sub (-(1 / (2 * x ^ 2))) (32 * π ^ 2 * Real.exp (-(4 * π * x)) /
        (1 - Real.exp (-(4 * π * x))) ^ 2)
      have hsq_nn : |(rhoUDeriv x / rhoU x) ^ 2| = (rhoUDeriv x / rhoU x) ^ 2 :=
        abs_of_nonneg (sq_nonneg _)
      rw [hsq_nn] at ha2
      linarith only [ha1, ha2, ha3]
    have hmul := mul_le_mul_of_nonneg_right htri (sq_nonneg r)
    dsimp [B_log]
    linarith only [hmul, h1, h2, h3, h4]
  obtain ⟨hx1_pos, hx1_le, hx2_le, _⟩ := hx_bounds hc0 hζ
  set x1 := 2 / (c' * rhoU x)
  set x2 := -(4 * rhoUDeriv x / (c' ^ 2 * rhoU x ^ 3))
  have hg_abs : |lowerP0LogX x * x1| ≤ A_log / ζ := by
    rw [abs_mul, abs_of_pos hx1_pos]
    calc |lowerP0LogX x| * x1 ≤ |lowerP0LogX x| * (r / ζ) := by gcongr
      _ = (|lowerP0LogX x| * r) / ζ := by ring
      _ ≤ A_log / ζ := by gcongr
  have hg'_abs : |lowerP0LogX' x * x1 ^ 2 + lowerP0LogX x * x2| ≤ (B_log + A_log * C_x) / ζ ^ 2 := by
    have h1 : |lowerP0LogX' x * x1 ^ 2| ≤ B_log / ζ ^ 2 := by
      rw [abs_mul, abs_pow, abs_of_pos hx1_pos]
      have hx1_sq : x1 ^ 2 ≤ (r / ζ) ^ 2 := pow_le_pow_left₀ hx1_pos.le hx1_le 2
      calc |lowerP0LogX' x| * x1 ^ 2 ≤ |lowerP0LogX' x| * (r / ζ) ^ 2 := by gcongr
        _ = (|lowerP0LogX' x| * r ^ 2) / ζ ^ 2 := by ring
        _ ≤ B_log / ζ ^ 2 := by gcongr
    have h2 : |lowerP0LogX x * x2| ≤ (A_log * C_x) / ζ ^ 2 := by
      rw [abs_mul]
      calc |lowerP0LogX x| * |x2| ≤ |lowerP0LogX x| * (C_x * r / ζ ^ 2) := by gcongr
        _ = (|lowerP0LogX x| * r) * C_x / ζ ^ 2 := by ring
        _ ≤ (A_log * C_x) / ζ ^ 2 := by gcongr
    calc |lowerP0LogX' x * x1 ^ 2 + lowerP0LogX x * x2|
        ≤ |lowerP0LogX' x * x1 ^ 2| + |lowerP0LogX x * x2| := abs_add_le _ _
      _ ≤ B_log / ζ ^ 2 + (A_log * C_x) / ζ ^ 2 := add_le_add h1 h2
      _ = (B_log + A_log * C_x) / ζ ^ 2 := by ring
  refine ⟨hd_P0, hd_P1, ?_, ?_⟩
  · unfold lowerP0Deriv1
    rw [abs_mul, abs_of_pos hP0_pos]
    calc lowerP0 c' ζ * |lowerP0LogX x * x1|
        ≤ lowerP0 c' ζ * (A_log / ζ) := by gcongr
      _ ≤ lowerP0 c' ζ * (C_P0 / ζ) := by gcongr; exact le_max_left _ _
      _ = C_P0 * lowerP0 c' ζ / ζ := by ring
  · unfold lowerP0Deriv2
    rw [abs_mul, abs_of_pos hP0_pos]
    have hbr : |(lowerP0LogX' x * x1 ^ 2 + lowerP0LogX x * x2) + (lowerP0LogX x * x1) ^ 2| ≤
        (B_log + A_log * C_x + A_log ^ 2) / ζ ^ 2 := by
      have hsq : |(lowerP0LogX x * x1) ^ 2| ≤ A_log ^ 2 / ζ ^ 2 := by
        rw [abs_pow]
        calc |lowerP0LogX x * x1| ^ 2 ≤ (A_log / ζ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hg_abs 2
          _ = A_log ^ 2 / ζ ^ 2 := by ring
      calc |(lowerP0LogX' x * x1 ^ 2 + lowerP0LogX x * x2) + (lowerP0LogX x * x1) ^ 2|
          ≤ |lowerP0LogX' x * x1 ^ 2 + lowerP0LogX x * x2| + |(lowerP0LogX x * x1) ^ 2| := abs_add_le _ _
        _ ≤ (B_log + A_log * C_x) / ζ ^ 2 + A_log ^ 2 / ζ ^ 2 := add_le_add hg'_abs hsq
        _ = (B_log + A_log * C_x + A_log ^ 2) / ζ ^ 2 := by ring
    calc lowerP0 c' ζ * |(lowerP0LogX' x * x1 ^ 2 + lowerP0LogX x * x2) + (lowerP0LogX x * x1) ^ 2|
        ≤ lowerP0 c' ζ * ((B_log + A_log * C_x + A_log ^ 2) / ζ ^ 2) := by gcongr
      _ ≤ lowerP0 c' ζ * (C_P0 / ζ ^ 2) := by gcongr; exact le_max_right _ _
      _ = C_P0 * lowerP0 c' ζ / ζ ^ 2 := by ring

end

end FormalResearch.ModularBootstrap.FiveTerm
