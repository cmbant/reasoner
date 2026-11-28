module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeWeps
public import FormalResearch.ModularBootstrap.FiveTerm.OuterX

/-!
# Oscillatory Coefficient Bounds `W_1(ζ)` and `θ̃_ε(ζ)` on `(0, ∞)` (`ctl:freeze`)

Proves `lowerWeps_unwrappedTheta_deriv_bounds`:
`|W_1^(j)(ζ)| + |θ^(j)(ζ)| ≤ C_osc (ζ^{-j} + c'^{-j})` (`j = 1, 2`) for `c' ≥ 10000`,
`ε = c'^{-2}`, and `ζ > 0`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

private lemma lowerY_deriv_bounds :
    ∃ M_Y : ℝ, 0 < M_Y ∧ ∀ {x : ℝ}, xiStar < x →
      let y1 := fun t => (π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t /
          (2 * lowerY t)
      let y2 := fun t => -(π ^ 2 * (2 * Real.sinh (π * t) ^ 2 / (Real.cosh (π * t) + Real.sqrt 2) ^ 2 -
          Real.cosh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) / (2 * lowerY t) -
          (-(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) ^ 2 / (4 * lowerY t ^ 3)
      lowerY x ≤ 1 ∧ HasDerivAt lowerY (y1 x) x ∧ HasDerivAt y1 (y2 x) x ∧
      |y1 x| ≤ M_Y * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) ∧
      |y2 x| ≤ M_Y * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by
  let D_ch : ℝ := Real.cosh (π * (xiStar + 1)) + Real.sqrt 2
  let c_y : ℝ := Real.sqrt (π / D_ch)
  let c_y1 : ℝ := Real.sqrt (1 - slitA (xiStar + 1))
  let c_min : ℝ := min c_y c_y1
  have hDch_pos : 0 < D_ch := by dsimp [D_ch]; have := Real.cosh_pos (π * (xiStar + 1)); positivity
  have hcy_pos : 0 < c_y := by dsimp [c_y]; exact Real.sqrt_pos.mpr (div_pos Real.pi_pos hDch_pos)
  have hcy1_pos : 0 < c_y1 := by
    have h1 := slitA_lt_one (by linarith : xiStar < xiStar + 1)
    exact Real.sqrt_pos.mpr (by linarith)
  have hcmin_pos : 0 < c_min := lt_min hcy_pos hcy1_pos
  let M_Y : ℝ := max (π / (2 * c_min)) (3 * π ^ 2 / (2 * c_min) + π ^ 2 / (4 * c_min ^ 3)) + 1
  refine ⟨M_Y, by positivity, fun {x} hx => ?_⟩
  intro y1 y2
  have hx0 : 0 < x := xiStar_pos.trans hx
  have hy_mem : lowerY x ∈ Ioo (0 : ℝ) 1 := yOfX_mem hx
  have hy_pos : 0 < lowerY x := hy_mem.1
  have hy_le1 : lowerY x ≤ 1 := hy_mem.2.le
  have h1y : 1 - slitA x = lowerY x ^ 2 := by linarith only [one_sub_lowerY_sq hx]
  have hsa := slitA_derivs x
  have hev_y : lowerY =ᶠ[𝓝 x] fun t => Real.sqrt (1 - slitA t) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have hsq := one_sub_lowerY_sq ht
    have ht_nn : 0 ≤ lowerY t := (yOfX_mem ht).1.le
    rw [← hsq, sub_sub_cancel, Real.sqrt_sq ht_nn]
  have hd_inner : ∀ t, HasDerivAt (fun u => 1 - slitA u)
      ((π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) t := fun t =>
    ((hasDerivAt_const t (1 : ℝ)).sub (slitA_derivs t).1).congr_deriv (by ring)
  have hysq_pos : 0 < 1 - slitA x := by rw [h1y]; positivity
  have hd_y : HasDerivAt lowerY (y1 x) x := by
    have hsq := (hd_inner x).sqrt hysq_pos.ne'
    have hsqrt : Real.sqrt (1 - slitA x) = lowerY x := by
      rw [h1y, Real.sqrt_sq hy_pos.le]
    refine (hsq.congr_of_eventuallyEq hev_y).congr_deriv ?_
    rw [hsqrt]
  have hd_y1 : HasDerivAt y1 (y2 x) x := by
    have hneg_a1 := (slitA_derivs x).2.1.neg
    have hnum_hd : HasDerivAt
        (fun t => (π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t)
        (-(π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
            Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x)) x := by
      have heq : (fun t => (π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) =
          fun t => -(-(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) := by
        ext t; ring
      rw [heq]; exact hneg_a1
    have hden_hd : HasDerivAt (fun t => 2 * lowerY t) (2 * y1 x) x := hd_y.const_mul 2
    refine (hnum_hd.div hden_hd (by positivity)).congr_deriv ?_
    have hdn : Real.cosh (π * x) + Real.sqrt 2 ≠ 0 := by have := Real.cosh_pos (π * x); positivity
    dsimp [y2, y1]
    field_simp [hy_pos.ne', hdn]; ring
  have hy_lb : c_min * Real.sqrt (min (x - xiStar) 1) ≤ lowerY x := by
    rcases le_or_gt x (xiStar + 1) with hx1 | hx1
    · have hm : min (x - xiStar) 1 = x - xiStar := min_eq_left (by linarith)
      rw [hm]
      have hmvt := exists_hasDerivAt_eq_slope (fun t => Real.cosh (π * t))
        (fun t => π * Real.sinh (π * t)) hx
        (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousOn
        (fun t _ => ((Real.hasDerivAt_cosh (π * t)).comp t
          (by simpa using (hasDerivAt_id t).const_mul π)).congr_deriv (by ring))
      obtain ⟨ξ, hξ, hslope⟩ := hmvt
      have hch_xi : Real.cosh (π * xiStar) = Real.sqrt 2 := by
        have h := Real.cosh_sq_sub_sinh_sq (π * xiStar)
        rw [sinh_pi_mul_xiStar, one_pow] at h
        rw [← Real.sqrt_sq (Real.cosh_pos _).le]
        congr 1; linarith
      have hsh_ge1 : 1 ≤ Real.sinh (π * ξ) := by
        rw [← sinh_pi_mul_xiStar]
        exact (Real.sinh_lt_sinh.mpr (mul_lt_mul_of_pos_left hξ.1 Real.pi_pos)).le
      have hnum_ge : π * (x - xiStar) ≤ Real.cosh (π * x) - Real.sqrt 2 := by
        rw [hch_xi, eq_div_iff (sub_pos.mpr hx).ne'] at hslope
        have hpi := Real.pi_pos
        have hdx : 0 < x - xiStar := sub_pos.mpr hx
        have h1 : π * 1 * (x - xiStar) ≤ π * Real.sinh (π * ξ) * (x - xiStar) := by gcongr
        linarith only [h1, hslope]
      have hden_le : Real.cosh (π * x) + Real.sqrt 2 ≤ D_ch := by
        have hpx0 : 0 ≤ π * x := (mul_pos Real.pi_pos hx0).le
        have hpx1 : 0 ≤ π * (xiStar + 1) := (mul_pos Real.pi_pos (by linarith [xiStar_pos])).le
        have hch_le : Real.cosh (π * x) ≤ Real.cosh (π * (xiStar + 1)) :=
          Real.cosh_le_cosh.mpr (by
            rw [abs_of_nonneg hpx0, abs_of_nonneg hpx1]
            exact mul_le_mul_of_nonneg_left hx1 Real.pi_pos.le)
        dsimp [D_ch]; linarith only [hch_le]
      have hsq_ge : c_y ^ 2 * (x - xiStar) ≤ lowerY x ^ 2 := by
        rw [← h1y]; unfold slitA
        have hden_x : 0 < Real.cosh (π * x) + Real.sqrt 2 := by
          have := Real.cosh_pos (π * x); positivity
        have h1y' : 1 - 2 * Real.sqrt 2 / (Real.cosh (π * x) + Real.sqrt 2) =
            (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by
          field_simp [hden_x.ne']; ring
        rw [h1y']
        have hc2 : c_y ^ 2 = π / D_ch := Real.sq_sqrt (by positivity)
        rw [hc2]
        have hnum_nn : 0 ≤ Real.cosh (π * x) - Real.sqrt 2 := by
          have := mul_pos Real.pi_pos (sub_pos.mpr hx)
          linarith only [hnum_ge, this]
        calc (π / D_ch) * (x - xiStar) = (π * (x - xiStar)) / D_ch := by ring
          _ ≤ (Real.cosh (π * x) - Real.sqrt 2) / D_ch := by gcongr
          _ ≤ (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by gcongr
      have hsq_ge' : (c_y * Real.sqrt (x - xiStar)) ^ 2 ≤ lowerY x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (sub_pos.mpr hx).le]; exact hsq_ge
      have hc1 : c_min * Real.sqrt (x - xiStar) ≤ c_y * Real.sqrt (x - xiStar) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      have hys : c_y * Real.sqrt (x - xiStar) ≤ lowerY x := by
        nlinarith only [hsq_ge', hy_pos, hcy_pos, Real.sqrt_nonneg (x - xiStar)]
      exact hc1.trans hys
    · have hm : min (x - xiStar) 1 = 1 := min_eq_right (by linarith)
      rw [hm, Real.sqrt_one, mul_one]
      have hpx0 : 0 ≤ π * x := (mul_pos Real.pi_pos hx0).le
      have hpx1 : 0 ≤ π * (xiStar + 1) := (mul_pos Real.pi_pos (by linarith [xiStar_pos])).le
      have hch_le : Real.cosh (π * (xiStar + 1)) ≤ Real.cosh (π * x) :=
        Real.cosh_le_cosh.mpr (by
          rw [abs_of_nonneg hpx1, abs_of_nonneg hpx0]
          exact mul_le_mul_of_nonneg_left hx1.le Real.pi_pos.le)
      have ha_le : slitA x ≤ slitA (xiStar + 1) := by
        unfold slitA
        have hpos1 : 0 < Real.cosh (π * (xiStar + 1)) + Real.sqrt 2 := by
          have := Real.cosh_pos (π * (xiStar + 1)); positivity
        gcongr
      have h1y_ge : 1 - slitA (xiStar + 1) ≤ lowerY x ^ 2 := by linarith only [h1y, ha_le]
      have hcy1_le : c_y1 ≤ lowerY x := by
        rw [← Real.sqrt_sq hy_pos.le]; exact Real.sqrt_le_sqrt h1y_ge
      exact (min_le_right _ _).trans hcy1_le
  set m := min (x - xiStar) 1
  have hm_pos : 0 < m := lt_min (sub_pos.mpr hx) one_pos
  have ha_le1 : slitA x ≤ 1 := (slitA_lt_one hx).le
  obtain ⟨ha1_bd, ha2_bd⟩ := hsa.2.2 hx0.le
  have hpi := Real.pi_pos
  have hy1_abs : |y1 x| ≤ M_Y * m ^ (-(1 / 2 : ℝ)) := by
    have hnum_bd : |(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x| ≤ π := by
      have heq : |(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x| =
          |-(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x| := by
        rw [show -(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x =
          -((π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) by ring, abs_neg]
      rw [heq]; exact ha1_bd.trans (by nlinarith only [hpi, ha_le1])
    rw [Real.rpow_neg hm_pos.le, ← Real.sqrt_eq_rpow]
    dsimp [y1]
    rw [abs_div, abs_of_pos (mul_pos zero_lt_two hy_pos)]
    calc |π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) * slitA x| / (2 * lowerY x)
        ≤ π / (2 * (c_min * Real.sqrt m)) := by gcongr
      _ = (π / (2 * c_min)) * (Real.sqrt m)⁻¹ := by ring
      _ ≤ M_Y * (Real.sqrt m)⁻¹ := by
          gcongr; dsimp [M_Y]; exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hy2_abs : |y2 x| ≤ M_Y * m ^ (-(3 / 2 : ℝ)) := by
    have hm1 : m ≤ 1 := min_le_right _ _
    have hnum2_bd : |-(π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x)| ≤ 3 * π ^ 2 := by
      rw [abs_neg]; exact ha2_bd.trans (by nlinarith only [pow_pos hpi 2, ha_le1])
    have ha1_sq_bd : (-(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) ^ 2 ≤ π ^ 2 := by
      have h1 := ha1_bd.trans (by nlinarith only [hpi, ha_le1] : π * slitA x ≤ π)
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at h2
    have hm32 : m ^ (3 / 2 : ℝ) = m * Real.sqrt m := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm_pos, Real.rpow_one, Real.sqrt_eq_rpow]
    have ht1 : |-(π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) / (2 * lowerY x)| ≤
        (3 * π ^ 2 / (2 * c_min)) * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_div, abs_of_pos (mul_pos zero_lt_two hy_pos)]
      calc _ ≤ (3 * π ^ 2) / (2 * (c_min * Real.sqrt m)) := by gcongr
        _ = (3 * π ^ 2 / (2 * c_min)) * (Real.sqrt m)⁻¹ := by ring
        _ ≤ (3 * π ^ 2 / (2 * c_min)) * (m ^ (3 / 2 : ℝ))⁻¹ := by
            gcongr
            rw [hm32]
            exact mul_le_of_le_one_left (Real.sqrt_nonneg m) hm1
        _ = (3 * π ^ 2 / (2 * c_min)) * m ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_neg hm_pos.le]
    have ht2 : |(-(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) ^ 2 /
        (4 * lowerY x ^ 3)| ≤ (π ^ 2 / (4 * c_min ^ 3)) * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (mul_pos (by norm_num) (pow_pos hy_pos 3))]
      have hy3_lb : c_min ^ 3 * m ^ (3 / 2 : ℝ) ≤ lowerY x ^ 3 := by
        have h3 := pow_le_pow_left₀ (by positivity) hy_lb 3
        have hsm3 : Real.sqrt m ^ 3 = m ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hm_pos.le]; norm_num
        rw [mul_pow, hsm3] at h3
        exact h3
      calc _ ≤ π ^ 2 / (4 * (c_min ^ 3 * m ^ (3 / 2 : ℝ))) := by gcongr
        _ = (π ^ 2 / (4 * c_min ^ 3)) * (m ^ (3 / 2 : ℝ))⁻¹ := by ring
        _ = (π ^ 2 / (4 * c_min ^ 3)) * m ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_neg hm_pos.le]
    calc |y2 x| ≤ _ + _ := by dsimp [y2]; exact abs_sub _ _
      _ ≤ (3 * π ^ 2 / (2 * c_min) + π ^ 2 / (4 * c_min ^ 3)) * m ^ (-(3 / 2 : ℝ)) := by
          linarith only [add_le_add ht1 ht2]
      _ ≤ M_Y * m ^ (-(3 / 2 : ℝ)) := by
          gcongr; dsimp [M_Y]; exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  exact ⟨hy_le1, hd_y, hd_y1, hy1_abs, hy2_abs⟩

private lemma thetaMt_x_deriv_bounds :
    ∃ M_θ : ℝ, 0 ≤ M_θ ∧ ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 / 4 →
      let tFun := fun x => -2 * Real.arctan (ε * lowerY x / (slitA x + ε))
      ∃ t1 t2 : ℝ → ℝ, ∀ {x : ℝ}, xiStar < x →
        HasDerivAt tFun (t1 x) x ∧ HasDerivAt t1 (t2 x) x ∧
        |t1 x| ≤ M_θ * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) ∧
        |t2 x| ≤ M_θ * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨M_Y, hMY_pos, hy_data⟩ := lowerY_deriv_bounds
  refine ⟨2 * (π + M_Y) + 2 * (5 * π ^ 2 + 2 * π * M_Y + M_Y) + 4 * (π + M_Y) ^ 2, by positivity,
    fun {ε} hε0 hε1 => ?_⟩
  let q : ℝ → ℝ := fun x => ε / (slitA x + ε)
  let a1 : ℝ → ℝ := fun x => -(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
  let a2 : ℝ → ℝ := fun x =>
    π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
      Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
  let q1 : ℝ → ℝ := fun x => -ε * a1 x / (slitA x + ε) ^ 2
  let q2 : ℝ → ℝ := fun x => (-ε * a2 x * (slitA x + ε) + 2 * ε * a1 x ^ 2) / (slitA x + ε) ^ 3
  let y1 : ℝ → ℝ := fun t => (π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t /
      (2 * lowerY t)
  let y2 : ℝ → ℝ := fun t => -(π ^ 2 * (2 * Real.sinh (π * t) ^ 2 / (Real.cosh (π * t) + Real.sqrt 2) ^ 2 -
      Real.cosh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) / (2 * lowerY t) -
      (-(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) ^ 2 / (4 * lowerY t ^ 3)
  let u : ℝ → ℝ := fun x => q x * lowerY x
  let u1 : ℝ → ℝ := fun x => q1 x * lowerY x + q x * y1 x
  let u2 : ℝ → ℝ := fun x => q2 x * lowerY x + 2 * q1 x * y1 x + q x * y2 x
  let t1 : ℝ → ℝ := fun x => -2 * (u1 x / (1 + u x ^ 2))
  let t2 : ℝ → ℝ := fun x => -2 * ((u2 x * (1 + u x ^ 2) - 2 * u x * u1 x ^ 2) / (1 + u x ^ 2) ^ 2)
  refine ⟨t1, t2, fun {x} hx => ?_⟩
  have hx0 : 0 < x := xiStar_pos.trans hx
  have ha0 : 0 < slitA x := slitA_pos x
  have hs0 : 0 < slitA x + ε := by linarith
  have hsa := slitA_derivs x
  obtain ⟨hy1_le, hd_y, hd_y1, hy1_bd, hy2_bd⟩ := hy_data hx
  have hy_pos : 0 < lowerY x := (yOfX_mem hx).1
  have hq_hd : HasDerivAt q (q1 x) x := by
    have hd := (hasDerivAt_const x ε).div (hsa.1.add_const ε) hs0.ne'
    refine hd.congr_deriv ?_
    dsimp [q1, a1]; field_simp [hs0.ne']; ring
  have hq1_hd : HasDerivAt q1 (q2 x) x := by
    have hn : HasDerivAt (fun t => -ε * a1 t) (-ε * a2 x) x := hsa.2.1.const_mul (-ε)
    have hd : HasDerivAt (fun t => (slitA t + ε) ^ 2) (2 * (slitA x + ε) * a1 x) x :=
      ((hsa.1.add_const ε).pow 2).congr_deriv (by dsimp [a1]; simp)
    refine (hn.div hd (pow_pos hs0 2).ne').congr_deriv ?_
    dsimp [q2, a1, a2]; field_simp [hs0.ne']; ring
  have hu_hd : HasDerivAt u (u1 x) x := hq_hd.mul hd_y
  have hu1_hd : HasDerivAt u1 (u2 x) x := by
    have h1 := hq1_hd.mul hd_y
    have h2 := hq_hd.mul hd_y1
    refine (h1.add h2).congr_deriv ?_
    dsimp [u2]; ring
  have hu_eq : (fun t => -2 * Real.arctan (ε * lowerY t / (slitA t + ε))) =
      fun t => -2 * Real.arctan (u t) := by
    ext t; dsimp [u, q]; ring_nf
  have hden_pos : 0 < 1 + u x ^ 2 := by positivity
  have ht1_hd : HasDerivAt (fun t => -2 * Real.arctan (ε * lowerY t / (slitA t + ε))) (t1 x) x := by
    rw [hu_eq]
    refine ((hu_hd.arctan).const_mul (-2 : ℝ)).congr_deriv ?_
    dsimp [t1]; ring
  have ht2_hd : HasDerivAt t1 (t2 x) x := by
    have hden' : HasDerivAt (fun t => 1 + u t ^ 2) (2 * u x * u1 x) x :=
      ((hasDerivAt_const x (1 : ℝ)).add (hu_hd.pow 2)).congr_deriv (by simp)
    refine ((hu1_hd.div hden' hden_pos.ne').const_mul (-2 : ℝ)).congr_deriv ?_
    dsimp [t2]; field_simp [hden_pos.ne']
  have hq_bd : 0 ≤ q x ∧ q x ≤ 1 := ⟨by dsimp [q]; positivity, (div_le_one hs0).mpr (by linarith)⟩
  obtain ⟨ha1_bd, ha2_bd⟩ := hsa.2.2 hx0.le
  have hεa_sq : ε * slitA x ≤ (slitA x + ε) ^ 2 := by
    nlinarith only [sq_nonneg (slitA x - ε), hε0, ha0.le]
  have hq1_bd : |q1 x| ≤ π := by
    dsimp [q1]
    rw [abs_div, abs_of_pos (pow_pos hs0 2), abs_mul, abs_neg, abs_of_nonneg hε0]
    have hdiv1 : ε * slitA x / (slitA x + ε) ^ 2 ≤ 1 := (div_le_one (pow_pos hs0 2)).mpr hεa_sq
    calc ε * |a1 x| / (slitA x + ε) ^ 2 ≤ ε * (π * slitA x) / (slitA x + ε) ^ 2 := by gcongr
      _ = π * (ε * slitA x / (slitA x + ε) ^ 2) := by ring
      _ ≤ π * 1 := by gcongr
      _ = π := mul_one _
  have hq2_bd : |q2 x| ≤ 5 * π ^ 2 := by
    dsimp [q2]
    rw [abs_div, abs_of_pos (pow_pos hs0 3)]
    have ha_s : slitA x ≤ slitA x + ε := by linarith
    have hnum1 : |-ε * a2 x * (slitA x + ε)| ≤ 3 * π ^ 2 * (slitA x + ε) ^ 3 := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hε0, abs_of_pos hs0]
      calc ε * |a2 x| * (slitA x + ε) ≤ ε * (3 * π ^ 2 * slitA x) * (slitA x + ε) := by gcongr
        _ = 3 * π ^ 2 * (ε * slitA x) * (slitA x + ε) := by ring
        _ ≤ 3 * π ^ 2 * (slitA x + ε) ^ 2 * (slitA x + ε) := by gcongr
        _ = 3 * π ^ 2 * (slitA x + ε) ^ 3 := by ring
    have hnum2 : |2 * ε * a1 x ^ 2| ≤ 2 * π ^ 2 * (slitA x + ε) ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hε0, abs_pow]
      have ha1_sq : |a1 x| ^ 2 ≤ (π * slitA x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha1_bd 2
      calc 2 * ε * |a1 x| ^ 2 ≤ 2 * ε * (π * slitA x) ^ 2 := by gcongr
        _ = 2 * π ^ 2 * (ε * slitA x) * slitA x := by ring
        _ ≤ 2 * π ^ 2 * (slitA x + ε) ^ 2 * (slitA x + ε) := by gcongr
        _ = 2 * π ^ 2 * (slitA x + ε) ^ 3 := by ring
    calc |-ε * a2 x * (slitA x + ε) + 2 * ε * a1 x ^ 2| / (slitA x + ε) ^ 3
        ≤ (3 * π ^ 2 * (slitA x + ε) ^ 3 + 2 * π ^ 2 * (slitA x + ε) ^ 3) / (slitA x + ε) ^ 3 := by
          gcongr; exact (abs_add_le _ _).trans (add_le_add hnum1 hnum2)
      _ = 5 * π ^ 2 := by field_simp [(pow_pos hs0 3).ne']; ring
  set m := min (x - xiStar) 1
  have hm_pos : 0 < m := lt_min (sub_pos.mpr hx) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hm_ge1 : 1 ≤ m ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hm_pos.le, one_le_inv₀ (Real.rpow_pos_of_pos hm_pos _)]
    exact Real.rpow_le_one hm_pos.le hm1 (by norm_num)
  have hm_ge32 : m ^ (-(1 / 2 : ℝ)) ≤ m ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hm_pos hm1 (by norm_num)
  have hm_1_ge1 : 1 ≤ m ^ (-(3 / 2 : ℝ)) := hm_ge1.trans hm_ge32
  have hu1_bd : |u1 x| ≤ (π + M_Y) * m ^ (-(1 / 2 : ℝ)) := by
    have h1 : |q1 x * lowerY x| ≤ π * m ^ (-(1 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_pos hy_pos]
      calc |q1 x| * lowerY x ≤ π * 1 := by gcongr
        _ ≤ π * m ^ (-(1 / 2 : ℝ)) := by gcongr
    have h2 : |q x * y1 x| ≤ M_Y * m ^ (-(1 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hq_bd.1]
      calc q x * |y1 x| ≤ 1 * (M_Y * m ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul hq_bd.2 hy1_bd (abs_nonneg _) zero_le_one
        _ = M_Y * m ^ (-(1 / 2 : ℝ)) := by ring
    dsimp [u1]
    exact (abs_add_le _ _).trans (by linarith only [add_le_add h1 h2])
  have hu2_bd : |u2 x| ≤ (5 * π ^ 2 + 2 * π * M_Y + M_Y) * m ^ (-(3 / 2 : ℝ)) := by
    have h1 : |q2 x * lowerY x| ≤ 5 * π ^ 2 * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_pos hy_pos]
      calc |q2 x| * lowerY x ≤ 5 * π ^ 2 * 1 := by gcongr
        _ ≤ 5 * π ^ 2 * m ^ (-(3 / 2 : ℝ)) := by gcongr
    have h2 : |2 * q1 x * y1 x| ≤ 2 * π * M_Y * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos zero_lt_two]
      calc 2 * |q1 x| * |y1 x| ≤ 2 * π * (M_Y * m ^ (-(1 / 2 : ℝ))) := by gcongr
        _ ≤ 2 * π * (M_Y * m ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = 2 * π * M_Y * m ^ (-(3 / 2 : ℝ)) := by ring
    have h3 : |q x * y2 x| ≤ M_Y * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hq_bd.1]
      calc q x * |y2 x| ≤ 1 * (M_Y * m ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul hq_bd.2 hy2_bd (abs_nonneg _) zero_le_one
        _ = M_Y * m ^ (-(3 / 2 : ℝ)) := by ring
    dsimp [u2]
    have htri := (abs_add_le (q2 x * lowerY x + 2 * q1 x * y1 x) (q x * y2 x)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    linarith only [htri, h1, h2, h3]
  have ht1_bd : |t1 x| ≤ (2 * (π + M_Y) + 2 * (5 * π ^ 2 + 2 * π * M_Y + M_Y) + 4 * (π + M_Y) ^ 2) *
      m ^ (-(1 / 2 : ℝ)) := by
    have hden1 : 1 ≤ 1 + u x ^ 2 := by linarith [sq_nonneg (u x)]
    dsimp [t1]
    rw [abs_mul, abs_neg, abs_of_pos zero_lt_two, abs_div, abs_of_pos hden_pos]
    calc 2 * (|u1 x| / (1 + u x ^ 2)) ≤ 2 * (|u1 x| / 1) := by gcongr
      _ = 2 * |u1 x| := by ring
      _ ≤ 2 * ((π + M_Y) * m ^ (-(1 / 2 : ℝ))) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ (2 * (5 * π ^ 2 + 2 * π * M_Y + M_Y) + 4 * (π + M_Y) ^ 2) * m ^ (-(1 / 2 : ℝ)) := by positivity
          linarith only [this]
  have ht2_bd : |t2 x| ≤ (2 * (π + M_Y) + 2 * (5 * π ^ 2 + 2 * π * M_Y + M_Y) + 4 * (π + M_Y) ^ 2) *
      m ^ (-(3 / 2 : ℝ)) := by
    have hden1 : 1 ≤ 1 + u x ^ 2 := by linarith [sq_nonneg (u x)]
    have h2u : |2 * u x| ≤ (1 + u x ^ 2) ^ 2 := by
      have h1 : |2 * u x| ≤ 1 + u x ^ 2 := by
        rw [abs_mul, abs_of_pos zero_lt_two]
        nlinarith only [sq_nonneg (|u x| - 1), sq_abs (u x)]
      calc |2 * u x| ≤ 1 + u x ^ 2 := h1
        _ ≤ (1 + u x ^ 2) ^ 2 := by nlinarith only [hden1]
    have hu1_sq : |u1 x| ^ 2 ≤ (π + M_Y) ^ 2 * m ^ (-(3 / 2 : ℝ)) := by
      have hsq : |u1 x| ^ 2 ≤ ((π + M_Y) * m ^ (-(1 / 2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hu1_bd 2
      have hm_eq : (m ^ (-(1 / 2 : ℝ))) ^ 2 = m ^ (-1 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hm_pos.le]; norm_num
      have hm_le32 : m ^ (-1 : ℝ) ≤ m ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hm_pos hm1 (by norm_num)
      calc |u1 x| ^ 2 ≤ (π + M_Y) ^ 2 * (m ^ (-(1 / 2 : ℝ))) ^ 2 := by
            linarith only [hsq, show ((π + M_Y) * m ^ (-(1 / 2 : ℝ))) ^ 2 =
              (π + M_Y) ^ 2 * (m ^ (-(1 / 2 : ℝ))) ^ 2 by ring]
        _ = (π + M_Y) ^ 2 * m ^ (-1 : ℝ) := by rw [hm_eq]
        _ ≤ (π + M_Y) ^ 2 * m ^ (-(3 / 2 : ℝ)) := by gcongr
    have hfrac1 : |u2 x| / (1 + u x ^ 2) ≤ (5 * π ^ 2 + 2 * π * M_Y + M_Y) * m ^ (-(3 / 2 : ℝ)) := by
      calc |u2 x| / (1 + u x ^ 2) ≤ |u2 x| / 1 := by gcongr
        _ = |u2 x| := div_one _
        _ ≤ _ := hu2_bd
    have hfrac2 : |2 * u x * u1 x ^ 2| / (1 + u x ^ 2) ^ 2 ≤ (π + M_Y) ^ 2 * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_pow]
      calc |2 * u x| * |u1 x| ^ 2 / (1 + u x ^ 2) ^ 2
          ≤ (1 + u x ^ 2) ^ 2 * |u1 x| ^ 2 / (1 + u x ^ 2) ^ 2 := by gcongr
        _ = |u1 x| ^ 2 := by field_simp [hden_pos.ne']
        _ ≤ _ := hu1_sq
    dsimp [t2]
    rw [abs_mul, abs_neg, abs_of_pos zero_lt_two, abs_div, abs_of_pos (pow_pos hden_pos 2)]
    have htri : |u2 x * (1 + u x ^ 2) - 2 * u x * u1 x ^ 2| / (1 + u x ^ 2) ^ 2 ≤
        |u2 x| / (1 + u x ^ 2) + |2 * u x * u1 x ^ 2| / (1 + u x ^ 2) ^ 2 := by
      have h1 : |u2 x * (1 + u x ^ 2) - 2 * u x * u1 x ^ 2| ≤
          |u2 x| * (1 + u x ^ 2) + |2 * u x * u1 x ^ 2| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos hden_pos]
      calc _ ≤ (|u2 x| * (1 + u x ^ 2) + |2 * u x * u1 x ^ 2|) / (1 + u x ^ 2) ^ 2 := by gcongr
        _ = |u2 x| / (1 + u x ^ 2) + |2 * u x * u1 x ^ 2| / (1 + u x ^ 2) ^ 2 := by
            field_simp [hden_pos.ne']
    have hsum := htri.trans (add_le_add hfrac1 hfrac2)
    have hnn1 : 0 ≤ 2 * (π + M_Y) * m ^ (-(3 / 2 : ℝ)) := by positivity
    have hnn2 : 0 ≤ 2 * (π + M_Y) ^ 2 * m ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith only [hsum, hnn1, hnn2]
  exact ⟨ht1_hd, ht2_hd, ht1_bd, ht2_bd⟩

/-- **Derivative bounds for `W_1(ζ)` and `θ(ζ)` (`ctl:freeze-derivatives`, second bound):**
for `c' ≥ 10000` and `ζ > 0` (`ε = c'^{-2}`), both `W_1(ζ) = lowerWeps (c'^{-2}) (lowerY (x(ζ)))`
and `θ(ζ) = unwrappedTheta (c'^{-2}) (x(ζ))` are `C^2` with `|f^(j)(ζ)| ≤ C (ζ^{-j} + c'^{-j})` (`j = 1, 2`). -/
theorem lowerWeps_unwrappedTheta_deriv_bounds :
    ∃ C_osc : ℝ, 0 < C_osc ∧ ∀ {c' : ℝ}, 10000 ≤ c' →
      let W1 := fun ζ => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' ζ))
      let θ := fun ζ => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ)
      ∃ W1' W1'' θ' θ'' : ℝ → ℝ, ∀ {ζ : ℝ}, 0 < ζ →
        HasDerivAt W1 (W1' ζ) ζ ∧ HasDerivAt W1' (W1'' ζ) ζ ∧
        HasDerivAt θ (θ' ζ) ζ ∧ HasDerivAt θ' (θ'' ζ) ζ ∧
        |W1' ζ| ≤ C_osc * (ζ⁻¹ + c'⁻¹) ∧
        |W1'' ζ| ≤ C_osc * (ζ ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) ∧
        |θ' ζ| ≤ C_osc * (ζ⁻¹ + c'⁻¹) ∧
        |θ'' ζ| ≤ C_osc * (ζ ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
  obtain ⟨M_W, hMW_nn, hW_x⟩ := lowerWeps_x_deriv_bounds
  obtain ⟨M_θ, hMθ_nn, hmt_x⟩ := thetaMt_x_deriv_bounds
  obtain ⟨M_S2, hMS2_pos, _, hS2_diff, hS2_1, hS2_2, _⟩ := outerS2
  let M_tot : ℝ := max M_W (M_S2 + M_θ)
  have hMtot_nn : 0 ≤ M_tot := le_max_of_le_left hMW_nn
  obtain ⟨C_x, hCx_pos, hx_bounds⟩ := xOfZeta_deriv_bounds
  let C_osc : ℝ := M_tot * max 1 C_x + M_tot * (1 + C_x + C_x ^ 2) + 1
  refine ⟨C_osc, by positivity, fun {c'} hc' => ?_⟩
  have hc0 : 0 < c' := by linarith
  have hε0 : 0 ≤ c' ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  have hε1 : c' ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (c' ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc'])
      _ = 1 / 4 := by norm_num
  obtain ⟨w1, w2, hw_spec⟩ := hW_x hε0 hε1
  obtain ⟨t1, t2, ht_spec⟩ := hmt_x hε0 hε1
  have hW_chain := @zeta_chain_deriv_bounds (fun x => lowerWeps (c' ^ (-2 : ℝ)) (lowerY x))
    w1 w2 M_tot C_x hMtot_nn hCx_pos hx_bounds
    (fun {x} hx => by
      have hm : 0 < min (x - xiStar) 1 := lt_min (sub_pos.mpr hx) one_pos
      have hm1 : 1 ≤ (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hm.le, one_le_inv₀ (Real.rpow_pos_of_pos hm _)]
        exact Real.rpow_le_one hm.le (min_le_right _ _) (by norm_num)
      refine ⟨(hw_spec hx).1, ?_⟩
      calc |w1 x| ≤ M_W := (hw_spec hx).2.2.1
        _ ≤ M_tot := le_max_left _ _
        _ ≤ M_tot * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) :=
            le_mul_of_one_le_right hMtot_nn hm1)
    (fun {x} hx => by
      have hm : 0 < min (x - xiStar) 1 := lt_min (sub_pos.mpr hx) one_pos
      have hm1 : 1 ≤ (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_neg hm.le, one_le_inv₀ (Real.rpow_pos_of_pos hm _)]
        exact Real.rpow_le_one hm.le (min_le_right _ _) (by norm_num)
      refine ⟨(hw_spec hx).2.1, ?_⟩
      calc |w2 x| ≤ M_W := (hw_spec hx).2.2.2
        _ ≤ M_tot := le_max_left _ _
        _ ≤ M_tot * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) :=
            le_mul_of_one_le_right hMtot_nn hm1)
  have hθ_chain := @zeta_chain_deriv_bounds (fun x => unwrappedTheta (c' ^ (-2 : ℝ)) x)
    (fun x => deriv thetaOutX x + t1 x) (fun x => deriv (deriv thetaOutX) x + t2 x)
    M_tot C_x hMtot_nn hCx_pos hx_bounds
    (fun {x} hx => by
      have hx0 : 0 < x := xiStar_pos.trans hx
      have hd_s := (hS2_diff x hx).1.hasDerivAt
      have hd_t := (ht_spec hx).1
      have hsub : HasDerivAt (fun u => thetaOutX u + -2 * Real.arctan (c' ^ (-2 : ℝ) * lowerY u / (slitA u + c' ^ (-2 : ℝ))))
          (deriv thetaOutX x + t1 x) x := hd_s.add hd_t
      have heq : (fun u => thetaOutX u + -2 * Real.arctan (c' ^ (-2 : ℝ) * lowerY u / (slitA u + c' ^ (-2 : ℝ)))) =
          unwrappedTheta (c' ^ (-2 : ℝ)) := by
        ext u; unfold unwrappedTheta; ring
      rw [heq] at hsub
      have hexp1 : Real.exp (-(π * x)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := Real.pi_pos; nlinarith only [this, hx0]
      have hs1_le : |deriv thetaOutX x| ≤ M_S2 * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by
        calc |deriv thetaOutX x|
            ≤ M_S2 * (min (x - xiStar) 1) ^ (-1 / 2 : ℝ) * Real.exp (-(π * x)) := hS2_1 x hx
          _ ≤ M_S2 * (min (x - xiStar) 1) ^ (-1 / 2 : ℝ) * 1 := by gcongr
          _ = M_S2 * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by norm_num
      have h1 : |deriv thetaOutX x + t1 x| ≤
          (M_S2 + M_θ) * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by
        have htri := (abs_add_le _ _).trans (add_le_add hs1_le (ht_spec hx).2.2.1)
        linarith only [htri]
      refine ⟨hsub, h1.trans ?_⟩
      have hnn : 0 ≤ (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (lt_min (sub_pos.mpr hx) one_pos).le _
      gcongr; exact le_max_right _ _)
    (fun {x} hx => by
      have hx0 : 0 < x := xiStar_pos.trans hx
      have hd_s := (hS2_diff x hx).2.hasDerivAt
      have hd_t := (ht_spec hx).2.1
      refine ⟨hd_s.add hd_t, ?_⟩
      have hexp1 : Real.exp (-(π * x)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := Real.pi_pos; nlinarith only [this, hx0]
      have h1 : |deriv (deriv thetaOutX) x| ≤ M_S2 * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by
        calc |deriv (deriv thetaOutX) x|
            ≤ M_S2 * (min (x - xiStar) 1) ^ (-3 / 2 : ℝ) * Real.exp (-(π * x)) := hS2_2 x hx
          _ ≤ M_S2 * (min (x - xiStar) 1) ^ (-3 / 2 : ℝ) * 1 := by gcongr
          _ = M_S2 * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by norm_num
      have htri := (abs_add_le _ _).trans (add_le_add h1 (ht_spec hx).2.2.2)
      calc _ ≤ (M_S2 + M_θ) * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by linarith only [htri]
        _ ≤ M_tot * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by gcongr; exact le_max_right _ _)
  refine ⟨fun ζ => w1 (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ))),
    fun ζ => w2 (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ))) ^ 2 +
      w1 (xOfZeta c' ζ) * (-(4 * rhoUDeriv (xOfZeta c' ζ) / (c' ^ 2 * rhoU (xOfZeta c' ζ) ^ 3))),
    fun ζ => (deriv thetaOutX (xOfZeta c' ζ) + t1 (xOfZeta c' ζ)) * (2 / (c' * rhoU (xOfZeta c' ζ))),
    fun ζ => (deriv (deriv thetaOutX) (xOfZeta c' ζ) + t2 (xOfZeta c' ζ)) * (2 / (c' * rhoU (xOfZeta c' ζ))) ^ 2 +
      (deriv thetaOutX (xOfZeta c' ζ) + t1 (xOfZeta c' ζ)) *
        (-(4 * rhoUDeriv (xOfZeta c' ζ) / (c' ^ 2 * rhoU (xOfZeta c' ζ) ^ 3))),
    fun {ζ} hζ => ?_⟩
  obtain ⟨hWa, hWb, hWc, hWd⟩ := hW_chain hc0 hζ
  obtain ⟨hθa, hθb, hθc, hθd⟩ := hθ_chain hc0 hζ
  exact ⟨hWa, hWb, hθa, hθb, hWc, hWd, hθc, hθd⟩

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerWeps_unwrappedTheta_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerWeps_unwrappedTheta_deriv_bounds
