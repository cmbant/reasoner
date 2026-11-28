module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasBandBridge
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasGrowth
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasResidue
public import FormalResearch.ModularBootstrap.FiveTerm.LowerDyadic

/-!
# Local Strip Boas Positivity (`cts:boas`) — Assembly for `LowerBoas`

Proves the Virasoro local strip Boas lower bound (`cts:boas`):
for `c' ≥ cc` and every macroscopic good radius `R ∈ LowerRadiusRange virasoroC1 c'`,
`lowerBand virasoroProblem Gout virasoroPhi virasoroUhat c' R g ≥ -C c'^{-4/3}`.

* `lowerWeps_exp_decay`: `W_ε(y(x)) ≤ 128 c'⁴ e^{-2πx}` (`ε = c'^{-2}`) uniformly for `x > ξ_*`.
* `boasK_vert_norm_le`: `‖boasK φ₀ (x₀ + y I)‖ ≤ 3 e^{-4πy}` when `dist(x₀ - φ₀, ℤ) ≥ 1/8` and `y ≥ 0`.
* `cumulN_le_sq`: `N(x) ≤ (2/3) x²` for `x ≥ ξ_*`.
* `virasoro_lowerBand_lower_bound`: combines `boas_freezing_estimate` (`ctl:freeze`), `boas_local_lower`
  on `[z - L₀(z), z + L₀(z)] × [0, 2 log c']`, `boasH_growth`, `gauss_top_le`/`gauss_vert_le`, and
  `boas_zeta_to_lowerBand`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.ModularBootstrap.ConcreteBootstrap FixedWeightTip Contour Bessel

noncomputable section

/-! ### 1. Exponential decay of `W_ε` and polynomial-exponential Jacobian integral -/

private lemma lowerWeps_exp_decay {c' x : ℝ} (hc1 : 1 ≤ c') (hx : xiStar < x) :
    lowerWeps (c' ^ (-2 : ℝ)) (lowerY x) ≤ 128 * c' ^ (4 : ℝ) * Real.exp (-(2 * π * x)) := by
  have hc0 : 0 < c' := by linarith
  set ε : ℝ := c' ^ (-2 : ℝ)
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc0 _
  have hε_le1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have ha_pos : 0 < slitA x := slitA_pos x
  have ha_lt1 : slitA x < 1 := slitA_lt_one hx
  have hmt_ge : ε ^ 2 ≤ mtDen ε (slitA x) := by
    unfold mtDen
    have h1 : ε ^ 2 ≤ (slitA x + ε) ^ 2 := by nlinarith only [ha_pos, hε_pos]
    have h2 : 0 ≤ ε ^ 2 * (1 - slitA x) := by nlinarith only [ha_lt1, hε_pos]
    linarith only [h1, h2]
  have ha_le : slitA x ≤ 4 * Real.sqrt 2 * Real.exp (-(π * x)) := by
    unfold slitA
    have hexp_pos : 0 < Real.exp (π * x) := Real.exp_pos _
    have hcosh_ge : Real.exp (π * x) / 2 ≤ Real.cosh (π * x) := by
      rw [Real.cosh_eq]
      have : 0 < Real.exp (-(π * x)) := Real.exp_pos _
      linarith only [this]
    have hden_ge : Real.exp (π * x) / 2 ≤ Real.cosh (π * x) + Real.sqrt 2 := by
      have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith only [hcosh_ge, this]
    rw [div_le_iff₀ (by positivity)]
    calc 2 * Real.sqrt 2 = (4 * Real.sqrt 2 * Real.exp (-(π * x))) * (Real.exp (π * x) / 2) := by
          rw [Real.exp_neg]; field_simp [hexp_pos.ne']; ring
      _ ≤ (4 * Real.sqrt 2 * Real.exp (-(π * x))) * (Real.cosh (π * x) + Real.sqrt 2) := by gcongr
  have ha_sq : slitA x ^ 2 ≤ 32 * Real.exp (-(2 * π * x)) := by
    have hsq : (4 * Real.sqrt 2 * Real.exp (-(π * x))) ^ 2 = 32 * Real.exp (-(2 * π * x)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt zero_le_two, ← Real.exp_nat_mul]
      norm_num; ring_nf
    calc slitA x ^ 2 ≤ (4 * Real.sqrt 2 * Real.exp (-(π * x))) ^ 2 :=
          pow_le_pow_left₀ ha_pos.le ha_le 2
      _ = 32 * Real.exp (-(2 * π * x)) := hsq
  have hε_inv : (ε ^ 2)⁻¹ = c' ^ (4 : ℝ) := by
    dsimp [ε]
    rw [← Real.rpow_natCast (c' ^ (-2 : ℝ)) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_neg hc0.le]
    norm_num
  rw [lowerWeps_eq hε_pos.le hx, div_eq_mul_inv]
  have h1e_sq : (1 + ε) ^ 2 ≤ 4 := by nlinarith only [hε_pos, hε_le1]
  have hmt_pos : 0 < mtDen ε (slitA x) := lt_of_lt_of_le (sq_pos_of_pos hε_pos) hmt_ge
  calc (1 + ε) ^ 2 * slitA x ^ 2 * (mtDen ε (slitA x))⁻¹
      ≤ 4 * (32 * Real.exp (-(2 * π * x))) * (ε ^ 2)⁻¹ := by gcongr
    _ = 128 * c' ^ (4 : ℝ) * Real.exp (-(2 * π * x)) := by rw [hε_inv]; ring

private lemma cumulN_le_sq {x : ℝ} (hx : xiStar ≤ x) : cumulN x ≤ (2 / 3 : ℝ) * x ^ 2 := by
  have hρ_ub : ∀ t ∈ Icc xiStar x, rhoU t ≤ (4 / 3 : ℝ) * t := by
    intro t ht
    rw [rhoU_eq_of_ge ht.1]
    have hpi := Real.pi_pos
    have hxt : 0 < t := xiStar_pos.trans_le ht.1
    have hs_ge1 : 1 ≤ Real.sinh (π * t) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_le_sinh.mpr (by nlinarith only [hpi, ht.1])
    have harc_le : arccoshR (Real.sinh (π * t)) ≤ π * t := by
      unfold arccoshR
      have hsqrt_le : Real.sqrt (Real.sinh (π * t) ^ 2 - 1) ≤ Real.sinh (π * t) :=
        Real.sqrt_le_iff.mpr ⟨by positivity, by linarith⟩
      have harg_pos : 0 < Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1) := by positivity
      have h2s : 2 * Real.sinh (π * t) ≤ Real.exp (π * t) := by
        rw [Real.sinh_eq]
        have : 0 < Real.exp (-(π * t)) := Real.exp_pos _
        linarith only [this]
      calc Real.log (Real.sinh (π * t) + Real.sqrt (Real.sinh (π * t) ^ 2 - 1))
          ≤ Real.log (2 * Real.sinh (π * t)) := Real.log_le_log harg_pos (by linarith only [hsqrt_le])
        _ ≤ Real.log (Real.exp (π * t)) := Real.log_le_log (by positivity) h2s
        _ = π * t := Real.log_exp _
    calc (4 / (3 * π)) * arccoshR (Real.sinh (π * t))
        ≤ (4 / (3 * π)) * (π * t) := by gcongr
      _ = (4 / 3 : ℝ) * t := by field_simp [hpi.ne']
  have hint : IntervalIntegrable rhoU volume xiStar x :=
    (continuousOn_rhoU.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hx
  have hint2 : IntervalIntegrable (fun t : ℝ => (4 / 3 : ℝ) * t) volume xiStar x :=
    (continuous_const.mul continuous_id).continuousOn.intervalIntegrable_of_Icc hx
  have hmono := intervalIntegral.integral_mono_on hx hint hint2 hρ_ub
  have hcalc : ∫ t in xiStar..x, (4 / 3 : ℝ) * t = (2 / 3 : ℝ) * (x ^ 2 - xiStar ^ 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hcalc] at hmono
  unfold cumulN
  have hxi_sq : 0 ≤ xiStar ^ 2 := sq_nonneg xiStar
  have hx_sq : 0 ≤ x ^ 2 := sq_nonneg x
  linarith only [hmono, hxi_sq, hx_sq]

private lemma integral_exp_poly_decay :
    IntegrableOn (fun x : ℝ => (1 + x) ^ 7 * Real.exp (-(2 * π * x))) (Ioi xiStar) ∧
      ∫ x in Ioi xiStar, (1 + x) ^ 7 * Real.exp (-(2 * π * x)) ≤
        (2 : ℝ) ^ 7 * (1 + (Nat.factorial 7 : ℝ) / π ^ 7) / π := by
  have hpi := Real.pi_pos
  let C_p : ℝ := (2 : ℝ) ^ 7 * (1 + (Nat.factorial 7 : ℝ) / π ^ 7)
  have hCp_nn : 0 ≤ C_p := by dsimp [C_p]; positivity
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      (1 + x) ^ 7 * Real.exp (-(2 * π * x)) ≤ C_p * Real.exp (-(π * x)) := by
    intro x hx
    have hx_nn : 0 ≤ x := (mem_Ioi.mp hx).le
    have hexp_fac : x ^ 7 * Real.exp (-(π * x)) ≤ (Nat.factorial 7 : ℝ) / π ^ 7 := by
      have hsum := Real.sum_le_exp_of_nonneg (mul_nonneg hpi.le hx_nn) 8
      have hterm := Finset.single_le_sum (f := fun i => (π * x) ^ i / (Nat.factorial i : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by norm_num : 7 < 8))
      have h7 : (π * x) ^ 7 / (Nat.factorial 7 : ℝ) ≤ Real.exp (π * x) := hterm.trans hsum
      have hfac_pos : (0 : ℝ) < Nat.factorial 7 := Nat.cast_pos.mpr (Nat.factorial_pos 7)
      rw [mul_pow] at h7
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      rw [div_le_iff₀ hfac_pos] at h7
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hpi 7)]
      calc x ^ 7 * π ^ 7 = π ^ 7 * x ^ 7 := by ring
        _ ≤ Real.exp (π * x) * (Nat.factorial 7 : ℝ) := by linarith only [h7]
        _ = (Nat.factorial 7 : ℝ) * Real.exp (π * x) := by ring
    have h1x : (1 + x) ^ 7 ≤ (2 : ℝ) ^ 7 * (1 + x ^ 7) := by
      by_cases hx1 : x ≤ 1
      · have hle : (1 + x) ^ 7 ≤ (2 : ℝ) ^ 7 := pow_le_pow_left₀ (by linarith) (by linarith) 7
        have h1_le : 1 ≤ 1 + x ^ 7 := le_add_of_nonneg_right (pow_nonneg hx_nn 7)
        nlinarith only [hle, h1_le, pow_pos (by norm_num : (0 : ℝ) < 2) 7]
      · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
        have hle : (1 + x) ^ 7 ≤ (2 * x) ^ 7 := pow_le_pow_left₀ (by linarith) (by linarith) 7
        rw [mul_pow] at hle
        have hx7_le : x ^ 7 ≤ 1 + x ^ 7 := by linarith
        nlinarith only [hle, hx7_le, pow_pos (by norm_num : (0 : ℝ) < 2) 7]
    calc (1 + x) ^ 7 * Real.exp (-(2 * π * x))
        = (1 + x) ^ 7 * Real.exp (-(π * x)) * Real.exp (-(π * x)) := by
          rw [show -(2 * π * x) = -(π * x) + -(π * x) by ring, Real.exp_add]; ring
      _ ≤ ((2 : ℝ) ^ 7 * (1 + x ^ 7)) * Real.exp (-(π * x)) * Real.exp (-(π * x)) := by gcongr
      _ = (2 : ℝ) ^ 7 * (Real.exp (-(π * x)) + x ^ 7 * Real.exp (-(π * x))) * Real.exp (-(π * x)) := by ring
      _ ≤ (2 : ℝ) ^ 7 * (1 + (Nat.factorial 7 : ℝ) / π ^ 7) * Real.exp (-(π * x)) := by
          have hexp_le1 : Real.exp (-(π * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          gcongr
  have hint_exp0 : IntegrableOn (fun x : ℝ => Real.exp (-π * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith only [hpi]) 0
  have hint_exp : IntegrableOn (fun x : ℝ => C_p * Real.exp (-(π * x))) (Ioi 0) := by
    have hfun : (fun x : ℝ => C_p * Real.exp (-π * x)) = fun x : ℝ => C_p * Real.exp (-(π * x)) := by
      ext x; ring_nf
    exact hfun ▸ (hint_exp0.const_mul C_p)
  have hint_0 : IntegrableOn (fun x : ℝ => (1 + x) ^ 7 * Real.exp (-(2 * π * x))) (Ioi 0) := by
    refine hint_exp.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by linarith [(mem_Ioi.mp hx).le]) 7) (Real.exp_pos _).le)]
    exact hpt x hx
  have hint_xi : IntegrableOn (fun x : ℝ => (1 + x) ^ 7 * Real.exp (-(2 * π * x))) (Ioi xiStar) :=
    hint_0.mono_set (Ioi_subset_Ioi xiStar_pos.le)
  have hval_exp : ∫ x in Ioi (0 : ℝ), Real.exp (-(π * x)) = π⁻¹ := by
    have hcomp : ∫ x in Ioi (0 : ℝ), Real.exp (-x) = 1 := integral_exp_neg_Ioi_zero
    have hsub := MeasureTheory.integral_comp_mul_left_Ioi (fun u => Real.exp (-u)) 0 hpi
    simp only [mul_zero, smul_eq_mul] at hsub
    rw [hcomp, mul_one] at hsub
    exact hsub
  have hbd_0 : ∫ x in Ioi (0 : ℝ), (1 + x) ^ 7 * Real.exp (-(2 * π * x)) ≤ C_p / π := by
    have hm := MeasureTheory.setIntegral_mono_on hint_0 hint_exp measurableSet_Ioi hpt
    rw [MeasureTheory.integral_const_mul, hval_exp, ← div_eq_mul_inv] at hm
    exact hm
  have hbd_xi : ∫ x in Ioi xiStar, (1 + x) ^ 7 * Real.exp (-(2 * π * x)) ≤
      ∫ x in Ioi (0 : ℝ), (1 + x) ^ 7 * Real.exp (-(2 * π * x)) := by
    refine MeasureTheory.setIntegral_mono_set hint_0 ?_ (ae_of_all _ (Ioi_subset_Ioi xiStar_pos.le))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg (by linarith [(mem_Ioi.mp hx).le]) 7) (Real.exp_pos _).le
  exact ⟨hint_xi, hbd_xi.trans hbd_0⟩

/-! ### 2. Vertical `boasK` bound and Gaussian local contour lower bound -/

private lemma boasK_vert_norm_le (φ₀ x₀ y : ℝ) (hy : 0 ≤ y)
    (hdist : ∀ n : ℤ, (1 / 8 : ℝ) ≤ |x₀ - φ₀ - n|) :
    ‖boasK φ₀ ((x₀ : ℂ) + y * I)‖ ≤ 3 * Real.exp (-(4 * π * y)) := by
  have hqn : ‖boasQ φ₀ ((x₀ : ℂ) + y * I)‖ = Real.exp (-(2 * π * y)) := by
    rw [boasQ_norm]; simp
  set r : ℝ := Real.exp (-(2 * π * y))
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_le1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [Real.pi_pos, hy])
  set t : ℝ := x₀ - φ₀
  have hq_eq : boasQ φ₀ ((x₀ : ℂ) + y * I) = (r : ℂ) * Complex.exp (((2 * π * t : ℝ) : ℂ) * I) := by
    unfold boasQ
    rw [show (2 : ℂ) * (π : ℂ) * I * (((x₀ : ℂ) + y * I) - (φ₀ : ℂ)) =
        ((-(2 * π * y) : ℝ) : ℂ) + (((2 * π * t : ℝ) : ℂ) * I) by
      dsimp [t]; push_cast; ring_nf; simp [Complex.I_sq]; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
  have hnorm_sq : ‖1 - boasQ φ₀ ((x₀ : ℂ) + y * I)‖ ^ 2 =
      (1 - r) ^ 2 + 4 * r * Real.sin (π * t) ^ 2 := by
    rw [hq_eq, Complex.sq_norm, Complex.normSq_apply]
    have hce := Complex.exp_ofReal_mul_I (2 * π * t)
    have hre : (1 - (r : ℂ) * Complex.exp (((2 * π * t : ℝ) : ℂ) * I)).re =
        1 - r * Real.cos (2 * π * t) := by
      rw [hce, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have him : (1 - (r : ℂ) * Complex.exp (((2 * π * t : ℝ) : ℂ) * I)).im =
        -(r * Real.sin (2 * π * t)) := by
      rw [hce, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre, him]
    have hcs : Real.cos (2 * π * t) = 1 - 2 * Real.sin (π * t) ^ 2 := by
      have := Real.cos_two_mul (π * t)
      have hsc := Real.sin_sq_add_cos_sq (π * t)
      rw [show 2 * (π * t) = 2 * π * t by ring] at this
      nlinarith only [this, hsc]
    have hsc2 := Real.sin_sq_add_cos_sq (2 * π * t)
    have halg : (1 - r * Real.cos (2 * π * t)) * (1 - r * Real.cos (2 * π * t)) +
          -(r * Real.sin (2 * π * t)) * -(r * Real.sin (2 * π * t)) =
        1 - 2 * r * Real.cos (2 * π * t) + r ^ 2 * (Real.sin (2 * π * t) ^ 2 + Real.cos (2 * π * t) ^ 2) := by
      ring
    rw [halg, hsc2, mul_one, hcs]
    ring
  have hden_ge : (1 / 3 : ℝ) ≤ ‖1 - boasQ φ₀ ((x₀ : ℂ) + y * I)‖ := by
    by_cases hr_half : r ≤ 1 / 2
    · have h1 : 1 / 2 ≤ ‖(1 : ℂ) - boasQ φ₀ ((x₀ : ℂ) + y * I)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (boasQ φ₀ ((x₀ : ℂ) + y * I))
        rw [norm_one, hqn] at this
        linarith only [this, hr_half]
      linarith only [h1]
    · have hr_gt : 1 / 2 < r := lt_of_not_ge hr_half
      let n : ℤ := round t
      let δ : ℝ := t - n
      have hδ_hi : |δ| ≤ 1 / 2 := abs_sub_round t
      have hδ_lo : 1 / 8 ≤ |δ| := by simpa [δ] using hdist n
      have hsin_eq : |Real.sin (π * t)| = Real.sin (π * |δ|) := by
        have ht_eq : π * t = π * δ + n * π := by dsimp [δ]; ring
        rw [ht_eq, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
        rcases le_or_gt 0 δ with hδ0 | hδ0
        · rw [abs_of_nonneg hδ0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
            (by nlinarith only [Real.pi_pos, hδ0, abs_of_nonneg hδ0 ▸ hδ_hi]))]
        · have hneg : |δ| = -δ := abs_of_neg hδ0
          have hpe : π * δ = -(π * |δ|) := by rw [hneg]; ring
          rw [hpe, Real.sin_neg, abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
            (by positivity) (by nlinarith only [Real.pi_pos, hδ_hi]))]
      have hsin_ge : 1 / 4 ≤ |Real.sin (π * t)| := by
        rw [hsin_eq]
        have hj := Real.mul_le_sin (by positivity : 0 ≤ π * |δ|) (by nlinarith only [Real.pi_pos, hδ_hi])
        have hj2 : 1 / 4 ≤ 2 / π * (π * |δ|) := by
          rw [show 2 / π * (π * |δ|) = 2 * |δ| by field_simp [Real.pi_pos.ne']]
          linarith only [hδ_lo]
        exact hj2.trans hj
      have hsin_sq : 1 / 16 ≤ Real.sin (π * t) ^ 2 := by
        have : (1 / 4 : ℝ) ^ 2 ≤ |Real.sin (π * t)| ^ 2 := pow_le_pow_left₀ (by positivity) hsin_ge 2
        rw [sq_abs] at this
        norm_num at this
        exact this
      have hsq_ge : (1 / 3 : ℝ) ^ 2 ≤ ‖1 - boasQ φ₀ ((x₀ : ℂ) + y * I)‖ ^ 2 := by
        rw [hnorm_sq]
        have h1r : 0 ≤ (1 - r) ^ 2 := sq_nonneg _
        nlinarith only [h1r, hr_gt, hsin_sq]
      nlinarith only [hsq_ge, norm_nonneg (1 - boasQ φ₀ ((x₀ : ℂ) + y * I))]
  unfold boasK
  rw [norm_div, norm_pow, hqn, ← Real.exp_nat_mul]
  have hexp_eq : Real.exp ((2 : ℕ) * -(2 * π * y)) = Real.exp (-(4 * π * y)) := by
    congr 1; push_cast; ring
  rw [hexp_eq]
  have hden_pos : 0 < ‖1 - boasQ φ₀ ((x₀ : ℂ) + y * I)‖ := by linarith only [hden_ge]
  calc Real.exp (-(4 * π * y)) / ‖1 - boasQ φ₀ ((x₀ : ℂ) + y * I)‖
      ≤ Real.exp (-(4 * π * y)) / (1 / 3 : ℝ) := by gcongr
    _ = 3 * Real.exp (-(4 * π * y)) := by ring

private lemma boas_local_frozen_lower :
    ∃ c_L C_L : ℝ, max virasoroCQEnv 10000 ≤ c_L ∧ 0 < C_L ∧
      ∀ {c' T R : ℝ} {g : ℝ → ℝ}, c_L ≤ c' →
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        T ≤ virasoroDeltaChart c' (-virasoroAThr) →
        LowerRadiusRange virasoroC1 c' R →
        ∀ {z : ℝ}, boasZetaStar c' ≤ z →
          -(C_L * Real.sqrt (Real.log c') *
              (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) *
              lowerPζ c' R z * (1 + xOfZeta c' z) ^ 6 * Real.exp (-(2 * π * xOfZeta c' z))) ≤
            boasFrozenInt c' R (fun ζ => (boasH c' g (ζ : ℂ)).re) z := by
  obtain ⟨c_hg, C_hg, hc_hg10, hChg_pos, h_growth⟩ := boasH_growth
  obtain ⟨c_hr, hc_hr10, hhr⟩ := boasH_ofReal_nonneg
  obtain ⟨c_T, C_P, hcT_tap, _, hPζ_props⟩ := lowerPζ_properties
  let K_g : ℝ := 1 / Real.sqrt (2 * π)
  let C_top : ℝ := 36 * K_g * C_hg * 8
  let C_vert : ℝ := 6 * K_g * C_hg * 8
  let C_L : ℝ := 2 * 128 * (C_top + 2 * C_vert)
  let c_L0 : ℝ := max (max c_hg c_hr) (max c_T (max virasoroCQEnv 10000))
  refine ⟨c_L0, C_L, (le_max_right _ _).trans (le_max_right _ _),
    by positivity, fun {c' T R g} hc' hwf hT_hi hR {z} hz => ?_⟩
  have hc_hg : c_hg ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc_hr : c_hr ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc_T : c_T ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc10000 : 10000 ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc0 : 0 < c' := by linarith only [hc10000]
  have hc1 : 1 < c' := by linarith only [hc10000]
  have hlog_ge1 : 1 ≤ Real.log c' := by
    have hexp_le : Real.exp 1 ≤ c' := (Real.exp_one_lt_d9.le).trans (by linarith only [hc10000])
    exact (Real.le_log_iff_exp_le hc0).mpr hexp_le
  have hlog_half : (1 / 2 : ℝ) ≤ Real.log c' := by linarith only [hlog_ge1]
  have hL_le_9log : 8 * Real.log c' + 1 / 2 ≤ 9 * Real.log c' := by linarith only [hlog_ge1]
  have hexp_h : Real.exp (-(4 * π * Real.log c')) ≤ 1 / 2 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.sum_le_exp_of_nonneg zero_le_one 2
      norm_num [Finset.sum_range_succ] at this
      exact this
    have hexp_ge4 : 1 ≤ 4 * π * Real.log c' := by nlinarith only [Real.pi_gt_d2, hlog_ge1]
    calc Real.exp (-(4 * π * Real.log c'))
        ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith only [hexp_ge4])
      _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
      _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by positivity) h2e
      _ = 1 / 2 := by norm_num
  have h8_le_c4 : 8 * Real.log c' + 1 / 2 ≤ c' / 4 := by
    have hsq_ge : 100 ≤ Real.sqrt c' :=
      Real.le_sqrt_of_sq_le (by linarith only [hc10000])
    have hsq_pos : 0 < Real.sqrt c' := by linarith only [hsq_ge]
    have hlog_sq : Real.log c' ≤ 2 * Real.sqrt c' := by
      have heq : c' = Real.sqrt c' ^ (2 : ℕ) := (Real.sq_sqrt hc0.le).symm
      have h1 : Real.log (Real.sqrt c') ≤ Real.sqrt c' - 1 := Real.log_le_sub_one_of_pos hsq_pos
      calc Real.log c' = Real.log (Real.sqrt c' ^ (2 : ℕ)) := by conv_lhs => rw [heq]
        _ = 2 * Real.log (Real.sqrt c') := by rw [Real.log_pow]; norm_num
        _ ≤ 2 * (Real.sqrt c' - 1) := by linarith only [h1]
        _ ≤ 2 * Real.sqrt c' := by linarith only
    have hsq_ub : 100 * Real.sqrt c' ≤ c' := by
      calc 100 * Real.sqrt c' ≤ Real.sqrt c' * Real.sqrt c' := by gcongr
        _ = c' := Real.mul_self_sqrt hc0.le
    linarith only [hlog_sq, hsq_ub, hc10000]
  have hc0 : 0 < c' := by linarith only [hc10000]
  have hc1 : 1 < c' := by linarith only [hc10000]
  have hzmin_pos : 0 < zetaMin c' := zetaMin_pos hc0
  have hlog_pos : 0 < Real.log c' := Real.log_pos hc1
  have hz_pos : 0 < z := by
    have : boasZetaStar c' = zetaMin c' + 8 * Real.log c' + 1 := rfl
    linarith only [hz, hzmin_pos, hlog_pos, this]
  -- Rectangle parameters
  let φ₀ : ℝ := boasPhi0 c' z
  let L₀ : ℝ := goodL0 c' (boasPhi0 c') z
  let H : ℝ := 2 * Real.log c'
  have hH_pos : 0 < H := by dsimp [H]; positivity
  obtain ⟨hL_lo, hL_hi, hpole_R, hpole_L⟩ := goodL0_bounds_and_poles c' (boasPhi0 c') z
  have hL_pos : 0 < L₀ := by dsimp [L₀]; linarith only [hL_lo, hlog_pos]
  have hL_le9 : L₀ ≤ 9 * Real.log c' := hL_hi.trans hL_le_9log
  have h_re_min : zetaMin c' ≤ z - L₀ := by
    have : boasZetaStar c' = zetaMin c' + 8 * Real.log c' + 1 := rfl
    linarith only [hz, hL_hi, this]
  have hab : z - L₀ < z + L₀ := by linarith only [hL_pos]
  -- Complex Gaussian-weighted Boas integrand on `U = {ζ | (3/8) zetaMin c' < Re ζ ∧ |Im ζ| < (c'/3) xiStar}`
  let W_g : ℝ := Real.sqrt (2 * Real.log c')
  have hW_pos : 0 < W_g := Real.sqrt_pos.mpr (by positivity)
  have hW_sq : W_g ^ 2 = 2 * Real.log c' := Real.sq_sqrt (by positivity)
  let gaussC : ℂ → ℂ := fun ζ =>
    Complex.exp (-((ζ - (z : ℂ)) ^ 2) / (2 * (W_g : ℂ) ^ 2)) /
      ((Real.sqrt (2 * π) * W_g : ℝ) : ℂ)
  let gz : ℂ → ℂ := fun ζ => gaussC ζ * boasH c' g ζ
  let U : Set ℂ := {ζ : ℂ | (3 / 8 : ℝ) * zetaMin c' < ζ.re ∧ |ζ.im| < (c' / 3) * xiStar}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hU_sub : U ⊆ zetaStrip c' := fun ζ hζ =>
    ⟨lt_trans (by positivity) hζ.1, hζ.2⟩
  have hrect_sub_U : (Icc (z - L₀) (z + L₀)) ×ℂ (Icc 0 H) ⊆ U := by
    intro ζ hζ
    refine ⟨?_, ?_⟩
    · have h1 : (3 / 8 : ℝ) * zetaMin c' < zetaMin c' := by linarith only [hzmin_pos]
      exact h1.trans_le (h_re_min.trans hζ.1.1)
    · have h_abs : |ζ.im| ≤ H := abs_le.mpr ⟨by linarith only [hζ.2.1, hH_pos], hζ.2.2⟩
      exact h_abs.trans_lt (two_log_lt_zetaStrip hc10000)
  have hgz_diff : DifferentiableOn ℂ gz U := by
    have hgc : Differentiable ℂ gaussC := by
      unfold gaussC; fun_prop
    exact hgc.differentiableOn.mul ((differentiableOn_boasH (by linarith only [hc10000]) hwf.1).mono hU_sub)
  have hgaussC_real : ∀ u : ℝ, gaussC (u : ℂ) = ((gaussW c' (z - u) : ℝ) : ℂ) := by
    intro u
    rw [← gaussW_symm c' (z - u), show -(z - u) = u - z by ring]
    dsimp [gaussC, gaussW]
    have harg : -(((u : ℂ) - (z : ℂ)) ^ 2) / (2 * (W_g : ℂ) ^ 2) =
        ((-(u - z) ^ 2 / (2 * (2 * Real.log c')) : ℝ) : ℂ) := by
      rw [show (W_g : ℂ) ^ 2 = ((W_g ^ 2 : ℝ) : ℂ) by push_cast; ring, hW_sq]
      push_cast; ring
    rw [harg, ← Complex.ofReal_exp]
    push_cast; rfl
  have hgz_real_eq : ∀ {u : ℝ}, z - L₀ ≤ u →
      (gz (u : ℂ)).re = gaussW c' (z - u) * (boasH c' g (u : ℂ)).re ∧ (gz (u : ℂ)).im = 0 := by
    intro u hu
    have hu_q : (1 / 4 : ℝ) * zetaMin c' ≤ u := by linarith only [hzmin_pos, h_re_min, hu]
    obtain ⟨hHim, _⟩ := hhr hc_hr hwf hT_hi hu_q
    have hH_eq : boasH c' g (u : ℂ) = (((boasH c' g (u : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hHim
    have hgz_eq : gz (u : ℂ) = ((gaussW c' (z - u) * (boasH c' g (u : ℂ)).re : ℝ) : ℂ) := by
      dsimp [gz]
      rw [hgaussC_real u]
      conv_lhs => rhs; rw [hH_eq]
      rw [← Complex.ofReal_mul]
    rw [hgz_eq, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨rfl, rfl⟩
  have hgz_real : ∀ u ∈ Icc (z - L₀) (z + L₀), (gz (u : ℂ)).im = 0 := fun u hu =>
    (hgz_real_eq hu.1).2
  have ha_ne : ∀ n : ℤ, (n : ℝ) + φ₀ ≠ z - L₀ := by
    intro n heq
    have h1 := hpole_L n
    have h2 : z - L₀ - φ₀ - n = 0 := by linarith only [heq]
    rw [h2, abs_zero] at h1
    linarith only [h1]
  have hb_ne : ∀ n : ℤ, (n : ℝ) + φ₀ ≠ z + L₀ := by
    intro n heq
    have h1 := hpole_R n
    have h2 : z + L₀ - φ₀ - n = 0 := by linarith only [heq]
    rw [h2, abs_zero] at h1
    linarith only [h1]
  have hgz_poles : ∀ n : ℤ, z - L₀ < (n : ℝ) + φ₀ → (n : ℝ) + φ₀ < z + L₀ →
      0 ≤ (gz (((n : ℝ) + φ₀ : ℝ) : ℂ)).re := by
    intro n hlo _
    rw [(hgz_real_eq hlo.le).1]
    have hu_q : (1 / 4 : ℝ) * zetaMin c' ≤ (n : ℝ) + φ₀ := by linarith only [hzmin_pos, h_re_min, hlo]
    exact mul_nonneg (gaussW_nonneg c' _) (hhr hc_hr hwf hT_hi hu_q).2
  -- Growth bound on the rectangle `Icc (z - L₀) (z + L₀) ×ℂ Icc 0 H`
  set x : ℝ := xOfZeta c' z
  obtain ⟨hx_gt, hcum_eq, _⟩ := xOfZeta_spec hc0 hz_pos
  have hx_pos : 0 < x := xiStar_pos.trans hx_gt
  have h_poly_norm : ∀ {ζ : ℂ}, ζ ∈ (Icc (z - L₀) (z + L₀)) ×ℂ (Icc 0 H) →
      ‖1 + ζ / (c' : ℂ)‖ ^ 3 ≤ 8 * (1 + x) ^ 6 := by
    intro ζ hζ
    have hre_pos : 0 < ζ.re := by linarith only [hzmin_pos, h_re_min, hζ.1.1]
    have hre_ub : |ζ.re| ≤ z + L₀ := by
      rw [abs_of_pos hre_pos]; exact hζ.1.2
    have him_ub : |ζ.im| ≤ H := abs_le.mpr ⟨by linarith only [hζ.2.1, hH_pos], hζ.2.2⟩
    have hnorm_ζ : ‖ζ‖ ≤ z + L₀ + H := by
      calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
        _ ≤ z + L₀ + H := add_le_add hre_ub him_ub
    have hz_ub : z ≤ (2 / 3 : ℝ) * c' * x ^ 2 := by
      rw [← hcum_eq]
      have := cumulN_le_sq hx_gt.le
      nlinarith only [this, hc0]
    have hLH_ub : L₀ + H ≤ c' / 2 := by
      have : L₀ + H ≤ 8 * Real.log c' + 1 / 2 + 2 * Real.log c' := by
        dsimp [H]; linarith only [hL_hi]
      -- Note `8 log c' + 1/2 ≤ c'/4` gives `2 log c' ≤ c'/16`, so `L₀ + H ≤ c'/2`
      linarith only [hL_hi, h8_le_c4, hc10000, show 2 * Real.log c' ≤ c' / 16 by linarith only [h8_le_c4]]
    have h1ζ : ‖1 + ζ / (c' : ℂ)‖ ≤ 2 * (1 + x) ^ 2 := by
      have htri : ‖1 + ζ / (c' : ℂ)‖ ≤ 1 + ‖ζ‖ / c' := by
        calc ‖(1 : ℂ) + ζ / (c' : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖ζ / (c' : ℂ)‖ := norm_add_le _ _
          _ = 1 + ‖ζ‖ / c' := by rw [norm_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      have hdiv : ‖ζ‖ / c' ≤ (2 / 3 : ℝ) * x ^ 2 + 1 / 2 := by
        rw [div_le_iff₀ hc0]
        calc ‖ζ‖ ≤ z + (L₀ + H) := by linarith only [hnorm_ζ]
          _ ≤ (2 / 3 : ℝ) * c' * x ^ 2 + c' / 2 := add_le_add hz_ub hLH_ub
          _ = ((2 / 3 : ℝ) * x ^ 2 + 1 / 2) * c' := by ring
      have hx_sq : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith only [hx_pos]
      have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
      linarith only [htri, hdiv, hx_sq, hx2]
    have h1ζ_nn : 0 ≤ ‖1 + ζ / (c' : ℂ)‖ := norm_nonneg _
    calc ‖1 + ζ / (c' : ℂ)‖ ^ 3 ≤ (2 * (1 + x) ^ 2) ^ 3 := pow_le_pow_left₀ h1ζ_nn h1ζ 3
      _ = 8 * (1 + x) ^ 6 := by ring
  have hgz_rect_growth : ∀ {ζ : ℂ}, ζ ∈ (Icc (z - L₀) (z + L₀)) ×ℂ (Icc 0 H) →
      ‖boasH c' g ζ‖ ≤ C_hg * c' ^ 2 * (8 * (1 + x) ^ 6) * Real.exp (2 * π * |ζ.im|) := by
    intro ζ hζ
    have hre_ge : (3 / 8 : ℝ) * zetaMin c' ≤ ζ.re := by linarith only [hzmin_pos, h_re_min, hζ.1.1]
    have him_le : |ζ.im| ≤ 2 * Real.log c' := abs_le.mpr ⟨by linarith only [hζ.2.1, hH_pos], hζ.2.2⟩
    have hg := (h_growth hc_hg hwf.1 hwf.2.1 hre_ge him_le).2
    calc ‖boasH c' g ζ‖
        ≤ C_hg * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 * Real.exp (2 * π * |ζ.im|) := hg
      _ ≤ C_hg * c' ^ 2 * (8 * (1 + x) ^ 6) * Real.exp (2 * π * |ζ.im|) := by
          gcongr; exact h_poly_norm hζ
  -- Top edge bound
  have hTop_bd : ‖boasTop gz φ₀ (z - L₀) (z + L₀) H‖ ≤
      C_top * Real.sqrt (Real.log c') * c' ^ (3 - 4 * π) * (1 + x) ^ 6 := by
    let M_top : ℝ := (K_g * c' / W_g) * (C_hg * c' ^ 2 * (8 * (1 + x) ^ 6) * Real.exp (2 * π * H))
    have hM_top_spec : ∀ u : ℝ, z - L₀ ≤ u → u ≤ z + L₀ → ‖gz ((u : ℂ) + H * I)‖ ≤ M_top := by
      intro u hu_lo hu_hi
      have hmem : (u : ℂ) + H * I ∈ (Icc (z - L₀) (z + L₀)) ×ℂ (Icc 0 H) := by
        refine ⟨?_, ?_⟩ <;> simp [hu_lo, hu_hi, hH_pos.le]
      have hgc_top : ‖gaussC ((u : ℂ) + H * I)‖ ≤ K_g * c' / W_g := by
        dsimp [gaussC, K_g]
        have hdiff : ((u : ℂ) + H * I) - (z : ℂ) = (((u - z : ℝ) : ℂ) + (H : ℂ) * I) := by
          push_cast; ring
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) hW_pos),
          hdiff]
        have hgt_eq : Real.exp (H ^ 2 / (2 * W_g ^ 2)) = c' := by
          dsimp [H]; rw [hW_sq]; exact (gauss_window_exponents hc1).2.1
        have hgt : ‖Complex.exp (-(((u - z : ℝ) : ℂ) + (H : ℂ) * I) ^ 2 / (2 * (W_g : ℂ) ^ 2))‖ ≤ c' :=
          (gauss_top_le (u - z) H W_g).trans_eq hgt_eq
        calc ‖Complex.exp (-(((u - z : ℝ) : ℂ) + (H : ℂ) * I) ^ 2 / (2 * (W_g : ℂ) ^ 2))‖ /
              (Real.sqrt (2 * π) * W_g)
            ≤ c' / (Real.sqrt (2 * π) * W_g) := div_le_div_of_nonneg_right hgt (by positivity)
          _ = 1 / Real.sqrt (2 * π) * c' / W_g := by ring
      have hH_growth : ‖boasH c' g ((u : ℂ) + H * I)‖ ≤
          C_hg * c' ^ 2 * (8 * (1 + x) ^ 6) * Real.exp (2 * π * H) := by
        have h1 := hgz_rect_growth hmem
        simpa [abs_of_pos hH_pos] using h1
      dsimp [gz]
      rw [norm_mul]
      exact mul_le_mul hgc_top hH_growth (norm_nonneg _) (by positivity)
    have hq_top : Real.exp (-(2 * π * H)) ≤ 1 / 2 := by
      dsimp [H]; rwa [show -(2 * π * (2 * Real.log c')) = -(4 * π * Real.log c') by ring]
    have htop := boasTop_norm_le gz φ₀ (z - L₀) (z + L₀) H M_top hab.le hq_top hM_top_spec
    have hexp_H_plus : Real.exp (2 * π * H) = c' ^ (4 * π) := by
      dsimp [H]; rw [Real.rpow_def_of_pos hc0]; congr 1; ring
    have hexp_H_minus : Real.exp (-(4 * π * H)) = c' ^ (-(8 * π)) := by
      dsimp [H]; rw [Real.rpow_def_of_pos hc0]; congr 1; ring
    have hpow_tot : c' * c' ^ 2 * c' ^ (4 * π) * c' ^ (-(8 * π)) = c' ^ (3 - 4 * π) := by
      rw [show c' * c' ^ 2 = c' ^ (3 : ℝ) by norm_cast; ring, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
      congr 1; ring
    have hL_ratio : (z + L₀) - (z - L₀) ≤ 18 * Real.log c' := by linarith only [hL_le9]
    have hlog_sqrt : Real.log c' / W_g ≤ Real.sqrt (Real.log c') := by
      dsimp [W_g]
      rw [Real.sqrt_mul zero_le_two, div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr zero_lt_two) (Real.sqrt_pos.mpr hlog_pos))]
      have h12 : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
      calc Real.log c' = Real.sqrt (Real.log c') * Real.sqrt (Real.log c') :=
            (Real.mul_self_sqrt hlog_pos.le).symm
        _ ≤ Real.sqrt (Real.log c') * (Real.sqrt 2 * Real.sqrt (Real.log c')) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.sqrt_nonneg _) h12) (Real.sqrt_nonneg _)
    calc ‖boasTop gz φ₀ (z - L₀) (z + L₀) H‖
        ≤ 2 * M_top * Real.exp (-(4 * π * H)) * ((z + L₀) - (z - L₀)) := htop
      _ ≤ 2 * M_top * Real.exp (-(4 * π * H)) * (18 * Real.log c') := by
          gcongr
      _ = 36 * K_g * C_hg * 8 * (Real.log c' / W_g) *
            (c' * c' ^ 2 * c' ^ (4 * π) * c' ^ (-(8 * π))) * (1 + x) ^ 6 := by
          dsimp [M_top]; rw [hexp_H_plus, hexp_H_minus]; ring
      _ ≤ C_top * Real.sqrt (Real.log c') * c' ^ (3 - 4 * π) * (1 + x) ^ 6 := by
          dsimp [C_top]; rw [hpow_tot]
          gcongr
  -- Vertical edge bound template for `x₀ = z ± L₀`
  have hVert_bd : ∀ {x₀ : ℝ}, (x₀ = z + L₀ ∨ x₀ = z - L₀) →
      (∀ n : ℤ, (1 / 8 : ℝ) ≤ |x₀ - φ₀ - n|) →
      ‖boasVert gz φ₀ x₀ H‖ ≤
        C_vert * Real.sqrt (Real.log c') * c' ^ (-13 : ℝ) * (1 + x) ^ 6 := by
    intro x₀ hx₀ hdist
    let C_v : ℝ := 3 * (K_g * c' ^ (-15 : ℝ) / W_g) * (C_hg * c' ^ 2 * (8 * (1 + x) ^ 6))
    have hCv_spec : ∀ y : ℝ, 0 ≤ y → y ≤ H →
        ‖gz ((x₀ : ℂ) + y * I) * boasK φ₀ ((x₀ : ℂ) + y * I)‖ ≤ C_v := by
      intro y hy0 hyH
      have hx₀_mem : x₀ ∈ Icc (z - L₀) (z + L₀) := by
        rcases hx₀ with rfl | rfl <;> exact ⟨by linarith only [hL_pos], by linarith only [hL_pos]⟩
      have hmem : (x₀ : ℂ) + y * I ∈ (Icc (z - L₀) (z + L₀)) ×ℂ (Icc 0 H) := by
        refine ⟨?_, ?_⟩ <;> simp [hx₀_mem.1, hx₀_mem.2, hy0, hyH]
      have hgc_vert : ‖gaussC ((x₀ : ℂ) + y * I)‖ ≤ K_g * c' ^ (-15 : ℝ) / W_g := by
        dsimp [gaussC, K_g]
        have hdiff : ((x₀ : ℂ) + y * I) - (z : ℂ) = (((x₀ - z : ℝ) : ℂ) + (y : ℂ) * I) := by
          push_cast; ring
        have h_abs : L₀ ≤ |x₀ - z| := by
          rcases hx₀ with rfl | rfl
          · rw [show z + L₀ - z = L₀ by ring, abs_of_pos hL_pos]
          · rw [show z - L₀ - z = -L₀ by ring, abs_neg, abs_of_pos hL_pos]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) hW_pos),
          hdiff]
        have hgv_ub : Real.exp (-(L₀ ^ 2 - H ^ 2) / (2 * W_g ^ 2)) ≤ c' ^ (-15 : ℝ) := by
          dsimp [H]
          rw [hW_sq, neg_div]
          refine (Real.exp_le_exp.mpr ?_).trans_eq (gauss_window_exponents hc1).2.2
          have hsq : (8 * Real.log c') ^ 2 ≤ L₀ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hL_lo 2
          exact neg_le_neg (div_le_div_of_nonneg_right (by linarith only [hsq]) (by positivity))
        have hgv := (gauss_vert_le (x₀ - z) y H L₀ W_g hyH hy0 h_abs hL_pos.le).trans hgv_ub
        calc ‖Complex.exp (-(((x₀ - z : ℝ) : ℂ) + (y : ℂ) * I) ^ 2 / (2 * (W_g : ℂ) ^ 2))‖ /
              (Real.sqrt (2 * π) * W_g)
            ≤ c' ^ (-15 : ℝ) / (Real.sqrt (2 * π) * W_g) := div_le_div_of_nonneg_right hgv (by positivity)
          _ = 1 / Real.sqrt (2 * π) * c' ^ (-15 : ℝ) / W_g := by ring
      have hHy := hgz_rect_growth hmem
      simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, abs_of_nonneg hy0] at hHy
      have hKy := boasK_vert_norm_le φ₀ x₀ y hy0 hdist
      have hexp_cancel : Real.exp (2 * π * y) * Real.exp (-(4 * π * y)) ≤ 1 := by
        rw [← Real.exp_add, show 2 * π * y + -(4 * π * y) = -(2 * π * y) by ring]
        exact Real.exp_le_one_iff.mpr (by nlinarith only [Real.pi_pos, hy0])
      rw [norm_mul, norm_mul]
      calc ‖gaussC ((x₀ : ℂ) + y * I)‖ * ‖boasH c' g ((x₀ : ℂ) + y * I)‖ *
            ‖boasK φ₀ ((x₀ : ℂ) + y * I)‖
          ≤ (K_g * c' ^ (-15 : ℝ) / W_g) *
              (C_hg * c' ^ 2 * (8 * (1 + x) ^ 6) * Real.exp (2 * π * y)) *
              (3 * Real.exp (-(4 * π * y))) := by
            gcongr
        _ = C_v * (Real.exp (2 * π * y) * Real.exp (-(4 * π * y))) := by dsimp [C_v]; ring
        _ ≤ C_v * 1 := by gcongr
        _ = C_v := mul_one _
    have hv := boasVert_norm_le gz φ₀ x₀ H C_v hH_pos.le hCv_spec
    have hH_div : H / W_g ≤ 2 * Real.sqrt (Real.log c') := by
      dsimp [H, W_g]
      have hw_sq : Real.sqrt (2 * Real.log c') * Real.sqrt (2 * Real.log c') = 2 * Real.log c' :=
        Real.mul_self_sqrt (by positivity)
      conv_lhs => lhs; rw [← hw_sq]
      rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (by positivity)).ne', Real.sqrt_mul zero_le_two]
      have hsq2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      gcongr
    have hpow_v : c' ^ (-15 : ℝ) * c' ^ 2 = c' ^ (-13 : ℝ) := by
      rw [show c' ^ (2 : ℕ) = c' ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hc0]
      congr 1; norm_num
    calc ‖boasVert gz φ₀ x₀ H‖
        ≤ C_v * H := hv
      _ = 3 * K_g * C_hg * 8 * (H / W_g) * (c' ^ (-15 : ℝ) * c' ^ 2) * (1 + x) ^ 6 := by
          dsimp [C_v]; ring
      _ ≤ 3 * K_g * C_hg * 8 * (2 * Real.sqrt (Real.log c')) * c' ^ (-13 : ℝ) * (1 + x) ^ 6 := by
          rw [hpow_v]; gcongr
      _ = C_vert * Real.sqrt (Real.log c') * c' ^ (-13 : ℝ) * (1 + x) ^ 6 := by
          dsimp [C_vert]; ring
  have hRight_bd := hVert_bd (Or.inl rfl) hpole_R
  have hLeft_bd := hVert_bd (Or.inr rfl) hpole_L
  -- Combine with `boas_local_lower` and `boasA_eq_cos`
  have hlocal := boas_local_lower gz φ₀ (z - L₀) (z + L₀) H hab hH_pos hU_open hgz_diff
    hrect_sub_U hgz_real ha_ne hb_ne hgz_poles
  have hosc_eq : ∫ ζ in (z - L₀)..(z + L₀), (gz (ζ : ℂ)).re * (1 + 2 * Real.cos (2 * π * (ζ - φ₀))) =
      ∫ ζ in (z - L₀)..(z + L₀),
        gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re * (1 + 2 * Real.cos (2 * π * (ζ - φ₀))) := by
    refine intervalIntegral.integral_congr fun ζ hζ => ?_
    rw [uIcc_of_le hab.le] at hζ
    rw [(hgz_real_eq hζ.1).1]
  rw [hosc_eq] at hlocal
  -- Nonnegativity of `(1 - W₀) * gaussW * h` on `[z - L₀, z + L₀]`
  set W₀ : ℝ := lowerWeps (c' ^ (-2 : ℝ)) (lowerY x)
  have hW₀_mem : W₀ ∈ Icc (0 : ℝ) 1 := lowerWeps_mem_Icc (Real.rpow_nonneg hc0.le (-2)) hx_gt
  have hPζ_nn : 0 ≤ lowerPζ c' R z := by
    have hz_half : zetaMin c' / 2 ≤ z := by linarith only [hzmin_pos, h_re_min, hL_pos]
    obtain ⟨_, _, _, hP_spec, _⟩ := hPζ_props hc_T hR
    exact (hP_spec hz_half).1.le
  have h_sub_nn : 0 ≤ ∫ ζ in (z - L₀)..(z + L₀),
      (1 - W₀) * (gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re) := by
    refine intervalIntegral.integral_nonneg hab.le fun ζ hζ => ?_
    have hq : (1 / 4 : ℝ) * zetaMin c' ≤ ζ := by linarith only [hzmin_pos, h_re_min, hζ.1]
    exact mul_nonneg (by linarith only [hW₀_mem.2])
      (mul_nonneg (gaussW_nonneg c' _) (hhr hc_hr hwf hT_hi hq).2)
  have h_gaussH_int : IntervalIntegrable (fun ζ => gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re)
      volume (z - L₀) (z + L₀) := by
    have hcont : ContinuousOn (fun ζ => gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re) (Icc (z - L₀) (z + L₀)) := by
      have hg_c : ContinuousOn (fun ζ => gaussW c' (z - ζ)) (Icc (z - L₀) (z + L₀)) := by
        unfold gaussW; fun_prop
      have hH_c : ContinuousOn (fun ζ : ℝ => (boasH c' g (ζ : ℂ)).re) (Icc (z - L₀) (z + L₀)) := by
        have hm : MapsTo (fun ζ : ℝ => (ζ : ℂ)) (Icc (z - L₀) (z + L₀)) U :=
          fun ζ hζ => hrect_sub_U ⟨hζ, ⟨le_rfl, hH_pos.le⟩⟩
        exact Complex.continuous_re.comp_continuousOn
          ((differentiableOn_boasH (by linarith only [hc10000]) hwf.1).continuousOn.comp
            Complex.continuous_ofReal.continuousOn (hm.mono Subset.rfl hU_sub))
      exact hg_c.mul hH_c
    exact hcont.intervalIntegrable_of_Icc hab.le
  have h_osc_int : IntervalIntegrable
      (fun ζ => gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re * (1 + 2 * Real.cos (2 * π * (ζ - φ₀))))
      volume (z - L₀) (z + L₀) := by
    have hcos : Continuous (fun ζ : ℝ => 1 + 2 * Real.cos (2 * π * (ζ - φ₀))) := by fun_prop
    exact h_gaussH_int.mul_continuousOn hcos.continuousOn
  have hfrozen_eq : boasFrozenInt c' R (fun ζ => (boasH c' g (ζ : ℂ)).re) z =
      lowerPζ c' R z * ((1 - W₀) * (∫ ζ in (z - L₀)..(z + L₀), gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re) +
        W₀ * (∫ ζ in (z - L₀)..(z + L₀),
          gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re * (1 + 2 * Real.cos (2 * π * (ζ - φ₀))))) := by
    unfold boasFrozenInt
    dsimp [L₀, φ₀, W₀, x]
    rw [← intervalIntegral.integral_const_mul (1 - lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))),
      ← intervalIntegral.integral_const_mul (lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))),
      ← intervalIntegral.integral_add (h_gaussH_int.const_mul _) (h_osc_int.const_mul _),
      ← intervalIntegral.integral_const_mul (lowerPζ c' R z)]
    refine intervalIntegral.integral_congr fun ζ _ => ?_
    rw [boasA_eq_cos c' R ζ z hz_pos]
    dsimp [φ₀, boasPhi0]
    ring
  have hEdge_tot : ‖boasTop gz φ₀ (z - L₀) (z + L₀) H‖ +
      ‖boasVert gz φ₀ (z + L₀) H‖ + ‖boasVert gz φ₀ (z - L₀) H‖ ≤
      (C_top + 2 * C_vert) * Real.sqrt (Real.log c') *
        (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6 := by
    have hsq_nn : 0 ≤ Real.sqrt (Real.log c') := Real.sqrt_nonneg _
    have hpow_nn1 : 0 ≤ c' ^ (3 - 4 * π) := Real.rpow_nonneg hc0.le _
    have hpow_nn2 : 0 ≤ c' ^ (-13 : ℝ) := Real.rpow_nonneg hc0.le _
    have hx6_nn : 0 ≤ (1 + x) ^ 6 := by positivity
    calc ‖boasTop gz φ₀ (z - L₀) (z + L₀) H‖ +
          ‖boasVert gz φ₀ (z + L₀) H‖ + ‖boasVert gz φ₀ (z - L₀) H‖
        ≤ C_top * Real.sqrt (Real.log c') * c' ^ (3 - 4 * π) * (1 + x) ^ 6 +
            C_vert * Real.sqrt (Real.log c') * c' ^ (-13 : ℝ) * (1 + x) ^ 6 +
            C_vert * Real.sqrt (Real.log c') * c' ^ (-13 : ℝ) * (1 + x) ^ 6 :=
          add_le_add (add_le_add hTop_bd hRight_bd) hLeft_bd
      _ ≤ (C_top + 2 * C_vert) * Real.sqrt (Real.log c') *
            (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6 := by
          have h1 : C_top * Real.sqrt (Real.log c') * c' ^ (3 - 4 * π) * (1 + x) ^ 6 ≤
              C_top * Real.sqrt (Real.log c') * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6 := by
            gcongr; linarith only [hpow_nn2]
          have h2 : 2 * C_vert * Real.sqrt (Real.log c') * c' ^ (-13 : ℝ) * (1 + x) ^ 6 ≤
              2 * C_vert * Real.sqrt (Real.log c') * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6 := by
            gcongr; linarith only [hpow_nn1]
          linarith only [h1, h2]
  have hW_decay : W₀ ≤ 128 * c' ^ (4 : ℝ) * Real.exp (-(2 * π * x)) :=
    lowerWeps_exp_decay hc1.le hx_gt
  have h_drop_nonneg : 0 ≤ lowerPζ c' R z * ((1 - W₀) * ∫ ζ in (z - L₀)..(z + L₀),
      gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re) := by
    have h1 := h_sub_nn
    rw [intervalIntegral.integral_const_mul] at h1
    exact mul_nonneg hPζ_nn h1
  have h_edge_mul : -(C_L * Real.sqrt (Real.log c') *
        (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) *
        lowerPζ c' R z * (1 + x) ^ 6 * Real.exp (-(2 * π * x))) ≤
      lowerPζ c' R z * (W₀ * ∫ ζ in (z - L₀)..(z + L₀),
        gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re * (1 + 2 * Real.cos (2 * π * (ζ - φ₀)))) := by
    have hE_neg : -((2 * (C_top + 2 * C_vert)) * Real.sqrt (Real.log c') *
          (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6) ≤
        ∫ ζ in (z - L₀)..(z + L₀),
          gaussW c' (z - ζ) * (boasH c' g (ζ : ℂ)).re * (1 + 2 * Real.cos (2 * π * (ζ - φ₀))) := by
      linarith only [hlocal, hEdge_tot]
    have hPW_nn : 0 ≤ lowerPζ c' R z * W₀ := mul_nonneg hPζ_nn hW₀_mem.1
    have h1 := mul_le_mul_of_nonneg_left hE_neg hPW_nn
    have h2 : lowerPζ c' R z * W₀ *
          ((2 * (C_top + 2 * C_vert)) * Real.sqrt (Real.log c') *
            (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6) ≤
        C_L * Real.sqrt (Real.log c') * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) *
          lowerPζ c' R z * (1 + x) ^ 6 * Real.exp (-(2 * π * x)) := by
      have hCL_eq : 2 * (C_top + 2 * C_vert) * 128 = C_L := by
        dsimp [C_L]; ring
      calc lowerPζ c' R z * W₀ *
            ((2 * (C_top + 2 * C_vert)) * Real.sqrt (Real.log c') *
              (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6)
          ≤ lowerPζ c' R z * (128 * c' ^ (4 : ℝ) * Real.exp (-(2 * π * x))) *
              ((2 * (C_top + 2 * C_vert)) * Real.sqrt (Real.log c') *
                (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * (1 + x) ^ 6) := by
            gcongr
        _ = C_L * Real.sqrt (Real.log c') *
              (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) *
              lowerPζ c' R z * (1 + x) ^ 6 * Real.exp (-(2 * π * x)) := by
            rw [← hCL_eq]; ring
    linarith only [h1, h2]
  rw [hfrozen_eq, mul_add]
  linarith only [h_drop_nonneg, h_edge_mul]

/-! ### 3. Main Virasoro Boas assembly (`virasoro_lowerBand_lower_bound`) -/

/-- **`cts:boas`** (unconditional at Virasoro): at every good radius `R ∈ LowerRadiusRange virasoroC1 c'`,
the band integral satisfies `lowerBand virasoroProblem Gout virasoroPhi virasoroUhat c' R g ≥ -C c'^{-4/3}`. -/
theorem virasoro_lowerBand_lower_bound :
    ∃ cc C : ℝ, 10000 ≤ cc ∧ 0 ≤ C ∧
      ∀ c : ℝ, cc ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ),
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        LowerViolator virasoroPhi c T →
        T ≤ virasoroDeltaChart c (-virasoroAThr) →
        ∀ (N : ℕ) (R : ℝ), LowerGoodCircle N R → LowerRadiusRange virasoroC1 c R →
          -(C * c ^ (-(4 / 3 : ℝ))) ≤ lowerBand virasoroProblem Gout virasoroPhi virasoroUhat c R g := by
  obtain ⟨c_F, C_F, hcF_10, hCF_pos, hF⟩ := boas_freezing_estimate
  obtain ⟨c_Z, K_1, K_early, K_err, hcZ_max, hK1_pos, hKe_pos, hKerr_pos, hZ⟩ := boas_zeta_to_lowerBand
  obtain ⟨c_L, C_L, hcL_max, hCL_pos, hL⟩ := boas_local_frozen_lower
  obtain ⟨c_T, _, hcT_tap, _, hPζ_props⟩ := lowerPζ_properties
  obtain ⟨hint_exp, hval_exp⟩ := integral_exp_poly_decay
  let C_exp : ℝ := (2 : ℝ) ^ 7 * (1 + (Nat.factorial 7 : ℝ) / π ^ 7) / π
  let C_loc : ℝ := 4 * C_L * C_exp / (Real.sqrt 3 * π) + 1
  let C_tot : ℝ := K_err + C_F * K_1 + 9 * K_early + C_loc
  have hCexp_nn : 0 ≤ C_exp := by dsimp [C_exp]; positivity
  have hCloc_pos : 0 < C_loc := by dsimp [C_loc]; positivity
  have hCtot_pos : 0 < C_tot := by positivity
  have htop_exp : 3 - 4 * π + 37 / 8 < -(4 / 3 : ℝ) := by
    have := top_edge_exponent; linarith only [this]
  have htap10 : 10000 ≤ taperC0 := by linarith only [taperC0_ge]
  refine ⟨max (max c_F c_Z) (max c_L (max c_T 10000)), C_tot,
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)), hCtot_pos.le,
    fun c' hc' T g hwf hviol hT_hi N R _ hR => ?_⟩
  have hcF : c_F ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hcZ : c_Z ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hcL : c_L ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hcT : c_T ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hc_tap : taperC0 ≤ c' := hcT_tap.trans hcT
  have hc10000 : 10000 ≤ c' := htap10.trans hc_tap
  have hc0 : 0 < c' := by linarith only [hc10000]
  have hc1 : 1 ≤ c' := by linarith only [hc10000]
  obtain ⟨h_aesm, h_nn, hPh_int, h_tot, h_early, h_band_err⟩ := hZ hcZ hwf hviol hT_hi hR
  obtain ⟨hFr_int, hFr_err⟩ := hF hcF hR h_aesm h_nn hPh_int
  let h : ℝ → ℝ := fun ζ => (boasH c' g (ζ : ℂ)).re
  -- Step 1: Bound `∫_{boasZetaStar c'}^∞ lowerPζ(z) (1 + x(z))^6 exp(-2π x(z)) dz ≤ √c' / (√3 π) * C_exp`
  let φ : ℝ → ℝ := fun z => lowerPζ c' R z * (1 + xOfZeta c' z) ^ 6 * Real.exp (-(2 * π * xOfZeta c' z))
  have hzstar_pos : 0 < boasZetaStar c' := by
    have := zetaMin_pos hc0
    have := Real.log_nonneg hc1
    unfold boasZetaStar; linarith
  have hx_derivW : ∀ z ∈ Ioi (boasZetaStar c'),
      HasDerivWithinAt (xOfZeta c') (2 / (c' * rhoU (xOfZeta c' z))) (Ioi (boasZetaStar c')) z :=
    fun z hz => (hasDerivAt_xOfZeta hc0 (hzstar_pos.trans hz)).hasDerivWithinAt
  have hx_inj : InjOn (xOfZeta c') (Ioi (boasZetaStar c')) :=
    (xOfZeta_strictMono hc0).injOn.mono (Ioi_subset_Ioi hzstar_pos.le)
  have hx_img_sub : xOfZeta c' '' Ioi (boasZetaStar c') ⊆ Ioi xiStar := by
    rintro x ⟨z, hz, rfl⟩
    exact (xOfZeta_spec hc0 (hzstar_pos.trans hz)).1
  let majX : ℝ → ℝ := fun x => (Real.sqrt c' / (Real.sqrt 3 * π)) * ((1 + x) ^ 7 * Real.exp (-(2 * π * x)))
  have hmajX_int : IntegrableOn majX (xOfZeta c' '' Ioi (boasZetaStar c')) :=
    (hint_exp.mono_set hx_img_sub).const_mul _
  have hmajZ_int : IntegrableOn (fun z => (2 / (c' * rhoU (xOfZeta c' z))) * majX (xOfZeta c' z))
      (Ioi (boasZetaStar c')) := by
    have h1 := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hx_derivW hx_inj majX).mp hmajX_int
    refine h1.congr_fun (fun z hz => ?_) measurableSet_Ioi
    have hz_pos := hzstar_pos.trans hz
    have hρ_pos := rhoU_pos (xOfZeta_spec hc0 hz_pos).1
    dsimp only
    rw [smul_eq_mul, abs_of_pos (by positivity)]
  have hφ_le_maj : ∀ z ∈ Ioi (boasZetaStar c'),
      φ z ≤ (2 / (c' * rhoU (xOfZeta c' z))) * majX (xOfZeta c' z) := by
    intro z hz
    have hz_pos := hzstar_pos.trans hz
    have hx_gt := (xOfZeta_spec hc0 hz_pos).1
    have hx_pos := xiStar_pos.trans hx_gt
    have hρ_pos := rhoU_pos hx_gt
    have htap_le : lowerTaper virasoroPhi virasoroUhat c' R (c' * xOfZeta c' z ^ 2 / 3) ≤ 1 := by
      rw [lowerTaper_zeta_eq hc_tap hR hz_pos]
      obtain ⟨_, _, _, hW_spec⟩ := taperWζ_bounds_and_derivs hc_tap hR
      have hz_half : zetaMin c' / 2 ≤ z := by
        have hln := Real.log_nonneg hc1
        have hz' := mem_Ioi.mp hz
        unfold boasZetaStar at hz'
        linarith only [zetaMin_pos hc0, hz', hln]
      exact (hW_spec hz_half).2.1
    have hP0_pos := lowerP0_pos hc0 hz_pos
    have hPζ_le_P0 : lowerPζ c' R z ≤ lowerP0 c' z := by
      unfold lowerPζ
      exact mul_le_of_le_one_left hP0_pos.le htap_le
    have hP0_le : lowerP0 c' z ≤
        (2 / (c' * rhoU (xOfZeta c' z))) * (Real.sqrt c' / (Real.sqrt 3 * π) * (1 + xOfZeta c' z)) := by
      unfold lowerP0
      have hsqrt_le : Real.sqrt (xOfZeta c' z) ≤ 1 + xOfZeta c' z := by
        have hsq_le_one_add : Real.sqrt (xOfZeta c' z) ^ 2 ≤ (1 + xOfZeta c' z) ^ 2 := by
          rw [Real.sq_sqrt hx_pos.le]
          nlinarith only [hx_pos]
        nlinarith only [hsq_le_one_add, Real.sqrt_nonneg (xOfZeta c' z), hx_pos]
      have hexp_le1 : (1 - Real.exp (-(4 * π * xOfZeta c' z))) ^ 2 ≤ 1 := by
        have h1 : 0 < Real.exp (-(4 * π * xOfZeta c' z)) := Real.exp_pos _
        have h2 : Real.exp (-(4 * π * xOfZeta c' z)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
        nlinarith only [h1, h2]
      calc 2 * Real.sqrt (xOfZeta c' z) * (1 - Real.exp (-(4 * π * xOfZeta c' z))) ^ 2 /
            (Real.sqrt 3 * π * Real.sqrt c' * rhoU (xOfZeta c' z))
          ≤ 2 * (1 + xOfZeta c' z) * 1 / (Real.sqrt 3 * π * Real.sqrt c' * rhoU (xOfZeta c' z)) := by
            gcongr
        _ = (2 / (c' * rhoU (xOfZeta c' z))) * (Real.sqrt c' / (Real.sqrt 3 * π) * (1 + xOfZeta c' z)) := by
            have h3p : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
            have hsc_p : 0 < Real.sqrt c' := Real.sqrt_pos.mpr hc0
            have hsqc : Real.sqrt c' ^ 2 = c' := Real.sq_sqrt hc0.le
            field_simp [hc0.ne', hρ_pos.ne', h3p.ne', Real.pi_pos.ne', hsc_p.ne']
            linarith only [hsqc]
    have hex_nn : 0 ≤ (1 + xOfZeta c' z) ^ 6 * Real.exp (-(2 * π * xOfZeta c' z)) := by positivity
    calc φ z = lowerPζ c' R z * ((1 + xOfZeta c' z) ^ 6 * Real.exp (-(2 * π * xOfZeta c' z))) := by
          dsimp [φ]; ring
      _ ≤ ((2 / (c' * rhoU (xOfZeta c' z))) * (Real.sqrt c' / (Real.sqrt 3 * π) * (1 + xOfZeta c' z))) *
            ((1 + xOfZeta c' z) ^ 6 * Real.exp (-(2 * π * xOfZeta c' z))) :=
          mul_le_mul_of_nonneg_right (hPζ_le_P0.trans hP0_le) hex_nn
      _ = (2 / (c' * rhoU (xOfZeta c' z))) * majX (xOfZeta c' z) := by
          dsimp [majX]; ring
  have hφ_cont : ContinuousOn φ (Ioi (boasZetaStar c')) := by
    obtain ⟨_, _, _, hP_spec, _⟩ := hPζ_props hcT hR
    have hP_c : ContinuousOn (lowerPζ c' R) (Ioi (boasZetaStar c')) := fun z hz => by
      have hz_half : zetaMin c' / 2 ≤ z := by
        have hln := Real.log_nonneg hc1; have hz' := mem_Ioi.mp hz
        unfold boasZetaStar at hz'; linarith only [zetaMin_pos hc0, hz', hln]
      exact (hP_spec hz_half).2.1.continuousAt.continuousWithinAt
    have hx_c : ContinuousOn (xOfZeta c') (Ioi (boasZetaStar c')) := fun z hz =>
      (hasDerivAt_xOfZeta hc0 (hzstar_pos.trans hz)).continuousAt.continuousWithinAt
    exact (hP_c.mul (((continuousOn_const.add hx_c).pow 6))).mul
      (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul hx_c).neg))
  have hφ_int : IntegrableOn φ (Ioi (boasZetaStar c')) := by
    refine hmajZ_int.mono' (hφ_cont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz_pos := hzstar_pos.trans hz
    have htap_nn : 0 ≤ lowerTaper virasoroPhi virasoroUhat c' R (c' * xOfZeta c' z ^ 2 / 3) := by
      rw [lowerTaper_zeta_eq hc_tap hR hz_pos]
      obtain ⟨_, _, _, hW_spec⟩ := taperWζ_bounds_and_derivs hc_tap hR
      have hz_half : zetaMin c' / 2 ≤ z := by
        have hln := Real.log_nonneg hc1; have hz' := mem_Ioi.mp hz
        unfold boasZetaStar at hz'; linarith only [zetaMin_pos hc0, hz', hln]
      exact (hW_spec hz_half).1.le
    have hP_nn : 0 ≤ lowerPζ c' R z := mul_nonneg htap_nn (lowerP0_pos hc0 hz_pos).le
    have hx_pos := xiStar_pos.trans (xOfZeta_spec hc0 hz_pos).1
    rw [Real.norm_of_nonneg (by dsimp [φ]; positivity)]
    exact hφ_le_maj z hz
  have hφ_int_bd : ∫ z in Ioi (boasZetaStar c'), φ z ≤
      Real.sqrt c' / (Real.sqrt 3 * π) * C_exp := by
    have h1 := MeasureTheory.setIntegral_mono_on hφ_int hmajZ_int measurableSet_Ioi hφ_le_maj
    have h2 : ∫ z in Ioi (boasZetaStar c'), (2 / (c' * rhoU (xOfZeta c' z))) * majX (xOfZeta c' z) =
        ∫ x in xOfZeta c' '' Ioi (boasZetaStar c'), majX x := by
      rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hx_derivW hx_inj majX]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
      have hz_pos := hzstar_pos.trans hz
      have hρ_pos := rhoU_pos (xOfZeta_spec hc0 hz_pos).1
      rw [smul_eq_mul, abs_of_pos (by positivity)]
    have h3 : ∫ x in xOfZeta c' '' Ioi (boasZetaStar c'), majX x ≤ ∫ x in Ioi xiStar, majX x := by
      refine MeasureTheory.setIntegral_mono_set (hint_exp.const_mul _) ?_ (ae_of_all _ hx_img_sub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx_nn := (xiStar_pos.trans hx).le
      dsimp [majX]; positivity
    have h4 : ∫ x in Ioi xiStar, majX x ≤ Real.sqrt c' / (Real.sqrt 3 * π) * C_exp := by
      dsimp [majX]
      rw [MeasureTheory.integral_const_mul]
      gcongr
    exact h1.trans (h2 ▸ h3.trans h4)
  -- Step 2: Integrate the local lower bound over `Ici (boasZetaStar c')`
  let fac : ℝ := C_L * Real.sqrt (Real.log c') * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ)
  have hfac_nn : 0 ≤ fac := by dsimp [fac]; positivity
  have hFr_int_Ioi : IntegrableOn (boasFrozenInt c' R h) (Ioi (boasZetaStar c')) :=
    hFr_int.mono_set Ioi_subset_Ici_self
  have h_fr_lower : -(fac * (Real.sqrt c' / (Real.sqrt 3 * π) * C_exp)) ≤
      ∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z := by
    rw [← MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici]
    have hm := MeasureTheory.setIntegral_mono_on (hφ_int.const_mul (-fac)) hFr_int_Ioi measurableSet_Ioi
      fun z hz => by
        have hloc := hL hcL hwf hT_hi hR (mem_Ioi.mp hz).le
        dsimp [fac, φ, h] at hloc ⊢
        linarith only [hloc]
    rw [MeasureTheory.integral_const_mul] at hm
    have hmul : -fac * (Real.sqrt c' / (Real.sqrt 3 * π) * C_exp) ≤
        -fac * ∫ z in Ioi (boasZetaStar c'), φ z := by
      have := mul_le_mul_of_nonneg_left hφ_int_bd hfac_nn
      linarith only [this]
    linarith only [hm, hmul]
  -- Step 3: Simplify the exponent `fac * √c' ≤ 4 C_L c'^{-4/3}`
  have hfac_sqrt_ub : fac * (Real.sqrt c' / (Real.sqrt 3 * π) * C_exp) ≤ C_loc * c' ^ (-(4 / 3 : ℝ)) := by
    have hlog_bd : Real.sqrt (Real.log c') ≤ 2 * c' ^ (1 / 8 : ℝ) := by
      have hlog4 : Real.log c' ≤ 4 * c' ^ (1 / 4 : ℝ) := by
        have heq : c' = (c' ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
        conv_lhs => rw [heq]
        rw [Real.log_pow, Nat.cast_ofNat]
        have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc0 (1 / 4 : ℝ))
        linarith only [h1]
      have hsq18 : Real.sqrt (4 * c' ^ (1 / 4 : ℝ)) = 2 * c' ^ (1 / 8 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num,
          ← Real.sqrt_sq (Real.rpow_nonneg hc0.le (1 / 8 : ℝ)), ← Real.rpow_natCast,
          ← Real.rpow_mul hc0.le]
        congr 2; norm_num
      exact (Real.sqrt_le_sqrt hlog4).trans_eq hsq18
    have hsqrt_c : Real.sqrt c' = c' ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c'
    have hpow_tot : c' ^ (1 / 8 : ℝ) * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) * c' ^ (1 / 2 : ℝ) ≤
        2 * c' ^ (-(4 / 3 : ℝ)) := by
      have h1 : c' ^ (1 / 8 : ℝ) * c' ^ (3 - 4 * π) * c' ^ (4 : ℝ) * c' ^ (1 / 2 : ℝ) ≤ c' ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
        refine Real.rpow_le_rpow_of_exponent_le hc1 ?_
        linarith only [htop_exp]
      have h2 : c' ^ (1 / 8 : ℝ) * c' ^ (-13 : ℝ) * c' ^ (4 : ℝ) * c' ^ (1 / 2 : ℝ) ≤ c' ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      linarith only [h1, h2]
    calc fac * (Real.sqrt c' / (Real.sqrt 3 * π) * C_exp)
        = C_L * C_exp / (Real.sqrt 3 * π) *
            (Real.sqrt (Real.log c') * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) * Real.sqrt c') := by
          dsimp [fac]; ring
      _ ≤ C_L * C_exp / (Real.sqrt 3 * π) *
            ((2 * c' ^ (1 / 8 : ℝ)) * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) * c' ^ (1 / 2 : ℝ)) := by
          rw [← hsqrt_c]; gcongr
      _ ≤ C_L * C_exp / (Real.sqrt 3 * π) * (4 * c' ^ (-(4 / 3 : ℝ))) := by
          have h4_le : (2 * c' ^ (1 / 8 : ℝ)) * (c' ^ (3 - 4 * π) + c' ^ (-13 : ℝ)) * c' ^ (4 : ℝ) * c' ^ (1 / 2 : ℝ) ≤
              4 * c' ^ (-(4 / 3 : ℝ)) := by
            linarith only [hpow_tot]
          gcongr
      _ = (4 * C_L * C_exp / (Real.sqrt 3 * π)) * c' ^ (-(4 / 3 : ℝ)) := by ring
      _ ≤ C_loc * c' ^ (-(4 / 3 : ℝ)) := by
          have hcle : 4 * C_L * C_exp / (Real.sqrt 3 * π) ≤ C_loc := by
            dsimp [C_loc]; linarith
          gcongr
  -- Step 4: Combine freezing error, band bridge error, and frozen local lower bound
  have hpow43 : c' ^ (-1 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = c' ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc0]; congr 1; norm_num
  have hFr_err' : |(∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) -
        ∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ| ≤
      (C_F * K_1 + 9 * K_early) * c' ^ (-(4 / 3 : ℝ)) := by
    calc |(∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z) -
          ∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ|
        ≤ C_F * c' ^ (-1 : ℝ) * (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) +
            9 * ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ := hFr_err
      _ ≤ C_F * c' ^ (-1 : ℝ) * (K_1 * c' ^ (-(1 / 3 : ℝ))) + 9 * (K_early * c' ^ (-(4 / 3 : ℝ))) := by
          gcongr
      _ = C_F * K_1 * (c' ^ (-1 : ℝ) * c' ^ (-(1 / 3 : ℝ))) + 9 * K_early * c' ^ (-(4 / 3 : ℝ)) := by ring
      _ = (C_F * K_1 + 9 * K_early) * c' ^ (-(4 / 3 : ℝ)) := by rw [hpow43]; ring
  have h1 := (abs_le.mp h_band_err).2
  have h2 := (abs_le.mp hFr_err').2
  have h_fr_c : -(C_loc * c' ^ (-(4 / 3 : ℝ))) ≤ ∫ z in Ici (boasZetaStar c'), boasFrozenInt c' R h z := by
    linarith only [h_fr_lower, hfac_sqrt_ub]
  dsimp [C_tot]
  linarith only [h1, h2, h_fr_c]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_lowerBand_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_lowerBand_lower_bound

end

end FormalResearch.ModularBootstrap.FiveTerm