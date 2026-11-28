module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeCoord
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3a

/-!
# Oscillatory coefficient bounds `W_1(ζ)` and `θ̃_ε(ζ)` on `[ζ_min/2, ∞)` (`ctl:freeze`)

Proves:
* `lowerWeps_mem_Icc`: `0 ≤ lowerWeps ε (lowerY x) ≤ 1` for `ε ≥ 0`, `x > 0`;
* `sin_lowerThetaEps_eq`: exact unwrapped phase identity inside `Real.sin`;
* `lowerWeps_unwrappedTheta_deriv_bounds`: `|W_1^(j)(ζ)| + |θ^(j)(ζ)| ≤ C (ζ^{-j} + c'^{-j})`
  (`j = 1, 2`) for `c' ≥ 10000`, `ε = c'^{-2}`, `ζ > 0`.
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

/-! ### 1. Auxiliary `slitA(x) = 1 - lowerY(x)^2` and `0 ≤ W̃_ε ≤ 1` -/

/-- `a(x) = 1 - y(x)^2 = 2 √2 / (cosh(πx) + √2) ∈ (0, 1)`. -/
def slitA (x : ℝ) : ℝ := 2 * Real.sqrt 2 / (Real.cosh (π * x) + Real.sqrt 2)

/-- Denominator `(a + ε)^2 + ε^2 (1 - a)` of `|M̃_ε(iy)|^2`. -/
def mtDen (ε a : ℝ) : ℝ := (a + ε) ^ 2 + ε ^ 2 * (1 - a)

lemma lowerY_eq_yOfX (x : ℝ) : lowerY x = yOfX x := rfl

lemma slitA_pos (x : ℝ) : 0 < slitA x := by
  unfold slitA; have := Real.cosh_pos (π * x); positivity

lemma slitA_lt_one {x : ℝ} (hx : xiStar < x) : slitA x < 1 := by
  have hch_xi : Real.cosh (π * xiStar) = Real.sqrt 2 := by
    have h := Real.cosh_sq_sub_sinh_sq (π * xiStar)
    rw [sinh_pi_mul_xiStar, one_pow] at h
    rw [← Real.sqrt_sq (Real.cosh_pos _).le]
    congr 1; linarith
  have hch_gt : Real.sqrt 2 < Real.cosh (π * x) := by
    rw [← hch_xi]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_of_pos (mul_pos Real.pi_pos xiStar_pos),
      abs_of_pos (mul_pos Real.pi_pos (xiStar_pos.trans hx))]
    exact mul_lt_mul_of_pos_left hx Real.pi_pos
  unfold slitA
  rw [div_lt_one (by positivity)]
  linarith only [hch_gt]

lemma one_sub_lowerY_sq {x : ℝ} (hx : xiStar < x) : 1 - lowerY x ^ 2 = slitA x := by
  have hnn : 0 ≤ (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by
    have h1 := slitA_lt_one hx
    have hpos := Real.cosh_pos (π * x)
    unfold slitA at h1
    rw [div_lt_one (by positivity)] at h1
    exact div_nonneg (by linarith only [h1]) (by positivity)
  have hsq : lowerY x ^ 2 = (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by
    unfold lowerY; exact Real.sq_sqrt hnn
  rw [hsq]; unfold slitA
  have hdn : Real.cosh (π * x) + Real.sqrt 2 ≠ 0 := by have := Real.cosh_pos (π * x); positivity
  field_simp [hdn]; ring

lemma lowerWeps_eq {ε x : ℝ} (hε : 0 ≤ ε) (hx : xiStar < x) :
    lowerWeps ε (lowerY x) = (1 + ε) ^ 2 * slitA x ^ 2 / mtDen ε (slitA x) := by
  set y := lowerY x
  set a := slitA x
  have ha0 : 0 < a := slitA_pos x
  have ha1 : a < 1 := slitA_lt_one hx
  have h1y : 1 - y ^ 2 = a := one_sub_lowerY_sq hx
  have hy2 : y ^ 2 = 1 - a := by linarith only [h1y]
  have hmt : lowerMt ε (Complex.I * (y : ℂ)) =
      (((1 + ε) * a : ℝ) : ℂ) / (((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)) := by
    unfold lowerMt
    have e1 : 1 + (Complex.I * (y : ℂ)) ^ 2 = ((a : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq, ← h1y]; push_cast; ring
    have e2 : 1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) =
        (((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)) := by
      rw [e1]; push_cast; ring
    rw [e1, e2]; push_cast; ring
  have hden_eq : ‖(((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ))‖ ^ 2 = mtDen ε a := by
    have h1 : (((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)).re = a + ε := by simp
    have h2 : (((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)).im = ε * y := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
    unfold mtDen
    nlinarith only [hy2]
  unfold lowerWeps
  rw [hmt, norm_div, div_pow, hden_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by linarith) ha0)]
  ring

lemma lowerWeps_mem_Icc {ε x : ℝ} (hε : 0 ≤ ε) (hx : xiStar < x) :
    0 ≤ lowerWeps ε (lowerY x) ∧ lowerWeps ε (lowerY x) ≤ 1 := by
  rw [lowerWeps_eq hε hx]
  set a := slitA x
  have ha0 : 0 < a := slitA_pos x
  have ha1 : a < 1 := slitA_lt_one hx
  have hden_pos : 0 < mtDen ε a := by unfold mtDen; positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hden_pos]
  have hdiff : mtDen ε a - (1 + ε) ^ 2 * a ^ 2 = ε * (1 - a) * (2 * a + ε * (2 + a)) := by
    unfold mtDen; ring
  have hnonneg : 0 ≤ ε * (1 - a) * (2 * a + ε * (2 + a)) := by positivity
  linarith only [hdiff, hnonneg]

/-! ### 2. Unwrapped `lowerThetaEps` inside `Real.sin` -/

/-- Unwrapped outer phase `θ_out(y(x)) - 2 arctan(ε y(x) / (a(x) + ε))`. -/
def unwrappedTheta (ε x : ℝ) : ℝ :=
  thetaOutX x - 2 * Real.arctan (ε * lowerY x / (slitA x + ε))

lemma sin_lowerThetaEps_eq {ε c' x : ℝ} (hε : 0 ≤ ε) (hx : xiStar < x) :
    Real.sin (lowerThetaEps Gout ε (lowerY x) - 2 * π * c' * cumulN x) =
      Real.sin (unwrappedTheta ε x - 2 * π * c' * cumulN x) := by
  set y := lowerY x
  have hy_mem : y ∈ Ioo (0 : ℝ) 1 := yOfX_mem hx
  have hW_pos : 0 < Wslit y := Wslit_pos' hy_mem
  have hG_polar := gout_polar hy_mem
  have hG_ne : Gout (Complex.I * (y : ℂ)) ≠ 0 := by
    rw [hG_polar]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hW_pos.ne') (Complex.exp_ne_zero _)
  have hexp_G : Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) =
      Complex.exp (Complex.I * (thetaOutX x : ℂ)) := by
    have hnorm : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := by
      rw [hG_polar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW_pos,
        show Complex.I * (thetaOut y : ℂ) = (thetaOut y : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := Complex.norm_mul_exp_arg_mul_I (Gout (Complex.I * (y : ℂ)))
    rw [hnorm, hG_polar, mul_comm (Complex.arg _ : ℂ) Complex.I] at h1
    have h2 : Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) =
        Complex.exp (Complex.I * (thetaOut y : ℂ)) :=
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hW_pos.ne') h1
    rwa [← thetaOut_yOfX hx]
  set a := slitA x
  have ha0 : 0 < a := slitA_pos x
  have ha1 : a < 1 := slitA_lt_one hx
  have h1y : 1 - y ^ 2 = a := one_sub_lowerY_sq hx
  have hden_pos : 0 < a + ε := by linarith
  let z_d : ℂ := ((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)
  have hzd_re : 0 < z_d.re := by simp [z_d]; exact hden_pos
  have hmt_eq : lowerMt ε (Complex.I * (y : ℂ)) =
      (((1 + ε) * a : ℝ) : ℂ) / z_d := by
    unfold lowerMt
    have e1 : 1 + (Complex.I * (y : ℂ)) ^ 2 = ((a : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq, ← h1y]; push_cast; ring
    have e2 : 1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) = z_d := by
      rw [e1]; dsimp [z_d]; push_cast; ring
    rw [e1, e2]; push_cast; ring
  have harg_mt : Complex.arg (lowerMt ε (Complex.I * (y : ℂ))) =
      -Real.arctan (ε * y / (a + ε)) := by
    have hnum_pos : 0 < (1 + ε) * a := mul_pos (by linarith) ha0
    have hinv_re : 0 < z_d⁻¹.re := by
      rw [Complex.inv_re]
      exact div_pos hzd_re (Complex.normSq_pos.mpr (fun h0 => by rw [h0] at hzd_re; simp at hzd_re))
    have hre_mt : 0 < (lowerMt ε (Complex.I * (y : ℂ))).re := by
      rw [hmt_eq, div_eq_mul_inv, Complex.re_ofReal_mul]
      exact mul_pos hnum_pos hinv_re
    rw [Complex.arg_eq_arctan_of_re_pos hre_mt]
    have hdiv_im_re : (lowerMt ε (Complex.I * (y : ℂ))).im / (lowerMt ε (Complex.I * (y : ℂ))).re =
        -(ε * y / (a + ε)) := by
      have hre : (lowerMt ε (Complex.I * (y : ℂ))).re = ((1 + ε) * a) * ((a + ε) / Complex.normSq z_d) := by
        rw [hmt_eq, div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re]
        simp [z_d]
      have him : (lowerMt ε (Complex.I * (y : ℂ))).im = ((1 + ε) * a) * (-(ε * y) / Complex.normSq z_d) := by
        rw [hmt_eq, div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im]
        simp [z_d]
      rw [him, hre]
      have hns_ne : Complex.normSq z_d ≠ 0 := (Complex.normSq_pos.mpr (fun h0 => by rw [h0] at hzd_re; simp at hzd_re)).ne'
      field_simp [hnum_pos.ne', hden_pos.ne', hns_ne]
    rw [hdiv_im_re, Real.arctan_neg]
  have hsin_eq : ∀ φ ψ : ℝ, Complex.exp (Complex.I * (φ : ℂ)) = Complex.exp (Complex.I * (ψ : ℂ)) →
      Real.sin φ = Real.sin ψ := fun φ ψ h => by
    have him := congrArg Complex.im h
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_im,
      mul_comm Complex.I, Complex.exp_ofReal_mul_I_im] at him
    exact him
  refine hsin_eq _ _ ?_
  unfold lowerThetaEps unwrappedTheta
  rw [harg_mt]
  have hsplit : ∀ A B : ℝ, Complex.exp (Complex.I * ((A + B : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (A : ℂ)) * Complex.exp (Complex.I * (B : ℂ)) := fun A B => by
    push_cast; rw [mul_add, Complex.exp_add]
  rw [show (Complex.arg (Gout (Complex.I * (y : ℂ))) + 2 * -(Real.arctan (ε * y / (a + ε))) -
      2 * π * c' * cumulN x) =
      Complex.arg (Gout (Complex.I * (y : ℂ))) +
        (-(2 * Real.arctan (ε * y / (a + ε))) - 2 * π * c' * cumulN x) by ring,
    show thetaOutX x - 2 * Real.arctan (ε * y / (a + ε)) - 2 * π * c' * cumulN x =
      thetaOutX x + (-(2 * Real.arctan (ε * y / (a + ε))) - 2 * π * c' * cumulN x) by ring]
  rw [hsplit, hsplit, hexp_G]

/-! ### 3. Chain rule template from `x` (`min(r, 1)` singularities) to `ζ` -/

/-- Shared chain rule: if `f` is `C^2` on `x > ξ_*` with `|f'(x)| ≤ M (min r 1)^{-1/2}`
and `|f''(x)| ≤ M (min r 1)^{-3/2}` (`r = x - ξ_*`), then `(f ∘ xOfZeta c')` has
`|d^j/dζ^j| ≤ C * (ζ^{-j} + c'^{-j})` (`j = 1, 2`). -/
lemma zeta_chain_deriv_bounds {f f1 f2 : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf1 : ∀ {x : ℝ}, xiStar < x → HasDerivAt f (f1 x) x ∧
      |f1 x| ≤ M * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)))
    (hf2 : ∀ {x : ℝ}, xiStar < x → HasDerivAt f1 (f2 x) x ∧
      |f2 x| ≤ M * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c' ζ : ℝ}, 0 < c' → 0 < ζ →
      let g1 := fun u => f1 (xOfZeta c' u) * (2 / (c' * rhoU (xOfZeta c' u)))
      let g2 := fun u => f2 (xOfZeta c' u) * (2 / (c' * rhoU (xOfZeta c' u))) ^ 2 +
        f1 (xOfZeta c' u) * (-(4 * rhoUDeriv (xOfZeta c' u) / (c' ^ 2 * rhoU (xOfZeta c' u) ^ 3)))
      HasDerivAt (fun u => f (xOfZeta c' u)) (g1 ζ) ζ ∧
      HasDerivAt g1 (g2 ζ) ζ ∧
      |g1 ζ| ≤ C * (ζ⁻¹ + c'⁻¹) ∧
      |g2 ζ| ≤ C * (ζ ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
  obtain ⟨C_x, hCx_pos, hx_bounds⟩ := xOfZeta_deriv_bounds
  refine ⟨M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1, by positivity, fun {c' ζ} hc0 hζ => ?_⟩
  intro g1 g2
  obtain ⟨hx_gt, _, _⟩ := xOfZeta_spec hc0 hζ
  set x := xOfZeta c' ζ
  set r := x - xiStar
  set x1 := 2 / (c' * rhoU x)
  set x2 := -(4 * rhoUDeriv x / (c' ^ 2 * rhoU x ^ 3))
  have hr_pos : 0 < r := sub_pos.mpr hx_gt
  have hd_x := hasDerivAt_xOfZeta hc0 hζ
  have hd_x' := hasDerivAt_xOfZeta' hc0 hζ
  have hd_f : HasDerivAt (fun u => f (xOfZeta c' u)) (g1 ζ) ζ :=
    ((hf1 hx_gt).1.comp ζ hd_x).congr_deriv (by simp [g1, x])
  have hd_f1 : HasDerivAt (fun u => f1 (xOfZeta c' u)) (f2 x * x1) ζ :=
    (hf2 hx_gt).1.comp ζ hd_x
  have hd_g1 : HasDerivAt g1 (g2 ζ) ζ :=
    (hd_f1.mul hd_x').congr_deriv (by dsimp [g2, x, x1, x2]; ring)
  obtain ⟨hx1_pos, hx1_le, hx2_le, hx_inf⟩ := hx_bounds hc0 hζ
  have hf1_bd := (hf1 hx_gt).2
  have hf2_bd := (hf2 hx_gt).2
  have hζm2 : ζ ^ (-2 : ℝ) = (ζ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hζ.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcm2 : c' ^ (-2 : ℝ) = (c' ^ 2)⁻¹ := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨hd_f, hd_g1, ?_, ?_⟩
  · rcases le_or_gt r 1 with hr1 | hr1
    · have hmin : min r 1 = r := min_eq_left hr1
      rw [hmin, Real.rpow_neg hr_pos.le, ← Real.sqrt_eq_rpow] at hf1_bd
      have hsr : Real.sqrt r * (r / Real.sqrt r) = r := by
        rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr hr_pos).ne']
      have hsr1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
      calc |g1 ζ| = |f1 x| * x1 := by dsimp [g1, x, x1]; rw [abs_mul, abs_of_pos hx1_pos]
        _ ≤ (M * (Real.sqrt r)⁻¹) * (r / ζ) := by gcongr
        _ = M * Real.sqrt r / ζ := by
            rw [← div_eq_mul_inv (r / Real.sqrt r) _]
            have : (Real.sqrt r)⁻¹ * r = Real.sqrt r := by
              rw [inv_mul_eq_div]; exact Real.div_sqrt
            calc M * (Real.sqrt r)⁻¹ * (r / ζ) = M * ((Real.sqrt r)⁻¹ * r) / ζ := by ring
              _ = M * Real.sqrt r / ζ := by rw [this]
        _ ≤ M * 1 / ζ := by gcongr
        _ = M * ζ⁻¹ := by ring
        _ ≤ (M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1) * (ζ⁻¹ + c'⁻¹) := by
            have h1 : M ≤ M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1 := by
              nlinarith [le_max_left (1 : ℝ) C_x, show 0 ≤ M * (1 + C_x + C_x ^ 2) by positivity]
            nlinarith [inv_nonneg.mpr hζ.le, inv_nonneg.mpr hc0.le, h1]
    · have hmin : min r 1 = 1 := min_eq_right hr1.le
      rw [hmin, Real.one_rpow, mul_one] at hf1_bd
      have hx1_inf := (hx_inf (by dsimp [r] at hr1; linarith)).1
      calc |g1 ζ| = |f1 x| * x1 := by dsimp [g1, x, x1]; rw [abs_mul, abs_of_pos hx1_pos]
        _ ≤ M * (C_x / c') := by gcongr
        _ = (M * C_x) * c'⁻¹ := by ring
        _ ≤ (M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1) * (ζ⁻¹ + c'⁻¹) := by
            have h1 : M * C_x ≤ M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1 := by
              nlinarith [le_max_right (1 : ℝ) C_x, show 0 ≤ M * (1 + C_x + C_x ^ 2) by positivity]
            nlinarith [inv_nonneg.mpr hζ.le, inv_nonneg.mpr hc0.le, h1]
  · rw [hζm2, hcm2]
    rcases le_or_gt r 1 with hr1 | hr1
    · have hmin : min r 1 = r := min_eq_left hr1
      rw [hmin, Real.rpow_neg hr_pos.le, ← Real.sqrt_eq_rpow] at hf1_bd
      rw [hmin] at hf2_bd
      have hsr1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
      have hr32 : r ^ (-(3 / 2 : ℝ)) * r ^ 2 = Real.sqrt r := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr_pos, Real.sqrt_eq_rpow]; norm_num
      have hx1_sq : x1 ^ 2 ≤ r ^ 2 / ζ ^ 2 := by
        calc x1 ^ 2 ≤ (r / ζ) ^ 2 := pow_le_pow_left₀ hx1_pos.le hx1_le 2
          _ = r ^ 2 / ζ ^ 2 := by ring
      have ht1 : |f2 x * x1 ^ 2| ≤ M / ζ ^ 2 := by
        rw [abs_mul, abs_pow, abs_of_pos hx1_pos]
        calc |f2 x| * x1 ^ 2 ≤ (M * r ^ (-(3 / 2 : ℝ))) * (r ^ 2 / ζ ^ 2) := by gcongr
          _ = M * (r ^ (-(3 / 2 : ℝ)) * r ^ 2) / ζ ^ 2 := by ring
          _ = M * Real.sqrt r / ζ ^ 2 := by rw [hr32]
          _ ≤ M * 1 / ζ ^ 2 := by gcongr
          _ = M / ζ ^ 2 := by ring
      have ht2 : |f1 x * x2| ≤ M * C_x / ζ ^ 2 := by
        rw [abs_mul]
        have hsr : (Real.sqrt r)⁻¹ * r = Real.sqrt r := by rw [inv_mul_eq_div]; exact Real.div_sqrt
        calc |f1 x| * |x2| ≤ (M * (Real.sqrt r)⁻¹) * (C_x * r / ζ ^ 2) := by gcongr
          _ = M * C_x * ((Real.sqrt r)⁻¹ * r) / ζ ^ 2 := by ring
          _ = M * C_x * Real.sqrt r / ζ ^ 2 := by rw [hsr]
          _ ≤ M * C_x * 1 / ζ ^ 2 := by gcongr
          _ = M * C_x / ζ ^ 2 := by ring
      calc |g2 ζ| ≤ |f2 x * x1 ^ 2| + |f1 x * x2| := by dsimp [g2]; exact abs_add_le _ _
        _ ≤ M / ζ ^ 2 + M * C_x / ζ ^ 2 := add_le_add ht1 ht2
        _ = M * (1 + C_x) * (ζ ^ 2)⁻¹ := by ring
        _ ≤ (M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1) * ((ζ ^ 2)⁻¹ + (c' ^ 2)⁻¹) := by
            have h1 : M * (1 + C_x) ≤ M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1 := by
              have : 0 ≤ M * C_x ^ 2 := by positivity
              have : 0 ≤ M * max 1 C_x := by positivity
              linarith
            have hinv : 0 ≤ (ζ ^ 2)⁻¹ := by positivity
            have hinv2 : 0 ≤ (c' ^ 2)⁻¹ := by positivity
            nlinarith only [h1, hinv, hinv2]
    · have hmin : min r 1 = 1 := min_eq_right hr1.le
      rw [hmin, Real.one_rpow, mul_one] at hf1_bd hf2_bd
      have hx_inf' := hx_inf (by dsimp [r] at hr1; linarith)
      have hx1_sq : x1 ^ 2 ≤ C_x ^ 2 / c' ^ 2 := by
        calc x1 ^ 2 ≤ (C_x / c') ^ 2 := pow_le_pow_left₀ hx1_pos.le hx_inf'.1 2
          _ = C_x ^ 2 / c' ^ 2 := by ring
      have ht1 : |f2 x * x1 ^ 2| ≤ M * C_x ^ 2 / c' ^ 2 := by
        rw [abs_mul, abs_pow, abs_of_pos hx1_pos]
        calc |f2 x| * x1 ^ 2 ≤ M * (C_x ^ 2 / c' ^ 2) := by gcongr
          _ = M * C_x ^ 2 / c' ^ 2 := by ring
      have ht2 : |f1 x * x2| ≤ M * C_x / c' ^ 2 := by
        rw [abs_mul]
        calc |f1 x| * |x2| ≤ M * (C_x / c' ^ 2) := by gcongr; exact hx_inf'.2
          _ = M * C_x / c' ^ 2 := by ring
      calc |g2 ζ| ≤ |f2 x * x1 ^ 2| + |f1 x * x2| := by dsimp [g2]; exact abs_add_le _ _
        _ ≤ M * C_x ^ 2 / c' ^ 2 + M * C_x / c' ^ 2 := add_le_add ht1 ht2
        _ = M * (C_x + C_x ^ 2) * (c' ^ 2)⁻¹ := by ring
        _ ≤ (M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1) * ((ζ ^ 2)⁻¹ + (c' ^ 2)⁻¹) := by
            have h1 : M * (C_x + C_x ^ 2) ≤ M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1 := by
              have : 0 ≤ M * max 1 C_x := by positivity
              linarith
            have hinv : 0 ≤ (ζ ^ 2)⁻¹ := by positivity
            have hinv2 : 0 ≤ (c' ^ 2)⁻¹ := by positivity
            nlinarith only [h1, hinv, hinv2]

/-! ### 4. `C^2` bounds for `W_1(ζ)` and `unwrappedTheta(ζ)` -/

/-- `slitA'` and `slitA''` relative bounds on `ℝ`. -/
private lemma slitA_derivs (x : ℝ) :
    let a1 := -(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
    let a2 := π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
    HasDerivAt slitA a1 x ∧ HasDerivAt (fun t => -(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) a2 x ∧
    (0 ≤ x → |a1| ≤ π * slitA x ∧ |a2| ≤ 3 * π ^ 2 * slitA x) := by
  intro a1 a2
  have hpi := Real.pi_pos
  have hpos_den : ∀ t, 0 < Real.cosh (π * t) + Real.sqrt 2 := fun t => by
    have := Real.cosh_pos (π * t); positivity
  have hd_ch : ∀ t, HasDerivAt (fun u => Real.cosh (π * u) + Real.sqrt 2) (π * Real.sinh (π * t)) t := fun t =>
    (((Real.hasDerivAt_cosh (π * t)).comp t (by simpa using (hasDerivAt_id t).const_mul π)).add_const _).congr_deriv (by ring)
  have hd_sh : ∀ t, HasDerivAt (fun u => Real.sinh (π * u)) (π * Real.cosh (π * t)) t := fun t =>
    ((Real.hasDerivAt_sinh (π * t)).comp t (by simpa using (hasDerivAt_id t).const_mul π)).congr_deriv (by ring)
  have hd_a : ∀ t, HasDerivAt slitA
      (-(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) t := fun t => by
    have hd := (hasDerivAt_const t (2 * Real.sqrt 2)).div (hd_ch t) (hpos_den t).ne'
    refine hd.congr_deriv ?_
    unfold slitA
    field_simp [(hpos_den t).ne']; ring
  have hd_ratio : HasDerivAt (fun t => -(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)))
      (-(π ^ 2 * (Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) -
        Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2))) x := by
    have hq := ((hd_sh x).const_mul π).div (hd_ch x) (hpos_den x).ne'
    refine hq.neg.congr_deriv ?_
    field_simp [(hpos_den x).ne']; ring
  have hd_a2 : HasDerivAt (fun t => -(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) a2 x := by
    refine (hd_ratio.mul (hd_a x)).congr_deriv ?_
    dsimp [a2]; ring
  refine ⟨hd_a x, hd_a2, fun hx0 => ?_⟩
  have ha0 : 0 < slitA x := slitA_pos x
  have hsh0 : 0 ≤ Real.sinh (π * x) := Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le hx0)
  have hch_pos : 0 < Real.cosh (π * x) := Real.cosh_pos _
  have hsh_le_ch : Real.sinh (π * x) ≤ Real.cosh (π * x) := by
    have := Real.cosh_sq_sub_sinh_sq (π * x)
    nlinarith only [this, hsh0, hch_pos]
  have hrat1 : Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) ≤ 1 :=
    (div_le_one (hpos_den x)).mpr (by linarith only [hsh_le_ch, Real.sqrt_nonneg 2])
  have hrat2 : Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) ≤ 1 :=
    (div_le_one (hpos_den x)).mpr (by linarith only [Real.sqrt_nonneg 2])
  have h1 : |a1| ≤ π * slitA x := by
    have hnn : 0 ≤ π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) := by positivity
    dsimp [a1]
    rw [abs_mul, abs_neg, abs_of_nonneg hnn, abs_of_pos ha0]
    calc π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) * slitA x
        = π * (Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x := by ring
      _ ≤ π * 1 * slitA x := by gcongr
      _ = π * slitA x := by ring
  have h2 : |a2| ≤ 3 * π ^ 2 * slitA x := by
    have hr1_nn : 0 ≤ Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) := by positivity
    have hr2_nn : 0 ≤ Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) := by positivity
    have hsq : Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 ≤ 1 := by
      rw [← div_pow]; exact pow_le_one₀ hr1_nn hrat1
    have hmid : |2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2))]
    dsimp [a2]
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hpi 2), abs_of_pos ha0]
    calc π ^ 2 * |2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
            Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)| * slitA x
        ≤ π ^ 2 * 3 * slitA x := by gcongr
      _ = 3 * π ^ 2 * slitA x := by ring
  exact ⟨h1, h2⟩

private lemma mtDen_bounds {ε a : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4) (ha0 : 0 < a) :
    (a + ε) ^ 2 / 2 ≤ mtDen ε a ∧ mtDen ε a ≤ 2 * (a + ε) ^ 2 := by
  have h1 : mtDen ε a - (a + ε) ^ 2 / 2 = a ^ 2 / 2 + ε * (1 - ε) * a + 3 / 2 * ε ^ 2 := by
    unfold mtDen; ring
  have h2 : 2 * (a + ε) ^ 2 - mtDen ε a = a ^ 2 + ε * (2 + ε) * a := by
    unfold mtDen; ring
  have hn1 : 0 ≤ a ^ 2 / 2 + ε * (1 - ε) * a + 3 / 2 * ε ^ 2 := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have hn2 : 0 ≤ a ^ 2 + ε * (2 + ε) * a := by positivity
  exact ⟨by linarith only [h1, hn1], by linarith only [h2, hn2]⟩

private lemma lowerWeps_x_deriv_bounds :
    ∃ M_W : ℝ, 0 ≤ M_W ∧ ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 / 4 →
      let wFun := fun x => lowerWeps ε (lowerY x)
      ∃ w1 w2 : ℝ → ℝ, ∀ {x : ℝ}, xiStar < x →
        HasDerivAt wFun (w1 x) x ∧ HasDerivAt w1 (w2 x) x ∧
        |w1 x| ≤ M_W ∧ |w2 x| ≤ M_W := by
  refine ⟨1600 * π ^ 2, by positivity, fun {ε} hε0 hε1 => ?_⟩
  let gw : ℝ → ℝ := fun a => (1 + ε) ^ 2 * a ^ 2 / mtDen ε a
  let P1 : ℝ → ℝ := fun a => (1 + ε) ^ 2 * (ε * (2 - ε) * a ^ 2 + 4 * ε ^ 2 * a)
  let P1' : ℝ → ℝ := fun a => (1 + ε) ^ 2 * (2 * ε * (2 - ε) * a + 4 * ε ^ 2)
  let D' : ℝ → ℝ := fun a => 2 * a + ε * (2 - ε)
  let gw1 : ℝ → ℝ := fun a => P1 a / mtDen ε a ^ 2
  let gw2 : ℝ → ℝ := fun a => (P1' a * mtDen ε a - 2 * P1 a * D' a) / mtDen ε a ^ 3
  let a1 : ℝ → ℝ := fun x => -(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
  let a2 : ℝ → ℝ := fun x =>
    π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
      Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
  refine ⟨fun x => gw1 (slitA x) * a1 x, fun x => gw2 (slitA x) * a1 x ^ 2 + gw1 (slitA x) * a2 x,
    fun {x} hx => ?_⟩
  have hx0 : 0 < x := xiStar_pos.trans hx
  have ha0 : 0 < slitA x := slitA_pos x
  have hden_pos : ∀ a > 0, 0 < mtDen ε a := fun a ha =>
    (mtDen_bounds hε0 hε1 ha).1.trans_lt' (by positivity)
  have hD_hasDeriv : ∀ a, HasDerivAt (mtDen ε) (D' a) a := fun a => by
    have hD_eq : mtDen ε = fun t => t ^ 2 + ε * (2 - ε) * t + 2 * ε ^ 2 := by
      ext t; unfold mtDen; ring
    rw [hD_eq]
    have h1 := (((hasDerivAt_id a).pow 2).add ((hasDerivAt_id a).const_mul (ε * (2 - ε)))).add_const (2 * ε ^ 2)
    refine h1.congr_deriv ?_
    dsimp [D']; simp; ring
  have hgw_hd : ∀ a > 0, HasDerivAt gw (gw1 a) a := fun a ha => by
    have hn : HasDerivAt (fun t => (1 + ε) ^ 2 * t ^ 2) ((1 + ε) ^ 2 * (2 * a)) a :=
      (((hasDerivAt_id a).pow 2).const_mul ((1 + ε) ^ 2)).congr_deriv (by simp; ring)
    refine (hn.div (hD_hasDeriv a) (hden_pos a ha).ne').congr_deriv ?_
    dsimp [gw1, P1]; unfold mtDen
    have hdn : (a + ε) ^ 2 + ε ^ 2 * (1 - a) ≠ 0 := by
      have := hden_pos a ha; unfold mtDen at this; exact this.ne'
    field_simp [hdn]; ring
  have hgw1_hd : ∀ a > 0, HasDerivAt gw1 (gw2 a) a := fun a ha => by
    have hp : HasDerivAt P1 (P1' a) a := by
      have h1 := (((hasDerivAt_id a).pow 2).const_mul (ε * (2 - ε))).add ((hasDerivAt_id a).const_mul (4 * ε ^ 2))
      exact (h1.const_mul ((1 + ε) ^ 2)).congr_deriv (by dsimp [P1']; simp; ring)
    have hq : HasDerivAt (fun t => mtDen ε t ^ 2) (2 * mtDen ε a * D' a) a :=
      ((hD_hasDeriv a).pow 2).congr_deriv (by simp; ring)
    refine (hp.div hq (pow_pos (hden_pos a ha) 2).ne').congr_deriv ?_
    dsimp [gw2]
    have hdn : mtDen ε a ≠ 0 := (hden_pos a ha).ne'
    field_simp [hdn]; ring
  have hev : (fun t => lowerWeps ε (lowerY t)) =ᶠ[𝓝 x] fun t => gw (slitA t) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact lowerWeps_eq hε0 ht
  have hsa := slitA_derivs x
  have hd_w1 : HasDerivAt (fun t => lowerWeps ε (lowerY t)) (gw1 (slitA x) * a1 x) x := by
    have hev_a : (fun t => gw (slitA t)) =ᶠ[𝓝 x] fun t => lowerWeps ε (lowerY t) := hev.symm
    exact (((hgw_hd (slitA x) ha0).comp x hsa.1).congr_deriv (by simp)).congr_of_eventuallyEq hev_a
  have hd_w2 : HasDerivAt (fun t => gw1 (slitA t) * a1 t)
      (gw2 (slitA x) * a1 x ^ 2 + gw1 (slitA x) * a2 x) x := by
    have h1 := ((hgw1_hd (slitA x) ha0).comp x hsa.1).congr_deriv (by simp)
    exact (h1.mul hsa.2.1).congr_deriv (by ring)
  obtain ⟨hD_lo, hD_hi⟩ := mtDen_bounds hε0 hε1 ha0
  set a := slitA x
  set s := a + ε
  have hs_pos : 0 < s := by positivity
  have ha_le_s : a ≤ s := by dsimp [s]; linarith
  have hε_le_s : ε ≤ s := by dsimp [s]; linarith
  have h2ε : 0 ≤ 2 - ε := by linarith
  have h1ε : (1 + ε) ^ 2 ≤ 4 := by nlinarith
  have hP1_bd : |P1 a| ≤ 4 * (2 * ε * a ^ 2 + 4 * ε ^ 2 * a) := by
    have hnn : 0 ≤ P1 a := by dsimp [P1]; positivity
    rw [abs_of_nonneg hnn]
    dsimp [P1]
    calc (1 + ε) ^ 2 * (ε * (2 - ε) * a ^ 2 + 4 * ε ^ 2 * a)
        ≤ 4 * (ε * 2 * a ^ 2 + 4 * ε ^ 2 * a) := by gcongr; linarith
      _ = 4 * (2 * ε * a ^ 2 + 4 * ε ^ 2 * a) := by ring
  have hP1a_bd : |P1 a| * a ≤ 24 * s ^ 4 := by
    calc |P1 a| * a ≤ 4 * (2 * ε * a ^ 3 + 4 * ε ^ 2 * a ^ 2) := by
          linarith only [mul_le_mul_of_nonneg_right hP1_bd ha0.le]
      _ ≤ 4 * (2 * s * s ^ 3 + 4 * s ^ 2 * s ^ 2) := by gcongr
      _ = 24 * s ^ 4 := by ring
  have hgw1_a : |gw1 a| * a ≤ 96 := by
    have hD2_lo : s ^ 4 / 4 ≤ mtDen ε a ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hD_lo 2
      linarith only [this]
    dsimp [gw1]
    rw [abs_div, abs_of_pos (pow_pos (hden_pos a ha0) 2), div_mul_eq_mul_div]
    calc |P1 a| * a / mtDen ε a ^ 2 ≤ (24 * s ^ 4) / (s ^ 4 / 4) := by gcongr
      _ = 96 := by field_simp [hs_pos.ne']; ring
  have hP1'_bd : |P1' a| ≤ 32 * ε * s := by
    have hnn : 0 ≤ P1' a := by dsimp [P1']; positivity
    rw [abs_of_nonneg hnn]
    dsimp [P1']
    calc (1 + ε) ^ 2 * (2 * ε * (2 - ε) * a + 4 * ε ^ 2)
        ≤ 4 * (2 * ε * 2 * s + 4 * ε * s) := by gcongr; linarith
      _ = 32 * ε * s := by ring
  have hD'_bd : |D' a| ≤ 2 * s := by
    have hnn : 0 ≤ D' a := by dsimp [D']; positivity
    rw [abs_of_nonneg hnn]
    dsimp [D']; linarith
  have hgw2_a2 : |gw2 a| * a ^ 2 ≤ 1280 := by
    have hD3_lo : s ^ 6 / 8 ≤ mtDen ε a ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hD_lo 3
      linarith only [this]
    have hnum_bd : |P1' a * mtDen ε a - 2 * P1 a * D' a| * a ^ 2 ≤ 160 * s ^ 6 := by
      have h1 : |P1' a * mtDen ε a| * a ^ 2 ≤ 64 * s ^ 6 := by
        rw [abs_mul, abs_of_pos (hden_pos a ha0)]
        calc |P1' a| * mtDen ε a * a ^ 2 ≤ (32 * ε * s) * (2 * s ^ 2) * s ^ 2 := by gcongr
          _ ≤ (32 * s * s) * (2 * s ^ 2) * s ^ 2 := by gcongr
          _ = 64 * s ^ 6 := by ring
      have h2' : |2 * P1 a * D' a| * a ^ 2 ≤ 96 * s ^ 6 := by
        rw [abs_mul, abs_mul, abs_of_pos zero_lt_two]
        calc 2 * |P1 a| * |D' a| * a ^ 2 = 2 * (|P1 a| * a) * |D' a| * a := by ring
          _ ≤ 2 * (24 * s ^ 4) * (2 * s) * s := by gcongr
          _ = 96 * s ^ 6 := by ring
      calc |P1' a * mtDen ε a - 2 * P1 a * D' a| * a ^ 2
          ≤ (|P1' a * mtDen ε a| + |2 * P1 a * D' a|) * a ^ 2 :=
            mul_le_mul_of_nonneg_right (abs_sub _ _) (sq_nonneg _)
        _ ≤ 64 * s ^ 6 + 96 * s ^ 6 := by
            have := add_le_add h1 h2'
            linarith only [this]
        _ = 160 * s ^ 6 := by ring
    dsimp [gw2]
    rw [abs_div, abs_of_pos (pow_pos (hden_pos a ha0) 3), div_mul_eq_mul_div]
    calc |P1' a * mtDen ε a - 2 * P1 a * D' a| * a ^ 2 / mtDen ε a ^ 3
        ≤ (160 * s ^ 6) / (s ^ 6 / 8) := by gcongr
      _ = 1280 := by field_simp [hs_pos.ne']; ring
  obtain ⟨ha1_bd, ha2_bd⟩ := hsa.2.2 hx0.le
  have hpi := Real.pi_pos
  have hpi1 : 1 ≤ π ^ 2 := by have := Real.pi_gt_three; nlinarith
  have hw1_bd : |gw1 a * a1 x| ≤ 1600 * π ^ 2 := by
    rw [abs_mul]
    calc |gw1 a| * |a1 x| ≤ |gw1 a| * (π * a) := by gcongr
      _ = (|gw1 a| * a) * π := by ring
      _ ≤ 96 * π := by gcongr
      _ ≤ 1600 * π ^ 2 := by have := Real.pi_gt_three; nlinarith only [this]
  have hw2_bd : |gw2 a * a1 x ^ 2 + gw1 a * a2 x| ≤ 1600 * π ^ 2 := by
    have ht1 : |gw2 a * a1 x ^ 2| ≤ 1280 * π ^ 2 := by
      rw [abs_mul, abs_pow]
      have ha1_sq : |a1 x| ^ 2 ≤ (π * a) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha1_bd 2
      calc |gw2 a| * |a1 x| ^ 2 ≤ |gw2 a| * (π * a) ^ 2 := by gcongr
        _ = (|gw2 a| * a ^ 2) * π ^ 2 := by ring
        _ ≤ 1280 * π ^ 2 := by gcongr
    have ht2 : |gw1 a * a2 x| ≤ 288 * π ^ 2 := by
      rw [abs_mul]
      calc |gw1 a| * |a2 x| ≤ |gw1 a| * (3 * π ^ 2 * a) := by gcongr
        _ = (|gw1 a| * a) * (3 * π ^ 2) := by ring
        _ ≤ 96 * (3 * π ^ 2) := by gcongr
        _ = 288 * π ^ 2 := by ring
    calc |gw2 a * a1 x ^ 2 + gw1 a * a2 x|
        ≤ |gw2 a * a1 x ^ 2| + |gw1 a * a2 x| := abs_add_le _ _
      _ ≤ 1280 * π ^ 2 + 288 * π ^ 2 := add_le_add ht1 ht2
      _ ≤ 1600 * π ^ 2 := by have : 0 ≤ π ^ 2 := by positivity; linarith
  exact ⟨hd_w1, hd_w2, hw1_bd, hw2_bd⟩

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
    rw [← one_sub_lowerY_sq ht, sub_sub_cancel, Real.sqrt_sq (yOfX_mem ht).1.le]
  have hd_inner : ∀ t, HasDerivAt (fun u => 1 - slitA u)
      ((π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) t := fun t => by
    exact ((hasDerivAt_const t (1 : ℝ)).sub (slitA_derivs t).1).congr_deriv (by ring)
  have hysq_pos : 0 < 1 - slitA x := by rw [h1y]; positivity
  have hd_y : HasDerivAt lowerY (y1 x) x := by
    have hsq := ((hd_inner x).sqrt hysq_pos.ne')
    refine (hsq.congr_of_eventuallyEq hev_y.symm).congr_deriv ?_
    rw [Real.sqrt_eq_iff_mul_self_eq hysq_pos.le hy_pos.le |>.mpr (by nlinarith [h1y])]
    dsimp [y1]; ring
  have hd_y1 : HasDerivAt y1 (y2 x) x := by
    have hneg_a1 := ((slitA_derivs x).2.1).neg
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
    dsimp [y2, y1]
    field_simp [hy_pos.ne']
    ring
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
      have hsh_ge1 : 1 ≤ Real.sinh (π * ξ) := (sinh_pi_gt_one hξ.1).le
      have hnum_ge : π * (x - xiStar) ≤ Real.cosh (π * x) - Real.sqrt 2 := by
        rw [hch_xi, eq_div_iff (sub_pos.mpr hx).ne'] at hslope
        nlinarith only [hslope, hsh_ge1, Real.pi_pos, sub_pos.mpr hx]
      have hden_le : Real.cosh (π * x) + Real.sqrt 2 ≤ D_ch := by
        have := Real.cosh_le_cosh.mpr (by
          rw [abs_of_pos (mul_pos Real.pi_pos hx0), abs_of_pos (by positivity [xiStar_pos])]
          exact mul_le_mul_of_nonneg_left hx1 Real.pi_pos.le)
        dsimp [D_ch]; linarith
      have hsq_ge : c_y ^ 2 * (x - xiStar) ≤ lowerY x ^ 2 := by
        rw [← h1y]; unfold slitA
        have h1y' : 1 - 2 * Real.sqrt 2 / (Real.cosh (π * x) + Real.sqrt 2) =
            (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by
          have := Real.cosh_pos (π * x)
          field_simp [(by positivity : Real.cosh (π * x) + Real.sqrt 2 ≠ 0)]; ring
        rw [h1y']
        have hc2 : c_y ^ 2 = π / D_ch := Real.sq_sqrt (by positivity)
        rw [hc2]
        calc (π / D_ch) * (x - xiStar) = (π * (x - xiStar)) / D_ch := by ring
          _ ≤ (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by
              calc (π * (x - xiStar)) / D_ch
                  ≤ (Real.cosh (π * x) - Real.sqrt 2) / D_ch := by gcongr
                _ ≤ (Real.cosh (π * x) - Real.sqrt 2) / (Real.cosh (π * x) + Real.sqrt 2) := by
                    gcongr; nlinarith only [hnum_ge, Real.pi_pos, sub_pos.mpr hx]
      have hsq_ge' : (c_y * Real.sqrt (x - xiStar)) ^ 2 ≤ lowerY x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (sub_pos.mpr hx).le]; exact hsq_ge
      have hc1 : c_min * Real.sqrt (x - xiStar) ≤ c_y * Real.sqrt (x - xiStar) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      have hys : c_y * Real.sqrt (x - xiStar) ≤ lowerY x := by
        nlinarith only [hsq_ge', hy_pos, hcy_pos, Real.sqrt_nonneg (x - xiStar)]
      exact hc1.trans hys
    · have hm : min (x - xiStar) 1 = 1 := min_eq_right (by linarith)
      rw [hm, Real.sqrt_one, mul_one]
      have hch_le : Real.cosh (π * (xiStar + 1)) ≤ Real.cosh (π * x) :=
        Real.cosh_le_cosh.mpr (by
          rw [abs_of_pos (by positivity [xiStar_pos]), abs_of_pos (mul_pos Real.pi_pos hx0)]
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
    rw [abs_div, abs_of_pos (by positivity)]
    calc |π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) * slitA x| / (2 * lowerY x)
        ≤ π / (2 * (c_min * Real.sqrt m)) := by gcongr
      _ = (π / (2 * c_min)) * (Real.sqrt m)⁻¹ := by ring
      _ ≤ M_Y * (Real.sqrt m)⁻¹ := by
          gcongr; dsimp [M_Y]; exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hy2_abs : |y2 x| ≤ M_Y * m ^ (-(3 / 2 : ℝ)) := by
    have hm1 : m ≤ 1 := min_le_right _ _
    have hsm1 : Real.sqrt m ≤ 1 := Real.sqrt_le_one.mpr hm1
    have hnum2_bd : |-(π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x)| ≤ 3 * π ^ 2 := by
      rw [abs_neg]; exact ha2_bd.trans (by nlinarith only [pow_pos hpi 2, ha_le1])
    have ha1_sq_bd : (-(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) ^ 2 ≤ π ^ 2 := by
      have h1 := ha1_bd.trans (by nlinarith only [hpi, ha_le1] : π * slitA x ≤ π)
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      simpa [sq_abs] using this
    have hm32 : m ^ (3 / 2 : ℝ) = m * Real.sqrt m := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm_pos, Real.rpow_one, Real.sqrt_eq_rpow]
    have ht1 : |-(π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) / (2 * lowerY x)| ≤
        (3 * π ^ 2 / (2 * c_min)) * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_div, abs_of_pos (by positivity)]
      calc _ ≤ (3 * π ^ 2) / (2 * (c_min * Real.sqrt m)) := by gcongr
        _ = (3 * π ^ 2 / (2 * c_min)) * (Real.sqrt m)⁻¹ := by ring
        _ ≤ (3 * π ^ 2 / (2 * c_min)) * (m ^ (3 / 2 : ℝ))⁻¹ := by
            gcongr
            rw [inv_le_inv₀ (Real.sqrt_pos.mpr hm_pos) (Real.rpow_pos_of_pos hm_pos _), hm32]
            nlinarith only [hm1, Real.sqrt_pos.mpr hm_pos]
        _ = (3 * π ^ 2 / (2 * c_min)) * m ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_neg hm_pos.le]
    have ht2 : |(-(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x) ^ 2 /
        (4 * lowerY x ^ 3)| ≤ (π ^ 2 / (4 * c_min ^ 3)) * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity)]
      have hy3_lb : c_min ^ 3 * m ^ (3 / 2 : ℝ) ≤ lowerY x ^ 3 := by
        have h3 := pow_le_pow_left₀ (by positivity) hy_lb 3
        have hsm3 : Real.sqrt m ^ 3 = m ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hm_pos.le]; norm_num
        linarith only [h3, show (c_min * Real.sqrt m) ^ 3 = c_min ^ 3 * Real.sqrt m ^ 3 by ring, hsm3]
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
  have hq_hd : HasDerivAt q (q1 x) x := by
    have hd := (hasDerivAt_const x ε).div (hsa.1.add_const ε) hs0.ne'
    refine hd.congr_deriv ?_
    dsimp [q1]; field_simp [hs0.ne']; ring
  have hq1_hd : HasDerivAt q1 (q2 x) x := by
    have hn : HasDerivAt (fun t => -ε * a1 t) (-ε * a2 x) x := (hsa.2.1.const_mul (-ε))
    have hd : HasDerivAt (fun t => (slitA t + ε) ^ 2) (2 * (slitA x + ε) * a1 x) x :=
      ((hsa.1.add_const ε).pow 2).congr_deriv (by simp; ring)
    refine (hn.div hd (pow_pos hs0 2).ne').congr_deriv ?_
    dsimp [q2]; field_simp [hs0.ne']; ring
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
    have h1 := ((hu_hd.arctan).const_mul (-2 : ℝ))
    refine h1.congr_deriv ?_
    dsimp [t1]; ring
  have ht2_hd : HasDerivAt t1 (t2 x) x := by
    have hden' : HasDerivAt (fun t => 1 + u t ^ 2) (2 * u x * u1 x) x :=
      ((hasDerivAt_const x (1 : ℝ)).add ((hu_hd.pow 2))).congr_deriv (by simp; ring)
    have hq_hd' := (hu1_hd.div hden' hden_pos.ne').const_mul (-2 : ℝ)
    refine hq_hd'.congr_deriv ?_
    dsimp [t2]; field_simp [hden_pos.ne']; ring
  have hq_bd : 0 ≤ q x ∧ q x ≤ 1 := ⟨by dsimp [q]; positivity, (div_le_one hs0).mpr (by linarith)⟩
  obtain ⟨ha1_bd, ha2_bd⟩ := hsa.2.2 hx0.le
  have hεa_sq : ε * slitA x ≤ (slitA x + ε) ^ 2 := by
    nlinarith only [sq_nonneg (slitA x - ε), hε0, ha0.le]
  have hq1_bd : |q1 x| ≤ π := by
    dsimp [q1]
    rw [abs_div, abs_of_pos (pow_pos hs0 2), abs_mul, abs_neg, abs_of_nonneg hε0]
    calc ε * |a1 x| / (slitA x + ε) ^ 2 ≤ ε * (π * slitA x) / (slitA x + ε) ^ 2 := by gcongr
      _ = π * (ε * slitA x / (slitA x + ε) ^ 2) := by ring
      _ ≤ π * 1 := by gcongr; exact (div_le_one (pow_pos hs0 2)).mpr hεa_sq
      _ = π := mul_one _
  have hq2_bd : |q2 x| ≤ 5 * π ^ 2 := by
    dsimp [q2]
    rw [abs_div, abs_of_pos (pow_pos hs0 3)]
    have hnum1 : |-ε * a2 x * (slitA x + ε)| ≤ 3 * π ^ 2 * (slitA x + ε) ^ 3 := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hε0, abs_of_pos hs0]
      calc ε * |a2 x| * (slitA x + ε) ≤ ε * (3 * π ^ 2 * slitA x) * (slitA x + ε) := by gcongr
        _ = 3 * π ^ 2 * (ε * slitA x) * (slitA x + ε) := by ring
        _ ≤ 3 * π ^ 2 * (slitA x + ε) ^ 2 * (slitA x + ε) := by gcongr
        _ = 3 * π ^ 2 * (slitA x + ε) ^ 3 := by ring
    have hnum2 : |2 * ε * a1 x ^ 2| ≤ 2 * π ^ 2 * (slitA x + ε) ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hε0, abs_pow]
      have ha1_sq : |a1 x| ^ 2 ≤ (π * slitA x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha1_bd 2
      have ha_s : slitA x ≤ slitA x + ε := by linarith
      calc 2 * ε * |a1 x| ^ 2 ≤ 2 * ε * (π * slitA x) ^ 2 := by gcongr
        _ = 2 * π ^ 2 * (ε * slitA x) * slitA x := by ring
        _ ≤ 2 * π ^ 2 * (slitA x + ε) ^ 2 * (slitA x + ε) := by gcongr
        _ = 2 * π ^ 2 * (slitA x + ε) ^ 3 := by ring
    calc |-ε * a2 x * (slitA x + ε) + 2 * ε * a1 x ^ 2| / (slitA x + ε) ^ 3
        ≤ (3 * π ^ 2 * (slitA x + ε) ^ 3 + 2 * π ^ 2 * (slitA x + ε) ^ 3) / (slitA x + ε) ^ 3 := by
          gcongr; exact (abs_add_le _ _).trans (add_le_add hnum1 hnum2)
      _ = 5 * π ^ 2 := by field_simp [pow_pos hs0 3 |>.ne']; ring
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
      rw [abs_mul, abs_of_pos (yOfX_mem hx).1]
      calc |q1 x| * lowerY x ≤ π * 1 := by gcongr
        _ ≤ π * m ^ (-(1 / 2 : ℝ)) := by gcongr
    have h2 : |q x * y1 x| ≤ M_Y * m ^ (-(1 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hq_bd.1]
      calc q x * |y1 x| ≤ 1 * (M_Y * m ^ (-(1 / 2 : ℝ))) := by gcongr
        _ = M_Y * m ^ (-(1 / 2 : ℝ)) := by ring
    dsimp [u1]
    exact (abs_add_le _ _).trans (by linarith only [add_le_add h1 h2])
  have hu2_bd : |u2 x| ≤ (5 * π ^ 2 + 2 * π * M_Y + M_Y) * m ^ (-(3 / 2 : ℝ)) := by
    have h1 : |q2 x * lowerY x| ≤ 5 * π ^ 2 * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_pos (yOfX_mem hx).1]
      calc |q2 x| * lowerY x ≤ 5 * π ^ 2 * 1 := by gcongr
        _ ≤ 5 * π ^ 2 * m ^ (-(3 / 2 : ℝ)) := by gcongr
    have h2 : |2 * q1 x * y1 x| ≤ 2 * π * M_Y * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos zero_lt_two]
      calc 2 * |q1 x| * |y1 x| ≤ 2 * π * (M_Y * m ^ (-(1 / 2 : ℝ))) := by gcongr
        _ ≤ 2 * π * (M_Y * m ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = 2 * π * M_Y * m ^ (-(3 / 2 : ℝ)) := by ring
    have h3 : |q x * y2 x| ≤ M_Y * m ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hq_bd.1]
      calc q x * |y2 x| ≤ 1 * (M_Y * m ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = M_Y * m ^ (-(3 / 2 : ℝ)) := by ring
    dsimp [u2]
    have htri := (abs_add_le (q2 x * lowerY x + 2 * q1 x * y1 x) (q x * y2 x)).trans
      (add_le_add_right (abs_add_le _ _) _)
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
        rw [abs_mul, abs_of_pos zero_lt_two, abs_le]
        constructor <;> nlinarith [sq_nonneg (|u x| - 1), abs_nonneg (u x), sq_abs (u x)]
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
        simpa [abs_mul, abs_of_pos hden_pos] using abs_sub (u2 x * (1 + u x ^ 2)) (2 * u x * u1 x ^ 2)
      calc _ ≤ (|u2 x| * (1 + u x ^ 2) + |2 * u x * u1 x ^ 2|) / (1 + u x ^ 2) ^ 2 := by gcongr
        _ = |u2 x| / (1 + u x ^ 2) + |2 * u x * u1 x ^ 2| / (1 + u x ^ 2) ^ 2 := by
            field_simp [hden_pos.ne']; ring
    have hsum := htri.trans (add_le_add hfrac1 hfrac2)
    have : 0 ≤ 2 * (π + M_Y) * m ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith only [hsum, this, show 0 ≤ 2 * (π + M_Y) ^ 2 * m ^ (-(3 / 2 : ℝ)) by positivity]
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
  have hW_chain := zeta_chain_deriv_bounds (f := fun x => lowerWeps (c' ^ (-2 : ℝ)) (lowerY x))
    (f1 := w1) (f2 := w2) (M := M_tot) hMtot_nn
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
  have hθ_chain := zeta_chain_deriv_bounds (f := fun x => unwrappedTheta (c' ^ (-2 : ℝ)) x)
    (f1 := fun x => deriv thetaOutX x + t1 x)
    (f2 := fun x => deriv (deriv thetaOutX) x + t2 x)
    (M := M_tot) hMtot_nn
    (fun {x} hx => by
      have hd_s := (hS2_diff x hx).1.hasDerivAt
      have hd_t := (ht_spec hx).1
      have hsub := hd_s.add hd_t
      have heq : (fun u => thetaOutX u + -2 * Real.arctan (c' ^ (-2 : ℝ) * lowerY u / (slitA u + c' ^ (-2 : ℝ)))) =
          unwrappedTheta (c' ^ (-2 : ℝ)) := by
        ext u; unfold unwrappedTheta; ring
      rw [heq] at hsub
      have h1 : |deriv thetaOutX x + t1 x| ≤
          M_S2 * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) + M_θ * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by
        have hs1 := hS2_1 x hx
        have ht1 := (ht_spec hx).2.2.1
        have := abs_add_le (deriv thetaOutX x) (t1 x)
        calc _ ≤ _ + _ := this
          _ ≤ _ := add_le_add (by linarith only [hs1, Real.exp_le_one_iff.mpr (by have := Real.pi_pos; have := xiStar_pos; nlinarith : -(π * x) ≤ 0),
              show M_S2 * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) * Real.exp (-(π * x)) ≤
                M_S2 * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) by
                exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by have := Real.pi_pos; have := xiStar_pos; nlinarith))]) ht1
      refine ⟨hsub, h1.trans ?_⟩
      have hnn : 0 ≤ (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (lt_min (sub_pos.mpr hx) one_pos).le _
      calc (M_S2 + M_θ) * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ))
          ≤ M_tot * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := by gcongr; exact le_max_right _ _
        _ = M_tot * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)) := rfl)
    (fun {x} hx => by
      have hd_s := (hS2_diff x hx).2.hasDerivAt
      have hd_t := (ht_spec hx).2.1
      refine ⟨hd_s.add hd_t, ?_⟩
      have hs2 := hS2_2 x hx
      have ht2 := (ht_spec hx).2.2.2
      have hexp1 : Real.exp (-(π * x)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := Real.pi_pos; have := xiStar_pos; nlinarith)
      have h1 : |deriv (deriv thetaOutX) x| ≤ M_S2 * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) :=
        hs2.trans (mul_le_of_le_one_right (by positivity) hexp1)
      have htri := (abs_add_le _ _).trans (add_le_add h1 ht2)
      calc _ ≤ (M_S2 + M_θ) * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by linarith only [htri]
        _ ≤ M_tot * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ)) := by gcongr; exact le_max_right _ _)
  obtain ⟨CW, -, hW_all⟩ := hW_chain
  obtain ⟨Cθ, -, hθ_all⟩ := hθ_chain
  refine ⟨fun ζ => w1 (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ))),
    fun ζ => w2 (xOfZeta c' ζ) * (2 / (c' * rhoU (xOfZeta c' ζ))) ^ 2 +
      w1 (xOfZeta c' ζ) * (-(4 * rhoUDeriv (xOfZeta c' ζ) / (c' ^ 2 * rhoU (xOfZeta c' ζ) ^ 3))),
    fun ζ => (deriv thetaOutX (xOfZeta c' ζ) + t1 (xOfZeta c' ζ)) * (2 / (c' * rhoU (xOfZeta c' ζ))),
    fun ζ => (deriv (deriv thetaOutX) (xOfZeta c' ζ) + t2 (xOfZeta c' ζ)) * (2 / (c' * rhoU (xOfZeta c' ζ))) ^ 2 +
      (deriv thetaOutX (xOfZeta c' ζ) + t1 (xOfZeta c' ζ)) *
        (-(4 * rhoUDeriv (xOfZeta c' ζ) / (c' ^ 2 * rhoU (xOfZeta c' ζ) ^ 3))),
    fun {ζ} hζ => ?_⟩
  obtain ⟨hWa, hWb, hWc, hWd⟩ := hW_all hc0 hζ
  obtain ⟨hθa, hθb, hθc, hθd⟩ := hθ_all hc0 hζ
  exact ⟨hWa, hWb, hθa, hθb, hWc, hWd, hθc, hθd⟩

end

end FormalResearch.ModularBootstrap.FiveTerm
