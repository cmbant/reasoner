module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeCoord
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3a

/-!
# Slit Weight `W_1(ζ)` and Chain-Rule Template (`ctl:freeze`)

Proves:
* `lowerWeps_mem_Icc`: `0 ≤ lowerWeps ε (lowerY x) ≤ 1` for `ε ≥ 0`, `x > ξ_*`;
* `sin_lowerThetaEps_eq`: exact unwrapped phase identity inside `Real.sin`;
* `zeta_chain_deriv_bounds`: `C^2` chain-rule template from `x > ξ_*` to `ζ > 0`;
* `lowerWeps_x_deriv_bounds`: uniform `x`-derivative bounds on `x ↦ lowerWeps ε (lowerY x)` for `0 ≤ ε ≤ 1/4`.
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
  rw [div_lt_one (by have := Real.cosh_pos (π * x); positivity)]
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
    have hnum : (1 + (ε : ℂ)) * (1 + (Complex.I * (y : ℂ)) ^ 2) = (((1 + ε) * a : ℝ) : ℂ) := by
      rw [e1]; push_cast; ring
    have e2 : 1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) =
        (((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)) := by
      rw [e1]; push_cast; ring
    rw [hnum, e2]
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

private lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have hz_ne : z ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have harg_lt : |z.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hsin := Complex.sin_arg z
  have hcos := Complex.cos_arg hz_ne
  have htan : Real.tan z.arg = z.im / z.re := by
    rw [Real.tan_eq_sin_div_cos, hsin, hcos]
    have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
    field_simp [hnorm]
  rw [← htan, Real.arctan_tan (abs_lt.mp harg_lt).1 (abs_lt.mp harg_lt).2]

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
  have hexp_G : Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) =
      Complex.exp (Complex.I * (thetaOutX x : ℂ)) := by
    have hnorm : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := by
      rw [hG_polar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW_pos,
        show Complex.I * (thetaOut y : ℂ) = (thetaOut y : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := Complex.norm_mul_exp_arg_mul_I (Gout (Complex.I * (y : ℂ)))
    rw [hnorm] at h1
    nth_rewrite 2 [hG_polar] at h1
    have h1' : ((Wslit y : ℝ) : ℂ) * Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) =
        ((Wslit y : ℝ) : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ)) := by
      rwa [mul_comm Complex.I (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)]
    have h2 : Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (y : ℂ))) : ℂ)) =
        Complex.exp (Complex.I * (thetaOut y : ℂ)) :=
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hW_pos.ne') h1'
    rwa [← thetaOut_yOfX hx]
  set a := slitA x
  have ha0 : 0 < a := slitA_pos x
  have h1y : 1 - y ^ 2 = a := one_sub_lowerY_sq hx
  have hden_pos : 0 < a + ε := by linarith
  let z_d : ℂ := ((a + ε : ℝ) : ℂ) + Complex.I * ((ε * y : ℝ) : ℂ)
  have hzd_re : 0 < z_d.re := by simp [z_d]; exact hden_pos
  have hmt_eq : lowerMt ε (Complex.I * (y : ℂ)) = (((1 + ε) * a : ℝ) : ℂ) / z_d := by
    unfold lowerMt
    have e1 : 1 + (Complex.I * (y : ℂ)) ^ 2 = ((a : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq, ← h1y]; push_cast; ring
    have hnum : (1 + (ε : ℂ)) * (1 + (Complex.I * (y : ℂ)) ^ 2) = (((1 + ε) * a : ℝ) : ℂ) := by
      rw [e1]; push_cast; ring
    have e2 : 1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)) = z_d := by
      rw [e1]; dsimp [z_d]; push_cast; ring
    rw [hnum, e2]
  have harg_mt : Complex.arg (lowerMt ε (Complex.I * (y : ℂ))) =
      -Real.arctan (ε * y / (a + ε)) := by
    have hnum_pos : 0 < (1 + ε) * a := mul_pos (by linarith) ha0
    have hns_pos : 0 < Complex.normSq z_d :=
      Complex.normSq_pos.mpr (fun h0 => by rw [h0] at hzd_re; simp at hzd_re)
    have hinv_re : 0 < z_d⁻¹.re := by
      rw [Complex.inv_re]
      exact div_pos hzd_re hns_pos
    have hre_mt : 0 < (lowerMt ε (Complex.I * (y : ℂ))).re := by
      rw [hmt_eq, div_eq_mul_inv, Complex.re_ofReal_mul]
      exact mul_pos hnum_pos hinv_re
    rw [arg_eq_arctan_of_re_pos hre_mt]
    have hdiv_im_re : (lowerMt ε (Complex.I * (y : ℂ))).im / (lowerMt ε (Complex.I * (y : ℂ))).re =
        -(ε * y / (a + ε)) := by
      have hre : (lowerMt ε (Complex.I * (y : ℂ))).re =
          ((1 + ε) * a) * ((a + ε) / Complex.normSq z_d) := by
        rw [hmt_eq, div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re]
        simp [z_d]
      have him : (lowerMt ε (Complex.I * (y : ℂ))).im =
          ((1 + ε) * a) * (-(ε * y) / Complex.normSq z_d) := by
        rw [hmt_eq, div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im]
        simp [z_d]
      rw [him, hre]
      field_simp [hnum_pos.ne', hden_pos.ne', hns_pos.ne']
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
lemma zeta_chain_deriv_bounds {f f1 f2 : ℝ → ℝ} {M C_x : ℝ} (hM : 0 ≤ M) (hCx_pos : 0 < C_x)
    (hx_bounds : ∀ {c' ζ : ℝ}, 0 < c' → 0 < ζ →
      let x := xOfZeta c' ζ; let r := x - xiStar
      let x1 := 2 / (c' * rhoU x); let x2 := -(4 * rhoUDeriv x / (c' ^ 2 * rhoU x ^ 3))
      0 < x1 ∧ x1 ≤ r / ζ ∧ |x2| ≤ C_x * r / ζ ^ 2 ∧
      (xiStar + 1 ≤ x → x1 ≤ C_x / c' ∧ |x2| ≤ C_x / c' ^ 2))
    (hf1 : ∀ {x : ℝ}, xiStar < x → HasDerivAt f (f1 x) x ∧
      |f1 x| ≤ M * (min (x - xiStar) 1) ^ (-(1 / 2 : ℝ)))
    (hf2 : ∀ {x : ℝ}, xiStar < x → HasDerivAt f1 (f2 x) x ∧
      |f2 x| ≤ M * (min (x - xiStar) 1) ^ (-(3 / 2 : ℝ))) :
    ∀ {c' ζ : ℝ}, 0 < c' → 0 < ζ →
      let C := M * max 1 C_x + M * (1 + C_x + C_x ^ 2) + 1
      let g1 := fun u => f1 (xOfZeta c' u) * (2 / (c' * rhoU (xOfZeta c' u)))
      let g2 := fun u => f2 (xOfZeta c' u) * (2 / (c' * rhoU (xOfZeta c' u))) ^ 2 +
        f1 (xOfZeta c' u) * (-(4 * rhoUDeriv (xOfZeta c' u) / (c' ^ 2 * rhoU (xOfZeta c' u) ^ 3)))
      HasDerivAt (fun u => f (xOfZeta c' u)) (g1 ζ) ζ ∧
      HasDerivAt g1 (g2 ζ) ζ ∧
      |g1 ζ| ≤ C * (ζ⁻¹ + c'⁻¹) ∧
      |g2 ζ| ≤ C * (ζ ^ (-2 : ℝ) + c' ^ (-2 : ℝ)) := by
  intro c' ζ hc0 hζ C g1 g2
  have hC_pos : 0 < C := by positivity
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
      have hsr : (Real.sqrt r)⁻¹ * r = Real.sqrt r := by
        rw [inv_mul_eq_div]; exact Real.div_sqrt
      have hsr1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr hr1
      have hM_le : M ≤ C := by
        dsimp [C]
        nlinarith [le_max_left (1 : ℝ) C_x, show 0 ≤ M * (1 + C_x + C_x ^ 2) by positivity]
      calc |g1 ζ| = |f1 x| * x1 := by dsimp [g1, x, x1]; rw [abs_mul, abs_of_pos hx1_pos]
        _ ≤ (M * (Real.sqrt r)⁻¹) * (r / ζ) := by gcongr
        _ = M * ((Real.sqrt r)⁻¹ * r) / ζ := by ring
        _ = M * Real.sqrt r / ζ := by rw [hsr]
        _ ≤ M * 1 / ζ := by gcongr
        _ = M * ζ⁻¹ := by ring
        _ ≤ C * ζ⁻¹ := by gcongr
        _ ≤ C * (ζ⁻¹ + c'⁻¹) := by gcongr; exact le_add_of_nonneg_right (inv_nonneg.mpr hc0.le)
    · have hmin : min r 1 = 1 := min_eq_right hr1.le
      rw [hmin, Real.one_rpow, mul_one] at hf1_bd
      have hx1_inf := (hx_inf (by dsimp [r] at hr1; linarith)).1
      have hM_le : M * C_x ≤ C := by
        dsimp [C]
        nlinarith [le_max_right (1 : ℝ) C_x, show 0 ≤ M * (1 + C_x + C_x ^ 2) by positivity]
      calc |g1 ζ| = |f1 x| * x1 := by dsimp [g1, x, x1]; rw [abs_mul, abs_of_pos hx1_pos]
        _ ≤ M * (C_x / c') := by gcongr
        _ = (M * C_x) * c'⁻¹ := by ring
        _ ≤ C * c'⁻¹ := by gcongr
        _ ≤ C * (ζ⁻¹ + c'⁻¹) := by gcongr; exact le_add_of_nonneg_left (inv_nonneg.mpr hζ.le)
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
      have hM_le : M * (1 + C_x) ≤ C := by
        dsimp [C]
        have : 0 ≤ M * C_x ^ 2 := by positivity
        have : 0 ≤ M * max 1 C_x := by positivity
        linarith
      calc |g2 ζ| ≤ |f2 x * x1 ^ 2| + |f1 x * x2| := by dsimp [g2]; exact abs_add_le _ _
        _ ≤ M / ζ ^ 2 + M * C_x / ζ ^ 2 := add_le_add ht1 ht2
        _ = M * (1 + C_x) * (ζ ^ 2)⁻¹ := by ring
        _ ≤ C * (ζ ^ 2)⁻¹ := by gcongr
        _ ≤ C * ((ζ ^ 2)⁻¹ + (c' ^ 2)⁻¹) := by
            gcongr; exact le_add_of_nonneg_right (by positivity)
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
      have hM_le : M * (C_x + C_x ^ 2) ≤ C := by
        dsimp [C]
        have : 0 ≤ M * max 1 C_x := by positivity
        linarith
      calc |g2 ζ| ≤ |f2 x * x1 ^ 2| + |f1 x * x2| := by dsimp [g2]; exact abs_add_le _ _
        _ ≤ M * C_x ^ 2 / c' ^ 2 + M * C_x / c' ^ 2 := add_le_add ht1 ht2
        _ = M * (C_x + C_x ^ 2) * (c' ^ 2)⁻¹ := by ring
        _ ≤ C * (c' ^ 2)⁻¹ := by gcongr
        _ ≤ C * ((ζ ^ 2)⁻¹ + (c' ^ 2)⁻¹) := by
            gcongr; exact le_add_of_nonneg_left (by positivity)

/-! ### 4. `slitA` derivatives and `W_1(x)` bounds -/

/-- `slitA'` and `slitA''` relative bounds on `ℝ`. -/
lemma slitA_derivs (x : ℝ) :
    let a1 := -(π * Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
    let a2 := π ^ 2 * (2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)) * slitA x
    HasDerivAt slitA a1 x ∧
    HasDerivAt (fun t => -(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) a2 x ∧
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
    field_simp [(hpos_den x).ne']
  have hd_a2 : HasDerivAt (fun t => -(π * Real.sinh (π * t) / (Real.cosh (π * t) + Real.sqrt 2)) * slitA t) a2 x := by
    refine (hd_ratio.mul (hd_a x)).congr_deriv ?_
    dsimp [a2]
    field_simp [(hpos_den x).ne']
    ring
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
    have hr1_nn : 0 ≤ Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 := by positivity
    have hr1_nn' : 0 ≤ Real.sinh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) := by positivity
    have hr2_nn : 0 ≤ Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2) := by positivity
    have hsq : Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 ≤ 1 := by
      rw [← div_pow]; exact pow_le_one₀ hr1_nn' hrat1
    have hmid : |2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 -
        Real.cosh (π * x) / (Real.cosh (π * x) + Real.sqrt 2)| ≤ 3 := by
      rw [show 2 * Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2 =
        2 * (Real.sinh (π * x) ^ 2 / (Real.cosh (π * x) + Real.sqrt 2) ^ 2) by ring]
      rw [abs_le]
      constructor <;> linarith only [hsq, hrat2, hr1_nn, hr2_nn]
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

lemma lowerWeps_x_deriv_bounds :
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
    dsimp [D']; simp
  have hgw_hd : ∀ a > 0, HasDerivAt gw (gw1 a) a := fun a ha => by
    have hn : HasDerivAt (fun t => (1 + ε) ^ 2 * t ^ 2) ((1 + ε) ^ 2 * (2 * a)) a :=
      (((hasDerivAt_id a).pow 2).const_mul ((1 + ε) ^ 2)).congr_deriv (by simp)
    refine (hn.div (hD_hasDeriv a) (hden_pos a ha).ne').congr_deriv ?_
    dsimp [gw1, P1, D']; unfold mtDen
    have hdn : (a + ε) ^ 2 + ε ^ 2 * (1 - a) ≠ 0 := by
      have := hden_pos a ha; unfold mtDen at this; exact this.ne'
    field_simp [hdn]; ring
  have hgw1_hd : ∀ a > 0, HasDerivAt gw1 (gw2 a) a := fun a ha => by
    have hp_sq : HasDerivAt (fun t : ℝ => ε * (2 - ε) * t ^ 2) (2 * ε * (2 - ε) * a) a :=
      (((hasDerivAt_id a).pow 2).const_mul (ε * (2 - ε))).congr_deriv (by simp; ring)
    have hp_lin : HasDerivAt (fun t : ℝ => 4 * ε ^ 2 * t) (4 * ε ^ 2) a := by
      simpa using (hasDerivAt_id a).const_mul (4 * ε ^ 2)
    have hp : HasDerivAt P1 (P1' a) a := by
      refine ((hp_sq.add hp_lin).const_mul ((1 + ε) ^ 2)).congr_deriv ?_
      dsimp [P1']
    have hq : HasDerivAt (fun t => mtDen ε t ^ 2) (2 * mtDen ε a * D' a) a :=
      ((hD_hasDeriv a).pow 2).congr_deriv (by simp)
    refine (hp.div hq (pow_pos (hden_pos a ha) 2).ne').congr_deriv ?_
    dsimp [gw2]
    have hdn : mtDen ε a ≠ 0 := (hden_pos a ha).ne'
    field_simp [hdn]
  have hev : (fun t => lowerWeps ε (lowerY t)) =ᶠ[𝓝 x] fun t => gw (slitA t) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact lowerWeps_eq hε0 ht
  have hsa := slitA_derivs x
  have hd_w1 : HasDerivAt (fun t => lowerWeps ε (lowerY t)) (gw1 (slitA x) * a1 x) x := by
    have hcomp : HasDerivAt (fun t => gw (slitA t)) (gw1 (slitA x) * a1 x) x :=
      ((hgw_hd (slitA x) ha0).comp x hsa.1).congr_deriv (by dsimp [a1])
    exact hcomp.congr_of_eventuallyEq hev
  have hd_w2 : HasDerivAt (fun t => gw1 (slitA t) * a1 t)
      (gw2 (slitA x) * a1 x ^ 2 + gw1 (slitA x) * a2 x) x := by
    have h1 : HasDerivAt (fun t => gw1 (slitA t)) (gw2 (slitA x) * a1 x) x :=
      ((hgw1_hd (slitA x) ha0).comp x hsa.1).congr_deriv (by dsimp [a1])
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
    have h2 : 2 * ε * (2 - ε) * a ≤ 2 * ε * 2 * s := by
      have : (2 - ε) * a ≤ 2 * s := by nlinarith only [ha_le_s, ha0, hε0]
      nlinarith only [this, hε0]
    have h3 : 4 * ε ^ 2 ≤ 4 * ε * s := by
      have : ε * ε ≤ ε * s := mul_le_mul_of_nonneg_left hε_le_s hε0
      linarith
    calc (1 + ε) ^ 2 * (2 * ε * (2 - ε) * a + 4 * ε ^ 2)
        ≤ 4 * (2 * ε * 2 * s + 4 * ε * s) := by
          apply mul_le_mul h1ε (add_le_add h2 h3) (by positivity) (by positivity)
      _ = 32 * ε * s := by ring
  have hD'_bd : |D' a| ≤ 2 * s := by
    have hnn : 0 ≤ D' a := by dsimp [D']; positivity
    rw [abs_of_nonneg hnn]
    dsimp [D', s]
    nlinarith only [hε0, hε1]
  have hgw2_a2 : |gw2 a| * a ^ 2 ≤ 1280 := by
    have hD3_lo : s ^ 6 / 8 ≤ mtDen ε a ^ 3 := by
      have := pow_le_pow_left₀ (by positivity) hD_lo 3
      linarith only [this]
    have ha2_s2 : a ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ ha0.le ha_le_s 2
    have hnum_bd : |P1' a * mtDen ε a - 2 * P1 a * D' a| * a ^ 2 ≤ 160 * s ^ 6 := by
      have h1 : |P1' a * mtDen ε a| * a ^ 2 ≤ 64 * s ^ 6 := by
        have hden_nn : 0 ≤ mtDen ε a := (hden_pos a ha0).le
        rw [abs_mul, abs_of_pos (hden_pos a ha0)]
        calc |P1' a| * mtDen ε a * a ^ 2
            ≤ (32 * ε * s) * (2 * s ^ 2) * s ^ 2 := by gcongr
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
        _ ≤ 64 * s ^ 6 + 96 * s ^ 6 := by linarith only [add_le_add h1 h2']
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
      _ ≤ 1600 * π ^ 2 := by
          have : 0 ≤ π ^ 2 := by positivity
          linarith only [this]
  exact ⟨hd_w1, hd_w2, hw1_bd, hw2_bd⟩

end

end FormalResearch.ModularBootstrap.FiveTerm
