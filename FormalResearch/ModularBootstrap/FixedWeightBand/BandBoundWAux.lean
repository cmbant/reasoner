module

public import FormalResearch.ModularBootstrap.StripMultiplier.BandBound

/-!
# Weight-Free Ingredients of the Band Bound at Weight `w` (Proposition `Y_V`, `vlo:YV`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, proof of Proposition `Y_V` (`vlo:YV`):
the hypotheses of the shared strip band reduction (`teb:mellin`, Proposition TE.3(1)) that do not
involve the weight `w` or `Q`.  They depend only on the weight-free edge functions of
Lemma `J4.0` (`vlo:J40`), the Langer chart `pg : LangerChartSpec` and the scale constants of the
Virasoro witness `StripMultiplier.yvWitness pg` (whose weight-free fields are reused verbatim, so
that the `Langer` bookkeeping `langerDelta_props`, `langerNegV_*` of `StripMultiplier.BandBound`
is imported rather than copied).

* `edgeInvNu`, `edgeInvNu_abs_le`, `edgeInvNu_continuousOn`: the derivative `(1/ν')' = -ν''/ν'²` of
  the dispersion coordinate, bounded by `C (1+τ)^{-2}` (integrable on `(0, ∞)`);
* `yv_tau0_below`, `yv_tau0_band`: the `τ₀` threshold bound (`τ₀(x) ≤ A₀ c'^{-1/3}` for `t < T`) and
  the band bound `τ₀(x)² ≤ C_τ c'^{-2/3} ṽ` on `T ≤ t ≤ t(-R)` (from `lemma_S6`);
* `yv_rhoR_le`: `2 ρ_R ≤ 0.035` on the annulus `R ≤ c₀ c'^{2/3}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart ChartGeometry StripBand
open FormalResearch.ModularBootstrap.StripMultiplier

/-! ### Section 1: The dispersion coordinate `ν` -/

/-- `(1/ν')' = -ν''/(ν')²`, the derivative of the inverse of `ν'(τ) = edgeNuDeriv τ`. -/
noncomputable def edgeInvNu (τ : ℝ) : ℝ := -(edgeNuDeriv2 τ) / (edgeNuDeriv τ) ^ 2

lemma edgeInvNu_abs_le (pg : LangerChartSpec) {τ : ℝ} (hτ : 0 ≤ τ) :
    |edgeInvNu τ| ≤ ((yvWitness pg).C_ν2 / (yvWitness pg).cnu₁ ^ 2) * ((1 + τ) ^ 2)⁻¹ := by
  let w := yvWitness pg
  have hcnu₁_pos : 0 < w.cnu₁ := w.hcnu₁
  have h1τ : 0 < 1 + τ := by linarith
  have hnu_lb : w.cnu₁ * (1 + τ) ≤ edgeNuDeriv τ := (w.hnu_bd τ hτ).1
  have hnu_pos : 0 < edgeNuDeriv τ := lt_of_lt_of_le (mul_pos hcnu₁_pos h1τ) hnu_lb
  have h2 : |edgeNuDeriv2 τ| ≤ w.C_ν2 := w.hnu2_bd τ hτ
  have hCν2_nn : 0 ≤ w.C_ν2 := w.hC_ν2.le
  have hden_lb : w.cnu₁ ^ 2 * (1 + τ) ^ 2 ≤ edgeNuDeriv τ ^ 2 := by
    have : (w.cnu₁ * (1 + τ)) ^ 2 ≤ edgeNuDeriv τ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnu_lb 2
    linarith [show (w.cnu₁ * (1 + τ)) ^ 2 = w.cnu₁ ^ 2 * (1 + τ) ^ 2 by ring]
  unfold edgeInvNu
  rw [abs_div, abs_neg, abs_of_pos (sq_pos_of_pos hnu_pos)]
  calc |edgeNuDeriv2 τ| / edgeNuDeriv τ ^ 2
      ≤ w.C_ν2 / (w.cnu₁ ^ 2 * (1 + τ) ^ 2) := by gcongr
    _ = (w.C_ν2 / w.cnu₁ ^ 2) * ((1 + τ) ^ 2)⁻¹ := by
        field_simp [hcnu₁_pos.ne', h1τ.ne']

lemma edgeInvNu_continuousOn (pg : LangerChartSpec) : ContinuousOn edgeInvNu (Ioi 0) := by
  have h1 : Continuous edgeNuDeriv :=
    continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_edgeNuDeriv τ).continuousAt
  have hcpi : Continuous (fun s : ℝ => Real.cosh (Real.pi * s)) :=
    Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  have hch2 : Continuous (fun s : ℝ => Real.cosh (Real.pi * s / 2)) :=
    Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2)
  have hsh2 : Continuous (fun s : ℝ => Real.sinh (Real.pi * s / 2)) :=
    Real.continuous_sinh.comp ((continuous_const.mul continuous_id).div_const 2)
  have h2 : Continuous edgeNuDeriv2 := by
    unfold edgeNuDeriv2 edgeX0Deriv2 edgeY0Deriv2 edgeX0Deriv edgeY0Deriv edgeX0 edgeY0
    have hcosh_ne : ∀ s : ℝ, Real.cosh (Real.pi * s) ≠ 0 := fun s => (Real.cosh_pos _).ne'
    have hx0_c : Continuous (fun s => Real.arsinh √(Real.cosh (Real.pi * s)) / Real.pi) :=
      (hcpi.sqrt.arsinh).div_const Real.pi
    have hy0_c : Continuous (fun s => Real.arsinh (√2 * Real.sinh (Real.pi * s / 2)) / Real.pi) :=
      ((continuous_const.mul hsh2).arsinh).div_const Real.pi
    have hsqrt_c : Continuous (fun s => √(Real.cosh (Real.pi * s))) := hcpi.sqrt
    have hrpow_c : Continuous (fun s => Real.cosh (Real.pi * s) ^ (3 / 2 : ℝ)) :=
      hcpi.rpow_const fun s => Or.inl (hcosh_ne s)
    have hx_d2_c : Continuous (fun s => (Real.pi / (2 * √2)) * Real.cosh (Real.pi * s / 2) /
        Real.cosh (Real.pi * s) ^ (3 / 2 : ℝ)) :=
      (continuous_const.mul hch2).div hrpow_c fun s => by positivity [Real.cosh_pos (Real.pi * s)]
    have hy_d2_c : Continuous (fun s => -(Real.pi / (2 * √2)) * Real.sinh (Real.pi * s / 2) /
        Real.cosh (Real.pi * s) ^ (3 / 2 : ℝ)) :=
      (continuous_const.mul hsh2).div hrpow_c fun s => by positivity [Real.cosh_pos (Real.pi * s)]
    have hx_d1_c : Continuous (fun s => (1 / √2) * Real.sinh (Real.pi * s / 2) /
        √(Real.cosh (Real.pi * s))) :=
      (continuous_const.mul hsh2).div hsqrt_c fun s => Real.sqrt_ne_zero'.mpr (Real.cosh_pos _)
    have hy_d1_c : Continuous (fun s => (1 / √2) * Real.cosh (Real.pi * s / 2) /
        √(Real.cosh (Real.pi * s))) :=
      (continuous_const.mul hch2).div hsqrt_c fun s => Real.sqrt_ne_zero'.mpr (Real.cosh_pos _)
    exact continuous_const.mul (((hx_d2_c.mul hy0_c).add ((continuous_const.mul hx_d1_c).mul
      hy_d1_c)).add (hx0_c.mul hy_d2_c))
  exact h2.neg.continuousOn.div (h1.pow 2).continuousOn fun τ hτ =>
    pow_ne_zero 2 (lt_of_lt_of_le (mul_pos (yvWitness pg).hcnu₁
      (by linarith [(mem_Ioi.mp hτ).le]))
      ((yvWitness pg).hnu_bd τ (mem_Ioi.mp hτ).le).1).ne'

lemma edgeInvNu_integrable (pg : LangerChartSpec) : IntegrableOn edgeInvNu (Ioi 0) := by
  obtain ⟨hint_sq, _⟩ := integral_Ioi_inv_add_one_sq
  refine (hint_sq.const_mul ((yvWitness pg).C_ν2 / (yvWitness pg).cnu₁ ^ 2)).mono'
    ((edgeInvNu_continuousOn pg).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
  rw [Real.norm_eq_abs]
  exact edgeInvNu_abs_le pg (mem_Ioi.mp hτ).le

lemma edgeInvNu_int_le (pg : LangerChartSpec) :
    ∫ τ in Ioi (0 : ℝ), |edgeInvNu τ| ≤ (yvWitness pg).C_ν2 / (yvWitness pg).cnu₁ ^ 2 := by
  obtain ⟨hint_sq, hval_sq⟩ := integral_Ioi_inv_add_one_sq
  have h_int_abs : IntegrableOn (fun τ => |edgeInvNu τ|) (Ioi 0) :=
    (edgeInvNu_integrable pg).abs
  calc ∫ τ in Ioi (0 : ℝ), |edgeInvNu τ|
      ≤ ∫ τ in Ioi (0 : ℝ), ((yvWitness pg).C_ν2 / (yvWitness pg).cnu₁ ^ 2) * ((1 + τ) ^ 2)⁻¹ :=
        setIntegral_mono_on h_int_abs (hint_sq.const_mul _) measurableSet_Ioi
          fun τ hτ => edgeInvNu_abs_le pg (mem_Ioi.mp hτ).le
    _ = ((yvWitness pg).C_ν2 / (yvWitness pg).cnu₁ ^ 2) * ∫ τ in Ioi (0 : ℝ), ((1 + τ) ^ 2)⁻¹ :=
        integral_const_mul _ _
    _ = (yvWitness pg).C_ν2 / (yvWitness pg).cnu₁ ^ 2 := by rw [hval_sq, mul_one]

/-! ### Section 2: The annulus and the `τ₀` bounds -/

lemma yv_rhoR_le (pg : LangerChartSpec) {A_thr c' R : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1) :
    2 * rhoR (yvBandParams pg A_thr) c' R ≤ 0.035 := by
  let w := yvWitness pg
  have hc'_pos : 0 < c' := by linarith [yvThresh_ge pg A_thr]
  have hR_le_c0 : R ≤ w.c₀ * c' ^ (2 / 3 : ℝ) := (langerDelta_props hc' hR_lb hR_ub).2.1
  unfold rhoR
  have h1 : c' ^ (-(1 / 3 : ℝ)) * √R ≤ √w.c₀ := by
    have hrt : √R ≤ √w.c₀ * c' ^ (1 / 3 : ℝ) := by
      calc √R ≤ √(w.c₀ * c' ^ (2 / 3 : ℝ)) := Real.sqrt_le_sqrt hR_le_c0
        _ = √w.c₀ * √(c' ^ (2 / 3 : ℝ)) := Real.sqrt_mul w.hc₀_pos.le _
        _ = √w.c₀ * c' ^ (1 / 3 : ℝ) := by
            rw [Real.sqrt_eq_rpow (c' ^ (2 / 3 : ℝ)), ← Real.rpow_mul hc'_pos.le]; norm_num
    have hc_cancel : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc'_pos]; simp
    calc c' ^ (-(1 / 3 : ℝ)) * √R ≤ c' ^ (-(1 / 3 : ℝ)) * (√w.c₀ * c' ^ (1 / 3 : ℝ)) := by gcongr
      _ = √w.c₀ * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) := by ring
      _ = √w.c₀ := by rw [hc_cancel, mul_one]
  calc 2 * ((yvBandParams pg A_thr).κ_ζ * c' ^ (-(1 / 3 : ℝ)) * √R)
      = 2 * kappaV * (c' ^ (-(1 / 3 : ℝ)) * √R) := by dsimp [yvBandParams]; ring
    _ ≤ (2 * kappaV) * √w.c₀ := mul_le_mul_of_nonneg_left h1 (by have := kappaV_pos; positivity)
    _ ≤ 0.035 := w.hc₀_rho

/-- `τ₀(ξ) ≤ (3/2) κ_V √v c'^{-1/3}` for `ξ = Δ(-v)`, `0 ≤ v ≤ R`, from `lemma_S6`
(`pg.bL`-chart bound `hS6_tau0`). -/
lemma yv_tau0_le_of_mem (pg : LangerChartSpec) {A_thr c' R ξ : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hξ_mem : ξ ∈ Icc (langerDelta pg c' 0) (langerDelta pg c' (-R))) :
    0 ≤ langerNegV pg c' R ξ ∧
    langerNegV pg c' R ξ ≤ R ∧
    0 ≤ edgeTau0 c' ξ ∧
    edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * kappaV * √(langerNegV pg c' R ξ) * c' ^ (-(1 / 3 : ℝ)) := by
  let w := yvWitness pg
  have hc'_pos : 0 < c' := by linarith [yvThresh_ge pg A_thr]
  have hR_le_c0 : R ≤ w.c₀ * c' ^ (2 / 3 : ℝ) := (langerDelta_props hc' hR_lb hR_ub).2.1
  have hv_spec := langerNegV_mem_and_eq hc' hR_lb hR_ub hξ_mem
  set v := langerNegV pg c' R ξ
  have hvc : v * c' ^ (-(2 / 3 : ℝ)) ≤ w.c₀ := by
    have hc_cancel : c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc'_pos]; simp
    calc v * c' ^ (-(2 / 3 : ℝ)) ≤ (w.c₀ * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hv_spec.1.2.trans hR_le_c0) (Real.rpow_nonneg hc'_pos.le _)
      _ = w.c₀ := by rw [mul_assoc, hc_cancel, mul_one]
  have hS6 := w.hS6_tau0 c' v hc'_pos hv_spec.1.1 hvc
  rw [hv_spec.2] at hS6
  have h1C : 1 + w.C₁ * w.c₀ ≤ 3 / 2 := by linarith [w.hc₀_C1]
  have hc_inv13 : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc'_pos]; simp
  refine ⟨hv_spec.1.1, hv_spec.1.2, hS6.2.2.2.2.1, ?_⟩
  have h2 : c' ^ (1 / 3 : ℝ) * edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * (kappaV * √v) :=
    hS6.2.2.2.2.2.trans (mul_le_mul_of_nonneg_right h1C
      (mul_nonneg kappaV_pos.le (Real.sqrt_nonneg _)))
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hc'_pos.le (-(1 / 3 : ℝ)))
  rw [← mul_assoc, mul_comm (c' ^ (-(1 / 3 : ℝ))), hc_inv13, one_mul] at h3
  calc edgeTau0 c' ξ ≤ c' ^ (-(1 / 3 : ℝ)) * ((3 / 2 : ℝ) * (kappaV * √v)) := h3
    _ = (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := by ring

lemma yv_tau0_below (pg : LangerChartSpec) {A_thr c' R T : ℝ} (hA_thr : 0 ≤ A_thr)
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr)) {ξ : ℝ} (hξ : ξ < T) :
    edgeTau0 c' ξ ≤ (yvBandParams pg A_thr).A_0 * c' ^ (-(1 / 3 : ℝ)) := by
  let w := yvWitness pg
  have hc'_pos : 0 < c' := by linarith [yvThresh_ge pg A_thr]
  have hProps := langerDelta_props hc' hR_lb hR_ub
  have hR_pos : 0 < R := hProps.1
  have hA_le_R : max A_thr 1 ≤ R := hProps.2.2.1
  have hg_mono : StrictMonoOn (fun v => langerDelta pg c' (-v)) (Icc 0 R) := hProps.2.2.2.2.1
  by_cases hle0 : ξ ≤ langerDelta pg c' 0
  · have hsq_le : √(3 * ξ / c') ≤ xiStar := by
      rw [langerDelta_zero] at hle0
      by_cases hξ0 : ξ ≤ 0
      · rw [Real.sqrt_eq_zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) hc'_pos.le)]
        exact xiStar_pos.le
      · push Not at hξ0
        rw [Real.sqrt_le_iff]
        refine ⟨xiStar_pos.le, ?_⟩
        rw [div_le_iff₀ hc'_pos]
        linarith
    have htau0_0 : edgeTau0 c' ξ = 0 := by
      unfold edgeTau0; simp only [hsq_le, ↓reduceIte]
    rw [htau0_0]
    dsimp [yvBandParams]
    have := kappaV_pos
    positivity
  · push Not at hle0
    have hA_mem : A_thr ∈ Icc (0 : ℝ) R := ⟨hA_thr, (le_max_left A_thr 1).trans hA_le_R⟩
    have hAmax_mem : max A_thr 1 ∈ Icc (0 : ℝ) R := ⟨by positivity, hA_le_R⟩
    have hA_le_R_d : langerDelta pg c' (-A_thr) ≤ langerDelta pg c' (-R) :=
      hg_mono.monotoneOn hA_mem ⟨hR_pos.le, le_rfl⟩ hA_mem.2
    have hA_le_Amax_d : langerDelta pg c' (-A_thr) ≤ langerDelta pg c' (-max A_thr 1) :=
      hg_mono.monotoneOn hA_mem hAmax_mem (le_max_left A_thr 1)
    have hξ_mem : ξ ∈ Icc (langerDelta pg c' 0) (langerDelta pg c' (-R)) :=
      ⟨hle0.le, (hξ.le.trans hT_hi).trans hA_le_R_d⟩
    obtain ⟨hv0, hvR, -, hub⟩ := yv_tau0_le_of_mem pg hc' hR_lb hR_ub hξ_mem
    have hv_spec := langerNegV_mem_and_eq hc' hR_lb hR_ub hξ_mem
    set v := langerNegV pg c' R ξ
    have hv_le_A : v ≤ max A_thr 1 := by
      by_contra hlt; push Not at hlt
      have hlt_d := hg_mono hAmax_mem hv_spec.1 hlt
      dsimp only at hlt_d
      rw [hv_spec.2] at hlt_d
      linarith [hξ.le, hT_hi, hA_le_Amax_d]
    calc edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := hub
      _ ≤ (3 / 2 : ℝ) * kappaV * √(max A_thr 1) * c' ^ (-(1 / 3 : ℝ)) := by
          have hκ := kappaV_pos; gcongr

lemma yv_tau0_band (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T) {ξ : ℝ}
    (hξ : ξ ∈ Icc T (langerDelta pg c' (-R))) :
    edgeTau0 c' ξ ^ 2 ≤ (yvBandParams pg A_thr).C_τ * c' ^ (-(2 / 3 : ℝ)) *
      (-(-langerNegV pg c' R ξ)) := by
  have hc'_pos : 0 < c' := by linarith [yvThresh_ge pg A_thr]
  have hξ_mem : ξ ∈ Icc (langerDelta pg c' 0) (langerDelta pg c' (-R)) :=
    ⟨hT_lo.trans hξ.1, hξ.2⟩
  obtain ⟨hv0, -, hτ0, hub⟩ := yv_tau0_le_of_mem pg hc' hR_lb hR_ub hξ_mem
  set v := langerNegV pg c' R ξ
  have hsq : edgeTau0 c' ξ ^ 2 ≤ ((3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hτ0 hub 2
  have hsq_rw : ((3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ))) ^ 2 =
      (9 / 4 : ℝ) * kappaV ^ 2 * c' ^ (-(2 / 3 : ℝ)) * v := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hv0,
      ← Real.rpow_natCast (c' ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc'_pos.le]
    norm_num; ring
  rw [hsq_rw] at hsq
  simpa [neg_neg, yvBandParams] using hsq

end FormalResearch.ModularBootstrap.FixedWeightBand
