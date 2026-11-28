module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerFoldChart
public import FormalResearch.ModularBootstrap.FiveTerm.LowerVirasoroPsi
public import FormalResearch.ModularBootstrap.Contour.VirasoroScaleChoice

/-!
# Unconditional Shifted Airy Chart `phi`, `uhat` at Virasoro (`LowerChartMain`)

Discharges the `chart : LowerChart c0Star gamma0 c1 phi uhat` field of `LowerMainInputs`
unconditionally by feeding `virasoroPsiEps_spec` into `fj_inverse_chart` (Lemma FJ (2)):

* `virasoroMu`, `virasoroLam`, `virasoroPsiChart`, `virasoroUhat`, `virasoroC1`, `virasoroPhi`.
* `virasoroChart_holds : LowerChart c0Star gamma0 virasoroC1 virasoroPhi virasoroUhat`.
* `lowerLangerPhase_band`: extends `LowerLangerBridge` across the whole `O(c^{2/3})`
  chart band `-5 * virasoroC1 ^ 2 * c ^ (2 / 3) ≤ u < 0`.
* `virasoroUhat_phase_match`: exact phase-transfer identity on that band, matching Paper II
  (`cts:phic-exp`, `cts:boas`):
  `2 * √(-u) * (virasoroUhat c u - u) = arg(G_out(iy)) + 2 arg(M̃_{c^{-2}}(iy))`.
-/

@[expose] public section

open Complex Metric Set Filter Topology Real
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.ModularBootstrap.Contour

noncomputable section

/-- Outer-band chart scaling `μ_c = β⁻¹ c^{-2/3}`. -/
def virasoroMu (c : ℝ) : ℝ := betaTip⁻¹ * c ^ (-(2 / 3 : ℝ))

/-- Outer-band chart shift scale `λ_c = β c^{-1/3}`. -/
def virasoroLam (c : ℝ) : ℝ := betaTip * c ^ (-(1 / 3 : ℝ))

/-- Virasoro fold-chart shift family `ψ_c := ψ_{c^{-2}}` on `w ∈ ball 0 ρ_ψ`. -/
def virasoroPsiChart (c : ℝ) (w : ℂ) : ℂ := virasoroPsiEps (c ^ (-2 : ℝ)) w

/-- Explicit real-axis inverse coordinate `û_c(ũ) = ũ + λ_c Re(ψ_c(μ_c ũ))` (`fj:lemma` (2)). -/
def virasoroUhat (c u : ℝ) : ℝ := fjUhat virasoroLam virasoroMu virasoroPsiChart c u

/-- Packaged analytic shift parameters and Langer band threshold for choosing `virasoroC1`. -/
structure ChartParamsPack where
  ρ_ψ : ℝ
  r_ψ : ℝ
  M_ψ : ℝ
  C_ψ : ℝ
  r_τ : ℝ
  hrψ_pos : 0 < r_ψ
  hrψ_lt : r_ψ < ρ_ψ
  hMψ_nn : 0 ≤ M_ψ
  hCψ_nn : 0 ≤ C_ψ
  hrτ_pos : 0 < r_τ
  hrτ_le : r_τ ≤ 1 / (10 * π)
  hψ_spec : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 4 →
    DifferentiableOn ℂ (virasoroPsiEps ε) (ball 0 ρ_ψ) ∧
    (∀ a ∈ ball (0 : ℂ) ρ_ψ, virasoroPsiEps ε (starRingEnd ℂ a) = starRingEnd ℂ (virasoroPsiEps ε a)) ∧
    (∀ a ∈ closedBall (0 : ℂ) r_ψ, ‖virasoroPsiEps ε a‖ ≤ M_ψ ∧ ‖deriv (virasoroPsiEps ε) a‖ ≤ M_ψ) ∧
    |(virasoroPsiEps ε 0).re - (c0Star / cStar) / betaTip| ≤ C_ψ * ε ∧
    |(deriv (virasoroPsiEps ε) 0).re - gamma0| ≤ C_ψ * ε
  hψ_phase : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 4 →
    ∀ x : ℝ, xiStar < x → tauPhase x < r_ψ →
      x < xiStar + r_τ ∧
      lowerYVal x ∈ Ioo (0 : ℝ) 1 ∧
      2 * betaTip ^ (3 / 2 : ℝ) * √(tauPhase x) * (virasoroPsiEps ε ((-(tauPhase x) : ℝ) : ℂ)).re =
        Complex.arg (Gout (Complex.I * (lowerYVal x : ℂ))) +
          2 * Complex.arg ((1 + ε : ℂ) * (1 + (Complex.I * (lowerYVal x : ℂ)) ^ 2) /
            (1 + (Complex.I * (lowerYVal x : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (lowerYVal x : ℂ))))
  δ_band : ℝ
  hδ_band_pos : 0 < δ_band
  hband : ∀ {c u : ℝ}, 0 < c → -(δ_band * c ^ (2 / 3 : ℝ)) ≤ u → u < 0 →
    tauPhase (√(3 * virasoroDeltaChart c u / c)) = -u / (betaTip * c ^ (2 / 3 : ℝ))

lemma chart_params_nonempty : Nonempty ChartParamsPack := by
  obtain ⟨ρ_ψ, r_ψ, M_ψ, C_ψ, r_τ, hrψ_pos, hrψ_lt, hMψ_nn, hCψ_nn, hrτ_pos, hrτ_le,
    hψ_spec, hψ_phase⟩ := virasoroPsiEps_spec
  let pg := lemmaGPotentialInput_virasoro
  let r₀ : ℝ := min (min pg.r_A (1 / 2)) (xiStar / 2)
  have hr₀_pos : 0 < r₀ := by have := pg.hr_A_pos; have := xiStar_pos; positivity
  let r_ξ : ℝ := min virasoroRXiInf ((xiStar + r₀) ^ 2 / 3 - xiBar)
  have hr_ξ_pos : 0 < r_ξ := by
    have h1 : 0 < virasoroRXiInf := virasoroRXiInf_pos
    have h2 : xiBar < (xiStar + r₀) ^ 2 / 3 := by
      unfold xiBar
      have : xiStar ^ 2 < (xiStar + r₀) ^ 2 := sq_lt_sq' (by linarith [xiStar_pos]) (by linarith)
      linarith
    exact lt_min h1 (by linarith)
  have hcont_xi : ContinuousAt virasoroXiInf 0 :=
    (langerCore.hxiInf_an 0 (mem_ball_self virasoroRUInf_pos)).continuousAt
  obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ := Metric.continuousAt_iff.mp hcont_xi r_ξ hr_ξ_pos
  let δ : ℝ := min (min δ_u virasoroRUInf) (2 * virasoroBV ^ 2)
  have hδ_pos : 0 < δ := lt_min (lt_min hδ_u_pos virasoroRUInf_pos) (by have := virasoroBV_pos; positivity)
  let δ_band : ℝ := δ / 2
  have hδ_band_pos : 0 < δ_band := half_pos hδ_pos
  have hband : ∀ {c u : ℝ}, 0 < c → -(δ_band * c ^ (2 / 3 : ℝ)) ≤ u → u < 0 →
      tauPhase (√(3 * virasoroDeltaChart c u / c)) = -u / (betaTip * c ^ (2 / 3 : ℝ)) := by
    intro c u hc0 hu1 hu2
    set w : ℝ := u * c ^ (-(2 / 3 : ℝ)) with hw_def
    have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 (2 / 3)
    have hcm23_pos : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 (-(2 / 3))
    have hc23_mul : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc0]; simp
    have hw_abs : |w| < δ := by
      rw [hw_def, abs_mul, abs_of_pos hcm23_pos]
      have hδc_nn : 0 ≤ δ_band * c ^ (2 / 3 : ℝ) := mul_nonneg hδ_band_pos.le hc23_pos.le
      have hu_abs : |u| ≤ δ_band * c ^ (2 / 3 : ℝ) := abs_le.mpr ⟨hu1, by linarith only [hu2, hδc_nn]⟩
      calc |u| * c ^ (-(2 / 3 : ℝ))
          ≤ (δ_band * c ^ (2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hu_abs hcm23_pos.le
        _ = δ_band * (c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) := by ring
        _ = δ_band := by rw [hc23_mul, mul_one]
        _ < δ := half_lt_self hδ_pos
    have hw_ball : (w : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact hw_abs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hξ_im : (virasoroXiInf (w : ℂ)).im = 0 :=
      virasoroXiInf_ofReal_im (hw_abs.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
    set ξ : ℝ := (virasoroXiInf (w : ℂ)).re with hξ_def
    have hξ_c : (ξ : ℂ) = virasoroXiInf (w : ℂ) := Complex.ext rfl hξ_im.symm
    have hΔ_eq : virasoroDeltaChart c u / c = ξ := by
      unfold virasoroDeltaChart virasoroXiChartC
      rw [← Complex.ofReal_mul, ← hw_def, ← hξ_def]
      field_simp [hc0.ne']
    rw [mul_div_assoc, hΔ_eq]
    have hu_inv : virasoroUInf (ξ : ℂ) = (w : ℂ) := by
      rw [hξ_c]; exact virasoroUInf_xiInf hw_ball
    set A2 : ℝ := virasoroAC c ^ 2 with hA2_def
    have hA2_eq : A2 = 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := virasoroAC_sq c hc0.le
    have hsA : StrictAntiOn (virasoroDeltaChart c) (Icc (-A2) A2) := virasoroDeltaChart_strictAnti hc0
    have hδ_le_bv : δ_band ≤ 2 * virasoroBV ^ 2 :=
      (half_le_self hδ_pos.le).trans (min_le_right _ _)
    have hu_mem : u ∈ Icc (-A2) A2 := by
      refine ⟨?_, ?_⟩
      · rw [hA2_eq]
        have h1 : δ_band * c ^ (2 / 3 : ℝ) ≤ 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hδ_le_bv hc23_pos.le
        linarith only [hu1, h1]
      · have hA2_nn : 0 ≤ A2 := sq_nonneg _
        linarith only [hu2, hA2_nn]
    have h0_mem : (0 : ℝ) ∈ Icc (-A2) A2 := ⟨by linarith [sq_nonneg (virasoroAC c)], by positivity⟩
    have hΔ_gt : virasoroDeltaChart c 0 < virasoroDeltaChart c u := hsA hu_mem h0_mem hu2
    rw [virasoroDeltaChart_zero] at hΔ_gt
    have hξ_gt : xiBar < ξ := by
      rw [← hΔ_eq, lt_div_iff₀ hc0]
      exact hΔ_gt
    have hξ_dist : |ξ - xiBar| < r_ξ := by
      have hnorm : dist (virasoroXiInf (w : ℂ)) (xiBar : ℂ) < r_ξ := by
        rw [← virasoroXiInf_zero]
        refine hδ_u ?_
        rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        exact hw_abs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      rw [← hξ_c, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hnorm
      exact hnorm
    have hξ_pos : 0 < ξ := by
      have := xiStar_pos; unfold xiBar at hξ_gt
      nlinarith only [sq_nonneg xiStar, hξ_gt]
    set x : ℝ := Real.sqrt (3 * ξ) with hx_def
    have hx_gt : xiStar < x := by
      rw [hx_def, Real.lt_sqrt xiStar_pos.le]
      unfold xiBar at hξ_gt
      linarith only [hξ_gt]
    have hx_lt : x < xiStar + r₀ := by
      rw [hx_def, Real.sqrt_lt' (by positivity [xiStar_pos])]
      have h1 : ξ - xiBar < (xiStar + r₀) ^ 2 / 3 - xiBar :=
        (le_abs_self _).trans_lt (hξ_dist.trans_le (min_le_right _ _))
      linarith only [h1]
    have hcum := tip_potential_cumulN_eq hx_gt hx_lt
    have hcum_pos : 0 < cumulN x := by
      have h1 := cumulN_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx_gt.le) hx_gt
      rwa [cumulN_xiStar] at h1
    have hA_re_pos : 0 < (pg.A (((x - xiStar : ℝ) : ℂ))).re := by
      have hlhs_pos : 0 < (x - xiStar) ^ (3 / 2 : ℝ) * (pg.A (((x - xiStar : ℝ) : ℂ))).re := by
        rw [hcum]; exact div_pos hcum_pos kTip_pos
      exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos (by linarith only [hx_gt]) _)).mp hlhs_pos
    have hx_abs : |x - xiStar| < pg.r_A := by
      rw [abs_of_pos (by linarith only [hx_gt])]
      exact (by linarith only [hx_lt] : x - xiStar < r₀).trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hA_im : (pg.A (((x - xiStar : ℝ) : ℂ))).im = 0 := pg.hA_real _ hx_abs
    have hA_c : pg.A (((x - xiStar : ℝ) : ℂ)) = ((pg.A (((x - xiStar : ℝ) : ℂ))).re : ℂ) :=
      Complex.ext rfl hA_im
    have hA_cpow : (pg.A (((x - xiStar : ℝ) : ℂ))) ^ (2 / 3 : ℂ) =
        (((pg.A (((x - xiStar : ℝ) : ℂ))).re ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
      conv_lhs => rw [hA_c]
      rw [show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hA_re_pos.le]
    have hu_re := congrArg Complex.re hu_inv
    have hb_eq : virasoroBOfXi (ξ : ℂ) = (x : ℂ) := virasoroBOfXi_ofReal hξ_pos.le
    have hu_val : (virasoroUInf (ξ : ℂ)).re =
        -betaTip * ((x - xiStar) * (pg.A (((x - xiStar : ℝ) : ℂ))).re ^ (2 / 3 : ℝ)) := by
      unfold virasoroUInf
      dsimp only
      simp_rw [hb_eq, ← Complex.ofReal_sub]
      dsimp only [pg] at hA_cpow
      rw [hA_cpow]
      push_cast; simp; ring
    rw [hu_val, Complex.ofReal_re] at hu_re
    have htau_eq : (x - xiStar) * (pg.A (((x - xiStar : ℝ) : ℂ))).re ^ (2 / 3 : ℝ) = tauPhase x := by
      unfold tauPhase
      rw [← hcum, Real.mul_rpow (Real.rpow_nonneg (by linarith only [hx_gt]) _) hA_re_pos.le,
        ← Real.rpow_mul (by linarith only [hx_gt])]
      norm_num
    rw [htau_eq] at hu_re
    have hβ := betaTip_pos
    have hc23_eq : c ^ (-(2 / 3 : ℝ)) = (c ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le (2 / 3)
    rw [hw_def, hc23_eq] at hu_re
    rw [eq_div_iff (mul_ne_zero hβ.ne' hc23_pos.ne')]
    have hmul : tauPhase x * (betaTip * c ^ (2 / 3 : ℝ)) = -((-betaTip * tauPhase x) * c ^ (2 / 3 : ℝ)) := by ring
    rw [hmul, hu_re]
    field_simp [hc23_pos.ne']
  exact ⟨⟨ρ_ψ, r_ψ, M_ψ, C_ψ, r_τ, hrψ_pos, hrψ_lt, hMψ_nn, hCψ_nn, hrτ_pos, hrτ_le,
    hψ_spec, hψ_phase, δ_band, hδ_band_pos, hband⟩⟩

/-- Canonical parameter witness for `virasoroC1` and `virasoroPhi`. -/
def chartParams : ChartParamsPack := Classical.choice chart_params_nonempty

/-- Unconditional outer-band chart radius constant `c_1 > 0` for FIVE-L. -/
def virasoroC1 : ℝ :=
  min (virasoroBVChoice / 10)
    (min (√(chartParams.r_ψ * betaTip / 16)) (√(chartParams.δ_band / 10)))

lemma virasoroC1_pos : 0 < virasoroC1 := by
  have h1 : 0 < virasoroBVChoice / 10 := div_pos virasoroBVChoice_pos (by norm_num)
  have h2 : 0 < √(chartParams.r_ψ * betaTip / 16) :=
    Real.sqrt_pos.mpr (by have := chartParams.hrψ_pos; have := betaTip_pos; positivity)
  have h3 : 0 < √(chartParams.δ_band / 10) :=
    Real.sqrt_pos.mpr (by have := chartParams.hδ_band_pos; positivity)
  exact lt_min h1 (lt_min h2 h3)

lemma virasoroC1_small : 10 * virasoroC1 ≤ virasoroBVChoice := by
  have h1 : virasoroC1 ≤ virasoroBVChoice / 10 := min_le_left _ _
  linarith only [h1]

private lemma virasoroC1_r0_cond : 4 * virasoroC1 ^ 2 * betaTip⁻¹ ≤ chartParams.r_ψ / 4 := by
  have h1 : virasoroC1 ≤ √(chartParams.r_ψ * betaTip / 16) := (min_le_right _ _).trans (min_le_left _ _)
  have hsq : virasoroC1 ^ 2 ≤ chartParams.r_ψ * betaTip / 16 := by
    have hnn : 0 ≤ chartParams.r_ψ * betaTip / 16 := by
      have := chartParams.hrψ_pos; have := betaTip_pos; positivity
    calc virasoroC1 ^ 2
        ≤ (√(chartParams.r_ψ * betaTip / 16)) ^ 2 := pow_le_pow_left₀ virasoroC1_pos.le h1 2
      _ = chartParams.r_ψ * betaTip / 16 := Real.sq_sqrt hnn
  have hβ := betaTip_pos
  calc 4 * virasoroC1 ^ 2 * betaTip⁻¹
      ≤ 4 * (chartParams.r_ψ * betaTip / 16) * betaTip⁻¹ := by
        gcongr
    _ = chartParams.r_ψ / 4 := by field_simp [hβ.ne']; ring

private lemma virasoroC1_band_cond : 5 * virasoroC1 ^ 2 ≤ chartParams.δ_band / 2 := by
  have h1 : virasoroC1 ≤ √(chartParams.δ_band / 10) := (min_le_right _ _).trans (min_le_right _ _)
  have hsq : virasoroC1 ^ 2 ≤ chartParams.δ_band / 10 := by
    have hnn : 0 ≤ chartParams.δ_band / 10 := by have := chartParams.hδ_band_pos; positivity
    calc virasoroC1 ^ 2
        ≤ (√(chartParams.δ_band / 10)) ^ 2 := pow_le_pow_left₀ virasoroC1_pos.le h1 2
      _ = chartParams.δ_band / 10 := Real.sq_sqrt hnn
  linarith only [hsq]

lemma virasoroChart_exists :
    ∃ phi : ℝ → ℂ → ℂ, LowerChart c0Star gamma0 virasoroC1 phi virasoroUhat := by
  have hβ := betaTip_pos
  have hc2 : ∀ {c : ℝ}, 2 ≤ c → 0 ≤ c ^ (-2 : ℝ) ∧ c ^ (-2 : ℝ) ≤ 1 / 4 := by
    intro c hc
    have hc_pos : 0 < c := by linarith only [hc]
    have hnn : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc_pos.le _
    have hle : c ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hc_pos.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      norm_num
      nlinarith only [hc]
    have h14 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num
    exact ⟨hnn, hle.trans_eq h14⟩
  refine fj_inverse_chart (mu := virasoroMu) (lam := virasoroLam) (ψ := virasoroPsiChart)
    (c1 := virasoroC1) (ρ0 := chartParams.ρ_ψ) (r0 := chartParams.r_ψ) (M := chartParams.M_ψ)
    (c_ψ := 2) (Cμ := betaTip⁻¹) (Clam := betaTip) (β := (c0Star / cStar) / betaTip)
    (γ := gamma0) (C_jet := chartParams.C_ψ) (c0_const := c0Star)
    virasoroC1_pos (lt_trans chartParams.hrψ_pos chartParams.hrψ_lt) chartParams.hrψ_pos
    chartParams.hrψ_lt chartParams.hMψ_nn (inv_pos.mpr hβ) hβ chartParams.hCψ_nn
    (fun c hc => mul_pos (inv_pos.mpr hβ) (Real.rpow_pos_of_pos hc _))
    (fun c hc => mul_pos hβ (Real.rpow_pos_of_pos hc _))
    (fun c hc => by
      dsimp [virasoroLam, virasoroMu]
      calc betaTip * c ^ (-(1 / 3 : ℝ)) * (betaTip⁻¹ * c ^ (-(2 / 3 : ℝ)))
          = (betaTip * betaTip⁻¹) * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by ring
        _ = 1 * c ^ (-1 : ℝ) := by
          rw [mul_inv_cancel₀ hβ.ne', ← Real.rpow_add hc]; congr 2; norm_num
        _ = c⁻¹ := by rw [one_mul, Real.rpow_neg_one])
    (fun c _ => le_rfl) (fun c _ => le_rfl) virasoroC1_r0_cond
    (fun c hc => (chartParams.hψ_spec _ (hc2 hc).1 (hc2 hc).2).1)
    (fun c hc => (chartParams.hψ_spec _ (hc2 hc).1 (hc2 hc).2).2.1)
    (fun c hc => (chartParams.hψ_spec _ (hc2 hc).1 (hc2 hc).2).2.2.1)
    (fun c hc => by
      have h1 := (chartParams.hψ_spec _ (hc2 hc).1 (hc2 hc).2).2.2.2.1
      have hc1 : 1 ≤ c := by linarith only [hc]
      have hpow : c ^ (-2 : ℝ) ≤ c ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      exact h1.trans (mul_le_mul_of_nonneg_left hpow chartParams.hCψ_nn))
    (fun c hc => by
      have h1 := (chartParams.hψ_spec _ (hc2 hc).1 (hc2 hc).2).2.2.2.2
      have hc1 : 1 ≤ c := by linarith only [hc]
      have hpow : c ^ (-2 : ℝ) ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      exact h1.trans (mul_le_mul_of_nonneg_left hpow chartParams.hCψ_nn))
    (fun c _ => by dsimp [virasoroLam]; field_simp [hβ.ne'])

/-- Canonical shifted Airy chart `φ_c` at Virasoro (`cts:cauchy-dual` (1)). -/
def virasoroPhi : ℝ → ℂ → ℂ := Classical.choose virasoroChart_exists

/-- **`cts:cauchy-dual` (1) and `cts:phic-exp` at Virasoro**: `virasoroPhi` and `virasoroUhat`
satisfy `LowerChart c0Star gamma0 virasoroC1` unconditionally. -/
theorem virasoroChart_holds :
    LowerChart c0Star gamma0 virasoroC1 virasoroPhi virasoroUhat :=
  Classical.choose_spec virasoroChart_exists

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoroChart_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroChart_holds

/-- **Langer coordinate on the full `O(c^{2/3})` negative chart band**:
for every `c > 0` and `-5 c₁² c^{2/3} ≤ u < 0`, `tauPhase (√(3 Δ_c(u)/c)) = -u / (β c^{2/3}) < r_ψ`. -/
theorem lowerLangerPhase_band {c u : ℝ} (hc0 : 0 < c)
    (hu1 : -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ u) (hu2 : u < 0) :
    tauPhase (√(3 * virasoroDeltaChart c u / c)) = -u / (betaTip * c ^ (2 / 3 : ℝ)) ∧
    tauPhase (√(3 * virasoroDeltaChart c u / c)) < chartParams.r_ψ ∧
    xiStar < √(3 * virasoroDeltaChart c u / c) := by
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 (2 / 3)
  have hu_band : -(chartParams.δ_band * c ^ (2 / 3 : ℝ)) ≤ u := by
    have h1 : 5 * virasoroC1 ^ 2 ≤ chartParams.δ_band :=
      virasoroC1_band_cond.trans (half_le_self chartParams.hδ_band_pos.le)
    nlinarith only [hu1, h1, hc23]
  have htau := chartParams.hband hc0 hu_band hu2
  have hτ_lt : tauPhase (√(3 * virasoroDeltaChart c u / c)) < chartParams.r_ψ := by
    rw [htau]
    have hβ := betaTip_pos
    have hneg_u : -u ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := by linarith only [hu1]
    have hdiv : -u / (betaTip * c ^ (2 / 3 : ℝ)) ≤ 5 * virasoroC1 ^ 2 * betaTip⁻¹ := by
      rw [div_le_iff₀ (mul_pos hβ hc23)]
      calc -u ≤ 5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ) := hneg_u
        _ = 5 * virasoroC1 ^ 2 * betaTip⁻¹ * (betaTip * c ^ (2 / 3 : ℝ)) := by
          field_simp [hβ.ne']
    have hr : 5 * virasoroC1 ^ 2 * betaTip⁻¹ < chartParams.r_ψ := by
      have h4 := virasoroC1_r0_cond
      have hrψ := chartParams.hrψ_pos
      linarith only [h4, hrψ]
    exact hdiv.trans_lt hr
  have hx_gt : xiStar < √(3 * virasoroDeltaChart c u / c) := by
    have hA2 : virasoroAC c ^ 2 = 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := virasoroAC_sq c hc0.le
    have h5bv : 5 * virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by
      have hbv := virasoroC1_small.trans virasoroBVChoice_le
      have hsq : (10 * virasoroC1) ^ 2 ≤ virasoroBV ^ 2 :=
        pow_le_pow_left₀ (by linarith only [virasoroC1_pos]) hbv 2
      nlinarith only [hsq, virasoroBV_pos]
    have hu_mem : u ∈ Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) :=
      ⟨by rw [hA2]; nlinarith only [hu1, h5bv, hc23], by linarith only [hu2, sq_nonneg (virasoroAC c)]⟩
    have h0_mem : (0 : ℝ) ∈ Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2) :=
      ⟨by linarith [sq_nonneg (virasoroAC c)], by positivity⟩
    have hΔ_gt : virasoroDeltaChart c 0 < virasoroDeltaChart c u :=
      (virasoroDeltaChart_strictAnti hc0) hu_mem h0_mem hu2
    rw [virasoroDeltaChart_zero] at hΔ_gt
    rw [Real.lt_sqrt xiStar_pos.le, lt_div_iff₀ hc0]
    have hxiBar : xiBar = xiStar ^ 2 / 3 := rfl
    rw [hxiBar] at hΔ_gt
    linarith only [hΔ_gt]
  exact ⟨htau, hτ_lt, hx_gt⟩

/-- **Exact phase transfer on the outer band (`cts:boas` / `cts:phic-exp`)**:
for `c ≥ 2` and `-5 c₁² c^{2/3} ≤ u < 0`, setting `x = √(3 Δ_c(u)/c)` and `y = lowerYVal x`:
`2 √(-u) (û_c(u) - u) = arg(G_out(iy)) + 2 arg(M̃_{c^{-2}}(iy))`. -/
theorem virasoroUhat_phase_match {c u : ℝ} (hc2 : 2 ≤ c)
    (hu1 : -(5 * virasoroC1 ^ 2 * c ^ (2 / 3 : ℝ)) ≤ u) (hu2 : u < 0) :
    let x := √(3 * virasoroDeltaChart c u / c)
    xiStar < x ∧ lowerYVal x ∈ Ioo (0 : ℝ) 1 ∧
    2 * √(-u) * (virasoroUhat c u - u) =
      Complex.arg (Gout (Complex.I * (lowerYVal x : ℂ))) +
        2 * Complex.arg ((1 + ((c ^ (-2 : ℝ) : ℝ) : ℂ)) * (1 + (Complex.I * (lowerYVal x : ℂ)) ^ 2) /
          (1 + (Complex.I * (lowerYVal x : ℂ)) ^ 2 + ((c ^ (-2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I * (lowerYVal x : ℂ)))) := by
  intro x
  have hc0 : 0 < c := by linarith only [hc2]
  obtain ⟨htau, hτ_lt, hx_gt⟩ := lowerLangerPhase_band hc0 hu1 hu2
  have hε0 : 0 ≤ c ^ (-2 : ℝ) := Real.rpow_nonneg hc0.le _
  have hε1 : c ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (c ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by nlinarith only [hc2])
      _ = 1 / 4 := by norm_num
  obtain ⟨_, hy, h_eq⟩ := chartParams.hψ_phase (c ^ (-2 : ℝ)) hε0 hε1 x hx_gt hτ_lt
  refine ⟨hx_gt, hy, ?_⟩
  have hβ := betaTip_pos
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 (2 / 3)
  have hneg_u : -u = betaTip * c ^ (2 / 3 : ℝ) * tauPhase x := by
    rw [htau]; field_simp [hβ.ne', hc23.ne']
  have hmu_u : virasoroMu c * u = -(tauPhase x) := by
    dsimp [virasoroMu]
    rw [htau, Real.rpow_neg hc0.le]
    field_simp [hβ.ne', hc23.ne']
  have hdiff : virasoroUhat c u - u =
      virasoroLam c * (virasoroPsiEps (c ^ (-2 : ℝ)) ((-(tauPhase x) : ℝ) : ℂ)).re := by
    dsimp [virasoroUhat, fjUhat, virasoroPsiChart]
    rw [hmu_u]; ring
  have htau_nn : 0 ≤ tauPhase x := by
    rw [htau]; exact div_nonneg (by linarith only [hu2]) (by positivity)
  have hsqrt_prod : √(-u) * virasoroLam c = betaTip ^ (3 / 2 : ℝ) * √(tauPhase x) := by
    rw [hneg_u, Real.sqrt_mul (mul_pos hβ hc23).le, Real.sqrt_mul hβ.le]
    dsimp [virasoroLam]
    have hc_prod : √(c ^ (2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]
      norm_num
    have hβ_prod : √betaTip * betaTip = betaTip ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      conv_lhs => rhs; rw [← Real.rpow_one betaTip]
      rw [← Real.rpow_add hβ]
      norm_num
    calc (√betaTip * √(c ^ (2 / 3 : ℝ)) * √(tauPhase x)) * (betaTip * c ^ (-(1 / 3 : ℝ)))
        = (√betaTip * betaTip) * (√(c ^ (2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) * √(tauPhase x) := by ring
      _ = betaTip ^ (3 / 2 : ℝ) * 1 * √(tauPhase x) := by rw [hβ_prod, hc_prod]
      _ = betaTip ^ (3 / 2 : ℝ) * √(tauPhase x) := by ring
  calc 2 * √(-u) * (virasoroUhat c u - u)
      = 2 * (√(-u) * virasoroLam c) *
          (virasoroPsiEps (c ^ (-2 : ℝ)) ((-(tauPhase x) : ℝ) : ℂ)).re := by
        rw [hdiff]; ring
    _ = 2 * betaTip ^ (3 / 2 : ℝ) * √(tauPhase x) *
          (virasoroPsiEps (c ^ (-2 : ℝ)) ((-(tauPhase x) : ℝ) : ℂ)).re := by
        rw [hsqrt_prod]; ring
    _ = _ := h_eq

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoroUhat_phase_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroUhat_phase_match

end

end FormalResearch.ModularBootstrap.FiveTerm
