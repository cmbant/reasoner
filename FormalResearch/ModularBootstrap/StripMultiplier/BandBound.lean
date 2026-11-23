module

public import FormalResearch.ModularBootstrap.StripMultiplier.EdgeKernel
public import FormalResearch.ModularBootstrap.Chart.Langer
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart
public import FormalResearch.ModularBootstrap.StripBand.BandReduction
public import FormalResearch.TwoEdgeBootstrap.Bootstrap

/-!
# Proposition `Y_V` (Band Bound) and Proposition `X_V`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2 (`Proposition X_V`, `vlo:XV`,
lines 458–463) and §J4 (`Proposition Y_V`, `vlo:YV`, lines 516–529).

Defines:
* `langerDelta pg c' u`: inverse Langer energy image `c' (Re b_L(u c'^{-2/3}))^2 / 3`
  (equal to `ConcreteBootstrap.virasoroDeltaChart c' u` for `pg = langerChartSpec_virasoro`,
  see `langerDelta_virasoro_eq`);
* `langerNegV pg c' R t`: canonical nonnegative Langer coordinate `v = -ũ(t) ∈ [0, R]` on
  `[langerDelta pg c' 0, langerDelta pg c' (-R)]`;
* `yvBandParams pg A_thr` and `yvBandInstance`: full verification of `(MS1)` (from `lemma_S4`),
  `(MS2)` (from `lemma_J4_0`, `lemma_J4_1`, `lemma_J4_2`), and the Langer band/threshold
  bounds (`lemma_S6`) constructing a `StripBand.BandReductionInstance` from any test function
  `g ∈ TestClass virasoroProblem (c'/12)` with `0 < M[g]`, `g ≥ 0` on `[T, ∞)`, and
  `-A_thr ≤ ũ_T ≤ 0`.

Proves:
* `proposition_YV_of_spec`: parametric form of Proposition `Y_V` for any `pg : LangerChartSpec`;
* `proposition_YV`: **unconditional Proposition `Y_V` (`vlo:YV`)** obtained by instantiating
  `pg = ConcreteBootstrap.langerChartSpec_virasoro` — the band bound
  `‖W̃_V(ζ₀)‖ ≤ C_Y c'^{-5/6} (c'^{1/3} (B₁ + B₂) + c'^{-1/6}) / cos ψ`
  on the sector `S = {ρ_R / 3 ≤ |ζ₀| ≤ 2 ρ_R, cos ψ ≥ c'^{-1/12}}`, together with the sector
  bound and explicit integral formulas for `B₁, B₂` and `ũ(Δ(u)) = u`, via `teb_band_reduction`;
* `proposition_XV_of_bootstrap`: **Proposition `X_V` (`vlo:XV`)** — `B₁ + B₂ ≤ C_X (1 + log L) c'^{-1/3}`
  from `TwoEdgeBootstrap.BootstrapInstance` via `teb_bootstrap_part1`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.StripMultiplier

open Crossing Integration ComplexBessel Mellin Chart ChartGeometry StripBand
open FormalResearch.TwoEdgeBootstrap

/-! ### Section 1: Langer chart energy map `Δ(u)` and its inverse -/

/-- Inverse Langer energy image `Δ(u) = c' (Re b_L(u c'^{-2/3}))^2 / 3`
(`lower_o1_two_edge.tex`, §J2–J4). -/
noncomputable def langerDelta (pg : LangerChartSpec) (c' u : ℝ) : ℝ :=
  c' * ((pg.bL ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) ^ 2 / 3

lemma langerDelta_zero (pg : LangerChartSpec) (c' : ℝ) :
    langerDelta pg c' 0 = c' * xiStar ^ 2 / 3 := by
  unfold langerDelta
  rw [zero_mul, Complex.ofReal_zero, pg.hbL_zero, Complex.ofReal_re]

lemma integral_Ioi_inv_add_one_sq :
    IntegrableOn (fun τ : ℝ => ((1 + τ) ^ 2)⁻¹) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), ((1 + τ) ^ 2)⁻¹ = 1 := by
  have hd : ∀ τ ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(1 + t)⁻¹) (((1 + τ) ^ 2)⁻¹) τ := by
    intro τ hτ
    have hpos : 1 + τ ≠ 0 := by linarith [mem_Ici.mp hτ]
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 τ := by
      simpa using (hasDerivAt_id' τ).const_add (1 : ℝ)
    exact (h1.inv hpos).neg.congr_deriv (by ring)
  have htop : Tendsto (fun t : ℝ => -(1 + t)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_id)).neg.trans (by simp)
  have hint : IntegrableOn (fun τ : ℝ => ((1 + τ) ^ 2)⁻¹) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hd (fun _ _ => by positivity) htop
  refine ⟨hint, ?_⟩
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint htop
  norm_num at hval ⊢
  exact hval

lemma langer_bL_re_strictAnti (pg : LangerChartSpec) :
    ∃ r_mono ∈ Ioo 0 pg.rL,
      StrictAntiOn (fun x : ℝ => (pg.bL (x : ℂ)).re) (Icc (-r_mono) r_mono) ∧
      ContinuousOn (fun x : ℝ => (pg.bL (x : ℂ)).re) (Icc (-r_mono) r_mono) := by
  have hd0_an : AnalyticAt ℂ (deriv pg.bL) 0 :=
    pg.hbL_an.deriv 0 (mem_ball_self pg.hrL_pos)
  have hd0_cont : ContinuousAt (fun x : ℝ => (deriv pg.bL (x : ℂ)).re) 0 := by
    have h1 : ContinuousAt (fun z : ℂ => (deriv pg.bL z).re) 0 :=
      Complex.continuous_re.continuousAt.comp hd0_an.continuousAt
    exact h1.comp_of_eq Complex.continuous_ofReal.continuousAt Complex.ofReal_zero
  have hval0 : (deriv pg.bL (0 : ℂ)).re = -(1 / betaTip) := by
    rw [pg.hbL_deriv]
    simp
  have heps : 0 < 1 / (2 * betaTip) := by have := betaTip_pos; positivity
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := Metric.continuousAt_iff.mp hd0_cont (1 / (2 * betaTip)) heps
  let r_mono : ℝ := min (pg.rL / 2) (δ / 2)
  have hr_pos : 0 < r_mono := lt_min (by linarith [pg.hrL_pos]) (by linarith)
  have hr_lt_rL : r_mono < pg.rL :=
    (min_le_left _ _).trans_lt (by linarith [pg.hrL_pos])
  have h_deriv : ∀ x ∈ Icc (-r_mono) r_mono,
      HasDerivAt (fun t : ℝ => (pg.bL (t : ℂ)).re) (deriv pg.bL (x : ℂ)).re x := by
    intro x hx
    have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) pg.rL := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt hr_lt_rL
    have hd_c : HasDerivAt pg.bL (deriv pg.bL (x : ℂ)) (x : ℂ) :=
      (pg.hbL_an (x : ℂ) hx_ball).differentiableAt.hasDerivAt
    have hd_comp : HasDerivAt (fun t : ℝ => pg.bL (t : ℂ)) (deriv pg.bL (x : ℂ)) x :=
      hd_c.comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd_comp
  have h_neg : ∀ x ∈ Icc (-r_mono) r_mono, (deriv pg.bL (x : ℂ)).re < 0 := by
    intro x hx
    have hx_δ : dist x 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      exact (abs_le.mpr hx).trans_lt ((min_le_right _ _).trans_lt (by linarith))
    have hdist := hδ_bd hx_δ
    rw [Real.dist_eq, Complex.ofReal_zero, hval0, abs_sub_lt_iff] at hdist
    have h1 : (deriv pg.bL (x : ℂ)).re < -(1 / betaTip) + 1 / (2 * betaTip) := by
      linarith [hdist.1]
    have h2 : -(1 / betaTip) + 1 / (2 * betaTip) = -(1 / (2 * betaTip)) := by ring
    linarith [heps]
  have hanti : StrictAntiOn (fun x : ℝ => (pg.bL (x : ℂ)).re) (Icc (-r_mono) r_mono) :=
    strictAntiOn_of_deriv_neg (convex_Icc (-r_mono) r_mono)
      (fun x hx => (h_deriv x hx).continuousAt.continuousWithinAt)
      fun x hx => (h_deriv x (interior_subset hx)).deriv ▸ h_neg x (interior_subset hx)
  have hcont : ContinuousOn (fun x : ℝ => (pg.bL (x : ℂ)).re) (Icc (-r_mono) r_mono) :=
    fun x hx => (h_deriv x hx).continuousAt.continuousWithinAt
  exact ⟨r_mono, ⟨hr_pos, hr_lt_rL⟩, hanti, hcont⟩

lemma langer_edgeTau0_bound (pg : LangerChartSpec) :
    ∃ c₀_max > 0, ∃ C₁ ≥ 0,
      ∀ c₀ ∈ Ioo 0 c₀_max, ∀ (c' v : ℝ), 0 < c' → 0 ≤ v → v * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
        let t := langerDelta pg c' (-v)
        0 < t ∧
        (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).im = 0 ∧
        xiStar ≤ (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re ∧
        √(3 * t / c') = (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re ∧
        0 ≤ edgeTau0 c' t ∧
        c' ^ (1 / 3 : ℝ) * edgeTau0 c' t ≤ (1 + C₁ * c₀) * (kappaV * √v) := by
  obtain ⟨_, q_V, c₀_max, hc₀_pos, C₁, hC₁_nn, _, _, _, _, _, _, _, _, hS6_2, hS6_3⟩ := lemma_S6 pg
  refine ⟨c₀_max, hc₀_pos, C₁, hC₁_nn, fun c₀ hc₀ c' v hc' hv hvc => ?_⟩
  have ha_sq : (√v) ^ 2 * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ := by rwa [Real.sq_sqrt hv]
  have h2 := hS6_2 c₀ hc₀ c' (√v) 0 hc' (Real.sqrt_nonneg v) le_rfl
    (div_nonneg Real.pi_pos.le zero_le_two) ha_sq
  have h3 := hS6_3 c₀ hc₀ c' v hc' hv hvc
  have hu_eq : ((√v ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((Real.pi - 2 * 0 : ℝ) : ℂ)) =
      -(v : ℂ) := by
    rw [Real.sq_sqrt hv]
    simp only [mul_zero, sub_zero]
    rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_pi_mul_I, mul_neg_one]
  set z : ℂ := -(v : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) with hz_def
  set ζp : ℂ := (kappaV : ℂ) * ((c' ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (-(v : ℂ)) ^ (1 / 2 : ℂ) *
    q_V z with hζp_def
  set τ₀ : ℝ := ζp.im
  have hz_eq : ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ) = z := by
    dsimp [z]; push_cast; ring
  have h2_bL : chartB ζp = pg.bL z := by
    have := h2.2.1
    rw [hu_eq] at this
    simpa [hz_def, hζp_def] using this
  have hτ₀_nn : 0 ≤ τ₀ := h3.1
  have hτ₀_ub : |c' ^ (1 / 3 : ℝ) * τ₀ - kappaV * √v| ≤ C₁ * c₀ * (kappaV * √v) := h3.2.2.1
  have hb_eq : pg.bL z = (edgeX0 τ₀ : ℂ) := by
    rw [← h2_bL]
    exact h3.2.2.2
  have hre_eq : (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re = edgeX0 τ₀ := by
    rw [hz_eq, hb_eq, Complex.ofReal_re]
  have him_eq : (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).im = 0 := by
    rw [hz_eq, hb_eq, Complex.ofReal_im]
  have hxi_le : xiStar ≤ (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re := by
    rw [hre_eq]; exact xiStar_le_edgeX0 hτ₀_nn
  have hdelta_eq : langerDelta pg c' (-v) = c' * edgeX0 τ₀ ^ 2 / 3 := by
    unfold langerDelta
    rw [show (-v) * c' ^ (-(2 / 3 : ℝ)) = -(v * c' ^ (-(2 / 3 : ℝ))) by ring, hre_eq]
  have ht_pos : 0 < langerDelta pg c' (-v) := by
    rw [hdelta_eq]
    have hx0_pos : 0 < edgeX0 τ₀ := edgeX0_pos hτ₀_nn
    positivity
  have hrt_eq : √(3 * langerDelta pg c' (-v) / c') = edgeX0 τ₀ := by
    rw [hdelta_eq, show 3 * (c' * edgeX0 τ₀ ^ 2 / 3) / c' = edgeX0 τ₀ ^ 2 by
      field_simp [hc'.ne']]
    exact Real.sqrt_sq (edgeX0_pos hτ₀_nn).le
  have htau0_eq : edgeTau0 c' (langerDelta pg c' (-v)) = τ₀ := by
    rcases eq_or_lt_of_le (xiStar_le_edgeX0 hτ₀_nn) with hxi_eq | hxi_lt
    · have h0 : edgeTau0 c' (langerDelta pg c' (-v)) = 0 := by
        unfold edgeTau0
        simp only [show √(3 * langerDelta pg c' (-v) / c') = edgeX0 τ₀ from hrt_eq,
          ← hxi_eq, le_refl, ↓reduceIte]
      have hτ0_eq0 : τ₀ = 0 := by
        apply edgeX0_strictMonoOn.injOn (by simp [hτ₀_nn]) (by simp)
        rw [edgeX0_zero, ← hxi_eq]
      rw [h0, hτ0_eq0]
    · have hxe := (edgeX0_edgeTau0 hc' (by rwa [hrt_eq])).2
      exact edgeX0_strictMonoOn.injOn (edgeTau0_nonneg c' (langerDelta pg c' (-v))) hτ₀_nn
        (by rw [hxe, hrt_eq])
  have hc13_le : c' ^ (1 / 3 : ℝ) * edgeTau0 c' (langerDelta pg c' (-v)) ≤
      (1 + C₁ * c₀) * (kappaV * √v) := by
    rw [htau0_eq]
    have h1 := (abs_le.mp hτ₀_ub).2
    linarith
  refine ⟨ht_pos, him_eq, hxi_le, by rw [hrt_eq, hre_eq], edgeTau0_nonneg _ _, hc13_le⟩

/-! ### Section 2: Packaged witnesses and `BandReductionParams` -/

structure YVWitness (pg : LangerChartSpec) where
  -- Lemma S4
  C_S4 : ℝ
  c_S4 : ℝ
  hC_S4 : 0 < C_S4
  hc_S4 : 10000 ≤ c_S4
  hS4 : ∀ {c' : ℝ}, c_S4 ≤ c' → ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
    DifferentiableOn ℂ (tildeWV c' g) stripOpen ∧
    ContinuousOn (tildeWV c' g) stripClosed ∧
    (∀ ζ ∈ stripClosed, tildeWV c' g (1 - ζ) = -tildeWV c' g ζ) ∧
    (∀ ζ ∈ stripClosed, ‖tildeWV c' g ζ‖ ≤ C_S4 * virasoroProblem.cardyNorm (c' / 12) g)
  -- Lemma J4.1
  c_J41 : ℝ
  hc_J41 : 10000 ≤ c_J41
  hJ41_edge : ∀ {c' : ℝ}, c_J41 ≤ c' → ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
    ∀ τ : ℝ, tildeWV c' g (Complex.I * (τ : ℂ)) =
      ∫ t in Ioi (0 : ℝ), edgeKernelK c' τ t * ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)
  -- Lemma J4.2
  C_A1 : ℝ
  C_A1' : ℝ
  C_A2 : ℝ
  C_sub : ℝ
  κ_sub : ℝ
  c_J42 : ℝ
  hC_A1 : 0 < C_A1
  hC_A1' : 0 < C_A1'
  hC_A2 : 0 < C_A2
  hC_sub : 0 < C_sub
  hκ_sub : 0 < κ_sub
  hc_J42 : 10000 ≤ c_J42
  hA1_bd : ∀ {c' : ℝ}, c_J42 ≤ c' → ∀ τ : ℝ, ‖edgeA1 c' τ‖ ≤ C_A1 ∧
    ∃ d : ℂ, HasDerivAt (edgeA1 c') d τ ∧ ‖d‖ ≤ C_A1' / (c' * (1 + |τ|) ^ 3)
  hA2_bd : ∀ {c' : ℝ}, c_J42 ≤ c' → ∀ {t : ℝ}, 0 < t → xiStar / 2 ≤ √(3 * t / c') →
    0 ≤ edgeA2 c' t ∧ edgeA2 c' t ≤ C_A2
  hK_sub : ∀ {c' : ℝ}, c_J42 ≤ c' → ∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
    ∀ τ : ℝ, ‖edgeKernelK c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c')
  -- Lemma J4.0
  cnu₁ : ℝ
  cnu₂ : ℝ
  hcnu₁ : 0 < cnu₁
  hcnu₂ : 0 < cnu₂
  hnu_bd : ∀ τ : ℝ, 0 ≤ τ → cnu₁ * (1 + τ) ≤ edgeNuDeriv τ ∧ edgeNuDeriv τ ≤ cnu₂ * (1 + τ)
  C_ν2 : ℝ
  hC_ν2 : 0 < C_ν2
  hnu2_bd : ∀ τ : ℝ, 0 ≤ τ → |edgeNuDeriv2 τ| ≤ C_ν2
  c_mv : ℝ
  hc_mv : 0 < c_mv
  hmv_step : ∀ τ : ℝ, 0 < τ → c_mv * min (τ ^ 2) 1 ≤ edgeMV τ - edgeMV (τ / 2)
  c_sl : ℝ
  hc_sl : 0 < c_sl
  hmv_slope : ∀ τ : ℝ, 0 < τ → c_sl * (τ / (1 + τ ^ 3)) ≤ (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ
  -- Langer
  r_mono : ℝ
  hr_mono : r_mono ∈ Ioo 0 pg.rL
  h_bL_anti : StrictAntiOn (fun x : ℝ => (pg.bL (x : ℂ)).re) (Icc (-r_mono) r_mono)
  h_bL_cont : ContinuousOn (fun x : ℝ => (pg.bL (x : ℂ)).re) (Icc (-r_mono) r_mono)
  c₀_max : ℝ
  C₁ : ℝ
  hc₀_max : 0 < c₀_max
  hC₁ : 0 ≤ C₁
  c₀ : ℝ
  hc₀_pos : 0 < c₀
  hc₀_lt_max : c₀ < c₀_max
  hc₀_lt_rmono : c₀ < r_mono
  hc₀_C1 : C₁ * c₀ ≤ 1 / 2
  hc₀_rho : 2 * kappaV * √c₀ ≤ 0.035
  hS6_tau0 : ∀ (c' v : ℝ), 0 < c' → 0 ≤ v → v * c' ^ (-(2 / 3 : ℝ)) ≤ c₀ →
    let t := langerDelta pg c' (-v)
    0 < t ∧
    (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).im = 0 ∧
    xiStar ≤ (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re ∧
    √(3 * t / c') = (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re ∧
    0 ≤ edgeTau0 c' t ∧
    c' ^ (1 / 3 : ℝ) * edgeTau0 c' t ≤ (1 + C₁ * c₀) * (kappaV * √v)

lemma yvWitness_exists (pg : LangerChartSpec) : Nonempty (YVWitness pg) := by
  obtain ⟨C_S4, c_S4, hC_S4, hc_S4, hS4⟩ := lemma_S4
  obtain ⟨_, c_J41, _, hc_J41, hJ41⟩ := lemma_J4_1
  obtain ⟨C_A1, C_A1', C_A2, C_sub, κ_sub, c_J42, hC_A1, hC_A1', hC_A2, hC_sub, hκ_sub, hc_J42,
    hJ42⟩ := lemma_J4_2
  obtain ⟨cnu₁, cnu₂, hcnu₁, hcnu₂, hnu_bd⟩ := lemma_J4_0.2.2.2.2.1
  obtain ⟨C_ν2, hC_ν2, hnu2_bd⟩ := lemma_J4_0.2.2.2.2.2.1
  obtain ⟨c_mv, hc_mv, hmv_step⟩ := lemma_J4_0.2.2.2.2.2.2.2.1
  obtain ⟨c_sl, hc_sl, hmv_slope⟩ := lemma_J4_0.2.2.2.2.2.2.2.2
  obtain ⟨r_mono, hr_mono, h_bL_anti, h_bL_cont⟩ := langer_bL_re_strictAnti pg
  obtain ⟨c₀_max, hc₀_max, C₁, hC₁, hS6⟩ := langer_edgeTau0_bound pg
  let c₀ : ℝ := min (min (c₀_max / 2) (r_mono / 2))
    (min (1 / (2 * (C₁ + 1))) ((0.035 / (2 * kappaV)) ^ 2 / 2))
  have hκ_pos : 0 < kappaV := kappaV_pos
  have hc₀_pos : 0 < c₀ := by
    have hr_pos : 0 < r_mono := hr_mono.1
    have hC1_pos : 0 < C₁ + 1 := by linarith
    dsimp [c₀]
    positivity
  have hc₀_lt_max : c₀ < c₀_max :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hc₀_lt_rmono : c₀ < r_mono :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith [hr_mono.1])
  have hc₀_C1 : C₁ * c₀ ≤ 1 / 2 := by
    have hle : c₀ ≤ 1 / (2 * (C₁ + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have hC1_ne : C₁ + 1 ≠ 0 := by linarith
    calc C₁ * c₀ ≤ C₁ * (1 / (2 * (C₁ + 1))) := mul_le_mul_of_nonneg_left hle hC₁
      _ = (1 / 2) * (C₁ / (C₁ + 1)) := by field_simp [hC1_ne]
      _ ≤ (1 / 2) * 1 := by
          gcongr
          exact (div_le_one (by linarith)).mpr (by linarith)
      _ = 1 / 2 := mul_one _
  have hc₀_rho : 2 * kappaV * √c₀ ≤ 0.035 := by
    have hle : c₀ ≤ (0.035 / (2 * kappaV)) ^ 2 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (half_le_self (sq_nonneg _))
    have hsqrt : √c₀ ≤ 0.035 / (2 * kappaV) :=
      (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq (by positivity))
    calc 2 * kappaV * √c₀ ≤ 2 * kappaV * (0.035 / (2 * kappaV)) := by gcongr
      _ = 0.035 := by field_simp [hκ_pos.ne']
  exact ⟨{
    C_S4 := C_S4
    c_S4 := c_S4
    hC_S4 := hC_S4
    hc_S4 := hc_S4
    hS4 := hS4
    c_J41 := c_J41
    hc_J41 := hc_J41
    hJ41_edge := fun {c'} hc' {g} hg => (hJ41 hc' hg).1
    C_A1 := C_A1
    C_A1' := C_A1'
    C_A2 := C_A2
    C_sub := C_sub
    κ_sub := κ_sub
    c_J42 := c_J42
    hC_A1 := hC_A1
    hC_A1' := hC_A1'
    hC_A2 := hC_A2
    hC_sub := hC_sub
    hκ_sub := hκ_sub
    hc_J42 := hc_J42
    hA1_bd := fun {c'} hc' => (hJ42 hc').1
    hA2_bd := fun {c'} hc' {t} ht hx => (hJ42 hc').2.1 ht hx
    hK_sub := fun {c'} hc' {t} ht hx τ => (hJ42 hc').2.2.1 ht hx τ
    cnu₁ := cnu₁
    cnu₂ := cnu₂
    hcnu₁ := hcnu₁
    hcnu₂ := hcnu₂
    hnu_bd := hnu_bd
    C_ν2 := C_ν2
    hC_ν2 := hC_ν2
    hnu2_bd := hnu2_bd
    c_mv := c_mv
    hc_mv := hc_mv
    hmv_step := hmv_step
    c_sl := c_sl
    hc_sl := hc_sl
    hmv_slope := hmv_slope
    r_mono := r_mono
    hr_mono := hr_mono
    h_bL_anti := h_bL_anti
    h_bL_cont := h_bL_cont
    c₀_max := c₀_max
    C₁ := C₁
    hc₀_max := hc₀_max
    hC₁ := hC₁
    c₀ := c₀
    hc₀_pos := hc₀_pos
    hc₀_lt_max := hc₀_lt_max
    hc₀_lt_rmono := hc₀_lt_rmono
    hc₀_C1 := hc₀_C1
    hc₀_rho := hc₀_rho
    hS6_tau0 := fun c' v hc' hv hvc => hS6 c₀ ⟨hc₀_pos, hc₀_lt_max⟩ c' v hc' hv hvc }⟩

noncomputable def yvWitness (pg : LangerChartSpec) : YVWitness pg :=
  Classical.choice (yvWitness_exists pg)

/-- Canonical `BandReductionParams` package for Virasoro `W̃_V` with threshold Langer bound
`A_thr` (`lower_o1_two_edge.tex`, Proposition `Y_V`). -/
noncomputable def yvBandParams (pg : LangerChartSpec) (A_thr : ℝ) : BandReductionParams :=
  let w := yvWitness pg
  { M := 0
    b := √(w.c₀ / 2)
    κ_ζ := kappaV
    A_0 := (3 / 2 : ℝ) * kappaV * √(max A_thr 1)
    C_W := w.C_S4
    C_a := max (w.C_A1 + w.C_A1') (max w.C_A2 w.C_sub)
    c_1 := 2 * w.c_mv
    c_2 := 2 * w.c_sl
    C_ν := max w.cnu₁⁻¹ (w.C_ν2 / w.cnu₁ ^ 2)
    κ_sub := w.κ_sub
    C_τ := (9 / 4 : ℝ) * kappaV ^ 2
    hM := le_rfl
    hb := Real.sqrt_pos.mpr (div_pos w.hc₀_pos zero_lt_two)
    hκ_ζ := kappaV_pos
    hA_0 := by have := kappaV_pos; positivity
    hC_W := w.hC_S4
    hC_a := lt_of_lt_of_le (add_pos w.hC_A1 w.hC_A1') (le_max_left _ _)
    hc_1 := by linarith [w.hc_mv]
    hc_2 := by linarith [w.hc_sl]
    hC_ν := lt_of_lt_of_le (inv_pos.mpr w.hcnu₁) (le_max_left _ _)
    hκ_sub := w.hκ_sub
    hC_τ := by have := kappaV_pos; positivity }

/-- Scale threshold `c' ≥ yvThresh pg A_thr` ensuring `c' ≥ c_S4, c_J41, c_J42`, `R ≤ c₀ c'^{2/3}`,
and `max A_thr 1 ≤ P.b^2 c'^{2/3}` (`lower_o1_two_edge.tex`, Proposition `Y_V`). -/
noncomputable def yvThresh (pg : LangerChartSpec) (A_thr : ℝ) : ℝ :=
  let w := yvWitness pg
  max (max w.c_S4 (max w.c_J41 w.c_J42))
    (((2 * max A_thr 1) / w.c₀) ^ (3 / 2 : ℝ))

lemma yvThresh_ge (pg : LangerChartSpec) (A_thr : ℝ) :
    10000 ≤ yvThresh pg A_thr := by
  let w := yvWitness pg
  exact le_trans w.hc_S4 (le_trans (le_max_left _ _) (le_max_left _ _))

/-! ### Section 3: Canonical nonnegative Langer inverse coordinate `v = -ũ(t)` -/

/-- Nonnegative Langer coordinate `v = -ũ(t) ∈ [0, R]` on `[Δ(0), Δ(-R)]`, constructed by
intermediate value theorem from `pg.bL` (`0` outside `[Δ(0), Δ(-R)]`). -/
noncomputable def langerNegV (pg : LangerChartSpec) (c' R t : ℝ) : ℝ := by
  classical
  exact if h : ∃ v ∈ Icc (0 : ℝ) R, langerDelta pg c' (-v) = t then Classical.choose h else 0

lemma langerDelta_props {pg : LangerChartSpec} {A_thr c' R : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1) :
    let w := yvWitness pg
    0 < R ∧
    R ≤ w.c₀ * c' ^ (2 / 3 : ℝ) ∧
    max A_thr 1 ≤ R ∧
    (∀ v ∈ Icc (0 : ℝ) R,
      -(v * c' ^ (-(2 / 3 : ℝ))) ∈ Icc (-w.r_mono) w.r_mono ∧
      xiStar ≤ (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re) ∧
    StrictMonoOn (fun v => langerDelta pg c' (-v)) (Icc (0 : ℝ) R) ∧
    ContinuousOn (fun v => langerDelta pg c' (-v)) (Icc (0 : ℝ) R) := by
  let w := yvWitness pg
  have hwc0 : 0 < w.c₀ := w.hc₀_pos
  have hc'_10000 : 10000 ≤ c' := (yvThresh_ge pg A_thr).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hc_ratio : (2 * max A_thr 1) / w.c₀ ≤ c' ^ (2 / 3 : ℝ) := by
    have h1 : (((2 * max A_thr 1) / w.c₀) ^ (3 / 2 : ℝ)) ≤ c' := by
      calc (((2 * max A_thr 1) / w.c₀) ^ (3 / 2 : ℝ))
          ≤ yvThresh pg A_thr := le_max_right _ _
        _ ≤ c' := hc'
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_mul (by positivity)] at h2
    norm_num at h2
    exact h2
  have hb_sq : (yvBandParams pg A_thr).b ^ 2 = w.c₀ / 2 := by
    dsimp [yvBandParams]
    exact Real.sq_sqrt (div_nonneg w.hc₀_pos.le zero_lt_two.le)
  have hA_le_lb : max A_thr 1 ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rw [hb_sq]
    have hmul := mul_le_mul_of_nonneg_left hc_ratio (div_nonneg w.hc₀_pos.le zero_lt_two.le)
    have heq : (w.c₀ / 2) * ((2 * max A_thr 1) / w.c₀) = max A_thr 1 := by
      field_simp [w.hc₀_pos.ne']
    linarith
  have hA_le_R : max A_thr 1 ≤ R := hA_le_lb.trans hR_lb
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) hA_le_R
  have h1_le_lb : 1 ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) :=
    (le_max_right A_thr 1).trans hA_le_lb
  have hR_le_c0 : R ≤ w.c₀ * c' ^ (2 / 3 : ℝ) := by
    rw [hb_sq] at hR_ub h1_le_lb
    linarith
  have hmem_rmono : ∀ v ∈ Icc (0 : ℝ) R, -(v * c' ^ (-(2 / 3 : ℝ))) ∈ Icc (-w.r_mono) w.r_mono := by
    intro v hv
    have hvc : v * c' ^ (-(2 / 3 : ℝ)) ≤ w.c₀ := by
      have h1 : v * c' ^ (-(2 / 3 : ℝ)) ≤ (w.c₀ * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hv.2.trans hR_le_c0) (Real.rpow_nonneg hc'_pos.le _)
      have hc_cancel : c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = 1 := by
        rw [← Real.rpow_add hc'_pos]; simp
      calc v * c' ^ (-(2 / 3 : ℝ)) ≤ w.c₀ * (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) := by
            linarith
        _ = w.c₀ := by rw [hc_cancel, mul_one]
    have hnn : 0 ≤ v * c' ^ (-(2 / 3 : ℝ)) := mul_nonneg hv.1 (Real.rpow_nonneg hc'_pos.le _)
    constructor <;> linarith [w.hc₀_lt_rmono, w.hr_mono.1]
  have hbL_anti_v : StrictAntiOn (fun v : ℝ => -(v * c' ^ (-(2 / 3 : ℝ)))) (Icc (0 : ℝ) R) := by
    intro v₁ _ v₂ _ h12
    have hc_neg_pos : 0 < c' ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc'_pos _
    nlinarith
  have hb_mono : StrictMonoOn
      (fun v : ℝ => (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re) (Icc (0 : ℝ) R) := by
    intro v₁ h₁ v₂ h₂ h12
    exact w.h_bL_anti (hmem_rmono v₂ h₂) (hmem_rmono v₁ h₁) (hbL_anti_v h₁ h₂ h12)
  have hxi_le_v : ∀ v ∈ Icc (0 : ℝ) R,
      xiStar ≤ (pg.bL ((-(v * c' ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ)).re := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [zero_mul, neg_zero, Complex.ofReal_zero, pg.hbL_zero, Complex.ofReal_re]
    · have h0_lt : (0 : ℝ) < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
      have hle := (hb_mono ⟨le_rfl, hR_pos.le⟩ hv h0_lt).le
      simpa [pg.hbL_zero] using hle
  have hg_mono : StrictMonoOn (fun v => langerDelta pg c' (-v)) (Icc (0 : ℝ) R) := by
    intro v₁ h₁ v₂ h₂ h12
    unfold langerDelta
    have hb1 := hb_mono h₁ h₂ h12
    have hx1 : 0 < (pg.bL (((-v₁ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re := by
      rw [show (-v₁ * c' ^ (-(2 / 3 : ℝ))) = -(v₁ * c' ^ (-(2 / 3 : ℝ))) by ring]
      exact lt_of_lt_of_le xiStar_pos (hxi_le_v v₁ h₁)
    have hx2 : 0 < (pg.bL (((-v₂ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re := by
      rw [show (-v₂ * c' ^ (-(2 / 3 : ℝ))) = -(v₂ * c' ^ (-(2 / 3 : ℝ))) by ring]
      exact lt_of_lt_of_le xiStar_pos (hxi_le_v v₂ h₂)
    have hsq : ((pg.bL (((-v₁ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re) ^ 2 <
        ((pg.bL (((-v₂ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re) ^ 2 := by
      nlinarith [show (pg.bL (((-v₁ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re <
          (pg.bL (((-v₂ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re by
        simpa [neg_mul] using hb1]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsq hc'_pos) (by norm_num)
  have hg_cont : ContinuousOn (fun v => langerDelta pg c' (-v)) (Icc (0 : ℝ) R) := by
    unfold langerDelta
    have hmap : Continuous (fun v : ℝ => -v * c' ^ (-(2 / 3 : ℝ))) :=
      (continuous_neg).mul continuous_const
    have hb_comp : ContinuousOn (fun v : ℝ =>
        (pg.bL (((-v * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))).re) (Icc (0 : ℝ) R) :=
      w.h_bL_cont.comp hmap.continuousOn fun v hv => by
        simpa [neg_mul] using hmem_rmono v hv
    exact (continuousOn_const.mul (hb_comp.pow 2)).div_const 3
  refine ⟨hR_pos, hR_le_c0, hA_le_R, fun v hv => ⟨hmem_rmono v hv, hxi_le_v v hv⟩, hg_mono, hg_cont⟩

lemma langerNegV_mem_and_eq {pg : LangerChartSpec} {A_thr c' R t : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (ht : t ∈ Icc (langerDelta pg c' 0) (langerDelta pg c' (-R))) :
    langerNegV pg c' R t ∈ Icc (0 : ℝ) R ∧
      langerDelta pg c' (-(langerNegV pg c' R t)) = t := by
  have ⟨hR_pos, _, _, _, _, hg_cont⟩ := langerDelta_props hc' hR_lb hR_ub
  have hIVT : Icc (langerDelta pg c' (-0)) (langerDelta pg c' (-R)) ⊆
      (fun v => langerDelta pg c' (-v)) '' Icc 0 R :=
    intermediate_value_Icc hR_pos.le hg_cont
  rw [neg_zero] at hIVT
  have hex : ∃ v ∈ Icc (0 : ℝ) R, langerDelta pg c' (-v) = t := by
    simpa [mem_image] using hIVT ht
  dsimp only [langerNegV]
  split_ifs
  exact Classical.choose_spec ‹_›

lemma langerNegV_inv_delta {pg : LangerChartSpec} {A_thr c' R u : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hu : u ∈ Icc (-R) 0) :
    -langerNegV pg c' R (langerDelta pg c' u) = u := by
  have ⟨_, _, _, _, hg_mono, _⟩ := langerDelta_props hc' hR_lb hR_ub
  have hneg_mem : -u ∈ Icc (0 : ℝ) R := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hex : ∃ v ∈ Icc (0 : ℝ) R, langerDelta pg c' (-v) = langerDelta pg c' u :=
    ⟨-u, hneg_mem, by rw [neg_neg]⟩
  dsimp only [langerNegV]
  split_ifs
  have hspec := Classical.choose_spec ‹_›
  have hinj := hg_mono.injOn hspec.1 hneg_mem (by rw [neg_neg]; exact hspec.2)
  linarith

lemma langerNegV_monotoneOn {pg : LangerChartSpec} {A_thr c' R : ℝ}
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1) :
    MonotoneOn (langerNegV pg c' R) (Icc (langerDelta pg c' 0) (langerDelta pg c' (-R))) := by
  have ⟨_, _, _, _, hg_mono, _⟩ := langerDelta_props hc' hR_lb hR_ub
  intro t₁ h₁ t₂ h₂ h12
  have hv1 := langerNegV_mem_and_eq hc' hR_lb hR_ub h₁
  have hv2 := langerNegV_mem_and_eq hc' hR_lb hR_ub h₂
  by_contra hlt
  push Not at hlt
  have hlt_d := hg_mono hv2.1 hv1.1 hlt
  dsimp only at hlt_d
  rw [hv1.2, hv2.2] at hlt_d
  linarith

/-! ### Section 4: Constructing the concrete `BandReductionInstance` -/

/-- Canonical `(MS1)–(MS2)` `BandReductionInstance` for `W̃_V(ζ) / M[g]` from any test function `g`
with `0 < M[g]`, `g ≥ 0` on `[T, ∞)`, and `T ∈ [Δ(0), Δ(-A_thr)]` (`-A_thr ≤ ũ_T ≤ 0`). -/
noncomputable def yvBandInstance (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr)
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    BandReductionInstance (yvBandParams pg A_thr) :=
  let P := yvBandParams pg A_thr
  let w := yvWitness pg
  let M := virasoroProblem.cardyNorm (c' / 12) g
  let fPos : ℝ → ℝ := fun t => max (g t) 0 * virasoroProblem.cardyV (c' / 12) t / M
  let fNeg : ℝ → ℝ := fun t => max (-g t) 0 * virasoroProblem.cardyV (c' / 12) t / M
  let dmPos : Measure ℝ := (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (fPos t))
  let dmNeg : Measure ℝ := (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (fNeg t))
  let hc'_10000 : 10000 ≤ c' := (yvThresh_ge pg A_thr).trans hc'
  let hc'_24 : 24 ≤ c' := by linarith
  let hc'_pos : 0 < c' := by linarith
  let hc'_ge1 : 1 ≤ c' := by linarith
  let ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let hc'_S4 : w.c_S4 ≤ c' := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hc')
  let hc'_J41 : w.c_J41 ≤ c' :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hc'))
  let hc'_J42 : w.c_J42 ≤ c' :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hc'))
  let hS4_g := w.hS4 hc'_S4 hg
  let hProps := langerDelta_props hc' hR_lb hR_ub
  let hR_pos : 0 < R := hProps.1
  let hR_le_c0 : R ≤ w.c₀ * c' ^ (2 / 3 : ℝ) := hProps.2.1
  let hA_le_R : max A_thr 1 ≤ R := hProps.2.2.1
  let hg_mono : StrictMonoOn (fun v => langerDelta pg c' (-v)) (Icc 0 R) := hProps.2.2.2.2.1
  let hV_cont : Continuous (fun t => virasoroProblem.cardyV (c' / 12) t) :=
    continuous_cardyV virasoroProblem (c' / 12)
  let hg_cont : ContinuousOn g (Ioi 0) := hg.cont.mono Ioi_subset_Ici_self
  let hfPos_meas : AEMeasurable fPos (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn fPos (Ioi 0) := fun t ht =>
      (((hg_cont t ht).sup continuousWithinAt_const).mul hV_cont.continuousWithinAt).div_const M
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  let hfNeg_meas : AEMeasurable fNeg (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn fNeg (Ioi 0) := fun t ht =>
      (((hg_cont t ht).neg.sup continuousWithinAt_const).mul hV_cont.continuousWithinAt).div_const M
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  let hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  let hfPos_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ fPos t := fun t ht => by
    dsimp [fPos]
    exact div_nonneg (mul_nonneg (le_max_right _ _)
      (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)) hM_pos.le
  let hfNeg_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ fNeg t := fun t ht => by
    dsimp [fNeg]
    exact div_nonneg (mul_nonneg (le_max_right _ _)
      (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)) hM_pos.le
  let hf_sum : ∀ t, fPos t + fNeg t = |g t| * virasoroProblem.cardyV (c' / 12) t / M := fun t => by
    dsimp [fPos, fNeg]
    have habs : max (g t) 0 + max (-g t) 0 = |g t| := by
      rcases le_total 0 (g t) with h | h
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add, abs_of_nonpos h]
    rw [← add_div, ← add_mul, habs]
  let hint_cardy_M : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t / M) (Ioi 0) :=
    hg.int_cardy.div_const M
  let hfPos_int : IntegrableOn fPos (Ioi 0) :=
    hint_cardy_M.mono' hfPos_meas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (hfPos_nn t ht), ← hf_sum t]
        linarith [hfNeg_nn t ht])
  let hfNeg_int : IntegrableOn fNeg (Ioi 0) :=
    hint_cardy_M.mono' hfNeg_meas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (hfNeg_nn t ht), ← hf_sum t]
        linarith [hfPos_nn t ht])
  let hdmPos_univ : dmPos univ = ENNReal.ofReal (∫ t in Ioi 0, fPos t) := by
    dsimp [dmPos]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hfPos_int
      (ae_restrict_of_forall_mem measurableSet_Ioi hfPos_nn)).symm
  let hdmNeg_univ : dmNeg univ = ENNReal.ofReal (∫ t in Ioi 0, fNeg t) := by
    dsimp [dmNeg]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hfNeg_int
      (ae_restrict_of_forall_mem measurableSet_Ioi hfNeg_nn)).symm
  let hdmPos_fin : IsFiniteMeasure dmPos := ⟨by rw [hdmPos_univ]; exact ENNReal.ofReal_lt_top⟩
  let hdmNeg_fin : IsFiniteMeasure dmNeg := ⟨by rw [hdmNeg_univ]; exact ENNReal.ofReal_lt_top⟩
  let h_rhoR_ub : 2 * rhoR P c' R ≤ 0.035 := by
    unfold rhoR
    have h1 : c' ^ (-(1 / 3 : ℝ)) * √R ≤ √w.c₀ := by
      have hsq : R ≤ w.c₀ * c' ^ (2 / 3 : ℝ) := hR_le_c0
      have hrt : √R ≤ √w.c₀ * c' ^ (1 / 3 : ℝ) := by
        calc √R ≤ √(w.c₀ * c' ^ (2 / 3 : ℝ)) := Real.sqrt_le_sqrt hsq
          _ = √w.c₀ * √(c' ^ (2 / 3 : ℝ)) := Real.sqrt_mul w.hc₀_pos.le _
          _ = √w.c₀ * c' ^ (1 / 3 : ℝ) := by
              rw [Real.sqrt_eq_rpow (c' ^ (2 / 3 : ℝ)), ← Real.rpow_mul hc'_pos.le]; norm_num
      have hc_cancel : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add hc'_pos]; simp
      calc c' ^ (-(1 / 3 : ℝ)) * √R ≤ c' ^ (-(1 / 3 : ℝ)) * (√w.c₀ * c' ^ (1 / 3 : ℝ)) := by gcongr
        _ = √w.c₀ * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) := by ring
        _ = √w.c₀ := by rw [hc_cancel, mul_one]
    calc 2 * (P.κ_ζ * c' ^ (-(1 / 3 : ℝ)) * √R)
        = 2 * kappaV * (c' ^ (-(1 / 3 : ℝ)) * √R) := by dsimp [P, yvBandParams]; ring
      _ ≤ (2 * kappaV) * √w.c₀ := mul_le_mul_of_nonneg_left h1 (by have := kappaV_pos; positivity)
      _ ≤ 0.035 := w.hc₀_rho
  let hT_ge_xiBar : c' * xiStar ^ 2 / 3 ≤ T := by
    rwa [← langerDelta_zero pg c']
  let hE_sub_sub : Ioc 0 (c' * (xiStar / 2) ^ 2 / 3) ⊆ Ioo 0 T := by
    intro ξ hξ
    refine ⟨hξ.1, hξ.2.trans_lt ?_⟩
    have hxi_sq : 0 < c' * xiStar ^ 2 / 3 := by have := xiStar_pos; positivity
    calc c' * (xiStar / 2) ^ 2 / 3 = (c' * xiStar ^ 2 / 3) / 4 := by ring
      _ < c' * xiStar ^ 2 / 3 := by linarith
      _ ≤ T := hT_ge_xiBar
  let x_cut : ℝ := c' * (xiStar / 2) ^ 2 / 3
  let hx_cut_pos : 0 < x_cut := by have := xiStar_pos; positivity
  let a0p : ℝ → ℂ := fun τ => Classical.choose (w.hA1_bd hc'_J42 τ).2
  let ha0p_spec : ∀ τ, HasDerivAt (edgeA1 c') (a0p τ) τ ∧ ‖a0p τ‖ ≤ w.C_A1' / (c' * (1 + |τ|) ^ 3) :=
    fun τ => Classical.choose_spec (w.hA1_bd hc'_J42 τ).2
  let invNu' : ℝ → ℝ := fun τ => -(edgeNuDeriv2 τ) / (edgeNuDeriv τ) ^ 2
  let hinvNu'_le : ∀ τ ∈ Ioi (0 : ℝ), |invNu' τ| ≤ (w.C_ν2 / w.cnu₁ ^ 2) * ((1 + τ) ^ 2)⁻¹ := by
    intro τ hτ
    have hτ_nn : 0 ≤ τ := (mem_Ioi.mp hτ).le
    have hcnu₁_pos : 0 < w.cnu₁ := w.hcnu₁
    have hCν2_nn : 0 ≤ w.C_ν2 := w.hC_ν2.le
    have h1τ : 0 < 1 + τ := by linarith
    have hnu_lb : w.cnu₁ * (1 + τ) ≤ edgeNuDeriv τ := (w.hnu_bd τ hτ_nn).1
    have hnu_pos : 0 < edgeNuDeriv τ := lt_of_lt_of_le (mul_pos hcnu₁_pos h1τ) hnu_lb
    have h2 : |edgeNuDeriv2 τ| ≤ w.C_ν2 := w.hnu2_bd τ hτ_nn
    have hden_lb : w.cnu₁ ^ 2 * (1 + τ) ^ 2 ≤ edgeNuDeriv τ ^ 2 := by
      have : (w.cnu₁ * (1 + τ)) ^ 2 ≤ edgeNuDeriv τ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hnu_lb 2
      linarith [show (w.cnu₁ * (1 + τ)) ^ 2 = w.cnu₁ ^ 2 * (1 + τ) ^ 2 by ring]
    dsimp [invNu']
    rw [abs_div, abs_neg, abs_of_pos (sq_pos_of_pos hnu_pos)]
    calc |edgeNuDeriv2 τ| / edgeNuDeriv τ ^ 2
        ≤ w.C_ν2 / (w.cnu₁ ^ 2 * (1 + τ) ^ 2) := by gcongr
      _ = (w.C_ν2 / w.cnu₁ ^ 2) * ((1 + τ) ^ 2)⁻¹ := by
          field_simp [hcnu₁_pos.ne', h1τ.ne']
  let hinvNu'_cont : ContinuousOn invNu' (Ioi 0) := by
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
      have hx_d2_c : Continuous (fun s => (Real.pi / (2 * √2)) * Real.cosh (Real.pi * s / 2) / Real.cosh (Real.pi * s) ^ (3 / 2 : ℝ)) :=
        (continuous_const.mul hch2).div hrpow_c fun s => by positivity [Real.cosh_pos (Real.pi * s)]
      have hy_d2_c : Continuous (fun s => -(Real.pi / (2 * √2)) * Real.sinh (Real.pi * s / 2) / Real.cosh (Real.pi * s) ^ (3 / 2 : ℝ)) :=
        (continuous_const.mul hsh2).div hrpow_c fun s => by positivity [Real.cosh_pos (Real.pi * s)]
      have hx_d1_c : Continuous (fun s => (1 / √2) * Real.sinh (Real.pi * s / 2) / √(Real.cosh (Real.pi * s))) :=
        (continuous_const.mul hsh2).div hsqrt_c fun s => Real.sqrt_ne_zero'.mpr (Real.cosh_pos _)
      have hy_d1_c : Continuous (fun s => (1 / √2) * Real.cosh (Real.pi * s / 2) / √(Real.cosh (Real.pi * s))) :=
        (continuous_const.mul hch2).div hsqrt_c fun s => Real.sqrt_ne_zero'.mpr (Real.cosh_pos _)
      exact continuous_const.mul (((hx_d2_c.mul hy0_c).add ((continuous_const.mul hx_d1_c).mul hy_d1_c)).add (hx0_c.mul hy_d2_c))
    exact h2.neg.continuousOn.div (h1.pow 2).continuousOn fun τ hτ =>
      pow_ne_zero 2 (lt_of_lt_of_le (mul_pos w.hcnu₁ (by linarith [(mem_Ioi.mp hτ).le]))
        (w.hnu_bd τ (mem_Ioi.mp hτ).le).1).ne'
  { c := c'
    ε := -1
    R := R
    hc := by linarith
    hε := Or.inr rfl
    hR_lb := hR_lb
    hR_ub := hR_ub
    hρR_ub := h_rhoR_ub
    W_tilde := fun ζ => ((M⁻¹ : ℝ) : ℂ) * tildeWV c' g ζ
    hW_cont := continuousOn_const.mul hS4_g.2.1
    hW_holo := (differentiableOn_const _).mul hS4_g.1
    hW_symm := fun ζ h0 h1 => by
      rw [hS4_g.2.2.1 ζ ⟨h0, h1⟩]
      push_cast; ring
    hW_bound := fun ζ h0 h1 => by
      have hbd := hS4_g.2.2.2 ζ ⟨h0, h1⟩
      dsimp only [yvBandParams]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le), Real.rpow_zero, mul_one]
      calc M⁻¹ * ‖tildeWV c' g ζ‖ ≤ M⁻¹ * (w.C_S4 * M) :=
            mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hM_pos.le)
        _ = w.C_S4 := by rw [mul_comm w.C_S4 M, ← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
    dmPos := dmPos
    dmNeg := dmNeg
    hdmPos_fin := hdmPos_fin
    hdmNeg_fin := hdmNeg_fin
    hdmPos_supp := by
      dsimp [dmPos]
      rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
    hdmNeg_supp := by
      dsimp [dmNeg]
      rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
    hdm_tv := by
      rw [hdmPos_univ, hdmNeg_univ,
        ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi hfPos_nn),
        ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi hfNeg_nn),
        ← integral_add hfPos_int hfNeg_int]
      have heq : EqOn (fun t => fPos t + fNeg t)
          (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t / M) (Ioi 0) :=
        fun t _ => hf_sum t
      rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_div]
      change virasoroProblem.cardyNorm (c' / 12) g / M ≤ 1
      rw [div_self hM_pos.ne']
    T := T
    hdm_nonneg_tail := by
      dsimp [dmNeg]
      rw [withDensity_apply _ measurableSet_Ici]
      refine setLIntegral_eq_zero measurableSet_Ici fun t ht => ?_
      dsimp [fNeg]
      have hgt := hg_nonneg t ht
      rw [max_eq_right (neg_nonpos.mpr hgt), zero_mul, zero_div, ENNReal.ofReal_zero]
    E_sub := Ioc 0 x_cut
    hE_sub_meas := measurableSet_Ioc
    hE_sub_sub := hE_sub_sub
    K_edge := edgeKernelK c'
    hK_meas := measurable_edgeKernelK hc'_pos.le
    hW_edge := fun τ => by
      rw [mul_comm (τ : ℂ) Complex.I, w.hJ41_edge hc'_J41 hg τ]
      -- Connect `∫ K(τ, t) (g t * V t / M)` to `(∫ K ∂dmPos) - (∫ K ∂dmNeg)`
      have hint_main : IntegrableOn (fun t => edgeKernelK c' τ t *
          ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)) (Ioi 0) := by
        let ω := chartOmega (Complex.I * (τ : ℂ))
        let z : ℂ := 1 / 2 + (c' : ℂ) * ω
        have hω_re : 0 < ω.re := by
          dsimp [ω]; rw [chartOmega_left_edge τ]
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
          exact lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
        have hz_re : 0 < z.re := by
          dsimp [z]; simp only [Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
          linarith [mul_pos hc'_pos hω_re]
        have hint_mg := integrableOn_mellinTransformG ha hg hz_re
        let Cfac : ℂ := Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
          (2 * (Real.pi : ℂ)) ^ z / Complex.Gamma z
        refine (hint_mg.const_mul Cfac).congr ((ae_restrict_iff' measurableSet_Ioi).mpr
          (ae_of_all _ fun t ht => ?_))
        have ht0 : 0 < t := mem_Ioi.mp ht
        have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) t := by
          have := virasoro_cardyV_ge ha ht0.le
          have h8 : 0 < 8 * Real.pi ^ 4 * t ^ 2 := by positivity
          linarith
        have hV_ne : (virasoroProblem.cardyV (c' / 12) t : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr hV_pos.ne'
        unfold edgeKernelK
        simp only [ht0, ↓reduceIte]
        dsimp [Cfac, z, ω]
        push_cast; field_simp [hV_ne]
      have hmeas_K : AEStronglyMeasurable (edgeKernelK c' τ) (volume.restrict (Ioi 0)) :=
        (measurable_edgeKernelK hc'_pos.le).comp (measurable_const.prodMk measurable_id)
          |>.aestronglyMeasurable
      have hint_K_pos : IntegrableOn (fun t => edgeKernelK c' τ t * (fPos t : ℂ)) (Ioi 0) := by
        refine (hint_main.div_const (M : ℂ)).mono
          ((hmeas_K.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
            hfPos_meas.aestronglyMeasurable))) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
        have hV_nn := virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hfPos_nn t ht), norm_div, norm_mul,
          Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
        have hmax_le : max (g t) 0 ≤ |g t| := max_le (le_abs_self _) (abs_nonneg _)
        calc ‖edgeKernelK c' τ t‖ * fPos t
            = ‖edgeKernelK c' τ t‖ * (max (g t) 0 * virasoroProblem.cardyV (c' / 12) t) / M := by
              dsimp [fPos]; ring
          _ ≤ ‖edgeKernelK c' τ t‖ * |g t * virasoroProblem.cardyV (c' / 12) t| /
                virasoroProblem.cardyNorm (c' / 12) g := by
              dsimp [M]; rw [abs_mul, abs_of_nonneg hV_nn]
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hmax_le hV_nn) (norm_nonneg _)) hM_pos.le
      have hint_K_neg : IntegrableOn (fun t => edgeKernelK c' τ t * (fNeg t : ℂ)) (Ioi 0) := by
        refine (hint_main.div_const (M : ℂ)).mono
          ((hmeas_K.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
            hfNeg_meas.aestronglyMeasurable))) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
        have hV_nn := virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hfNeg_nn t ht), norm_div, norm_mul,
          Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
        have hmax_le : max (-g t) 0 ≤ |g t| := max_le (neg_le_abs _) (abs_nonneg _)
        calc ‖edgeKernelK c' τ t‖ * fNeg t
            = ‖edgeKernelK c' τ t‖ * (max (-g t) 0 * virasoroProblem.cardyV (c' / 12) t) / M := by
              dsimp [fNeg]; ring
          _ ≤ ‖edgeKernelK c' τ t‖ * |g t * virasoroProblem.cardyV (c' / 12) t| /
                virasoroProblem.cardyNorm (c' / 12) g := by
              dsimp [M]; rw [abs_mul, abs_of_nonneg hV_nn]
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hmax_le hV_nn) (norm_nonneg _)) hM_pos.le
      have hI_pos : ∫ ξ : ℝ, edgeKernelK c' τ ξ ∂dmPos =
          ∫ t in Ioi (0 : ℝ), edgeKernelK c' τ t * (fPos t : ℂ) := by
        dsimp [dmPos]
        rw [integral_withDensity_eq_integral_toReal_smul₀ hfPos_meas.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [ENNReal.toReal_ofReal (hfPos_nn t ht), Complex.real_smul, mul_comm]
      have hI_neg : ∫ ξ : ℝ, edgeKernelK c' τ ξ ∂dmNeg =
          ∫ t in Ioi (0 : ℝ), edgeKernelK c' τ t * (fNeg t : ℂ) := by
        dsimp [dmNeg]
        rw [integral_withDensity_eq_integral_toReal_smul₀ hfNeg_meas.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [ENNReal.toReal_ofReal (hfNeg_nn t ht), Complex.real_smul, mul_comm]
      rw [hI_pos, hI_neg, ← integral_sub hint_K_pos hint_K_neg]
      have hsub_eq : EqOn (fun t => edgeKernelK c' τ t * (fPos t : ℂ) - edgeKernelK c' τ t * (fNeg t : ℂ))
          (fun t => ((M⁻¹ : ℝ) : ℂ) * (edgeKernelK c' τ t * ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ))) (Ioi 0) := by
        intro t _
        dsimp [fPos, fNeg]
        calc edgeKernelK c' τ t * ↑(max (g t) 0 * virasoroProblem.cardyV (c' / 12) t / M) -
              edgeKernelK c' τ t * ↑(max (-g t) 0 * virasoroProblem.cardyV (c' / 12) t / M)
            = ((M⁻¹ : ℝ) : ℂ) * (edgeKernelK c' τ t *
                (((max (g t) 0 - max (-g t) 0 : ℝ) : ℂ) * ↑(virasoroProblem.cardyV (c' / 12) t))) := by
              push_cast; ring
          _ = ((M⁻¹ : ℝ) : ℂ) * (edgeKernelK c' τ t * ↑(g t * virasoroProblem.cardyV (c' / 12) t)) := by
              rw [show max (g t) 0 - max (-g t) 0 = g t by
                rcases le_total 0 (g t) with h | h <;> simp [h]]
              push_cast; ring
      rw [setIntegral_congr_fun measurableSet_Ioi hsub_eq, integral_const_mul]
    hK_sub := fun ξ hξ τ => by
      have hξ0 : 0 ≤ ξ := hξ.1.le
      have hxt : √(3 * ξ / c') ≤ xiStar / 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨div_nonneg xiStar_pos.le zero_le_two, ?_⟩
        have h3 : ξ ≤ c' * (xiStar / 2) ^ 2 / 3 := hξ.2
        rw [div_le_iff₀ hc'_pos]
        linarith
      exact (w.hK_sub hc'_J42 hξ.1 hxt τ).trans (mul_le_mul_of_nonneg_right
        ((le_max_right w.C_A2 w.C_sub).trans (le_max_right _ _)) (Real.exp_pos _).le)
    a_0 := edgeA1 c'
    a_0' := a0p
    a_2 := fun ξ => (edgeA2 c' ξ : ℂ)
    R_0 := edgeRV c'
    Phi := edgePhi c'
    hK_factor := fun ξ hξ τ => edgeKernelK_factorization hc'_24 τ hξ.1
    ha_2_bd := fun ξ hξ => by
      have hξ0 : 0 ≤ ξ := hξ.1.le
      have hxt : xiStar / 2 ≤ √(3 * ξ / c') := by
        by_contra hlt; push Not at hlt
        apply hξ.2
        refine ⟨hξ.1, ?_⟩
        have hsq : (√(3 * ξ / c')) ^ 2 ≤ (xiStar / 2) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hlt.le 2
        rw [Real.sq_sqrt (by positivity), div_le_iff₀ hc'_pos] at hsq
        dsimp [x_cut]
        linarith
      have hbd := w.hA2_bd hc'_J42 hξ.1 hxt
      rw [Complex.norm_real, Real.norm_of_nonneg hbd.1]
      exact hbd.2.trans ((le_max_left w.C_A2 w.C_sub).trans (le_max_right _ _))
    ha_0_deriv := fun τ => (ha0p_spec τ).1
    ha_0_bd := fun τ => by
      dsimp [P, yvBandParams]
      rw [Real.rpow_zero, mul_one]
      have h1 := (w.hA1_bd hc'_J42 τ).1
      have h2 := (ha0p_spec τ).2
      have h1t : 1 ≤ c' * (1 + |τ|) ^ 3 := by
        have hpow : 1 ≤ (1 + |τ|) ^ 3 := by
          have : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
          nlinarith [sq_nonneg (1 + |τ|)]
        nlinarith [hc'_ge1]
      have h2' : ‖a0p τ‖ ≤ w.C_A1' := by
        calc ‖a0p τ‖ ≤ w.C_A1' / (c' * (1 + |τ|) ^ 3) := h2
          _ ≤ w.C_A1' / 1 := div_le_div_of_nonneg_left w.hC_A1'.le zero_lt_one h1t
          _ = w.C_A1' := div_one _
      exact (add_le_add h1 h2').trans (le_max_left _ _)
    hR_0_nonpos := fun ξ hξ τ => edgeRV_nonpos hξ.1 hc'_pos
    hR_0_cont := fun ξ _ => edgeRV_continuousOn c' ξ
    hR_0_even := fun _ _ τ => edgeRV_even c' τ _
    hR_0_unimodal := fun ξ hξ => ⟨edgeTau0 c' ξ, edgeRV_unimodal hc'_pos hξ.1⟩
    hPhi_odd := fun ξ hξ τ => edgePhi_odd hc'_pos hξ.1
    ν := edgeNu
    ν' := edgeNuDeriv
    invNu' := invNu'
    hν_deriv := fun τ _ => hasDerivAt_edgeNu τ
    hν'_cont := (continuous_iff_continuousAt.mpr fun τ =>
      (hasDerivAt_edgeNuDeriv τ).continuousAt).continuousOn
    hν'_inv_pos := fun τ hτ => by
      have hnu_lb : w.cnu₁ * (1 + τ) ≤ edgeNuDeriv τ := (w.hnu_bd τ hτ.le).1
      have h1τ : 1 ≤ 1 + τ := by linarith
      have hnu_ge : w.cnu₁ ≤ edgeNuDeriv τ := by
        calc w.cnu₁ = w.cnu₁ * 1 := (mul_one _).symm
          _ ≤ w.cnu₁ * (1 + τ) := mul_le_mul_of_nonneg_left h1τ w.hcnu₁.le
          _ ≤ edgeNuDeriv τ := hnu_lb
      have hnu_pos : 0 < edgeNuDeriv τ := lt_of_lt_of_le w.hcnu₁ hnu_ge
      refine ⟨inv_pos.mpr hnu_pos, ?_⟩
      dsimp [P, yvBandParams]
      exact (inv_anti₀ w.hcnu₁ hnu_ge).trans (le_max_left _ _)
    hν'_inv_deriv := fun τ hτ => by
      have hnu_pos : 0 < edgeNuDeriv τ := lt_of_lt_of_le
        (mul_pos w.hcnu₁ (by linarith : 0 < 1 + τ)) (w.hnu_bd τ hτ.le).1
      exact ((hasDerivAt_edgeNuDeriv τ).inv hnu_pos.ne').congr_deriv (by dsimp [invNu'])
    hinvNu'_cont := hinvNu'_cont
    hinvNu'_integrable := by
      obtain ⟨hint_sq, _⟩ := integral_Ioi_inv_add_one_sq
      refine (hint_sq.const_mul (w.C_ν2 / w.cnu₁ ^ 2)).mono'
        (hinvNu'_cont.aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_)
      rw [Real.norm_eq_abs]
      exact hinvNu'_le τ hτ
    hinvNu'_int := by
      obtain ⟨hint_sq, hval_sq⟩ := integral_Ioi_inv_add_one_sq
      have h_int_abs : IntegrableOn (fun τ => |invNu' τ|) (Ioi 0) :=
        ((hint_sq.const_mul (w.C_ν2 / w.cnu₁ ^ 2)).mono'
          (hinvNu'_cont.aestronglyMeasurable measurableSet_Ioi)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => by
            rw [Real.norm_eq_abs]; exact hinvNu'_le τ hτ)).abs
      calc ∫ τ in Ioi (0 : ℝ), |invNu' τ|
          ≤ ∫ τ in Ioi (0 : ℝ), (w.C_ν2 / w.cnu₁ ^ 2) * ((1 + τ) ^ 2)⁻¹ :=
            setIntegral_mono_on h_int_abs (hint_sq.const_mul _) measurableSet_Ioi hinvNu'_le
        _ = (w.C_ν2 / w.cnu₁ ^ 2) * ∫ τ in Ioi (0 : ℝ), ((1 + τ) ^ 2)⁻¹ :=
            integral_const_mul _ _
        _ = (w.C_ν2 / w.cnu₁ ^ 2) := by rw [hval_sq, mul_one]
        _ ≤ P.C_ν := le_max_right _ _
    μ := fun t => 2 * Real.log (√(3 * t / c') / xiStar)
    m := fun τ => 2 * (edgeMV τ - Real.log xiStar)
    m' := fun τ => 2 * (edgeX0Deriv τ / edgeX0 τ)
    hPhi_deriv := fun ξ hξ τ _ => by
      refine (hasDerivAt_edgePhi hc'_pos hξ.1 τ).congr_deriv ?_
      have hx_pos : 0 < √(3 * ξ / c') := Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hξ.1) hc'_pos)
      have hx0_pos : 0 < edgeX0 τ := edgeX0_pos_all τ
      rw [show √(3 * ξ / c') / edgeX0 τ = (√(3 * ξ / c') / xiStar) / (edgeX0 τ / xiStar) by
        field_simp [xiStar_pos.ne', hx0_pos.ne']]
      rw [Real.log_div (div_pos hx_pos xiStar_pos).ne' (div_pos hx0_pos xiStar_pos).ne',
        Real.log_div hx0_pos.ne' xiStar_pos.ne']
      unfold edgeMV; ring
    hm_0 := by unfold edgeMV; rw [edgeX0_zero, sub_self, mul_zero]
    hm_cont := by
      have hx0_cont : Continuous edgeX0 :=
        continuous_iff_continuousAt.mpr fun s => (hasDerivAt_edgeX0 s).continuousAt
      refine ContinuousOn.const_mul (ContinuousOn.sub ?_ continuousOn_const) 2
      exact ContinuousOn.log hx0_cont.continuousOn fun τ _ => (edgeX0_pos_all τ).ne'
    hm_strictMono := by
      intro τ₁ h₁ τ₂ h₂ h12
      unfold edgeMV
      have hlt := edgeX0_strictMonoOn h₁ h₂ h12
      have hlog := Real.log_lt_log (edgeX0_pos h₁) hlt
      linarith
    hm_deriv := fun τ hτ => by
      have hm := (hasDerivAt_edgeMV hτ.le).sub_const (Real.log xiStar)
      exact hm.const_mul 2
    hm_step := fun τ hτ => by
      have h := w.hmv_step τ hτ
      dsimp [P, yvBandParams]
      linarith
    hm_slope := fun τ hτ => by
      have h := w.hmv_slope τ hτ
      dsimp [P, yvBandParams]
      rw [show 2 * (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ =
          2 * ((edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ) by ring]
      calc 2 * w.c_sl * τ / (1 + τ ^ 3)
          = 2 * (w.c_sl * (τ / (1 + τ ^ 3))) := by ring
        _ ≤ 2 * ((edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ) := by gcongr
    τ_0 := edgeTau0 c'
    hτ_0_nn := edgeTau0_nonneg c'
    hτ_0_eq_zero := fun ξ hmu => by
      have hx_le : √(3 * ξ / c') ≤ xiStar := by
        by_cases hξ : ξ ≤ 0
        · have hdiv : 3 * ξ / c' ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc'_pos.le
          rw [Real.sqrt_eq_zero_of_nonpos hdiv]
          exact xiStar_pos.le
        · push Not at hξ
          have hx_pos : 0 < √(3 * ξ / c') :=
            Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hξ) hc'_pos)
          have hlog : Real.log (√(3 * ξ / c') / xiStar) ≤ 0 := by linarith
          have hdiv1 : √(3 * ξ / c') / xiStar ≤ 1 :=
            (Real.log_nonpos_iff (div_pos hx_pos xiStar_pos).le).mp hlog
          exact (div_le_one xiStar_pos).mp hdiv1
      unfold edgeTau0
      simp only [hx_le, ↓reduceIte]
    hτ_0_root := fun ξ hmu => by
      by_cases hξ : ξ ≤ 0
      · exfalso
        have hdiv : 3 * ξ / c' ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc'_pos.le
        rw [Real.sqrt_eq_zero_of_nonpos hdiv, zero_div, Real.log_zero, mul_zero] at hmu
        exact lt_irrefl 0 hmu
      · push Not at hξ
        have hx_pos : 0 < √(3 * ξ / c') :=
          Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hξ) hc'_pos)
        have hlog : 0 < Real.log (√(3 * ξ / c') / xiStar) := by linarith
        have h1lt : 1 < √(3 * ξ / c') / xiStar :=
          (Real.log_pos_iff (div_pos hx_pos xiStar_pos).le).mp hlog
        have hx_gt : xiStar < √(3 * ξ / c') := (one_lt_div xiStar_pos).mp h1lt
        have hxe := (edgeX0_edgeTau0 hc'_pos hx_gt).2
        unfold edgeMV
        rw [hxe, Real.log_div hx_pos.ne' xiStar_pos.ne']
    u_tilde := fun ξ => -langerNegV pg c' R ξ
    Delta := langerDelta pg c'
    hτ_0_below := fun ξ hξ => by
      by_cases hle0 : ξ ≤ langerDelta pg c' 0
      · have hsq_le : √(3 * ξ / c') ≤ xiStar := by
          rw [langerDelta_zero] at hle0
          by_cases hξ0 : ξ ≤ 0
          · rw [Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hc'_pos.le)]
            exact xiStar_pos.le
          · push Not at hξ0
            rw [Real.sqrt_le_iff]
            refine ⟨xiStar_pos.le, ?_⟩
            rw [div_le_iff₀ hc'_pos]
            linarith
        have htau0_0 : edgeTau0 c' ξ = 0 := by
          unfold edgeTau0; simp only [hsq_le, ↓reduceIte]
        rw [htau0_0]
        dsimp [P, yvBandParams]
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
          ⟨hle0.le, (hξ.1.le.trans hT_hi).trans hA_le_R_d⟩
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
        have hv_le_A : v ≤ max A_thr 1 := by
          by_contra hlt; push Not at hlt
          have hlt_d := hg_mono hAmax_mem hv_spec.1 hlt
          dsimp only at hlt_d
          rw [hv_spec.2] at hlt_d
          linarith [hξ.1.le, hT_hi, hA_le_Amax_d]
        have h1C : 1 + w.C₁ * w.c₀ ≤ 3 / 2 := by linarith [w.hc₀_C1]
        have hc_inv13 : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add hc'_pos]; simp
        have hc13_le := hS6.2.2.2.2.2
        have htau0_ub : edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := by
          have h2 : c' ^ (1 / 3 : ℝ) * edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * (kappaV * √v) :=
            hc13_le.trans (mul_le_mul_of_nonneg_right h1C (mul_nonneg kappaV_pos.le (Real.sqrt_nonneg _)))
          have h3 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hc'_pos.le (-(1 / 3 : ℝ)))
          rw [← mul_assoc, mul_comm (c' ^ (-(1 / 3 : ℝ))), hc_inv13, one_mul] at h3
          calc edgeTau0 c' ξ ≤ c' ^ (-(1 / 3 : ℝ)) * ((3 / 2 : ℝ) * (kappaV * √v)) := h3
            _ = (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := by ring
        calc edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := htau0_ub
          _ ≤ (3 / 2 : ℝ) * kappaV * √(max A_thr 1) * c' ^ (-(1 / 3 : ℝ)) := by
              have hκ := kappaV_pos; gcongr
    hτ_0_band := fun ξ hξ => by
      have hξ_mem : ξ ∈ Icc (langerDelta pg c' 0) (langerDelta pg c' (-R)) :=
        ⟨hT_lo.trans hξ.1, hξ.2⟩
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
      have htau0_ub : edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := by
        have h2 : c' ^ (1 / 3 : ℝ) * edgeTau0 c' ξ ≤ (3 / 2 : ℝ) * (kappaV * √v) :=
          hS6.2.2.2.2.2.trans (mul_le_mul_of_nonneg_right h1C (mul_nonneg kappaV_pos.le (Real.sqrt_nonneg _)))
        have h3 := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hc'_pos.le (-(1 / 3 : ℝ)))
        rw [← mul_assoc, mul_comm (c' ^ (-(1 / 3 : ℝ))), hc_inv13, one_mul] at h3
        calc edgeTau0 c' ξ ≤ c' ^ (-(1 / 3 : ℝ)) * ((3 / 2 : ℝ) * (kappaV * √v)) := h3
          _ = (3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ)) := by ring
      have hsq : edgeTau0 c' ξ ^ 2 ≤ ((3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hS6.2.2.2.2.1 htau0_ub 2
      have hsq_rw : ((3 / 2 : ℝ) * kappaV * √v * c' ^ (-(1 / 3 : ℝ))) ^ 2 =
          (9 / 4 : ℝ) * kappaV ^ 2 * c' ^ (-(2 / 3 : ℝ)) * v := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hv_spec.1.1,
          ← Real.rpow_natCast (c' ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc'_pos.le]
        norm_num; ring
      rw [hsq_rw] at hsq
      simpa [neg_neg, P, yvBandParams] using hsq
    hu_tilde_int := by
      have hmono : MonotoneOn (fun ξ => -(-langerNegV pg c' R ξ)) (Icc T (langerDelta pg c' (-R))) := by
        have hm := langerNegV_monotoneOn hc' hR_lb hR_ub
        intro ξ₁ h₁ ξ₂ h₂ h12
        simpa [neg_neg] using hm ⟨hT_lo.trans h₁.1, h₁.2⟩ ⟨hT_lo.trans h₂.1, h₂.2⟩ h12
      have hmeas : AEMeasurable (fun ξ => -(-langerNegV pg c' R ξ))
          (dmPos.restrict (Icc T (langerDelta pg c' (-R)))) :=
        aemeasurable_restrict_of_monotoneOn measurableSet_Icc hmono
      refine (integrable_const R).mono' hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc fun ξ hξ => ?_
      have hv_spec := langerNegV_mem_and_eq hc' hR_lb hR_ub ⟨hT_lo.trans hξ.1, hξ.2⟩
      rw [neg_neg, Real.norm_of_nonneg hv_spec.1.1]
      exact hv_spec.1.2 }

/-! ### Section 5: Proposition `Y_V` (`vlo:YV`) and Proposition `X_V` (`vlo:XV`) -/

/-- Exact bridge formulas for `bandB1`, `bandB2`, `W_tilde`, and `u_tilde` on `yvBandInstance`:
on `[T, ∞)`, `g ≥ 0` so `dmPos = (g * V / M) dt` and `u_tilde (langerDelta pg c' u) = u`. -/
lemma yvBandInstance_moments (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr)
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    let I := yvBandInstance pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    let M := virasoroProblem.cardyNorm (c' / 12) g
    (∀ ζ : ℂ, I.W_tilde ζ = ((M⁻¹ : ℝ) : ℂ) * tildeWV c' g ζ) ∧
    (∀ u ∈ Icc (-R) 0, I.u_tilde (langerDelta pg c' u) = u) ∧
    bandB1 I = R⁻¹ * ∫ t in Icc T (langerDelta pg c' (-R)),
      (-I.u_tilde t) * (g t * virasoroProblem.cardyV (c' / 12) t / M) ∧
    bandB2 I = ∫ t in Ici (langerDelta pg c' (-R)),
      g t * virasoroProblem.cardyV (c' / 12) t / M := by
  intro I M
  have hc'_pos : 0 < c' := lt_of_lt_of_le (by norm_num) ((yvThresh_ge pg A_thr).trans hc')
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith [(yvThresh_ge pg A_thr).trans hc']
  have hT_pos : 0 < T := by
    have h0 : 0 < langerDelta pg c' 0 := by
      rw [langerDelta_zero]; have := xiStar_pos; positivity
    exact lt_of_lt_of_le h0 hT_lo
  have hV_cont : Continuous (fun t => virasoroProblem.cardyV (c' / 12) t) :=
    continuous_cardyV virasoroProblem (c' / 12)
  have hg_cont : ContinuousOn g (Ioi 0) := hg.cont.mono Ioi_subset_Ici_self
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  let fPos : ℝ → ℝ := fun t => max (g t) 0 * virasoroProblem.cardyV (c' / 12) t / M
  have hfPos_meas : AEMeasurable fPos (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn fPos (Ioi 0) := fun t ht =>
      (((hg_cont t ht).sup continuousWithinAt_const).mul hV_cont.continuousWithinAt).div_const M
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).aemeasurable
  have hfPos_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ fPos t := fun t ht => by
    dsimp [fPos]
    exact div_nonneg (mul_nonneg (le_max_right _ _)
      (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)) hM_pos.le
  have hf_sum_le : ∀ t ∈ Ioi (0 : ℝ), fPos t ≤ |g t| * virasoroProblem.cardyV (c' / 12) t / M := fun t ht => by
    dsimp [fPos]
    have hV_nn := virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le
    have hmax_le : max (g t) 0 ≤ |g t| := max_le (le_abs_self _) (abs_nonneg _)
    gcongr
  have hfPos_int : IntegrableOn fPos (Ioi 0) :=
    (hg.int_cardy.div_const M).mono' hfPos_meas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_of_nonneg (hfPos_nn t ht)]; exact hf_sum_le t ht)
  refine ⟨fun _ => by dsimp [I, yvBandInstance], fun u hu => ?_, ?_, ?_⟩
  · simpa [I, yvBandInstance] using langerNegV_inv_delta hc' hR_lb hR_ub hu
  · dsimp only [bandB1, I, yvBandInstance]
    congr 1
    simp only [neg_neg]
    have hsub_Icc : Icc T (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) :=
      fun t ht => lt_of_lt_of_le hT_pos ht.1
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hfPos_meas.ennreal_ofReal.restrict
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun t => langerNegV pg c' R t) measurableSet_Icc]
    have h_meas_eq : (volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R))) =
        volume.restrict (Icc T (langerDelta pg c' (-R))) := by
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub_Icc]
    change ∫ t, (ENNReal.ofReal (fPos t)).toReal • langerNegV pg c' R t
        ∂((volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R)))) = _
    rw [h_meas_eq]
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [ENNReal.toReal_ofReal (hfPos_nn t (mem_Ioi.mpr (lt_of_lt_of_le hT_pos ht.1))),
      smul_eq_mul, mul_comm]
    dsimp [fPos]
    rw [max_eq_left (hg_nonneg t ht.1)]
  · have hB2_eq : bandB2 I = (((volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (fPos s))) (Ici (langerDelta pg c' (-R)))).toReal := by
      dsimp only [bandB2, I, yvBandInstance]
    rw [hB2_eq, withDensity_apply _ (measurableSet_Ici : MeasurableSet (Ici (langerDelta pg c' (-R))))]
    have hsub : Ici (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) := by
      have hProps := langerDelta_props hc' hR_lb hR_ub
      have h0_lt : 0 < langerDelta pg c' 0 := by
        rw [langerDelta_zero]; have := xiStar_pos; positivity
      have h_mono := hProps.2.2.2.2.1.monotoneOn ⟨le_rfl, hProps.1.le⟩ ⟨hProps.1.le, le_rfl⟩ hProps.1.le
      rw [neg_zero] at h_mono
      exact fun t ht => lt_of_lt_of_le (lt_of_lt_of_le h0_lt h_mono) ht
    have hfPos_int_tail : IntegrableOn fPos (Ici (langerDelta pg c' (-R))) :=
      hfPos_int.mono_set hsub
    have hl_eq : ∫⁻ a in Ici (langerDelta pg c' (-R)), ENNReal.ofReal (fPos a) ∂(volume.restrict (Ioi 0)) =
        ∫⁻ a in Ici (langerDelta pg c' (-R)), ENNReal.ofReal (fPos a) := by
      rw [Measure.restrict_restrict measurableSet_Ici, inter_eq_left.mpr hsub]
    rw [hl_eq, ← ofReal_integral_eq_lintegral_ofReal hfPos_int_tail
        (ae_restrict_of_forall_mem measurableSet_Ici fun t ht => hfPos_nn t (hsub ht)),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ici fun t ht => hfPos_nn t (hsub ht))]
    refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
    dsimp [fPos]
    have ht_T : T ≤ t := by
      have hProps := langerDelta_props hc' hR_lb hR_ub
      have hA_le : langerDelta pg c' (-A_thr) ≤ langerDelta pg c' (-R) :=
        hProps.2.2.2.2.1.monotoneOn ⟨hA_thr, (le_max_left A_thr 1).trans hProps.2.2.1⟩
          ⟨hProps.1.le, le_rfl⟩ ((le_max_left A_thr 1).trans hProps.2.2.1)
      linarith [mem_Ici.mp ht]
    rw [max_eq_left (hg_nonneg t ht_T)]

/-- **Proposition `Y_V` (instance form)** (`lower_o1_two_edge.tex`, §J4, `vlo:YV`, lines 516–529):
explicit `BandReductionInstance` band bound on `S` for `c' ≥ yvThresh pg A_thr` and `R ∈ [P.b^2 c'^{2/3}, P.b^2 c'^{2/3} + 1]`. -/
theorem proposition_YV_inst (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr)
    (hc' : yvThresh pg A_thr ≤ c')
    (hR_lb : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t)
    {ζ₀ : ℂ} {ψ : ℝ}
    (hlo : rhoR (yvBandParams pg A_thr) c' R / 3 ≤ ‖ζ₀‖)
    (hhi : ‖ζ₀‖ ≤ 2 * rhoR (yvBandParams pg A_thr) c' R)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ)
    (hcos_lb : c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ) :
    let P := yvBandParams pg A_thr
    let I := yvBandInstance pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    ‖tildeWV c' g ζ₀‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      (tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
    ‖tildeWV c' g ζ₀‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      (tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
  intro P I
  have hlo' : rhoR P I.c I.R / 3 ≤ ‖ζ₀‖ := by dsimp [I, yvBandInstance]; exact hlo
  have hhi' : ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R := by dsimp [I, yvBandInstance]; exact hhi
  have hcos_lb' : I.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ := by dsimp [I, yvBandInstance]; exact hcos_lb
  have hred := teb_band_reduction I hlo' hhi' hcos_eq hcos_lb'
  have hW_eq : ‖I.W_tilde ζ₀‖ = (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWV c' g ζ₀‖ := by
    have hI_W : I.W_tilde ζ₀ = ((virasoroProblem.cardyNorm (c' / 12) g : ℝ)⁻¹ : ℂ) * tildeWV c' g ζ₀ := by
      dsimp only [I, yvBandInstance]; simp only [Complex.ofReal_inv]
    rw [hI_W, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
  rw [hW_eq] at hred
  have hIc : I.c = c' := by dsimp only [I, yvBandInstance]
  have hred' : (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWV c' g ζ₀‖ ≤
      tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ ∧
      (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWV c' g ζ₀‖ ≤
      tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ))) := by
    simpa only [hIc] using hred
  have hmul1 : ‖tildeWV c' g ζ₀‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      (tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) := by
    have h1 := mul_le_mul_of_nonneg_left hred'.1 hM_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at h1
  have hmul2 : ‖tildeWV c' g ζ₀‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      (tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
    have h2 := mul_le_mul_of_nonneg_left hred'.2 hM_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at h2
  exact ⟨hmul1, hmul2⟩

/-- **Proposition `Y_V` (parametric `LangerChartSpec` form)** (`lower_o1_two_edge.tex`, §J4,
`vlo:YV`, lines 516–529). -/
theorem proposition_YV_of_spec (pg : LangerChartSpec) {A_thr : ℝ} (hA_thr : 0 ≤ A_thr) :
    ∃ (c₀ C_Y b : ℝ), 10000 ≤ c₀ ∧ 0 < C_Y ∧ 0 < b ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R → R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 →
        langerDelta pg c' 0 ≤ T → T ≤ langerDelta pg c' (-A_thr) →
        ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          (∀ t ∈ Ici T, 0 ≤ g t) →
          ∃ u_tilde : ℝ → ℝ,
            (∀ u ∈ Icc (-R) 0, u_tilde (langerDelta pg c' u) = u) ∧
            let M := virasoroProblem.cardyNorm (c' / 12) g
            let B₁ := R⁻¹ * ∫ t in Icc T (langerDelta pg c' (-R)),
              (-u_tilde t) * (g t * virasoroProblem.cardyV (c' / 12) t / M)
            let B₂ := ∫ t in Ici (langerDelta pg c' (-R)),
              g t * virasoroProblem.cardyV (c' / 12) t / M
            0 ≤ B₁ ∧ 0 ≤ B₂ ∧
            ∀ {ζ₀ : ℂ} {ψ : ℝ},
              kappaV * c' ^ (-(1 / 3 : ℝ)) * √R / 3 ≤ ‖ζ₀‖ →
              ‖ζ₀‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √R) →
              ζ₀.re = ‖ζ₀‖ * Real.cos ψ →
              c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
              ‖tildeWV c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
              ‖tildeWV c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
  let P := yvBandParams pg A_thr
  refine ⟨yvThresh pg A_thr, tebBandConst P, P.b,
    yvThresh_ge pg A_thr, tebBandConst_pos P, P.hb,
    fun {c' R T} hc' hR_lb hR_ub hT_lo hT_hi {g} hg hM_pos hg_nonneg => ?_⟩
  let I := yvBandInstance pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
  have hmom := yvBandInstance_moments pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
  refine ⟨I.u_tilde, hmom.2.1, ?_⟩
  dsimp only
  rw [← hmom.2.2.1, ← hmom.2.2.2]
  refine ⟨bandB1_nonneg I, bandB2_nonneg I, fun {ζ₀} {ψ} hlo hhi hcos_eq hcos_lb => ?_⟩
  have hρ_eq : rhoR P c' R = kappaV * c' ^ (-(1 / 3 : ℝ)) * √R := rfl
  exact proposition_YV_inst pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    (hρ_eq.symm ▸ hlo) (hρ_eq.symm ▸ hhi) hcos_eq hcos_lb

/-- On `|u| ≤ virasoroAC c'^2`, `langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' u`
coincides with `ConcreteBootstrap.virasoroDeltaChart c' u`. -/
lemma langerDelta_virasoro_eq {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ ConcreteBootstrap.virasoroAC c' ^ 2) :
    langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' u =
      ConcreteBootstrap.virasoroDeltaChart c' u := by
  have hb := ConcreteBootstrap.virasoroBChart_ofReal hc' hu
  have hbL_eq : ConcreteBootstrap.langerChartSpec_virasoro.bL
      ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = ConcreteBootstrap.virasoroBChart c' (u : ℂ) := by
    rw [← ConcreteBootstrap.langerChartSpec_virasoro_bL_eq c' (u : ℂ)]
    congr 1
    push_cast; rfl
  unfold langerDelta
  rw [hbL_eq]
  have hre_sq : ((ConcreteBootstrap.virasoroBChart c' (u : ℂ)).re : ℂ) =
      ConcreteBootstrap.virasoroBChart c' (u : ℂ) :=
    Complex.ext rfl hb.1.symm
  have hc_eq : ((c' * ((ConcreteBootstrap.virasoroBChart c' (u : ℂ)).re) ^ 2 / 3 : ℝ) : ℂ) =
      (ConcreteBootstrap.virasoroDeltaChart c' u : ℂ) := by
    push_cast
    rw [hre_sq]
    exact hb.2.2.2
  exact Complex.ofReal_inj.mp hc_eq

/-- **Proposition `Y_V` (band bound, unconditional)** (`lower_o1_two_edge.tex`, §J4, `vlo:YV`,
lines 516–529): instantiated with `ConcreteBootstrap.langerChartSpec_virasoro`, given
`A_thr ≥ 0`, there exist `c₀ ≥ 10000`, `C_Y > 0`, and `b > 0` such that for any `c' ≥ c₀`,
`R ∈ [b^2 c'^{2/3}, b^2 c'^{2/3} + 1]`, `g ∈ TestClass virasoroProblem (c'/12)` with `M[g] > 0`,
`g ≥ 0` on `[T, ∞)`, and `T ∈ [Δ(0), Δ(-A_thr)]`, on `S` one has the band bound. -/
theorem proposition_YV {A_thr : ℝ} (hA_thr : 0 ≤ A_thr) :
    ∃ (c₀ C_Y b : ℝ), 10000 ≤ c₀ ∧ 0 < C_Y ∧ 0 < b ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R → R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 →
        langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' 0 ≤ T →
        T ≤ langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-A_thr) →
        ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          (∀ t ∈ Ici T, 0 ≤ g t) →
          ∃ u_tilde : ℝ → ℝ,
            (∀ u ∈ Icc (-R) 0,
              u_tilde (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' u) = u) ∧
            let M := virasoroProblem.cardyNorm (c' / 12) g
            let B₁ := R⁻¹ * ∫ t in Icc T
                (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-R)),
              (-u_tilde t) * (g t * virasoroProblem.cardyV (c' / 12) t / M)
            let B₂ := ∫ t in Ici
                (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-R)),
              g t * virasoroProblem.cardyV (c' / 12) t / M
            0 ≤ B₁ ∧ 0 ≤ B₂ ∧
            ∀ {ζ₀ : ℂ} {ψ : ℝ},
              kappaV * c' ^ (-(1 / 3 : ℝ)) * √R / 3 ≤ ‖ζ₀‖ →
              ‖ζ₀‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √R) →
              ζ₀.re = ‖ζ₀‖ * Real.cos ψ →
              c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
              ‖tildeWV c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
              ‖tildeWV c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) :=
  proposition_YV_of_spec ConcreteBootstrap.langerChartSpec_virasoro hA_thr

/-- **Proposition `X_V`** (`lower_o1_two_edge.tex`, §J2, `vlo:XV`, lines 458–463):
any `TwoEdgeBootstrap.BootstrapInstance P` (obtained from `(B1)–(B2)` of `TE.2`) satisfies
`B₁ + B₂ ≤ C_X (1 + log L) c'^{-1/3}` for `c ≥ tebC2 P`. -/
theorem proposition_XV_of_bootstrap (P : BootstrapParams) (I : BootstrapInstance P)
    (hc : tebC2 P ≤ I.c) :
    I.B_1 + I.B_2 ≤ tebCX P * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) :=
  teb_bootstrap_part1 P I hc

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.proposition_YV_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_YV_of_spec

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.proposition_YV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_YV

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.proposition_XV_of_bootstrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_XV_of_bootstrap

end FormalResearch.ModularBootstrap.StripMultiplier