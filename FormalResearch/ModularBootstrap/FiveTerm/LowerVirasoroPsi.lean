module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerFoldChart
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3Taylor
public import FormalResearch.ModularBootstrap.FiveTerm.UpperTipMatch
public import FormalResearch.ModularBootstrap.FiveTerm.LowerLangerBridge
public import FormalResearch.ModularBootstrap.FiveTerm.OuterBridge

/-!
# Virasoro Fold Phase Shift `ψ_ε` (`cts:cauchy-dual` (1), `cts:phic-exp`)

Constructs the analytic real-symmetric fold-chart shift family `virasoroPsiEps ε a`
(`ε ∈ [0, 1/4]`) on a fixed complex disc `ball 0 r_psi`:

  `virasoroPsiEps ε (-τ) = √(Y₀(τ)) / (2 β^{3/2}) * (T_out(τ Y₀(τ)) + T_M(ε, τ Y₀(τ)))`

where:
1. `rC τ` (`virasoro_tauInv_exists`) inverts `r ↦ r * (pg.A r)^(2/3)` near `0`, matching `tauPhase (ξ_* + r) = τ`
   for small `τ > 0` via `tip_potential_cumulN_eq`.
2. `Y0 τ := dslope coshY 0 τ` (`virasoro_Y0_exists`) satisfies `τ * Y0 τ = (cosh(π(ξ_* + rC τ)) - √2)/(cosh(...) + √2)`,
   `Y0 0 = slitY`, `deriv Y0 0 = slitY * slitB` (via `slit_sq_tau`), and `τ * (Y0 τ).re = y(ξ_* + r)^2`.
3. `T_out` (`virasoro_Tout_exists`) factors `(L(iz) - L(-iz))/(2i)` from `VirasoroG3Taylor.g3Out_taylor`
   via `odd_holomorphic_factor`: `T_out 0 = g1Vir`, `deriv T_out 0 = -g3Vir`, and `y * (T_out (y^2)).re = θ_out(y)`.
4. `T_M ε` (`virasoro_TM_exists`) factors `-2 arctan(ε z / (1 - z^2 + ε)) = i log((1+iu)/(1-iu))` via
   `odd_holomorphic_factor` with uniform `‖T_M ε‖, ‖deriv (T_M ε)‖ ≤ C_M ε` and
   `y * (T_M ε (y^2)).re = 2 arg(M̃_ε(iy))`.
5. Combining them (`virasoroPsiEps_spec`) gives:
   - uniform holomorphy, real-symmetry, and `C^1` bounds on `closedBall 0 r_ψ` (`0 < r_ψ < ρ_ψ`),
   - `(virasoroPsiEps 0 0).re = (c0Star / cStar) / betaTip` and `(deriv (virasoroPsiEps 0) 0).re = gamma0`,
   - `O(ε)` jet stability for `ε ∈ [0, 1/4]`,
   - exact phase matching on `(0, r_ψ]`:
     `2 β^{3/2} √τ (virasoroPsiEps ε (-τ)).re = arg(Gout(iy)) + 2 arg((1+ε)(1-y^2)/(1-y^2+ε(1+iy)))`.
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.SignUncertainty

noncomputable section

noncomputable def lowerYVal (x : ℝ) : ℝ :=
  √((Real.cosh (π * x) - √2) / (Real.cosh (π * x) + √2))

private lemma hasDerivAt_conj_conj_psi {g : ℂ → ℂ} {z d : ℂ}
    (hg : HasDerivAt g d (starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (g (starRingEnd ℂ w))) (starRingEnd ℂ d) z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hg ⊢
  have hcont : Continuous fun t : ℂ => starRingEnd ℂ t := Complex.continuous_conj
  have htend : Tendsto (fun t : ℂ => starRingEnd ℂ t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, map_eq_zero] using ht
  have hlim := (hcont.tendsto d).comp (hg.comp htend)
  refine hlim.congr' (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [map_mul, map_inv₀, Complex.conj_conj, map_sub, map_add]

private lemma conj_symm_of_real_ball {g : ℂ → ℂ} {r : ℝ} (_hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r))
    (hreal : ∃ δ > 0, δ ≤ r ∧ ∀ x : ℝ, 0 < x → x < δ → (g (x : ℂ)).im = 0) :
    ∀ w ∈ ball (0 : ℂ) r, g (starRingEnd ℂ w) = starRingEnd ℂ (g w) := by
  obtain ⟨δ, hδ_pos, hδ_le, him⟩ := hreal
  let g_c : ℂ → ℂ := fun w => starRingEnd ℂ (g (starRingEnd ℂ w))
  have hgc_diff : DifferentiableOn ℂ g_c (ball 0 r) := fun w hw => by
    have hw' : starRingEnd ℂ w ∈ ball (0 : ℂ) r := by
      simpa only [mem_ball_zero_iff, Complex.norm_conj] using hw
    exact (hasDerivAt_conj_conj_psi ((hg.differentiableAt (isOpen_ball.mem_nhds hw')).hasDerivAt)).differentiableAt.differentiableWithinAt
  have han_g : AnalyticOnNhd ℂ g (ball 0 r) := hg.analyticOnNhd isOpen_ball
  have han_gc : AnalyticOnNhd ℂ g_c (ball 0 r) := hgc_diff.analyticOnNhd isOpen_ball
  set w0 : ℝ := δ / 2
  have hw0_pos : 0 < w0 := half_pos hδ_pos
  have hw0_mem : (w0 : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0_pos]
    dsimp [w0]; linarith only [hδ_pos, hδ_le]
  have h_eqon : EqOn g g_c (ball 0 r) := by
    refine han_g.eqOn_of_preconnected_of_frequently_eq han_gc (convex_ball _ _).isPreconnected hw0_mem ?_
    rw [frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hV_open, hw0V, hVU⟩ := hU
    obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hV_open (w0 : ℂ) hw0V
    set x : ℝ := w0 + min (ε / 2) (δ / 4)
    have hxw : x ≠ w0 := by
      have : 0 < min (ε / 2) (δ / 4) := lt_min (half_pos hε_pos) (by positivity)
      linarith only [this]
    have hx_pos : 0 < x := by
      have : 0 ≤ min (ε / 2) (δ / 4) := le_min (half_pos hε_pos).le (by positivity)
      linarith only [hw0_pos, this]
    have hx_lt : x < δ := by
      have h1 : min (ε / 2) (δ / 4) ≤ δ / 4 := min_le_right _ _
      dsimp [x, w0]; linarith only [hδ_pos, h1]
    have hx_eq : g (x : ℂ) = g_c (x : ℂ) := by
      dsimp [g_c]
      apply Complex.ext <;> simp [him x hx_pos hx_lt]
    refine ⟨(x : ℂ), hVU ⟨hball ?_, Complex.ofReal_injective.ne hxw⟩, hx_eq⟩
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    dsimp [x]
    rw [add_sub_cancel_left, abs_of_nonneg (le_min (half_pos hε_pos).le (by positivity))]
    exact (min_le_left _ _).trans_lt (half_lt_self hε_pos)
  intro w hw
  have hwc : starRingEnd ℂ w ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball_zero_iff, Complex.norm_conj] using hw
  have h := h_eqon hwc
  dsimp [g_c] at h
  simpa only [Complex.conj_conj] using h

/-! ### 1. Constant-identity bridge (`slitY` vs `betaTip` and `c0Star`, `gamma0`) -/

private lemma sqrt_slitY_div_two_betaTip :
    √slitY / (2 * betaTip ^ (3 / 2 : ℝ)) = 3 / (8 * √2) := by
  have hpi := Real.pi_pos
  have h2pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h2sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hY_pos : 0 < slitY := by unfold slitY; positivity
  have hsY_pos : 0 < √slitY := Real.sqrt_pos.mpr hY_pos
  have hsY_sq : √slitY ^ 2 = π / (2 * √2) := by
    rw [Real.sq_sqrt hY_pos.le]; rfl
  have hk_eq : KTip = 2 * π * kTip := rfl
  have hbt : betaTip ^ (3 / 2 : ℝ) = (3 / 4 : ℝ) * KTip := by linarith only [four_thirds_betaTip_rpow]
  have hbt' : betaTip ^ (3 / 2 : ℝ) = 8 / (3 * √2) * √slitY := by
    rw [hbt, hk_eq, kTip_eq_slit]
    have hc3 : √slitY ^ 3 = (π / (2 * √2)) * √slitY := by
      rw [pow_succ, hsY_sq]
    rw [hc3]
    field_simp [hpi.ne', h2pos.ne']
    norm_num
  rw [hbt']
  field_simp [hsY_pos.ne', h2pos.ne']
  nlinarith only [h2sq]

private lemma psi0_const_eq_c0_div_cStar_betaTip :
    √slitY / (2 * betaTip ^ (3 / 2 : ℝ)) * g1Vir = (c0Star / cStar) / betaTip := by
  rw [sqrt_slitY_div_two_betaTip, c0Star_eq_alphaTip_mul_g1Vir]
  unfold alphaTip cStar
  have hxi : xiStar ≠ 0 := xiStar_pos.ne'
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  have h2 : √2 ≠ 0 := by positivity
  field_simp
  ring

private lemma psi0_deriv_eq_gamma0 :
    √slitY / (2 * betaTip ^ (3 / 2 : ℝ)) * (slitY * g3Vir - slitB / 2 * g1Vir) = gamma0 := by
  rw [sqrt_slitY_div_two_betaTip, gamma0_eq_gamma0Of]
  unfold gamma0Of slitY slitB
  have h2sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2ne : √2 ≠ 0 := by positivity
  field_simp
  rw [h2sq]
  ring

/-! ### 2. Complex local inverse `rC` of `r ↦ r * (pg.A r)^(2/3)` -/

private lemma virasoro_tauInv_exists :
    ∃ rτ : ℝ, 0 < rτ ∧ ∃ sτ : ℝ, 0 < sτ ∧ sτ ≤ 1 / (10 * π) ∧
      ∃ rC : ℂ → ℂ,
        DifferentiableOn ℂ rC (ball 0 rτ) ∧
        (∀ τ ∈ ball (0 : ℂ) rτ, rC (starRingEnd ℂ τ) = starRingEnd ℂ (rC τ)) ∧
        rC 0 = 0 ∧
        deriv rC 0 = 1 ∧
        (∀ τ : ℝ, 0 < τ → τ < rτ →
          0 < (rC (τ : ℂ)).re ∧ (rC (τ : ℂ)).re < sτ ∧
          (rC (τ : ℂ)).im = 0 ∧
          tauPhase (xiStar + (rC (τ : ℂ)).re) = τ) := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  have hrA : 0 < pg.r_A := pg.hr_A_pos
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  let R0 : ℝ := min (pg.r_A / 2) (min (1 / (10 * π)) (xiStar / 2))
  have hR0_pos : 0 < R0 := by positivity
  have hA_cont : ContinuousAt pg.A 0 := (pg.hA_an 0 (mem_ball_self hrA)).continuousAt
  have hev_A : ∀ᶠ r : ℂ in 𝓝 0, ‖pg.A r - 1‖ < 1 / 2 := by
    have : Tendsto pg.A (𝓝 0) (𝓝 1) := by simpa [pg.hA_0] using hA_cont.tendsto
    have hball : ∀ᶠ r : ℂ in 𝓝 0, pg.A r ∈ ball (1 : ℂ) (1 / 2) :=
      this.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num))
    exact hball.mono fun _ hr => by simpa [Metric.mem_ball, dist_eq_norm] using hr
  obtain ⟨rA1, hrA1_pos, hrA1_ball⟩ := Metric.mem_nhds_iff.mp hev_A
  set r1 : ℝ := min R0 (rA1 / 2)
  have hr1_pos : 0 < r1 := lt_min hR0_pos (half_pos hrA1_pos)
  have hr1_rA : r1 < pg.r_A := by
    have : r1 ≤ pg.r_A / 2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith only [this, hrA]
  have hr1_slit : ∀ r ∈ ball (0 : ℂ) r1, pg.A r ∈ Complex.slitPlane := by
    intro r hr
    have hr' : r ∈ ball (0 : ℂ) rA1 := by
      rw [mem_ball_zero_iff] at hr ⊢
      exact hr.trans_le ((min_le_right _ _).trans (half_le_self hrA1_pos.le))
    have hnorm : ‖pg.A r - 1‖ < 1 / 2 := hrA1_ball hr'
    have hre : 1 / 2 < (pg.A r).re := by
      have habs : |(pg.A r - 1).re| ≤ ‖pg.A r - 1‖ := Complex.abs_re_le_norm _
      have hsub : (pg.A r - 1).re = (pg.A r).re - 1 := by simp
      rw [hsub] at habs
      linarith only [(abs_lt.mp (habs.trans_lt hnorm)).1]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith only [hre]))
  let ψF : ℂ → ℂ := fun r => r * ((pg.A r) ^ ((2 / 3 : ℝ) : ℂ) - 1)
  have hψF_diff : DifferentiableOn ℂ ψF (ball 0 r1) := by
    intro r hr
    have hAr := ((pg.hA_an r (ball_subset_ball hr1_rA.le hr)).differentiableAt).hasDerivAt
    have hpow := hAr.cpow_const (c := ((2 / 3 : ℝ) : ℂ)) (hr1_slit r hr)
    exact ((hasDerivAt_id r).mul (hpow.sub_const 1)).differentiableAt.differentiableWithinAt
  have hψF_0 : ψF 0 = 0 := by simp [ψF]
  have hdψF_0 : deriv ψF 0 = 0 := by
    have hAr := ((pg.hA_an 0 (mem_ball_self hrA)).differentiableAt).hasDerivAt
    have hpow := hAr.cpow_const (c := ((2 / 3 : ℝ) : ℂ)) (hr1_slit 0 (mem_ball_self hr1_pos))
    have hd : HasDerivAt ψF (1 * ((pg.A 0) ^ ((2 / 3 : ℝ) : ℂ) - 1) +
        0 * (((2 / 3 : ℝ) : ℂ) * pg.A 0 ^ (((2 / 3 : ℝ) : ℂ) - 1) * deriv pg.A 0)) 0 :=
      (hasDerivAt_id 0).mul (hpow.sub_const 1)
    rw [pg.hA_0, Complex.one_cpow, sub_self, mul_zero, zero_mul, add_zero] at hd
    exact hd.deriv
  have hdψF_cont : ContinuousAt (deriv ψF) 0 :=
    ((hψF_diff.deriv isOpen_ball) 0 (mem_ball_self hr1_pos)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr1_pos)) |>.continuousAt
  have hev_dψF : ∀ᶠ r : ℂ in 𝓝 0, ‖deriv ψF r‖ < 1 / 4 := by
    have : Tendsto (deriv ψF) (𝓝 0) (𝓝 0) := by simpa [hdψF_0] using hdψF_cont.tendsto
    have hball : ∀ᶠ r : ℂ in 𝓝 0, deriv ψF r ∈ ball (0 : ℂ) (1 / 4) :=
      this.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num))
    exact hball.mono fun _ hr => by simpa [Metric.mem_ball, dist_eq_norm] using hr
  obtain ⟨r2, hr2_pos, hr2_ball⟩ := Metric.mem_nhds_iff.mp hev_dψF
  set s : ℝ := min (r1 / 2) (r2 / 2)
  have hs_pos : 0 < s := lt_min (half_pos hr1_pos) (half_pos hr2_pos)
  have hs_le_sτ : s ≤ 1 / (10 * π) :=
    (min_le_left _ _).trans (le_trans (half_le_self hr1_pos.le) ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs_bound_d : ∀ z ∈ closedBall (0 : ℂ) s, ‖deriv ψF z‖ ≤ 1 / 4 := fun z hz => by
    have hz' : z ∈ ball (0 : ℂ) r2 := by
      rw [mem_ball_zero_iff]
      exact (mem_closedBall_zero_iff.mp hz).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr2_pos))
    exact (show ‖deriv ψF z‖ < 1 / 4 from hr2_ball hz').le
  have hs_bound_v : ∀ z ∈ closedBall (0 : ℂ) s, ‖ψF z‖ ≤ (1 / 4) * s := fun z hz => by
    have hder : ∀ x ∈ closedBall (0 : ℂ) s, HasDerivWithinAt ψF (deriv ψF x) (closedBall (0 : ℂ) s) x := by
      intro x hx
      have hx' : x ∈ ball (0 : ℂ) r1 := by
        rw [mem_ball_zero_iff]
        exact (mem_closedBall_zero_iff.mp hx).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr1_pos))
      exact (hψF_diff.differentiableAt (isOpen_ball.mem_nhds hx')).hasDerivAt.hasDerivWithinAt
    have hmv := (convex_closedBall (0 : ℂ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
      hder hs_bound_d hz (mem_closedBall_self hs_pos.le)
    have hmv' : ‖ψF z‖ ≤ (1 / 4) * ‖z‖ := by
      simpa [hψF_0, dist_eq_norm, norm_sub_rev] using hmv
    exact hmv'.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) (by norm_num))
  -- Rescale `Ψ(a) = s⁻¹ * ψF (s * a)` on `ball 0 2` to apply `ct_inv_chart`
  let Ψ : ℂ → ℂ := fun a => (s⁻¹ : ℂ) * ψF ((s : ℂ) * a)
  have hΨ_diff : DifferentiableOn ℂ Ψ (ball 0 2) := by
    intro a ha
    have hsa : (s : ℂ) * a ∈ ball (0 : ℂ) r1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      have ha2 : ‖a‖ < 2 := mem_ball_zero_iff.mp ha
      calc s * ‖a‖ < s * 2 := mul_lt_mul_of_pos_left ha2 hs_pos
        _ ≤ (r1 / 2) * 2 := mul_le_mul_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ = r1 := by ring
    exact ((hψF_diff.differentiableAt (isOpen_ball.mem_nhds hsa)).comp a ((hasDerivAt_id a).const_mul (s : ℂ)).differentiableAt |>.const_mul (s⁻¹ : ℂ)).differentiableWithinAt
  have hΨ_bd : ∀ a ∈ closedBall (0 : ℂ) 1, ‖Ψ a‖ ≤ 1 / 4 ∧ ‖deriv Ψ a‖ ≤ 1 / 4 := by
    intro a ha
    have hsa : (s : ℂ) * a ∈ closedBall (0 : ℂ) s := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      exact mul_le_of_le_one_right hs_pos.le (mem_closedBall_zero_iff.mp ha)
    refine ⟨?_, ?_⟩
    · rw [show Ψ a = (s⁻¹ : ℂ) * ψF ((s : ℂ) * a) from rfl, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs_pos.le]
      calc s⁻¹ * ‖ψF ((s : ℂ) * a)‖ ≤ s⁻¹ * ((1 / 4) * s) := mul_le_mul_of_nonneg_left (hs_bound_v _ hsa) (by positivity)
        _ = 1 / 4 := by field_simp [hs_pos.ne']
    · have hsa_r1 : (s : ℂ) * a ∈ ball (0 : ℂ) r1 := by
        rw [mem_ball_zero_iff] at *
        exact (mem_closedBall_zero_iff.mp hsa).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr1_pos))
      have hd1 : HasDerivAt ψF (deriv ψF ((s : ℂ) * a)) ((s : ℂ) * a) :=
        (hψF_diff.differentiableAt (isOpen_ball.mem_nhds hsa_r1)).hasDerivAt
      have hd2 : HasDerivAt (fun w : ℂ => (s : ℂ) * w) (s : ℂ) a := by
        simpa using (hasDerivAt_id a).const_mul (s : ℂ)
      have hdΨ : HasDerivAt Ψ ((s⁻¹ : ℂ) * (deriv ψF ((s : ℂ) * a) * (s : ℂ))) a :=
        (hd1.comp a hd2).const_mul (s⁻¹ : ℂ)
      have hder_eq : deriv Ψ a = deriv ψF ((s : ℂ) * a) := by
        rw [hdΨ.deriv]
        have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
        field_simp [hsC]
      rw [hder_eq]
      exact hs_bound_d _ hsa
  obtain ⟨g, hg_spec, hg_uniq, hg_deriv⟩ := ct_inv_chart hΨ_diff (by norm_num : (1 : ℝ) < 2) one_pos hΨ_bd
    zero_le_one (by norm_num) (by norm_num)
  let rC : ℂ → ℂ := fun τ => (s : ℂ) * g ((s⁻¹ : ℂ) * τ)
  let rτ : ℝ := s / 2
  have hrτ_pos : 0 < rτ := half_pos hs_pos
  have hmem_half : ∀ τ ∈ ball (0 : ℂ) rτ, (s⁻¹ : ℂ) * τ ∈ ball (0 : ℂ) (1 / 2) := by
    intro τ hτ
    rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
    rw [mem_ball_zero_iff] at hτ
    have : τ ∈ ball (0 : ℂ) (s / 2) := mem_ball_zero_iff.mpr hτ
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at hτ ⊢
    calc s⁻¹ * ‖τ‖ * 2 = s⁻¹ * (‖τ‖ * 2) := by ring
      _ < s⁻¹ * s := mul_lt_mul_of_pos_left hτ (by positivity)
      _ = 1 := inv_mul_cancel₀ hs_pos.ne'
  have hrC_rel : ∀ τ ∈ ball (0 : ℂ) rτ,
      rC τ ∈ closedBall (0 : ℂ) s ∧ rC τ + ψF (rC τ) = τ := by
    intro τ hτ
    obtain ⟨hg1, hg2⟩ := hg_spec _ (hmem_half τ hτ)
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff] at hg1 ⊢
      dsimp [rC]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      exact mul_le_of_le_one_right hs_pos.le hg1
    · have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
      dsimp [rC, Ψ] at *
      have hg2' := congrArg (fun z : ℂ => (s : ℂ) * z) hg2
      simp only [mul_add] at hg2'
      rw [← mul_assoc (s : ℂ) (s⁻¹ : ℂ), mul_inv_cancel₀ hsC, one_mul] at hg2'
      rw [← mul_assoc (s : ℂ) (s⁻¹ : ℂ), mul_inv_cancel₀ hsC, one_mul] at hg2'
      simpa only [one_mul] using hg2'
  have hrC_diff : DifferentiableOn ℂ rC (ball 0 rτ) := fun τ hτ => by
    have hd1 := hg_deriv _ (hmem_half τ hτ)
    have hd2 : HasDerivAt (fun w : ℂ => (s⁻¹ : ℂ) * w) (s⁻¹ : ℂ) τ := by
      simpa using (hasDerivAt_id τ).const_mul (s⁻¹ : ℂ)
    exact ((hd1.comp τ hd2).const_mul (s : ℂ)).differentiableAt.differentiableWithinAt
  have hrC_0 : rC 0 = 0 := by
    have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_self (by norm_num)
    have h0_uniq : (0 : ℂ) + (1 : ℂ) * Ψ 0 = 0 := by simp [Ψ, hψF_0]
    have hg0 : 0 = g 0 := hg_uniq 0 h0_mem 0 (mem_closedBall_self zero_le_one) h0_uniq
    dsimp [rC]; rw [mul_zero, ← hg0, mul_zero]
  have hd_rC0 : deriv rC 0 = 1 := by
    have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := mem_ball_self (by norm_num)
    have hd1 := hg_deriv 0 h0_mem
    have h0_uniq : (0 : ℂ) + (1 : ℂ) * Ψ 0 = 0 := by simp [Ψ, hψF_0]
    have hg0 : g 0 = 0 := (hg_uniq 0 h0_mem 0 (mem_closedBall_self zero_le_one) h0_uniq).symm
    have hdΨ0 : deriv Ψ 0 = 0 := by
      have ha : (0 : ℂ) ∈ ball (0 : ℂ) r1 := mem_ball_self hr1_pos
      have hd_ψF : HasDerivAt ψF 0 0 := by
        simpa [hdψF_0] using (hψF_diff.differentiableAt (isOpen_ball.mem_nhds ha)).hasDerivAt
      have hd_sc : HasDerivAt (fun w : ℂ => (s : ℂ) * w) (s : ℂ) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_mul (s : ℂ)
      have hd_cmp : HasDerivAt (fun w : ℂ => ψF ((s : ℂ) * w)) (0 * (s : ℂ)) 0 :=
        hd_ψF.comp_of_eq 0 hd_sc (mul_zero _).symm
      have hd_cmp2 := hd_cmp.const_mul (s⁻¹ : ℂ)
      simpa [Ψ] using hd_cmp2.deriv
    rw [hg0, hdΨ0] at hd1
    simp only [mul_zero, add_zero, div_one] at hd1
    have hd2 : HasDerivAt (fun w : ℂ => (s⁻¹ : ℂ) * w) (s⁻¹ : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (s⁻¹ : ℂ)
    have hd_rC : HasDerivAt rC ((s : ℂ) * (1 * (s⁻¹ : ℂ))) 0 :=
      (hd1.comp_of_eq 0 hd2 (mul_zero _).symm).const_mul (s : ℂ)
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
    have heq : (s : ℂ) * (1 * (s⁻¹ : ℂ)) = 1 := by field_simp [hsC]
    rw [heq] at hd_rC
    exact hd_rC.deriv
  have hA_conj : ∀ z ∈ ball (0 : ℂ) r1, pg.A (starRingEnd ℂ z) = starRingEnd ℂ (pg.A z) := by
    refine conj_symm_of_real_ball hr1_pos ((pg.hA_an.mono (ball_subset_ball hr1_rA.le)).differentiableOn) ?_
    refine ⟨r1, hr1_pos, le_rfl, fun x hx0 hx_lt => pg.hA_real x ?_⟩
    rw [abs_of_pos hx0]; exact hx_lt.trans hr1_rA
  have hψF_conj : ∀ z ∈ ball (0 : ℂ) r1, ψF (starRingEnd ℂ z) = starRingEnd ℂ (ψF z) := by
    intro z hz
    dsimp [ψF]
    rw [hA_conj z hz, Complex.conj_cpow (pg.A z) ((2 / 3 : ℝ) : ℂ) (Complex.slitPlane_arg_ne_pi (hr1_slit z hz))]
    have h23 : starRingEnd ℂ ((2 / 3 : ℝ) : ℂ) = ((2 / 3 : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [h23]
    simp only [map_mul, map_sub, map_one]
  have hrC_conj : ∀ τ ∈ ball (0 : ℂ) rτ, rC (starRingEnd ℂ τ) = starRingEnd ℂ (rC τ) := by
    intro τ hτ
    have hτc : starRingEnd ℂ τ ∈ ball (0 : ℂ) rτ := by
      simpa only [mem_ball_zero_iff, Complex.norm_conj] using hτ
    have hg1 : g ((s⁻¹ : ℂ) * τ) ∈ closedBall (0 : ℂ) 1 := (hg_spec _ (hmem_half τ hτ)).1
    have hg2 : g ((s⁻¹ : ℂ) * τ) + (1 : ℂ) * Ψ (g ((s⁻¹ : ℂ) * τ)) = (s⁻¹ : ℂ) * τ :=
      (hg_spec _ (hmem_half τ hτ)).2
    have hgc_mem : starRingEnd ℂ (g ((s⁻¹ : ℂ) * τ)) ∈ closedBall (0 : ℂ) 1 := by
      simpa only [mem_closedBall_zero_iff, Complex.norm_conj] using hg1
    have hs_prod_r1 : (s : ℂ) * g ((s⁻¹ : ℂ) * τ) ∈ ball (0 : ℂ) r1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      calc s * ‖g ((s⁻¹ : ℂ) * τ)‖ ≤ s * 1 := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hg1) hs_pos.le
        _ = s := mul_one s
        _ < r1 := (min_le_left _ _).trans_lt (half_lt_self hr1_pos)
    have hΨ_conj : Ψ (starRingEnd ℂ (g ((s⁻¹ : ℂ) * τ))) = starRingEnd ℂ (Ψ (g ((s⁻¹ : ℂ) * τ))) := by
      dsimp [Ψ]
      rw [show (s : ℂ) * starRingEnd ℂ (g ((s⁻¹ : ℂ) * τ)) = starRingEnd ℂ ((s : ℂ) * g ((s⁻¹ : ℂ) * τ)) by
        simp only [map_mul, Complex.conj_ofReal]]
      rw [hψF_conj _ hs_prod_r1]
      simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    have hg_eq : starRingEnd ℂ (g ((s⁻¹ : ℂ) * τ)) = g ((s⁻¹ : ℂ) * starRingEnd ℂ τ) := by
      refine hg_uniq _ (hmem_half _ hτc) _ hgc_mem ?_
      rw [hΨ_conj]
      calc starRingEnd ℂ (g ((s⁻¹ : ℂ) * τ)) + (1 : ℂ) * starRingEnd ℂ (Ψ (g ((s⁻¹ : ℂ) * τ)))
          = starRingEnd ℂ (g ((s⁻¹ : ℂ) * τ) + (1 : ℂ) * Ψ (g ((s⁻¹ : ℂ) * τ))) := by
            simp only [map_add, map_mul, map_one]
        _ = starRingEnd ℂ ((s⁻¹ : ℂ) * τ) := by rw [hg2]
        _ = (s⁻¹ : ℂ) * starRingEnd ℂ τ := by simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    dsimp [rC]
    rw [← hg_eq, map_mul, Complex.conj_ofReal]
  refine ⟨rτ, hrτ_pos, s * 4 / 3, by positivity, ?_, rC, hrC_diff, hrC_conj, hrC_0, hd_rC0, ?_⟩
  · have : s ≤ r1 / 2 := min_le_left _ _
    have hr1_le : r1 ≤ 1 / (10 * π) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [this, hr1_le, hr1_pos]
  · intro τ hτ0 hτ_lt
    have hτ_ball : (τ : ℂ) ∈ ball (0 : ℂ) rτ := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]; exact hτ_lt
    obtain ⟨hmem_s, hrel⟩ := hrC_rel (τ : ℂ) hτ_ball
    have him : (rC (τ : ℂ)).im = 0 := by
      have h := hrC_conj (τ : ℂ) hτ_ball
      simp only [Complex.conj_ofReal] at h
      have him0 := congrArg Complex.im h
      simp only [Complex.conj_im] at him0
      linarith only [him0]
    set r : ℝ := (rC (τ : ℂ)).re
    have hr_c : rC (τ : ℂ) = (r : ℂ) := Complex.ext rfl him
    have hr_abs : |r| ≤ s := by
      simpa [hr_c, Complex.norm_real, Real.norm_eq_abs] using mem_closedBall_zero_iff.mp hmem_s
    have hψ_bd : ‖ψF (r : ℂ)‖ ≤ (1 / 4) * |r| := by
      have hder : ∀ x ∈ closedBall (0 : ℂ) |r|, HasDerivWithinAt ψF (deriv ψF x) (closedBall (0 : ℂ) |r|) x := by
        intro x hx
        have hx' : x ∈ ball (0 : ℂ) r1 := by
          rw [mem_ball_zero_iff]
          exact (mem_closedBall_zero_iff.mp hx).trans_lt (hr_abs.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hr1_pos)))
        exact (hψF_diff.differentiableAt (isOpen_ball.mem_nhds hx')).hasDerivAt.hasDerivWithinAt
      have hmv := (convex_closedBall (0 : ℂ) |r|).norm_image_sub_le_of_norm_hasDerivWithin_le
        hder (fun x hx => hs_bound_d x (closedBall_subset_closedBall hr_abs hx))
        (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]) (mem_closedBall_self (abs_nonneg r))
      simpa [hψF_0, dist_eq_norm, norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] using hmv
    have hr_diff : |r - τ| ≤ (1 / 4) * |r| := by
      have hsub : ((r - τ : ℝ) : ℂ) = -ψF (r : ℂ) := by
        rw [hr_c] at hrel; push_cast; linear_combination hrel
      rw [← Real.norm_eq_abs, ← Complex.norm_real, hsub, norm_neg]
      exact hψ_bd
    have h43 : |r| ≤ 4 / 3 * τ := by
      have h2 : |r| ≤ τ + |r - τ| := by
        calc |r| = |(r - τ) + τ| := by ring_nf
          _ ≤ |r - τ| + |τ| := abs_add_le _ _
          _ = τ + |r - τ| := by rw [abs_of_pos hτ0, add_comm]
      linarith only [h2, hr_diff]
    have hr_pos : 0 < r := by
      have h1 := (abs_le.mp hr_diff).1
      linarith only [h1, h43, hτ0]
    have hr_lt_sτ : r < s * 4 / 3 := by
      have h1 : r = |r| := (abs_of_pos hr_pos).symm
      have hτ_s : τ < s / 2 := hτ_lt
      have h2 : 4 / 3 * τ < 4 / 3 * (s / 2) := by linarith only [hτ_s]
      linarith only [h1, h43, h2, hs_pos]
    have hr_lt_r1 : r < r1 := by
      have : s ≤ r1 / 2 := min_le_left _ _
      linarith only [hr_lt_sτ, this, hr1_pos]
    have hr_tip_lt : xiStar + r < xiStar + min (min pg.r_A (1 / 2)) (xiStar / 2) := by
      have hle : r1 ≤ min (min pg.r_A (1 / 2)) (xiStar / 2) := by
        have h1 : r1 ≤ R0 := min_le_left _ _
        have h2 : R0 ≤ pg.r_A / 2 := min_le_left _ _
        have h3 : R0 ≤ 1 / (10 * π) := (min_le_right _ _).trans (min_le_left _ _)
        have h4 : R0 ≤ xiStar / 2 := (min_le_right _ _).trans (min_le_right _ _)
        have h12 : 1 / (10 * π) ≤ 1 / 2 := by
          have : 1 ≤ π := by linarith only [Real.two_le_pi]
          rw [one_div_le_one_div (by positivity) (by norm_num)]
          linarith only [this]
        exact le_min (le_min (by linarith only [h1, h2, hrA]) (by linarith only [h1, h3, h12])) (by linarith only [h1, h4])
      linarith only [hr_lt_r1, hle]
    have htip := tip_potential_cumulN_eq (by linarith only [hr_pos] : xiStar < xiStar + r) hr_tip_lt
    simp only [add_sub_cancel_left] at htip
    have hAre_pos : 0 < (pg.A (r : ℂ)).re := by
      have hmem : (r : ℂ) ∈ ball (0 : ℂ) rA1 := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]
        exact hr_lt_r1.trans_le ((min_le_right _ _).trans (half_le_self hrA1_pos.le))
      have hnorm : ‖pg.A (r : ℂ) - 1‖ < 1 / 2 := hrA1_ball hmem
      have habs : |(pg.A (r : ℂ) - 1).re| ≤ ‖pg.A (r : ℂ) - 1‖ := Complex.abs_re_le_norm _
      have hsub : (pg.A (r : ℂ) - 1).re = (pg.A (r : ℂ)).re - 1 := by simp
      rw [hsub] at habs
      linarith only [(abs_lt.mp (habs.trans_lt hnorm)).1]
    have hAim0 : (pg.A (r : ℂ)).im = 0 := pg.hA_real r (by rw [abs_of_pos hr_pos]; exact hr_lt_r1.trans hr1_rA)
    have hAc : pg.A (r : ℂ) = (((pg.A (r : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hAim0
    have hF_re : (r * (pg.A (r : ℂ)).re ^ (2 / 3 : ℝ) : ℝ) = τ := by
      have hrel_r : (r : ℂ) * (pg.A (r : ℂ)) ^ ((2 / 3 : ℝ) : ℂ) = (τ : ℂ) := by
        calc (r : ℂ) * (pg.A (r : ℂ)) ^ ((2 / 3 : ℝ) : ℂ)
            = (r : ℂ) + (r : ℂ) * ((pg.A (r : ℂ)) ^ ((2 / 3 : ℝ) : ℂ) - 1) := by ring
          _ = rC (τ : ℂ) + ψF (rC (τ : ℂ)) := by rw [hr_c]
          _ = (τ : ℂ) := hrel
      rw [hAc, ← Complex.ofReal_cpow hAre_pos.le, ← Complex.ofReal_mul] at hrel_r
      exact Complex.ofReal_injective hrel_r
    have htau_eq : tauPhase (xiStar + r) = τ := by
      unfold tauPhase
      rw [← htip, Real.mul_rpow (Real.rpow_nonneg hr_pos.le _) hAre_pos.le, ← Real.rpow_mul hr_pos.le]
      norm_num
      exact hF_re
    exact ⟨hr_pos, hr_lt_sτ, him, htau_eq⟩

/-! ### 3. Holomorphic slit factor `Y0` (`τ * Y0 τ = y(ξ_* + rC τ)^2`) -/

private lemma virasoro_Y0_exists :
    ∃ rY : ℝ, 0 < rY ∧ ∃ sY : ℝ, 0 < sY ∧ sY ≤ 1 / (10 * π) ∧
      ∃ rC Y0 : ℂ → ℂ,
        DifferentiableOn ℂ rC (ball 0 rY) ∧
        DifferentiableOn ℂ Y0 (ball 0 rY) ∧
        (∀ τ ∈ ball (0 : ℂ) rY, Y0 (starRingEnd ℂ τ) = starRingEnd ℂ (Y0 τ)) ∧
        (∀ τ ∈ ball (0 : ℂ) rY, 0 < (Y0 τ).re ∧ Y0 τ ∈ Complex.slitPlane) ∧
        Y0 0 = (slitY : ℂ) ∧
        deriv Y0 0 = ((slitY * slitB : ℝ) : ℂ) ∧
        (∀ τ : ℝ, 0 < τ → τ < rY →
          0 < (rC (τ : ℂ)).re ∧ (rC (τ : ℂ)).re < sY ∧
          (rC (τ : ℂ)).im = 0 ∧
          tauPhase (xiStar + (rC (τ : ℂ)).re) = τ ∧
          lowerYVal (xiStar + (rC (τ : ℂ)).re) ∈ Ioo (0 : ℝ) 1 ∧
          τ * (Y0 (τ : ℂ)).re = lowerYVal (xiStar + (rC (τ : ℂ)).re) ^ 2) := by
  obtain ⟨rτ, hrτ_pos, sτ, hsτ_pos, hsτ_le, rC, hrC_diff, hrC_conj, hrC_0, hd_rC0, hrC_real⟩ :=
    virasoro_tauInv_exists
  let coshY : ℂ → ℂ := fun τ =>
    (Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) - (√2 : ℂ)) /
      (Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ))
  have hden0 : Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC 0)) + (√2 : ℂ) = ((2 * √2 : ℝ) : ℂ) := by
    rw [hrC_0, add_zero, show (π : ℂ) * (xiStar : ℂ) = ((π * xiStar : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cosh, cosh_pi_xiStar]
    push_cast; ring
  have hden_cont : ContinuousAt (fun τ => Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ)) 0 := by
    refine ContinuousAt.add ?_ continuousAt_const
    exact Complex.continuous_cosh.continuousAt.comp
      (continuousAt_const.mul (continuousAt_const.add ((hrC_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrτ_pos))).continuousAt)))
  have hev_den : ∀ᶠ τ : ℂ in 𝓝 0, ‖Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ) - ((2 * √2 : ℝ) : ℂ)‖ < √2 := by
    have : Tendsto (fun τ => Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ)) (𝓝 0) (𝓝 ((2 * √2 : ℝ) : ℂ)) := by
      simpa [hden0] using hden_cont.tendsto
    have hball : ∀ᶠ τ : ℂ in 𝓝 0, Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ) ∈
        ball (((2 * √2 : ℝ) : ℂ)) √2 :=
      this.eventually (Metric.ball_mem_nhds _ (Real.sqrt_pos.mpr (by norm_num)))
    exact hball.mono fun _ h => by simpa [Metric.mem_ball, dist_eq_norm] using h
  obtain ⟨r1, hr1_pos, hr1_ball⟩ := Metric.mem_nhds_iff.mp hev_den
  set rY1 : ℝ := min rτ r1
  have hrY1_pos : 0 < rY1 := lt_min hrτ_pos hr1_pos
  have hden_ne : ∀ τ ∈ ball (0 : ℂ) rY1, Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ) ≠ 0 := by
    intro τ hτ
    have hτ' : τ ∈ ball (0 : ℂ) r1 := ball_subset_ball (min_le_right _ _) hτ
    have hdist : ‖Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)) + (√2 : ℂ) - ((2 * √2 : ℝ) : ℂ)‖ < √2 := hr1_ball hτ'
    intro h0
    rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hdist
    linarith only [hdist, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
  have hcoshY_diff : DifferentiableOn ℂ coshY (ball 0 rY1) := fun τ hτ => by
    have hτ' : τ ∈ ball (0 : ℂ) rτ := ball_subset_ball (min_le_left _ _) hτ
    have hd_rC : DifferentiableAt ℂ rC τ := hrC_diff.differentiableAt (isOpen_ball.mem_nhds hτ')
    have hd_cosh : DifferentiableAt ℂ (fun w => Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC w))) τ :=
      (Complex.differentiable_cosh _).comp τ (differentiableAt_const _ |>.mul (differentiableAt_const _ |>.add hd_rC))
    exact ((hd_cosh.sub_const _).div (hd_cosh.add_const _) (hden_ne τ hτ)).differentiableWithinAt
  have hcoshY_0 : coshY 0 = 0 := by
    dsimp [coshY]
    rw [hrC_0, add_zero, show (π : ℂ) * (xiStar : ℂ) = ((π * xiStar : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cosh, cosh_pi_xiStar]
    simp
  let Y0 : ℂ → ℂ := dslope coshY 0
  have hY0_diff : DifferentiableOn ℂ Y0 (ball 0 rY1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hrY1_pos))).mpr hcoshY_diff
  have hY0_0 : Y0 0 = (slitY : ℂ) := by
    dsimp [Y0]; rw [dslope_same]
    have hd_rC : HasDerivAt rC 1 0 := hd_rC0 ▸ (hrC_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrτ_pos))).hasDerivAt
    have hd_arg : HasDerivAt (fun τ => (π : ℂ) * ((xiStar : ℂ) + rC τ)) (π : ℂ) 0 := by
      have := (hd_rC.const_add (xiStar : ℂ)).const_mul (π : ℂ)
      simpa using this
    have hd_c : HasDerivAt (fun τ => Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC τ)))
        ((π : ℂ) * Complex.sinh ((π : ℂ) * ((xiStar : ℂ) + rC 0))) 0 := by
      simpa [Function.comp_def, mul_comm] using (Complex.hasDerivAt_cosh _).comp 0 hd_arg
    have hnum0 : Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC 0)) - (√2 : ℂ) = 0 := by
      rw [hrC_0, add_zero, show (π : ℂ) * (xiStar : ℂ) = ((π * xiStar : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_cosh, cosh_pi_xiStar, sub_self]
    have hsinh0 : Complex.sinh ((π : ℂ) * ((xiStar : ℂ) + rC 0)) = 1 := by
      rw [hrC_0, add_zero, show (π : ℂ) * (xiStar : ℂ) = ((π * xiStar : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_sinh, sinh_pi_mul_xiStar]; simp
    have hden0_ne : Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC 0)) + (√2 : ℂ) ≠ 0 := hden_ne 0 (mem_ball_self hrY1_pos)
    have hd_q := (hd_c.sub_const (√2 : ℂ)).div (hd_c.add_const (√2 : ℂ)) hden0_ne
    rw [hnum0, hsinh0, hden0] at hd_q
    have hd_val : deriv coshY 0 = ((slitY : ℝ) : ℂ) := by
      rw [show deriv coshY 0 = deriv ((fun x => Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC x)) - (√2 : ℂ)) /
          (fun x => Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + rC x)) + (√2 : ℂ))) 0 from rfl, hd_q.deriv]
      unfold slitY
      have h2C : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      push_cast
      field_simp [h2C]
      ring
    exact hd_val
  have hev_reY : ∀ᶠ τ : ℂ in 𝓝 0, 0 < (Y0 τ).re := by
    have hcont : ContinuousAt Y0 0 := (hY0_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrY1_pos))).continuousAt
    have hlim : Tendsto (fun τ => (Y0 τ).re) (𝓝 0) (𝓝 slitY) := by
      have := Complex.continuous_re.continuousAt.tendsto.comp hcont.tendsto
      simpa [Function.comp_def, hY0_0] using this
    have hslitY : 0 < slitY := by unfold slitY; positivity
    exact hlim.eventually (Ioi_mem_nhds hslitY)
  obtain ⟨r2, hr2_pos, hr2_ball⟩ := Metric.mem_nhds_iff.mp hev_reY
  set rY : ℝ := min rY1 r2
  have hrY_pos : 0 < rY := lt_min hrY1_pos hr2_pos
  have hY0_conj : ∀ τ ∈ ball (0 : ℂ) rY, Y0 (starRingEnd ℂ τ) = starRingEnd ℂ (Y0 τ) := by
    refine conj_symm_of_real_ball hrY_pos (hY0_diff.mono (ball_subset_ball (min_le_left _ _))) ?_
    refine ⟨rY, hrY_pos, le_rfl, fun τ hτ0 hτ_lt => ?_⟩
    obtain ⟨hr_pos, hr_lt, him, _⟩ := hrC_real τ hτ0 (hτ_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    have hrc : rC (τ : ℂ) = (((rC (τ : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl him
    have hnum_im : (coshY (τ : ℂ)).im = 0 := by
      dsimp [coshY]; rw [hrc]
      have harg : (π : ℂ) * ((xiStar : ℂ) + ((rC (τ : ℂ)).re : ℝ)) =
          ((π * (xiStar + (rC (τ : ℂ)).re) : ℝ) : ℂ) := by push_cast; ring
      rw [harg, ← Complex.ofReal_cosh]
      rw [show ((Real.cosh (π * (xiStar + (rC (τ : ℂ)).re)) : ℂ) - (√2 : ℂ)) /
          ((Real.cosh (π * (xiStar + (rC (τ : ℂ)).re)) : ℂ) + (√2 : ℂ)) =
          (((Real.cosh (π * (xiStar + (rC (τ : ℂ)).re)) - √2) /
            (Real.cosh (π * (xiStar + (rC (τ : ℂ)).re)) + √2) : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_im _
    have hτC : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ0.ne'
    have hmul : (τ : ℂ) * Y0 (τ : ℂ) = coshY (τ : ℂ) := by
      calc (τ : ℂ) * Y0 (τ : ℂ)
          = ((τ : ℂ) - 0) • dslope coshY 0 (τ : ℂ) := by simp [Y0]
        _ = coshY (τ : ℂ) - coshY 0 := sub_smul_dslope coshY 0 (τ : ℂ)
        _ = coshY (τ : ℂ) := by rw [hcoshY_0, sub_zero]
    have him2 := congrArg Complex.im hmul
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him2
    rw [hnum_im] at him2
    exact (mul_eq_zero.mp him2).resolve_left hτ0.ne'
  have hY0_real_band : ∀ τ : ℝ, 0 < τ → τ < rY →
      0 < (rC (τ : ℂ)).re ∧ (rC (τ : ℂ)).re < sτ ∧
      (rC (τ : ℂ)).im = 0 ∧
      tauPhase (xiStar + (rC (τ : ℂ)).re) = τ ∧
      lowerYVal (xiStar + (rC (τ : ℂ)).re) ∈ Ioo (0 : ℝ) 1 ∧
      τ * (Y0 (τ : ℂ)).re = lowerYVal (xiStar + (rC (τ : ℂ)).re) ^ 2 := by
    intro τ hτ0 hτ_lt
    obtain ⟨hr_pos, hr_lt, him, htau⟩ := hrC_real τ hτ0 (hτ_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    set r : ℝ := (rC (τ : ℂ)).re
    set y : ℝ := lowerYVal (xiStar + r)
    have hcosh_gt : √2 < Real.cosh (π * (xiStar + r)) := by
      rw [← cosh_pi_xiStar]
      exact Real.cosh_lt_cosh.mpr (by
        rw [abs_of_pos (mul_pos Real.pi_pos xiStar_pos), abs_of_pos (mul_pos Real.pi_pos (by linarith only [xiStar_pos, hr_pos]))]
        exact mul_lt_mul_of_pos_left (by linarith only [hr_pos]) Real.pi_pos)
    have hden_pos : 0 < Real.cosh (π * (xiStar + r)) + √2 := by positivity
    have hq_pos : 0 < (Real.cosh (π * (xiStar + r)) - √2) / (Real.cosh (π * (xiStar + r)) + √2) :=
      div_pos (by linarith only [hcosh_gt]) hden_pos
    have hq_lt1 : (Real.cosh (π * (xiStar + r)) - √2) / (Real.cosh (π * (xiStar + r)) + √2) < 1 := by
      rw [div_lt_one hden_pos]; linarith only [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    have hy0 : 0 < y := Real.sqrt_pos.mpr hq_pos
    have hy1 : y < 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hq_pos.le hq_lt1
    have hmul : (τ : ℂ) * Y0 (τ : ℂ) = coshY (τ : ℂ) := by
      calc (τ : ℂ) * Y0 (τ : ℂ)
          = ((τ : ℂ) - 0) • dslope coshY 0 (τ : ℂ) := by simp [Y0]
        _ = coshY (τ : ℂ) - coshY 0 := sub_smul_dslope coshY 0 (τ : ℂ)
        _ = coshY (τ : ℂ) := by rw [hcoshY_0, sub_zero]
    have hrc : rC (τ : ℂ) = (r : ℂ) := Complex.ext rfl him
    have hcoshy_re : (coshY (τ : ℂ)).re = y ^ 2 := by
      dsimp [coshY]; rw [hrc]
      have harg : (π : ℂ) * ((xiStar : ℂ) + (r : ℂ)) = ((π * (xiStar + r) : ℝ) : ℂ) := by push_cast; ring
      rw [harg, ← Complex.ofReal_cosh]
      have : ((Real.cosh (π * (xiStar + r)) : ℂ) - (√2 : ℂ)) / ((Real.cosh (π * (xiStar + r)) : ℂ) + (√2 : ℂ)) =
          (((Real.cosh (π * (xiStar + r)) - √2) / (Real.cosh (π * (xiStar + r)) + √2) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [this, Complex.ofReal_re]
      exact (Real.sq_sqrt hq_pos.le).symm
    have hre := congrArg Complex.re hmul
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    rw [hre, hcoshy_re]
    exact ⟨hr_pos, hr_lt, him, htau, ⟨hy0, hy1⟩, rfl⟩
  have hd_Y0 : deriv Y0 0 = ((slitY * slitB : ℝ) : ℂ) := by
    have hd_at := (hY0_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrY1_pos))).hasDerivAt
    have hlim : Tendsto (fun τ : ℝ => ((Y0 (τ : ℂ) - Y0 0) / (τ : ℂ)).re) (𝓝[>] 0) (𝓝 (deriv Y0 0).re) := by
      have h1 : Tendsto (fun z : ℂ => (Y0 z - Y0 0) / z) (𝓝[≠] 0) (𝓝 (deriv Y0 0)) := by
        have := hd_at.tendsto_slope_zero
        simpa [smul_eq_mul, div_eq_inv_mul] using this
      have hre := Complex.continuous_re.continuousAt.tendsto.comp h1
      have h2 : Tendsto (fun τ : ℝ => (τ : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨(Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds),
           by filter_upwards [self_mem_nhdsWithin] with τ hτ; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)⟩
      exact hre.comp h2
    have hbound : ∀ᶠ τ : ℝ in 𝓝[>] 0, |((Y0 (τ : ℂ) - Y0 0) / (τ : ℂ)).re - slitY * slitB| ≤ 290 * τ := by
      filter_upwards [Ioo_mem_nhdsGT hrY_pos] with τ hτ
      obtain ⟨hr_pos, hr_lt, _, htau, ⟨hy0, hy1⟩, hτY⟩ := hY0_real_band τ hτ.1 hτ.2
      set r : ℝ := (rC (τ : ℂ)).re
      set y : ℝ := lowerYVal (xiStar + r)
      have hπr : π * r ≤ 1 / 10 := by
        have h1 : r < sτ := hr_lt
        have h2 : sτ ≤ 1 / (10 * π) := hsτ_le
        have hpi := Real.pi_pos
        calc π * r ≤ π * (1 / (10 * π)) := by nlinarith only [h1, h2, hpi]
          _ = 1 / 10 := by field_simp [hpi.ne']
      have hC_eq : Real.cosh (π * (xiStar + r)) = √2 * (1 + y ^ 2) / (1 - y ^ 2) := by
        have hden_pos : 0 < Real.cosh (π * (xiStar + r)) + √2 := by positivity
        have hq : y ^ 2 = (Real.cosh (π * (xiStar + r)) - √2) / (Real.cosh (π * (xiStar + r)) + √2) := by
          have h1 : √2 < Real.cosh (π * (xiStar + r)) := by
            rw [← cosh_pi_xiStar]
            exact Real.cosh_lt_cosh.mpr (by
              rw [abs_of_pos (mul_pos Real.pi_pos xiStar_pos), abs_of_pos (mul_pos Real.pi_pos (by linarith only [xiStar_pos, hr_pos]))]
              exact mul_lt_mul_of_pos_left (by linarith only [hr_pos]) Real.pi_pos)
          exact Real.sq_sqrt (div_nonneg (by linarith only [h1]) hden_pos.le)
        have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
        rw [eq_div_iff hy2.ne']
        have : y ^ 2 * (Real.cosh (π * (xiStar + r)) + √2) = Real.cosh (π * (xiStar + r)) - √2 := by
          rw [hq]; field_simp [hden_pos.ne']
        nlinarith only [this]
      have hsq := slit_sq_tau hr_pos hπr hy0 hy1 hC_eq
      rw [htau, ← hτY] at hsq
      have hre_div : ((Y0 (τ : ℂ) - Y0 0) / (τ : ℂ)).re = ((Y0 (τ : ℂ)).re - slitY) / τ := by
        rw [hY0_0, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
          Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← div_eq_mul_inv]
      rw [hre_div]
      have halg : ((Y0 (τ : ℂ)).re - slitY) / τ - slitY * slitB =
          (τ * (Y0 (τ : ℂ)).re - slitY * τ * (1 + slitB * τ)) / τ ^ 2 := by
        field_simp [hτ.1.ne']; ring
      rw [halg, abs_div, abs_of_pos (sq_pos_of_pos hτ.1)]
      calc |τ * (Y0 (τ : ℂ)).re - slitY * τ * (1 + slitB * τ)| / τ ^ 2
          ≤ (290 * τ ^ 3) / τ ^ 2 := div_le_div_of_nonneg_right hsq (sq_nonneg _)
        _ = 290 * τ := by field_simp [hτ.1.ne']
    have h0_lim : Tendsto (fun τ : ℝ => ((Y0 (τ : ℂ) - Y0 0) / (τ : ℂ)).re) (𝓝[>] 0) (𝓝 (slitY * slitB)) := by
      have h290 : Tendsto (fun τ : ℝ => 290 * τ) (𝓝[>] 0) (𝓝 0) := by
        have hcont290 : ContinuousAt (fun τ : ℝ => 290 * τ) 0 := (continuous_const.mul continuous_id).continuousAt
        simpa using hcont290.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound h290)
    have hre_eq : (deriv Y0 0).re = slitY * slitB := tendsto_nhds_unique hlim h0_lim
    have him_eq : (deriv Y0 0).im = 0 := by
      have hY0d : HasDerivAt Y0 (deriv Y0 0) (starRingEnd ℂ 0) := by
        rw [map_zero]
        exact (hY0_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrY1_pos))).hasDerivAt
      have hconj := hasDerivAt_conj_conj_psi hY0d
      have hfun_eq : (fun w : ℂ => starRingEnd ℂ (Y0 (starRingEnd ℂ w))) =ᶠ[𝓝 0] Y0 := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrY_pos)] with w hw
        rw [hY0_conj w (by simpa [mem_ball_zero_iff] using hw), Complex.conj_conj]
      have hderiv_eq : starRingEnd ℂ (deriv Y0 0) = deriv Y0 0 := by
        rw [← hconj.deriv, hfun_eq.deriv_eq]
      have him := congrArg Complex.im hderiv_eq
      simp only [Complex.conj_im] at him
      linarith only [him]
    exact Complex.ext hre_eq him_eq
  refine ⟨rY, hrY_pos, sτ, hsτ_pos, hsτ_le, rC, Y0,
    hrC_diff.mono (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))),
    hY0_diff.mono (ball_subset_ball (min_le_left _ _)), hY0_conj, ?_, hY0_0, hd_Y0, hY0_real_band⟩
  intro τ hτ
  have hτ' : τ ∈ ball (0 : ℂ) r2 := ball_subset_ball (min_le_right _ _) hτ
  have hre : 0 < (Y0 τ).re := by simpa using hr2_ball hτ'
  exact ⟨hre, Complex.mem_slitPlane_iff.mpr (Or.inl hre)⟩

/-! ### 4. Outer factor `T_out` (`L` from `VirasoroG3Taylor.g3Out_taylor`) -/

private lemma gout_mem_closure_halfDisc_of_re_zero {y : ℝ} (hy : |y| < 1) :
    (y : ℂ) * Complex.I ∈ closure halfDisc := by
  have hy_norm : ‖(y : ℂ) * Complex.I‖ < 1 := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I] using hy
  rw [Metric.mem_closure_iff]
  intro ε hε_pos
  set δ : ℝ := min (ε / 2) ((1 - |y|) / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hε_pos) (by linarith only [hy])
  refine ⟨(δ : ℂ) + (y : ℂ) * Complex.I, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hnorm_d : ‖(δ : ℂ) + (y : ℂ) * Complex.I‖ ≤ δ + |y| := by
        calc ‖(δ : ℂ) + (y : ℂ) * Complex.I‖
            ≤ ‖(δ : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = δ + |y| := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      have : δ ≤ (1 - |y|) / 2 := min_le_right _ _
      linarith only [hnorm_d, this, hy]
    · simp [hδ_pos]
  · rw [dist_eq_norm]
    have hsub : (y : ℂ) * Complex.I - ((δ : ℂ) + (y : ℂ) * Complex.I) = -(δ : ℂ) := by ring
    rw [hsub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
    exact (min_le_left _ _).trans_lt (half_lt_self hε_pos)

private lemma three_deriv_comp_const_mul {F : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (ball 0 ρ)) {a : ℂ} (ha : ‖a‖ ≤ 1) :
    iteratedDeriv 3 (fun z : ℂ => F (a * z)) 0 = a ^ 3 * iteratedDeriv 3 F 0 := by
  have h1 : ∀ z ∈ ball (0 : ℂ) ρ,
      deriv (fun w => F (a * w)) z = a * deriv F (a * z) := fun z hz => by
    rw [mem_ball_zero_iff] at hz
    have haz : a * z ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, norm_mul]
      calc ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = ‖z‖ := one_mul _
        _ < ρ := hz
    have hdF : HasDerivAt F (deriv F (a * z)) (a * z) :=
      (hF.differentiableAt (isOpen_ball.mem_nhds haz)).hasDerivAt
    have hdz : HasDerivAt (fun w : ℂ => a * w) a z := by simpa using (hasDerivAt_id z).const_mul a
    have hdc : HasDerivAt (fun w => F (a * w)) (deriv F (a * z) * a) z := hdF.comp z hdz
    simpa [mul_comm] using hdc.deriv
  have hF1 : DifferentiableOn ℂ (deriv F) (ball 0 ρ) := hF.deriv isOpen_ball
  have h2 : ∀ z ∈ ball (0 : ℂ) ρ,
      deriv (deriv (fun w => F (a * w))) z = a ^ 2 * deriv (deriv F) (a * z) := fun z hz => by
    have heq : deriv (fun w => F (a * w)) =ᶠ[𝓝 z] (fun w => a * deriv F (a * w)) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using h1 w hw
    rw [heq.deriv_eq]
    rw [mem_ball_zero_iff] at hz
    have haz : a * z ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, norm_mul]
      calc ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = ‖z‖ := one_mul _
        _ < ρ := hz
    have hdF1 : HasDerivAt (deriv F) (deriv (deriv F) (a * z)) (a * z) :=
      (hF1.differentiableAt (isOpen_ball.mem_nhds haz)).hasDerivAt
    have hdz : HasDerivAt (fun w : ℂ => a * w) a z := by simpa using (hasDerivAt_id z).const_mul a
    have hdc0 : HasDerivAt (fun w => deriv F (a * w)) (deriv (deriv F) (a * z) * a) z :=
      hdF1.comp z hdz
    have hdc := hdc0.const_mul a
    rw [hdc.deriv]; ring
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) (ball 0 ρ) := hF1.deriv isOpen_ball
  have h3 : deriv (deriv (deriv (fun w => F (a * w)))) 0 = a ^ 3 * deriv (deriv (deriv F)) 0 := by
    have heq : deriv (deriv (fun w => F (a * w))) =ᶠ[𝓝 0] (fun w => a ^ 2 * deriv (deriv F) (a * w)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with w hw using h2 w hw
    rw [heq.deriv_eq]
    have hdF2 : HasDerivAt (deriv (deriv F)) (deriv (deriv (deriv F)) 0) 0 :=
      (hF2.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))).hasDerivAt
    have hdz : HasDerivAt (fun w : ℂ => a * w) a 0 := by simpa using (hasDerivAt_id (0 : ℂ)).const_mul a
    have hdc0 : HasDerivAt (fun w => deriv (deriv F) (a * w)) (deriv (deriv (deriv F)) 0 * a) 0 := by
      simpa [Function.comp_def, mul_zero] using hdF2.comp_of_eq 0 hdz (mul_zero a).symm
    have hdc := hdc0.const_mul (a ^ 2)
    rw [hdc.deriv]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  exact h3

private lemma virasoro_Tout_exists :
    ∃ rTout yTout M_out : ℝ, 0 < rTout ∧ 0 < yTout ∧ yTout ^ 2 ≤ rTout / 4 ∧ yTout ≤ 1 / 2 ∧ 0 ≤ M_out ∧
      ∃ T_out : ℂ → ℂ,
        DifferentiableOn ℂ T_out (ball 0 rTout) ∧
        (∀ w ∈ ball (0 : ℂ) rTout, T_out (starRingEnd ℂ w) = starRingEnd ℂ (T_out w)) ∧
        T_out 0 = (g1Vir : ℂ) ∧
        deriv T_out 0 = ((-g3Vir : ℝ) : ℂ) ∧
        (∀ w ∈ closedBall (0 : ℂ) (rTout / 4), ‖T_out w‖ ≤ M_out ∧ ‖deriv T_out w‖ ≤ M_out) ∧
        (∀ y : ℝ, 0 < y → y < yTout →
          y * (T_out ((y ^ 2 : ℝ) : ℂ)).re = thetaOut y ∧ |thetaOut y| < π) := by
  obtain ⟨ρL, hρL, L, hL_diff, hL_exp, hL0, hdL0, _, hdddL0⟩ := g3Out_taylor
  have hL_cont : ContinuousAt L 0 := (hL_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρL))).continuousAt
  have hev_L : ∀ᶠ z : ℂ in 𝓝 0, ‖L z‖ < π / 4 := by
    have : Tendsto L (𝓝 0) (𝓝 0) := by simpa [hL0] using hL_cont.tendsto
    have hball : ∀ᶠ z : ℂ in 𝓝 0, L z ∈ ball (0 : ℂ) (π / 4) :=
      this.eventually (Metric.ball_mem_nhds (0 : ℂ) (div_pos Real.pi_pos (by norm_num)))
    exact hball.mono fun _ h => by simpa [Metric.mem_ball, dist_eq_norm] using h
  obtain ⟨δL, hδL_pos, hδL_ball⟩ := Metric.mem_nhds_iff.mp hev_L
  have hL_conj : ∀ z ∈ ball (0 : ℂ) ρL, L (starRingEnd ℂ z) = starRingEnd ℂ (L z) := by
    refine conj_symm_of_real_ball hρL hL_diff ?_
    refine ⟨min ρL (min δL (1 / 2)), by positivity, min_le_left _ _, fun x hx0 hx_lt => ?_⟩
    have hx_half : (x : ℂ) ∈ halfDisc := by
      refine ⟨?_, by simp [hx0]⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact lt_trans (hx_lt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num)
    have hx_ρL : ‖(x : ℂ)‖ < ρL := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx_lt.trans_le (min_le_left _ _)
    have hx_δL : ‖(x : ℂ)‖ < δL := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hGx_exp : Gout (x : ℂ) = Complex.exp (L (x : ℂ)) := hL_exp (x : ℂ) (subset_closure hx_half) hx_ρL
    have hGx_conj : Gout (starRingEnd ℂ (x : ℂ)) = starRingEnd ℂ (Gout (x : ℂ)) := gout_conj hx_half
    simp only [Complex.conj_ofReal] at hGx_conj
    have h_exp_eq : Complex.exp (L (x : ℂ)) = Complex.exp (starRingEnd ℂ (L (x : ℂ))) := by
      rw [← hGx_exp]
      calc Gout (x : ℂ) = starRingEnd ℂ (Gout (x : ℂ)) := hGx_conj
        _ = starRingEnd ℂ (Complex.exp (L (x : ℂ))) := by rw [hGx_exp]
        _ = Complex.exp (starRingEnd ℂ (L (x : ℂ))) := (Complex.exp_conj _).symm
    have hdiff_exp : Complex.exp (L (x : ℂ) - starRingEnd ℂ (L (x : ℂ))) = 1 := by
      rw [Complex.exp_sub, h_exp_eq, div_self (Complex.exp_ne_zero _)]
    have hsub_eq : L (x : ℂ) - starRingEnd ℂ (L (x : ℂ)) = ((2 * (L (x : ℂ)).im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [hsub_eq] at hdiff_exp
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hdiff_exp
    have hk_im : 2 * (L (x : ℂ)).im = 2 * (k : ℝ) * π := by
      have h_lhs : (((2 * (L (x : ℂ)).im : ℝ) : ℂ) * Complex.I).im = 2 * (L (x : ℂ)).im := by simp
      have h_rhs : ((k : ℂ) * (2 * (π : ℂ) * Complex.I)).im = 2 * (k : ℝ) * π := by
        simp [Complex.mul_im]; ring
      have := congrArg Complex.im hk
      linarith only [this, h_lhs, h_rhs]
    have hLx_norm : ‖L (x : ℂ)‖ < π / 4 := hδL_ball (mem_ball_zero_iff.mpr hx_δL)
    have hLim_lt : |(L (x : ℂ)).im| < π / 4 :=
      (Complex.abs_im_le_norm _).trans_lt hLx_norm
    have hk0 : k = 0 := by
      have h_k : |(k : ℝ)| * π < π / 4 := by
        have h_abs : |(k : ℝ) * π| = |(L (x : ℂ)).im| := by
          congr 1; linarith only [hk_im]
        rw [abs_mul, abs_of_pos Real.pi_pos] at h_abs
        linarith only [h_abs, hLim_lt]
      have h_k1 : |(k : ℝ)| < 1 / 4 := by nlinarith only [h_k, Real.pi_pos]
      rcases Int.lt_trichotomy k 0 with hk_neg | rfl | hk_pos
      · have h1 : (1 : ℝ) ≤ -(k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ -k)
        linarith only [(abs_lt.mp h_k1).1, h1]
      · rfl
      · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
        linarith only [(abs_lt.mp h_k1).2, h1]
    rw [hk0, Int.cast_zero] at hk_im
    linarith only [hk_im]
  let oL : ℂ → ℂ := fun z => (L (Complex.I * z) - L (-Complex.I * z)) / (2 * Complex.I)
  have hoL_diff : DifferentiableOn ℂ oL (ball 0 ρL) := fun z hz => by
    have hz1 : Complex.I * z ∈ ball (0 : ℂ) ρL := by
      simpa [mem_ball_zero_iff, norm_mul, Complex.norm_I] using hz
    have hz2 : -Complex.I * z ∈ ball (0 : ℂ) ρL := by
      simpa [mem_ball_zero_iff, norm_mul, norm_neg, Complex.norm_I] using hz
    have hd1 := (hL_diff.differentiableAt (isOpen_ball.mem_nhds hz1)).comp z ((hasDerivAt_id z).const_mul Complex.I).differentiableAt
    have hd2 := (hL_diff.differentiableAt (isOpen_ball.mem_nhds hz2)).comp z ((hasDerivAt_id z).const_mul (-Complex.I)).differentiableAt
    exact ((hd1.sub hd2).div_const (2 * Complex.I)).differentiableWithinAt
  have hoL_odd : ∀ z ∈ ball (0 : ℂ) ρL, oL (-z) = -oL z := fun z _ => by
    dsimp [oL]
    rw [show Complex.I * -z = -Complex.I * z by ring, show -Complex.I * -z = Complex.I * z by ring]
    ring
  have hoL_conj : ∀ z ∈ ball (0 : ℂ) ρL, oL (starRingEnd ℂ z) = starRingEnd ℂ (oL z) := fun z hz => by
    have hz1 : Complex.I * z ∈ ball (0 : ℂ) ρL := by
      simpa [mem_ball_zero_iff, norm_mul, Complex.norm_I] using hz
    have hz2 : -Complex.I * z ∈ ball (0 : ℂ) ρL := by
      simpa [mem_ball_zero_iff, norm_mul, norm_neg, Complex.norm_I] using hz
    have hc1 : Complex.I * starRingEnd ℂ z = starRingEnd ℂ (-Complex.I * z) := by
      simp only [map_mul, map_neg, Complex.conj_I, neg_neg]
    have hc2 : -Complex.I * starRingEnd ℂ z = starRingEnd ℂ (Complex.I * z) := by
      simp only [map_mul, Complex.conj_I]
    dsimp [oL]
    rw [hc1, hc2, hL_conj _ hz2, hL_conj _ hz1]
    have h2I : starRingEnd ℂ (2 * Complex.I) = -(2 * Complex.I) := by
      simp only [map_mul, map_ofNat, Complex.conj_I]; ring
    rw [map_div₀, map_sub, h2I]
    ring
  have hdoL_0 : deriv oL 0 = (g1Vir : ℂ) := by
    have h0 : HasDerivAt L (g1Out : ℂ) 0 := by
      simpa [hdL0] using (hL_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρL))).hasDerivAt
    have hd_iz : HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul Complex.I
    have hd_niz : HasDerivAt (fun z : ℂ => -Complex.I * z) (-Complex.I) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-Complex.I)
    have h1 : HasDerivAt (fun z => L (Complex.I * z)) (Complex.I * (g1Out : ℂ)) 0 := by
      simpa [Function.comp_def, mul_comm] using h0.comp_of_eq 0 hd_iz (mul_zero _).symm
    have h2 : HasDerivAt (fun z => L (-Complex.I * z)) (-Complex.I * (g1Out : ℂ)) 0 := by
      simpa [Function.comp_def, mul_comm] using h0.comp_of_eq 0 hd_niz (mul_zero _).symm
    have h12 := (h1.sub h2).div_const (2 * Complex.I)
    have hval : (Complex.I * (g1Out : ℂ) - -Complex.I * (g1Out : ℂ)) / (2 * Complex.I) = (g1Vir : ℂ) := by
      rw [g1Out_eq_g1Vir]
      field_simp [Complex.I_ne_zero]
      ring
    rw [hval] at h12
    exact h12.deriv
  have hddd_oL0 : iteratedDeriv 3 oL 0 / 6 = ((-g3Vir : ℝ) : ℂ) := by
    have h1 : iteratedDeriv 3 (fun z => L (Complex.I * z)) 0 = Complex.I ^ 3 * iteratedDeriv 3 L 0 :=
      three_deriv_comp_const_mul hρL hL_diff (by simp)
    have h2 : iteratedDeriv 3 (fun z => L (-Complex.I * z)) 0 = (-Complex.I) ^ 3 * iteratedDeriv 3 L 0 :=
      three_deriv_comp_const_mul hρL hL_diff (by simp)
    have hoL_fun : oL = ((1 / (2 * Complex.I)) • fun z => L (Complex.I * z) - L (-Complex.I * z)) := by
      ext z; simp [oL, div_eq_inv_mul, smul_eq_mul]
    have hd1 : ContDiffAt ℂ 3 (fun z => L (Complex.I * z)) 0 := by
      have hdiff1 : DifferentiableOn ℂ (fun z => L (Complex.I * z)) (ball 0 ρL) := fun z hz => by
        have hz1 : Complex.I * z ∈ ball (0 : ℂ) ρL := by simpa [mem_ball_zero_iff, norm_mul] using hz
        exact ((hL_diff.differentiableAt (isOpen_ball.mem_nhds hz1)).comp z
          ((hasDerivAt_id z).const_mul Complex.I).differentiableAt).differentiableWithinAt
      exact ((hdiff1.analyticOnNhd isOpen_ball) 0 (mem_ball_self hρL)).contDiffAt
    have hd2 : ContDiffAt ℂ 3 (fun z => L (-Complex.I * z)) 0 := by
      have hdiff2 : DifferentiableOn ℂ (fun z => L (-Complex.I * z)) (ball 0 ρL) := fun z hz => by
        have hz2 : -Complex.I * z ∈ ball (0 : ℂ) ρL := by simpa [mem_ball_zero_iff, norm_mul, norm_neg] using hz
        exact ((hL_diff.differentiableAt (isOpen_ball.mem_nhds hz2)).comp z
          ((hasDerivAt_id z).const_mul (-Complex.I)).differentiableAt).differentiableWithinAt
      exact ((hdiff2.analyticOnNhd isOpen_ball) 0 (mem_ball_self hρL)).contDiffAt
    rw [hoL_fun, iteratedDeriv_const_smul (hd1.sub hd2),
      show (fun z => L (Complex.I * z) - L (-Complex.I * z)) = (fun z => L (Complex.I * z)) - (fun z => L (-Complex.I * z)) from rfl,
      iteratedDeriv_sub hd1 hd2, h1, h2]
    have hL3 : iteratedDeriv 3 L 0 / 6 = (g3Out : ℂ) := by
      simpa [iteratedDeriv_succ, iteratedDeriv_one] using hdddL0
    have hI3 : Complex.I ^ 3 = -Complex.I := by
      calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
        _ = (-1) * Complex.I := by rw [Complex.I_sq]
        _ = -Complex.I := by ring
    have hnI3 : (-Complex.I) ^ 3 = Complex.I := by
      calc (-Complex.I) ^ 3 = -(Complex.I ^ 2 * Complex.I) := by ring
        _ = -((-1) * Complex.I) := by rw [Complex.I_sq]
        _ = Complex.I := by ring
    rw [hI3, hnI3, smul_eq_mul]
    calc (1 / (2 * Complex.I) * (-Complex.I * iteratedDeriv 3 L 0 - Complex.I * iteratedDeriv 3 L 0)) / 6
        = -(iteratedDeriv 3 L 0 / 6) := by field_simp [Complex.I_ne_zero]; ring
      _ = -(g3Out : ℂ) := by rw [hL3]
      _ = ((-g3Vir : ℝ) : ℂ) := by rw [g3Out_eq_g3Vir]; push_cast; ring
  set rL : ℝ := min (ρL / 2) (1 / 2)
  have hrL_pos : 0 < rL := by positivity
  have hrL_lt : rL < ρL := (min_le_left _ _).trans_lt (half_lt_self hρL)
  have h_bdd : BddAbove ((fun z => ‖oL z‖) '' closedBall (0 : ℂ) rL) :=
    ((isCompact_closedBall (0 : ℂ) rL).image_of_continuousOn
      ((hoL_diff.mono (closedBall_subset_ball hrL_lt)).continuousOn.norm)).bddAbove
  set Bout : ℝ := max (sSup ((fun z => ‖oL z‖) '' closedBall (0 : ℂ) rL)) 0
  have hBout_nn : 0 ≤ Bout := le_max_right _ _
  have hBout_bd : ∀ z ∈ closedBall (0 : ℂ) rL, ‖oL z‖ ≤ Bout := fun z hz =>
    (le_csSup h_bdd ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  obtain ⟨T_out, hT_diff, hT_conj, hT_eq, hT0, hdT0, hT_bd, hdT_bd⟩ :=
    odd_holomorphic_factor hρL hrL_pos hrL_lt hBout_nn hoL_diff hBout_bd hoL_odd hoL_conj
  rw [hdoL_0] at hT0
  rw [hddd_oL0] at hdT0
  have hev_theta : ∀ᶠ y : ℝ in 𝓝 0, |thetaOut y| < π / 4 := by
    have hcont : ContinuousWithinAt thetaOut (Ioo (-1 : ℝ) 1) 0 := thetaOut_soft.2.2 0 (by constructor <;> norm_num)
    have hnhds : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have hlim : Tendsto thetaOut (𝓝 0) (𝓝 0) := by
      simpa [thetaOut_soft.1] using (hcont.continuousAt hnhds).tendsto
    have hball : ∀ᶠ y : ℝ in 𝓝 0, thetaOut y ∈ ball (0 : ℝ) (π / 4) :=
      hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) (div_pos Real.pi_pos (by norm_num)))
    exact hball.mono fun _ h => by simpa [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using h
  obtain ⟨yθ, hyθ_pos, hyθ_ball⟩ := Metric.mem_nhds_iff.mp hev_theta
  set yTout : ℝ := min (min (rL / 3) δL) (min yθ (1 / 2))
  have hyTout_pos : 0 < yTout := lt_min (lt_min (by positivity) hδL_pos) (lt_min hyθ_pos (by norm_num))
  have hyTout_rL3 : yTout ≤ rL / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hyTout_half : yTout ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let rTout : ℝ := rL ^ 2 / 2
  have hrTout_pos : 0 < rTout := by positivity
  have hy2_le : yTout ^ 2 ≤ rTout / 4 := by
    have h1 : yTout ^ 2 ≤ (rL / 3) ^ 2 := pow_le_pow_left₀ hyTout_pos.le hyTout_rL3 2
    have h2 : (rL / 3) ^ 2 ≤ rTout / 4 := by dsimp [rTout]; nlinarith only [sq_nonneg rL]
    linarith only [h1, h2]
  let Mout : ℝ := max (4 / 3 * Bout / rL) (32 / 3 * Bout / rL ^ 3)
  have hMout_nn : 0 ≤ Mout := le_max_of_le_left (by positivity)
  refine ⟨rTout, yTout, Mout, hrTout_pos, hyTout_pos, hy2_le, hyTout_half, hMout_nn, T_out,
    hT_diff.mono (ball_subset_ball (by dsimp [rTout]; nlinarith only [hrL_pos])),
    fun w hw => hT_conj w (ball_subset_ball (by dsimp [rTout]; nlinarith only [hrL_pos]) hw),
    hT0, hdT0, fun w hw => ?_, fun y hy0 hy_lt => ?_⟩
  · have hw4 : w ∈ closedBall (0 : ℂ) (rL ^ 2 / 4) :=
      closedBall_subset_closedBall (by dsimp [rTout]; nlinarith only [hrL_pos]) hw
    have hw8 : w ∈ closedBall (0 : ℂ) (rL ^ 2 / 8) :=
      closedBall_subset_closedBall (by dsimp [rTout]; linarith only []) hw
    exact ⟨(hT_bd w hw4).trans (le_max_left _ _), (hdT_bd w hw8).trans (le_max_right _ _)⟩
  · have hy_rL : y < rL := hy_lt.trans_le (hyTout_rL3.trans (by linarith only [hrL_pos]))
    have hy_δL : y < δL := hy_lt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hy_yθ : y < yθ := hy_lt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hy_1 : y < 1 := hy_lt.trans_le hyTout_half |>.trans (by norm_num)
    have hy_ρL : ‖Complex.I * (y : ℂ)‖ < ρL := by
      simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0] using hy_rL.trans hrL_lt
    have hy_cl : Complex.I * (y : ℂ) ∈ closure halfDisc := by
      rw [mul_comm]; exact gout_mem_closure_halfDisc_of_re_zero (by rw [abs_of_pos hy0]; exact hy_1)
    have hG_exp : Gout (Complex.I * (y : ℂ)) = Complex.exp (L (Complex.I * (y : ℂ))) := hL_exp _ hy_cl hy_ρL
    have hL_im_eq : L (-Complex.I * (y : ℂ)) = starRingEnd ℂ (L (Complex.I * (y : ℂ))) := by
      have h1 : Complex.I * (y : ℂ) ∈ ball (0 : ℂ) ρL := mem_ball_zero_iff.mpr hy_ρL
      rw [show -Complex.I * (y : ℂ) = starRingEnd ℂ (Complex.I * (y : ℂ)) by simp [Complex.conj_I]]
      exact hL_conj _ h1
    have hoL_y : oL (y : ℂ) = ((L (Complex.I * (y : ℂ))).im : ℂ) := by
      dsimp [oL]
      rw [hL_im_eq]
      have hsub : L (Complex.I * (y : ℂ)) - starRingEnd ℂ (L (Complex.I * (y : ℂ))) =
          ((2 * (L (Complex.I * (y : ℂ))).im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsub]
      field_simp [Complex.I_ne_zero]
      push_cast; ring
    have hT_y : (y : ℂ) * T_out ((y ^ 2 : ℝ) : ℂ) = oL (y : ℂ) := by
      have hy_ball : (y : ℂ) ∈ ball (0 : ℂ) rL := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]; exact hy_rL
      simpa [← Complex.ofReal_pow] using (hT_eq (y : ℂ) hy_ball).symm
    have hT_re : y * (T_out ((y ^ 2 : ℝ) : ℂ)).re = (L (Complex.I * (y : ℂ))).im := by
      have hre := congrArg Complex.re hT_y
      rw [hoL_y, Complex.ofReal_re] at hre
      simpa [Complex.mul_re] using hre
    have hpolar := gout_polar (⟨hy0, hy_1⟩ : y ∈ Ioo (0 : ℝ) 1)
    have hW_pos : 0 < Wslit y := by
      have hn : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := gout_modulus ⟨hy0, hy_1⟩
      rw [← hn, hG_exp]
      exact Complex.norm_exp _ ▸ Real.exp_pos _
    have hexp_norm : Real.exp (L (Complex.I * (y : ℂ))).re = Wslit y := by
      have hn1 : ‖Complex.exp (L (Complex.I * (y : ℂ)))‖ = Real.exp (L (Complex.I * (y : ℂ))).re := Complex.norm_exp _
      have hn2 : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := gout_modulus ⟨hy0, hy_1⟩
      rw [hG_exp, hn1] at hn2
      exact hn2
    have hsplit : L (Complex.I * (y : ℂ)) = ((L (Complex.I * (y : ℂ))).re : ℂ) + ((L (Complex.I * (y : ℂ))).im : ℂ) * Complex.I :=
      (Complex.re_add_im _).symm
    have hexp_eq : Complex.exp (((L (Complex.I * (y : ℂ))).im : ℂ) * Complex.I) =
        Complex.exp (Complex.I * (thetaOut y : ℂ)) := by
      have h1 : (Wslit y : ℂ) * Complex.exp (((L (Complex.I * (y : ℂ))).im : ℂ) * Complex.I) =
          (Wslit y : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ)) := by
        calc (Wslit y : ℂ) * Complex.exp (((L (Complex.I * (y : ℂ))).im : ℂ) * Complex.I)
            = Complex.exp ((L (Complex.I * (y : ℂ))).re : ℂ) * Complex.exp (((L (Complex.I * (y : ℂ))).im : ℂ) * Complex.I) := by
              rw [← Complex.ofReal_exp, hexp_norm]
          _ = Complex.exp (L (Complex.I * (y : ℂ))) := by rw [← Complex.exp_add, ← hsplit]
          _ = Gout (Complex.I * (y : ℂ)) := hG_exp.symm
          _ = (Wslit y : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ)) := hpolar
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hW_pos.ne') h1
    have hdiff_exp : Complex.exp (((((L (Complex.I * (y : ℂ))).im - thetaOut y : ℝ) : ℂ)) * Complex.I) = 1 := by
      rw [show ((((L (Complex.I * (y : ℂ))).im - thetaOut y : ℝ) : ℂ)) * Complex.I =
          ((L (Complex.I * (y : ℂ))).im : ℂ) * Complex.I - Complex.I * (thetaOut y : ℂ) by push_cast; ring]
      rw [Complex.exp_sub, hexp_eq, div_self (Complex.exp_ne_zero _)]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hdiff_exp
    have hk_eq : (L (Complex.I * (y : ℂ))).im - thetaOut y = 2 * (k : ℝ) * π := by
      have := congrArg Complex.im hk
      have h1 : ((((L (Complex.I * (y : ℂ))).im - thetaOut y : ℝ) : ℂ) * Complex.I).im =
          (L (Complex.I * (y : ℂ))).im - thetaOut y := by simp
      have h2 : ((k : ℂ) * (2 * (π : ℂ) * Complex.I)).im = 2 * (k : ℝ) * π := by
        simp [Complex.mul_im]; ring
      linarith only [this, h1, h2]
    have hLim_bd : |(L (Complex.I * (y : ℂ))).im| < π / 4 := by
      have hIy_mem : Complex.I * (y : ℂ) ∈ ball (0 : ℂ) δL := by
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
        exact hy_δL
      have hL_norm : ‖L (Complex.I * (y : ℂ))‖ < π / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hδL_ball hIy_mem
      exact (Complex.abs_im_le_norm _).trans_lt hL_norm
    have hth_bd : |thetaOut y| < π / 4 := by
      have : y ∈ ball (0 : ℝ) yθ := by rw [Real.ball_eq_Ioo]; exact ⟨by linarith only [hy0, hyθ_pos], by linarith only [hy_yθ]⟩
      simpa [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using hyθ_ball this
    have hk0 : k = 0 := by
      have hdiff_bd : |(L (Complex.I * (y : ℂ))).im - thetaOut y| < π / 2 := by
        calc |(L (Complex.I * (y : ℂ))).im - thetaOut y|
            ≤ |(L (Complex.I * (y : ℂ))).im| + |thetaOut y| := abs_sub _ _
          _ < π / 4 + π / 4 := add_lt_add hLim_bd hth_bd
          _ = π / 2 := by ring
      rw [hk_eq] at hdiff_bd
      have hk_lt : |(k : ℝ)| < 1 / 4 := by
        have hpi := Real.pi_pos
        rw [abs_mul, abs_mul, abs_two, abs_of_pos hpi] at hdiff_bd
        nlinarith only [hdiff_bd, hpi]
      rcases Int.lt_trichotomy k 0 with hk_neg | rfl | hk_pos
      · have : (1 : ℝ) ≤ -(k : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ -k by omega)
        linarith only [(abs_lt.mp hk_lt).1, this]
      · rfl
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
        linarith only [(abs_lt.mp hk_lt).2, this]
    simp only [hk0, Int.cast_zero] at hk_eq
    have him_th : (L (Complex.I * (y : ℂ))).im = thetaOut y := by linarith only [hk_eq]
    rw [hT_re, him_th]
    exact ⟨rfl, hth_bd.trans (by linarith only [Real.pi_pos])⟩

/-! ### 5. Edge-multiplier phase `T_M ε` (`0 ≤ ε ≤ 1/4`) -/

private noncomputable def uM (ε : ℝ) (z : ℂ) : ℂ :=
  (ε : ℂ) * z / (1 - z ^ 2 + (ε : ℂ))

private noncomputable def qM (ε : ℝ) (z : ℂ) : ℂ :=
  (1 + Complex.I * uM ε z) / (1 - Complex.I * uM ε z)

private noncomputable def fM (ε : ℝ) (z : ℂ) : ℂ :=
  Complex.I * Complex.log (qM ε z)

private lemma qM_bounds {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (3 / 4)) :
    1 - z ^ 2 + (ε : ℂ) ≠ 0 ∧
    1 - Complex.I * uM ε z ≠ 0 ∧
    0 < (qM ε z).re ∧
    qM ε z ∈ Complex.slitPlane ∧
    (‖z‖ ≤ 1 / 2 → ‖uM ε z‖ ≤ (2 / 3) * ε ∧ ‖qM ε z - 1‖ ≤ 2 * ε ∧ ‖fM ε z‖ ≤ 4 * ε) := by
  have hz_lt : ‖z‖ < 3 / 4 := mem_ball_zero_iff.mp hz
  have hz2 : ‖z ^ 2‖ < 9 / 16 := by
    rw [norm_pow]; nlinarith only [hz_lt, norm_nonneg z]
  have hden_re : 7 / 16 < (1 - z ^ 2 + (ε : ℂ)).re := by
    have habs : |(z ^ 2).re| ≤ ‖z ^ 2‖ := Complex.abs_re_le_norm _
    have : (1 - z ^ 2 + (ε : ℂ)).re = 1 - (z ^ 2).re + ε := by simp
    linarith only [this, (abs_lt.mp (habs.trans_lt hz2)).2, hε0]
  have hden_norm : 7 / 16 < ‖1 - z ^ 2 + (ε : ℂ)‖ :=
    hden_re.trans_le (Complex.re_le_norm _)
  have hden_ne : 1 - z ^ 2 + (ε : ℂ) ≠ 0 := norm_pos_iff.mp (by linarith only [hden_norm])
  have hu_lt : ‖uM ε z‖ < 3 / 7 := by
    dsimp [uM]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0]
    have hnum : ε * ‖z‖ < (1 / 4) * (3 / 4) := by nlinarith only [hε0, hε1, hz_lt, norm_nonneg z]
    rw [div_lt_iff₀ (by linarith only [hden_norm])]
    nlinarith only [hnum, hden_norm]
  have h1u_lb : 4 / 7 < ‖1 - Complex.I * uM ε z‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (Complex.I * uM ε z)
    rw [norm_one, norm_mul, Complex.norm_I, one_mul] at h1
    linarith only [h1, hu_lt]
  have h1u_ne : 1 - Complex.I * uM ε z ≠ 0 := norm_pos_iff.mp (by linarith only [h1u_lb])
  have hq_re : 0 < (qM ε z).re := by
    set w := Complex.I * uM ε z
    have hw_norm : ‖w‖ < 3 / 7 := by simpa [w, norm_mul, Complex.norm_I] using hu_lt
    have hw_sq : ‖w‖ ^ 2 < 1 := by nlinarith only [hw_norm, norm_nonneg w]
    have h1w : 1 - w ≠ 0 := h1u_ne
    have hdiv_re : ((1 + w) / (1 - w)).re =
        ((1 + w) * starRingEnd ℂ (1 - w)).re / Complex.normSq (1 - w) := by
      rw [Complex.div_re, Complex.normSq_apply]
      have hconj : (1 + w) * starRingEnd ℂ (1 - w) =
          ⟨(1 + w).re * (1 - w).re + (1 + w).im * (1 - w).im,
            (1 + w).im * (1 - w).re - (1 + w).re * (1 - w).im⟩ := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
      rw [hconj]; ring
    have hnum_eq : ((1 + w) * starRingEnd ℂ (1 - w)).re = 1 - Complex.normSq w := by
      simp only [map_sub, map_one]
      simp [Complex.mul_re, Complex.normSq_apply]; ring
    rw [show qM ε z = (1 + w) / (1 - w) from rfl, hdiv_re, hnum_eq]
    have hnsq_pos : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h1w
    have hw_nsq : Complex.normSq w < 1 := by rwa [Complex.normSq_eq_norm_sq]
    exact div_pos (by linarith only [hw_nsq]) hnsq_pos
  have hq_slit : qM ε z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hq_re)
  refine ⟨hden_ne, h1u_ne, hq_re, hq_slit, fun hz12 => ?_⟩
  have hden2 : 3 / 4 ≤ ‖1 - z ^ 2 + (ε : ℂ)‖ := by
    have hz2' : ‖z ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; nlinarith only [hz12, norm_nonneg z]
    have habs : |(z ^ 2).re| ≤ ‖z ^ 2‖ := Complex.abs_re_le_norm _
    have hre2 : 3 / 4 ≤ (1 - z ^ 2 + (ε : ℂ)).re := by
      have : (1 - z ^ 2 + (ε : ℂ)).re = 1 - (z ^ 2).re + ε := by simp
      linarith only [this, (abs_le.mp (habs.trans hz2')).2, hε0]
    exact hre2.trans (Complex.re_le_norm _)
  have hu2 : ‖uM ε z‖ ≤ (2 / 3) * ε := by
    dsimp [uM]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε0, div_le_iff₀ (by linarith only [hden2])]
    calc ε * ‖z‖ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left hz12 hε0
      _ = (2 / 3) * ε * (3 / 4) := by ring
      _ ≤ (2 / 3) * ε * ‖1 - z ^ 2 + (ε : ℂ)‖ := mul_le_mul_of_nonneg_left hden2 (by positivity)
  have h1u2 : 5 / 6 ≤ ‖1 - Complex.I * uM ε z‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (Complex.I * uM ε z)
    rw [norm_one, norm_mul, Complex.norm_I, one_mul] at h1
    have : (2 / 3) * ε ≤ 1 / 6 := by linarith only [hε1]
    linarith only [h1, hu2, this]
  have hq_sub : qM ε z - 1 = 2 * Complex.I * uM ε z / (1 - Complex.I * uM ε z) := by
    dsimp [qM]; field_simp [h1u_ne]; ring
  have hq_bd : ‖qM ε z - 1‖ ≤ 2 * ε := by
    rw [hq_sub, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
      div_le_iff₀ (by linarith only [h1u2])]
    calc 2 * ‖uM ε z‖ ≤ 2 * ((2 / 3) * ε) := by linarith only [hu2]
      _ ≤ 2 * ε * (5 / 6) := by nlinarith only [hε0]
      _ ≤ 2 * ε * ‖1 - Complex.I * uM ε z‖ := mul_le_mul_of_nonneg_left h1u2 (by positivity)
  have hf_bd : ‖fM ε z‖ ≤ 4 * ε := by
    dsimp [fM]
    rw [norm_mul, Complex.norm_I, one_mul]
    have hq_12 : ‖qM ε z - 1‖ ≤ 1 / 2 := hq_bd.trans (by linarith only [hε1])
    have hlog_mv : ‖Complex.log (qM ε z)‖ ≤ 2 * ‖qM ε z - 1‖ := by
      set ζ := qM ε z
      have hζ_mem : ζ ∈ closedBall (1 : ℂ) (1 / 2) := by rwa [mem_closedBall, dist_eq_norm]
      have hder : ∀ x ∈ closedBall (1 : ℂ) (1 / 2),
          HasDerivWithinAt Complex.log x⁻¹ (closedBall (1 : ℂ) (1 / 2)) x := fun x hx => by
        have hx_slit : x ∈ Complex.slitPlane := by
          have hx1 : ‖x - 1‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using mem_closedBall.mp hx
          have habs : |(x - 1).re| ≤ ‖x - 1‖ := Complex.abs_re_le_norm _
          have hxre : 1 / 2 ≤ x.re := by
            have : (x - 1).re = x.re - 1 := by simp
            linarith only [this, (abs_le.mp (habs.trans hx1)).1]
          exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith only [hxre]))
        exact (Complex.hasDerivAt_log hx_slit).hasDerivWithinAt
      have hinv_bd : ∀ x ∈ closedBall (1 : ℂ) (1 / 2), ‖x⁻¹‖ ≤ 2 := fun x hx => by
        have hx1 : ‖x - 1‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using mem_closedBall.mp hx
        have h1 := norm_sub_norm_le (1 : ℂ) (1 - x)
        rw [norm_one, norm_sub_rev, sub_sub_cancel] at h1
        have hlb : 1 / 2 ≤ ‖x‖ := by linarith only [h1, hx1]
        rw [norm_inv]
        calc ‖x‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlb
          _ = 2 := by norm_num
      have hmv := (convex_closedBall (1 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
        hder hinv_bd hζ_mem (mem_closedBall_self (by norm_num))
      simpa [Complex.log_one, dist_eq_norm, norm_sub_rev] using hmv
    exact hlog_mv.trans (by linarith only [hq_bd])
  exact ⟨hu2, hq_bd, hf_bd⟩

lemma virasoro_TM_exists (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4) :
    ∃ T_M : ℂ → ℂ,
      DifferentiableOn ℂ T_M (ball 0 (1 / 4)) ∧
      (∀ w ∈ ball (0 : ℂ) (1 / 4), T_M (starRingEnd ℂ w) = starRingEnd ℂ (T_M w)) ∧
      (∀ w ∈ closedBall (0 : ℂ) (1 / 16), ‖T_M w‖ ≤ 32 / 3 * ε) ∧
      (∀ w ∈ closedBall (0 : ℂ) (1 / 32), ‖deriv T_M w‖ ≤ 1024 / 3 * ε) ∧
      (∀ y : ℝ, 0 < y → y < 1 / 2 →
        y * (T_M ((y ^ 2 : ℝ) : ℂ)).re =
          2 * Complex.arg ((1 + ε : ℂ) * (1 + (Complex.I * (y : ℂ)) ^ 2) /
            (1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ))))) := by
  have hf_diff : DifferentiableOn ℂ (fM ε) (ball 0 (3 / 4)) := fun z hz => by
    obtain ⟨hd1, hd2, _, hq_slit, _⟩ := qM_bounds hε0 hε1 hz
    have hdu : DifferentiableAt ℂ (uM ε) z :=
      (differentiableAt_const _ |>.mul differentiableAt_id).div
        ((differentiableAt_const _ |>.sub (differentiableAt_id.pow 2)).add (differentiableAt_const _)) hd1
    have hdq : DifferentiableAt ℂ (qM ε) z :=
      (differentiableAt_const _ |>.add (differentiableAt_const _ |>.mul hdu)).div
        (differentiableAt_const _ |>.sub (differentiableAt_const _ |>.mul hdu)) hd2
    have hdlog : DifferentiableAt ℂ (fun w => Complex.log (qM ε w)) z :=
      ((Complex.hasDerivAt_log hq_slit).differentiableAt).comp z hdq
    exact (hdlog.const_mul Complex.I).differentiableWithinAt
  have hf_odd : ∀ z ∈ ball (0 : ℂ) (3 / 4), fM ε (-z) = -fM ε z := fun z hz => by
    obtain ⟨_, _, _, hq_slit, _⟩ := qM_bounds hε0 hε1 hz
    have hu_odd : uM ε (-z) = -uM ε z := by dsimp [uM]; ring
    have hq_inv : qM ε (-z) = (qM ε z)⁻¹ := by
      dsimp [qM]; rw [hu_odd, mul_neg, ← sub_eq_add_neg, sub_neg_eq_add, inv_div]
    dsimp [fM]
    rw [hq_inv, Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hq_slit)]
    ring
  have hf_conj : ∀ z ∈ ball (0 : ℂ) (3 / 4), fM ε (starRingEnd ℂ z) = starRingEnd ℂ (fM ε z) := fun z hz => by
    obtain ⟨_, h1u, _, hq_slit, _⟩ := qM_bounds hε0 hε1 hz
    have hu_conj : uM ε (starRingEnd ℂ z) = starRingEnd ℂ (uM ε z) := by
      dsimp [uM]
      simp only [map_div₀, map_mul, map_add, map_sub, map_pow, map_one, Complex.conj_ofReal]
    have hq_conj : qM ε (starRingEnd ℂ z) = starRingEnd ℂ ((qM ε z)⁻¹) := by
      dsimp [qM]
      rw [hu_conj]
      have hconj_num : 1 + Complex.I * starRingEnd ℂ (uM ε z) = starRingEnd ℂ (1 - Complex.I * uM ε z) := by
        simp [Complex.conj_I]
      have hconj_den : 1 - Complex.I * starRingEnd ℂ (uM ε z) = starRingEnd ℂ (1 + Complex.I * uM ε z) := by
        simp only [map_add, map_one, map_mul, Complex.conj_I]; ring
      rw [hconj_num, hconj_den, ← map_div₀, inv_div]
    dsimp [fM]
    have hinv_slit : (qM ε z)⁻¹ ∈ Complex.slitPlane := by
      have hre : 0 < (qM ε z).re := (qM_bounds hε0 hε1 hz).2.2.1
      have hinv_re : 0 < (qM ε z)⁻¹.re := by
        rw [Complex.inv_re]
        exact div_pos hre (Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero hq_slit))
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hinv_re)
    rw [hq_conj, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hinv_slit),
      Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hq_slit)]
    simp only [map_mul, map_neg, Complex.conj_I]
    ring
  have hf_bd : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), ‖fM ε z‖ ≤ 4 * ε := fun z hz => by
    have hz' : z ∈ ball (0 : ℂ) (3 / 4) := closedBall_subset_ball (by norm_num) hz
    exact (qM_bounds hε0 hε1 hz').2.2.2.2 (mem_closedBall_zero_iff.mp hz) |>.2.2
  obtain ⟨T_M, hTM_diff, hTM_conj, hTM_eq, _, _, hTM_bd, hdTM_bd⟩ :=
    odd_holomorphic_factor (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by positivity : 0 ≤ 4 * ε) hf_diff hf_bd hf_odd hf_conj
  have h14 : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  have h16 : (1 / 2 : ℝ) ^ 2 / 4 = 1 / 16 := by norm_num
  have h32 : (1 / 2 : ℝ) ^ 2 / 8 = 1 / 32 := by norm_num
  rw [h14] at hTM_diff hTM_conj
  rw [h16] at hTM_bd
  rw [h32] at hdTM_bd
  refine ⟨T_M, hTM_diff, hTM_conj, fun w hw => ?_, fun w hw => ?_, fun y hy0 hy12 => ?_⟩
  · refine (hTM_bd w hw).trans_eq ?_; ring
  · refine (hdTM_bd w hw).trans_eq ?_; ring
  · have hy_ball : (y : ℂ) ∈ ball (0 : ℂ) (1 / 2) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
      exact hy12
    have hTM_y := hTM_eq (y : ℂ) hy_ball
    have hy_re : y * (T_M ((y ^ 2 : ℝ) : ℂ)).re = (fM ε (y : ℂ)).re := by
      have hre := congrArg Complex.re hTM_y
      simpa [Complex.mul_re, ← Complex.ofReal_pow] using hre.symm
    have hden_pos : 0 < 1 - y ^ 2 + ε := by nlinarith only [hy0, hy12, hε0]
    set u : ℝ := ε * y / (1 - y ^ 2 + ε)
    have hu_eq : uM ε (y : ℂ) = (u : ℂ) := by
      dsimp [uM, u]; push_cast; rfl
    have h1u_pos : 0 < √(1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h1u_ne : (√(1 + u ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1u_pos.ne'
    have hq_polar : qM ε (y : ℂ) = Complex.exp (((2 * Real.arctan u : ℝ) : ℂ) * Complex.I) := by
      have hp1 := polar_re_pos one_pos u
      have hp2 := polar_re_pos one_pos (-u)
      simp only [one_pow, div_one, neg_sq, Real.arctan_neg] at hp1 hp2
      dsimp [qM]
      rw [hu_eq]
      have h_plus : (1 : ℂ) + Complex.I * (u : ℂ) =
          (√(1 + u ^ 2) : ℂ) * Complex.exp ((Real.arctan u : ℂ) * Complex.I) := by
        convert hp1 using 2; ring
      have h_minus : (1 : ℂ) - Complex.I * (u : ℂ) =
          (√(1 + u ^ 2) : ℂ) * Complex.exp (((-Real.arctan u : ℝ) : ℂ) * Complex.I) := by
        convert hp2 using 2; push_cast; ring
      rw [h_plus, h_minus, mul_div_mul_left _ _ h1u_ne, ← Complex.exp_sub]
      congr 1; push_cast; ring
    have h2arc_gt : -π < 2 * Real.arctan u := by
      have := Real.neg_pi_div_two_lt_arctan u; linarith only [Real.pi_pos, this]
    have h2arc_le : 2 * Real.arctan u ≤ π := by
      have := Real.arctan_lt_pi_div_two u; linarith only [Real.pi_pos, this]
    have hf_re : (fM ε (y : ℂ)).re = -2 * Real.arctan u := by
      dsimp [fM]
      rw [hq_polar, Complex.log_exp
        (by simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]; exact h2arc_gt)
        (by simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]; exact h2arc_le)]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    -- Now compute `Complex.arg ((1+ε)(1 - y^2) / ((1 - y^2 + ε) + I ε y))`
    have h_m_eq : (1 + (ε : ℂ)) * (1 + (Complex.I * (y : ℂ)) ^ 2) /
        (1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ))) =
        (((1 + ε) * (1 - y ^ 2) / ((1 - y ^ 2 + ε) ^ 2 + (ε * y) ^ 2) : ℝ) : ℂ) *
          (((1 - y ^ 2 + ε : ℝ) : ℂ) + ((- (ε * y) : ℝ) : ℂ) * Complex.I) := by
      have hden_ne : (1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ))) ≠ 0 := by
        have hI2 : (Complex.I * (y : ℂ)) ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
          rw [mul_pow, Complex.I_sq]; push_cast; ring
        rw [hI2]
        intro h0
        have hre0 := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
          zero_mul, sub_zero, add_zero, Complex.zero_re] at hre0
        linarith only [hre0, hden_pos]
      have hden_sq_ne : (1 - y ^ 2 + ε) ^ 2 + (ε * y) ^ 2 ≠ 0 := by positivity
      have hden_sqC : (((1 - y ^ 2 + ε) ^ 2 + (ε * y) ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hden_sq_ne
      rw [div_eq_iff hden_ne]
      have hI2 : (Complex.I * (y : ℂ)) ^ 2 = -((y ^ 2 : ℝ) : ℂ) := by
        rw [mul_pow, Complex.I_sq]; push_cast; ring
      rw [hI2, Complex.ofReal_div, mul_assoc,
        show (((1 - y ^ 2 + ε : ℝ) : ℂ) + ((- (ε * y) : ℝ) : ℂ) * Complex.I) *
            (1 + -((y ^ 2 : ℝ) : ℂ) + (ε : ℂ) * (1 + Complex.I * (y : ℂ))) =
            (((1 - y ^ 2 + ε) ^ 2 + (ε * y) ^ 2 : ℝ) : ℂ) by
          push_cast; linear_combination -(ε : ℂ) ^ 2 * (y : ℂ) ^ 2 * Complex.I_sq,
        div_mul_cancel₀ _ hden_sqC]
      push_cast; ring
    have hpref_pos : 0 < (1 + ε) * (1 - y ^ 2) / ((1 - y ^ 2 + ε) ^ 2 + (ε * y) ^ 2) := by
      have h1y2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy12]
      positivity
    have hpolar_m := polar_re_pos hden_pos (-(ε * y))
    have hrad_pos : 0 < √((1 - y ^ 2 + ε) ^ 2 + (-(ε * y)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have harg_m : Complex.arg ((1 + (ε : ℂ)) * (1 + (Complex.I * (y : ℂ)) ^ 2) /
        (1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)))) = -Real.arctan u := by
      rw [h_m_eq, hpolar_m, ← mul_assoc, ← Complex.ofReal_mul,
        Complex.arg_real_mul _ (mul_pos hpref_pos hrad_pos), Complex.exp_mul_I]
      rw [Complex.arg_cos_add_sin_mul_I
        ⟨by linarith only [Real.pi_pos, Real.neg_pi_div_two_lt_arctan (-(ε * y) / (1 - y ^ 2 + ε))],
        by linarith only [Real.pi_pos, Real.arctan_lt_pi_div_two (-(ε * y) / (1 - y ^ 2 + ε))]⟩]
      rw [neg_div, Real.arctan_neg]
    rw [hy_re, hf_re, harg_m]
    ring

/-! ### 6. Combined Virasoro shift `virasoroPsiEps` and `virasoroPsiEps_spec` -/

structure PsiBasePack where
  rY : ℝ
  hrY_pos : 0 < rY
  sY : ℝ
  hsY_pos : 0 < sY
  hsY_le : sY ≤ 1 / (10 * π)
  rC : ℂ → ℂ
  Y0 : ℂ → ℂ
  hrC_diff : DifferentiableOn ℂ rC (ball 0 rY)
  hY0_diff : DifferentiableOn ℂ Y0 (ball 0 rY)
  hY0_conj : ∀ τ ∈ ball (0 : ℂ) rY, Y0 (starRingEnd ℂ τ) = starRingEnd ℂ (Y0 τ)
  hY0_pos : ∀ τ ∈ ball (0 : ℂ) rY, 0 < (Y0 τ).re ∧ Y0 τ ∈ Complex.slitPlane
  hY0_0 : Y0 0 = (slitY : ℂ)
  hd_Y0 : deriv Y0 0 = ((slitY * slitB : ℝ) : ℂ)
  hY0_band : ∀ τ : ℝ, 0 < τ → τ < rY →
    0 < (rC (τ : ℂ)).re ∧ (rC (τ : ℂ)).re < sY ∧
    (rC (τ : ℂ)).im = 0 ∧
    tauPhase (xiStar + (rC (τ : ℂ)).re) = τ ∧
    lowerYVal (xiStar + (rC (τ : ℂ)).re) ∈ Ioo (0 : ℝ) 1 ∧
    τ * (Y0 (τ : ℂ)).re = lowerYVal (xiStar + (rC (τ : ℂ)).re) ^ 2
  rTout : ℝ
  yTout : ℝ
  Mout : ℝ
  hrTout_pos : 0 < rTout
  hyTout_pos : 0 < yTout
  hy2_le : yTout ^ 2 ≤ rTout / 4
  hyTout_half : yTout ≤ 1 / 2
  hMout_nn : 0 ≤ Mout
  Tout : ℂ → ℂ
  hTout_diff : DifferentiableOn ℂ Tout (ball 0 rTout)
  hTout_conj : ∀ w ∈ ball (0 : ℂ) rTout, Tout (starRingEnd ℂ w) = starRingEnd ℂ (Tout w)
  hTout_0 : Tout 0 = (g1Vir : ℂ)
  hdTout_0 : deriv Tout 0 = ((-g3Vir : ℝ) : ℂ)
  hTout_bd : ∀ w ∈ closedBall (0 : ℂ) (rTout / 4), ‖Tout w‖ ≤ Mout ∧ ‖deriv Tout w‖ ≤ Mout
  hTout_real : ∀ y : ℝ, 0 < y → y < yTout →
    y * (Tout ((y ^ 2 : ℝ) : ℂ)).re = thetaOut y ∧ |thetaOut y| < π

lemma virasoro_psi_base_nonempty : Nonempty PsiBasePack := by
  obtain ⟨rY, hrY_pos, sY, hsY_pos, hsY_le, rC, Y0, hrC_diff, hY0_diff, hY0_conj, hY0_pos,
    hY0_0, hd_Y0, hY0_band⟩ := virasoro_Y0_exists
  obtain ⟨rTout, yTout, Mout, hrTout_pos, hyTout_pos, hy2_le, hyTout_half, hMout_nn,
    Tout, hTout_diff, hTout_conj, hTout_0, hdTout_0, hTout_bd, hTout_real⟩ := virasoro_Tout_exists
  exact ⟨⟨rY, hrY_pos, sY, hsY_pos, hsY_le, rC, Y0, hrC_diff, hY0_diff, hY0_conj, hY0_pos,
    hY0_0, hd_Y0, hY0_band, rTout, yTout, Mout, hrTout_pos, hyTout_pos, hy2_le, hyTout_half,
    hMout_nn, Tout, hTout_diff, hTout_conj, hTout_0, hdTout_0, hTout_bd, hTout_real⟩⟩

noncomputable def psiBase : PsiBasePack := Classical.choice virasoro_psi_base_nonempty

/-- Edge-multiplier odd factor `T_M(ε, w)` (`0 ≤ ε ≤ 1/4`). -/
noncomputable def virasoroTM (ε : ℝ) (w : ℂ) : ℂ :=
  if h : 0 ≤ ε ∧ ε ≤ 1 / 4 then (Classical.choose (virasoro_TM_exists ε h.1 h.2)) w else 0

/-- Virasoro fold-chart phase shift `ψ_ε(a)` (`ε ∈ [0, 1/4]`) for `cts:cauchy-dual` (1) and `cts:phic-exp`. -/
noncomputable def virasoroPsiEps (ε : ℝ) (a : ℂ) : ℂ :=
  if 0 ≤ ε ∧ ε ≤ 1 / 4 then
    (psiBase.Y0 (-a)) ^ ((1 / 2 : ℝ) : ℂ) / ((2 * betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      (psiBase.Tout (-a * psiBase.Y0 (-a)) + virasoroTM ε (-a * psiBase.Y0 (-a)))
  else 0

/-- Complete analytic, jet, and real-band phase-matching specification of `virasoroPsiEps`
for `cts:cauchy-dual` (1) and `cts:phic-exp`. -/
theorem virasoroPsiEps_spec :
    ∃ ρ_ψ r_ψ M_ψ C_ψ r_τ : ℝ,
      0 < r_ψ ∧ r_ψ < ρ_ψ ∧ 0 ≤ M_ψ ∧ 0 ≤ C_ψ ∧ 0 < r_τ ∧ r_τ ≤ 1 / (10 * π) ∧
      (∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 4 →
        DifferentiableOn ℂ (virasoroPsiEps ε) (ball 0 ρ_ψ) ∧
        (∀ a ∈ ball (0 : ℂ) ρ_ψ, virasoroPsiEps ε (starRingEnd ℂ a) = starRingEnd ℂ (virasoroPsiEps ε a)) ∧
        (∀ a ∈ closedBall (0 : ℂ) r_ψ, ‖virasoroPsiEps ε a‖ ≤ M_ψ ∧ ‖deriv (virasoroPsiEps ε) a‖ ≤ M_ψ) ∧
        |(virasoroPsiEps ε 0).re - (c0Star / cStar) / betaTip| ≤ C_ψ * ε ∧
        |(deriv (virasoroPsiEps ε) 0).re - gamma0| ≤ C_ψ * ε) ∧
      (∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 4 →
        ∀ x : ℝ, xiStar < x → tauPhase x < r_ψ →
          x < xiStar + r_τ ∧
          lowerYVal x ∈ Ioo (0 : ℝ) 1 ∧
          2 * betaTip ^ (3 / 2 : ℝ) * √(tauPhase x) * (virasoroPsiEps ε ((-(tauPhase x) : ℝ) : ℂ)).re =
            Complex.arg (Gout (Complex.I * (lowerYVal x : ℂ))) +
              2 * Complex.arg ((1 + ε : ℂ) * (1 + (Complex.I * (lowerYVal x : ℂ)) ^ 2) /
                (1 + (Complex.I * (lowerYVal x : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (lowerYVal x : ℂ))))) := by
  let wRad : ℝ := min (psiBase.rTout / 4) (1 / 32)
  have hwRad_pos : 0 < wRad := lt_min (div_pos psiBase.hrTout_pos (by norm_num)) (by norm_num)
  let g0 : ℂ → ℂ := fun a => (psiBase.Y0 (-a)) ^ ((1 / 2 : ℝ) : ℂ) / ((2 * betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ)
  let argW : ℂ → ℂ := fun a => -a * psiBase.Y0 (-a)
  let psiOut : ℂ → ℂ := fun a => g0 a * psiBase.Tout (argW a)
  have hargW0 : argW 0 = 0 := by simp [argW]
  have hargW_cont : ContinuousAt argW 0 := by
    have hY0c : ContinuousAt psiBase.Y0 (-0) := by
      simpa using (psiBase.hY0_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self psiBase.hrY_pos))).continuousAt
    exact (continuousAt_id.neg).mul (hY0c.comp continuous_neg.continuousAt)
  have hev_argW : ∀ᶠ a : ℂ in 𝓝 0, ‖argW a‖ < wRad := by
    have : Tendsto argW (𝓝 0) (𝓝 0) := by simpa [hargW0] using hargW_cont.tendsto
    have hball : ∀ᶠ a : ℂ in 𝓝 0, argW a ∈ ball (0 : ℂ) wRad :=
      this.eventually (Metric.ball_mem_nhds (0 : ℂ) hwRad_pos)
    exact hball.mono fun _ h => by simpa [Metric.mem_ball, dist_eq_norm] using h
  obtain ⟨rA, hrA_pos, hrA_ball⟩ := Metric.mem_nhds_iff.mp hev_argW
  let rHalf : ℝ := min (psiBase.rY / 2) rA
  have hrHalf_pos : 0 < rHalf := lt_min (half_pos psiBase.hrY_pos) hrA_pos
  have hY0_bdd : BddAbove ((fun τ => ‖psiBase.Y0 τ‖) '' closedBall (0 : ℂ) rHalf) :=
    ((isCompact_closedBall (0 : ℂ) rHalf).image_of_continuousOn
      ((psiBase.hY0_diff.mono (closedBall_subset_ball (by dsimp [rHalf]; linarith only [min_le_left (psiBase.rY / 2) rA, psiBase.hrY_pos]))).continuousOn.norm)).bddAbove
  set MY0 : ℝ := max (sSup ((fun τ => ‖psiBase.Y0 τ‖) '' closedBall (0 : ℂ) rHalf)) 1
  have hMY0_pos : 0 < MY0 := by positivity
  let ρ_ψ : ℝ := min rHalf (psiBase.yTout ^ 2 / (2 * MY0))
  have hρψ_pos : 0 < ρ_ψ := lt_min hrHalf_pos (by have := psiBase.hyTout_pos; positivity)
  let r_ψ : ℝ := ρ_ψ / 2
  have hrψ_pos : 0 < r_ψ := half_pos hρψ_pos
  have hrψ_lt : r_ψ < ρ_ψ := half_lt_self hρψ_pos
  -- Bound `‖g0‖, ‖deriv g0‖, ‖deriv argW‖, ‖psiOut‖, ‖deriv psiOut‖` on `closedBall 0 r_ψ`
  have hg0_diff : DifferentiableOn ℂ g0 (ball 0 ρ_ψ) := fun a ha => by
    have ha' : -a ∈ ball (0 : ℂ) psiBase.rY := by
      rw [mem_ball_zero_iff, norm_neg]
      exact (mem_ball_zero_iff.mp ha).trans_le ((min_le_left _ _).trans (min_le_left _ _) |>.trans (half_le_self psiBase.hrY_pos.le))
    have hdY := ((psiBase.hY0_diff.differentiableAt (isOpen_ball.mem_nhds ha')).comp a (hasDerivAt_neg a).differentiableAt).hasDerivAt
    have hdPow := hdY.cpow_const (c := ((1 / 2 : ℝ) : ℂ)) (psiBase.hY0_pos _ ha').2
    exact (hdPow.div_const _).differentiableAt.differentiableWithinAt
  have hargW_diff : DifferentiableOn ℂ argW (ball 0 ρ_ψ) := fun a ha => by
    have ha' : -a ∈ ball (0 : ℂ) psiBase.rY := by
      rw [mem_ball_zero_iff, norm_neg]
      exact (mem_ball_zero_iff.mp ha).trans_le ((min_le_left _ _).trans (min_le_left _ _) |>.trans (half_le_self psiBase.hrY_pos.le))
    have hdY := (psiBase.hY0_diff.differentiableAt (isOpen_ball.mem_nhds ha')).comp a (hasDerivAt_neg a).differentiableAt
    exact (differentiableAt_id.neg.mul hdY).differentiableWithinAt
  have hpsiOut_diff : DifferentiableOn ℂ psiOut (ball 0 ρ_ψ) := fun a ha => by
    have ha_rA : a ∈ ball (0 : ℂ) rA := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) ha
    have haw : argW a ∈ ball (0 : ℂ) psiBase.rTout := by
      have h1 : ‖argW a‖ < wRad := hrA_ball ha_rA
      exact mem_ball_zero_iff.mpr (h1.trans_le ((min_le_left _ _).trans (div_le_self psiBase.hrTout_pos.le (by norm_num))))
    have hdT := (psiBase.hTout_diff.differentiableAt (isOpen_ball.mem_nhds haw)).comp a (hargW_diff.differentiableAt (isOpen_ball.mem_nhds ha))
    exact ((hg0_diff.differentiableAt (isOpen_ball.mem_nhds ha)).mul hdT).differentiableWithinAt
  have hcomp_bdd : ∀ {F : ℂ → ℂ}, DifferentiableOn ℂ F (ball 0 ρ_ψ) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ closedBall (0 : ℂ) r_ψ, ‖F a‖ ≤ B := fun {F} hF => by
    have hb : BddAbove ((fun a => ‖F a‖) '' closedBall (0 : ℂ) r_ψ) :=
      ((isCompact_closedBall (0 : ℂ) r_ψ).image_of_continuousOn
        ((hF.mono (closedBall_subset_ball hrψ_lt)).continuousOn.norm)).bddAbove
    refine ⟨max (sSup ((fun a => ‖F a‖) '' closedBall (0 : ℂ) r_ψ)) 0, le_max_right _ _, fun a ha =>
      (le_csSup hb ⟨a, ha, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨Mg0, hMg0, hMg0_bd⟩ := hcomp_bdd hg0_diff
  obtain ⟨Mg0', hMg0', hMg0'_bd⟩ := hcomp_bdd (hg0_diff.deriv isOpen_ball)
  obtain ⟨Marg', hMarg', hMarg'_bd⟩ := hcomp_bdd (hargW_diff.deriv isOpen_ball)
  obtain ⟨MpOut, hMpOut, hMpOut_bd⟩ := hcomp_bdd hpsiOut_diff
  obtain ⟨MpOut', hMpOut', hMpOut'_bd⟩ := hcomp_bdd (hpsiOut_diff.deriv isOpen_ball)
  let CM : ℝ := max (Mg0 * (32 / 3)) (Mg0' * (32 / 3) + Mg0 * (Marg' * (1024 / 3)))
  have hCM_nn : 0 ≤ CM := le_max_of_le_left (by positivity)
  let M_ψ : ℝ := max MpOut MpOut' + CM * (1 / 4)
  have hMψ_nn : 0 ≤ M_ψ := by positivity
  -- Exact value and derivative of `psiOut` at `0`
  have hg0_0 : g0 0 = ((√slitY / (2 * betaTip ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
    dsimp [g0]
    rw [neg_zero, psiBase.hY0_0]
    have hYpos : 0 < slitY := by unfold slitY; positivity
    rw [← Complex.ofReal_cpow hYpos.le, Real.sqrt_eq_rpow]
    push_cast; rfl
  have hdg0_0 : deriv g0 0 = ((-(√slitY / (2 * betaTip ^ (3 / 2 : ℝ)) * (slitB / 2)) : ℝ) : ℂ) := by
    have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) psiBase.rY := mem_ball_self psiBase.hrY_pos
    have hdY : HasDerivAt (fun a => psiBase.Y0 (-a)) (-((slitY * slitB : ℝ) : ℂ)) 0 := by
      have h1 : HasDerivAt psiBase.Y0 (deriv psiBase.Y0 0) 0 :=
        (psiBase.hY0_diff.differentiableAt (isOpen_ball.mem_nhds h0_mem)).hasDerivAt
      rw [psiBase.hd_Y0] at h1
      have h2 := h1.comp_of_eq (0 : ℂ) (hasDerivAt_neg (0 : ℂ)) neg_zero.symm
      simpa [Function.comp_def] using h2
    have hY_slit : psiBase.Y0 (-0) ∈ Complex.slitPlane := by
      rw [neg_zero]; exact (psiBase.hY0_pos 0 h0_mem).2
    have hpow := hdY.cpow_const hY_slit (c := ((1 / 2 : ℝ) : ℂ))
    have hg0d := hpow.div_const ((2 * betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ)
    rw [hg0d.deriv, neg_zero, psiBase.hY0_0]
    have hYpos : 0 < slitY := by unfold slitY; positivity
    have hsY_ne : √slitY ≠ 0 := (Real.sqrt_pos.mpr hYpos).ne'
    have hbt_pos : 0 < betaTip ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos betaTip_pos _
    have hcp : (slitY : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - 1) = (((√slitY)⁻¹ : ℝ) : ℂ) := by
      have hm : ((1 / 2 : ℝ) : ℂ) - 1 = ((- (1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [hm, ← Complex.ofReal_cpow hYpos.le, Real.rpow_neg hYpos.le, ← Real.sqrt_eq_rpow,
        Complex.ofReal_inv]
    rw [hcp]
    have hs_inv : (√slitY)⁻¹ * slitY = √slitY := by
      field_simp [hsY_ne]; rw [Real.sq_sqrt hYpos.le]
    push_cast
    have : (1 / 2 : ℂ) * ((√slitY)⁻¹ : ℂ) * -((slitY : ℂ) * (slitB : ℂ)) / (2 * ((betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
        -((√slitY : ℂ) / (2 * ((betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * ((slitB : ℂ) / 2)) := by
      have h1 : ((√slitY)⁻¹ : ℂ) * (slitY : ℂ) = (√slitY : ℂ) := by exact_mod_cast hs_inv
      calc (1 / 2 : ℂ) * ((√slitY)⁻¹ : ℂ) * -((slitY : ℂ) * (slitB : ℂ)) / (2 * ((betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ))
          = -(1 / 2 * (((√slitY)⁻¹ : ℂ) * (slitY : ℂ)) * (slitB : ℂ) / (2 * ((betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by ring
        _ = -(1 / 2 * (√slitY : ℂ) * (slitB : ℂ) / (2 * ((betaTip ^ (3 / 2 : ℝ) : ℝ) : ℂ))) := by rw [h1]
        _ = _ := by ring
    exact this
  have hpsiOut0 : psiOut 0 = (((c0Star / cStar) / betaTip : ℝ) : ℂ) := by
    dsimp [psiOut]
    rw [hg0_0, hargW0, psiBase.hTout_0, ← Complex.ofReal_mul, psi0_const_eq_c0_div_cStar_betaTip]
  have hd_psiOut0 : deriv psiOut 0 = (gamma0 : ℂ) := by
    have h0_mem : (0 : ℂ) ∈ ball (0 : ℂ) ρ_ψ := mem_ball_self hρψ_pos
    have hdg0 : HasDerivAt g0 (deriv g0 0) 0 :=
      (hg0_diff.differentiableAt (isOpen_ball.mem_nhds h0_mem)).hasDerivAt
    have hd_arg : HasDerivAt argW (-(slitY : ℂ)) 0 := by
      have h0Y : (0 : ℂ) ∈ ball (0 : ℂ) psiBase.rY := mem_ball_self psiBase.hrY_pos
      have hdY := ((psiBase.hY0_diff.differentiableAt (isOpen_ball.mem_nhds h0Y)).hasDerivAt).comp_of_eq
        (0 : ℂ) (hasDerivAt_neg (0 : ℂ)) neg_zero.symm
      have h := (hasDerivAt_neg (0 : ℂ)).mul hdY
      simpa only [argW, Function.comp_def, Pi.mul_def, neg_zero, psiBase.hY0_0, one_mul, neg_one_mul,
        zero_mul, add_zero] using h
    have hdT : HasDerivAt psiBase.Tout ((-g3Vir : ℝ) : ℂ) (argW 0) := by
      rw [hargW0, ← psiBase.hdTout_0]
      exact (psiBase.hTout_diff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self psiBase.hrTout_pos))).hasDerivAt
    have hdp : HasDerivAt psiOut (deriv g0 0 * psiBase.Tout (argW 0) + g0 0 * ((-g3Vir : ℝ) : ℂ) * -(slitY : ℂ)) 0 := by
      have hm : HasDerivAt (fun a => g0 a * psiBase.Tout (argW a))
          (deriv g0 0 * psiBase.Tout (argW 0) + g0 0 * ((-g3Vir : ℝ) : ℂ) * -(slitY : ℂ)) 0 := by
        simpa only [Function.comp_def, Pi.mul_def, mul_assoc] using hdg0.mul (hdT.comp 0 hd_arg)
      exact hm
    rw [hdp.deriv, hdg0_0, hg0_0, hargW0, psiBase.hTout_0]
    rw [show ((- (√slitY / (2 * betaTip ^ (3 / 2 : ℝ)) * (slitB / 2)) : ℝ) : ℂ) * (g1Vir : ℂ) +
        ((√slitY / (2 * betaTip ^ (3 / 2 : ℝ)) : ℝ) : ℂ) * ((-g3Vir : ℝ) : ℂ) * -(slitY : ℂ) =
        ((√slitY / (2 * betaTip ^ (3 / 2 : ℝ)) * (slitY * g3Vir - slitB / 2 * g1Vir) : ℝ) : ℂ) by
      push_cast; ring]
    rw [psi0_deriv_eq_gamma0]
  refine ⟨ρ_ψ, r_ψ, M_ψ, CM, psiBase.sY, hrψ_pos, hrψ_lt, hMψ_nn, hCM_nn, psiBase.hsY_pos, psiBase.hsY_le,
    fun ε hε0 hε1 => ?_, fun ε hε0 hε1 x hx_gt htau_lt => ?_⟩
  · have hTM := Classical.choose_spec (virasoro_TM_exists ε hε0 hε1)
    set TM := Classical.choose (virasoro_TM_exists ε hε0 hε1)
    obtain ⟨hTM_diff, hTM_conj, hTM_bd, hdTM_bd, _⟩ := hTM
    have h_eq : ∀ a : ℂ, virasoroPsiEps ε a = psiOut a + g0 a * TM (argW a) := fun a => by
      dsimp [virasoroPsiEps, virasoroTM, psiOut, g0, argW]
      simp only [hε0, hε1, and_self, ↓reduceIte, ↓reduceDIte]
      ring
    have hTM_comp_diff : DifferentiableOn ℂ (fun a => g0 a * TM (argW a)) (ball 0 ρ_ψ) := fun a ha => by
      have ha_rA : a ∈ ball (0 : ℂ) rA := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) ha
      have haw : argW a ∈ ball (0 : ℂ) (1 / 4) := by
        have h1 : ‖argW a‖ < wRad := hrA_ball ha_rA
        exact mem_ball_zero_iff.mpr (h1.trans_le ((min_le_right _ _).trans (by norm_num)))
      have hdTM := (hTM_diff.differentiableAt (isOpen_ball.mem_nhds haw)).comp a (hargW_diff.differentiableAt (isOpen_ball.mem_nhds ha))
      exact ((hg0_diff.differentiableAt (isOpen_ball.mem_nhds ha)).mul hdTM).differentiableWithinAt
    have hψ_diff : DifferentiableOn ℂ (virasoroPsiEps ε) (ball 0 ρ_ψ) := fun a ha => by
      have h1 : virasoroPsiEps ε = fun z => psiOut z + g0 z * TM (argW z) := funext h_eq
      rw [h1]
      exact ((hpsiOut_diff.differentiableAt (isOpen_ball.mem_nhds ha)).add
        (hTM_comp_diff.differentiableAt (isOpen_ball.mem_nhds ha))).differentiableWithinAt
    have hψ_conj : ∀ a ∈ ball (0 : ℂ) ρ_ψ,
        virasoroPsiEps ε (starRingEnd ℂ a) = starRingEnd ℂ (virasoroPsiEps ε a) := fun a ha => by
      have haY : -a ∈ ball (0 : ℂ) psiBase.rY := by
        rw [mem_ball_zero_iff, norm_neg]
        exact (mem_ball_zero_iff.mp ha).trans_le ((min_le_left _ _).trans (min_le_left _ _) |>.trans (half_le_self psiBase.hrY_pos.le))
      have ha_rA : a ∈ ball (0 : ℂ) rA := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) ha
      have haw_rad : ‖argW a‖ < wRad := hrA_ball ha_rA
      have hY_conj : psiBase.Y0 (-starRingEnd ℂ a) = starRingEnd ℂ (psiBase.Y0 (-a)) := by
        rw [show -starRingEnd ℂ a = starRingEnd ℂ (-a) by simp]
        exact psiBase.hY0_conj _ haY
      have hg0_conj : g0 (starRingEnd ℂ a) = starRingEnd ℂ (g0 a) := by
        dsimp [g0]
        rw [hY_conj, Complex.conj_cpow (psiBase.Y0 (-a)) ((1 / 2 : ℝ) : ℂ)
          (Complex.slitPlane_arg_ne_pi (psiBase.hY0_pos _ haY).2)]
        have h12 : starRingEnd ℂ ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
        rw [h12]
        simp only [map_div₀, Complex.conj_ofReal]
      have hargW_conj : argW (starRingEnd ℂ a) = starRingEnd ℂ (argW a) := by
        dsimp [argW]; rw [hY_conj]; simp only [map_mul, map_neg]
      have hTout_conj : psiBase.Tout (argW (starRingEnd ℂ a)) = starRingEnd ℂ (psiBase.Tout (argW a)) := by
        rw [hargW_conj]
        exact psiBase.hTout_conj _ (mem_ball_zero_iff.mpr (haw_rad.trans_le ((min_le_left _ _).trans (div_le_self psiBase.hrTout_pos.le (by norm_num)))))
      have hTM_c : TM (argW (starRingEnd ℂ a)) = starRingEnd ℂ (TM (argW a)) := by
        rw [hargW_conj]
        exact hTM_conj _ (mem_ball_zero_iff.mpr (haw_rad.trans_le ((min_le_right _ _).trans (by norm_num))))
      rw [h_eq, h_eq]
      dsimp [psiOut]
      rw [hg0_conj, hTout_conj, hTM_c]
      simp only [map_add, map_mul]
    have hM_part : ∀ a ∈ closedBall (0 : ℂ) r_ψ,
        ‖g0 a * TM (argW a)‖ ≤ CM * ε ∧ ‖deriv (fun z => g0 z * TM (argW z)) a‖ ≤ CM * ε := fun a ha => by
      have ha_ball : a ∈ ball (0 : ℂ) ρ_ψ := closedBall_subset_ball hrψ_lt ha
      have ha_rA : a ∈ ball (0 : ℂ) rA := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) ha_ball
      have haw_rad : ‖argW a‖ < wRad := hrA_ball ha_rA
      have haw16 : argW a ∈ closedBall (0 : ℂ) (1 / 16) :=
        mem_closedBall_zero_iff.mpr (haw_rad.le.trans ((min_le_right _ _).trans (by norm_num)))
      have haw32 : argW a ∈ closedBall (0 : ℂ) (1 / 32) :=
        mem_closedBall_zero_iff.mpr (haw_rad.le.trans (min_le_right _ _))
      have haw14 : argW a ∈ ball (0 : ℂ) (1 / 4) :=
        mem_ball_zero_iff.mpr (haw_rad.trans_le ((min_le_right _ _).trans (by norm_num)))
      have hb1 : ‖g0 a * TM (argW a)‖ ≤ CM * ε := by
        rw [norm_mul]
        calc ‖g0 a‖ * ‖TM (argW a)‖ ≤ Mg0 * (32 / 3 * ε) :=
              mul_le_mul (hMg0_bd a ha) (hTM_bd _ haw16) (norm_nonneg _) hMg0
          _ = (Mg0 * (32 / 3)) * ε := by ring
          _ ≤ CM * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε0
      have hb2 : ‖deriv (fun z => g0 z * TM (argW z)) a‖ ≤ CM * ε := by
        have hdg : HasDerivAt g0 (deriv g0 a) a :=
          (hg0_diff.differentiableAt (isOpen_ball.mem_nhds ha_ball)).hasDerivAt
        have hda : HasDerivAt argW (deriv argW a) a :=
          (hargW_diff.differentiableAt (isOpen_ball.mem_nhds ha_ball)).hasDerivAt
        have hdTM := ((hTM_diff.differentiableAt (isOpen_ball.mem_nhds haw14)).hasDerivAt).comp a hda
        have hprod : HasDerivAt (fun z => g0 z * TM (argW z))
            (deriv g0 a * TM (argW a) + g0 a * (deriv TM (argW a) * deriv argW a)) a :=
          hdg.mul hdTM
        rw [hprod.deriv]
        calc ‖deriv g0 a * TM (argW a) + g0 a * (deriv TM (argW a) * deriv argW a)‖
            ≤ ‖deriv g0 a‖ * ‖TM (argW a)‖ + ‖g0 a‖ * (‖deriv TM (argW a)‖ * ‖deriv argW a‖) := by
              exact (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le (by rw [norm_mul, norm_mul]))
          _ ≤ Mg0' * (32 / 3 * ε) + Mg0 * ((1024 / 3 * ε) * Marg') := by
              gcongr
              · exact hMg0'_bd a ha
              · exact hTM_bd _ haw16
              · exact hMg0_bd a ha
              · exact hdTM_bd _ haw32
              · exact hMarg'_bd a ha
          _ = (Mg0' * (32 / 3) + Mg0 * (Marg' * (1024 / 3))) * ε := by ring
          _ ≤ CM * ε := mul_le_mul_of_nonneg_right (le_max_right _ _) hε0
      exact ⟨hb1, hb2⟩
    have hψ_bd : ∀ a ∈ closedBall (0 : ℂ) r_ψ, ‖virasoroPsiEps ε a‖ ≤ M_ψ ∧ ‖deriv (virasoroPsiEps ε) a‖ ≤ M_ψ := fun a ha => by
      obtain ⟨h1, h2⟩ := hM_part a ha
      have ha_ball : a ∈ ball (0 : ℂ) ρ_ψ := closedBall_subset_ball hrψ_lt ha
      have hcM14 : CM * ε ≤ CM * (1 / 4) := mul_le_mul_of_nonneg_left hε1 hCM_nn
      refine ⟨?_, ?_⟩
      · rw [h_eq]
        calc ‖psiOut a + g0 a * TM (argW a)‖ ≤ ‖psiOut a‖ + ‖g0 a * TM (argW a)‖ := norm_add_le _ _
          _ ≤ MpOut + CM * ε := add_le_add (hMpOut_bd a ha) h1
          _ ≤ max MpOut MpOut' + CM * (1 / 4) := add_le_add (le_max_left _ _) hcM14
      · have hdp1 : HasDerivAt psiOut (deriv psiOut a) a :=
          (hpsiOut_diff.differentiableAt (isOpen_ball.mem_nhds ha_ball)).hasDerivAt
        have hdp2 : HasDerivAt (fun z => g0 z * TM (argW z)) (deriv (fun z => g0 z * TM (argW z)) a) a :=
          (hTM_comp_diff.differentiableAt (isOpen_ball.mem_nhds ha_ball)).hasDerivAt
        have hder_eq : deriv (virasoroPsiEps ε) a = deriv psiOut a + deriv (fun z => g0 z * TM (argW z)) a := by
          have : virasoroPsiEps ε = fun z => psiOut z + g0 z * TM (argW z) := funext h_eq
          rw [this]
          exact (hdp1.add hdp2).deriv
        rw [hder_eq]
        calc ‖deriv psiOut a + deriv (fun z => g0 z * TM (argW z)) a‖
            ≤ ‖deriv psiOut a‖ + ‖deriv (fun z => g0 z * TM (argW z)) a‖ := norm_add_le _ _
          _ ≤ MpOut' + CM * ε := add_le_add (hMpOut'_bd a ha) h2
          _ ≤ max MpOut MpOut' + CM * (1 / 4) := add_le_add (le_max_right _ _) hcM14
    have h0_mem : (0 : ℂ) ∈ closedBall (0 : ℂ) r_ψ := mem_closedBall_self hrψ_pos.le
    have h0_val : |(virasoroPsiEps ε 0).re - (c0Star / cStar) / betaTip| ≤ CM * ε := by
      have hre : (virasoroPsiEps ε 0).re - (c0Star / cStar) / betaTip = (g0 0 * TM (argW 0)).re := by
        rw [h_eq, Complex.add_re, hpsiOut0, Complex.ofReal_re]; ring
      rw [hre]
      exact (Complex.abs_re_le_norm _).trans (hM_part 0 h0_mem).1
    have h0_der : |(deriv (virasoroPsiEps ε) 0).re - gamma0| ≤ CM * ε := by
      have h0_ball : (0 : ℂ) ∈ ball (0 : ℂ) ρ_ψ := mem_ball_self hρψ_pos
      have hdp1 : HasDerivAt psiOut (deriv psiOut 0) 0 :=
        (hpsiOut_diff.differentiableAt (isOpen_ball.mem_nhds h0_ball)).hasDerivAt
      have hdp2 : HasDerivAt (fun z => g0 z * TM (argW z)) (deriv (fun z => g0 z * TM (argW z)) 0) 0 :=
        (hTM_comp_diff.differentiableAt (isOpen_ball.mem_nhds h0_ball)).hasDerivAt
      have hder_eq : deriv (virasoroPsiEps ε) 0 = deriv psiOut 0 + deriv (fun z => g0 z * TM (argW z)) 0 := by
        have : virasoroPsiEps ε = fun z => psiOut z + g0 z * TM (argW z) := funext h_eq
        rw [this]
        exact (hdp1.add hdp2).deriv
      have hre : (deriv (virasoroPsiEps ε) 0).re - gamma0 = (deriv (fun z => g0 z * TM (argW z)) 0).re := by
        rw [hder_eq, Complex.add_re, hd_psiOut0, Complex.ofReal_re]; ring
      rw [hre]
      exact (Complex.abs_re_le_norm _).trans (hM_part 0 h0_mem).2
    exact ⟨hψ_diff, hψ_conj, hψ_bd, h0_val, h0_der⟩
  · set τ : ℝ := tauPhase x
    have hτ_pos : 0 < τ := by
      dsimp [τ]; unfold tauPhase
      have hcum : 0 < cumulN x := by
        have h1 := cumulN_strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx_gt.le) hx_gt
        rwa [cumulN_xiStar] at h1
      exact Real.rpow_pos_of_pos (div_pos hcum kTip_pos) _
    have hτ_rY : τ < psiBase.rY := by
      have h1 : ρ_ψ ≤ psiBase.rY / 2 := (min_le_left _ _).trans (min_le_left _ _)
      linarith only [htau_lt, hrψ_lt, h1, psiBase.hrY_pos]
    obtain ⟨hr_pos, hr_sY, _, htau_r, _, hτY⟩ := psiBase.hY0_band τ hτ_pos hτ_rY
    set r : ℝ := (psiBase.rC (τ : ℂ)).re
    have hx_eq : x = xiStar + r := by
      have hx_mem : x ∈ Ici xiStar := Set.mem_Ici.mpr hx_gt.le
      have hr_mem : xiStar + r ∈ Ici xiStar := Set.mem_Ici.mpr (by linarith only [hr_pos])
      exact tauPhase_strictMonoOn.injOn hx_mem hr_mem (htau_r.symm)
    have hx_lt_sY : x < xiStar + psiBase.sY := by linarith only [hx_eq, hr_sY]
    have hτ_ball : (τ : ℂ) ∈ ball (0 : ℂ) psiBase.rY := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ_pos]; exact hτ_rY
    have hY0_im : (psiBase.Y0 (τ : ℂ)).im = 0 := by
      have h := psiBase.hY0_conj (τ : ℂ) hτ_ball
      simp only [Complex.conj_ofReal] at h
      have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      linarith only [this]
    have hY0_re_pos : 0 < (psiBase.Y0 (τ : ℂ)).re := (psiBase.hY0_pos (τ : ℂ) hτ_ball).1
    have hY0_bd : ‖psiBase.Y0 (τ : ℂ)‖ ≤ MY0 := by
      have hτ_half : (τ : ℂ) ∈ closedBall (0 : ℂ) rHalf := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ_pos]
        exact (htau_lt.trans hrψ_lt).le.trans (min_le_left _ _)
      exact (le_csSup hY0_bdd ⟨_, hτ_half, rfl⟩).trans (le_max_left _ _)
    set y : ℝ := lowerYVal x
    have hy_sq : y ^ 2 = τ * (psiBase.Y0 (τ : ℂ)).re := by
      change lowerYVal x ^ 2 = _
      rw [hx_eq, hτY]
    have hy_pos : 0 < y := by
      have hC_gt : √2 < Real.cosh (π * x) := by
        rw [← cosh_pi_xiStar]
        exact Real.cosh_lt_cosh.mpr (by
          rw [abs_of_pos (mul_pos Real.pi_pos xiStar_pos), abs_of_pos (mul_pos Real.pi_pos (by linarith only [xiStar_pos, hx_gt]))]
          exact mul_lt_mul_of_pos_left (by linarith only [hx_gt]) Real.pi_pos)
      exact Real.sqrt_pos.mpr (div_pos (by linarith only [hC_gt]) (by positivity))
    have hy_sq_lt : y ^ 2 < psiBase.yTout ^ 2 := by
      rw [hy_sq]
      have hre_le : (psiBase.Y0 (τ : ℂ)).re ≤ MY0 := (Complex.re_le_norm _).trans hY0_bd
      have hτ_lt' : τ < psiBase.yTout ^ 2 / (2 * MY0) :=
        htau_lt.trans (hrψ_lt.trans_le (min_le_right _ _))
      calc τ * (psiBase.Y0 (τ : ℂ)).re ≤ τ * MY0 := mul_le_mul_of_nonneg_left hre_le hτ_pos.le
        _ < (psiBase.yTout ^ 2 / (2 * MY0)) * MY0 := mul_lt_mul_of_pos_right hτ_lt' hMY0_pos
        _ = psiBase.yTout ^ 2 / 2 := by field_simp [hMY0_pos.ne']
        _ < psiBase.yTout ^ 2 := half_lt_self (sq_pos_of_pos psiBase.hyTout_pos)
    have hy_lt_yTout : y < psiBase.yTout := by
      have := Real.sqrt_lt_sqrt (sq_nonneg y) hy_sq_lt
      rwa [Real.sqrt_sq hy_pos.le, Real.sqrt_sq psiBase.hyTout_pos.le] at this
    have hy_1 : y < 1 := hy_lt_yTout.trans_le psiBase.hyTout_half |>.trans (by norm_num)
    have hy_half : y < 1 / 2 := lt_of_lt_of_le hy_lt_yTout psiBase.hyTout_half
    have hTM := Classical.choose_spec (virasoro_TM_exists ε hε0 hε1)
    set TM := Classical.choose (virasoro_TM_exists ε hε0 hε1)
    obtain ⟨hTM_diff, hTM_conj, _, _, hTM_arg⟩ := hTM
    have hTM_y := hTM_arg y hy_pos hy_half
    obtain ⟨hTout_y, hth_lt⟩ := psiBase.hTout_real y hy_pos hy_lt_yTout
    have h_argW_eq : -(((-τ : ℝ) : ℂ)) * psiBase.Y0 (-((-τ : ℝ) : ℂ)) = ((y ^ 2 : ℝ) : ℂ) := by
      have hY0_c : psiBase.Y0 (τ : ℂ) = (((psiBase.Y0 (τ : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hY0_im
      rw [show -((-τ : ℝ) : ℂ) = (τ : ℂ) by push_cast; ring, hY0_c, ← Complex.ofReal_mul, ← hy_sq]
    have h_g0_eq : g0 ((-τ : ℝ) : ℂ) = ((√(psiBase.Y0 (τ : ℂ)).re / (2 * betaTip ^ (3 / 2 : ℝ)) : ℝ) : ℂ) := by
      dsimp [g0]
      have hY0_c : psiBase.Y0 (τ : ℂ) = (((psiBase.Y0 (τ : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hY0_im
      rw [show -((-τ : ℝ) : ℂ) = (τ : ℂ) by push_cast; ring, hY0_c,
        ← Complex.ofReal_cpow hY0_re_pos.le, ← Real.sqrt_eq_rpow]
      push_cast; rfl
    have h_psi_re : (virasoroPsiEps ε ((-τ : ℝ) : ℂ)).re =
        √(psiBase.Y0 (τ : ℂ)).re / (2 * betaTip ^ (3 / 2 : ℝ)) *
          ((psiBase.Tout ((y ^ 2 : ℝ) : ℂ)).re + (TM ((y ^ 2 : ℝ) : ℂ)).re) := by
      have h_eq : virasoroPsiEps ε ((-τ : ℝ) : ℂ) =
          g0 ((-τ : ℝ) : ℂ) * (psiBase.Tout (argW ((-τ : ℝ) : ℂ)) + TM (argW ((-τ : ℝ) : ℂ))) := by
        dsimp [virasoroPsiEps, virasoroTM, g0, argW]
        split_ifs with h <;> first | rfl | exact False.elim (h ⟨hε0, hε1⟩)
      rw [h_eq, h_g0_eq]
      dsimp [argW]
      rw [h_argW_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re]
    have hy_prod : √τ * √(psiBase.Y0 (τ : ℂ)).re = y := by
      rw [← Real.sqrt_mul hτ_pos.le, ← hy_sq, Real.sqrt_sq hy_pos.le]
    have h_lhs : 2 * betaTip ^ (3 / 2 : ℝ) * √τ * (virasoroPsiEps ε ((-τ : ℝ) : ℂ)).re =
        thetaOut y + 2 * Complex.arg ((1 + ε : ℂ) * (1 + (Complex.I * (y : ℂ)) ^ 2) /
          (1 + (Complex.I * (y : ℂ)) ^ 2 + (ε : ℂ) * (1 + Complex.I * (y : ℂ)))) := by
      rw [h_psi_re]
      have hbt_ne : betaTip ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos betaTip_pos _).ne'
      calc 2 * betaTip ^ (3 / 2 : ℝ) * √τ *
            (√(psiBase.Y0 (τ : ℂ)).re / (2 * betaTip ^ (3 / 2 : ℝ)) *
              ((psiBase.Tout ((y ^ 2 : ℝ) : ℂ)).re + (TM ((y ^ 2 : ℝ) : ℂ)).re))
          = (√τ * √(psiBase.Y0 (τ : ℂ)).re) *
              ((psiBase.Tout ((y ^ 2 : ℝ) : ℂ)).re + (TM ((y ^ 2 : ℝ) : ℂ)).re) := by
            field_simp [hbt_ne]
        _ = y * (psiBase.Tout ((y ^ 2 : ℝ) : ℂ)).re + y * (TM ((y ^ 2 : ℝ) : ℂ)).re := by
            rw [hy_prod]; ring
        _ = _ := by rw [hTout_y, hTM_y]
    have h_arg_gout : Complex.arg (Gout (Complex.I * (y : ℂ))) = thetaOut y := by
      have hW_pos : 0 < Wslit y := by
        have h1 : 0 < 1 - y ^ 2 := by nlinarith only [hy_pos, hy_1]
        have h2 : 0 < 1 + 6 * y ^ 2 + y ^ 4 := by positivity
        unfold Wslit
        have hpi := Real.pi_pos
        have hxi := xiStar_pos
        have hxOf_pos := xOf_pos ⟨hy_pos, hy_1⟩
        have h3 : 0 < 1 - Real.exp (-(4 * π * xOf y)) := by
          rw [sub_pos, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith only [hpi, hxOf_pos])
        have h4 : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
          rw [sub_pos, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith only [hpi, hxi])
        positivity
      rw [gout_polar ⟨hy_pos, hy_1⟩, Complex.arg_real_mul _ hW_pos, mul_comm Complex.I,
        Complex.exp_mul_I]
      exact Complex.arg_cos_add_sin_mul_I ⟨(abs_lt.mp hth_lt).1, (abs_lt.mp hth_lt).2.le⟩
    rw [h_arg_gout]
    exact ⟨hx_lt_sY, ⟨hy_pos, hy_1⟩, h_lhs⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoroPsiEps_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroPsiEps_spec

end

end FormalResearch.ModularBootstrap.FiveTerm


