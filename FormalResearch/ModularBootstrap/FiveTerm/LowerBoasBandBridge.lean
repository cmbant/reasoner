module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeGlobal
public import FormalResearch.ModularBootstrap.FiveTerm.LowerPass2Top
public import FormalResearch.ModularBootstrap.FiveTerm.LowerChartMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerSign
public import FormalResearch.ModularBootstrap.Bessel.VAsymptotic

/-!
# Band Moment Transfer and `t ↔ ζ` Density Bridge (`cts:boas` Step 3)

Connects `lowerBand` in the threshold coordinate `t` to the conformal phase coordinate `ζ`:
* `virasoro_moments_any_radius`: extends `virasoro_top_moments` (`ctl:pass2`) from the selected
  radius `R_J` to every macroscopic radius `R` in `LowerRadiusRange virasoroC1 c' R`, giving
  `virasoroBandB1 c' R T g + virasoroBandB2 c' R g ≤ K_M c'^{-1/3}`.
* `boasT` and `boasThreshold_eq_boasT_zetaMin`: exact change of variables `t(ζ) = c' x(ζ)^2 / 3`
  matching `virasoroDeltaChart c' (-c'^{4/7})` at `ζ = ζ_min(c')`.
* `lowerP0_mul_boasH_asymptotic`: uses `besselV_asymptotic` (`Lemma B(c)`) to prove
  `|P_0(ζ) H_c(ζ) - t'(ζ) g(t) V(t) / M[g]| ≤ C c'^{-1} t'(ζ) g(t) V(t) / M[g]`.
* `boas_zeta_to_lowerBand`: packages `IntegrableOn (P h)`, the `O(c'^{-1/3})` total bound, the
  `O(c'^{-4/3})` early-layer bound on `[ζ_min, 2 ζ_min]`, and `|∫ A_ζ(ζ) h(ζ) - lowerBand| ≤ K c'^{-4/3}`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

noncomputable section

/-! ### 1. `t ↔ ζ` Langer coordinate matching and Jacobian -/

/-- Band threshold `t_0(c') = Δ_c(-c'^{4/7})`. -/
def boasThreshold (c' : ℝ) : ℝ := virasoroDeltaChart c' (-(c' ^ (4 / 7 : ℝ)))

/-- Threshold map `t(ζ) = c' x(ζ)^2 / 3`. -/
def boasT (c' ζ : ℝ) : ℝ := c' * xOfZeta c' ζ ^ 2 / 3

/-- Derivative `dt/dζ = (4 / 3) x(ζ) / ρ_U(x(ζ))`. -/
def boasT' (c' ζ : ℝ) : ℝ := (4 / 3 : ℝ) * xOfZeta c' ζ / rhoU (xOfZeta c' ζ)

private lemma virasoro_delta_xOfZeta {c' ζ : ℝ} (hc0 : 0 < c') (hζ : 0 < ζ)
    (hv : vOfZeta ζ ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) :
    virasoroDeltaChart c' (-vOfZeta ζ) = boasT c' ζ := by
  have hv_pos : 0 < vOfZeta ζ := vOfZeta_pos hζ
  obtain ⟨hx_gt, hcum_eq, _⟩ := xOfZeta_spec hc0 hζ
  set x := xOfZeta c' ζ
  obtain ⟨htau, _, hx'_gt⟩ := lowerLangerPhase_band hc0 (u := -vOfZeta ζ)
    (by linarith only [hv]) (by linarith only [hv_pos])
  set x' := √(3 * virasoroDeltaChart c' (-vOfZeta ζ) / c')
  have htau_eq : tauPhase x' = tauPhase x := by
    rw [htau, neg_neg]
    have hβ := betaTip_pos
    have hc23 : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    unfold vOfZeta tauPhase
    have hk_pos := kTip_pos
    have hpi := Real.pi_pos
    have hβ_eq : betaTip = (3 * π * kTip / 2) ^ (2 / 3 : ℝ) := by
      unfold betaTip KTip; congr 1; ring
    have hmul : betaTip * c' ^ (2 / 3 : ℝ) = (3 * π * kTip / 2 * c') ^ (2 / 3 : ℝ) := by
      rw [hβ_eq]
      exact (@Real.mul_rpow (3 * π * kTip / 2) c' (2 / 3 : ℝ) (by positivity) hc0.le).symm
    rw [hmul, ← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    calc (3 * π * ζ / 2) / (3 * π * kTip / 2 * c')
        = (ζ / c') / kTip := by field_simp [hk_pos.ne', hc0.ne', hpi.ne']
      _ = cumulN x / kTip := by
          congr 1; rw [div_eq_iff hc0.ne']; linarith only [hcum_eq]
  have hx'_eq : x' = x := tauPhase_strictMonoOn.injOn hx'_gt.le hx_gt.le htau_eq
  have hΔ_nn : 0 ≤ 3 * virasoroDeltaChart c' (-vOfZeta ζ) / c' := by
    by_contra h
    have h0 : x' = 0 := by dsimp [x']; exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)
    linarith only [h0, hx'_gt, xiStar_pos]
  have hsq : 3 * virasoroDeltaChart c' (-vOfZeta ζ) / c' = x ^ 2 := by
    calc 3 * virasoroDeltaChart c' (-vOfZeta ζ) / c' = x' ^ 2 := (Real.sq_sqrt hΔ_nn).symm
      _ = x ^ 2 := by rw [hx'_eq]
  unfold boasT
  field_simp [hc0.ne'] at hsq ⊢
  linarith only [hsq]

private lemma vOfZeta_zetaMin {c' : ℝ} (hc0 : 0 < c') :
    vOfZeta (zetaMin c') = c' ^ (4 / 7 : ℝ) := by
  unfold vOfZeta zetaMin
  have hpi := Real.pi_pos.ne'
  rw [show 3 * π * (2 / (3 * π) * c' ^ (6 / 7 : ℝ)) / 2 = c' ^ (6 / 7 : ℝ) by field_simp [hpi],
    ← Real.rpow_mul hc0.le]
  norm_num

lemma boasThreshold_eq_boasT_zetaMin :
    ∃ c_thr : ℝ, 1 ≤ c_thr ∧ ∀ {c' : ℝ}, c_thr ≤ c' →
      boasThreshold c' = boasT c' (zetaMin c') := by
  have hc1_pos := virasoroC1_pos
  have hev : ∀ᶠ c' : ℝ in atTop, c' ^ (4 / 7 : ℝ) ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
    have ht : Tendsto (fun c' : ℝ => c' ^ (2 / 21 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 21)
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (ht.const_mul_atTop (by positivity : 0 < 5 * virasoroC1 ^ 2)).eventually_ge_atTop 1] with c' hc0 h21
    have hpow : c' ^ (2 / 3 : ℝ) = c' ^ (2 / 21 : ℝ) * c' ^ (4 / 7 : ℝ) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [hpow, ← mul_assoc]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hc0.le _) h21
  obtain ⟨c_thr, hc_thr⟩ := eventually_atTop.mp hev
  refine ⟨max 1 c_thr, le_max_left _ _, fun {c'} hc' => ?_⟩
  have hc0 : 0 < c' := by linarith [(le_max_left _ _).trans hc']
  have hv := hc_thr c' ((le_max_right _ _).trans hc')
  unfold boasThreshold
  rw [← vOfZeta_zetaMin hc0]
  exact virasoro_delta_xOfZeta hc0 (zetaMin_pos hc0) (by rwa [vOfZeta_zetaMin hc0])

lemma boasT_deriv_and_image {c' : ℝ} (hc0 : 0 < c') :
    (∀ {ζ : ℝ}, 0 < ζ → HasDerivAt (boasT c') (boasT' c' ζ) ζ ∧ 0 < boasT' c' ζ) ∧
    StrictMonoOn (boasT c') (Ioi 0) ∧
    boasT c' '' Ioi (zetaMin c') = Ioi (boasT c' (zetaMin c')) := by
  have hderiv : ∀ {ζ : ℝ}, 0 < ζ → HasDerivAt (boasT c') (boasT' c' ζ) ζ ∧ 0 < boasT' c' ζ := by
    intro ζ hζ
    obtain ⟨hx_gt, _, _⟩ := xOfZeta_spec hc0 hζ
    have hx_pos : 0 < xOfZeta c' ζ := xiStar_pos.trans hx_gt
    have hρ_pos : 0 < rhoU (xOfZeta c' ζ) := rhoU_pos hx_gt
    have hd_x := hasDerivAt_xOfZeta hc0 hζ
    have hd_t : HasDerivAt (fun t => c' * xOfZeta c' t ^ 2 / 3)
        (c' * (2 * xOfZeta c' ζ * (2 / (c' * rhoU (xOfZeta c' ζ)))) / 3) ζ :=
      (((hd_x.pow 2).const_mul c').div_const 3).congr_deriv (by ring)
    have hEq : c' * (2 * xOfZeta c' ζ * (2 / (c' * rhoU (xOfZeta c' ζ)))) / 3 = boasT' c' ζ := by
      unfold boasT'; field_simp [hc0.ne', hρ_pos.ne']; ring
    refine ⟨hEq ▸ hd_t, ?_⟩
    unfold boasT'; positivity
  have hmono : StrictMonoOn (boasT c') (Ioi 0) := by
    intro ζ₁ h1 ζ₂ h2 h12
    have hx_lt := xOfZeta_strictMono hc0 h1 h2 h12
    have hx1_pos : 0 < xOfZeta c' ζ₁ := xiStar_pos.trans (xOfZeta_spec hc0 h1).1
    unfold boasT
    have hsq : xOfZeta c' ζ₁ ^ 2 < xOfZeta c' ζ₂ ^ 2 := sq_lt_sq' (by linarith) hx_lt
    nlinarith only [hc0, hsq]
  refine ⟨hderiv, hmono, ?_⟩
  ext t
  refine ⟨?_, ?_⟩
  · rintro ⟨ζ, hζ, rfl⟩
    exact hmono (zetaMin_pos hc0) ((zetaMin_pos hc0).trans hζ) hζ
  · intro ht
    have hzmin_pos : 0 < zetaMin c' := zetaMin_pos hc0
    obtain ⟨hx0_gt, hcum0, _⟩ := xOfZeta_spec hc0 hzmin_pos
    set x0 := xOfZeta c' (zetaMin c')
    have hx0_pos : 0 < x0 := xiStar_pos.trans hx0_gt
    have ht_gt : c' * x0 ^ 2 / 3 < t := ht
    have ht_pos : 0 < 3 * t / c' := by
      have : 0 < c' * x0 ^ 2 / 3 := by positivity
      have : 0 < t := this.trans ht_gt
      positivity
    set x := √(3 * t / c')
    have hx0_lt_x : x0 < x := by
      rw [Real.lt_sqrt hx0_pos.le, lt_div_iff₀ hc0]
      linarith only [ht_gt]
    have hx_gt : xiStar < x := hx0_gt.trans hx0_lt_x
    have hcum_lt : cumulN x0 < cumulN x :=
      cumulN_strictMonoOn (Set.mem_Ici.mpr hx0_gt.le) (Set.mem_Ici.mpr hx_gt.le) hx0_lt_x
    set ζ := c' * cumulN x
    have hζ_gt : zetaMin c' < ζ := by
      have : c' * cumulN x0 < c' * cumulN x := mul_lt_mul_of_pos_left hcum_lt hc0
      linarith only [this, hcum0]
    have hζ_pos : 0 < ζ := hzmin_pos.trans_le hζ_gt.le
    obtain ⟨hxζ_gt, hcumζ, _⟩ := xOfZeta_spec hc0 hζ_pos
    have hxζ_eq : xOfZeta c' ζ = x := by
      have hce : cumulN (xOfZeta c' ζ) = cumulN x := by
        have : c' * cumulN (xOfZeta c' ζ) = c' * cumulN x := hcumζ
        exact mul_left_cancel₀ hc0.ne' this
      exact cumulN_strictMonoOn.injOn (Set.mem_Ici.mpr hxζ_gt.le) (Set.mem_Ici.mpr hx_gt.le) hce
    refine ⟨ζ, hζ_gt, ?_⟩
    unfold boasT
    rw [hxζ_eq, Real.sq_sqrt ht_pos.le]
    field_simp [hc0.ne']

/-! ### 2. Extending `B₁ + B₂ ≤ K c'^{-1/3}` from `R_J` to all `R ∈ LowerRadiusRange` -/

lemma virasoro_moments_any_radius :
    ∃ c_M K_M : ℝ, max virasoroCQEnv 10000 ≤ c_M ∧ 0 < K_M ∧
      ∀ {c' T R : ℝ} {g : ℝ → ℝ}, c_M ≤ c' →
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        LowerViolator virasoroPhi c' T →
        T ≤ virasoroDeltaChart c' (-virasoroAThr) →
        LowerRadiusRange virasoroC1 c' R →
        virasoroDeltaChart c' 0 ≤ T ∧
        T < virasoroDeltaChart c' (airyZero 1) ∧
        virasoroAThr ≤ R ∧
        R ≤ virasoroAC c' ^ 2 ∧
        T ≤ virasoroDeltaChart c' (-R) ∧
        virasoroBandB1 c' R T g + virasoroBandB2 c' R g ≤ K_M * c' ^ (-(1 / 3 : ℝ)) ∧
        0 ≤ virasoroBandB1 c' R T g ∧
        0 ≤ virasoroBandB2 c' R g ∧
        0 < virasoroProblem.cardyNorm (c' / 12) g ∧
        IntegrableOn (fun t => g t * virasoroProblem.cardyV (c' / 12) t / virasoroProblem.cardyNorm (c' / 12) g)
          (Ioi (boasThreshold c')) := by
  obtain ⟨K_top, c_top, hKtop_nn, hc_top_Q, htop⟩ := virasoro_top_moments
  obtain ⟨c_J, C_J, _, _, hJ⟩ := theoremJ_unconditional
  obtain ⟨c_ch, Cφ, hCφ_nn, hch⟩ := virasoroChart_holds
  have hc1_pos : 0 < virasoroC1 := virasoroC1_pos
  have hc1_bv : 10 * virasoroC1 ≤ virasoroBV := virasoroC1_small.trans virasoroBVChoice_le
  have h4c1_bv : 4 * virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by
    have hsq : (10 * virasoroC1) ^ 2 ≤ virasoroBV ^ 2 := pow_le_pow_left₀ (by positivity) hc1_bv 2
    nlinarith only [hsq]
  -- Violator lower bound `a_1 < virasoroUT c' T`
  let δ := -c0Star / cStar
  have hδ : 0 < δ := div_pos (neg_pos.mpr c0Star_neg) cStar_pos
  have hev : ∀ᶠ c' : ℝ in atTop,
      C_J ≤ Aopt * c' ^ (1 / 3 : ℝ) ∧
      (|gamma0 * airyZero 1| + Cφ) * c' ^ (-(2 / 3 : ℝ)) ≤ δ / 2 ∧
      virasoroAThr ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      c' ^ (4 / 7 : ℝ) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      max (max virasoroCQEnv 10000) (max c_top (max c_J c_ch)) ≤ c' := by
    have hc13 : Tendsto (fun c' : ℝ => c' ^ (1 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hc23 : Tendsto (fun c' : ℝ => c' ^ (2 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hc21 : Tendsto (fun c' : ℝ => c' ^ (2 / 21 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hm23 : Tendsto (fun c' : ℝ => (|gamma0 * airyZero 1| + Cφ) * c' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _
    have h47 : ∀ᶠ c' : ℝ in atTop, c' ^ (4 / 7 : ℝ) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),
        (hc21.const_mul_atTop (by positivity : 0 < virasoroC1 ^ 2)).eventually_ge_atTop 1] with c' hc0 h21
      have hpow : c' ^ (2 / 3 : ℝ) = c' ^ (2 / 21 : ℝ) * c' ^ (4 / 7 : ℝ) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      rw [hpow, ← mul_assoc]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hc0.le _) h21
    filter_upwards [(hc13.const_mul_atTop Aopt_pos).eventually_ge_atTop C_J,
      hm23.eventually (Iic_mem_nhds (by positivity : 0 < δ / 2)),
      (hc23.const_mul_atTop (by positivity : 0 < virasoroC1 ^ 2)).eventually_ge_atTop virasoroAThr,
      h47, eventually_ge_atTop _] with c' h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨c_M, hc_M⟩ := eventually_atTop.mp hev
  let ratio : ℝ := max 1 (pass2ScaleHi ^ 2 / virasoroC1 ^ 2)
  have hrat_ge : 1 ≤ ratio := le_max_left _ _
  let K_M : ℝ := ratio * (K_top + 1)
  have hKM_pos : 0 < K_M := by positivity
  refine ⟨max c_M (max virasoroCQEnv 10000), K_M, le_max_right _ _, hKM_pos,
    fun {c' T R g} hc' hwf hviol hT_hi hR => ?_⟩
  obtain ⟨hCJ, herr, hR_thr_min, h47_min, hmax⟩ := hc_M c' ((le_max_left _ _).trans hc')
  have hc_Q : virasoroCQEnv ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hmax)
  have hc10000 : 10000 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hmax)
  have hc_top : c_top ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have hc_J : c_J ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hmax))
  have hc_ch : c_ch ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hmax))
  have hc0 : 0 < c' := by linarith
  have hc1 : 1 ≤ c' := by linarith
  have ha_shift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha_shift hwf.1 hwf.2.1
  have hT_lo : virasoroDeltaChart c' 0 ≤ T := by
    rw [virasoroDeltaChart_zero]
    have hJc := hJ (by linarith only [hc_J] : c_J ≤ c' + 1) (by simpa [add_sub_cancel_right] using hwf)
    simp only [add_sub_cancel_right] at hJc; linarith only [hJc, hCJ]
  -- `a_1 < virasoroUT c' T`
  have ha1_lt_uT : airyZero 1 < virasoroUT c' T := by
    have hphi := (hch c' hc_ch).2.2.2.2
    have hpow1 : c' ^ (-1 : ℝ) ≤ c' ^ (-(1 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hpow43 : c' ^ (-(4 / 3 : ℝ)) ≤ c' ^ (-(1 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hm13_nn : 0 ≤ c' ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hm23_nn : 0 ≤ c' ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hrem : |gamma0 * airyZero 1 * c' ^ (-1 : ℝ)| + Cφ * c' ^ (-(4 / 3 : ℝ)) ≤
        (δ / 2) * c' ^ (-(1 / 3 : ℝ)) := by
      calc |gamma0 * airyZero 1 * c' ^ (-1 : ℝ)| + Cφ * c' ^ (-(4 / 3 : ℝ))
          = |gamma0 * airyZero 1| * c' ^ (-1 : ℝ) + Cφ * c' ^ (-(4 / 3 : ℝ)) := by
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hc0.le _)]
        _ ≤ |gamma0 * airyZero 1| * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ))) +
              Cφ * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ))) := by gcongr
        _ = ((|gamma0 * airyZero 1| + Cφ) * c' ^ (-(2 / 3 : ℝ))) * c' ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ (δ / 2) * c' ^ (-(1 / 3 : ℝ)) := by gcongr
    have hc0_eq : -(c0Star / cStar * c' ^ (-(1 / 3 : ℝ))) = δ * c' ^ (-(1 / 3 : ℝ)) := by
      dsimp [δ]; ring
    have hlo : airyZero 1 + (δ / 2) * c' ^ (-(1 / 3 : ℝ)) ≤ (virasoroPhi c' (airyZero 1 : ℂ)).re := by
      have hab := (abs_le.mp hphi).1
      have hγ := le_abs_self (gamma0 * airyZero 1 * c' ^ (-1 : ℝ))
      linarith
    have hδ_pos : 0 < (δ / 2) * c' ^ (-(1 / 3 : ℝ)) := mul_pos (half_pos hδ) (Real.rpow_pos_of_pos hc0 _)
    exact (by linarith : airyZero 1 < (virasoroPhi c' (airyZero 1 : ℂ)).re).trans hviol
  have hR_thr : virasoroAThr ≤ R := by
    have := hR.1; unfold lowerRmin at this; linarith only [this, hR_thr_min]
  have hR_AC : R ≤ virasoroAC c' ^ 2 := by
    have := hR.2; unfold lowerRmax at this
    rw [virasoroAC_sq c' hc0.le]
    have hc23_nn : 0 ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    calc R ≤ 4 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := this
      _ ≤ 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := by gcongr
  have hRm : -R ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hAThr_m : -virasoroAThr ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hT_R : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi.trans ((virasoroDeltaChart_strictAnti hc0).antitoneOn hRm hAThr_m (by linarith))
  have hT_a1 : T < virasoroDeltaChart c' (airyZero 1) := by
    have hu_mem := virasoroUT_between hc0 hAThr_m.1 (sq_nonneg _)
      (by linarith [virasoroAThr_pos]) hT_lo hT_hi
    rw [← hu_mem.2]
    have ha1_abs : |airyZero 1| ≤ virasoroAC c' ^ 2 := by
      have h1 := airyZero_neg 1
      have : virasoroAThr = -airyZero 1 + 1 := by unfold virasoroAThr; rw [abs_of_neg h1]
      rw [abs_of_neg h1]; linarith only [hR_thr, hR_AC, this]
    exact (virasoroDeltaChart_strictAnti hc0) (abs_le.mp ha1_abs)
      ⟨hAThr_m.1.trans hu_mem.1.1, hu_mem.1.2.trans (sq_nonneg _)⟩ ha1_lt_uT
  -- Apply `virasoro_top_moments` at `R_J` and transfer to `R`
  obtain ⟨R_J, hRJ_lo, hRJ_hi, hRJ_thr, hRJ_mom⟩ := htop hc_top hwf hT_a1 hT_hi
  have hRJ_pos : 0 < R_J := virasoroAThr_pos.trans_le hRJ_thr
  have hR_pos : 0 < R := virasoroAThr_pos.trans_le hR_thr
  have hRJ_AC : R_J ≤ virasoroAC c' ^ 2 := by
    have hc23_nn : 0 ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    have hhi_bv : pass2ScaleHi ^ 2 ≤ 2 * virasoroBV ^ 2 := by
      rw [pass2ScaleHi_sq]
      have hsq : virasoroBVChoice ^ 2 ≤ virasoroBV ^ 2 :=
        pow_le_pow_left₀ virasoroBVChoice_pos.le virasoroBVChoice_le 2
      linarith only [hsq]
    rw [virasoroAC_sq c' hc0.le]
    calc R_J ≤ pass2ScaleHi ^ 2 * c' ^ (2 / 3 : ℝ) - 1 := by linarith only [hRJ_hi]
      _ ≤ 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := by nlinarith only [hhi_bv, hc23_nn]
  have hRJm : -R_J ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith, by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hT_RJ : T ≤ virasoroDeltaChart c' (-R_J) :=
    hT_hi.trans ((virasoroDeltaChart_strictAnti hc0).antitoneOn hRJm hAThr_m (by linarith))
  -- Common `IntegrableOn` on `Ioi (virasoroDeltaChart c' 0)` for `dm(t)`
  have hΔ0_pos : 0 < virasoroDeltaChart c' 0 :=
    virasoroDeltaChart_pos hc0 (by rw [abs_zero]; exact sq_nonneg _)
  let dm : ℝ → ℝ := fun t => g t * virasoroProblem.cardyV (c' / 12) t / virasoroProblem.cardyNorm (c' / 12) g
  have hdm_int_Ioi0 : IntegrableOn dm (Ioi 0) := by
    have h1 : IntegrableOn (fun t => g t * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) := by
      refine hwf.1.int_cardy.mono'
        (((hwf.1.cont.mono Ioi_subset_Ici_self).mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).aestronglyMeasurable
          measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (virasoroProblem.cardyV_nonneg ha_shift (mem_Ioi.mp ht).le)]
    exact h1.div_const _
  have hdm_nn : ∀ t, T ≤ t → 0 ≤ dm t := fun t ht =>
    div_nonneg (mul_nonneg (hwf.2.2.2 t ht) (virasoroProblem.cardyV_nonneg ha_shift (hΔ0_pos.le.trans (hT_lo.trans ht))))
      hM_pos.le
  have h_ut_int : ∀ {a b : ℝ}, virasoroDeltaChart c' 0 ≤ a → a ≤ b → b ≤ virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) →
      IntervalIntegrable (fun t => (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)) volume a b := by
    intro a b ha0 hab hbA
    have hcont_t : ContinuousOn (fun t => (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)) (Icc a b) := by
      have hut_c : ContinuousOn (fun t => -virasoroUT c' t) (Icc a b) := by
        intro t ht
        have hu_t := virasoroUT_between hc0 (le_rfl : -(virasoroAC c' ^ 2) ≤ -(virasoroAC c' ^ 2))
          (sq_nonneg _) (by linarith [sq_nonneg (virasoroAC c')]) (ha0.trans ht.1) (ht.2.trans hbA)
        have hdiv := virasoroDeltaChart_div_mem hc0 (abs_le.mpr ⟨hu_t.1.1, hu_t.1.2.trans (sq_nonneg _)⟩)
        rw [hu_t.2] at hdiv
        have hξ_open : ((t / c' : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have h1 : |t / c' - xiBar| ≤ virasoroChartR0 := abs_le.mpr ⟨by linarith [hdiv.1], by linarith [hdiv.2]⟩
          exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
        have hcont_at : ContinuousAt (fun x : ℝ => virasoroUChart c' (x / c')) t := by
          unfold virasoroUChart
          have hcomp := (virasoroUInf_an _ hξ_open).continuousAt.comp_of_eq
            (Complex.continuous_ofReal.comp (continuous_id.div_const c')).continuousAt rfl
          exact (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp))
        exact hcont_at.neg.continuousWithinAt
      exact hut_c.mul ((hwf.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
        fun t ht => hΔ0_pos.le.trans (ha0.trans ht.1))
    exact hcont_t.intervalIntegrable_of_Icc hab
  -- Transfer `B₁(R) + B₂(R)` from `(B₁(R_J), B₂(R_J))`
  let gv : ℝ → ℝ := fun t => g t * virasoroProblem.cardyV (c' / 12) t
  have hgv_int_Ioi0 : IntegrableOn gv (Ioi 0) := by
    refine hwf.1.int_cardy.mono'
      (((hwf.1.cont.mono Ioi_subset_Ici_self).mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (virasoroProblem.cardyV_nonneg ha_shift (mem_Ioi.mp ht).le)]
  have hgv_nn : ∀ {t : ℝ}, T ≤ t → 0 ≤ gv t := fun {t} ht =>
    mul_nonneg (hwf.2.2.2 t ht) (virasoroProblem.cardyV_nonneg ha_shift (hΔ0_pos.le.trans (hT_lo.trans ht)))
  have hut_bd : ∀ {r s t : ℝ}, 0 ≤ r → r ≤ s → s ≤ virasoroAC c' ^ 2 →
      virasoroDeltaChart c' (-r) ≤ t → t ≤ virasoroDeltaChart c' (-s) →
      r ≤ -virasoroUT c' t ∧ -virasoroUT c' t ≤ s := by
    intro r s t hr hrs hsAC hlo hhi
    have hu := (virasoroUT_between hc0 (by linarith only [hsAC]) (by linarith only [hr, sq_nonneg (virasoroAC c')])
      (by linarith only [hrs]) hlo hhi).1
    exact ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  have hAC_mem : -(virasoroAC c' ^ 2) ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨le_rfl, by linarith [sq_nonneg (virasoroAC c')]⟩
  have hmom_transfer : virasoroBandB1 c' R T g + virasoroBandB2 c' R g ≤
      ratio * (virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g) := by
    by_cases hRRJ : R ≤ R_J
    · have hΔ_le : virasoroDeltaChart c' (-R) ≤ virasoroDeltaChart c' (-R_J) :=
        (virasoroDeltaChart_strictAnti hc0).antitoneOn hRJm hRm (by linarith only [hRRJ])
      have hratio_ge : R_J / R ≤ ratio := by
        refine le_trans ?_ (le_max_right _ _)
        have hc23_pos : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
        have hR_lo : virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR.1
        have hRJ_ub : R_J ≤ pass2ScaleHi ^ 2 * c' ^ (2 / 3 : ℝ) := by linarith only [hRJ_hi]
        rw [div_le_div_iff₀ hR_pos (by positivity : 0 < virasoroC1 ^ 2)]
        calc R_J * virasoroC1 ^ 2 ≤ (pass2ScaleHi ^ 2 * c' ^ (2 / 3 : ℝ)) * virasoroC1 ^ 2 := by gcongr
          _ = pass2ScaleHi ^ 2 * (virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) := by ring
          _ ≤ pass2ScaleHi ^ 2 * R := by gcongr
      have hint_T_R : IntervalIntegrable (fun t => (-virasoroUT c' t) * gv t) volume T (virasoroDeltaChart c' (-R)) :=
        h_ut_int hT_lo hT_R ((virasoroDeltaChart_strictAnti hc0).antitoneOn hAC_mem hRm hRm.1)
      have hint_R_RJ : IntervalIntegrable (fun t => (-virasoroUT c' t) * gv t) volume
          (virasoroDeltaChart c' (-R)) (virasoroDeltaChart c' (-R_J)) :=
        h_ut_int (hT_lo.trans hT_R) hΔ_le ((virasoroDeltaChart_strictAnti hc0).antitoneOn hAC_mem hRJm hRJm.1)
      have hgv_R_RJ : IntervalIntegrable gv volume (virasoroDeltaChart c' (-R)) (virasoroDeltaChart c' (-R_J)) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ_le]
        exact hgv_int_Ioi0.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (hΔ0_pos.trans_le (hT_lo.trans hT_R)).le))
      have hpart2 : ∫ t in (virasoroDeltaChart c' (-R))..(virasoroDeltaChart c' (-R_J)), gv t ≤
          R⁻¹ * ∫ t in (virasoroDeltaChart c' (-R))..(virasoroDeltaChart c' (-R_J)),
            (-virasoroUT c' t) * gv t := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on hΔ_le hgv_R_RJ (hint_R_RJ.const_mul _) fun t ht => ?_
        have hut := (hut_bd hR_pos.le hRRJ hRJ_AC ht.1 ht.2).1
        have hgv_t : 0 ≤ gv t := hgv_nn (hT_R.trans ht.1)
        calc gv t = 1 * gv t := (one_mul _).symm
          _ ≤ (R⁻¹ * (-virasoroUT c' t)) * gv t := by
              gcongr; rw [inv_mul_eq_div, one_le_div hR_pos]; exact hut
          _ = R⁻¹ * ((-virasoroUT c' t) * gv t) := by ring
      have hIci_split : ∫ t in Ici (virasoroDeltaChart c' (-R)), gv t =
          (∫ t in (virasoroDeltaChart c' (-R))..(virasoroDeltaChart c' (-R_J)), gv t) +
            ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t := by
        have hIoiR : IntegrableOn gv (Ioi (virasoroDeltaChart c' (-R))) :=
          hgv_int_Ioi0.mono_set (Ioi_subset_Ioi (hΔ0_pos.trans_le (hT_lo.trans hT_R)).le)
        rw [← MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici,
          ← MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici,
          intervalIntegral.integral_of_le hΔ_le]
        conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi hΔ_le]
        exact MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hIoiR.mono_set Ioc_subset_Ioi_self) (hIoiR.mono_set (Ioi_subset_Ioi hΔ_le))
      have hIci_RJ_nn : 0 ≤ ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ici fun t ht => hgv_nn (hT_RJ.trans ht)
      have hIci_tail : ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t ≤
          (R_J / R) * ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t :=
        le_mul_of_one_le_left hIci_RJ_nn ((one_le_div hR_pos).mpr hRRJ)
      have hRJ_split : ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t =
          (∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t) +
            ∫ t in (virasoroDeltaChart c' (-R))..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t :=
        (intervalIntegral.integral_add_adjacent_intervals hint_T_R hint_R_RJ).symm
      have hcomb : R⁻¹ * (∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t) +
          ∫ t in Ici (virasoroDeltaChart c' (-R)), gv t ≤
          (R_J / R) * (R_J⁻¹ * (∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t) +
            ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t) := by
        rw [hIci_split, hRJ_split]
        have h1 : R⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t =
            (R_J / R) * (R_J⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t) := by
          field_simp [hR_pos.ne', hRJ_pos.ne']
        have h2 : R⁻¹ * ∫ t in (virasoroDeltaChart c' (-R))..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t =
            (R_J / R) * (R_J⁻¹ * ∫ t in (virasoroDeltaChart c' (-R))..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t) := by
          field_simp [hR_pos.ne', hRJ_pos.ne']
        linarith only [h1, h2, hpart2, hIci_tail]
      have hRJ_nn : 0 ≤ virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g := by
        have h1 : 0 ≤ ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t := by
          refine intervalIntegral.integral_nonneg hT_RJ fun t ht => ?_
          have hut := (hut_bd le_rfl hRJ_pos.le hRJ_AC (by simpa using hT_lo.trans ht.1) ht.2).1
          exact mul_nonneg hut (hgv_nn ht.1)
        unfold virasoroBandB1 virasoroBandB2
        positivity
      calc virasoroBandB1 c' R T g + virasoroBandB2 c' R g
          = (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
              (R⁻¹ * (∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t) +
                ∫ t in Ici (virasoroDeltaChart c' (-R)), gv t) := by
            unfold virasoroBandB1 virasoroBandB2; dsimp [gv]; ring
        _ ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
              ((R_J / R) * (R_J⁻¹ * (∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t) +
                ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t)) := by gcongr
        _ = (R_J / R) * (virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g) := by
            unfold virasoroBandB1 virasoroBandB2; dsimp [gv]; ring
        _ ≤ ratio * (virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g) := by gcongr
    · have hRJR : R_J ≤ R := le_of_not_ge hRRJ
      have hΔ_le : virasoroDeltaChart c' (-R_J) ≤ virasoroDeltaChart c' (-R) :=
        (virasoroDeltaChart_strictAnti hc0).antitoneOn hRm hRJm (by linarith only [hRJR])
      have hint_T_RJ : IntervalIntegrable (fun t => (-virasoroUT c' t) * gv t) volume T (virasoroDeltaChart c' (-R_J)) :=
        h_ut_int hT_lo hT_RJ ((virasoroDeltaChart_strictAnti hc0).antitoneOn hAC_mem hRJm hRJm.1)
      have hint_RJ_R : IntervalIntegrable (fun t => (-virasoroUT c' t) * gv t) volume
          (virasoroDeltaChart c' (-R_J)) (virasoroDeltaChart c' (-R)) :=
        h_ut_int (hT_lo.trans hT_RJ) hΔ_le ((virasoroDeltaChart_strictAnti hc0).antitoneOn hAC_mem hRm hRm.1)
      have hgv_RJ_R : IntervalIntegrable gv volume (virasoroDeltaChart c' (-R_J)) (virasoroDeltaChart c' (-R)) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ_le]
        exact hgv_int_Ioi0.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (hΔ0_pos.trans_le (hT_lo.trans hT_RJ)).le))
      have hpart1 : R⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t ≤
          R_J⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t := by
        have h1 : 0 ≤ ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t := by
          refine intervalIntegral.integral_nonneg hT_RJ fun t ht => ?_
          have hut := (hut_bd le_rfl hRJ_pos.le hRJ_AC (by simpa using hT_lo.trans ht.1) ht.2).1
          exact mul_nonneg hut (hgv_nn ht.1)
        have hinv : R⁻¹ ≤ R_J⁻¹ := inv_anti₀ hRJ_pos hRJR
        gcongr
      have hpart2 : R⁻¹ * ∫ t in (virasoroDeltaChart c' (-R_J))..(virasoroDeltaChart c' (-R)),
            (-virasoroUT c' t) * gv t ≤
          ∫ t in (virasoroDeltaChart c' (-R_J))..(virasoroDeltaChart c' (-R)), gv t := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on hΔ_le (hint_RJ_R.const_mul _) hgv_RJ_R fun t ht => ?_
        have hut := (hut_bd hRJ_pos.le hRJR hR_AC ht.1 ht.2).2
        have hgv_t : 0 ≤ gv t := hgv_nn (hT_RJ.trans ht.1)
        calc R⁻¹ * ((-virasoroUT c' t) * gv t) = (R⁻¹ * (-virasoroUT c' t)) * gv t := by ring
          _ ≤ 1 * gv t := by
              gcongr; rw [inv_mul_le_iff₀ hR_pos]; linarith only [hut]
          _ = gv t := one_mul _
      have hIci_split : ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t =
          (∫ t in (virasoroDeltaChart c' (-R_J))..(virasoroDeltaChart c' (-R)), gv t) +
            ∫ t in Ici (virasoroDeltaChart c' (-R)), gv t := by
        have hIoiRJ : IntegrableOn gv (Ioi (virasoroDeltaChart c' (-R_J))) :=
          hgv_int_Ioi0.mono_set (Ioi_subset_Ioi (hΔ0_pos.trans_le (hT_lo.trans hT_RJ)).le)
        rw [← MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici,
          ← MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici,
          intervalIntegral.integral_of_le hΔ_le]
        conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi hΔ_le]
        exact MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hIoiRJ.mono_set Ioc_subset_Ioi_self) (hIoiRJ.mono_set (Ioi_subset_Ioi hΔ_le))
      have hR_split : ∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t =
          (∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t) +
            ∫ t in (virasoroDeltaChart c' (-R_J))..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t :=
        (intervalIntegral.integral_add_adjacent_intervals hint_T_RJ hint_RJ_R).symm
      have hcomb : virasoroBandB1 c' R T g + virasoroBandB2 c' R g ≤
          virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g := by
        have hraw : R⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t +
            ∫ t in Ici (virasoroDeltaChart c' (-R)), gv t ≤
            R_J⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t +
              ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t := by
          rw [hR_split, hIci_split, mul_add]
          linarith only [hpart1, hpart2]
        calc virasoroBandB1 c' R T g + virasoroBandB2 c' R g
            = (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
                (R⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R)), (-virasoroUT c' t) * gv t +
                  ∫ t in Ici (virasoroDeltaChart c' (-R)), gv t) := by
              unfold virasoroBandB1 virasoroBandB2; dsimp [gv]; ring
          _ ≤ (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
                (R_J⁻¹ * ∫ t in T..(virasoroDeltaChart c' (-R_J)), (-virasoroUT c' t) * gv t +
                  ∫ t in Ici (virasoroDeltaChart c' (-R_J)), gv t) := by gcongr
          _ = virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g := by
              unfold virasoroBandB1 virasoroBandB2; dsimp [gv]; ring
      have hB_nn : 0 ≤ virasoroBandB1 c' R T g + virasoroBandB2 c' R g :=
        add_nonneg (virasoroBandB1_nonneg hc_Q hR_thr hR_AC hwf hT_lo hT_hi)
          (virasoroBandB2_nonneg hc_Q hR_thr hR_AC hwf hT_hi)
      exact hcomb.trans (le_mul_of_one_le_left (hB_nn.trans hcomb) hrat_ge)
  have hmom_final : virasoroBandB1 c' R T g + virasoroBandB2 c' R g ≤ K_M * c' ^ (-(1 / 3 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hRJ_mom (by positivity : 0 ≤ ratio)
    calc virasoroBandB1 c' R T g + virasoroBandB2 c' R g
        ≤ ratio * (virasoroBandB1 c' R_J T g + virasoroBandB2 c' R_J g) := hmom_transfer
      _ ≤ ratio * (K_top * c' ^ (-(1 / 3 : ℝ))) := this
      _ ≤ ratio * ((K_top + 1) * c' ^ (-(1 / 3 : ℝ))) := by gcongr; linarith
      _ = K_M * c' ^ (-(1 / 3 : ℝ)) := by dsimp [K_M]; ring
  have hB1_nn := virasoroBandB1_nonneg hc_Q hR_thr hR_AC hwf hT_lo hT_hi
  have hB2_nn := virasoroBandB2_nonneg hc_Q hR_thr hR_AC hwf hT_hi
  have hthr_pos : 0 < boasThreshold c' := by
    have h47m : |-(c' ^ (4 / 7 : ℝ))| ≤ virasoroAC c' ^ 2 := by
      have hc1_bv_sq : virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by
        linarith only [h4c1_bv, sq_nonneg virasoroC1]
      rw [abs_neg, abs_of_pos (Real.rpow_pos_of_pos hc0 _), virasoroAC_sq c' hc0.le]
      calc c' ^ (4 / 7 : ℝ) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := h47_min
        _ ≤ 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := by
            have := Real.rpow_nonneg hc0.le (2 / 3 : ℝ); gcongr
    exact virasoroDeltaChart_pos hc0 h47m
  exact ⟨hT_lo, hT_a1, hR_thr, hR_AC, hT_R, hmom_final, hB1_nn, hB2_nn, hM_pos,
    hdm_int_Ioi0.mono_set (Ioi_subset_Ioi hthr_pos.le)⟩

/-! ### 3. Pointwise Bessel `B(c)` comparison between `P₀ H_c` and `t' g V / M` -/

lemma lowerP0_mul_boasH_asymptotic :
    ∃ c_B C_B : ℝ, 10000 ≤ c_B ∧ 0 < C_B ∧
      ∀ {c' T ζ : ℝ} {g : ℝ → ℝ}, c_B ≤ c' →
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        T ≤ virasoroDeltaChart c' (-virasoroAThr) →
        zetaMin c' ≤ ζ →
        0 ≤ (boasH c' g (ζ : ℂ)).re ∧
        (boasH c' g (ζ : ℂ)).im = 0 ∧
        |lowerP0 c' ζ * (boasH c' g (ζ : ℂ)).re -
            boasT' c' ζ * (g (boasT c' ζ) * virasoroProblem.cardyV (c' / 12) (boasT c' ζ) /
              virasoroProblem.cardyNorm (c' / 12) g)| ≤
          C_B * c' ^ (-1 : ℝ) *
            (boasT' c' ζ * (g (boasT c' ζ) * virasoroProblem.cardyV (c' / 12) (boasT c' ζ) /
              virasoroProblem.cardyNorm (c' / 12) g)) := by
  obtain ⟨c_hr, hc_hr10, hhr⟩ := boasH_ofReal_nonneg
  obtain ⟨c_thr, hc_thr1, hc_thr⟩ := boasThreshold_eq_boasT_zetaMin
  have hxi_pos : 0 < xiStar := xiStar_pos
  set e0 : ℝ := 1 - Real.exp (-(4 * π * xiStar))
  have he0_pos : 0 < e0 := by
    dsimp [e0]
    have hexp_lt : Real.exp (-(4 * π * xiStar)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [Real.pi_pos, hxi_pos])
    linarith only [hexp_lt]
  let K_bes : ℝ := 96 + 60 / xiStar
  let C_B : ℝ := 2 * K_bes / e0 ^ 2
  have hKB_pos : 0 < K_bes := by dsimp [K_bes]; positivity
  have hCB_pos : 0 < C_B := by dsimp [C_B]; exact div_pos (mul_pos zero_lt_two hKB_pos) (sq_pos_of_pos he0_pos)
  let c_B : ℝ := max (max c_hr c_thr) (max 10000 (max (48 + 4 / xiStar) (2 * K_bes / e0 ^ 2 + 1)))
  have hcB_ge : 10000 ≤ c_B := (le_max_left _ _).trans (le_max_right _ _)
  -- Also ensure `virasoroAThr ≤ c' ^ (4 / 7)` and `c' ^ (4 / 7) ≤ virasoroAC c' ^ 2`
  have hev_47 : ∀ᶠ c' : ℝ in atTop, virasoroAThr ≤ c' ^ (4 / 7 : ℝ) ∧ c' ^ (4 / 7 : ℝ) ≤ virasoroAC c' ^ 2 := by
    have h47 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 7)
    have h221 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 21)
    have hbv := virasoroBV_pos
    filter_upwards [eventually_ge_atTop (1 : ℝ), h47.eventually_ge_atTop virasoroAThr,
      (h221.const_mul_atTop (by positivity : 0 < 2 * virasoroBV ^ 2)).eventually_ge_atTop 1]
      with c' hc1 h1 h2
    have hc0 : 0 < c' := by linarith
    refine ⟨h1, ?_⟩
    rw [virasoroAC_sq c' hc0.le]
    have hpow : c' ^ (2 / 3 : ℝ) = c' ^ (2 / 21 : ℝ) * c' ^ (4 / 7 : ℝ) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [hpow, ← mul_assoc]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hc0.le _) h2
  obtain ⟨c_47, hc_47⟩ := eventually_atTop.mp hev_47
  refine ⟨max c_B c_47, C_B, hcB_ge.trans (le_max_left _ _), hCB_pos,
    fun {c' T ζ g} hc' hwf hT_hi hζ => ?_⟩
  have hcB' : c_B ≤ c' := (le_max_left _ _).trans hc'
  have hc_47' := hc_47 c' ((le_max_right _ _).trans hc')
  have hc_hr' : c_hr ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hcB')
  have hc_thr' : c_thr ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hcB')
  have hc10000 : 10000 ≤ c' := hcB_ge.trans hcB'
  have hc0 : 0 < c' := by linarith
  have hc_bes : 48 + 4 / xiStar ≤ c' :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcB'))
  have hc_half : 2 * K_bes / e0 ^ 2 + 1 ≤ c' :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcB'))
  have hzmin_pos : 0 < zetaMin c' := zetaMin_pos hc0
  have hζ_pos : 0 < ζ := hzmin_pos.trans_le hζ
  have hquarter : (1 / 4 : ℝ) * zetaMin c' ≤ ζ := by linarith only [hzmin_pos, hζ]
  obtain ⟨hH_im, hH_re⟩ := hhr hc_hr' hwf hT_hi hquarter
  refine ⟨hH_re, hH_im, ?_⟩
  set x : ℝ := xOfZeta c' ζ
  obtain ⟨hx_gt, _, _⟩ := xOfZeta_spec hc0 hζ_pos
  have hx_pos : 0 < x := hxi_pos.trans hx_gt
  have hρ_pos : 0 < rhoU x := rhoU_pos hx_gt
  -- Exact identity for `(boasH c' g ζ).re`
  obtain ⟨hb_im, _, _⟩ := bOfZeta_ofReal hc0 hζ_pos
  have hb_eq : bOfZeta c' (ζ : ℂ) = (x : ℂ) := Complex.ext rfl hb_im
  have ha_shift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero ha_shift hwf.1 hwf.2.1
  set M := virasoroProblem.cardyNorm (c' / 12) g
  have hH_eq : (boasH c' g (ζ : ℂ)).re =
      M⁻¹ * g (boasT c' ζ) * Real.exp ((2 * π / 3) * c' * x) := by
    unfold boasH boasT
    rw [hb_eq, PoissonJensen.hankelContinuation_ofReal hc0 hwf.1 x]
    have hre_eq : ((M : ℝ) : ℂ)⁻¹ * (g (c' * x ^ 2 / 3) : ℂ) *
          Complex.exp (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * (x : ℂ)) =
        ((M⁻¹ * g (c' * x ^ 2 / 3) * Real.exp ((2 * π / 3) * c' * x) : ℝ) : ℂ) := by
      rw [show (((2 * π / 3 : ℝ) : ℂ) * (c' : ℂ) * (x : ℂ)) =
          ((2 * π / 3 * c' * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
      push_cast; ring
    rw [hre_eq, Complex.ofReal_re]
  -- Check `T ≤ boasT c' ζ` so `0 ≤ g (boasT c' ζ)`
  have hT_le_boas : T ≤ boasT c' ζ := by
    have h47m : -(virasoroAC c' ^ 2) ≤ -(c' ^ (4 / 7 : ℝ)) := by linarith only [hc_47'.2]
    have hΔ_le : virasoroDeltaChart c' (-virasoroAThr) ≤ boasThreshold c' :=
      (virasoroDeltaChart_strictAnti hc0).antitoneOn ⟨h47m, by linarith [Real.rpow_pos_of_pos hc0 (4 / 7 : ℝ), sq_nonneg (virasoroAC c')]⟩
        ⟨by linarith only [hc_47'.1, hc_47'.2], by linarith [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
        (by linarith only [hc_47'.1])
    have hmono := (boasT_deriv_and_image hc0).2.1
    have hT_mono : boasT c' (zetaMin c') ≤ boasT c' ζ := hmono.monotoneOn hzmin_pos hζ_pos hζ
    have hthr_c' : boasThreshold c' = boasT c' (zetaMin c') := hc_thr hc_thr'
    rw [hthr_c'] at hΔ_le
    exact hT_hi.trans (hΔ_le.trans hT_mono)
  have hg_nn : 0 ≤ g (boasT c' ζ) := hwf.2.2.2 _ hT_le_boas
  -- Exact identity: `lowerP0 * exp((2π/3) c' x) = boasT' * besselAs (c' * besselL x) * (1 - exp(-4πx))^2`
  have hsqrt_as : √(2 * π * (c' * besselL x)) = 2 * π * √c' * √x / √3 := by
    unfold besselL
    have hsq : (2 * π * √c' * √x / √3) ^ 2 = 2 * π * (c' * (2 * π * x / 3)) := by
      rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hx_pos.le,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have hP0_id : lowerP0 c' ζ * Real.exp ((2 * π / 3) * c' * x) =
      boasT' c' ζ * besselAs (c' * besselL x) * (1 - Real.exp (-(4 * π * x))) ^ 2 := by
    unfold lowerP0 boasT' besselAs
    change (2 * √x * (1 - Real.exp (-(4 * π * x))) ^ 2 / (√3 * π * √c' * rhoU x)) *
        Real.exp ((2 * π / 3) * c' * x) =
      (4 / 3 * x / rhoU x) * (Real.exp (c' * besselL x) / √(2 * π * (c' * besselL x))) *
        (1 - Real.exp (-(4 * π * x))) ^ 2
    have hexp_eq : c' * besselL x = (2 * π / 3) * c' * x := by unfold besselL; ring
    have hx_sq : x = √x * √x := (Real.mul_self_sqrt hx_pos.le).symm
    have h3_sq : (3 : ℝ) = √3 * √3 := (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)).symm
    have hsc : √c' ≠ 0 := (Real.sqrt_pos.mpr hc0).ne'
    have hsx : √x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
    have hs3 : √(3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    rw [hsqrt_as, hexp_eq]
    conv_rhs => rw [hx_sq, h3_sq]
    field_simp [hρ_pos.ne', Real.pi_pos.ne', hc0.ne', hx_pos.ne', hsc, hsx, hs3]
    ring
  -- Combine with `besselV_asymptotic`
  have ha2 : (2 : ℝ) ≤ c' / 12 := by linarith only [hc10000]
  have hboasT_nn : 0 ≤ boasT c' ζ := by unfold boasT; positivity
  have hV_eq : virasoroProblem.cardyV (c' / 12) (boasT c' ζ) = besselV (c' / 12) (c' * x ^ 2 / 3) :=
    virasoro_cardyV_eq_besselV ha2 hboasT_nn
  have hL_pos : 0 < c' * besselL x := by unfold besselL; positivity
  have hAs_pos : 0 < besselAs (c' * besselL x) := besselAs_pos hL_pos
  have hbes := besselV_asymptotic hxi_pos hc_bes hx_gt.le
  set V := besselV (c' / 12) (c' * x ^ 2 / 3)
  set A := besselAs (c' * besselL x)
  set ex := 1 - Real.exp (-(4 * π * x))
  have hex_ge : e0 ≤ ex := by
    dsimp [e0, ex]
    have hle : -(4 * π * x) ≤ -(4 * π * xiStar) := by nlinarith only [Real.pi_pos, hx_gt]
    linarith only [Real.exp_le_exp.mpr hle]
  have hex_sq_ge : e0 ^ 2 ≤ ex ^ 2 := by nlinarith only [he0_pos, hex_ge]
  have hKB_bd : K_bes / c' ≤ e0 ^ 2 / 2 := by
    rw [div_le_div_iff₀ hc0 zero_lt_two]
    have : 2 * K_bes / e0 ^ 2 ≤ c' := by linarith only [hc_half]
    rwa [div_le_iff₀ (sq_pos_of_pos he0_pos)] at this
  have hV_lb : (e0 ^ 2 / 2) * A ≤ V := by
    have h1 := (abs_le.mp hbes).1
    have h2 : e0 ^ 2 - K_bes / c' ≤ V / A := by linarith only [h1, hex_sq_ge]
    have h3 : e0 ^ 2 / 2 ≤ V / A := by linarith only [h2, hKB_bd]
    rwa [le_div_iff₀ hAs_pos] at h3
  have hA_ub : A ≤ (2 / e0 ^ 2) * V := by
    have he0_sq_pos : 0 < e0 ^ 2 := sq_pos_of_pos he0_pos
    calc A = (2 / e0 ^ 2) * ((e0 ^ 2 / 2) * A) := by field_simp [he0_sq_pos.ne']
      _ ≤ (2 / e0 ^ 2) * V := by gcongr
  have hT'_pos : 0 < boasT' c' ζ := (boasT_deriv_and_image hc0).1 hζ_pos |>.2
  have hP0H_eq : lowerP0 c' ζ * (boasH c' g (ζ : ℂ)).re =
      boasT' c' ζ * (g (boasT c' ζ) / M) * (A * ex ^ 2) := by
    rw [hH_eq]
    calc lowerP0 c' ζ * (M⁻¹ * g (boasT c' ζ) * Real.exp ((2 * π / 3) * c' * x))
        = (g (boasT c' ζ) / M) * (lowerP0 c' ζ * Real.exp ((2 * π / 3) * c' * x)) := by ring
      _ = (g (boasT c' ζ) / M) * (boasT' c' ζ * A * ex ^ 2) := by rw [hP0_id]
      _ = boasT' c' ζ * (g (boasT c' ζ) / M) * (A * ex ^ 2) := by ring
  have hdm_eq : boasT' c' ζ * (g (boasT c' ζ) * virasoroProblem.cardyV (c' / 12) (boasT c' ζ) / M) =
      boasT' c' ζ * (g (boasT c' ζ) / M) * V := by
    rw [hV_eq]; ring
  rw [hP0H_eq, hdm_eq]
  have hcoeff_nn : 0 ≤ boasT' c' ζ * (g (boasT c' ζ) / M) := by positivity
  have hV_nn : 0 ≤ V := (mul_nonneg (by positivity) hAs_pos.le).trans hV_lb
  have hdiff : |A * ex ^ 2 - V| ≤ (K_bes / c') * A := by
    have h1 : A * ex ^ 2 - V = -(V / A - ex ^ 2) * A := by field_simp [hAs_pos.ne']; ring
    rw [h1, abs_mul, abs_neg, abs_of_pos hAs_pos]
    exact mul_le_mul_of_nonneg_right hbes hAs_pos.le
  calc |boasT' c' ζ * (g (boasT c' ζ) / M) * (A * ex ^ 2) - boasT' c' ζ * (g (boasT c' ζ) / M) * V|
      = boasT' c' ζ * (g (boasT c' ζ) / M) * |A * ex ^ 2 - V| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hcoeff_nn]
    _ ≤ boasT' c' ζ * (g (boasT c' ζ) / M) * ((K_bes / c') * A) := by gcongr
    _ ≤ boasT' c' ζ * (g (boasT c' ζ) / M) * ((K_bes / c') * ((2 / e0 ^ 2) * V)) := by gcongr
    _ = C_B * c' ^ (-1 : ℝ) * (boasT' c' ζ * (g (boasT c' ζ) / M) * V) := by
        dsimp [C_B]; rw [Real.rpow_neg_one]; ring

/-! ### 4. Bridging `∫ A_ζ(ζ) h(ζ) dζ` and early layer to `lowerBand` -/

lemma boas_zeta_to_lowerBand :
    ∃ c_Z K_1 K_early K_err : ℝ,
      max virasoroCQEnv 10000 ≤ c_Z ∧ 0 < K_1 ∧ 0 < K_early ∧ 0 < K_err ∧
      ∀ {c' T R : ℝ} {g : ℝ → ℝ}, c_Z ≤ c' →
        virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
        LowerViolator virasoroPhi c' T →
        T ≤ virasoroDeltaChart c' (-virasoroAThr) →
        LowerRadiusRange virasoroC1 c' R →
        let h : ℝ → ℝ := fun ζ => (boasH c' g (ζ : ℂ)).re
        AEStronglyMeasurable h (volume.restrict (Ici (zetaMin c'))) ∧
        (∀ {ζ : ℝ}, zetaMin c' ≤ ζ → 0 ≤ h ζ) ∧
        IntegrableOn (fun ζ => lowerPζ c' R ζ * h ζ) (Ici (zetaMin c')) ∧
        (∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ) ≤ K_1 * c' ^ (-(1 / 3 : ℝ)) ∧
        (∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ) ≤
          K_early * c' ^ (-(4 / 3 : ℝ)) ∧
        |(∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ) -
            lowerBand virasoroProblem Gout virasoroPhi virasoroUhat c' R g| ≤
          K_err * c' ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨c_M, K_M, hcM_max, hKM_pos, hM⟩ := virasoro_moments_any_radius
  obtain ⟨c_B, C_B, hcB_10, hCB_pos, hB⟩ := lowerP0_mul_boasH_asymptotic
  obtain ⟨c_T, C_P, hcT_tap, _, hPζ_props⟩ := lowerPζ_properties
  obtain ⟨c_thr, hc_thr1, hc_thr⟩ := boasThreshold_eq_boasT_zetaMin
  have htap_C0 : 10000 ≤ taperC0 := by linarith only [taperC0_ge]
  have hc1_pos : 0 < virasoroC1 := virasoroC1_pos
  have hc1_bv : 10 * virasoroC1 ≤ virasoroBV := virasoroC1_small.trans virasoroBVChoice_le
  have h4c1_bv : 4 * virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by
    have hsq : (10 * virasoroC1) ^ 2 ≤ virasoroBV ^ 2 := pow_le_pow_left₀ (by positivity) hc1_bv 2
    nlinarith only [hsq]
  -- Large `c'` conditions for taper/moment/threshold comparisons
  have hev : ∀ᶠ c' : ℝ in atTop,
      C_B * c' ^ (-1 : ℝ) ≤ 1 / 2 ∧
      virasoroAThr ≤ c' ^ (4 / 7 : ℝ) ∧
      2 * c' ^ (4 / 7 : ℝ) ≤ (1 / 2) * (virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) ∧
      c' ^ (4 / 7 : ℝ) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      max (max c_M c_B) (max c_T c_thr) ≤ c' := by
    have hc21 := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 21)
    have h47a := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 7)
    have hcm1 : Tendsto (fun c' : ℝ => C_B * c' ^ (-1 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop zero_lt_one).const_mul _
    have h47 : ∀ᶠ c' : ℝ in atTop, 2 * c' ^ (4 / 7 : ℝ) ≤ (1 / 2) * (virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ),
        (hc21.const_mul_atTop (div_pos (sq_pos_of_pos hc1_pos) (by norm_num) : 0 < virasoroC1 ^ 2 / 4)).eventually_ge_atTop 1] with c' hc0 h21
      have hpow : c' ^ (2 / 3 : ℝ) = c' ^ (2 / 21 : ℝ) * c' ^ (4 / 7 : ℝ) := by
        rw [← Real.rpow_add hc0]; congr 1; norm_num
      have h1 : c' ^ (4 / 7 : ℝ) ≤ (virasoroC1 ^ 2 / 4 * c' ^ (2 / 21 : ℝ)) * c' ^ (4 / 7 : ℝ) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hc0.le _) h21
      nlinarith only [h1, hpow]
    filter_upwards [hcm1.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < 1 / 2)),
      h47a.eventually_ge_atTop virasoroAThr, h47, eventually_ge_atTop _] with c' hcb hthr' h47' hmx
    refine ⟨hcb, hthr', h47', ?_, hmx⟩
    have hc47_nn : 0 ≤ c' ^ (4 / 7 : ℝ) := by positivity
    linarith only [h47', hc47_nn]
  obtain ⟨c_Z0, hc_Z0⟩ := eventually_atTop.mp hev
  let K_1 : ℝ := 6 * K_M
  let K_early : ℝ := 8 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * K_M + 1
  let K_err : ℝ := 9 * C_B * K_M + 1
  have hKe_pos : 0 < K_early := by
    dsimp [K_early]
    have hz := zpow_pos (sq_pos_of_pos hc1_pos) (-11 : ℤ)
    positivity
  refine ⟨max c_Z0 (max virasoroCQEnv 10000), K_1, K_early, K_err,
    le_max_right _ _, by positivity, hKe_pos, by positivity,
    fun {c' T R g} hc' hwf hviol hT_hi hR => ?_⟩
  obtain ⟨hCB_half, h47_thr, h47_half, h47_min, hmx⟩ := hc_Z0 c' ((le_max_left _ _).trans hc')
  have hc_M : c_M ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hmx)
  have hc_B : c_B ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hmx)
  have hc_T : c_T ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hmx)
  have hc_thr' : c_thr ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans hmx)
  have hc_tap : taperC0 ≤ c' := hcT_tap.trans hc_T
  have hc10000 : 10000 ≤ c' := htap_C0.trans hc_tap
  have hc0 : 0 < c' := by linarith only [hc10000]
  have hc1 : 1 ≤ c' := by linarith only [hc10000]
  obtain ⟨hT_lo, hT_a1, hR_thr, hR_AC, hT_R, hmom_bd, hB1_nn, hB2_nn, hM_pos, hdm_int_thr⟩ :=
    hM hc_M hwf hviol hT_hi hR
  have hR_pos : 0 < R := virasoroAThr_pos.trans_le hR_thr
  have hRm : -R ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith only [hR_AC], by linarith only [hR_pos, sq_nonneg (virasoroAC c')]⟩
  have hAThr_m : -virasoroAThr ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith only [hR_thr, hR_AC], by linarith only [virasoroAThr_pos, sq_nonneg (virasoroAC c')]⟩
  have hΔ0_pos : 0 < virasoroDeltaChart c' 0 :=
    virasoroDeltaChart_pos hc0 (by rw [abs_zero]; exact sq_nonneg _)
  set dm : ℝ → ℝ := fun t => g t * virasoroProblem.cardyV (c' / 12) t / virasoroProblem.cardyNorm (c' / 12) g
  have hdm_nn : ∀ {t : ℝ}, T ≤ t → 0 ≤ dm t := fun {t} ht =>
    div_nonneg (mul_nonneg (hwf.2.2.2 t ht)
      (virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith)
        (hΔ0_pos.le.trans (hT_lo.trans ht))))
      hM_pos.le
  -- Check `T ≤ boasThreshold c' ≤ virasoroDeltaChart c' (-R)`
  have hthr_eq : boasThreshold c' = boasT c' (zetaMin c') := hc_thr hc_thr'
  have h47_AC : c' ^ (4 / 7 : ℝ) ≤ virasoroAC c' ^ 2 := by
    rw [virasoroAC_sq c' hc0.le]
    have hc1_bv_sq : virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by linarith only [h4c1_bv, sq_nonneg virasoroC1]
    have hc23_nn : 0 ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    calc c' ^ (4 / 7 : ℝ) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := h47_min
      _ ≤ 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := by gcongr
  have hthr_m : -(c' ^ (4 / 7 : ℝ)) ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith only [h47_AC], by linarith only [Real.rpow_pos_of_pos hc0 (4 / 7 : ℝ), sq_nonneg (virasoroAC c')]⟩
  have hthr_le_ΔR : boasThreshold c' ≤ virasoroDeltaChart c' (-R) := by
    unfold boasThreshold
    have h47_R : c' ^ (4 / 7 : ℝ) ≤ R := h47_min.trans hR.1
    exact (virasoroDeltaChart_strictAnti hc0).antitoneOn hRm hthr_m (by linarith only [h47_R])
  have hT_thr : T ≤ boasThreshold c' := by
    unfold boasThreshold
    exact hT_hi.trans ((virasoroDeltaChart_strictAnti hc0).antitoneOn hthr_m hAThr_m (by linarith only [h47_thr]))
  -- `boasH` measurability and nonnegativity on `Ici (zetaMin c')`
  dsimp only []
  set h : ℝ → ℝ := fun ζ => (boasH c' g (ζ : ℂ)).re
  have h_nn : ∀ {ζ : ℝ}, zetaMin c' ≤ ζ → 0 ≤ h ζ := fun {ζ} hζ =>
    (hB hc_B hwf hT_hi hζ).1
  have h_cont : ContinuousOn h (Ici (zetaMin c')) := by
    have hsub : MapsTo (fun ζ : ℝ => (ζ : ℂ)) (Ici (zetaMin c')) (zetaStrip c') :=
      fun ζ hζ => mem_zetaStrip_of_log_im hc10000
        ((zetaMin_pos hc0).trans_le hζ) (by simpa using Real.log_nonneg hc1)
    have hdiff := (differentiableOn_boasH (by linarith only [hc10000]) hwf.1).continuousOn
    exact Complex.continuous_re.continuousOn.comp (hdiff.comp Complex.continuous_ofReal.continuousOn hsub)
  have h_aesm : AEStronglyMeasurable h (volume.restrict (Ici (zetaMin c'))) :=
    h_cont.aestronglyMeasurable measurableSet_Ici
  -- Taper/density properties on `Ici (zetaMin c')`
  obtain ⟨W1, W2, _, hW_spec⟩ := taperWζ_bounds_and_derivs hc_tap hR
  obtain ⟨P1, P2, _, hP_spec, _⟩ := hPζ_props hc_T hR
  have hPζ_cont : ContinuousOn (lowerPζ c' R) (Ici (zetaMin c')) := by
    intro ζ hζ
    have hz_half : zetaMin c' / 2 ≤ ζ := by
      have : 0 < zetaMin c' := zetaMin_pos hc0
      linarith only [this, mem_Ici.mp hζ]
    exact (hP_spec hz_half).2.1.continuousAt.continuousWithinAt
  have hPh_cont : ContinuousOn (fun ζ => lowerPζ c' R ζ * h ζ) (Ici (zetaMin c')) :=
    hPζ_cont.mul h_cont
  -- Change of variables on `Ioi (zetaMin c')` for `t = boasT c' ζ`
  obtain ⟨hT_deriv, hT_mono, hT_img⟩ := boasT_deriv_and_image hc0
  have hT_derivW : ∀ ζ ∈ Ioi (zetaMin c'), HasDerivWithinAt (boasT c') (boasT' c' ζ) (Ioi (zetaMin c')) ζ :=
    fun ζ hζ => (hT_deriv ((zetaMin_pos hc0).trans hζ)).1.hasDerivWithinAt
  have hT_inj : InjOn (boasT c') (Ioi (zetaMin c')) :=
    hT_mono.injOn.mono (Ioi_subset_Ioi (zetaMin_pos hc0).le)
  have hT_img_thr : boasT c' '' Ioi (zetaMin c') = Ioi (boasThreshold c') := by
    rw [hT_img, ← hthr_eq]
  let w : ℝ → ℝ := fun t => lowerTaper virasoroPhi virasoroUhat c' R t
  have hw_Icc : ∀ {ζ : ℝ}, zetaMin c' / 2 ≤ ζ → w (boasT c' ζ) ∈ Icc (0 : ℝ) 1 := by
    intro ζ hζ
    have hζ_pos : 0 < ζ := (half_pos (zetaMin_pos hc0)).trans_le hζ
    have hweq : w (boasT c' ζ) = taperWζ c' R ζ := lowerTaper_zeta_eq hc_tap hR hζ_pos
    rw [hweq]
    exact ⟨(hW_spec hζ).1.le, (hW_spec hζ).2.1⟩
  let dm_ζ : ℝ → ℝ := fun ζ => boasT' c' ζ * dm (boasT c' ζ)
  have hdm_ζ_int : IntegrableOn dm_ζ (Ioi (zetaMin c')) := by
    have h1 := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hT_derivW hT_inj dm).mp (hT_img_thr.symm ▸ hdm_int_thr)
    refine h1.congr_fun (fun ζ hζ => ?_) measurableSet_Ioi
    have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans hζ
    rw [smul_eq_mul, abs_of_pos (hT_deriv hζ_pos).2]
  -- Pointwise comparison between `lowerP0 c' ζ * h ζ` and `dm_ζ ζ`
  have hP0H_ub : ∀ {ζ : ℝ}, zetaMin c' ≤ ζ →
      0 ≤ lowerP0 c' ζ * h ζ ∧ lowerP0 c' ζ * h ζ ≤ 2 * dm_ζ ζ := by
    intro ζ hζ
    have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans_le hζ
    have hP0_pos : 0 < lowerP0 c' ζ := lowerP0_pos hc0 hζ_pos
    have hB_ζ := hB hc_B hwf hT_hi hζ
    have hdm_ζ_nn : 0 ≤ dm_ζ ζ := by
      have hT_ζ : T ≤ boasT c' ζ :=
        hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn (zetaMin_pos hc0) hζ_pos hζ)
      exact mul_nonneg (hT_deriv hζ_pos).2.le (hdm_nn hT_ζ)
    have hdiff_ub : |lowerP0 c' ζ * h ζ - dm_ζ ζ| ≤ (1 / 2 : ℝ) * dm_ζ ζ := by
      calc |lowerP0 c' ζ * h ζ - dm_ζ ζ|
          ≤ C_B * c' ^ (-1 : ℝ) * dm_ζ ζ := hB_ζ.2.2
        _ ≤ (1 / 2 : ℝ) * dm_ζ ζ := by gcongr
    refine ⟨mul_nonneg hP0_pos.le hB_ζ.1, ?_⟩
    linarith only [(abs_le.mp hdiff_ub).2, hdm_ζ_nn]
  -- Integrability of `lowerPζ c' R ζ * h ζ`
  have hPh_eq : ∀ {ζ : ℝ}, 0 < ζ → lowerPζ c' R ζ * h ζ = w (boasT c' ζ) * (lowerP0 c' ζ * h ζ) := by
    intro ζ _; unfold lowerPζ w boasT; ring
  have hPh_int_Ioi : IntegrableOn (fun ζ => lowerPζ c' R ζ * h ζ) (Ioi (zetaMin c')) := by
    refine (hdm_ζ_int.const_mul 2).mono'
      ((hPh_cont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ζ hζ
    have hzmin_pos : 0 < zetaMin c' := zetaMin_pos hc0
    have hζ_pos : 0 < ζ := hzmin_pos.trans hζ
    have hζ_le : zetaMin c' ≤ ζ := (mem_Ioi.mp hζ).le
    have hζ_half : zetaMin c' / 2 ≤ ζ := by linarith only [hzmin_pos, hζ_le]
    have hw := hw_Icc hζ_half
    have hP0 := hP0H_ub hζ_le
    rw [hPh_eq hζ_pos, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1, abs_of_nonneg hP0.1]
    have hdm_ζ_nn : 0 ≤ dm_ζ ζ := by
      have hT_ζ : T ≤ boasT c' ζ :=
        hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn (zetaMin_pos hc0) hζ_pos hζ_le)
      exact mul_nonneg (hT_deriv hζ_pos).2.le (hdm_nn hT_ζ)
    rw [Real.norm_of_nonneg (by positivity)]
    calc w (boasT c' ζ) * (lowerP0 c' ζ * h ζ) ≤ 1 * (2 * dm_ζ ζ) :=
          mul_le_mul hw.2 hP0.2 hP0.1 zero_le_one
      _ = 2 * dm_ζ ζ := one_mul _
  have hPh_int_Ici : IntegrableOn (fun ζ => lowerPζ c' R ζ * h ζ) (Ici (zetaMin c')) :=
    MeasureTheory.integrableOn_Ici_iff_integrableOn_Ioi.mpr hPh_int_Ioi
  -- Coordinate `ζ_R0 := zetaOfV R` corresponding to `virasoroDeltaChart c' (-R)`
  let ζ_R0 : ℝ := zetaOfV R
  have hζR0_pos : 0 < ζ_R0 := zetaOfV_pos hR_pos
  have hv_ζR0 : vOfZeta ζ_R0 = R := vOfZeta_zetaOfV hR_pos.le
  have hR5 : vOfZeta ζ_R0 ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rw [hv_ζR0]
    have : R ≤ 4 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := hR.2
    have hc23_nn : 0 ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    nlinarith only [this, hc23_nn, sq_nonneg virasoroC1]
  have hT_ζR0 : boasT c' ζ_R0 = virasoroDeltaChart c' (-R) := by
    rw [← hv_ζR0, virasoro_delta_xOfZeta hc0 hζR0_pos hR5]
  -- Useful relation: `ζ ≤ ζ_R0 → -virasoroUT c' (boasT c' ζ) = vOfZeta ζ`
  have hut_boasT : ∀ {ζ : ℝ}, 0 < ζ → ζ ≤ ζ_R0 →
      -virasoroUT c' (boasT c' ζ) = vOfZeta ζ := by
    intro ζ hζ hζR0
    have hv_le : vOfZeta ζ ≤ R := by
      rw [← hv_ζR0]
      unfold vOfZeta
      exact Real.rpow_le_rpow (by positivity) (by gcongr) (by norm_num)
    have hv5 : vOfZeta ζ ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
      have hc23_nn : 0 ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
      have : R ≤ 4 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := hR.2
      nlinarith only [hv_le, this, hc23_nn, sq_nonneg virasoroC1]
    have hΔ_eq : boasT c' ζ = virasoroDeltaChart c' (-vOfZeta ζ) :=
      (virasoro_delta_xOfZeta hc0 hζ hv5).symm
    have hv_pos := vOfZeta_pos hζ
    have hv_AC : vOfZeta ζ ≤ virasoroAC c' ^ 2 := hv_le.trans hR_AC
    have hm1 : -(virasoroAC c' ^ 2) ≤ -vOfZeta ζ := by linarith only [hv_AC]
    have hm2 : -vOfZeta ζ ≤ 0 := by linarith only [hv_pos]
    have hΔ0_le : virasoroDeltaChart c' 0 ≤ virasoroDeltaChart c' (-vOfZeta ζ) :=
      (virasoroDeltaChart_strictAnti hc0).antitoneOn ⟨hm1, by linarith [sq_nonneg (virasoroAC c')]⟩
        ⟨by linarith [sq_nonneg (virasoroAC c')], sq_nonneg _⟩ hm2
    obtain ⟨hmem_u, h_ut⟩ := virasoroUT_between hc0 hm1 (sq_nonneg _) hm2 hΔ0_le hΔ_eq.le
    have hmem_u' : virasoroUT c' (boasT c' ζ) ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
      ⟨hm1.trans hmem_u.1, hmem_u.2.trans (sq_nonneg _)⟩
    have hinj := (virasoroDeltaChart_strictAnti hc0).injOn hmem_u'
      ⟨hm1, by linarith [sq_nonneg (virasoroAC c')]⟩ (by rw [hΔ_eq, h_ut])
    linarith only [hinj]
  -- Moment kernel `k(t)` matching `B₁ + B₂`
  let k : ℝ → ℝ := fun t => if t ≤ virasoroDeltaChart c' (-R) then 3 * (R⁻¹ * (-virasoroUT c' t)) else 1
  have hw_le_k : ∀ {ζ : ℝ}, zetaMin c' ≤ ζ → w (boasT c' ζ) ≤ k (boasT c' ζ) := by
    intro ζ hζ
    have hzmin_pos : 0 < zetaMin c' := zetaMin_pos hc0
    have hζ_pos : 0 < ζ := hzmin_pos.trans_le hζ
    have hζ_half : zetaMin c' / 2 ≤ ζ := by linarith only [hzmin_pos, hζ]
    have hweq : w (boasT c' ζ) = taperWζ c' R ζ := lowerTaper_zeta_eq hc_tap hR hζ_pos
    dsimp [k]
    split_ifs with hle
    · have hζ_le_R0 : ζ ≤ ζ_R0 := by
        rw [← hT_ζR0] at hle
        exact (hT_mono.le_iff_le hζ_pos hζR0_pos).mp hle
      have hut_eq := hut_boasT hζ_pos hζ_le_R0
      rw [hweq, hut_eq]
      by_cases htap : ζ ≤ zetaR c' R
      · obtain ⟨hW12, htv_lo, htv_hi⟩ := (hW_spec hζ_half).2.2.1 htap
        by_cases htv_R : taperV c' ζ ≤ R
        · have hdiv1 : taperV c' ζ / R ≤ 1 := (div_le_one hR_pos).mpr htv_R
          have hdiv_nn : 0 ≤ taperV c' ζ / R :=
            div_nonneg (by linarith only [htv_lo, (vOfZeta_pos hζ_pos).le]) hR_pos.le
          have hpow12 : (taperV c' ζ / R) ^ 12 ≤ taperV c' ζ / R :=
            pow_le_of_le_one hdiv_nn hdiv1 (by norm_num)
          calc taperWζ c' R ζ ≤ 2 * (taperV c' ζ / R) ^ 12 := hW12
            _ ≤ 2 * (taperV c' ζ / R) := by gcongr
            _ ≤ 2 * ((3 / 2 : ℝ) * vOfZeta ζ / R) := by gcongr
            _ = 3 * (R⁻¹ * vOfZeta ζ) := by ring
        · have hR_lt : R < taperV c' ζ := lt_of_not_ge htv_R
          calc taperWζ c' R ζ ≤ 1 := (hW_spec hζ_half).2.1
            _ ≤ taperV c' ζ / R := (one_le_div hR_pos).mpr hR_lt.le
            _ ≤ (3 / 2 : ℝ) * vOfZeta ζ / R := by gcongr
            _ ≤ 3 * (R⁻¹ * vOfZeta ζ) := by
                have := (vOfZeta_pos hζ_pos).le; rw [inv_mul_eq_div]; linarith only [this, hR_pos]
      · obtain ⟨_, _, _, _, _, hneg_uR, _, _⟩ := taper_R_phi_bounds hc_tap hR
        have htap_gt : zetaR c' R < ζ := lt_of_not_ge htap
        have huR_le_v : -(virasoroPhi c' (-R)).re ≤ vOfZeta ζ := by
          have hv_zr : vOfZeta (zetaR c' R) = -(virasoroPhi c' (-R)).re := by
            unfold zetaR; exact vOfZeta_zetaOfV (by linarith only [hneg_uR])
          rw [← hv_zr]
          unfold vOfZeta
          exact Real.rpow_le_rpow (by positivity) (by gcongr) (by norm_num)
        have hR2 : R ≤ 2 * vOfZeta ζ := by
          have : (1 / 2 : ℝ) * R ≤ -(virasoroPhi c' (-R)).re :=
            (taper_R_phi_bounds hc_tap hR).2.1
          linarith only [this, huR_le_v]
        calc taperWζ c' R ζ ≤ 1 := (hW_spec hζ_half).2.1
          _ ≤ 2 * (R⁻¹ * vOfZeta ζ) := by rw [inv_mul_eq_div, mul_div_assoc']; exact (one_le_div hR_pos).mpr hR2
          _ ≤ 3 * (R⁻¹ * vOfZeta ζ) := by
              have : 0 ≤ R⁻¹ * vOfZeta ζ := mul_nonneg (inv_nonneg.mpr hR_pos.le) (vOfZeta_pos hζ_pos).le
              linarith only [this]
    · have h1 := (hw_Icc hζ_half).2
      exact h1
  -- Continuity of `-virasoroUT c'` and `dm` on `[T, Δ(-R)]`
  have hAC_mem : -(virasoroAC c' ^ 2) ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨le_rfl, by linarith [sq_nonneg (virasoroAC c')]⟩
  have hut_cont_TR : ContinuousOn (fun t => -virasoroUT c' t) (Icc T (virasoroDeltaChart c' (-R))) := by
    intro t ht
    have hu_t := virasoroUT_between hc0 (le_rfl : -(virasoroAC c' ^ 2) ≤ -(virasoroAC c' ^ 2))
      (sq_nonneg _) (by linarith [sq_nonneg (virasoroAC c')]) (hT_lo.trans ht.1)
      (ht.2.trans ((virasoroDeltaChart_strictAnti hc0).antitoneOn hAC_mem hRm hRm.1))
    have hdiv := virasoroDeltaChart_div_mem hc0 (abs_le.mpr ⟨hu_t.1.1, hu_t.1.2.trans (sq_nonneg _)⟩)
    rw [hu_t.2] at hdiv
    have hξ_open : ((t / c' : ℝ) : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |t / c' - xiBar| ≤ virasoroChartR0 := abs_le.mpr ⟨by linarith [hdiv.1], by linarith [hdiv.2]⟩
      exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
    have hcont_at : ContinuousAt (fun x : ℝ => virasoroUChart c' (x / c')) t := by
      unfold virasoroUChart
      have hcomp := (virasoroUInf_an _ hξ_open).continuousAt.comp_of_eq
        (Complex.continuous_ofReal.comp (continuous_id.div_const c')).continuousAt rfl
      exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hcomp)
    exact hcont_at.neg.continuousWithinAt
  have hdm_cont_TR : ContinuousOn dm (Icc T (virasoroDeltaChart c' (-R))) :=
    ((hwf.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
      fun t ht => hΔ0_pos.le.trans (hT_lo.trans ht.1)).div_const _
  -- Integrability and `3 K_M c'^{-1/3}` bound for `k (boasT c' ζ) * dm_ζ ζ`
  have hk_dm_bound : IntegrableOn (fun ζ => k (boasT c' ζ) * dm_ζ ζ) (Ioi (zetaMin c')) ∧
      (∫ ζ in Ioi (zetaMin c'), k (boasT c' ζ) * dm_ζ ζ) ≤ 3 * K_M * c' ^ (-(1 / 3 : ℝ)) := by
    have hk_cont_lo : ContinuousOn (fun t => 3 * (R⁻¹ * (-virasoroUT c' t)) * dm t)
        (Icc T (virasoroDeltaChart c' (-R))) :=
      (continuousOn_const.mul (continuousOn_const.mul hut_cont_TR)).mul hdm_cont_TR
    have hk_int_Ioc : IntegrableOn (fun t => k t * dm t) (Ioc (boasThreshold c') (virasoroDeltaChart c' (-R))) := by
      have h1 : IntegrableOn (fun t => 3 * (R⁻¹ * (-virasoroUT c' t)) * dm t)
          (Ioc (boasThreshold c') (virasoroDeltaChart c' (-R))) :=
        (hk_cont_lo.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hT_thr))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioc
      dsimp [k]; simp only [ht.2, ↓reduceIte]
    have hk_int_Ioi_tail : IntegrableOn (fun t => k t * dm t) (Ioi (virasoroDeltaChart c' (-R))) := by
      have h1 := hdm_int_thr.mono_set (Ioi_subset_Ioi hthr_le_ΔR)
      refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have hnot : ¬ (t ≤ virasoroDeltaChart c' (-R)) := not_le.mpr (mem_Ioi.mp ht)
      dsimp [k]; simp only [hnot, ↓reduceIte, one_mul]
    have hk_int_t : IntegrableOn (fun t => k t * dm t) (Ioi (boasThreshold c')) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hthr_le_ΔR]
      exact hk_int_Ioc.union hk_int_Ioi_tail
    have hk_int_ζ : IntegrableOn (fun ζ => k (boasT c' ζ) * dm_ζ ζ) (Ioi (zetaMin c')) := by
      have h1 := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
        measurableSet_Ioi hT_derivW hT_inj (fun t => k t * dm t)).mp (hT_img_thr.symm ▸ hk_int_t)
      refine h1.congr_fun (fun ζ hζ => ?_) measurableSet_Ioi
      rw [smul_eq_mul, abs_of_pos (hT_deriv ((zetaMin_pos hc0).trans hζ)).2]
      dsimp [dm_ζ]; ring
    have hk_eq_img : ∫ ζ in Ioi (zetaMin c'), k (boasT c' ζ) * dm_ζ ζ =
        ∫ t in Ioi (boasThreshold c'), k t * dm t := by
      rw [← hT_img_thr, MeasureTheory.integral_image_eq_integral_abs_deriv_smul
        measurableSet_Ioi hT_derivW hT_inj (fun t => k t * dm t)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun ζ hζ => ?_
      rw [smul_eq_mul, abs_of_pos (hT_deriv ((zetaMin_pos hc0).trans hζ)).2]
      dsimp [dm_ζ]; ring
    have hk_bd_lo : ∫ t in Ioc (boasThreshold c') (virasoroDeltaChart c' (-R)), k t * dm t ≤
        3 * virasoroBandB1 c' R T g := by
      have heq : ∫ t in Ioc (boasThreshold c') (virasoroDeltaChart c' (-R)), k t * dm t =
          3 * (R⁻¹ * (virasoroProblem.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in Ioc (boasThreshold c') (virasoroDeltaChart c' (-R)),
              (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)) := by
        have h0 : (fun t => k t * dm t) =ᶠ[ae (volume.restrict (Ioc (boasThreshold c') (virasoroDeltaChart c' (-R))))]
            fun t => (3 * (R⁻¹ * (virasoroProblem.cardyNorm (c' / 12) g)⁻¹)) *
              ((-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t)) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          dsimp [k, dm]; simp only [ht.2, ↓reduceIte]; ring
        rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc h0, MeasureTheory.integral_const_mul]
        ring
      have hsub_int : ∫ t in Ioc (boasThreshold c') (virasoroDeltaChart c' (-R)),
            (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t) ≤
          ∫ t in T..(virasoroDeltaChart c' (-R)),
            (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t) := by
        rw [intervalIntegral.integral_of_le hT_R]
        have hint_TR : IntegrableOn (fun t => (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t))
            (Ioc T (virasoroDeltaChart c' (-R))) := by
          have hc_ut : ContinuousOn (fun t => (-virasoroUT c' t) * (g t * virasoroProblem.cardyV (c' / 12) t))
              (Icc T (virasoroDeltaChart c' (-R))) :=
            hut_cont_TR.mul ((hwf.1.cont.mul (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).mono
              fun t ht => hΔ0_pos.le.trans (hT_lo.trans ht.1))
          exact hc_ut.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        refine MeasureTheory.setIntegral_mono_set hint_TR ?_ (Ioc_subset_Ioc_left hT_thr).eventuallyLE
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have hu := (virasoroUT_between hc0 hRm.1 (sq_nonneg _) (by linarith only [hR_pos])
          (hT_lo.trans ht.1) ht.2).1
        have hut_nn : 0 ≤ -virasoroUT c' t := by linarith only [hu.2]
        have hg_nn := hwf.2.2.2 t ht.1
        have hV_nn := virasoroProblem.cardyV_nonneg (by rw [virasoroProblem_totalShift]; linarith)
          (hΔ0_pos.le.trans (hT_lo.trans ht.1))
        exact mul_nonneg hut_nn (mul_nonneg hg_nn hV_nn)
      rw [heq]
      unfold virasoroBandB1
      gcongr
    have hk_bd_tail : ∫ t in Ioi (virasoroDeltaChart c' (-R)), k t * dm t = virasoroBandB2 c' R g := by
      have h0 : (fun t => k t * dm t) =ᶠ[ae (volume.restrict (Ioi (virasoroDeltaChart c' (-R))))] dm := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hnot : ¬ (t ≤ virasoroDeltaChart c' (-R)) := not_le.mpr (mem_Ioi.mp ht)
        dsimp [k]; simp only [hnot, ↓reduceIte, one_mul]
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi h0, MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici]
      unfold virasoroBandB2
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext t; dsimp [dm]; ring
    have hk_split : ∫ t in Ioi (boasThreshold c'), k t * dm t =
        (∫ t in Ioc (boasThreshold c') (virasoroDeltaChart c' (-R)), k t * dm t) +
          ∫ t in Ioi (virasoroDeltaChart c' (-R)), k t * dm t := by
      conv_lhs => rw [← Set.Ioc_union_Ioi_eq_Ioi hthr_le_ΔR]
      exact MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hk_int_Ioc hk_int_Ioi_tail
    refine ⟨hk_int_ζ, ?_⟩
    rw [hk_eq_img, hk_split, hk_bd_tail]
    linarith only [hk_bd_lo, hB2_nn, hmom_bd]
  -- Total bound on `Ici (zetaMin c')`
  have h_total_bd : ∫ ζ in Ici (zetaMin c'), lowerPζ c' R ζ * h ζ ≤ K_1 * c' ^ (-(1 / 3 : ℝ)) := by
    rw [MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici.symm]
    have hmono_int : ∫ ζ in Ioi (zetaMin c'), lowerPζ c' R ζ * h ζ ≤
        ∫ ζ in Ioi (zetaMin c'), 2 * (k (boasT c' ζ) * dm_ζ ζ) := by
      refine MeasureTheory.setIntegral_mono_on hPh_int_Ioi (hk_dm_bound.1.const_mul 2) measurableSet_Ioi
        fun ζ hζ => ?_
      have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans hζ
      have hζ_le : zetaMin c' ≤ ζ := (mem_Ioi.mp hζ).le
      have hdm_ζ_nn : 0 ≤ dm_ζ ζ :=
        mul_nonneg (hT_deriv hζ_pos).2.le
          (hdm_nn (hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn (zetaMin_pos hc0) hζ_pos hζ_le)))
      have hw_nn : 0 ≤ w (boasT c' ζ) := (hw_Icc (by linarith [zetaMin_pos hc0, hζ_le])).1
      calc lowerPζ c' R ζ * h ζ = w (boasT c' ζ) * (lowerP0 c' ζ * h ζ) := hPh_eq hζ_pos
        _ ≤ k (boasT c' ζ) * (2 * dm_ζ ζ) :=
            mul_le_mul (hw_le_k hζ_le) (hP0H_ub hζ_le).2 (hP0H_ub hζ_le).1
              (hw_nn.trans (hw_le_k hζ_le))
        _ = 2 * (k (boasT c' ζ) * dm_ζ ζ) := by ring
    rw [MeasureTheory.integral_const_mul] at hmono_int
    calc ∫ ζ in Ioi (zetaMin c'), lowerPζ c' R ζ * h ζ
        ≤ 2 * ∫ ζ in Ioi (zetaMin c'), k (boasT c' ζ) * dm_ζ ζ := hmono_int
      _ ≤ 2 * (3 * K_M * c' ^ (-(1 / 3 : ℝ))) := by gcongr; exact hk_dm_bound.2
      _ = K_1 * c' ^ (-(1 / 3 : ℝ)) := by dsimp [K_1]; ring
  -- Early-layer bound on `[zetaMin c', 2 * zetaMin c']`
  have h_early_bd : ∫ ζ in Icc (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ ≤
      K_early * c' ^ (-(4 / 3 : ℝ)) := by
    have hzmin_pos : 0 < zetaMin c' := zetaMin_pos hc0
    have h2z_lt : zetaMin c' < 2 * zetaMin c' := by linarith only [hzmin_pos]
    have hv_2z : vOfZeta (2 * zetaMin c') ≤ 2 * c' ^ (4 / 7 : ℝ) := by
      unfold vOfZeta zetaMin
      have hpi := Real.pi_pos.ne'
      rw [show 3 * π * (2 * (2 / (3 * π) * c' ^ (6 / 7 : ℝ))) / 2 = 2 * c' ^ (6 / 7 : ℝ) by field_simp [hpi],
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul hc0.le, show (6 / 7 : ℝ) * (2 / 3 : ℝ) = 4 / 7 by norm_num]
      have h223 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      gcongr
    have hR1_lo : virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR.1
    have h2z_le_ζR : 2 * zetaMin c' ≤ zetaR c' R := by
      obtain ⟨_, _, _, _, _, hneg_uR, _, _⟩ := taper_R_phi_bounds hc_tap hR
      have h1 : (1 / 2 : ℝ) * R ≤ -(virasoroPhi c' (-R)).re := (taper_R_phi_bounds hc_tap hR).2.1
      have hv_le_uR : vOfZeta (2 * zetaMin c') ≤ -(virasoroPhi c' (-R)).re := by
        have hhalf : (1 / 2 : ℝ) * (virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) ≤ (1 / 2 : ℝ) * R := by linarith only [hR1_lo]
        linarith only [hv_2z, h47_half, hhalf, h1]
      unfold zetaR
      rw [← zetaOfV_vOfZeta (by linarith only [hzmin_pos] : 0 ≤ 2 * zetaMin c')]
      exact (zetaOfV_le_iff (vOfZeta_pos (by positivity)).le (by linarith only [hneg_uR])).mpr hv_le_uR
    have h2z_le_R0 : 2 * zetaMin c' ≤ ζ_R0 := by
      have hv_le_R : vOfZeta (2 * zetaMin c') ≤ R := by
        have hhc : 0 ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by positivity
        linarith only [hv_2z, h47_half, hR1_lo, hhc]
      dsimp [ζ_R0]
      rw [← zetaOfV_vOfZeta (by linarith only [hzmin_pos] : 0 ≤ 2 * zetaMin c')]
      exact (zetaOfV_le_iff (vOfZeta_pos (by positivity)).le hR_pos.le).mpr hv_le_R
    let C_ew : ℝ := 4 * (3 * c' ^ (4 / 7 : ℝ) / R) ^ 12 * (R / c' ^ (4 / 7 : ℝ))
    have hCew_nn : 0 ≤ C_ew := by dsimp [C_ew]; positivity
    have hpt : ∀ ζ ∈ Ioo (zetaMin c') (2 * zetaMin c'),
        lowerPζ c' R ζ * h ζ ≤ C_ew * (R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ) := by
      intro ζ hζ
      have hζ_pos : 0 < ζ := hzmin_pos.trans hζ.1
      have hζ_half : zetaMin c' / 2 ≤ ζ := by linarith only [hzmin_pos, hζ.1]
      have hζ_tap : ζ ≤ zetaR c' R := hζ.2.le.trans h2z_le_ζR
      have hζ_R0 : ζ ≤ ζ_R0 := hζ.2.le.trans h2z_le_R0
      obtain ⟨hW12, htv_lo, htv_hi⟩ := (hW_spec hζ_half).2.2.1 hζ_tap
      have hv_le_2 : vOfZeta ζ ≤ 2 * c' ^ (4 / 7 : ℝ) := by
        have h1 : vOfZeta ζ ≤ vOfZeta (2 * zetaMin c') := by
          unfold vOfZeta
          exact Real.rpow_le_rpow (by positivity) (by gcongr; exact hζ.2.le) (by norm_num)
        exact h1.trans hv_2z
      have htv_3 : taperV c' ζ ≤ 3 * c' ^ (4 / 7 : ℝ) := by linarith only [htv_hi, hv_le_2]
      have htv_nn : 0 ≤ taperV c' ζ := by
        linarith only [htv_lo, (vOfZeta_pos hζ_pos).le]
      have hw_12 : w (boasT c' ζ) ≤ 2 * (3 * c' ^ (4 / 7 : ℝ) / R) ^ 12 := by
        dsimp only [w]; unfold boasT
        rw [lowerTaper_zeta_eq hc_tap hR hζ_pos]
        exact hW12.trans (by gcongr)
      have hv_lo : c' ^ (4 / 7 : ℝ) ≤ -virasoroUT c' (boasT c' ζ) := by
        rw [hut_boasT hζ_pos hζ_R0, ← vOfZeta_zetaMin hc0]
        unfold vOfZeta
        exact Real.rpow_le_rpow (by positivity) (by gcongr; exact hζ.1.le) (by norm_num)
      have hc47_pos : 0 < c' ^ (4 / 7 : ℝ) := Real.rpow_pos_of_pos hc0 _
      have h1_ut : 1 ≤ R / c' ^ (4 / 7 : ℝ) * (R⁻¹ * (-virasoroUT c' (boasT c' ζ))) := by
        have hEq : R / c' ^ (4 / 7 : ℝ) * (R⁻¹ * (-virasoroUT c' (boasT c' ζ))) =
            -virasoroUT c' (boasT c' ζ) / c' ^ (4 / 7 : ℝ) := by field_simp [hR_pos.ne', hc47_pos.ne']
        rw [hEq, one_le_div hc47_pos]
        exact hv_lo
      have hdm_ζ_nn : 0 ≤ dm_ζ ζ :=
        mul_nonneg (hT_deriv hζ_pos).2.le
          (hdm_nn (hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn hzmin_pos hζ_pos hζ.1.le)))
      have hP0_2 := (hP0H_ub hζ.1.le).2
      have hP0_nn := (hP0H_ub hζ.1.le).1
      calc lowerPζ c' R ζ * h ζ = w (boasT c' ζ) * (lowerP0 c' ζ * h ζ) := hPh_eq hζ_pos
        _ ≤ (2 * (3 * c' ^ (4 / 7 : ℝ) / R) ^ 12) * (2 * dm_ζ ζ) :=
            mul_le_mul hw_12 hP0_2 hP0_nn (by positivity)
        _ = 4 * (3 * c' ^ (4 / 7 : ℝ) / R) ^ 12 * (1 * dm_ζ ζ) := by ring
        _ ≤ 4 * (3 * c' ^ (4 / 7 : ℝ) / R) ^ 12 *
              ((R / c' ^ (4 / 7 : ℝ) * (R⁻¹ * (-virasoroUT c' (boasT c' ζ)))) * dm_ζ ζ) := by
            gcongr
        _ = C_ew * (R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ) := by dsimp [C_ew]; ring
    have h_e_int : IntegrableOn (fun ζ => lowerPζ c' R ζ * h ζ) (Ioo (zetaMin c') (2 * zetaMin c')) :=
      hPh_int_Ioi.mono_set Ioo_subset_Ioi_self
    have h_ut_dm_int : IntegrableOn (fun ζ => R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ)
        (Ioo (zetaMin c') (2 * zetaMin c')) := by
      have hsub_oo : Ioo (zetaMin c') (2 * zetaMin c') ⊆ Ioi (zetaMin c') := Ioo_subset_Ioi_self
      have h_le_k : ∀ ζ ∈ Ioo (zetaMin c') (2 * zetaMin c'),
          ‖R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ‖ ≤ ‖k (boasT c' ζ) * dm_ζ ζ‖ := by
        intro ζ hζ
        have hζ_pos : 0 < ζ := hzmin_pos.trans hζ.1
        have hζ_R0 : ζ ≤ ζ_R0 := hζ.2.le.trans h2z_le_R0
        have hT_le_R : boasT c' ζ ≤ virasoroDeltaChart c' (-R) := by
          rw [← hT_ζR0]; exact hT_mono.monotoneOn hζ_pos hζR0_pos hζ_R0
        have hdm_ζ_nn : 0 ≤ dm_ζ ζ :=
          mul_nonneg (hT_deriv hζ_pos).2.le
            (hdm_nn (hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn hzmin_pos hζ_pos hζ.1.le)))
        have hut_nn : 0 ≤ -virasoroUT c' (boasT c' ζ) := by
          rw [hut_boasT hζ_pos hζ_R0]; exact (vOfZeta_pos hζ_pos).le
        have hnorm1 : ‖R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ‖ =
            R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ :=
          Real.norm_of_nonneg (by positivity)
        have hnorm2 : ‖k (boasT c' ζ) * dm_ζ ζ‖ = 3 * (R⁻¹ * (-virasoroUT c' (boasT c' ζ))) * dm_ζ ζ := by
          dsimp [k]; simp only [hT_le_R, ↓reduceIte]
          exact Real.norm_of_nonneg (by positivity)
        rw [hnorm1, hnorm2]
        nlinarith only [show 0 ≤ R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ by positivity]
      have h_aesm : AEStronglyMeasurable (fun ζ => R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ)
          (volume.restrict (Ioo (zetaMin c') (2 * zetaMin c'))) := by
        have hcont_ut : ContinuousOn (fun ζ => -virasoroUT c' (boasT c' ζ)) (Ioo (zetaMin c') (2 * zetaMin c')) := by
          refine ContinuousOn.congr (f := fun ζ => vOfZeta ζ) ?_ (fun ζ hζ => hut_boasT (hzmin_pos.trans hζ.1) (hζ.2.le.trans h2z_le_R0))
          unfold vOfZeta
          refine ((continuousOn_const.mul continuousOn_id).div_const 2).rpow_const fun ζ hζ => Or.inl ?_
          have hzp := hzmin_pos.trans hζ.1; positivity
        have hdm_c : ContinuousOn dm_ζ (Ioo (zetaMin c') (2 * zetaMin c')) := by
          have hboas_cont : ContinuousOn (boasT c') (Ioo (zetaMin c') (2 * zetaMin c')) :=
            fun ζ hζ => (hT_deriv (hzmin_pos.trans hζ.1)).1.continuousAt.continuousWithinAt
          have hdm_c0 : ContinuousOn dm (Ioi T) :=
            ((hwf.1.cont.mono ((Ioi_subset_Ioi (hΔ0_pos.le.trans hT_lo)).trans Ioi_subset_Ici_self)).mul
              (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).div_const _
          have hm_boas : MapsTo (boasT c') (Ioo (zetaMin c') (2 * zetaMin c')) (Ioi T) :=
            fun ζ hζ => lt_of_le_of_lt hT_thr (hthr_eq ▸ hT_mono hzmin_pos (hzmin_pos.trans hζ.1) hζ.1)
          have hT'_c : ContinuousOn (boasT' c') (Ioo (zetaMin c') (2 * zetaMin c')) := by
            unfold boasT'
            have hx_c : ContinuousOn (xOfZeta c') (Ioo (zetaMin c') (2 * zetaMin c')) :=
              fun ζ hζ => (hasDerivAt_xOfZeta hc0 (hzmin_pos.trans hζ.1)).continuousAt.continuousWithinAt
            refine (continuousOn_const.mul hx_c).div (continuousOn_rhoU.comp hx_c fun ζ hζ =>
              (xOfZeta_spec hc0 (hzmin_pos.trans hζ.1)).1.le) fun ζ hζ =>
              (rhoU_pos (xOfZeta_spec hc0 (hzmin_pos.trans hζ.1)).1).ne'
          exact hT'_c.mul (hdm_c0.comp hboas_cont hm_boas)
        exact ((continuousOn_const.mul hcont_ut).mul hdm_c).aestronglyMeasurable measurableSet_Ioo
      exact (hk_dm_bound.1.mono_set hsub_oo).mono' h_aesm
        (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with ζ hζ; exact h_le_k ζ hζ)
    have h_int_oo : ∫ ζ in Ioo (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ ≤
        C_ew * virasoroBandB1 c' R T g := by
      have h1 := MeasureTheory.setIntegral_mono_on h_e_int (h_ut_dm_int.const_mul C_ew) measurableSet_Ioo
        fun ζ hζ => hpt ζ hζ
      rw [MeasureTheory.integral_const_mul] at h1
      have h2 : ∫ ζ in Ioo (zetaMin c') (2 * zetaMin c'), R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ ≤
          virasoroBandB1 c' R T g := by
        have hT_derivW_e : ∀ ζ ∈ Ioo (zetaMin c') (2 * zetaMin c'),
            HasDerivWithinAt (boasT c') (boasT' c' ζ) (Ioo (zetaMin c') (2 * zetaMin c')) ζ :=
          fun ζ hζ => (hT_deriv (hzmin_pos.trans hζ.1)).1.hasDerivWithinAt
        have hT_inj_e : InjOn (boasT c') (Ioo (zetaMin c') (2 * zetaMin c')) :=
          hT_inj.mono Ioo_subset_Ioi_self
        have heq_img : ∫ ζ in Ioo (zetaMin c') (2 * zetaMin c'), R⁻¹ * (-virasoroUT c' (boasT c' ζ)) * dm_ζ ζ =
            ∫ t in boasT c' '' Ioo (zetaMin c') (2 * zetaMin c'), R⁻¹ * (-virasoroUT c' t) * dm t := by
          rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hT_derivW_e hT_inj_e]
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun ζ hζ => ?_
          rw [smul_eq_mul, abs_of_pos (hT_deriv (hzmin_pos.trans hζ.1)).2]
          dsimp [dm_ζ]; ring
        rw [heq_img]
        have hsub_img : boasT c' '' Ioo (zetaMin c') (2 * zetaMin c') ⊆ Ioc T (virasoroDeltaChart c' (-R)) := by
          rintro t ⟨ζ, hζ, rfl⟩
          refine ⟨lt_of_le_of_lt hT_thr (hthr_eq ▸ hT_mono hzmin_pos (hzmin_pos.trans hζ.1) hζ.1), ?_⟩
          rw [← hT_ζR0]; exact hT_mono.monotoneOn (hzmin_pos.trans hζ.1) hζR0_pos (hζ.2.le.trans h2z_le_R0)
        have hint_Ioc : IntegrableOn (fun t => R⁻¹ * (-virasoroUT c' t) * dm t)
            (Ioc T (virasoroDeltaChart c' (-R))) := by
          have hc_ut : ContinuousOn (fun t => R⁻¹ * (-virasoroUT c' t) * dm t)
              (Icc T (virasoroDeltaChart c' (-R))) :=
            (continuousOn_const.mul hut_cont_TR).mul hdm_cont_TR
          exact hc_ut.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have hmono_t : ∫ t in boasT c' '' Ioo (zetaMin c') (2 * zetaMin c'), R⁻¹ * (-virasoroUT c' t) * dm t ≤
            ∫ t in Ioc T (virasoroDeltaChart c' (-R)), R⁻¹ * (-virasoroUT c' t) * dm t := by
          refine MeasureTheory.setIntegral_mono_set hint_Ioc ?_ hsub_img.eventuallyLE
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have hu := (virasoroUT_between hc0 hRm.1 (sq_nonneg _) (by linarith only [hR_pos])
            (hT_lo.trans ht.1) ht.2).1
          exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hR_pos.le) (by linarith only [hu.2])) (hdm_nn ht.1.le)
        refine hmono_t.trans_eq ?_
        rw [← intervalIntegral.integral_of_le hT_R]
        unfold virasoroBandB1
        rw [← intervalIntegral.integral_const_mul]
        congr 1; ext t; dsimp [dm]; ring
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hCew_nn)
    rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Icc.symm]
    have hB1_bd : virasoroBandB1 c' R T g ≤ K_M * c' ^ (-(1 / 3 : ℝ)) := by linarith only [hB2_nn, hmom_bd]
    have hCew_ub : C_ew ≤ 4 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * c' ^ (-(22 / 21 : ℝ)) := by
      have hc47_pos : 0 < c' ^ (4 / 7 : ℝ) := Real.rpow_pos_of_pos hc0 _
      have hCew_eq : C_ew = 4 * 3 ^ 12 * (c' ^ (4 / 7 : ℝ)) ^ 11 * R ^ (-11 : ℤ) := by
        dsimp [C_ew]
        rw [div_pow, mul_pow, zpow_neg, zpow_natCast]
        field_simp [hR_pos.ne', hc47_pos.ne']
        ring
      have hR11 : R ^ (-11 : ℤ) ≤ (virasoroC1 ^ 2) ^ (-11 : ℤ) * (c' ^ (2 / 3 : ℝ)) ^ (-11 : ℤ) := by
        have hlo : virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR.1
        have hlo_pos : 0 < virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by positivity
        have hz11 : R ^ (-11 : ℤ) ≤ (virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (-11 : ℤ) := by
          rw [zpow_neg, zpow_neg]
          exact inv_anti₀ (pow_pos hlo_pos 11) (pow_le_pow_left₀ hlo_pos.le hlo 11)
        rwa [mul_zpow] at hz11
      have hpow_c : (c' ^ (4 / 7 : ℝ)) ^ 11 * (c' ^ (2 / 3 : ℝ)) ^ (-11 : ℤ) = c' ^ (-(22 / 21 : ℝ)) := by
        rw [← Real.rpow_natCast (c' ^ (4 / 7 : ℝ)) 11, ← Real.rpow_mul hc0.le,
          ← Real.rpow_intCast (c' ^ (2 / 3 : ℝ)) (-11), ← Real.rpow_mul hc0.le,
          ← Real.rpow_add hc0]
        congr 1; norm_num
      calc C_ew = 4 * 3 ^ 12 * (c' ^ (4 / 7 : ℝ)) ^ 11 * R ^ (-11 : ℤ) := hCew_eq
        _ ≤ 4 * 3 ^ 12 * (c' ^ (4 / 7 : ℝ)) ^ 11 * ((virasoroC1 ^ 2) ^ (-11 : ℤ) * (c' ^ (2 / 3 : ℝ)) ^ (-11 : ℤ)) := by
            gcongr
        _ = 4 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * ((c' ^ (4 / 7 : ℝ)) ^ 11 * (c' ^ (2 / 3 : ℝ)) ^ (-11 : ℤ)) := by
            ring
        _ = 4 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * c' ^ (-(22 / 21 : ℝ)) := by rw [hpow_c]
    have hpow_29 : c' ^ (-(22 / 21 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc ∫ ζ in Ioo (zetaMin c') (2 * zetaMin c'), lowerPζ c' R ζ * h ζ
        ≤ C_ew * virasoroBandB1 c' R T g := h_int_oo
      _ ≤ (4 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * c' ^ (-(22 / 21 : ℝ))) * (K_M * c' ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul hCew_ub hB1_bd hB1_nn (by positivity)
      _ = (4 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * K_M) * (c' ^ (-(22 / 21 : ℝ)) * c' ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ K_early * c' ^ (-(4 / 3 : ℝ)) := by
          have h1 : 4 * 3 ^ 12 * (virasoroC1 ^ 2) ^ (-11 : ℤ) * K_M ≤ K_early := by
            dsimp [K_early]
            have hz := zpow_pos (sq_pos_of_pos hc1_pos) (-11 : ℤ)
            nlinarith only [hz, hKM_pos]
          gcongr
  -- Main band difference between `∫ A_ζ(ζ) h(ζ) dζ` and `lowerBand`
  have h_band_diff : |(∫ ζ in Ici (zetaMin c'), boasA c' R ζ ζ * h ζ) -
        lowerBand virasoroProblem Gout virasoroPhi virasoroUhat c' R g| ≤
      K_err * c' ^ (-(4 / 3 : ℝ)) := by
    let osc : ℝ → ℝ := fun ζ =>
      1 - 2 * lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' ζ)) *
        Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ))
    let oscT : ℝ → ℝ := fun t => 1 + 2 * lowerSc Gout c' (√(3 * t / c'))
    have hosc_bd : ∀ {ζ : ℝ}, 0 < ζ → |osc ζ| ≤ 3 := by
      intro ζ hζ
      have hW := lowerWeps_mem_Icc (Real.rpow_nonneg hc0.le (-2)) (xOfZeta_spec hc0 hζ).1
      have hsin := Real.abs_sin_le_one (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ))
      refine (abs_sub _ _).trans ?_
      rw [abs_one, abs_mul, abs_mul, abs_two, abs_of_nonneg hW.1]
      have hmul : lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' ζ)) *
          |Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ))| ≤ 1 := by
        calc _ ≤ 1 * 1 := mul_le_mul hW.2 hsin (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      linarith only [hmul]
    have hosc_eq_oscT : ∀ {ζ : ℝ}, 0 < ζ → oscT (boasT c' ζ) = osc ζ := by
      intro ζ hζ
      have hx_gt := (xOfZeta_spec hc0 hζ).1
      have hcum := (xOfZeta_spec hc0 hζ).2.1
      have hx_pos : 0 < xOfZeta c' ζ := xiStar_pos.trans hx_gt
      have hsqrt_x : √(3 * boasT c' ζ / c') = xOfZeta c' ζ := by
        unfold boasT
        rw [show 3 * (c' * xOfZeta c' ζ ^ 2 / 3) / c' = xOfZeta c' ζ ^ 2 by field_simp [hc0.ne'],
          Real.sqrt_sq hx_pos.le]
      dsimp [oscT, osc]
      unfold lowerSc
      rw [hsqrt_x, sin_lowerThetaEps_eq (Real.rpow_nonneg hc0.le (-2)) hx_gt,
        show 2 * π * c' * cumulN (xOfZeta c' ζ) = 2 * π * (c' * cumulN (xOfZeta c' ζ)) by ring, hcum]
      have hsin_neg : Real.sin (unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ) - 2 * π * ζ) =
          -Real.sin (2 * π * ζ - unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' ζ)) := by
        rw [← Real.sin_neg]; congr 1; ring
      rw [hsin_neg]; ring
    have hA_cont : ContinuousOn (fun ζ => boasA c' R ζ ζ) (Ioi (zetaMin c')) := by
      obtain ⟨_, _, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
      obtain ⟨_, _, θ', _, hspec⟩ := hWθ hc10000
      have hθ : ContinuousOn (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)) (Ioi 0) :=
        fun z hz => (hspec hz).2.2.1.continuousAt.continuousWithinAt
      have hW_c : ContinuousOn (fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))) (Ioi 0) :=
        fun z hz => (hspec hz).1.continuousAt.continuousWithinAt
      have hP_c : ContinuousOn (lowerPζ c' R) (Ioi (zetaMin c')) :=
        hPζ_cont.mono Ioi_subset_Ici_self
      unfold boasA
      exact hP_c.mul (continuousOn_const.sub ((continuousOn_const.mul (hW_c.mono (Ioi_subset_Ioi (zetaMin_pos hc0).le))).mul
        (Real.continuous_sin.comp_continuousOn ((continuousOn_const.mul continuousOn_id).sub
          (hθ.mono (Ioi_subset_Ioi (zetaMin_pos hc0).le))))))
    have hAh_int : IntegrableOn (fun ζ => boasA c' R ζ ζ * h ζ) (Ioi (zetaMin c')) := by
      refine (hPh_int_Ioi.const_mul 3).mono'
        ((hA_cont.mul (h_cont.mono Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ζ hζ
      have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans hζ
      have hP_nn : 0 ≤ lowerPζ c' R ζ := (hP_spec (by linarith [zetaMin_pos hc0, mem_Ioi.mp hζ])).1.le
      have hA_le := abs_boasA_le (ζ := ζ) hc0 hζ_pos hP_nn
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h_nn (mem_Ioi.mp hζ).le),
        Real.norm_of_nonneg (by positivity [hP_nn, h_nn (mem_Ioi.mp hζ).le])]
      nlinarith only [hA_le, h_nn (mem_Ioi.mp hζ).le]
    have hwdm_osc_int : IntegrableOn (fun ζ => w (boasT c' ζ) * dm_ζ ζ * osc ζ) (Ioi (zetaMin c')) := by
      have hosc_c : ContinuousOn osc (Ioi (zetaMin c')) := by
        obtain ⟨_, _, hWθ⟩ := lowerWeps_unwrappedTheta_deriv_bounds
        obtain ⟨_, _, _, _, hspec⟩ := hWθ hc10000
        have hθ : ContinuousOn (fun z => unwrappedTheta (c' ^ (-2 : ℝ)) (xOfZeta c' z)) (Ioi 0) :=
          fun z hz => (hspec hz).2.2.1.continuousAt.continuousWithinAt
        have hW_c : ContinuousOn (fun z => lowerWeps (c' ^ (-2 : ℝ)) (lowerY (xOfZeta c' z))) (Ioi 0) :=
          fun z hz => (hspec hz).1.continuousAt.continuousWithinAt
        exact continuousOn_const.sub ((continuousOn_const.mul (hW_c.mono (Ioi_subset_Ioi (zetaMin_pos hc0).le))).mul
          (Real.continuous_sin.comp_continuousOn ((continuousOn_const.mul continuousOn_id).sub
            (hθ.mono (Ioi_subset_Ioi (zetaMin_pos hc0).le)))))
      have hw_c : ContinuousOn (fun ζ => w (boasT c' ζ)) (Ioi (zetaMin c')) := by
        refine ContinuousOn.congr (f := taperWζ c' R) ?_ (fun ζ hζ =>
          lowerTaper_zeta_eq hc_tap hR ((zetaMin_pos hc0).trans hζ))
        intro ζ hζ
        exact (hW_spec (by linarith [zetaMin_pos hc0, mem_Ioi.mp hζ])).2.2.2.1.continuousAt.continuousWithinAt
      have hdm_c : ContinuousOn dm_ζ (Ioi (zetaMin c')) := by
        have hboas_cont : ContinuousOn (boasT c') (Ioi (zetaMin c')) :=
          fun ζ hζ => (hT_deriv ((zetaMin_pos hc0).trans hζ)).1.continuousAt.continuousWithinAt
        have hdm_c0 : ContinuousOn dm (Ioi T) :=
          ((hwf.1.cont.mono ((Ioi_subset_Ioi (hΔ0_pos.le.trans hT_lo)).trans Ioi_subset_Ici_self)).mul
            (continuous_cardyV virasoroProblem (c' / 12)).continuousOn).div_const _
        have hm_boas : MapsTo (boasT c') (Ioi (zetaMin c')) (Ioi T) :=
          fun ζ hζ => lt_of_le_of_lt hT_thr (hthr_eq ▸ hT_mono (zetaMin_pos hc0) ((zetaMin_pos hc0).trans hζ) hζ)
        have hT'_c : ContinuousOn (boasT' c') (Ioi (zetaMin c')) := by
          unfold boasT'
          have hx_c : ContinuousOn (xOfZeta c') (Ioi (zetaMin c')) :=
            fun ζ hζ => (hasDerivAt_xOfZeta hc0 ((zetaMin_pos hc0).trans hζ)).continuousAt.continuousWithinAt
          refine (continuousOn_const.mul hx_c).div (continuousOn_rhoU.comp hx_c fun ζ hζ =>
            (xOfZeta_spec hc0 ((zetaMin_pos hc0).trans hζ)).1.le) fun ζ hζ =>
            (rhoU_pos (xOfZeta_spec hc0 ((zetaMin_pos hc0).trans hζ)).1).ne'
        exact hT'_c.mul (hdm_c0.comp hboas_cont hm_boas)
      refine (hk_dm_bound.1.const_mul 3).mono'
        (((hw_c.mul hdm_c).mul hosc_c).aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with ζ hζ
      have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans hζ
      have hζ_le : zetaMin c' ≤ ζ := (mem_Ioi.mp hζ).le
      have hdm_ζ_nn : 0 ≤ dm_ζ ζ :=
        mul_nonneg (hT_deriv hζ_pos).2.le
          (hdm_nn (hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn (zetaMin_pos hc0) hζ_pos hζ_le)))
      have hw_nn : 0 ≤ w (boasT c' ζ) := (hw_Icc (by linarith [zetaMin_pos hc0, hζ_le])).1
      have hk_nn : 0 ≤ k (boasT c' ζ) := hw_nn.trans (hw_le_k hζ_le)
      have hnorm : ‖w (boasT c' ζ) * dm_ζ ζ * osc ζ‖ = w (boasT c' ζ) * dm_ζ ζ * |osc ζ| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hw_nn hdm_ζ_nn)]
      rw [hnorm, Real.norm_of_nonneg (by positivity)]
      calc w (boasT c' ζ) * dm_ζ ζ * |osc ζ| ≤ k (boasT c' ζ) * dm_ζ ζ * 3 :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hw_le_k hζ_le) hdm_ζ_nn) (hosc_bd hζ_pos)
              (abs_nonneg _) (mul_nonneg hk_nn hdm_ζ_nn)
        _ = 3 * (k (boasT c' ζ) * dm_ζ ζ) := by ring
    have hband_eq : lowerBand virasoroProblem Gout virasoroPhi virasoroUhat c' R g =
        ∫ ζ in Ioi (zetaMin c'), w (boasT c' ζ) * dm_ζ ζ * osc ζ := by
      unfold lowerBand
      change ∫ t in Ioi (boasThreshold c'), w t * dm t * oscT t = _
      rw [← hT_img_thr, MeasureTheory.integral_image_eq_integral_abs_deriv_smul
        measurableSet_Ioi hT_derivW hT_inj (fun t => w t * dm t * oscT t)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun ζ hζ => ?_
      have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans hζ
      rw [smul_eq_mul, abs_of_pos (hT_deriv hζ_pos).2, hosc_eq_oscT hζ_pos]
      dsimp [dm_ζ]; ring
    rw [MeasureTheory.setIntegral_congr_set Ioi_ae_eq_Ici.symm, hband_eq,
      ← MeasureTheory.integral_sub hAh_int hwdm_osc_int]
    have h_sub_le : ‖∫ ζ in Ioi (zetaMin c'), (boasA c' R ζ ζ * h ζ - w (boasT c' ζ) * dm_ζ ζ * osc ζ)‖ ≤
        ∫ ζ in Ioi (zetaMin c'), 3 * C_B * c' ^ (-1 : ℝ) * (k (boasT c' ζ) * dm_ζ ζ) := by
      refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
      refine MeasureTheory.setIntegral_mono_on (hAh_int.sub hwdm_osc_int).norm
        (hk_dm_bound.1.const_mul _) measurableSet_Ioi fun ζ hζ => ?_
      have hζ_pos : 0 < ζ := (zetaMin_pos hc0).trans hζ
      have hζ_le : zetaMin c' ≤ ζ := (mem_Ioi.mp hζ).le
      have hdm_ζ_nn : 0 ≤ dm_ζ ζ :=
        mul_nonneg (hT_deriv hζ_pos).2.le
          (hdm_nn (hT_thr.trans (hthr_eq ▸ hT_mono.monotoneOn (zetaMin_pos hc0) hζ_pos hζ_le)))
      have hw_nn : 0 ≤ w (boasT c' ζ) := (hw_Icc (by linarith [zetaMin_pos hc0, hζ_le])).1
      have hk_nn : 0 ≤ k (boasT c' ζ) := hw_nn.trans (hw_le_k hζ_le)
      have hA_eq : boasA c' R ζ ζ * h ζ = w (boasT c' ζ) * (lowerP0 c' ζ * h ζ) * osc ζ := by
        unfold boasA lowerPζ w boasT; dsimp [osc]; ring
      rw [hA_eq, Real.norm_eq_abs,
        show w (boasT c' ζ) * (lowerP0 c' ζ * h ζ) * osc ζ - w (boasT c' ζ) * dm_ζ ζ * osc ζ =
          w (boasT c' ζ) * osc ζ * (lowerP0 c' ζ * h ζ - dm_ζ ζ) by ring,
        abs_mul, abs_mul, abs_of_nonneg hw_nn]
      have hB_ζ := (hB hc_B hwf hT_hi hζ_le).2.2
      calc w (boasT c' ζ) * |osc ζ| * |lowerP0 c' ζ * h ζ - dm_ζ ζ|
          ≤ k (boasT c' ζ) * 3 * (C_B * c' ^ (-1 : ℝ) * dm_ζ ζ) :=
            mul_le_mul (mul_le_mul (hw_le_k hζ_le) (hosc_bd hζ_pos) (abs_nonneg _) hk_nn)
              hB_ζ (abs_nonneg _) (mul_nonneg hk_nn (by norm_num))
        _ = 3 * C_B * c' ^ (-1 : ℝ) * (k (boasT c' ζ) * dm_ζ ζ) := by ring
    rw [Real.norm_eq_abs] at h_sub_le
    rw [MeasureTheory.integral_const_mul] at h_sub_le
    have hpow43 : c' ^ (-1 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = c' ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    calc |∫ ζ in Ioi (zetaMin c'), (boasA c' R ζ ζ * h ζ - w (boasT c' ζ) * dm_ζ ζ * osc ζ)|
        ≤ 3 * C_B * c' ^ (-1 : ℝ) * ∫ ζ in Ioi (zetaMin c'), k (boasT c' ζ) * dm_ζ ζ := h_sub_le
      _ ≤ 3 * C_B * c' ^ (-1 : ℝ) * (3 * K_M * c' ^ (-(1 / 3 : ℝ))) := by
          gcongr; exact hk_dm_bound.2
      _ = (9 * C_B * K_M) * (c' ^ (-1 : ℝ) * c' ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ K_err * c' ^ (-(4 / 3 : ℝ)) := by
          rw [hpow43]; dsimp [K_err]; gcongr; linarith
  exact ⟨h_aesm, h_nn, hPh_int_Ici, h_total_bd, h_early_bd, h_band_diff⟩

#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boas_zeta_to_lowerBand

end

end FormalResearch.ModularBootstrap.FiveTerm
