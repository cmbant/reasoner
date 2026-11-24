module

public import FormalResearch.SignUncertainty.HankelBandInstance

/-!
# Assembly of the Hankel `BandReductionInstance` (M5-S5)

See `HankelBandInstance` for the field dictionary.  This module proves the remaining fields
(edge kernel measurability and bound, the edge representation `hW_edge`, continuity of `ũ` on the band,
`2ρ_R ≤ 0.035`) and defines `hankelBandInstance`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand FormalResearch.CohnElkies

/-- The edge phase `Φ(τ; ξ) = edgePhi (log π²ξ) τ`. -/
noncomputable def hankelBandPhi (τ ξ : ℝ) : ℝ := edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ

/-- The edge kernel `K_edge = a_0(τ) · a_2(ξ) · exp (c (R_0 - i Φ))` with `a_2 = 1`, `R_0 = 0`. -/
noncomputable def hankelBandK (c τ ξ : ℝ) : ℂ :=
  hankelEdgeAmp c τ * 1 * Complex.exp ((c : ℂ) * (((0 : ℝ) : ℂ) - Complex.I * (hankelBandPhi τ ξ : ℂ)))

lemma hankelBandPhi_eq (τ ξ : ℝ) :
    hankelBandPhi τ ξ = Real.log (Real.pi ^ 2 * ξ) * τ + edgePhi 0 τ := by
  unfold hankelBandPhi edgePhi
  ring

lemma continuous_edgePhi_zero : Continuous (edgePhi 0) :=
  continuous_iff_continuousAt.mpr fun τ => (hasDerivAt_edgePhi 0 τ).continuousAt

lemma hankelBandK_measurable {c : ℝ} (hc : 0 < c) :
    Measurable (fun p : ℝ × ℝ => hankelBandK c p.1 p.2) := by
  have hA : Measurable (hankelEdgeAmp c) := (hankelEdgeAmp_continuous hc).measurable
  have hE : Measurable (edgePhi 0) := continuous_edgePhi_zero.measurable
  have hL : Measurable (fun ξ : ℝ => Real.log (Real.pi ^ 2 * ξ)) :=
    Real.measurable_log.comp (measurable_const.mul measurable_id)
  have hP : Measurable (fun p : ℝ × ℝ => hankelBandPhi p.1 p.2) := by
    have : (fun p : ℝ × ℝ => hankelBandPhi p.1 p.2) =
        fun p => Real.log (Real.pi ^ 2 * p.2) * p.1 + edgePhi 0 p.1 :=
      funext fun p => hankelBandPhi_eq p.1 p.2
    rw [this]
    exact ((hL.comp measurable_snd).mul measurable_fst).add (hE.comp measurable_fst)
  unfold hankelBandK
  refine (((hA.comp measurable_fst).mul measurable_const)).mul ?_
  exact Complex.measurable_exp.comp (measurable_const.mul
    (measurable_const.sub (measurable_const.mul (Complex.measurable_ofReal.comp hP))))

lemma norm_hankelBandK {c : ℝ} (hc : 0 < c) (τ ξ : ℝ) : ‖hankelBandK c τ ξ‖ = ‖hankelEdgeAmp c τ‖ := by
  unfold hankelBandK
  have : (c : ℂ) * (((0 : ℝ) : ℂ) - Complex.I * (hankelBandPhi τ ξ : ℂ)) =
      ((-(c * hankelBandPhi τ ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I]
  simp

lemma hankelBandK_eq_inv {c : ℝ} (τ ξ : ℝ) (hξ : 0 < ξ) :
    hankelBandK c τ ξ = (mellinK0 c ((τ : ℂ) * Complex.I) ξ)⁻¹ := by
  rw [hankelEdge_kernel_inv_eq c τ ξ hξ]
  unfold hankelBandK hankelBandPhi hankelEdgeAmp hankelEdgeAmpB
  rw [mul_one]
  congr 2
  push_cast; ring

/-- **`u1cl:rep`**: `W̃_c(iτ) = ∫ K dm_+ - ∫ K dm_-`. -/
theorem hankelBand_W_edge {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (τ : ℝ) :
    hankelWtS c ε f ((τ : ℂ) * Complex.I) =
      (∫ ξ, hankelBandK c τ ξ ∂hankelDmPos c f) - ∫ ξ, hankelBandK c τ ξ ∂hankelDmNeg c f := by
  have hc0 : 0 < c := by linarith
  have hm : Measurable (fun ξ : ℝ => hankelBandK c τ ξ) := by
    have h := (hankelBandK_measurable hc0).comp ((measurable_const (a := τ)).prodMk measurable_id)
    exact h
  have hK : ∀ ξ ∈ Ioi (0 : ℝ), ‖hankelBandK c τ ξ‖ ≤ ‖hankelEdgeAmp c τ‖ :=
    fun ξ _ => (norm_hankelBandK hc0 τ ξ).le
  have key : (∫ ξ, hankelBandK c τ ξ ∂hankelDmPos c f) - ∫ ξ, hankelBandK c τ ξ ∂hankelDmNeg c f =
      ∫ ξ in Ioi (0 : ℝ), hankelBandK c τ ξ * (hankelDmDens c f ξ : ℂ) :=
    hankelDm_integral_sub hc0 hf hm.aestronglyMeasurable hK
  rw [key, hankelWtS_edge_eq hc hf τ]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  rw [hankelBandK_eq_inv τ ξ hξ]
  simp only [hankelDmDens]

/-- `ũ` is continuous on `{0 ≤ π²ξ - 1 ≤ 5·10⁻⁴}`. -/
lemma hankelBandU_continuousAt {c ξ : ℝ} (h0 : 0 ≤ Real.pi ^ 2 * ξ - 1) (h1 : Real.pi ^ 2 * ξ - 1 ≤ 5e-4) :
    ContinuousAt (hankelBandU c) ξ := by
  have hn : ‖((Real.pi ^ 2 * ξ - 1 : ℝ) : ℂ)‖ ≤ 1e-3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; linarith
  have hd := (hasDerivAt_chartY langerEta_etaC hn).continuousAt
  have hl : Continuous (fun ξ : ℝ => ((Real.pi ^ 2 * ξ - 1 : ℝ) : ℂ)) := by fun_prop
  have h2 : ContinuousAt (fun ξ : ℝ => chartY etaC (((Real.pi ^ 2 * ξ - 1 : ℝ) : ℂ))) ξ :=
    ContinuousAt.comp (g := chartY etaC) (f := fun ξ : ℝ => ((Real.pi ^ 2 * ξ - 1 : ℝ) : ℂ))
      (x := ξ) hd hl.continuousAt
  unfold hankelBandU
  exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp h2)

/-- `2ρ_R ≤ 0.035` at `R = b² c^{2/3}`. -/
lemma hankelBand_rho_le {c : ℝ} (hc : 0 < c) :
    2 * rhoR hankelBandParams c ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) ≤ 0.035 := by
  have hk := hankelLangerKappa_bounds
  have e' : (c ^ (1 / 3 : ℝ)) ^ 2 = c ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  have e : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) = ((1 / 100 : ℝ) * c ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [mul_pow, e']
  have hsq : √((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) = (1 / 100 : ℝ) * c ^ (1 / 3 : ℝ) := by
    rw [e]; exact Real.sqrt_sq (by positivity)
  have hprod : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc]; norm_num
  unfold rhoR
  rw [hsq]
  show 2 * (2 * langerKappa * c ^ (-(1 / 3 : ℝ)) * ((1 / 100 : ℝ) * c ^ (1 / 3 : ℝ))) ≤ 0.035
  have : 2 * (2 * langerKappa * c ^ (-(1 / 3 : ℝ)) * ((1 / 100 : ℝ) * c ^ (1 / 3 : ℝ))) =
      (4 / 100) * langerKappa * (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) := by ring
  rw [this, hprod]
  nlinarith [hk.2]

lemma hankelBand_exp_le_two {c : ℝ} (hc : 1 ≤ c) : Real.exp (1 / (6 * c)) ≤ 2 := by
  have h1 : 1 / (6 * c) ≤ Real.log 2 := by
    have : 1 / (6 * c) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    linarith [Real.log_two_gt_d9]
  calc Real.exp (1 / (6 * c)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h1
    _ = 2 := Real.exp_log (by norm_num)

lemma hankelBand_w_band {c u_T R ξ : ℝ} (hc0 : 0 < c) (hu0 : u_T ≤ 0) (hu : |u_T| ≤ langerRadius c)
    (hR0 : 0 ≤ R) (hR : R ≤ langerRadius c) (hξ : ξ ∈ Icc (hankelXi c u_T) (hankelXi c (-R))) :
    0 ≤ Real.pi ^ 2 * ξ - 1 ∧ Real.pi ^ 2 * ξ - 1 ≤ 5e-4 := by
  have hT := hankelXi_w_bounds hc0 hu hu0
  have hRb := hankelXi_w_bounds hc0 (x := -R) (by rw [abs_neg, abs_of_nonneg hR0]; exact hR) (by linarith)
  have hpi : 0 < Real.pi ^ 2 := by positivity
  exact ⟨by nlinarith [hξ.1, hT.1], by nlinarith [hξ.2, hRb.2.1]⟩

/-- **The Hankel band-reduction instance** at scale `c ≥ 3·10⁶`, level `u_T ∈ [-3, 0]`. -/
noncomputable def hankelBandInstance {c ε u_T : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hε : ε = 1 ∨ ε = -1)
    (hf : IsHankelEigenfn c ε f) (hmass : hankelMass c f = 1) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (htail : ∀ Δ : ℝ, c * hankelXi c u_T ≤ Δ → 0 ≤ f Δ) : BandReductionInstance hankelBandParams :=
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith
  have hu : |u_T| ≤ langerRadius c := by
    rw [abs_of_nonpos hu0]; linarith [(hankel_radius_ge hc).1]
  have hR0 : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by positivity
  have hR : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ langerRadius c := (hankel_radius_ge hc).2
  have hfinP := isFiniteMeasure_hankelDmPos hc0 hf
  have hfinN := isFiniteMeasure_hankelDmNeg hc0 hf
  { c := c
    ε := ε
    R := (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)
    hc := by linarith
    hε := hε
    hR_lb := le_refl _
    hR_ub := by
      show (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1
      linarith
    hρR_ub := hankelBand_rho_le hc0
    W_tilde := hankelWtS c ε f
    hW_cont := hankelWtS_continuousOn hc32 hf
    hW_holo := hankelWtS_differentiableOn hc32 hf
    hW_symm := fun ζ h0 h1 => hankelWtS_one_sub hc32 hf hε h0 h1
    hW_bound := fun ζ h0 h1 => by
      have h := hankelWtS_norm_le hc32 hf hε h0 h1
      rw [hmass, one_mul] at h
      have h2 := hankelBand_exp_le_two (show 1 ≤ c by linarith)
      have h3 : 0 ≤ (1 + ‖ζ‖) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
      show ‖hankelWtS c ε f ζ‖ ≤ 2 * (1 + ‖ζ‖) ^ (1 / 2 : ℝ)
      nlinarith
    dmPos := hankelDmPos c f
    dmNeg := hankelDmNeg c f
    hdmPos_fin := hfinP
    hdmNeg_fin := hfinN
    hdmPos_supp := hankelDmPos_Iic c f
    hdmNeg_supp := hankelDmNeg_Iic c f
    hdm_tv := (hankelDm_tv hc0 hf).trans_le (le_of_eq hmass)
    T := hankelXi c u_T
    hdm_nonneg_tail := hankelDmNeg_tail hc0 htail
    E_sub := ∅
    hE_sub_meas := MeasurableSet.empty
    hE_sub_sub := empty_subset _
    K_edge := hankelBandK c
    hK_meas := by
      have h := hankelBandK_measurable hc0
      exact h
    hW_edge := hankelBand_W_edge hc32 hf
    hK_sub := fun ξ hξ => absurd hξ (notMem_empty ξ)
    a_0 := hankelEdgeAmp c
    a_0' := hankelEdgeAmp' c
    a_2 := fun _ => 1
    R_0 := fun _ _ => 0
    Phi := hankelBandPhi
    hK_factor := fun ξ _ τ => rfl
    ha_2_bd := fun ξ _ => by show ‖(1 : ℂ)‖ ≤ 4; simp
    ha_0_deriv := hankelEdgeAmp_hasDerivAt hc0
    ha_0_bd := fun τ => hankelEdgeAmp_bound (by linarith) τ
    hR_0_nonpos := fun ξ _ τ => le_refl _
    hR_0_cont := fun ξ _ => continuousOn_const
    hR_0_even := fun ξ _ τ => rfl
    hR_0_unimodal := fun ξ _ => ⟨0, monotoneOn_const, antitoneOn_const⟩
    hPhi_odd := fun ξ _ τ => hankelEdgePhi_odd _ τ
    ν := fun τ => τ
    ν' := fun _ => 1
    invNu' := fun _ => 0
    hν_deriv := fun τ _ => hasDerivAt_id τ
    hν'_cont := continuousOn_const
    hν'_inv_pos := fun τ _ => ⟨by norm_num, by show ((1 : ℝ))⁻¹ ≤ 1; norm_num⟩
    hν'_inv_deriv := fun τ _ => hasDerivAt_const τ _
    hinvNu'_cont := continuousOn_const
    hinvNu'_int := by
      show ∫ τ in Ioi (0 : ℝ), |(0 : ℝ)| ≤ 1
      simp
    hinvNu'_integrable := integrableOn_zero
    μ := hankelBandMu
    m := hankelEdgeM
    m' := hankelEdgeM'
    hPhi_deriv := fun ξ hξ τ hτ => by
      have hξ0 : 0 < ξ := hξ.1
      have h := hankelEdgePhi_hasDerivAt (Real.log (Real.pi ^ 2 * ξ)) hτ
      have hμ : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by unfold hankelBandMu; rw [if_pos hξ0]
      exact h.congr_deriv (by rw [hμ]; ring)
    hm_0 := hankelEdgeM_zero
    hm_cont := hankelEdgeM_continuousOn
    hm_strictMono := hankelEdgeM_strictMonoOn
    hm_deriv := fun τ hτ => hankelEdgeM_hasDerivAt hτ
    hm_step := fun τ hτ => hankelEdgeM_step hτ
    hm_slope := fun τ hτ => by
      show (1 / 2 : ℝ) * τ / (1 + τ ^ 3) ≤ hankelEdgeM' τ / 1
      rw [div_one]; exact hankelEdgeM_slope hτ
    τ_0 := hankelBandTau0
    hτ_0_nn := hankelBandTau0_nonneg
    hτ_0_eq_zero := fun ξ h => hankelBandTau0_zero h
    hτ_0_root := fun ξ h => hankelBandTau0_root h
    u_tilde := hankelBandU c
    Delta := hankelXi c
    hτ_0_below := fun ξ hξ => hankelBandTau0_below hc hu0 hu3 hξ.1
    hτ_0_band := fun ξ hξ => hankelBandTau0_band hc hu0 hu3 hR0 hR hξ
    hu_tilde_int := by
      refine ContinuousOn.integrableOn_Icc ?_
      intro ξ hξ
      obtain ⟨h0, h1⟩ := hankelBand_w_band hc0 hu0 hu hR0 hR hξ
      exact (hankelBandU_continuousAt h0 h1).neg.continuousWithinAt }

/-- **Proposition TE.3(1) for the Hankel strip**: on the annulus sector around `|ζ| ≈ ρ_R`,
`‖W̃_c(ζ₀)‖ ≤ C_Y c^{-5/6} (c^{1/3}(B₁ + B₂) + c^{-1/6}) / cos ψ`, with the band moments `B₁, B₂` of the
instance (`bandB1`, `bandB2`: integrals of `dm_+` over the band `[ξ(u_T), ξ(-R)]` and the tail). -/
theorem hankel_band_reduction {c ε u_T : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hε : ε = 1 ∨ ε = -1)
    (hf : IsHankelEigenfn c ε f) (hmass : hankelMass c f = 1) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (htail : ∀ Δ : ℝ, c * hankelXi c u_T ≤ Δ → 0 ≤ f Δ) {ζ₀ : ℂ} {ψ : ℝ}
    (hlo : rhoR hankelBandParams c ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) / 3 ≤ ‖ζ₀‖)
    (hhi : ‖ζ₀‖ ≤ 2 * rhoR hankelBandParams c ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)))
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ) (hcos : c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ) :
    ‖hankelWtS c ε f ζ₀‖ ≤ tebBandConst hankelBandParams * c ^ (-(5 / 6 : ℝ)) *
      (c ^ (1 / 3 : ℝ) * (bandB1 (hankelBandInstance hc hε hf hmass hu0 hu3 htail) +
        bandB2 (hankelBandInstance hc hε hf hmass hu0 hu3 htail)) + c ^ (-(1 / 6 : ℝ))) / Real.cos ψ :=
  (teb_band_reduction (hankelBandInstance hc hε hf hmass hu0 hu3 htail) hlo hhi hcos_eq hcos).1

/-- info: 'FormalResearch.SignUncertainty.hankel_band_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_band_reduction

/-- info: 'FormalResearch.SignUncertainty.hankelBand_W_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBand_W_edge

end FormalResearch.SignUncertainty
