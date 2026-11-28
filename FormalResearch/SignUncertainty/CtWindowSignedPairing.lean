module

public import FormalResearch.SignUncertainty.CtWindowSignedAux

/-!
# Principal `(ct:K-signed)` pairing bound on `[-R, R]`

Pairs `dualK(ξ(φ_c(u))) - fsK(u)` against `Re(f_c(u))` via `FineOrderSigned.fs_pairing_principal`,
`CtWindowSignedCfu.outer_assembly_fs`, and `CtWindowSignedCfu.hankelHalfCubic`, giving
`O(c⁻¹ η_R + c^{-4/3})` with no `log c`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.CohnElkies
open FormalResearch.SignUncertainty.CtSd FormalResearch.SignUncertainty.CtChart
open FormalResearch.SignUncertainty.FineOrderSigned

private lemma fsOpCh_chain_eq {R₀ R1 R2 U : ℝ} (h1 : R1 = R2)
    (hA : 1 ≤ R1) (hB : R1 < R₀) (hC : kap * |U| ≤ R1 ^ 2 / 16)
    (hA' : 1 ≤ R2) (hB' : R2 < R₀) (hC' : kap * |U| ≤ R2 ^ 2 / 16) (G : ℂ → ℂ) :
    fsOpCh (fsChain hA hB hC) U G = fsOpCh (fsChain hA' hB' hC') U G := by
  subst h1; rfl

set_option maxHeartbeats 1600000 in
/-- **Principal `(ct:K-signed)` pairing bound** (log-free): for `c₁ > 0` sufficiently small and
`c` sufficiently large, pairs `dualK(ξ(φ_c(u))) - fsK(u)` against `Re(f_c(u))` with error
`O(c⁻¹ η_R + c^{-4/3})` (no `log c`, no `(1+|u|)^{1/2}` half-moment). -/
theorem window_signed_cfu_pairing {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ γ_w > (0 : ℝ), ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ_w → ∃ C_p c₀_p : ℝ, 0 ≤ C_p ∧ 3e6 ≤ c₀_p ∧
      ∀ {c C₁ C₂ : ℝ}, c₀_p ≤ c →
        CtChartBody c₁ ε c C₁ → CtChartBody ctChartC1 ε c C₂ →
        0 ≤ C₁ → 0 ≤ C₂ → C₂ * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 →
        ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f → hankelMass c f = 1 →
        ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
          |∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
              (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)| ≤
            C_p * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) := by
  obtain ⟨d, ϑ, th, zA_C, r_s, r_a, ρ_reg, M_Q, K_b, K_T, r_T,
    hr_s, hr_a, hρ_reg, hM_Q, hK_b, hK_T, hr_T, hrs_ρ, hrs_rT, hd_ra_le, hds1_KT, h3s1, hrq_half, hrq_3s1,
    hTf_lip, hthA, hth, hreg, hzA_diff, hzA_bd, hReal_link, hQ_bd, hQ_diff, hEb_bd, hE_diff,
    hd_B, hd_ψ, K_E, K_O, hKE, hKO, hEnorm, hOnorm⟩ := hankelHalfCubic ε hε
  obtain ⟨γ_u, hγ_u, hUhat⟩ := ctPhiR_uhatAn_inv hε hthA hth
  obtain ⟨_, _, _, _, hwin₂⟩ := ct_rosc_setup
  obtain ⟨ρ₁, M₁, hW₁, -⟩ := hwin₂ 1 (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hW₂, -⟩ := hwin₂ (-1) (Or.inr rfl)
  obtain ⟨C0, CA_tb, hC0, hCA_tb, hTail⟩ := tailBd_real hε.symm
  obtain ⟨Kb, hKb, hDual⟩ := CtDual.ct_dual_id_part2 hε
  have hρW_pos : 0 < min ρ₁ ρ₂ := lt_min hW₁.1 hW₂.1
  have hrS_pos : 0 < d.rAShrunk := d.rAShrunk_pos
  set γ_w : ℝ := min (min γ_u (ctChartC1 / 2))
    (min (Real.sqrt (d.rAShrunk / 16)) (Real.sqrt (min ρ₁ ρ₂ / 16)))
  have hγw_pos : 0 < γ_w := lt_min (lt_min hγ_u (half_pos ctChartC1_pos))
    (lt_min (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_pos.2 (by positivity)))
  refine ⟨γ_w, hγw_pos, fun c₁ hc₁ hle => ?_⟩
  have hle_u : c₁ ≤ γ_u := hle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle_Ch2 : c₁ ≤ ctChartC1 / 2 := hle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle_Ch : c₁ ≤ ctChartC1 := hle_Ch2.trans (half_le_self ctChartC1_pos.le)
  have hc₁_rAS : 8 * c₁ ^ 2 ≤ d.rAShrunk / 2 := by
    have hs : c₁ ≤ Real.sqrt (d.rAShrunk / 16) := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsq := pow_le_pow_left₀ hc₁.le hs 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    linarith
  have hsq_rho : 16 * c₁ ^ 2 ≤ min ρ₁ ρ₂ := by
    have hs : c₁ ≤ Real.sqrt (min ρ₁ ρ₂ / 16) := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hsq := pow_le_pow_left₀ hc₁.le hs 2
    rw [Real.sq_sqrt (by positivity)] at hsq
    linarith
  obtain ⟨c_u, hc_u, hU_inv⟩ := hUhat c₁ hc₁ hle_u
  set K1_tb : ℝ := 2 / CtCfu.d0
  set γ_tb : ℝ := min 1 ((15 / 16) * d.s₁ ^ 2 / K1_tb)
  set τs : ℝ := (1 / (2 * CtCfu.d0)) * d.s₁
  set Cb : ℝ := (1 + ((3 * d.s₁) ^ 2 + d.rAShrunk) * M_Q) * (1 + K_b) * Real.exp (d.M_ψ * (3 * d.s₁))
  have hCb0 : 0 ≤ Cb := by positivity
  have hK1_pos : 0 < K1_tb := by have := CtCfu.d0_pos; positivity
  have hγ_pos : 0 < γ_tb := by have := d.hs₁; positivity
  have hτs_pos : 0 < τs := by have := CtCfu.d0_pos; have := d.hs₁; positivity
  set C_ext : ℝ :=
    (1 / √π) * ((64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * d.s₁ ^ (-(9 / 2 : ℝ))) +
    Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
      ((2 / 9) * τs ^ (-(9 / 2 : ℝ)) + (2 / 3) * τs ^ (-(3 / 2 : ℝ)))
  have hCext0 : 0 ≤ C_ext := by have := d.hs₁; positivity
  obtain ⟨C_eta, C_rem, hCeta0, hCrem0, hFs⟩ :=
    fs_pairing_principal d hKE hKO hEnorm hOnorm (cl := c₁ ^ 2) (cu := 4 * c₁ ^ 2) (C_ext := C_ext)
      (by positivity) hCext0
  obtain ⟨c_small, hc_small⟩ := eventually_atTop.1 hankel_small_eventually
  set c₀_p : ℝ := max (max 3e6 (max c_u c_small)) (max d.n₀ (max (5000 : ℝ) (max ((4 / c₁ ^ 2) ^ 2)
    (max ((2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) + 1) ^ 2)
      (max (M₁ / (2 * c₁ ^ 2) + 1) (M₂ / (2 * c₁ ^ 2) + 1))))))
  have hc₀_3e6 : 3e6 ≤ c₀_p := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨max C_eta (2 * (C_rem + C_ext)), c₀_p, by positivity, hc₀_3e6, ?_⟩
  intro c C₁ C₂ hc hb₁ hb₂ hC1 hC2 hC2sm f hf hM R hR
  have hc0 : 0 < c := by linarith only [hc₀_3e6, hc]
  have hc2 : 2 ≤ c := by linarith only [hc₀_3e6, hc]
  have hc3e6 : 3e6 ≤ c := hc₀_3e6.trans hc
  have hc5000 : 5000 ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
  have hc_n0 : d.n₀ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hdn1 : 1 ≤ c := d.n₀_ge_one.trans hc_n0
  have hc_u' : c_u ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hc_sm' : c_small ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hc_4c : (4 / c₁ ^ 2) ^ 2 ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hc_rAS : (2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) + 1) ^ 2 ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))).trans hc
  have hc_M1 : M₁ / (2 * c₁ ^ 2) + 1 ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hc
  have hc_M2 : M₂ / (2 * c₁ ^ 2) + 1 ≤ c :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hc
  have hsmall := hc_small c hc_sm'
  have hc12_23 : c ^ ((1 : ℝ) / 2) ≤ c ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc2]) (by norm_num)
  have h4c₁_c23 : 4 / c₁ ^ 2 ≤ c ^ ((2 : ℝ) / 3) := by
    have h1 : 4 / c₁ ^ 2 ≤ c ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity) hc0.le]
      exact hc_4c
    exact h1.trans hc12_23
  have h4_le_c1c23 : 4 ≤ c₁ ^ 2 * c ^ ((2 : ℝ) / 3) := by
    rwa [div_le_iff₀ (sq_pos_of_pos hc₁), mul_comm] at h4c₁_c23
  have hR1 : 1 ≤ R := by linarith only [h4_le_c1c23, hR.1]
  have hR0 : 0 < R := by linarith only [hR1]
  have hR_add_lt_Rm : R + 1 ≤ ctRmax ctChartC1 c := by
    have h1 : c₁ ^ 2 ≤ ctChartC1 ^ 2 / 4 := by nlinarith only [hc₁, hle_Ch2, ctChartC1_pos]
    have h2 : 1 ≤ (ctChartC1 ^ 2 - c₁ ^ 2) * 4 * c ^ ((2 : ℝ) / 3) := by
      have hc23 : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc0 _
      nlinarith only [h1, h4_le_c1c23, sq_pos_of_pos hc₁, hc23]
    unfold ctRmax
    nlinarith only [hR.2, h2]
  have hRm : R ≤ ctRmax ctChartC1 c := by linarith only [hR_add_lt_Rm]
  have Hchart : CtRealChartHyp ε c C₂ := ⟨hb₂, hC2, hc3e6, hC2sm⟩
  obtain ⟨⟨ρ0, hρ0, hPhiDiff⟩, -⟩ := ctPhiC_spec Hchart.body.1
  obtain ⟨ρF, hρF, hFdiff, -, hFconj⟩ := ctFcC_holo ctChartC1_pos ctChartC1_le hb₂ hc3e6 (by linarith only [hC2sm]) hf
  have hR1ρF : R + 1 < ρF := hR_add_lt_Rm.trans_lt hρF
  have hR1ρ0 : R + 1 < ρ0 := hR_add_lt_Rm.trans_lt hρ0
  have hF_d : DifferentiableOn ℂ (ctFcC ctChartC1 ε c f) (ball 0 (R + 1)) :=
    hFdiff.mono (ball_subset_ball hR1ρF.le)
  let aInv : ℂ → ℂ := fun z => (ctMu c : ℂ) * ctPhiC ctChartC1 ε c z
  have ha_d : DifferentiableOn ℂ aInv (ball 0 (R + 1)) :=
    DifferentiableOn.const_mul (hPhiDiff.mono (ball_subset_ball hR1ρ0.le)) _
  have ha_in : ∀ z ∈ ball (0 : ℂ) (R + 1), aInv z ∈ ball (0 : ℂ) d.rAShrunk := by
    intro z hz
    have hzn : ‖z‖ ≤ R + 1 := (mem_ball_zero_iff.1 hz).le
    have hzm : ‖z‖ ≤ ctRmax ctChartC1 c := hzn.trans hR_add_lt_Rm
    have hcφ : ‖ctPhiC ctChartC1 ε c z‖ ≤ R + 2 := by
      have h1 := (hb₂.2.2.2 z hzm).1
      calc ‖ctPhiC ctChartC1 ε c z‖ = ‖z + (ctPhiC ctChartC1 ε c z - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖ctPhiC ctChartC1 ε c z - z‖ := norm_add_le _ _
        _ ≤ (R + 1) + C₂ * c ^ (-(1 / 3 : ℝ)) := add_le_add hzn h1
        _ ≤ R + 2 := by linarith only [hC2sm]
    have hμ0 := ctMu_pos hc0
    have hμR : ctMu c * R ≤ 8 * c₁ ^ 2 := by
      calc ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ ((2 : ℝ) / 3)) := mul_le_mul_of_nonneg_left hR.2 hμ0.le
        _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ ((2 : ℝ) / 3)) := by unfold ctMu; ring
        _ = 4 * (2 : ℝ) ^ ((2 : ℝ) / 3) * c₁ ^ 2 := by rw [← Real.rpow_add hc0]; simp
        _ ≤ 8 * c₁ ^ 2 := by
            have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
              calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
                _ = 2 := Real.rpow_one 2
            nlinarith only [h2, sq_nonneg c₁]
    have hμ2 : ctMu c * 2 < d.rAShrunk / 2 := by
      have hsq : 2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) < c ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.lt_sqrt (by positivity)]
        nlinarith only [hc_rAS, (by positivity : 0 ≤ 2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2))]
      have hlt : 2 * 2 ^ ((2 : ℝ) / 3) / (d.rAShrunk / 2) < c ^ ((2 : ℝ) / 3) := hsq.trans_le hc12_23
      rw [div_lt_iff₀ (half_pos hrS_pos)] at hlt
      unfold ctMu
      rw [Real.rpow_neg hc0.le]
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) * (c ^ ((2 : ℝ) / 3))⁻¹ * 2
          = 2 * (2 : ℝ) ^ ((2 : ℝ) / 3) / c ^ ((2 : ℝ) / 3) := by ring
        _ < d.rAShrunk / 2 := (div_lt_iff₀ (Real.rpow_pos_of_pos hc0 _)).2 (by linarith only [hlt])
    rw [mem_ball_zero_iff]
    dsimp [aInv]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ0.le]
    have := mul_le_mul_of_nonneg_left hcφ hμ0.le
    linarith only [this, hμR, hc₁_rAS, hμ2]
  have hF_r : ∀ x : ℝ, |x| ≤ R → (ctFcC ctChartC1 ε c f (x : ℂ)).im = 0 := fun x hx =>
    ctFcC_real_of_holo hρF hFconj (hx.trans hRm)
  have ha_r : ∀ x : ℝ, |x| ≤ R → (aInv (x : ℂ)).im = 0 := fun x hx => by
    dsimp [aInv]
    rw [Hchart.ctPhiC_ofReal (hx.trans hRm), ← Complex.ofReal_mul, Complex.ofReal_im]
  have ha_re_eq : ∀ x : ℝ, |x| ≤ R → (aInv (x : ℂ)).re = ctMu c * ctPhiR ε c x := fun x hx => by
    dsimp [aInv]
    rw [Hchart.ctPhiC_ofReal (hx.trans hRm), ← Complex.ofReal_mul, Complex.ofReal_re]
  have hu_eq : ∀ x : ℝ, |x| ≤ R → d.uReal c (aInv (x : ℂ)).re = x := fun x hx => by
    rw [ha_re_eq x hx]
    set ax : ℝ := ctMu c * ctPhiR ε c x
    have hmem : (x : ℂ) ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith only [hx]
    have hax_lt : |ax| < d.r_a := by
      have h1 := ha_in (x : ℂ) hmem
      have h2 : aInv (x : ℂ) = (ax : ℂ) := by
        dsimp [aInv, ax]; rw [Hchart.ctPhiC_ofReal (hx.trans hRm)]; push_cast; ring
      rw [h2, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
      exact h1.trans d.rAShrunk_lt
    unfold HalfCubicData.uReal HalfCubicData.aHat
    rw [hd_ψ c ax hdn1 hax_lt]
    have hre : ((ax : ℂ) + (c⁻¹ : ℂ) * (CtCfu.psiOf th ax : ℂ)).re = ax + c⁻¹ * CtCfu.psiOf th ax := by
      simp
    rw [hre]
    have hlam_eq : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ ((2 : ℝ) / 3) * (ax + c⁻¹ * CtCfu.psiOf th ax) =
        ctPhiR ε c x + ctLam c * CtCfu.psiOf th ax := by
      unfold ax ctMu ctLam
      have h2ne : (2 : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have hcne : c ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have h2neg : (2 : ℝ) ^ (-(2 / 3 : ℝ)) = ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg (by norm_num) _
      have hcneg : c ^ (-(2 / 3 : ℝ)) = (c ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg hc0.le _
      have hc13 : c ^ (-(1 / 3 : ℝ)) = c⁻¹ * c ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      rw [h2neg, hcneg, hc13]
      field_simp
    rw [hlam_eq]
    exact hU_inv c hc_u' R hR.1 hR.2 x (abs_le.1 hx)
  have hMF : ∫ x in (-R)..R, ‖ctFcC ctChartC1 ε c f (x : ℂ)‖ ≤ 2 := by
    have hnorm_eq : ∀ u ∈ Icc (-R) R, ‖ctFcC ctChartC1 ε c f (u : ℂ)‖ =
        |hankelPsiR c f (ctPhiR ε c u)| * ctPhiRD ε c u := fun u hu => by
      have hu_lt : |u| < ctRmax ctChartC1 c := abs_lt.2 ⟨by linarith only [hu.1, hR_add_lt_Rm],
        by linarith only [hu.2, hR_add_lt_Rm]⟩
      rw [Hchart.ctFcC_ofReal hu_lt]
      unfold ctFr
      have hphiD : 0 < ctPhiRD ε c u := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (Hchart.ctPhiRD_bounds hu_lt.le).1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hphiD]
    have hcongr : ∫ u in (-R)..R, ‖ctFcC ctChartC1 ε c f (u : ℂ)‖ =
        ∫ u in Ioo (-R) R, ctPhiRD ε c u * |hankelPsiR c f (ctPhiR ε c u)| := by
      rw [intervalIntegral.integral_of_le (by linarith only [hR0]), integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      rw [hnorm_eq u ⟨hu.1.le, hu.2.le⟩, mul_comm]
    have hsub := (Hchart.ctPhiR_subst (a := -R) (b := R) (by linarith only [hRm]) hRm (by linarith only [hR0])
      (fun x => |hankelPsiR c f x|)).symm
    have hsub_le : ∫ x in Ioo (ctPhiR ε c (-R)) (ctPhiR ε c R), |hankelPsiR c f x| ≤
        ∫ x in (-(langerRadius c))..(langerRadius c), |hankelPsiR c f x| := by
      have hmR_lt : -langerRadius c ≤ ctPhiR ε c (-R) :=
        (abs_le.1 (Hchart.abs_ctPhiR_lt (by simpa [abs_of_pos hR0] using hRm)).le).1
      have hR_lt : ctPhiR ε c R ≤ langerRadius c :=
        (abs_le.1 (Hchart.abs_ctPhiR_lt (by simpa [abs_of_pos hR0] using hRm)).le).2
      have hsub_set : Ioo (ctPhiR ε c (-R)) (ctPhiR ε c R) ⊆ Ioc (-(langerRadius c)) (langerRadius c) :=
        fun x hx => ⟨by linarith only [hmR_lt, hx.1], by linarith only [hR_lt, hx.2]⟩
      have hΨ_cont : ContinuousOn (fun x => |hankelPsiR c f x|) (Icc (-(langerRadius c)) (langerRadius c)) :=
        continuous_abs.comp_continuousOn (continuousOn_hankelPsiR hc0 hf)
      have hint_big : IntegrableOn (fun x => |hankelPsiR c f x|) (Ioc (-(langerRadius c)) (langerRadius c)) :=
        (hΨ_cont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [intervalIntegral.integral_of_le (by linarith [langerRadius_pos hc0])]
      exact setIntegral_mono_set hint_big (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun x hx => hsub_set hx)
    have hmass := hankel_psi_abs_mass hc5000 hf hε hM
    linarith only [hcongr, hsub, hsub_le, hmass, hsmall]
  have hL_close : ∀ x : ℝ, |x| ≤ R →
      let lam := c ^ (-(1 / 3 : ℝ))
      let R_c := d.s₁ / lam
      let R₀ := HalfCubicInternal.Rs d / lam
      let ax := (aInv (x : ℂ)).re
      ∀ (hR1_c : 1 ≤ R_c) (hRR_c : R_c < R₀) (hUR_c : kap * |d.uReal c ax| ≤ R_c ^ 2 / 16),
      |CtDual.dualK ε c (hankelXi c (ctPhiR ε c x)) -
        fsOpCh (fsChain hR1_c hRR_c hUR_c) (d.uReal c ax)
          (fun w => d.B c ax ((lam : ℂ) * w))| ≤ C_ext * c ^ (-(3 / 2 : ℝ)) := by
    intro x hx lam R_c R₀ ax hR1_c hRR_c hUR_c
    have hlam0 : 0 < lam := Real.rpow_pos_of_pos hc0 _
    have hclam3 : c * lam ^ 3 = 1 := by
      dsimp [lam]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      have h1 : -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 := by norm_num
      rw [h1, Real.rpow_neg_one]; exact mul_inv_cancel₀ hc0.ne'
    have hlam1 : lam ≤ 1 := by
      rw [show (1 : ℝ) = (1 : ℝ) ^ (-(1 / 3 : ℝ)) by simp]
      exact Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith only [hc2]) (by norm_num)
    have hmem_x : (x : ℂ) ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; linarith only [hx]
    have hax_S : |ax| < d.rAShrunk := by
      have h1 := ha_in (x : ℂ) hmem_x
      have h2 : aInv (x : ℂ) = (ax : ℂ) := Complex.ext rfl (ha_r x hx)
      rwa [h2, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
    have hax_dra : |ax| < d.r_a := hax_S.trans d.rAShrunk_lt
    have hax_ra : |ax| < r_a := hax_dra.trans_le hd_ra_le
    have hax_mem : (ax : ℂ) ∈ ball (0 : ℂ) r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hax_ra
    have hax_dmem : (ax : ℂ) ∈ ball (0 : ℂ) d.r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hax_dra
    obtain ⟨hzA_eq, hAF_eq, haC_eq, -, hpsi_eq, hXi_unit, hNF_eq⟩ := hReal_link ax hax_ra
    set β : ℝ := CtCfu.zA ax
    set psi : ℝ := CtCfu.psiOf th ax
    have hβ_in : ‖zA_C (ax : ℂ)‖ < ρ_reg ∧ ‖zA_C (ax : ℂ)‖ < r_T := hzA_bd (ax : ℂ) hax_mem
    have hβ_ρ : |β| < ρ_reg := by simpa [hzA_eq, Complex.norm_real, Real.norm_eq_abs] using hβ_in.1
    have hβ_rT : |β| < r_T := by simpa [hzA_eq, Complex.norm_real, Real.norm_eq_abs] using hβ_in.2
    have haC' : aC (β : ℂ) = (CtCfu.AF β : ℂ) := by
      rw [hAF_eq]; simpa [hzA_eq] using haC_eq
    have hpsi' : psiHat ϑ (β : ℂ) = (psi : ℂ) := by simpa [hzA_eq] using hpsi_eq
    have hQ_d : DifferentiableOn ℂ (fun s => CtChart.Qeps ϑ (s, (β : ℂ))) (ball 0 r_s) := by
      simpa [hzA_eq] using hQ_diff (ax : ℂ) hax_mem
    have hE_d : DifferentiableOn ℂ (fun s => Efun c (β : ℂ) s) (ball 0 r_s) := by
      simpa [hzA_eq] using hE_diff c (ax : ℂ) hc2 hax_mem
    have hgs_diff : DifferentiableOn ℂ (gAmp ax psi (fun s => CtChart.Qeps ϑ (s, (β : ℂ)))
        (fun s => Efun c (β : ℂ) s)) (ball 0 (3 * d.s₁)) := by
      have hsub : ball (0 : ℂ) (3 * d.s₁) ⊆ ball 0 r_s := ball_subset_ball h3s1.le
      unfold gAmp
      exact (((differentiableOn_const 1).add (((differentiableOn_id.pow 2).add
        (differentiableOn_const (ax : ℂ))).mul (hQ_d.mono hsub))).mul (hE_d.mono hsub)).mul
          ((differentiableOn_const (Complex.I * (psi : ℂ))).mul differentiableOn_id).cexp
    have hgs_bd : ∀ z ∈ ball (0 : ℂ) (3 * d.s₁), ‖gAmp ax psi (fun s => CtChart.Qeps ϑ (s, (β : ℂ)))
        (fun s => Efun c (β : ℂ) s) z‖ ≤ Cb := by
      intro z hz
      have hz_rs : z ∈ ball (0 : ℂ) r_s := ball_subset_ball h3s1.le hz
      have hz_3 : ‖z‖ ≤ 3 * d.s₁ := (mem_ball_zero_iff.1 hz).le
      have hQb : ‖CtChart.Qeps ϑ (z, (β : ℂ))‖ ≤ M_Q := by
        simpa [hzA_eq] using hQ_bd z hz_rs (ax : ℂ) hax_mem
      have hEb1 : ‖Efun c (β : ℂ) z - 1‖ ≤ K_b * c⁻¹ := by
        simpa [hzA_eq] using hEb_bd c z (ax : ℂ) hc2 hz_rs hax_mem
      have hEb : ‖Efun c (β : ℂ) z‖ ≤ 1 + K_b := by
        have h1 : K_b * c⁻¹ ≤ K_b := by
          have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hc2])
          nlinarith only [hK_b, this]
        calc ‖Efun c (β : ℂ) z‖ = ‖1 + (Efun c (β : ℂ) z - 1)‖ := by ring_nf
          _ ≤ ‖(1 : ℂ)‖ + ‖Efun c (β : ℂ) z - 1‖ := norm_add_le _ _
          _ ≤ 1 + K_b * c⁻¹ := by simpa using hEb1
          _ ≤ 1 + K_b := by linarith only [h1]
      have hpsi_bd : |psi| ≤ d.M_ψ := by
        have h1 := d.hψ_bd c (ax : ℂ) hdn1 hax_dmem
        rw [hd_ψ c ax hdn1 hax_dra, Complex.norm_real, Real.norm_eq_abs] at h1
        exact h1
      have hexp_bd : ‖Complex.exp (Complex.I * (psi : ℂ) * z)‖ ≤ Real.exp (d.M_ψ * (3 * d.s₁)) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.2
        have him : (Complex.I * (psi : ℂ) * z).re = -psi * z.im := by simp [Complex.mul_re]
        rw [him]
        have hzim : |z.im| ≤ 3 * d.s₁ := (Complex.abs_im_le_norm z).trans hz_3
        have h1 : -psi * z.im ≤ |psi| * |z.im| := by
          calc -psi * z.im ≤ |-psi * z.im| := le_abs_self _
            _ = |psi| * |z.im| := by rw [abs_mul, abs_neg]
        exact h1.trans (mul_le_mul hpsi_bd hzim (abs_nonneg _) d.hM_ψ)
      have hfac1 : ‖1 + (z ^ 2 + (ax : ℂ)) * CtChart.Qeps ϑ (z, (β : ℂ))‖ ≤
          1 + ((3 * d.s₁) ^ 2 + d.rAShrunk) * M_Q := by
        have hax_le : ‖(ax : ℂ)‖ ≤ d.rAShrunk := by simpa [Complex.norm_real, Real.norm_eq_abs] using hax_S.le
        have hzz : ‖z ^ 2 + (ax : ℂ)‖ ≤ (3 * d.s₁) ^ 2 + d.rAShrunk := by
          calc ‖z ^ 2 + (ax : ℂ)‖ ≤ ‖z ^ 2‖ + ‖(ax : ℂ)‖ := norm_add_le _ _
            _ = ‖z‖ ^ 2 + ‖(ax : ℂ)‖ := by rw [norm_pow]
            _ ≤ (3 * d.s₁) ^ 2 + d.rAShrunk := add_le_add (pow_le_pow_left₀ (norm_nonneg _) hz_3 2) hax_le
        have hadd := norm_add_le (1 : ℂ) ((z ^ 2 + (ax : ℂ)) * CtChart.Qeps ϑ (z, (β : ℂ)))
        rw [norm_one, norm_mul] at hadd
        exact hadd.trans (add_le_add le_rfl (mul_le_mul hzz hQb (norm_nonneg _) (by positivity)))
      dsimp [Cb]; unfold gAmp
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hfac1 hEb (norm_nonneg _) (by positivity)) hexp_bd (norm_nonneg _) (by positivity)
    set rr : ℝ := Real.sqrt (d.s₁ / lam)
    have hrr : 0 < rr := Real.sqrt_pos.2 (div_pos d.hs₁ hlam0)
    have hrr2 : rr ^ 2 = R_c := Real.sq_sqrt (div_pos d.hs₁ hlam0).le
    have hR1_rr : 1 ≤ rr ^ 2 := by rw [hrr2]; exact hR1_c
    have hRR_rr : rr ^ 2 < R₀ := by rw [hrr2]; exact hRR_c
    have hUR_rr : kap * |d.uReal c ax| ≤ (rr ^ 2) ^ 2 / 16 := by rw [hrr2]; exact hUR_c
    have hsR : d.s₁ = lam * rr ^ 2 := by rw [hrr2]; dsimp [R_c]; field_simp
    set Ua : ℝ := ax / (kap * lam ^ 2)
    set Uh : ℝ := d.uReal c ax
    have hk0 : 0 < kap := kap_pos
    have hUa : ax = kap * Ua * lam ^ 2 := by dsimp [Ua]; field_simp
    have hUh : kap * Uh * lam ^ 2 = ax + lam ^ 3 * psi := by
      dsimp [Uh, psi]
      unfold HalfCubicData.uReal HalfCubicData.aHat
      rw [hd_ψ c ax hdn1 hax_dra]
      have hre : ((ax : ℂ) + (c⁻¹ : ℂ) * (CtCfu.psiOf th ax : ℂ)).re = ax + c⁻¹ * CtCfu.psiOf th ax := by
        simp
      rw [hre]
      have h2eq : kap = (2 : ℝ) ^ ((2 : ℝ) / 3) := rfl
      have h2ne : (2 : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have hcne : c ^ ((2 : ℝ) / 3) ≠ 0 := by positivity
      have h2neg : (2 : ℝ) ^ (-(2 / 3 : ℝ)) = ((2 : ℝ) ^ ((2 : ℝ) / 3))⁻¹ := Real.rpow_neg (by norm_num) _
      have hl2 : lam ^ 2 = (c ^ ((2 : ℝ) / 3))⁻¹ := by
        dsimp [lam]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
        have h1 : -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) := by norm_num
        rw [h1, Real.rpow_neg hc0.le]
      have hl3 : lam ^ 3 = c⁻¹ := by
        dsimp [lam]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
        have h1 : -(1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = -1 := by norm_num
        rw [h1, Real.rpow_neg_one]
      rw [h2eq, h2neg, hl2, hl3]
      field_simp
    have hax_32 : |ax| ≤ d.s₁ ^ 2 / 32 := hax_S.le.trans (min_le_right _ _)
    have hax_16 : |ax| ≤ d.s₁ ^ 2 / 16 := hax_32.trans (by linarith [sq_nonneg d.s₁])
    have hAF_16 : |CtCfu.AF β| ≤ d.s₁ ^ 2 / 16 := by rwa [hAF_eq]
    have hseg : kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16 := by
      have e : (rr ^ 2) ^ 2 / 16 = (d.s₁ ^ 2 / 16) / lam ^ 2 := by rw [hrr2]; dsimp [R_c]; field_simp
      rw [e, le_div_iff₀ (pow_pos hlam0 2)]
      have h1 : kap * |Ua| * lam ^ 2 = |ax| := by
        dsimp [Ua]; rw [abs_div, abs_of_pos (mul_pos hk0 (pow_pos hlam0 2))]; field_simp
      rw [h1]; exact hax_16
    have hNc : Ncc c * ((lam * Real.sqrt lam : ℝ) : ℂ) =
        ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
      have hsq : Real.sqrt c * (lam * Real.sqrt lam) = 1 := by
        have h1 : lam * Real.sqrt lam = Real.sqrt (lam ^ 3) := by
          rw [show lam ^ 3 = lam ^ 2 * lam by ring, Real.sqrt_mul (pow_nonneg hlam0.le 2), Real.sqrt_sq hlam0.le]
        rw [h1, ← Real.sqrt_mul hc0.le, hclam3, Real.sqrt_one]
      unfold Ncc
      have h1 : (Real.sqrt c / Real.sqrt π) * (lam * Real.sqrt lam) = 1 / √π := by
        rw [div_mul_eq_mul_div, mul_comm (Real.sqrt c), mul_assoc]
        field_simp; linarith [hsq]
      calc ((Real.sqrt c / Real.sqrt π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) * ((lam * Real.sqrt lam : ℝ) : ℂ)
          = (((Real.sqrt c / Real.sqrt π) * (lam * Real.sqrt lam) : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
            push_cast; ring
        _ = _ := by rw [h1]
    have hRs_lt_half : HalfCubicInternal.Rs d < r_s / 2 := by
      have hsq := (HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.2.2.2
      have hlt_rq : HalfCubicInternal.rsSq d < d.r_q := by
        obtain ⟨_, _, _, _, h3, h2, h1', h0', hq, _, _⟩ := HalfCubicInternal.radii_chain d
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (half_pos hr_s).le (by rw [hsq]; exact hlt_rq.trans hrq_half)
    have hR₀_le : lam * R₀ ≤ 3 * d.s₁ := by
      have hsq := (HalfCubicInternal.radii_chain d).2.2.2.2.2.2.2.2.2.2
      have hlt_rq : HalfCubicInternal.rsSq d < d.r_q := by
        obtain ⟨_, _, _, _, h3, h2, h1', h0', hq, _, _⟩ := HalfCubicInternal.radii_chain d
        linarith
      have h3ds1 : 0 ≤ 3 * d.s₁ := by linarith only [d.hs₁]
      have hRs_lt_3 : HalfCubicInternal.Rs d < 3 * d.s₁ :=
        lt_of_pow_lt_pow_left₀ 2 h3ds1 (by rw [hsq]; exact hlt_rq.trans hrq_3s1)
      have hlam_eq : lam * R₀ = HalfCubicInternal.Rs d := by dsimp [R₀]; field_simp
      rw [hlam_eq]; exact hRs_lt_3.le
    have hs1ρ : 2 * d.s₁ < ρ_reg := by linarith only [h3s1, hrs_ρ, d.hs₁]
    have hTb : ∀ s ∈ Icc (0 : ℝ) (2 * d.s₁), |Treal β s| < 1 / 4 := by
      intro s hs
      have hsr : ‖(s : ℂ)‖ < r_T := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
        linarith only [hs.2, h3s1, hrs_rT, d.hs₁]
      have hβr' : ‖(β : ℂ)‖ < r_T := by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_rT
      have h1 := hTf_lip (s : ℂ) (β : ℂ) hsr hβr'
      have h2 : |Treal β s| ≤ ‖Tf ((s : ℂ), (β : ℂ))‖ := Complex.abs_re_le_norm _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
      have h3 : K_T * s ≤ K_T * (2 * d.s₁) := mul_le_mul_of_nonneg_left hs.2 hK_T
      have h5 : d.s₁ * (8 * K_T + 8) ≤ 1 := (le_div_iff₀ (by positivity)).1 hds1_KT
      linarith only [h1, h2, h3, h5, d.hs₁]
    have pb := pullBack_real hreg (by linarith only [hc2]) hs1ρ hβ_ρ hTb haC' hpsi'
    have hs1I : d.s₁ ∈ Icc (0 : ℝ) (2 * d.s₁) := ⟨d.hs₁.le, by linarith only [d.hs₁]⟩
    have hTpos := T_pos_of_deriv pb.hT pb.hT1 pb.hT0 d.s₁ ⟨d.hs₁, by linarith only [d.hs₁]⟩
    have hregs1 := hreg ((d.s₁ : ℝ) : ℂ) (β : ℂ)
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg d.hs₁.le]; linarith only [hs1ρ, d.hs₁])
      (by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_ρ)
    have hT1K : T1real β d.s₁ ≤ K1_tb := (Complex.re_le_norm _).trans hregs1.2.2.2.2.2.2.2.2.2
    obtain ⟨B1, B2, tb⟩ := hTail hc2 d.hs₁ (by linarith only [d.hs₁] : d.s₁ < 2 * d.s₁) hK1_pos
      pb.hT pb.hϕT hTpos (pb.hT1 d.s₁ hs1I) hT1K hAF_16
    have hτ1 : τs ≤ Treal β d.s₁ := T_lower (δ := 1 / (2 * CtCfu.d0)) pb.hT (fun s hs => by
      have hh := hreg (s : ℂ) (β : ℂ)
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith only [hs.2, hs1ρ])
        (by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_ρ)
      exact hh.2.2.2.2.2.2.2.2.1) pb.hT0 hs1I
    have hne : ∀ s ∈ Ioo (d.s₁ / 2) (2 * d.s₁), ax + s ^ 2 ≠ 0 := fun s hs => by
      have hs2_nn : 0 ≤ d.s₁ / 2 := by linarith only [d.hs₁]
      have h1 : (d.s₁ / 2) ^ 2 < s ^ 2 := pow_lt_pow_left₀ hs.1 hs2_nn (by norm_num)
      have : 0 < ax + s ^ 2 := by nlinarith only [(abs_le.1 hax_16).1, h1, sq_nonneg d.s₁]
      exact this.ne'
    have hUa' : CtCfu.AF β = kap * Ua * lam ^ 2 := hAF_eq.trans hUa
    have hUh' : kap * Uh * lam ^ 2 = CtCfu.AF β + lam ^ 3 * psi := hUh.trans (by rw [hAF_eq])
    have hgs_diff' : DifferentiableOn ℂ (gAmp (CtCfu.AF β) psi (fun s => CtChart.Qeps ϑ (s, (β : ℂ)))
        (fun s => Efun c (β : ℂ) s)) (ball 0 (3 * d.s₁)) := by
      simpa [hAF_eq] using hgs_diff
    have hgs_bd' : ∀ z ∈ ball (0 : ℂ) (3 * d.s₁), ‖gAmp (CtCfu.AF β) psi (fun s => CtChart.Qeps ϑ (s, (β : ℂ)))
        (fun s => Efun c (β : ℂ) s) z‖ ≤ Cb := by
      simpa [hAF_eq] using hgs_bd
    have hne' : ∀ s ∈ Ioo (d.s₁ / 2) (2 * d.s₁), CtCfu.AF β + s ^ 2 ≠ 0 := by
      simpa [hAF_eq] using hne
    obtain ⟨Itot, hItot_ten, hItot_bd⟩ := outer_assembly_fs (c := c) (lam := lam) (s1 := d.s₁)
      (s1' := 2 * d.s₁) (rr := rr) (a := CtCfu.AF β) (Ua := Ua) (Uh := Uh) (psi := psi) (L := CtCfu.NF β)
      (R₀ := R₀) (Nc := Ncc c) (N1 := ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)))
      hc0 hlam0 hlam1 hclam3 d.hs₁ (by linarith only [d.hs₁]) hrr hR1_rr hsR hUa' hUh' hseg rfl hNc
      hRR_rr hR₀_le (fsChain hR1_rr hRR_rr hUR_rr) hCb0 hgs_diff' hgs_bd' pb tb hne'
    have hx_langer : |ctPhiR ε c x| < langerRadius c := Hchart.abs_ctPhiR_lt (hx.trans hRm)
    have hxi_pos : 0 < hankelXi c (ctPhiR ε c x) := hankelXi_pos hc0 hx_langer.le
    have hdualK_eq : -Itot.re = CtDual.dualK ε c (hankelXi c (ctPhiR ε c x)) := by
      have hten' : Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b,
          CtSd.Bfun ε c τ * Complex.exp (Complex.I * c * (CtSd.phaseL (CtCfu.NF β) τ : ℂ))) atTop
          (𝓝 (((Real.sqrt (π * c / 12) : ℝ) : ℂ) * CtDual.dualI ε c (hankelXi c (ctPhiR ε c x)))) := by
        have hconst := (tendsto_const_nhds (x := ((Real.sqrt (π * c / 12) : ℝ) : ℂ))).mul
          ((hDual hc2).1 _ hxi_pos).1
        refine hconst.congr fun b => ?_
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun τ _ => ?_
        rw [CtSd.Bfun, CtDual.dualP_eq, hNF_eq, show ax = ctMu c * ctPhiR ε c x from ha_re_eq x hx,
          ← hankelXi_eq_hankelXiUnit hc0]
        ring
      have heq := tendsto_nhds_unique hItot_ten hten'
      rw [heq]; unfold CtDual.dualK; simp [Complex.mul_re]
    have hop_eq : fsOpCh (fsChain hR1_rr hRR_rr hUR_rr) Uh
        (fun w => (1 + (((lam : ℂ) * w) ^ 2 + (CtCfu.AF β : ℂ)) * CtChart.Qeps ϑ ((lam : ℂ) * w, (β : ℂ))) *
          Efun c (β : ℂ) ((lam : ℂ) * w)) =
        fsOpCh (fsChain hR1_c hRR_c hUR_c) (d.uReal c ax) (fun w => d.B c ax ((lam : ℂ) * w)) := by
      rw [fsOpCh_chain_eq hrr2 hR1_rr hRR_rr hUR_rr hR1_c hRR_c hUR_c
        (fun w => (1 + (((lam : ℂ) * w) ^ 2 + (CtCfu.AF β : ℂ)) * CtChart.Qeps ϑ ((lam : ℂ) * w, (β : ℂ))) *
          Efun c (β : ℂ) ((lam : ℂ) * w))]
      have hin : (fsChain hR1_c hRR_c hUR_c).intE Uh
          (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + (CtCfu.AF β : ℂ)) * CtChart.Qeps ϑ ((lam : ℂ) * w, (β : ℂ))) *
            Efun c (β : ℂ) ((lam : ℂ) * w))) =
          (fsChain hR1_c hRR_c hUR_c).intE (d.uReal c ax) (fun w => csr w * d.B c ax ((lam : ℂ) * w)) := by
        refine chain3_intE_congr (fsChain hR1_c hRR_c hUR_c) fun w hw => ?_
        have hwm : ‖(lam : ℂ) * w‖ < r_s / 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
          have h1 : lam * ‖w‖ < lam * R₀ := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hlam0
          have h2 : lam * R₀ = HalfCubicInternal.Rs d := by dsimp [R₀]; field_simp
          linarith only [h1, h2, hRs_lt_half]
        congr 1
        symm
        rw [hAF_eq]
        simpa [hzA_eq] using hd_B c (ax : ℂ) ((lam : ℂ) * w) hc2 hax_dmem hwm
      unfold fsOpCh
      dsimp only
      rw [hin]
    rw [hdualK_eq, hop_eq] at hItot_bd
    have hrr9 : 1 / rr ^ 9 = d.s₁ ^ (-(9 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
      have h1 : rr = d.s₁ ^ ((1 : ℝ) / 2) * c ^ ((1 : ℝ) / 6) := by
        have : d.s₁ / lam = d.s₁ * c ^ ((1 : ℝ) / 3) := by
          dsimp [lam]; rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le]; congr 2; norm_num
        dsimp [rr]; rw [this, Real.sqrt_eq_rpow, Real.mul_rpow d.hs₁.le (Real.rpow_nonneg hc0.le _),
          ← Real.rpow_mul hc0.le]; norm_num
      rw [h1, ← Real.rpow_natCast, Real.mul_rpow (Real.rpow_nonneg d.hs₁.le _) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul d.hs₁.le, ← Real.rpow_mul hc0.le, one_div,
        mul_inv, ← Real.rpow_neg d.hs₁.le, ← Real.rpow_neg hc0.le]
      norm_num
    have hexp_rr : Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 4 / rr ^ 6 := by
      have h1 : (rr ^ 2) ^ 3 / 4 + 1 ≤ Real.exp ((rr ^ 2) ^ 3 / 4) := Real.add_one_le_exp _
      have h2 : rr ^ 6 ≤ 4 * Real.exp ((rr ^ 2) ^ 3 / 4) := by linarith only [h1, show (rr ^ 2) ^ 3 = rr ^ 6 by ring]
      rw [Real.exp_neg, le_div_iff₀ (pow_pos hrr 6), inv_mul_le_iff₀ (Real.exp_pos _)]
      linarith only [h2]
    have hterm1 : (16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
        320000 * (2 * Cb) / rr ^ 9 ≤
        (64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * d.s₁ ^ (-(9 / 2 : ℝ)) * c ^ (-(3 / 2 : ℝ)) := by
      have ha1 : 16 * (2 * Cb) / rr ^ 3 * Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 64 * (2 * Cb) / rr ^ 9 := by
        have := mul_le_mul_of_nonneg_left hexp_rr (by positivity : 0 ≤ 16 * (2 * Cb) / rr ^ 3)
        refine this.trans_eq ?_; field_simp; ring
      have hb1' : 1024 * (2 * Cb) / rr ^ 9 * Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ 1024 * (2 * Cb) / rr ^ 9 := by
        have h0 : -((rr ^ 2) ^ 3 / 4) ≤ 0 := by linarith only [show (0 : ℝ) ≤ (rr ^ 2) ^ 3 / 4 by positivity]
        exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 h0)
      calc (16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
              320000 * (2 * Cb) / rr ^ 9
          ≤ 64 * (2 * Cb) / rr ^ 9 + 1024 * (2 * Cb) / rr ^ 9 + 320000 * (2 * Cb) / rr ^ 9 := by linarith only [ha1, hb1']
        _ = (64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * (1 / rr ^ 9) := by ring
        _ = _ := by rw [hrr9]; ring
    have hterm2 : (1 / c ^ 2) * ((4 * (Real.sqrt (π * c / 12) * CA_tb) * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
        ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ))) ≤
        Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
          ((2 / 9) * τs ^ (-(9 / 2 : ℝ)) + (2 / 3) * τs ^ (-(3 / 2 : ℝ))) * c ^ (-(3 / 2 : ℝ)) := by
      have hcKB : 1 / c ^ 2 * Real.sqrt (π * c / 12) = Real.sqrt (π / 12) * c ^ (-(3 / 2 : ℝ)) := by
        rw [show π * c / 12 = (π / 12) * c by ring, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow c,
          show c ^ 2 = c ^ (2 : ℝ) by norm_cast, one_div, ← Real.rpow_neg hc0.le]
        calc c ^ (-2 : ℝ) * (Real.sqrt (π / 12) * c ^ ((1 : ℝ) / 2))
            = Real.sqrt (π / 12) * (c ^ (-2 : ℝ) * c ^ ((1 : ℝ) / 2)) := by ring
          _ = Real.sqrt (π / 12) * c ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hc0]; norm_num
      have hV1 : (Treal β d.s₁) ^ (-9 / 2 : ℝ) ≤ τs ^ (-(9 / 2 : ℝ)) := by
        simpa [neg_div] using Real.rpow_le_rpow_of_nonpos hτs_pos hτ1 (by norm_num : -(9 / 2 : ℝ) ≤ 0)
      have hV2 : (Treal β d.s₁) ^ (-3 / 2 : ℝ) ≤ τs ^ (-(3 / 2 : ℝ)) := by
        simpa [neg_div] using Real.rpow_le_rpow_of_nonpos hτs_pos hτ1 (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      calc (1 / c ^ 2) * ((4 * (Real.sqrt (π * c / 12) * CA_tb) * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ)))
          = (1 / c ^ 2 * Real.sqrt (π * c / 12)) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ)) := by ring
        _ = (Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ))) *
                c ^ (-(3 / 2 : ℝ)) := by rw [hcKB]; ring
        _ ≤ _ := by gcongr
    refine hItot_bd.trans ?_
    have hπ0 : 0 ≤ 1 / √π := by positivity
    calc (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
            320000 * (2 * Cb) / rr ^ 9) +
          (1 / c ^ 2) * ((4 * (Real.sqrt (π * c / 12) * CA_tb) * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
            ((2 / 9) * (Treal β d.s₁) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β d.s₁) ^ (-3 / 2 : ℝ)))
        ≤ (1 / √π) * ((64 * (2 * Cb) + 1024 * (2 * Cb) + 320000 * (2 * Cb)) * d.s₁ ^ (-(9 / 2 : ℝ)) *
              c ^ (-(3 / 2 : ℝ))) +
            Real.sqrt (π / 12) * CA_tb * (4 * (1 + 4 * C0 / γ_tb + 3 * C0 ^ 2 / γ_tb ^ 2) / γ_tb ^ 2) *
              ((2 / 9) * τs ^ (-(9 / 2 : ℝ)) + (2 / 3) * τs ^ (-(3 / 2 : ℝ))) * c ^ (-(3 / 2 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hterm1 hπ0) hterm2
      _ = C_ext * c ^ (-(3 / 2 : ℝ)) := by dsimp [C_ext]; ring
  have hL_int : IntervalIntegrable (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
      ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
      (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) volume (-R) R := by
    have hF_re_cont : ContinuousOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re) (Icc (-R) R) :=
      Complex.continuous_re.comp_continuousOn (continuousOn_ctFcC_real Hchart hf hRm)
    have hfsK_cont : ContinuousOn fsK (Icc (-R) R) :=
      (continuous_iff_continuousAt.2 fun u => (hasDerivAt_fsK u).continuousAt).continuousOn
    have hphi_cont : ContinuousOn (fun u => hankelXi c (ctPhiR ε c u)) (Icc (-R) R) := by
      have hsub : Icc (-R) R ⊆ Icc (-ctRmax ctChartC1 c) (ctRmax ctChartC1 c) :=
        fun u hu => ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      have h1 := Hchart.continuousOn_ctPhiR.mono hsub
      intro u hu
      have hua : |u| ≤ ctRmax ctChartC1 c := abs_le.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      exact (hasDerivAt_hankelXi hc0 (Hchart.abs_ctPhiR_lt hua).le).continuousAt.comp_continuousWithinAt (h1 u hu)
    have hxi_pos : ∀ u ∈ Icc (-R) R, 0 < hankelXi c (ctPhiR ε c u) := fun u hu => by
      have hua : |u| ≤ ctRmax ctChartC1 c := abs_le.2 ⟨by linarith only [hu.1, hRm], by linarith only [hu.2, hRm]⟩
      exact hankelXi_pos hc0 (Hchart.abs_ctPhiR_lt hua).le
    have hmeas_dual : AEStronglyMeasurable (fun u => CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)))
        (volume.restrict (Icc (-R) R)) :=
      aestronglyMeasurable_dualK_comp hε hc2 measurableSet_Icc hphi_cont hxi_pos
    have hmeas_tot : AEStronglyMeasurable (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) (volume.restrict (Icc (-R) R)) := by
      simp only [Complex.one_re, mul_one]
      exact (hF_re_cont.aestronglyMeasurable measurableSet_Icc).mul
        (hmeas_dual.sub (hfsK_cont.aestronglyMeasurable measurableSet_Icc))
    obtain ⟨MF_re, hMF_re⟩ := isCompact_Icc.exists_bound_of_continuousOn hF_re_cont
    obtain ⟨Mfs, hMfs⟩ := isCompact_Icc.exists_bound_of_continuousOn hfsK_cont
    simp only [Real.norm_eq_abs] at hMF_re hMfs
    have hMF_nn : 0 ≤ MF_re := (abs_nonneg _).trans (hMF_re (-R) ⟨by linarith only [hR0], by linarith only [hR0]⟩)
    have hint_icc : IntegrableOn (fun u : ℝ => (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) (Icc (-R) R) := by
      refine Integrable.mono' (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne) (C := MF_re * (Kb + Mfs)))
        hmeas_tot ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_)
      simp only [Complex.one_re, mul_one, Real.norm_eq_abs, abs_mul]
      have hK_bd : |CtDual.dualK ε c (hankelXi c (ctPhiR ε c u))| ≤ Kb :=
        ((hDual hc2).1 _ (hxi_pos u hu)).2
      exact mul_le_mul (hMF_re u hu) ((abs_sub _ _).trans (add_le_add hK_bd (hMfs u hu)))
        (abs_nonneg _) hMF_nn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith only [hR0])).2
      (hint_icc.mono_set Ioc_subset_Icc_self)
  have hpr := hFs (n := c) (R := R) (ρ := R + 1) (Bn := 1) (MF := 2)
    (F := ctFcC ctChartC1 ε c f) (b := fun _ => 1) (aInv := aInv)
    (L := fun u => CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)))
    hc_n0 hR1 (by linarith) hR.1 hR.2 zero_le_one hF_d (differentiableOn_const _) ha_d ha_in
    hF_r (fun _ _ => Complex.one_im) ha_r hu_eq (fun _ _ => by simp) hMF hL_close hL_int
  have hcircle_le : (∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ /
      airyEnv (circleMap 0 R θ)) ≤ ctEta c₁ ε c f R := by
    have hM1_lt : M₁ < 2 * c₁ ^ 2 * c := by
      have h1 : M₁ / (2 * c₁ ^ 2) < c := by linarith only [hc_M1]
      have := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hc₁))).1 h1
      linarith only [this]
    have hM2_lt : M₂ < 2 * c₁ ^ 2 * c := by
      have h1 : M₂ / (2 * c₁ ^ 2) < c := by linarith only [hc_M2]
      have := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hc₁))).1 h1
      linarith only [this]
    have hagree : ∃ ρA : ℝ, ctRmax c₁ c < ρA ∧ EqOn (ctPhiC c₁ ε c) (ctPhiC ctChartC1 ε c) (ball 0 ρA) := by
      rcases hε with rfl | rfl
      · exact ctPhiC_agree hc0 hc₁ hle_Ch hb₁ hb₂ hW₁ (by linarith [min_le_left ρ₁ ρ₂]) hM1_lt
      · exact ctPhiC_agree hc0 hc₁ hle_Ch hb₁ hb₂ hW₂ (by linarith [min_le_right ρ₁ ρ₂]) hM2_lt
    obtain ⟨ρA, hρA, hphiAgree⟩ := hagree
    have hFcAgree : EqOn (ctFcC ctChartC1 ε c f) (ctFcC c₁ ε c f) (ball 0 ρA) :=
      ctFcC_agree_on_ball hphiAgree
    have hcongr : ∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ /
          airyEnv (circleMap 0 R θ) =
        ∫ θ in (0 : ℝ)..π, R * ‖ctFcC c₁ ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
      refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le Real.pi_pos.le] at hθ
      have him : 0 ≤ (circleMap 0 R θ).im := by
        simp only [circleMap, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero, Complex.exp_ofReal_mul_I_im]
        exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      have hmem : circleMap 0 R θ ∈ ball (0 : ℂ) ρA := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hR0]; exact hR.2.trans_lt hρA
      rw [div_eq_mul_inv, ← norm_airyUpE him, hFcAgree hmem]
    have hΨ_cont : ContinuousOn (hankelPsi c f) (sphere 0 R) := by
      have hsub : sphere (0 : ℂ) R ⊆ closedBall 0 (langerRadius c) := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_closedBall_zero_iff, hu]
        have hlt : ctRmax ctChartC1 c < langerRadius c := Hchart.Rm_add_lt.trans_le' (by
          linarith only [mul_nonneg hC2 (Real.rpow_nonneg hc0.le (-(1 / 3 : ℝ)))])
        exact hRm.trans hlt.le
      rw [langerRadius_eq] at hsub
      exact (analyticOnNhd_hankelPsi hc0 hf).differentiableOn.continuousOn.mono hsub
    have hG_cont : ContinuousOn (ctFcC c₁ ε c f) (sphere 0 R) := by
      have hsubA : sphere (0 : ℂ) R ⊆ ball 0 ρA := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_ball_zero_iff, hu]; exact hR.2.trans_lt hρA
      have hsubF : sphere (0 : ℂ) R ⊆ ball 0 ρF := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_ball_zero_iff, hu]; exact hRm.trans_lt hρF
      exact (hFdiff.continuousOn.mono hsubF).congr fun u hu => (hFcAgree (hsubA hu)).symm
    rw [hcongr]
    exact ctEta_ge_half hR0 hΨ_cont hG_cont
  have hc53 : c ^ (-(5 / 3 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc2]) (by norm_num)
  have hc32 : c ^ (-(3 / 2 : ℝ)) ≤ c ^ (-(4 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hc2]) (by norm_num)
  have hrem_bd : (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ))) * 2 ≤
      (2 * (C_rem + C_ext)) * c ^ (-(4 / 3 : ℝ)) := by
    have : C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ)) ≤
        C_rem * c ^ (-(4 / 3 : ℝ)) + C_ext * c ^ (-(4 / 3 : ℝ)) := by gcongr
    linarith only [this]
  have hη_nn : 0 ≤ c⁻¹ * ctEta c₁ ε c f R := mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hcongr_pr : (∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u)) =
      ∫ u in (-R)..R, (ctFcC ctChartC1 ε c f (u : ℂ)).re * ((fun _ : ℂ => (1 : ℂ)) (u : ℂ)).re *
        (CtDual.dualK ε c (hankelXi c (ctPhiR ε c u)) - fsK u) := by
    simp only [Complex.one_re, mul_one]
  rw [hcongr_pr]
  refine hpr.trans ?_
  rw [one_mul]
  calc C_eta * c⁻¹ * (∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ /
          airyEnv (circleMap 0 R θ)) +
        (C_rem * c ^ (-(5 / 3 : ℝ)) + C_ext * c ^ (-(3 / 2 : ℝ))) * 2
      ≤ C_eta * (c⁻¹ * ctEta c₁ ε c f R) + (2 * (C_rem + C_ext)) * c ^ (-(4 / 3 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hcircle_le (mul_nonneg hCeta0 (inv_nonneg.2 hc0.le))
        linarith only [this, hrem_bd]
    _ ≤ max C_eta (2 * (C_rem + C_ext)) * (c⁻¹ * ctEta c₁ ε c f R) +
          max C_eta (2 * (C_rem + C_ext)) * c ^ (-(4 / 3 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hη_nn)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hc43_nn)
    _ = max C_eta (2 * (C_rem + C_ext)) * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ))) := by ring

end FormalResearch.SignUncertainty
