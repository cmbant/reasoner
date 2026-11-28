module

public import FormalResearch.SignUncertainty.HankelBootMultilevelArc
public import FormalResearch.SignUncertainty.HankelBootAssembly

/-!
# Multilevel `(P, Q)` Two-Edge Bootstrap and `HbMultilevelLower D` (`u1cl:multilevel` lower half)

Proves `hbMultilevelLower_proved : ∀ D : ShellHBData, HbMultilevelLower D` (`R2a`–`R2c`):

* `D.Q = 0`: `hbMultilevelLower_Q_eq_zero` (`HankelBootMultilevelNodes.lean`).
* `D.Q ≠ 0`:
  * `hankel_quantC1_multilevel_of_feasible`: normalized prescribed profile gives `u_T > D.tm` with
    `QuantC1MultilevelB2Holds` and chart-inverted site points `u_site t` for `t ∈ D.S.erase D.tm`.
  * `hankelBootMultilevelParams`, `hankelBootMultilevelHBAt`: `BootstrapParams` and
    `BootstrapHBInstance P (hbTopWeights D)` from `hankel_yv_window_gen`, `hankelBoot_line_bound_gen`,
    `hankelBootMultilevel_arc`, `hankelBootMultilevel_nodes_lb`, and `hankelBootMultilevel_nodes_theta`.
  * `hbMultilevelLower_proved`: all-level `O(1)` lower bound `HbMultilevelLower D`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.TwoEdgeBootstrap FormalResearch.Special
  FormalResearch.ModularBootstrap.ConcreteBootstrap

private lemma hankelBoot_sites_to_u (D : ShellHBData) (R_off : ℝ) (hR : 0 ≤ R_off) :
    ∃ c₀ : ℝ, 3e6 ≤ c₀ ∧ ∀ t ∈ D.S.erase D.tm, ∀ c : ℝ, c₀ ≤ c → ∀ o : ℝ, |o| ≤ R_off →
      ∃ u : ℝ, |u - t| ≤ hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) ∧
        |u| ≤ |t| + hankelBeta1 * (R_off + 1) ∧ c * hankelXi c u = hankelLevel t c o := by
  induction (D.S.erase D.tm) using Finset.induction_on with
  | empty => exact ⟨3e6, le_rfl, fun _ h => by simp at h⟩
  | @insert a s _ ih =>
    obtain ⟨c_s, hcs, hs⟩ := ih
    obtain ⟨c_a, hca, ha⟩ := hankelLevel_to_u a R_off hR
    refine ⟨max c_a c_s, le_trans hcs (le_max_right _ _), fun t ht c hc o ho => ?_⟩
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | hts
    · exact ha c ((le_max_left _ _).trans hc) o ho
    · exact hs t hts c ((le_max_right _ _).trans hc) o ho

private lemma hankel_uT_exists_of_feasible (D : ShellHBData) {c ε T : ℝ} {f : ℝ → ℝ}
    (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1)
    (hTM_A : |D.tm| ≤ langerRadius c)
    (hδ_lt : hankelLobe c + 2 * langerRadius c * hankelRinf c < 1 / 4)
    (hT_lt : T < c * hankelXi c D.tm) :
    ∃ u_T : ℝ, D.tm < u_T ∧ u_T ≤ langerRadius c ∧ c * hankelXi c u_T = T := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hA := langerRadius_pos hc0
  have hAA : |langerRadius c| ≤ langerRadius c := by rw [abs_of_pos hA]
  have hTA_le : c * hankelXi c (langerRadius c) ≤ T := by
    by_contra hlt
    push Not at hlt
    have hneg := hankel_psi_neg_mass hc hf hε hM hAA hlt.le
    rw [intervalIntegral.integral_same] at hneg
    linarith [hankelLobe_nonneg c, mul_nonneg (mul_nonneg zero_le_two hA.le) hr]
  have htm_le_A : D.tm ≤ langerRadius c := (abs_le.mp hTM_A).2
  have hcont : ContinuousOn (fun x : ℝ => c * hankelXi c x) (Icc D.tm (langerRadius c)) := by
    intro x hx
    have hxA : |x| ≤ langerRadius c :=
      abs_le.mpr ⟨by linarith [(abs_le.mp hTM_A).1, hx.1], hx.2⟩
    exact ((hasDerivAt_hankelXi hc0 hxA).const_mul c).continuousAt.continuousWithinAt
  obtain ⟨u_T, hu_mem, hu_eq⟩ := intermediate_value_Icc' htm_le_A hcont ⟨hTA_le, hT_lt.le⟩
  have hne : D.tm ≠ u_T := by
    intro heq
    dsimp at hu_eq
    rw [heq, hu_eq] at hT_lt
    exact lt_irrefl _ hT_lt
  exact ⟨u_T, lt_of_le_of_ne hu_mem.1 hne, hu_mem.2, hu_eq⟩

private theorem hankel_quantC1_multilevel_of_feasible (D : ShellHBData) (R_off : ℝ) (hR : 0 ≤ R_off) :
    let δ_star := (shellHBQuantData D).1.1
    let κ_star := (shellHBQuantData D).1.2.1
    let C1 := (shellHBQuantData D).1.2.2
    ∃ c₀ : ℝ, 3e6 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
        ∀ T : ℝ, ∀ f : ℝ → ℝ, IsHankelPrescribed D r c ε T f → hankelMass c f = 1 →
          T < c * hankelXi c D.tm →
          ∃ u_T : ℝ, D.tm < u_T ∧ |u_T| ≤ langerRadius c ∧ c * hankelXi c u_T = T ∧
            QuantC1MultilevelB2Holds D δ_star κ_star C1 (hbZeroGapBelow D) (hankelPsi c f) u_T ∧
            ∃ u_site : ℝ → ℝ, ∀ t ∈ D.S.erase D.tm,
              |u_site t - t| ≤ hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) ∧
              |u_site t| ≤ langerRadius c ∧ -hankelRinf c ≤ hankelPsiR c f (u_site t) := by
  intro δ_star κ_star C1
  let D_1 : ℝ := hankelBeta1 * (R_off + 1)
  have hD1 : 0 ≤ D_1 := mul_nonneg hankelBeta1_pos.le (by linarith)
  let M_S : ℝ := D.S.sup' D.S_nonempty (fun s => |s|)
  have hM_S_nn : 0 ≤ M_S := le_trans (abs_nonneg D.tm) (Finset.le_sup' (fun s => |s|) D.tm_mem)
  let δ_lobe : ℝ → ℝ := fun c => hankelLobe c + (2 * langerRadius c + 1) * |hankelRinf c|
  have hδ_lim : Tendsto δ_lobe atTop (𝓝 0) := by
    simpa only [add_zero] using hankelLobe_tendsto.add hankelRinf_delta_tendsto
  have hδ_nn : ∀ᶠ c in atTop, 0 ≤ δ_lobe c := by
    filter_upwards [eventually_ge_atTop (5000 : ℝ)] with c hc
    have hc0 : 0 < c := by linarith
    have hA := (langerRadius_pos hc0).le
    have hl : 0 ≤ hankelLobe c := hankelLobe_nonneg c
    dsimp only [δ_lobe]; positivity
  obtain ⟨c₁, hc₁, hquant⟩ := hankel_quant_c1_multilevel_typeI D (C_0 := 60) (D_1 := D_1)
    (η_cap := hbZeroGapBelow D) (by norm_num) hD1 (hbZeroGapBelow_pos D)
    langerRadius δ_lobe tendsto_langerRadius hδ_nn hδ_lim
  obtain ⟨c_s, hc_s, hsites⟩ := hankelBoot_sites_to_u D R_off hR
  have hev : ∀ᶠ c in atTop, M_S + D_1 + 1 ≤ langerRadius c ∧ 1 ≤ langerRadius c ∧
      δ_lobe c < 1 / 4 := by
    refine (tendsto_langerRadius.eventually_ge_atTop (M_S + D_1 + 1)).and ?_
    exact (tendsto_langerRadius.eventually_ge_atTop 1).and (hδ_lim (Iio_mem_nhds (by norm_num)))
  obtain ⟨c_r, hc_r⟩ := eventually_atTop.1 hev
  let c₀ : ℝ := max (max c₁ c_s) (max c_r 3e6)
  refine ⟨c₀, le_trans (le_max_right _ _) (le_max_right _ _),
    fun c hc ε hε r hr T f hf hM hT_lt => ?_⟩
  have hc₁' : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc_s' : c_s ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc_r' : c_r ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
  have hc3 : 3e6 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hfeas := hf.toIsHankelFeasible
  have hrin : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  obtain ⟨hMA_le, hA1, hδ_lt⟩ := hc_r c hc_r'
  have hA := langerRadius_pos hc0
  have htm_M : |D.tm| ≤ M_S := Finset.le_sup' (fun s => |s|) D.tm_mem
  have htm_A : |D.tm| ≤ langerRadius c := by linarith
  have hδ_lt' : hankelLobe c + 2 * langerRadius c * hankelRinf c < 1 / 4 := by
    have hle : hankelLobe c + 2 * langerRadius c * hankelRinf c ≤ δ_lobe c := by
      dsimp only [δ_lobe]; rw [abs_of_nonneg hrin]; linarith
    linarith
  obtain ⟨u_T, htm_uT, huT_leA, hT_eq⟩ :=
    hankel_uT_exists_of_feasible D hc3 hfeas hε hM htm_A hδ_lt' hT_lt
  have huT_A : |u_T| ≤ langerRadius c :=
    abs_le.mpr ⟨by linarith [(abs_le.mp htm_A).1, htm_uT], huT_leA⟩
  have hδ_ge : hankelLobe c + 2 * langerRadius c * hankelRinf c ≤ δ_lobe c := by
    dsimp only [δ_lobe]; rw [abs_of_nonneg hrin]; linarith
  have hr_le_δ : hankelRinf c ≤ δ_lobe c := by
    have hl : 0 ≤ hankelLobe c := hankelLobe_nonneg c
    have h2 : 0 ≤ 2 * langerRadius c * hankelRinf c := mul_nonneg (by linarith) hrin
    dsimp only [δ_lobe]; rw [abs_of_nonneg hrin]; linarith
  choose u_site_raw hsite_raw using fun t (ht : t ∈ D.S.erase D.tm) =>
    hsites t ht c hc_s' (r t c) (hr t c)
  let u_site : ℝ → ℝ := fun t => if ht : t ∈ D.S.erase D.tm then u_site_raw t ht else 0
  have hsite_spec : ∀ t ∈ D.S.erase D.tm,
      |u_site t - t| ≤ D_1 * c ^ (-(1 / 3 : ℝ)) ∧ |u_site t| ≤ langerRadius c ∧
      -hankelRinf c ≤ hankelPsiR c f (u_site t) := by
    intro t ht
    have hs := hsite_raw t ht
    have hu_eq : u_site t = u_site_raw t ht := by simp only [u_site, ht, reduceDIte]
    rw [hu_eq]
    have ht_M : |t| ≤ M_S := Finset.le_sup' (fun s => |s|) (Finset.mem_erase.mp ht).2
    have hu_A : |u_site_raw t ht| ≤ langerRadius c := by linarith [hs.2.1]
    have hfx : 0 ≤ f (c * hankelXi c (u_site_raw t ht)) := by
      rw [hs.2.2]
      exact hf.sites_nonneg (hankelLevel t c (r t c)) (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    exact ⟨hs.1, hu_A, hankel_psi_sign_of_point hc5 hfe hε hM hu_A hfx⟩
  have hB2 := hquant c hc₁' (hankelPsi c f) u_T u_site
    (analyticOnNhd_hankelPsi hc0 hfe)
    (fun x hx => hankelPsi_real hc0 f (abs_le.2 hx))
    (fun u hu hcut => by
      have h := hankelPsi_envelope (by linarith : (2 : ℝ) ≤ c) hfe hε hM (u := u)
        (mem_closedBall_zero_iff.1 hu) hcut
      rwa [hankel_norm_exp_eq_airyEnv] at h)
    htm_uT huT_leA
    (fun t ht =>
      let hs := hsite_spec t ht
      ⟨hs.1, hs.2.1, by have := hs.2.2; unfold hankelPsiR at this; linarith⟩)
    (fun x hx => by
      have hxA : |x| ≤ langerRadius c :=
        abs_le.mpr ⟨hx.1, hx.2.trans (abs_le.mp huT_A).2⟩
      have hψ := hankel_psi_sign hc5 hfeas hε hM hxA (hT_eq ▸ hankel_phi_anti hc0 hxA huT_A hx.2)
      unfold hankelPsiR at hψ; linarith)
    (by
      have hnorm : ∀ x ∈ Icc (-langerRadius c) (langerRadius c),
          ‖hankelPsi c f (x : ℂ)‖ = |hankelPsiR c f x| := fun x hx => by
        have him := hankelPsi_real hc0 f (abs_le.2 hx)
        have hre : hankelPsi c f (x : ℂ) = ((hankelPsi c f (x : ℂ)).re : ℂ) :=
          Complex.ext rfl (by simp [him])
        rw [hre, Complex.norm_real, Real.norm_eq_abs]; rfl
      have hm1 : ∫ x in (-langerRadius c)..(langerRadius c), ‖hankelPsi c f (x : ℂ)‖ =
          ∫ x in (-langerRadius c)..(langerRadius c), |hankelPsiR c f x| := by
        refine intervalIntegral.integral_congr fun x hx => hnorm x ?_
        rw [uIcc_of_le (by linarith)] at hx; exact hx
      rw [hm1]
      refine (hankel_psi_abs_mass hc5 hfe hε hM).trans ?_
      have := hδ_ge; linarith [hankelLobe_nonneg c])
    (by
      have hneg := hankel_psi_neg_mass hc3 hfeas hε hM huT_A hT_eq.symm.le
      unfold hankelPsiR at hneg
      have := hδ_ge; linarith)
    (fun R' hR' hRu => by
      have hR'_abs : |-R'| ≤ langerRadius c := by
        rw [abs_neg, abs_of_nonneg hR'.1]; exact hR'.2
      have hup := hankel_psi_total_upper hc3 hfeas hε hM hR'_abs
        (hT_eq ▸ hankel_phi_anti hc0 hR'_abs huT_A hRu)
      exact hup.trans hδ_ge)
  exact ⟨u_T, htm_uT, huT_A, hT_eq, hB2, u_site, hsite_spec⟩

/-- `BootstrapParams` for the multilevel Hankel bootstrap at `D : ShellHBData` (`D.Q ≠ 0`) and
offset bound `R_off ≥ 0`. -/
noncomputable def hankelBootMultilevelParams (D : ShellHBData) (_hQ : D.Q ≠ 0)
    (R_off : ℝ) (hR : 0 ≤ R_off) : BootstrapParams :=
  let M_S := D.S.sup' D.S_nonempty (fun s => |s|)
  let U := max 3 (M_S + 1)
  have hU3 : 3 ≤ U := le_max_left _ _
  let M_pow := Real.exp (M_S + 1)
  let Rinf_coeff := max 70 (hankelLineRinfCoeffGen U)
  { b := 1 / 100
    C_a := max ((28 / 5 : ℝ) * virasoroArcCovConst) (hankelLineCaGen U)
    C_unc := (28 / 5 : ℝ) * hankelArcUncConst
    C_1 := M_pow * (shellHBQuantData D).1.2.2
    w_star := 1 / hbWeight D (D.tm : ℂ)
    κ_star := (shellHBQuantData D).1.2.1
    C_α := M_pow * hbWeightSumConst D
    C_fb := hankelWindowCGen U hU3
    D_1 := hankelBeta1 * (R_off + 1)
    η_0 := hbZeroGapBelow D
    δ_star := (shellHBQuantData D).1.1
    κ := 1 / 600000
    C_0 := max 16 (2 * Rinf_coeff * hankelTailI0)
    C_L := 4 * hankelWindowCGen U hU3
    γ := 1
    k_0 := 9
    hb := by norm_num
    hCa := le_trans (mul_nonneg (by norm_num) virasoroArcCovConst_pos.le) (le_max_left _ _)
    hCunc := by unfold hankelArcUncConst; have := Real.pi_pos; positivity
    hC1 := mul_pos (Real.exp_pos _) (shellHBQuantData D).2.2.2.2.1
    hw_star := one_div_pos.mpr (hbWeight_eq_real D (D.S_zero D.tm_mem)).2
    hκ_star := (shellHBQuantData D).2.2.2.1
    hCα := (mul_pos (Real.exp_pos _) (hbWeightSumConst_pos D)).le
    hCfb := one_le_hankelWindowCGen U hU3
    hD1 := mul_nonneg hankelBeta1_pos.le (by linarith)
    hη0 := hbZeroGapBelow_pos D
    hδ_star := (shellHBQuantData D).2.1
    hκ := by norm_num
    hC0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    hCL := by linarith [one_le_hankelWindowCGen U hU3]
    hγ := zero_le_one
    hk0 := by norm_num }

set_option maxHeartbeats 1200000 in
private noncomputable def hankelBootMultilevelHBAt (D : ShellHBData) (hQ : D.Q ≠ 0)
    (R_off : ℝ) (hR : 0 ≤ R_off)
    {c ε T u_T R : ℝ} {f : ℝ → ℝ} {u_site : ℝ → ℝ}
    (hc : 1e14 ≤ c)
    (hScale : 11 * max 3 (D.S.sup' D.S_nonempty (fun s => |s|) + 1) ≤ langerScale c)
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c)
    (h48 : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ))
    (hR1 : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hR2 : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hR_S : max (D.S.sup' D.S_nonempty (fun s => |s|) + 2) 48 ≤ R)
    (hR_tm : 2 * ((9 : ℝ) + 1) * (-D.tm) ≤ R)
    (hR_low : ∀ u : ℂ, ‖u‖ = R → 0 < airyPQW D.P D.Q u ∧
      airyPQW D.P D.Q u ^ 2 * airyEnv u / (64 * π * √R) ≤ ‖airyPQN D.P D.Q u‖ ^ 2 ∧
      (0 ≤ u.im → ‖airyPQM D.P D.Q u / airyPQN D.P D.Q u - I‖ * airyEnv u ≤ 168 * √π) ∧
      (u.im ≤ 0 → ‖airyPQM D.P D.Q u / airyPQN D.P D.Q u + I‖ * airyEnv u ≤ 168 * √π))
    (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hT : c * hankelXi c u_T = T)
    (htm_uT : D.tm < u_T)
    (hB2 : QuantC1MultilevelB2Holds D (shellHBQuantData D).1.1 (shellHBQuantData D).1.2.1
      (shellHBQuantData D).1.2.2 (hbZeroGapBelow D) (hankelPsi c f) u_T)
    (hsites : ∀ t ∈ D.S.erase D.tm,
      |u_site t - t| ≤ hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) ∧
      |u_site t| ≤ langerRadius c ∧ -hankelRinf c ≤ hankelPsiR c f (u_site t))
    (hsmall : 4 * langerRadius c * hankelRinf c ≤ 1)
    (hD1_small : hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4) :
    let P := hankelBootMultilevelParams D hQ R_off hR
    { I : BootstrapHBInstance P (hbTopWeights D) //
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
      I.c = c ∧ I.x_tilde = u_T - D.tm } := by
  intro P
  let M_S : ℝ := D.S.sup' D.S_nonempty (fun s => |s|)
  let U : ℝ := max 3 (M_S + 1)
  have hU3 : 3 ≤ U := le_max_left _ _
  have hU0 : 0 ≤ U := by linarith
  let M_pow : ℝ := Real.exp (M_S + 1)
  let Rinf_coeff : ℝ := max 70 (hankelLineRinfCoeffGen U)
  have hc3 : (3e6 : ℝ) ≤ c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  obtain ⟨hR48, hRA, hAR, hRc⟩ := hankelBoot_radius_facts hc3 h48 hR1 hR2
  have hR_pos : 0 < R := by linarith
  have hR10 : 10 ≤ R := by linarith
  have hUR : U + 1 ≤ R := by
    have hM2 : M_S + 2 ≤ R := (le_max_left _ _).trans hR_S
    dsimp only [U]
    have hle := add_le_add_right
      (max_le (show (3 : ℝ) ≤ R - 1 by linarith only [hR48])
        (show M_S + 1 ≤ R - 1 by linarith only [hM2])) (1 : ℝ)
    linarith only [hle]
  have hR_S' : max (M_S + 1) 10 ≤ R := by
    have hM2 : M_S + 2 ≤ R := (le_max_left _ _).trans hR_S
    exact max_le (by linarith) hR10
  have htm_M : |D.tm| ≤ M_S := Finset.le_sup' (fun s => |s|) D.tm_mem
  have htm_neg : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (airyZero_neg 1)
  have hu0 : u_T ≤ 0 := by
    have h1 := hB2.uT_sub_le.trans (min_le_left _ _)
    have hδ := (shellHBQuantData D).2.2.1
    have ha := airyZero_one.2
    linarith [D.tm_le_airyZero_one]
  have huU : -U ≤ u_T := by
    have hM_uT : -M_S ≤ u_T := by linarith [(abs_le.mp htm_M).1, htm_uT]
    have hU_ge : M_S + 1 ≤ U := le_max_right _ _
    linarith
  have huA : |u_T| ≤ langerRadius c := by
    rw [abs_le]
    have h1 : M_S + 2 ≤ R := (le_max_left _ _).trans hR_S
    exact ⟨by linarith [(abs_le.mp htm_M).1, htm_uT], by linarith [hu0, langerRadius_pos hc0]⟩
  have hRu : -R ≤ u_T := by linarith [huU, hUR]
  have hRA' : R ≤ langerRadius c := by linarith
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hsmall' : (2 * langerRadius c + 2 * R) * hankelRinf c ≤ 1 := by
    have : (2 * langerRadius c + 2 * R) * hankelRinf c ≤ 4 * langerRadius c * hankelRinf c :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    linarith
  have hB1_nn : 0 ≤ hankelBootB1 c f R u_T :=
    hankelBootB1_nonneg_gen hc3 f hu0 huA hR_pos hRA'
  have hB2_nn : 0 ≤ hankelBootB2 c f R := hankelBootB2_nonneg c f R
  set B_1 := hankelBootB1 c f R u_T
  set B_2 := hankelBootB2 c f R
  have hB1_le2 : B_1 ≤ 2 :=
    (hankelBootB1_le_B1k_gen hc3 hf hε hM hT hu0 huA hR_pos hRu hRA' 0).trans
      (hankelBootB1k_le_two_gen hc3 hf hε hM hu0 huA hRu hRA' hR_pos hsmall' 0)
  have hB2_le1 : B_2 ≤ 1 := hankelBootB2_le_one hc0 hfe hM R
  set L := P.C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
  have hC_fb : 1 ≤ P.C_fb := P.hCfb
  have hL_lb : 1 ≤ L := by
    have h1 : 1 ≤ c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 := by
      have : 0 ≤ c ^ (1 / 3 : ℝ) * (B_1 + B_2) :=
        mul_nonneg (Real.rpow_nonneg hc0.le _) (by linarith)
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ P.C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) := mul_le_mul hC_fb h1 zero_le_one (by linarith)
  have hL_ub : L ≤ P.C_L * c ^ P.γ := by
    have hc13_le : c ^ (1 / 3 : ℝ) ≤ c := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have h1 : c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ 4 * c := by
      have hB3_le : B_1 + B_2 ≤ 3 := by linarith
      calc c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ c * 3 + c :=
          add_le_add (mul_le_mul hc13_le hB3_le (by linarith) hc0.le) hc1
        _ = 4 * c := by ring
    show P.C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) ≤ (4 * P.C_fb) * c ^ (1 : ℝ)
    rw [Real.rpow_one]
    calc P.C_fb * (c ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) ≤ P.C_fb * (4 * c) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = (4 * P.C_fb) * c := by ring
  have hYV : YVEnvBound (hankelPsi c f) c R L :=
    hankel_yv_window_gen hU3 hc hScale hf hε hM hT hu0 huU huA hR1 hR2
  have hlobe := hankelBoot_lobe_le hc1
  have hRinf_le : hankelRinf c ≤ Rinf_coeff * hankelRinf c :=
    le_mul_of_one_le_left hr (by dsimp only [Rinf_coeff]; linarith [le_max_left 70 (hankelLineRinfCoeffGen U)])
  have hRinf_coeff_pos : 0 < Rinf_coeff := by
    dsimp only [Rinf_coeff]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hrinf_ub : Rinf_coeff * hankelRinf c ≤ P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-P.κ * c) := by
    have h1 : Real.exp (-(c / 40000)) ≤ Real.exp (-(1 / 600000 : ℝ) * c) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 := hankelTailI0_nonneg'
    have h3 : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    have hC0_ge : 2 * Rinf_coeff * hankelTailI0 ≤ P.C_0 := le_max_right _ _
    have hκ : P.κ = 1 / 600000 := rfl
    rw [hκ]
    calc Rinf_coeff * hankelRinf c
        = (2 * Rinf_coeff * hankelTailI0 * c ^ (1 / 3 : ℝ)) * Real.exp (-(c / 40000)) := by
          unfold hankelRinf; ring
      _ ≤ (2 * Rinf_coeff * hankelTailI0 * c ^ (1 / 3 : ℝ)) * Real.exp (-(1 / 600000 : ℝ) * c) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ P.C_0 * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 600000 : ℝ) * c) := by
          rw [mul_assoc (2 * Rinf_coeff * hankelTailI0), mul_assoc P.C_0]
          exact mul_le_mul_of_nonneg_right hC0_ge (mul_nonneg h3 (Real.exp_pos _).le)
  have hw_eq : 1 / P.w_star = hbWeight D (D.tm : ℂ) := by
    show 1 / (1 / hbWeight D (D.tm : ℂ)) = _
    rw [one_div_one_div]
  refine ⟨{
    c := c
    R := R
    a := √R
    B_1 := B_1
    B_2 := B_2
    L := L
    x_tilde := u_T - D.tm
    r_inf := Rinf_coeff * hankelRinf c
    C_err := 16
    hc := by linarith
    ha_lb := by
      calc P.b * c ^ (1 / 3 : ℝ) = √(P.b ^ 2 * c ^ (2 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq P.hb.le,
              show c ^ (2 / 3 : ℝ) = (c ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hc0.le _)]
        _ ≤ √R := Real.sqrt_le_sqrt hR1
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := by
      have : (0 : ℝ) ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by positivity
      show R ≤ 2 * (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1
      linarith
    hB1 := hB1_nn
    hB2 := hB2_nn
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := by linarith
    hx_ub := hB2.uT_sub_le
    hr_inf_nn := mul_nonneg hRinf_coeff_pos.le hr
    hr_inf_ub := hrinf_ub
    hC_err_nn := by norm_num
    hC_err_ub := le_max_left _ _
    B_1k := fun k => hankelBootB1k c f R u_T k
    B_2' := fun _ => B_2
    P_nodes := fun k ℓ => hankelBootMultilevelNodes D c f R ℓ k
    I_line := fun k ℓ => ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re
    Arc_cov := fun k ℓ => (28 / 5 : ℝ) * virasoroArcCov c R 0 L ℓ (fun _ => 0) k
    Arc_unc := ((28 / 5 : ℝ) * hankelArcUncConst) * c ^ (-(3 / 8 : ℝ))
    hB1k_nn := fun k _ _ => hankelBootB1k_nonneg_gen hc3 hf hε hM hT hu0 huA hR_pos hRu hRA' k
    hB2'_nn := fun _ _ _ => hB2_nn
    hB_sum := fun k _ _ => by
      have := hankelBootB1_le_B1k_gen hc3 hf hε hM hT hu0 huA hR_pos hRu hRA' k
      show B_1 + B_2 ≤ hankelBootB1k c f R u_T k + B_2
      linarith
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 :=
        hℓ_mem.2.trans ((min_le_left _ _).trans (shellHBQuantData D).2.2.1 |>.trans (by norm_num))
      exact hankelBootMultilevel_arc D hQ hc3 hfe hε hM h_c12 hR10 hRA hRc (by linarith)
        hℓ_nn hℓ_half hYV hR_low (show 9 ≤ k from hk0)
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ := by
        have hpos : 0 < P.D_1 * c ^ (-(1 / 3 : ℝ)) := by
          have : P.D_1 = hankelBeta1 * (R_off + 1) := rfl
          have hβ := hankelBeta1_pos
          rw [this]; positivity
        exact lt_of_lt_of_le hpos hℓ_mem.1
      have hle := virasoroArcCov_le (c' := c) (T := 0) hR10 (zero_le_one.trans hL_lb) hℓ_pos
        (fun _ => (0 : ℝ)) (k := k) (by have : 9 ≤ k := hk0; omega)
      have hscaled := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 28 / 5)
      have hCa : (28 / 5 : ℝ) * virasoroArcCovConst ≤ P.C_a := le_max_left _ _
      have hG : 0 ≤ Real.Gamma ((k : ℝ) + 1 / 2) := (Real.Gamma_pos_of_pos (by positivity)).le
      refine hscaled.trans ?_
      calc (28 / 5 : ℝ) *
            (virasoroArcCovConst * L * (√R)⁻¹ *
              (2 ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)))
          = ((28 / 5 : ℝ) * virasoroArcCovConst) * L * (√R)⁻¹ *
              (2 ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by
            ring
        _ ≤ P.C_a * L * (√R)⁻¹ *
              (2 ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by
            gcongr
    hArc_unc := le_rfl
    hI_line := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc0.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 :=
        hℓ_mem.2.trans ((min_le_left _ _).trans (shellHBQuantData D).2.2.1 |>.trans (by norm_num))
      have hk9 : 9 ≤ k := hk0
      have hlb := hankelBoot_line_bound_gen hU0 hc3 hf hε hM hT hu0 huU huA hUR hR10 hRA hAR
        hℓ_nn hℓ_half (k := k) (by omega) hkR
      have hCa : hankelLineCaGen U ≤ P.C_a := le_max_right _ _
      have h_ca_term : hankelLineCaGen U * ((k : ℝ) + 1) / R ≤ P.C_a * ((k : ℝ) + 1) / R := by
        gcongr
      have hRinf_line : hankelLineRinfCoeffGen U ≤ Rinf_coeff := le_max_right _ _
      have h_rinf_term : hankelLineRinfCoeffGen U * R * hankelRinf c ≤
          R * (Rinf_coeff * hankelRinf c) := by
        have : hankelLineRinfCoeffGen U * hankelRinf c ≤ Rinf_coeff * hankelRinf c :=
          mul_le_mul_of_nonneg_right hRinf_line hr
        nlinarith [mul_le_mul_of_nonneg_left this hR_pos.le]
      have h_lobe : hankelLobe c ≤ 16 * c * Real.exp (-P.κ * c) := by
        have hκ : P.κ = 1 / 600000 := rfl
        rw [hκ]; linarith [hlobe]
      show ∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re ≤
        -(63 / 100 : ℝ) * hankelBootB1k c f R u_T k - B_2 + P.C_a * ((k : ℝ) + 1) / R +
          R * (Rinf_coeff * hankelRinf c) + 16 * c * Real.exp (-P.κ * c)
      linarith only [hlb, h_ca_term, h_rinf_term, h_lobe]
    hW_top := hbTopWeights_nonneg D
    hP_nodes_lb_hb := fun k ℓ hk0 hkR hℓ_mem => by
      have hnb := hankelBootMultilevel_nodes_lb D hQ P.hD1 hc3 hf hε hM hT htm_uT hB2
        huA hR_S' hRA hsites hℓ_mem.1 hℓ_mem.2 hkR hD1_small
      have hΛ : tebLambdaN P (hbTopWeights D) =
          2 * (M_pow * (shellHBQuantData D).1.2.2) * (hbWeight D (D.tm : ℂ) + hbTopWeights D) := by
        unfold tebLambdaN
        rw [hw_eq]; rfl
      have hCα_rinf : M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c ≤
          P.C_α * R ^ (3 / 2 : ℝ) * (Rinf_coeff * hankelRinf c) := by
        have : M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) = P.C_α * R ^ (3 / 2 : ℝ) := rfl
        rw [this]
        exact mul_le_mul_of_nonneg_left hRinf_le (mul_nonneg P.hCα (by positivity))
      rw [hΛ]
      linarith only [hnb, hCα_rinf]
    P_theta_bound := fun hk0_R hℓ_mem => by
      have hθ0 := tebThetaHB_pos P (hbTopWeights_nonneg D)
      have hθ1 := tebThetaHB_le_half P (hbTopWeights D)
      have hnb := hankelBootMultilevel_nodes_theta D hQ P.hD1 hc3 hf hε hM hT htm_uT hB2
        huA hR_S' hRA hsites hθ0 hθ1 hℓ_mem.1 hℓ_mem.2 hk0_R hR_tm hD1_small
      have hθ_le : 2 * (M_pow * (shellHBQuantData D).1.2.2) * hbTopWeights D *
          tebThetaHB P (hbTopWeights D) ≤ P.κ_star / (4 * P.w_star) := by
        have h1 : tebThetaHB P (hbTopWeights D) ≤
            P.κ_star / (8 * P.w_star * P.C_1 * (hbTopWeights D + 1)) := by
          unfold tebThetaHB; exact min_le_right _ _
        have hWnn := hbTopWeights_nonneg D
        have hWlt : hbTopWeights D ≤ hbTopWeights D + 1 := by linarith
        have hC1p := P.hC1
        have hw_p := P.hw_star
        have hκ_p := P.hκ_star
        have h2 : 2 * P.C_1 * hbTopWeights D * tebThetaHB P (hbTopWeights D) ≤
            2 * P.C_1 * hbTopWeights D * (P.κ_star / (8 * P.w_star * P.C_1 * (hbTopWeights D + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : 2 * P.C_1 * hbTopWeights D * (P.κ_star / (8 * P.w_star * P.C_1 * (hbTopWeights D + 1))) ≤
            P.κ_star / (4 * P.w_star) := by
          have hden : 0 < hbTopWeights D + 1 := by linarith
          calc 2 * P.C_1 * hbTopWeights D * (P.κ_star / (8 * P.w_star * P.C_1 * (hbTopWeights D + 1)))
              = (P.κ_star / (4 * P.w_star)) * (hbTopWeights D / (hbTopWeights D + 1)) := by
                field_simp [hC1p.ne', hw_p.ne', hden.ne']; ring
            _ ≤ (P.κ_star / (4 * P.w_star)) * 1 := by
                gcongr; exact (div_le_one hden).mpr hWlt
            _ = P.κ_star / (4 * P.w_star) := mul_one _
        exact h2.trans h3
      have hkappa_half : (shellHBQuantData D).1.2.1 * hbWeight D (D.tm : ℂ) / 2 =
          P.κ_star / (2 * P.w_star) := by
        have : P.κ_star = (shellHBQuantData D).1.2.1 := rfl
        rw [← this]
        calc P.κ_star * hbWeight D (D.tm : ℂ) / 2
            = P.κ_star * (1 / P.w_star) / 2 := by rw [hw_eq]
          _ = P.κ_star / (2 * P.w_star) := by ring
      have hdiv : P.κ_star / (2 * P.w_star) - P.κ_star / (4 * P.w_star) = P.κ_star / (4 * P.w_star) := by
        ring
      have hcoeff : P.κ_star / (4 * P.w_star) ≤
          (shellHBQuantData D).1.2.1 * hbWeight D (D.tm : ℂ) / 2 -
            2 * (M_pow * (shellHBQuantData D).1.2.2) * hbTopWeights D * tebThetaHB P (hbTopWeights D) := by
        linarith only [hθ_le, hkappa_half, hdiv]
      have hterm_ge : P.κ_star / (4 * P.w_star) * (u_T - D.tm) ≤
          ((shellHBQuantData D).1.2.1 * hbWeight D (D.tm : ℂ) / 2 -
            2 * (M_pow * (shellHBQuantData D).1.2.2) * hbTopWeights D * tebThetaHB P (hbTopWeights D)) *
            (u_T - D.tm) :=
        mul_le_mul_of_nonneg_right hcoeff (by linarith)
      have hCα_rinf : M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) * hankelRinf c ≤
          P.C_α * R ^ (3 / 2 : ℝ) * (Rinf_coeff * hankelRinf c) := by
        have : M_pow * hbWeightSumConst D * R ^ (3 / 2 : ℝ) = P.C_α * R ^ (3 / 2 : ℝ) := rfl
        rw [this]
        exact mul_le_mul_of_nonneg_left hRinf_le (mul_nonneg P.hCα (by positivity))
      linarith only [hnb, hterm_ge, hCα_rinf]
  }, le_rfl, rfl, rfl⟩

private lemma hankel_prescribed_normalize {D : ShellHBData} {r : ℝ → ℝ → ℝ} {c ε T : ℝ}
    (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelPrescribed D r c ε T f) :
    ∃ g : ℝ → ℝ, IsHankelPrescribed D r c ε T g ∧ hankelMass c g = 1 := by
  obtain ⟨Δ0, hΔ0, hne⟩ := hf.nonzero
  have hm : 0 < hankelMass c f :=
    hankelMass_pos_of_continuousOn hc hf.cont hf.int ⟨Δ0, hΔ0, hne⟩
  set m := hankelMass c f with hmdef
  have hmi : 0 < m⁻¹ := inv_pos.2 hm
  refine ⟨fun Δ => m⁻¹ * f Δ, ⟨⟨hf.toIsHankelEigenfn.smul m⁻¹, ⟨Δ0, hΔ0, mul_ne_zero hmi.ne' hne⟩,
    ?_, fun Δ hΔ => mul_nonneg hmi.le (hf.tail_nonneg Δ hΔ)⟩,
    fun s hs => mul_nonneg hmi.le (hf.sites_nonneg s hs)⟩,
    by rw [hankelMass_smul, abs_of_pos hmi, inv_mul_cancel₀ hm.ne']⟩
  have := hf.origin_sign
  show ε * (m⁻¹ * f 0) ≤ 0
  nlinarith [mul_nonneg hmi.le (neg_nonneg.2 this)]

/-- **`u1cl:multilevel` lower half (`O(1)`)** at every Hermite–Biehler configuration `D : ShellHBData`:
for every `R_off ≥ 0` there exist constants `C, c₀` such that for all `c ≥ c₀`, either sign `ε = ±1`,
all bounded offsets `|r t c'| ≤ R_off`, and any prescribed feasible profile `(T, f)`,
`hbModel D c - C ≤ T`. -/
theorem hbMultilevelLower_proved (D : ShellHBData) : HbMultilevelLower D := by
  by_cases hQ : D.Q = 0
  · exact hbMultilevelLower_Q_eq_zero D hQ
  · intro R_off hR
    let P := hankelBootMultilevelParams D hQ R_off hR
    let M_S := D.S.sup' D.S_nonempty (fun s => |s|)
    let U := max 3 (M_S + 1)
    let K₀ := tebK0HB P (hbTopWeights D)
    obtain ⟨c_q, hc_q, hquant⟩ := hankel_quantC1_multilevel_of_feasible D R_off hR
    obtain ⟨T₀, hT₀, hcirc⟩ := airyPQ_good_circle_real D.P D.Q hQ
    obtain ⟨c_sm, hsm⟩ := eventually_atTop.1 hankel_small_eventually
    have hM_S_nn : 0 ≤ M_S := le_trans (abs_nonneg D.tm) (Finset.le_sup' (fun s => |s|) D.tm_mem)
    have hscale_lim : Tendsto langerScale atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).atTop_mul_const langerKappa_pos
    have hc23_lim : Tendsto (fun c : ℝ => (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (by norm_num)
    have hd1_lim : Tendsto (fun c : ℝ => P.D_1 * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      have : Tendsto (fun c : ℝ => P.D_1 / c ^ (1 / 3 : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
      rw [div_eq_mul_inv, Real.rpow_neg hc.le]
    have hxi_ev := hankelXi_approx_eventually (U := M_S + 1) (δ := 1) (by linarith) zero_lt_one
    have hev_all : ∀ᶠ c in atTop,
        max (max c_q 1e14) (max ((3 * π) ^ (12 : ℕ)) (max (tebC2 P) c_sm)) ≤ c ∧
        11 * U ≤ langerScale c ∧
        max T₀ (max (M_S + 2) (max 48 (2 * ((9 : ℝ) + 1) * (-D.tm)))) ≤
          (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ∧
        P.D_1 * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4 ∧
        (M_S + 1 ≤ langerRadius c ∧
          ∀ x : ℝ, |x| ≤ M_S + 1 →
            |c * hankelXi c x - (c / π ^ 2 - x * c ^ (1 / 3 : ℝ) / hankelBeta1)| ≤ 1) := by
      refine (eventually_ge_atTop _).and ?_
      refine (hscale_lim.eventually_ge_atTop (11 * U)).and ?_
      refine (hc23_lim.eventually_ge_atTop _).and ?_
      have hd1_ev : ∀ᶠ c : ℝ in atTop, P.D_1 * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 4 :=
        hd1_lim (Iic_mem_nhds (by norm_num))
      exact hd1_ev.and hxi_ev
    obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.1 hev_all
    let C : ℝ := max 1 (K₀ / hankelBeta1 + 1)
    refine ⟨C, max c_ev (max c_q 1e14), fun c hc ε hε r hr T f hf => ?_⟩
    have hc_ev' : c_ev ≤ c := (le_max_left _ _).trans hc
    obtain ⟨hc_max, hScale, hc23, hD1_sm, hMA, hxi_approx⟩ := hc_ev c hc_ev'
    have hcq : c_q ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc_max)
    have hc14 : 1e14 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc_max)
    have h_c12 : (3 * π) ^ (12 : ℕ) ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc_max)
    have hc_teb : tebC2 P ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_max))
    have hc_sm : c_sm ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc_max))
    have hc0 : 0 < c := by linarith
    have htm_M : |D.tm| ≤ M_S := Finset.le_sup' (fun s => |s|) D.tm_mem
    have htm_neg : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (airyZero_neg 1)
    have hmodel_eq : hbModel D c = c / π ^ 2 - D.tm * c ^ (1 / 3 : ℝ) / hankelBeta1 := by
      unfold hbModel; ring
    obtain ⟨g, hg_pres, hg_mass⟩ := hankel_prescribed_normalize hc0 hf
    have hg_feas := hg_pres.toIsHankelFeasible
    by_cases hT_ge : c * hankelXi c D.tm ≤ T
    · have hxi_tm := (abs_le.mp (hxi_approx D.tm (by linarith))).1
      have h1 : hbModel D c - 1 ≤ T := by linarith only [hmodel_eq, hxi_tm, hT_ge]
      linarith only [h1, le_max_left (1 : ℝ) (K₀ / hankelBeta1 + 1)]
    · push Not at hT_ge
      obtain ⟨u_T, htm_uT, _, hT_eq, hB2, u_site, hsites_spec⟩ :=
        hquant c hcq ε hε r hr T g hg_pres hg_mass hT_ge
      have hT₀_le : T₀ ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := (le_max_left _ _).trans hc23
      obtain ⟨R, hR1, hR2, hR_low⟩ := hcirc ((1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) hT₀_le
      have hM2_le : M_S + 2 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) :=
        (le_max_left _ _).trans ((le_max_right _ _).trans hc23)
      have h48_le : 48 ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) :=
        (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc23))
      have hR_tm_le : 2 * ((9 : ℝ) + 1) * (-D.tm) ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) :=
        (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc23))
      have hR_S : max (M_S + 2) 48 ≤ R := max_le (by linarith) (by linarith)
      have hR_tm : 2 * ((9 : ℝ) + 1) * (-D.tm) ≤ R := by linarith
      have hsites' : ∀ t ∈ D.S.erase D.tm,
          |u_site t - t| ≤ hankelBeta1 * (R_off + 1) * c ^ (-(1 / 3 : ℝ)) ∧
          |u_site t| ≤ langerRadius c ∧ -hankelRinf c ≤ hankelPsiR c g (u_site t) :=
        fun t ht => ⟨(hsites_spec t ht).1, (hsites_spec t ht).2.1, (hsites_spec t ht).2.2⟩
      obtain ⟨I, hI_L, hI_c, hI_x⟩ := hankelBootMultilevelHBAt D hQ R_off hR hc14 hScale h_c12 h48_le
        hR1 hR2 hR_S hR_tm hR_low hg_feas hε hg_mass hT_eq htm_uT hB2 hsites' (hsm c hc_sm) hD1_sm
      have hboot := (teb_bootstrap_hb P I (hI_c.symm ▸ hc_teb)).2 hI_L
      have huT_boot : c ^ (1 / 3 : ℝ) * (u_T - D.tm) ≤ K₀ := by
        rw [← hI_c, ← hI_x]; exact hboot.2
      have hu0 : u_T ≤ 0 := by
        have h1 := hB2.uT_sub_le.trans (min_le_left _ _)
        have hδ := (shellHBQuantData D).2.2.1
        have ha := airyZero_one.2
        linarith [D.tm_le_airyZero_one]
      have hu_abs : |u_T| ≤ M_S + 1 := by
        rw [abs_le]
        exact ⟨by linarith [(abs_le.mp htm_M).1, htm_uT], by linarith⟩
      have hxi_uT := (abs_le.mp (hxi_approx u_T hu_abs)).1
      have hk_div : (u_T - D.tm) * c ^ (1 / 3 : ℝ) / hankelBeta1 ≤ K₀ / hankelBeta1 :=
        div_le_div_of_nonneg_right (by linarith [huT_boot]) hankelBeta1_pos.le
      have hxi_step : hbModel D c - (K₀ / hankelBeta1 + 1) ≤ T := by
        have heq1 : hbModel D c - (u_T - D.tm) * c ^ (1 / 3 : ℝ) / hankelBeta1 - 1 =
            c / π ^ 2 - u_T * c ^ (1 / 3 : ℝ) / hankelBeta1 - 1 := by
          rw [hmodel_eq]; ring
        linarith only [heq1, hxi_uT, hT_eq, hk_div]
      linarith only [hxi_step, le_max_right (1 : ℝ) (K₀ / hankelBeta1 + 1)]

/-- info: 'FormalResearch.SignUncertainty.hbMultilevelLower_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbMultilevelLower_proved

end FormalResearch.SignUncertainty
