module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWNodes

/-!
# The Concrete `BootstrapHBInstance` at Every Fixed `(w, Q)` (Theorem `FT-L.FW`, Steps 0-4)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 0-5, and
`CFT/common/two_edge_bootstrap.tex`, Theorem `TE.2(4)` (`teb:bootstrap`).

* `bootstrapParamsForW`: concrete `BootstrapParams` at scale `b` (`N = Ai`, `m₀ = 1`, `k₀ = 5`), with
  `C_a = max C_a⁰ (4e^{6/5} + 3 C₀)`, `C_unc = LemmaQData.arcUncConst` (`C₀` the type-(II) constant of
  `Lemma Q (2)` at weight `w`);
* `lobe_scale_downW`: the scale-`b` lobe facts give the full-scale ones (`lemmaQ_general_lobe_scale_down`);
* `uT_range_of_violatorW`: range of `u_T`, `Δ(0) ≤ T ≤ Δ(-A_thr)` for a violator `T < Δ(a₁)`;
* `LemmaQData.sigma_arc_of_scale`: the arc condition on `ς` at `R + 1 ≤ A_{c'}(b)²`;
* `bootstrapHB_of_YVForW`: the `BootstrapHBInstance P 0` with `(B3)` from `YVInputAtForW prob b ψ̃`
  (the Virasoro `virasoro_bootstrapHB_of_YVFor`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem}


/-- Concrete `BootstrapParams` for `(P, Q) = (1, 0)` on Virasoro at scale `b > 0`. -/
noncomputable def bootstrapParamsForW (Q : LemmaQData prob)
    (b : ℝ) (hb : 0 < b)
    (C_fb : ℝ) (hC_fb : 1 ≤ C_fb)
    (C_gap κ_gap : ℝ) (_hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap) :
    BootstrapParams where
  b := b
  C_a := max virasoroArcCovConst (4 * Real.exp (6 / 5) + 3 * Q.C0)
  C_unc := Q.arcUncConst
  C_1 := quantC1C1
  w_star := quantC1WStar
  κ_star := quantC1KappaStar
  C_α := 0
  C_fb := C_fb
  D_1 := 1
  η_0 := quantC1Eta0
  δ_star := quantC1DeltaStar
  κ := κ_gap
  C_0 := max 1 C_gap
  C_L := 4 * C_fb
  γ := 1
  k_0 := 5
  hb := hb
  hCa := le_trans virasoroArcCovConst_pos.le (le_max_left _ _)
  hCunc := Q.arcUncConst_pos.le
  hC1 := quantC1C1_pos
  hw_star := quantC1WStar_pos
  hκ_star := quantC1KappaStar_pos
  hCα := le_rfl
  hCfb := hC_fb
  hD1 := zero_le_one
  hη0 := quantC1Eta0_pos
  hδ_star := quantC1DeltaStar_pos
  hκ := hκ_gap
  hC0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  hCL := by linarith
  hγ := zero_le_one
  hk0 := by omega


namespace LemmaQData

variable (Q : LemmaQData prob)

lemma sigma_arc_of_scale {b c' R : ℝ} (hb_pos : 0 < b) (hc'_ge1 : 1 ≤ c')
    (hR_ub_b : R + 1 ≤ chartACAt b c' ^ 2)
    (hς_arc : Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1) :
    Q.sigma c' * (3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1) ≤ 1 := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc'_ge1
  have hsig_nn := Q.sigma_nonneg hc'_ge1
  have hR_le_ac : R ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) := by
    rw [← chartACAt_sq b c' hc'_pos.le]; linarith [hR_ub_b]
  have hsqrtR : √R ≤ √2 * b * c' ^ (1 / 3 : ℝ) := by
    calc √R ≤ √(2 * b ^ 2 * c' ^ (2 / 3 : ℝ)) := Real.sqrt_le_sqrt hR_le_ac
      _ = √(chartACAt b c' ^ 2) := by rw [chartACAt_sq b c' hc'_pos.le]
      _ = chartACAt b c' := Real.sqrt_sq (chartACAt_pos hb_pos hc'_pos).le
      _ = √2 * b * c' ^ (1 / 3 : ℝ) := rfl
  have hc14 : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 12 : ℝ)) = c' ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hc'_pos]; norm_num
  have h3pi : 3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1 ≤
      3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1 := by
    calc 3 * π * √R * c' ^ (-(1 / 12 : ℝ)) + 1
        ≤ 3 * π * (√2 * b * c' ^ (1 / 3 : ℝ)) * c' ^ (-(1 / 12 : ℝ)) + 1 := by gcongr
      _ = 3 * π * √2 * b * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 12 : ℝ))) + 1 := by ring
      _ = 3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1 := by rw [hc14]
  exact (mul_le_mul_of_nonneg_left h3pi hsig_nn).trans hς_arc

end LemmaQData

variable [Q : LemmaQData prob]

/-- The scale-`b` lobe facts give the full-scale ones (the Virasoro `virasoro_lobe_scale_down`). -/
lemma lobe_scale_downW {b C_gap κ_gap c' T : ℝ}
    (hb_pos : 0 < b) (hb_le : b ≤ Q.bV) (hc'_Qenv : Q.cQ ≤ c')
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hdl_bd : deltaLobeAt prob b c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : deltaLobeAt prob b c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (chartACAt b c' ^ 2) < T) :
    chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 ∧
    deltaLobe prob Q.D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
    deltaLobe prob Q.D.r_1 c' g < 1 / 2 ∧
    virasoroDeltaChart c' (Q.AC c' ^ 2) < T :=
  lemmaQ_general_lobe_scale_down Q.D hb_pos hb_le (Q.hcQ_D.trans hc'_Qenv) hg.1
    (Q.cardyNorm_pos hc'_Qenv hg) hdl_bd hdl_half hT_A2

lemma uT_range_of_violatorW {c' R T : ℝ}
    (hc'_Qenv : Q.cQ ≤ c') (hR_thr : virasoroAThr ≤ R)
    (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) < T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (psiTilde prob c' g) (virasoroUT c' T)) :
    airyZero 1 < virasoroUT c' T ∧
    virasoroUT c' T ≤ -1 ∧
    virasoroDeltaChart c' (-1) ≤ T ∧
    virasoroDeltaChart c' 0 ≤ T ∧
    T ≤ virasoroDeltaChart c' (-virasoroAThr) ∧
    T ≤ virasoroDeltaChart c' (-R) := by
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hA2_ge4 : 4 ≤ Q.AC c' ^ 2 := by linarith [virasoroAThr_gt_two]
  have huT_Ioo : virasoroUT c' T ∈ Ioo (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2) :=
    (Q.part3 hc'_Qenv hg).2.2.1
      (hT_a1.trans ((Q.deltaChart_strictAnti hc'_pos)
        ⟨le_rfl, by linarith⟩
        ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
        (by linarith [airyZero_one.1])))
      hT_A2
  have hu_mem := Q.UT_between hc'_pos
    (by linarith [huT_Ioo.1]) (by linarith [huT_Ioo.2])
    (by linarith [huT_Ioo.1, huT_Ioo.2] : -(Q.AC c' ^ 2) ≤ Q.AC c' ^ 2)
    hT_A2.le
    (hT_a1.le.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩
      ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
      (by linarith [airyZero_one.1])))
  set u_T := virasoroUT c' T
  have hΔ_uT : virasoroDeltaChart c' u_T = T := hu_mem.2
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩
      ⟨by linarith [airyZero_one.1], by linarith [airyZero_one.2]⟩
      (not_lt.mp hle)
    linarith [hΔ_uT]
  have huT_le_m1 : u_T ≤ -1 := by
    have := (hB2.1).trans ((min_le_left _ _).trans quantC1DeltaStar_le)
    linarith [airyZero_one.2]
  have hT_lo_m1 : virasoroDeltaChart c' (-1) ≤ T := by
    rw [← hΔ_uT]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩ ⟨by linarith, by linarith⟩ huT_le_m1
  have hT_lo_0 : virasoroDeltaChart c' 0 ≤ T := by
    rw [← hΔ_uT]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hT_hi_AThr : T ≤ virasoroDeltaChart c' (-virasoroAThr) := by
    rw [← hΔ_uT]
    have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
      unfold virasoroAThr; rw [abs_of_neg (by linarith [airyZero_one.2])]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith [virasoroAThr_pos]⟩ ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩
      (by linarith [ha1_lt_uT, hAThr_eq])
  have hT_hi_R : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi_AThr.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [virasoroAThr_pos]⟩ (by linarith))
  exact ⟨ha1_lt_uT, huT_le_m1, hT_lo_m1, hT_lo_0, hT_hi_AThr, hT_hi_R⟩


/-- Construct the concrete `BootstrapHBInstance P 0` (together with `(B3)`) at scale
`0 < b ≤ Q.bV` for any violator `T < Δ(a₁)` at sufficiently large `c'`,
assuming `YVInputAtForW prob b`. -/
noncomputable def bootstrapHB_of_YVForW
    {b C_fb c_YV C_gap κ_gap : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hC_fb : 1 ≤ C_fb) (_hc_YV : 10000 ≤ c_YV)
    (hYVat : YVInputAtForW prob b (psiTilde prob) C_fb c_YV)
    (hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap)
    {c' T : ℝ} (hc'_Qenv : Q.cQ ≤ c') (hc'_YV : c_YV ≤ c')
    (h_c12 : (3 * π) ^ (12 : ℕ) ≤ c')
    (h_b48 : 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    (hς_half : Q.sigma c' ≤ 1 / 2)
    (hς_arc : Q.sigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hdl_bd : deltaLobeAt prob b c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hdl_half : deltaLobeAt prob b c' g < 1 / 2)
    (hT_A2 : virasoroDeltaChart c' (chartACAt b c' ^ 2) < T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (psiTilde prob c' g) (virasoroUT c' T)) :
    let P := bootstrapParamsForW Q b hb_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
    { I : BootstrapHBInstance P 0 //
      I.L ≤ P.C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧
      I.c = c' ∧ I.x_tilde = virasoroUT c' T - airyZero 1 } := by
  intro P
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  obtain ⟨hA2_le, hdl_bd_full, hdl_half_full, hT_A2_full⟩ :=
    lobe_scale_downW hb_pos hb_le hc'_Qenv hg hdl_bd hdl_half hT_A2
  let k₀ : ℕ := ⌈b ^ 2 * c' ^ (2 / 3 : ℝ)⌉₊
  have hk₀_ge48 : 48 ≤ k₀ := by
    dsimp [k₀]
    have : (48 : ℝ) ≤ (⌈b ^ 2 * c' ^ (2 / 3 : ℝ)⌉₊ : ℝ) :=
      h_b48.trans (Nat.le_ceil _)
    exact_mod_cast this
  have h_circ := good_circle_exists k₀ (by omega : 10 ≤ k₀)
  let R : ℝ := Classical.choose h_circ
  have hR_spec := Classical.choose_spec h_circ
  have hR_lb : (k₀ : ℝ) ≤ R := hR_spec.1
  have hR_le_k : R ≤ (k₀ : ℝ) + 1 := hR_spec.2.1
  have hR_low := hR_spec.2.2
  have hR_48 : 48 ≤ R := (by exact_mod_cast hk₀_ge48 : (48 : ℝ) ≤ k₀).trans hR_lb
  have hR_pos : 0 < R := by linarith
  have hR_bv : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := (Nat.le_ceil _).trans hR_lb
  have hR_ub_ceil : R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 2 := by
    have hlt := Nat.ceil_lt_add_one (by positivity : 0 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ))
    linarith
  have hR_ub_2b : R ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := by linarith
  have hR_ub_b : R + 1 ≤ chartACAt b c' ^ 2 := by
    rw [chartACAt_sq b c' hc'_pos.le]; linarith
  have hR_ub : R + 1 ≤ Q.AC c' ^ 2 := hR_ub_b.trans hA2_le
  have hAThr_lt : virasoroAThr < 3.4 := by
    obtain ⟨ha1, ha2⟩ := airyZero_one
    unfold virasoroAThr; rw [abs_of_neg (by linarith)]; linarith
  have hR_thr : virasoroAThr ≤ R := by linarith
  have h_good_ai : ∀ u : ℂ, ‖u‖ = R → airyAiC u ≠ 0 := by
    intro u hu h0
    have h1 := hR_low u hu
    rw [h0, norm_zero] at h1
    have h2 : 0 < 1 / (25 * π) * (1 + R) ^ (-(1 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u
      have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + R) (-(1 / 2 : ℝ))
      positivity
    linarith
  have hN_ex := airy_circleData hR_pos h_good_ai
  let N : ℕ := Classical.choose hN_ex
  have hN_spec := Classical.choose_spec hN_ex
  have hN : ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R) := hN_spec.1
  have hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R := hN_spec.2
  have hRp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖(airyBiC w - I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rplus_bound him (hw ▸ hR_low w hw)
  have hRm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖(airyBiC w + I * airyAiC w) / airyAiC w‖ * airyEnv w ≤ 30 * √π :=
    fun w hw him => airy_Rminus_bound him (hw ▸ hR_low w hw)
  obtain ⟨ha1_lt_uT, huT_le_m1, hT_lo_m1, hT_lo_0, hT_hi_AThr, hT_hi_R⟩ :=
    uT_range_of_violatorW hc'_Qenv hR_thr hR_ub hg hT_A2_full hT_a1 hB2
  set u_T := virasoroUT c' T
  have hB_sums := band_sums_leW hc'_Qenv hR_thr hR_ub hg hdl_half_full hT_lo_0 hT_hi_AThr
  have hB1_nn : 0 ≤ bandB1W prob c' R T g :=
    bandB1W_nonneg hc'_Qenv hR_thr (by linarith) hg hT_lo_0 hT_hi_AThr
  have hB2_nn : 0 ≤ bandB2W prob c' R g :=
    bandB2W_nonneg hc'_Qenv hR_thr (by linarith) hg hT_hi_AThr
  set B_1 := bandB1W prob c' R T g
  set B_2 := bandB2W prob c' R g
  set L := C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
  have hL_lb : 1 ≤ L := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 := by
      have : 0 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) :=
        mul_nonneg (Real.rpow_nonneg hc'_pos.le _) (by linarith)
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) := mul_le_mul hC_fb h1 zero_le_one (by linarith)
  have hL_ub : L ≤ P.C_L * c' ^ P.γ := by
    have hc13_le : c' ^ (1 / 3 : ℝ) ≤ c' := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have h1 : c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ 4 * c' := by
      have hB3_le : B_1 + B_2 ≤ 3 := by linarith [hB_sums.1, hB_sums.2]
      calc c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1
          ≤ c' * 3 + c' := add_le_add
              (mul_le_mul hc13_le hB3_le (by linarith) hc'_pos.le) hc'_ge1
        _ = 4 * c' := by ring
    dsimp [L, P, bootstrapParamsForW]
    rw [Real.rpow_one]
    calc C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
        ≤ C_fb * (4 * c') := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 4 * C_fb * c' := by ring
  have hς_arc' := Q.sigma_arc_of_scale hb_pos hc'_ge1 hR_ub_b hς_arc
  have hYV_env : YVEnvBound (psiTilde prob c' g) c' R L :=
    hYVat hc'_YV hR_thr hR_bv hR_ub_b hg hT_lo_0 hT_hi_AThr
  have hPN := pnodes_lb_and_thetaW hc'_Qenv hR_48 hR_ub hg hT_hi_AThr hT_A2_full.le hT_a1 hB2 hN
    P rfl rfl rfl rfl rfl rfl
  refine ⟨{
    c := c'
    R := R
    a := √R
    B_1 := B_1
    B_2 := B_2
    L := L
    x_tilde := u_T - airyZero 1
    r_inf := 0
    C_err := C_gap
    hc := by linarith
    ha_lb := by
      calc P.b * c' ^ (1 / 3 : ℝ)
          = √(b ^ 2 * c' ^ (2 / 3 : ℝ)) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb_pos.le,
              show c' ^ (2 / 3 : ℝ) = (c' ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hc'_pos.le _)]
            rfl
        _ ≤ √R := Real.sqrt_le_sqrt hR_bv
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := hR_ub_2b
    hB1 := hB1_nn
    hB2 := hB2_nn
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := by linarith
    hx_ub := hB2.1
    hr_inf_nn := le_rfl
    hr_inf_ub := by have := P.hC0; positivity
    hC_err_nn := hC_gap.le
    hC_err_ub := le_max_right _ _
    B_1k := fun k => bandB1kW prob c' R T g k
    B_2' := fun _ => B_2
    P_nodes := fun k ℓ => pNodesW prob c' R ℓ g k N
    I_line := fun k ℓ => ∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re
    Arc_cov := fun k ℓ => virasoroArcCov c' R T L ℓ g k
    Arc_unc := Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))
    hB1k_nn := fun k _ _ => bandB1kW_nonneg hc'_Qenv hR_pos.le (by linarith) hg hT_A2_full.le
      hT_hi_R (by linarith [huT_le_m1]) k
    hB2'_nn := fun _ _ _ => hB2_nn
    hB_sum := fun k _ _ => by
      have := bandB1W_le_B1k hc'_Qenv hR_pos (by linarith) hg hT_lo_0 hT_hi_R k
      linarith
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      exact quad_arc_boundW hc'_Qenv h_c12 hς_arc'
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) hR_ub (zero_le_one.trans hL_lb)
        hℓ_nn hℓ_half hg hYV_env hD hRp hRm hk0
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ := by
        have hpos : 0 < P.D_1 * c' ^ (-(1 / 3 : ℝ)) := by
          have : P.D_1 = 1 := rfl
          rw [this]; positivity
        exact lt_of_lt_of_le hpos hℓ_mem.1
      have hle := virasoroArcCov_le (c' := c') (T := T)
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) (zero_le_one.trans hL_lb) hℓ_pos g hk0
      have hCa : virasoroArcCovConst ≤ P.C_a := le_max_left _ _
      refine hle.trans ?_
      gcongr
    hArc_unc := le_rfl
    hI_line := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg P.hD1 (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans quantC1DeltaStar_le)
      have hlb := line_boundW hc'_Qenv (Q.sigma_nonneg hc'_ge1) hς_half
        (by linarith) hR_ub hℓ_nn hℓ_half hg hT_lo_m1 hT_hi_AThr hk0 hkR
      have hCa : 4 * Real.exp (6 / 5) + 3 * Q.C0 ≤ P.C_a := le_max_right _ _
      have h_ca_term : (4 * Real.exp (6 / 5) + 3 * Q.C0) * ((k : ℝ) + 1) / R ≤
          P.C_a * ((k : ℝ) + 1) / R := by gcongr
      have h_exp_le : deltaLobe prob Q.D.r_1 c' g ≤ C_gap * c' * Real.exp (-P.κ * c') := by
        have hκ_eq : P.κ = κ_gap := rfl
        rw [hκ_eq]
        calc deltaLobe prob Q.D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') := hdl_bd_full
          _ = 1 * (C_gap * Real.exp (-κ_gap * c')) := (one_mul _).symm
          _ ≤ c' * (C_gap * Real.exp (-κ_gap * c')) :=
              mul_le_mul_of_nonneg_right hc'_ge1 (mul_nonneg hC_gap.le (Real.exp_pos _).le)
          _ = C_gap * c' * Real.exp (-κ_gap * c') := by ring
      linarith
    hW_top := le_rfl
    hP_nodes_lb_hb := fun k ℓ hk0 hkR hℓ_mem => by
      simpa using hPN.1 k ℓ hk0 hkR hℓ_mem
    P_theta_bound := fun hk0_R hℓ_mem => by
      simpa using hPN.2 hk0_R hℓ_mem
  }, le_rfl, rfl, rfl⟩


/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lobe_scale_downW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lobe_scale_downW

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.uT_range_of_violatorW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uT_range_of_violatorW

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bootstrapHB_of_YVForW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bootstrapHB_of_YVForW

end FormalResearch.ModularBootstrap.FixedWeightBand
