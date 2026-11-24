module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWNodes
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapHBCore

/-!
# The Concrete `BootstrapHBInstance` at Every Fixed `(w, Q)` (Theorem `FT-L.FW`, Steps 0-4)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 0-5, and
`CFT/common/two_edge_bootstrap.tex`, Theorem `TE.2(4)` (`teb:bootstrap`).

* `bootstrapParamsForW`: concrete `BootstrapParams` at scale `b` (`N = Ai`, `m₀ = 1`, `k₀ = 5`), with
  `C_a = max C_a⁰ (4e^{6/5} + 3 C₀)`, `C_unc = LemmaQData.arcUncConst` (`C₀` the type-(II) constant of
  `Lemma Q (2)` at weight `w`);
* `lobe_scale_downW`: the scale-`b` lobe facts give the full-scale ones (`lemmaQ_general_lobe_scale_down`);
* `uT_range_of_violatorW_thr`: range of `u_T`, `Δ(0) ≤ T ≤ Δ(-A_thr)` for a violator `T < Δ(a₁)` and every
  `A_thr ∈ [virasoroAThr, R]` (`uT_range_of_violatorW`: `A_thr = virasoroAThr`);
* `LemmaQData.sigma_arc_of_scale`: the arc condition on `ς` at `R + 1 ≤ A_{c'}(b)²`;
* `bootstrapHB_of_YVForWThr`: the `BootstrapHBInstance P 0` with `(B3)` from `YVInputAtForWThr prob A_thr b ψ̃` at
  every `A_thr ∈ [virasoroAThr, 47]`, with `bootstrapParamsForWThr` (line constant `C_line ≥ lineCaW A_thr`);
  `bootstrapHB_of_YVForW` (the Virasoro `virasoro_bootstrapHB_of_YVFor`) is the case `A_thr = virasoroAThr`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem}


/-- Concrete `BootstrapParams` for `(P, Q) = (1, 0)` on Virasoro at scale `b > 0`, with the line constant
`C_line` (any upper bound of `lineCaW A_thr` for the cutoff radii `A_thr` in use): `C_a = max C_a⁰ (C_line + 3 C₀)`. -/
noncomputable def bootstrapParamsForWThr (Q : LemmaQData prob)
    (b : ℝ) (hb : 0 < b)
    (C_fb : ℝ) (hC_fb : 1 ≤ C_fb)
    (C_gap κ_gap : ℝ) (_hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap) (C_line : ℝ) :
    BootstrapParams where
  b := b
  C_a := max virasoroArcCovConst (C_line + 3 * Q.C0)
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


/-- Concrete `BootstrapParams` for `(P, Q) = (1, 0)` on Virasoro at scale `b > 0` (the level-one line constant
`4 e^{6/5}`). -/
noncomputable def bootstrapParamsForW (Q : LemmaQData prob)
    (b : ℝ) (hb : 0 < b)
    (C_fb : ℝ) (hC_fb : 1 ≤ C_fb)
    (C_gap κ_gap : ℝ) (hC_gap : 0 < C_gap) (hκ_gap : 0 < κ_gap) :
    BootstrapParams :=
  bootstrapParamsForWThr Q b hb C_fb hC_fb C_gap κ_gap hC_gap hκ_gap (4 * Real.exp (6 / 5))


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

lemma uT_range_of_violatorW_thr {A_thr c' R T : ℝ} (hA : virasoroAThr ≤ A_thr)
    (hc'_Qenv : Q.cQ ≤ c') (hR_thr : A_thr ≤ R)
    (hR_ub : R + 1 ≤ Q.AC c' ^ 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hT_A2 : virasoroDeltaChart c' (Q.AC c' ^ 2) < T)
    (hT_a1 : T < virasoroDeltaChart c' (airyZero 1))
    (hB2 : QuantC1B2Holds (psiTilde prob c' g) (virasoroUT c' T)) :
    airyZero 1 < virasoroUT c' T ∧
    virasoroUT c' T ≤ -1 ∧
    virasoroDeltaChart c' (-1) ≤ T ∧
    virasoroDeltaChart c' 0 ≤ T ∧
    T ≤ virasoroDeltaChart c' (-A_thr) ∧
    T ≤ virasoroDeltaChart c' (-R) := by
  have hc'_10000 : 10000 ≤ c' :=
    (Q.hcQ_10000.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hA_pos : 0 < A_thr := lt_of_lt_of_le virasoroAThr_pos hA
  have hR_pos : 0 < R := lt_of_lt_of_le hA_pos hR_thr
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
  have hT_hi_AThr : T ≤ virasoroDeltaChart c' (-A_thr) := by
    rw [← hΔ_uT]
    have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
      unfold virasoroAThr; rw [abs_of_neg (by linarith [airyZero_one.2])]
    exact (Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith [hA_pos]⟩ ⟨huT_Ioo.1.le, huT_Ioo.2.le⟩
      (by linarith [ha1_lt_uT, hAThr_eq])
  have hT_hi_R : T ≤ virasoroDeltaChart c' (-R) :=
    hT_hi_AThr.trans ((Q.deltaChart_strictAnti hc'_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [hA_pos]⟩ (by linarith))
  exact ⟨ha1_lt_uT, huT_le_m1, hT_lo_m1, hT_lo_0, hT_hi_AThr, hT_hi_R⟩


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
    T ≤ virasoroDeltaChart c' (-R) :=
  uT_range_of_violatorW_thr le_rfl hc'_Qenv hR_thr hR_ub hg hT_A2 hT_a1 hB2

/-- Construct the concrete `BootstrapHBInstance P 0` (together with `(B3)`) at scale
`0 < b ≤ Q.bV` for any violator `T < Δ(a₁)` at sufficiently large `c'`, assuming `YVInputAtForWThr prob A_thr b`
at a cutoff radius `A_thr ∈ [virasoroAThr, 47]` and a line constant `C_line ≥ lineCaW A_thr`
(`bootstrapHB_of_YVForW` is the case `A_thr = virasoroAThr`, `C_line = 4 e^{6/5}`). -/
noncomputable def bootstrapHB_of_YVForWThr
    {A_thr b C_fb c_YV C_gap κ_gap C_line : ℝ} (hA : virasoroAThr ≤ A_thr) (hA47 : A_thr ≤ 47)
    (hC_line : lineCaW A_thr ≤ C_line) (hb_pos : 0 < b) (hb_le : b ≤ Q.bV)
    (hC_fb : 1 ≤ C_fb) (_hc_YV : 10000 ≤ c_YV)
    (hYVat : YVInputAtForWThr prob A_thr b (psiTilde prob) C_fb c_YV)
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
    let P := bootstrapParamsForWThr Q b hb_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap C_line
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
  have hA_pos : 0 < A_thr := lt_of_lt_of_le virasoroAThr_pos hA
  have hR_thr : A_thr ≤ R := by linarith
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
    uT_range_of_violatorW_thr hA hc'_Qenv hR_thr hR_ub hg hT_A2_full hT_a1 hB2
  set u_T := virasoroUT c' T
  have hς_arc' := Q.sigma_arc_of_scale hb_pos hc'_ge1 hR_ub_b hς_arc
  have hPN := pnodes_lb_and_thetaW_thr hA hR_thr hc'_Qenv hR_48 hR_ub hg hT_hi_AThr hT_A2_full.le hT_a1 hB2 hN
    P rfl rfl rfl rfl rfl rfl
  have hδ : P.δ_star ≤ 1 / 2 := quantC1DeltaStar_le
  obtain ⟨I, hIL, hIc, hIx⟩ := bootstrapHB_core (Q := Q) P (W_top := 0) (A_thr := A_thr) (b := b)
    (C_fb := C_fb) (c_YV := c_YV) (C_gap := C_gap) (κ_gap := κ_gap) (C_line := C_line) (μ₀ := 1)
    (T := T) (x_tilde := u_T - airyZero 1)
    rfl rfl rfl rfl (le_max_right _ _) (le_max_right _ _)
    (by rw [one_mul]; exact le_max_left _ _) (by rw [one_mul]; rfl) zero_le_one
    (show (0 : ℝ) < 1 from zero_lt_one) hδ rfl hC_fb hC_gap (by linarith [virasoroAThr_gt_two]) hA47 hC_line
    hb_pos hYVat hc'_Qenv hc'_YV hς_half hg
    hdl_half_full hdl_bd_full hT_A2_full hR_48 hR_bv hR_ub_2b hR_ub_b hR_ub hR_thr huT_le_m1 hT_lo_m1 hT_lo_0
    hT_hi_AThr hT_hi_R (by linarith) hB2.1 le_rfl
    (fun k ℓ => pNodesW prob c' R ℓ g k N)
    (fun hk0 hℓ_nn hℓ_half hYV_env hL0 => by
      simpa only [one_mul] using quad_arc_boundW hc'_Qenv h_c12 hς_arc'
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) hR_ub hL0
        hℓ_nn hℓ_half hg hYV_env hD hRp hRm hk0)
    (fun k ℓ hk0 hkR hℓ_mem => by simpa using hPN.1 k ℓ hk0 hkR hℓ_mem)
    (fun hk0_R hℓ_mem => by simpa using hPN.2 hk0_R hℓ_mem)
  exact ⟨I, le_of_eq hIL, hIc, hIx⟩


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
      I.c = c' ∧ I.x_tilde = virasoroUT c' T - airyZero 1 } :=
  bootstrapHB_of_YVForWThr le_rfl (by linarith [virasoroAThr_lt_four]) (lineCaW_virasoroAThr_le) hb_pos hb_le
    hC_fb _hc_YV hYVat hC_gap hκ_gap hc'_Qenv hc'_YV h_c12 h_b48 hς_half hς_arc hg hdl_bd hdl_half
    hT_A2 hT_a1 hB2

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lobe_scale_downW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lobe_scale_downW

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.uT_range_of_violatorW_thr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uT_range_of_violatorW_thr

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.uT_range_of_violatorW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uT_range_of_violatorW

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bootstrapHB_of_YVForWThr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bootstrapHB_of_YVForWThr

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.bootstrapHB_of_YVForW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bootstrapHB_of_YVForW

end FormalResearch.ModularBootstrap.FixedWeightBand
