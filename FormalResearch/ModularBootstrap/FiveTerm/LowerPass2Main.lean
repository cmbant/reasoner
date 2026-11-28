module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMain
public import FormalResearch.ModularBootstrap.FiveTerm.LowerPass2Top
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodCircle
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodWtilde
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScaleBridge
public import FormalResearch.SignUncertainty.AiryEtaUnfold
public import FormalResearch.SignUncertainty.CtDyadicArea
public import FormalResearch.SignUncertainty.CtDyadicRadius

/-!
# Unconditional `LowerPass2` (`ctl:pass2`) via top-scale moments and good circles

Discharges `LowerPass2 virasoroProblem c1 phi` from `LowerChart c0 γ0 c1 phi uhat` with
`c0 < 0`, `0 < c1`, `10 * c1 ≤ virasoroBVChoice`.

Using the top-scale moment/arc-mass bounds from `LowerPass2Top` (`virasoro_pass2_top_data`),
the `lowerEta` unfolding (`AiryEtaUnfold.airy_eta_le_arcs`), the half-disc Cauchy area
inequality (`CtDyadicArea.ct_area_of_zeta`) for `id` and `lowerGoodWtilde`, and the good-radius
measure lower bound (`LowerGoodCircle.lowerGoodSet_measure`), Markov's inequality produces a
good Airy circle `R = r² ∈ [c1² c^{2/3}, 4 c1² c^{2/3}]` with `lowerEta ≤ C c^{-1/3}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric intervalIntegral
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Contour FormalResearch.SignUncertainty
open FormalResearch.HalfDiscCauchy

noncomputable section

private lemma virasoro_a1_lt_uT_of_violator {c0 γ0 c1 : ℝ} {phi : ℝ → ℂ → ℂ}
    {uhat : ℝ → ℝ → ℝ} (hc0 : c0 < 0) (hchart : LowerChart c0 γ0 c1 phi uhat) :
    ∃ c_a1 : ℝ, 0 < c_a1 ∧ ∀ {c T : ℝ}, c_a1 ≤ c → LowerViolator phi c T →
      airyZero 1 < virasoroUT c T := by
  obtain ⟨c_ch, Cφ, hCφ, hch⟩ := hchart
  set δ : ℝ := -c0 / cStar
  have hδ : 0 < δ := div_pos (neg_pos.mpr hc0) cStar_pos
  have hev : ∀ᶠ c : ℝ in atTop,
      (|γ0 * airyZero 1| + Cφ) * c ^ (-(2 / 3 : ℝ)) ≤ δ / 2 ∧
      max c_ch 1 ≤ c := by
    have ht : Tendsto (fun c : ℝ => (|γ0 * airyZero 1| + Cφ) * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul _
    exact (ht.eventually (Iic_mem_nhds (by positivity : 0 < δ / 2))).and (eventually_ge_atTop _)
  obtain ⟨c_a1, hc_a1⟩ := eventually_atTop.1 hev
  refine ⟨max c_a1 1, by positivity, fun {c T} hc hviol => ?_⟩
  have hc1 : 1 ≤ c := (le_max_right _ _).trans hc
  have hc_pos : 0 < c := by linarith
  obtain ⟨herr, hmax⟩ := hc_a1 c ((le_max_left _ _).trans hc)
  have hc_ch : c_ch ≤ c := (le_max_left _ _).trans hmax
  have hphi := (hch c hc_ch).2.2.2.2
  have hpow1 : c ^ (-1 : ℝ) ≤ c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc_pos]; norm_num
  have hpow43 : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_add hc_pos]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hm13_nn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc_pos.le _
  have hm23_nn : 0 ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hc_pos.le _
  have hrem : |γ0 * airyZero 1 * c ^ (-1 : ℝ)| + Cφ * c ^ (-(4 / 3 : ℝ)) ≤
      (δ / 2) * c ^ (-(1 / 3 : ℝ)) := by
    calc |γ0 * airyZero 1 * c ^ (-1 : ℝ)| + Cφ * c ^ (-(4 / 3 : ℝ))
        = |γ0 * airyZero 1| * c ^ (-1 : ℝ) + Cφ * c ^ (-(4 / 3 : ℝ)) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hc_pos.le _)]
      _ ≤ |γ0 * airyZero 1| * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) +
            Cφ * (c ^ (-(1 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) := by gcongr
      _ = ((|γ0 * airyZero 1| + Cφ) * c ^ (-(2 / 3 : ℝ))) * c ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ (δ / 2) * c ^ (-(1 / 3 : ℝ)) := by gcongr
  have hlo : airyZero 1 + (δ / 2) * c ^ (-(1 / 3 : ℝ)) ≤ (phi c (airyZero 1 : ℂ)).re := by
    have hab := (abs_le.mp hphi).1
    have hγ := le_abs_self (γ0 * airyZero 1 * c ^ (-1 : ℝ))
    have hδ_pos : 0 < (δ / 2) * c ^ (-(1 / 3 : ℝ)) :=
      mul_pos (half_pos hδ) (Real.rpow_pos_of_pos hc_pos _)
    have hc0_eq : -(c0 / cStar * c ^ (-(1 / 3 : ℝ))) = δ * c ^ (-(1 / 3 : ℝ)) := by
      dsimp [δ]; ring
    linarith
  have ha1_lt_phi : airyZero 1 < (phi c (airyZero 1 : ℂ)).re := by
    have : 0 < (δ / 2) * c ^ (-(1 / 3 : ℝ)) :=
      mul_pos (half_pos hδ) (Real.rpow_pos_of_pos hc_pos _)
    linarith
  exact ha1_lt_phi.trans hviol

private lemma virasoro_pass2_markov_H
    {r₀ M_id M_wt M C_env : ℝ} {F1 F2 : ℝ → ℝ≥0∞}
    (hr₀_10 : 10 ≤ r₀) (hM_id_nn : 0 ≤ M_id) (hM_wt_nn : 0 ≤ M_wt) (hM_nn : 0 ≤ M)
    (hM_eq : M = 2 * (2 * M_id + 8 * Real.exp C_env * M_wt))
    (hF1_aem : AEMeasurable F1 (volume.restrict (Ioc r₀ (3 / 2 * r₀))))
    (hF2_aem : AEMeasurable F2 (volume.restrict (Ioc r₀ (3 / 2 * r₀))))
    (hArea1 : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), F1 r ≤ ENNReal.ofReal M_id)
    (hArea2 : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), F2 r ≤ ENNReal.ofReal M_wt) :
    ∃ r ∈ lowerGoodSet r₀,
      ENNReal.ofReal 2 * (ENNReal.ofReal 2 * F1 r + ENNReal.ofReal (8 * Real.exp C_env) * F2 r) ≤
        ENNReal.ofReal (2 * (M + 1) / (r₀ / 36)) := by
  have hr₀_pos : 0 < r₀ := by linarith only [hr₀_10]
  let H : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal 2 * (ENNReal.ofReal 2 * F1 r + ENNReal.ofReal (8 * Real.exp C_env) * F2 r)
  have hH_int : ∫⁻ r in Icc r₀ (3 / 2 * r₀), H r ≤ ENNReal.ofReal (M + 1) := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm]
    have hcomb_aem : AEMeasurable (fun r => ENNReal.ofReal 2 * F1 r + ENNReal.ofReal (8 * Real.exp C_env) * F2 r)
        (volume.restrict (Ioc r₀ (3 / 2 * r₀))) :=
      (hF1_aem.const_mul _).add (hF2_aem.const_mul _)
    calc ∫⁻ r in Ioc r₀ (3 / 2 * r₀), H r
        = ENNReal.ofReal 2 * ∫⁻ r in Ioc r₀ (3 / 2 * r₀),
            (ENNReal.ofReal 2 * F1 r + ENNReal.ofReal (8 * Real.exp C_env) * F2 r) :=
          lintegral_const_mul'' _ hcomb_aem
      _ = ENNReal.ofReal 2 * ((∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal 2 * F1 r) +
            ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ENNReal.ofReal (8 * Real.exp C_env) * F2 r) := by
          rw [lintegral_add_left' (hF1_aem.const_mul _)]
      _ = ENNReal.ofReal 2 * (ENNReal.ofReal 2 * (∫⁻ r in Ioc r₀ (3 / 2 * r₀), F1 r) +
            ENNReal.ofReal (8 * Real.exp C_env) * (∫⁻ r in Ioc r₀ (3 / 2 * r₀), F2 r)) := by
          rw [lintegral_const_mul'' _ hF1_aem, lintegral_const_mul'' _ hF2_aem]
      _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 2 * ENNReal.ofReal M_id +
            ENNReal.ofReal (8 * Real.exp C_env) * ENNReal.ofReal M_wt) := by gcongr
      _ = ENNReal.ofReal M := by
          have hexp : 0 ≤ 8 * Real.exp C_env := mul_nonneg (by norm_num) (Real.exp_pos _).le
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hexp,
            ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hM_id_nn) (mul_nonneg hexp hM_wt_nn),
            ← ENNReal.ofReal_mul (by norm_num), ← hM_eq]
      _ ≤ ENNReal.ofReal (M + 1) := ENNReal.ofReal_le_ofReal (by linarith only [])
  exact markov_lintegral (lowerGoodSet_measurable r₀) (fun _ hr => hr.1) H
    (by linarith only [hM_nn]) (by linarith only [hr₀_pos])
    (lowerGoodSet_measure hr₀_10) (lowerGoodSet_finite_measure r₀) hH_int

private lemma virasoro_pass2_area_id {G : ℂ → ℂ} {r₀ A CSig CS ratio M_id : ℝ}
    (hr₀_pos : 0 < r₀) (hA9 : 9 * r₀ ≤ A) (hAr₀ : A / r₀ ≤ ratio)
    (hM_id : M_id = 7 * CSig + 8 * (9 * π / 2) * CS * ratio / π)
    (hG_hc : ContinuousOn G (closedHalfDisc A)) (hG_hd : DifferentiableOn ℂ G (openHalfDisc A))
    (hSig : hdArcMass A G ≤ CSig / A) (hS2 : ∫ t in (-A)..A, t ^ 2 * ‖G (t : ℂ)‖ ≤ CS * A) :
    ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖G ((r : ℂ) * Complex.exp (φ * I))‖) ≤ ENNReal.ofReal M_id := by
  have hA : 0 < A := by linarith only [hr₀_pos, hA9]
  have hid_c : ContinuousOn (id : ℂ → ℂ) {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀} := continuousOn_id
  have hid_in : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      (id ((r : ℂ) * Complex.exp (φ * I))) ∈ openHalfDisc A ∧
      r₀ / 4 ≤ ‖id ((r : ℂ) * Complex.exp (φ * I))‖ ∧
      ‖id ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4 := by
    intro r hr φ hφ
    have hr0 : 0 < r := lt_trans hr₀_pos hr.1
    have hnorm : ‖(r : ℂ) * Complex.exp (φ * I)‖ = r := SignUncertainty.norm_arc hr0 φ
    refine ⟨⟨by rw [id_eq, hnorm]; linarith only [hr.2, hA9, hr₀_pos], ?_⟩,
      by rw [id_eq, hnorm]; linarith only [hr.1, hr₀_pos],
      by rw [id_eq, hnorm]; linarith only [hr.2, hA9, hr₀_pos]⟩
    rw [id_eq, im_arc]
    exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
  refine (ct_area_of_zeta hr₀_pos hA9 (by positivity) hG_hc hG_hd hSig hS2
    id hid_c hid_in (fun t _ => ct_inv_norm_area_id hr₀_pos t)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 8 * (9 * π / 2) * CS * A / (π * r₀) = 8 * (9 * π / 2) * CS * (A / r₀) / π := by ring
  have hCS_nn : 0 ≤ CS := by
    have hInt_nn : 0 ≤ ∫ t in (-A)..A, t ^ 2 * ‖G (t : ℂ)‖ :=
      intervalIntegral.integral_nonneg (by linarith only [hA]) fun _ _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    exact nonneg_of_mul_nonneg_left (hInt_nn.trans hS2) hA
  rw [hM_id, h1]
  have := Real.pi_pos
  gcongr

private lemma virasoro_pass2_area_wt {c1 c Cφ r₀ A CSig CS ratio M_wt : ℝ}
    {phi : ℝ → ℂ → ℂ} {G : ℂ → ℂ}
    (hr₀_10 : 10 ≤ r₀) (hCφ : 0 ≤ Cφ)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c)
    (hA9 : 9 * r₀ ≤ A) (hAr₀ : A / r₀ ≤ ratio)
    (hM_wt : M_wt = 7 * CSig + 8 * (72 * π) * CS * ratio / π)
    (hG_hc : ContinuousOn G (closedHalfDisc A)) (hG_hd : DifferentiableOn ℂ G (openHalfDisc A))
    (hSig : hdArcMass A G ≤ CSig / A) (hS2 : ∫ t in (-A)..A, t ^ 2 * ‖G (t : ℂ)‖ ≤ CS * A) :
    ContinuousOn (lowerGoodWtilde phi c) {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀} ∧
    (∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
      r₀ / 4 ≤ ‖lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I))‖ ∧
      ‖lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4) ∧
    ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
      ENNReal.ofReal (r * ‖G (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) ≤ ENNReal.ofReal M_wt := by
  have hr₀_pos : 0 < r₀ := by linarith only [hr₀_10]
  have hA : 0 < A := by linarith only [hr₀_pos, hA9]
  obtain ⟨h_main, h_im, _, _, _, _⟩ :=
    lowerGood_wtilde_props hr₀_10 hCφ h_err h_der hρ him hcl hr₀_eq hc_pos
  have hwt_cont := lowerGood_wtilde_continuousOn hr₀_10 h_err hcl hρ hr₀_eq hc_pos
  have hζwt : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
      r₀ / 4 ≤ ‖lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I))‖ ∧
      ‖lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4 := by
    intro r hr φ hφ
    have hr0 : 0 < r := lt_trans hr₀_pos hr.1
    set w : ℂ := (r : ℂ) * Complex.exp (φ * I)
    have hwn : ‖w‖ = r := SignUncertainty.norm_arc hr0 φ
    have hw_lo2 : r₀ / 2 ≤ ‖w‖ := by rw [hwn]; linarith only [hr.1, hr₀_pos]
    have hw_hi2 : ‖w‖ ≤ 2 * r₀ := by rw [hwn]; linarith only [hr.2, hr₀_pos]
    have hwp := h_main w hw_lo2 hw_hi2
    have hw_im : 0 < w.im := by rw [im_arc]; exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    have hwt_im : 0 < (lowerGoodWtilde phi c w).im := h_im w (by rw [hwn]; exact hr.1.le) (by rw [hwn]; exact hr.2) hw_im
    exact ⟨⟨by linarith only [hwp.2.2.2.1, hA9, hr₀_pos], hwt_im⟩,
      hwp.2.2.2.2, by linarith only [hwp.2.2.2.1, hA9, hr₀_pos]⟩
  refine ⟨hwt_cont, hζwt, ?_⟩
  refine (ct_area_of_zeta hr₀_pos hA9 (by positivity) hG_hc hG_hd hSig hS2
    (lowerGoodWtilde phi c) hwt_cont hζwt
    (fun t _ => lowerGood_wtilde_inv_norm_area_le hr₀_10 hCφ h_err h_der hρ him hcl hr₀_eq hc_pos t)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 8 * (72 * π) * CS * A / (π * r₀) = 8 * (72 * π) * CS * (A / r₀) / π := by ring
  have hCS_nn : 0 ≤ CS := by
    have hInt_nn : 0 ≤ ∫ t in (-A)..A, t ^ 2 * ‖G (t : ℂ)‖ :=
      intervalIntegral.integral_nonneg (by linarith only [hA]) fun _ _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    exact nonneg_of_mul_nonneg_left (hInt_nn.trans hS2) hA
  rw [hM_wt, h1]
  have := Real.pi_pos
  gcongr

private lemma virasoro_pass2_circle_of_top
    {c1 c T r₀ A Cφ CSig CS ratio M_id M_wt M C_env C_pass : ℝ}
    {phi : ℝ → ℂ → ℂ} {Ψ G : ℂ → ℂ} {g : ℝ → ℝ}
    (hc1_pos : 0 < c1) (hc_1000 : 1000 ≤ c) (hc_pos : 0 < c)
    (hCφ : 0 ≤ Cφ) (hA : 0 < A) (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hSig : hdArcMass A G ≤ CSig / A)
    (hS2 : ∫ t in (-A)..A, t ^ 2 * ‖G (t : ℂ)‖ ≤ CS * A)
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ))
    (hr₀_10 : 10 ≤ r₀)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hA9 : 9 * r₀ ≤ A)
    (hAr₀ : A / r₀ ≤ ratio)
    (hC_env : C_env = 5 * c1 * Cφ)
    (hM_id : M_id = 7 * CSig + 8 * (9 * π / 2) * CS * ratio / π)
    (hM_wt : M_wt = 7 * CSig + 8 * (72 * π) * CS * ratio / π)
    (hM_eq : M = 2 * (2 * M_id + 8 * Real.exp C_env * M_wt))
    (hM_id_nn : 0 ≤ M_id) (hM_wt_nn : 0 ≤ M_wt) (hM_nn : 0 ≤ M)
    (hC_pass : C_pass = 72 * (M + 1) / c1)
    (hΨ_eq : Ψ = virasoroPsiTilde c g) (hG_eq : G = airyGReg Ψ A)
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ)) :
    ∃ (N : ℕ) (R : ℝ), LowerGoodCircle N R ∧ LowerRadiusRange c1 c R ∧
      lowerEta virasoroProblem phi c g R ≤ C_pass * c ^ (-(1 / 3 : ℝ)) := by
  have hr₀_pos : 0 < r₀ := by linarith only [hr₀_10]
  have hΨ_cont : ContinuousOn Ψ (closedBall (0 : ℂ) (virasoroAC c ^ 2)) := by
    rw [hΨ_eq]
    exact (virasoroPsiTilde_analyticOnNhd hc_1000 hg.1).continuousOn.mono fun z hz =>
      virasoro_closedBall_subset_psiDom hc_pos hz
  have hG_an : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) A) := by
    rw [hG_eq, hΨ_eq]
    exact lowerGood_GReg_analytic hc_1000 hA hA_ub hg.1
  have hG_c : ContinuousOn G (closedBall (0 : ℂ) A) := hG_an.continuousOn
  have hG_hc : ContinuousOn G (closedHalfDisc A) :=
    hG_c.mono fun _ hw => mem_closedBall_zero_iff.mpr hw.1
  have hG_hd : DifferentiableOn ℂ G (openHalfDisc A) :=
    fun z hz => (hG_an z (mem_closedBall_zero_iff.mpr hz.1.le)).differentiableAt.differentiableWithinAt
  have hArea_id := virasoro_pass2_area_id hr₀_pos hA9 hAr₀ hM_id hG_hc hG_hd hSig hS2
  obtain ⟨hwt_cont, hζwt, hArea_wt⟩ := virasoro_pass2_area_wt hr₀_10 hCφ h_err h_der hρ him hcl hr₀_eq hc_pos
    hA9 hAr₀ hM_wt hG_hc hG_hd hSig hS2
  have heta_arcs := airy_eta_le_arcs hr₀_10 hCφ h_err h_der hc_pos hr₀_eq hA9 hA_ub hΨ_cont hρ him hcl hC_env
  let F1 : ℝ → ℝ≥0∞ := fun r => ∫⁻ φ in Ioo (0 : ℝ) π,
    ENNReal.ofReal (r * ‖G ((r : ℂ) * Complex.exp (φ * I))‖)
  let F2 : ℝ → ℝ≥0∞ := fun r => ∫⁻ φ in Ioo (0 : ℝ) π,
    ENNReal.ofReal (r * ‖G (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖)
  have hF1_aem : AEMeasurable F1 (volume.restrict (Ioc r₀ (3 / 2 * r₀))) :=
    ct_lint_aem hG_c continuousOn_id hr₀_pos fun r hr φ hφ =>
      mem_closedBall_zero_iff.mpr (by
        rw [id_eq, SignUncertainty.norm_arc (lt_trans hr₀_pos hr.1) φ]
        linarith only [hr.2, hA9, hr₀_pos])
  have hF2_aem : AEMeasurable F2 (volume.restrict (Ioc r₀ (3 / 2 * r₀))) :=
    ct_lint_aem hG_c hwt_cont hr₀_pos fun r hr φ hφ =>
      mem_closedBall_zero_iff.mpr (le_trans (hζwt r hr φ hφ).2.2 (by linarith only [hA]))
  obtain ⟨r, hr_good, hr_H⟩ := virasoro_pass2_markov_H hr₀_10 hM_id_nn hM_wt_nn hM_nn hM_eq
    hF1_aem hF2_aem hArea_id hArea_wt
  have hr_Icc : r ∈ Icc r₀ (3 / 2 * r₀) := hr_good.1
  have hr_pos : 0 < r := lt_of_lt_of_le hr₀_pos hr_Icc.1
  obtain ⟨m, hm⟩ := hr_good.2
  obtain ⟨N, hN_good⟩ := lowerGood_circle_of_phase (hr₀_10.trans hr_Icc.1) m hm
  have hRange : LowerRadiusRange c1 c (r ^ 2) := by
    refine ⟨?_, ?_⟩
    · unfold lowerRmin
      have hsq : r₀ ^ 2 = c1 ^ 2 * c ^ (2 / 3 : ℝ) := by
        rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
      rw [← hsq]
      exact pow_le_pow_left₀ hr₀_pos.le hr_Icc.1 2
    · unfold lowerRmax
      have hsq : r₀ ^ 2 = c1 ^ 2 * c ^ (2 / 3 : ℝ) := by
        rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
      have hr2 : r ^ 2 ≤ (3 / 2 * r₀) ^ 2 := pow_le_pow_left₀ hr_pos.le hr_Icc.2 2
      nlinarith only [hr2, hsq, sq_nonneg r₀]
  obtain ⟨hc1_int, hc2_int, heta_le⟩ := heta_arcs r hr_Icc
  have h_eta_eq : lowerEta virasoroProblem phi c g (r ^ 2) = airyEta Ψ (phi c) (r ^ 2) := by
    unfold lowerEta airyEta lowerF SignUncertainty.airyF
    rw [hΨ_eq]
    congr 1; ext θ
    rw [FixedWeightBand.psiTilde_virasoroProblem hc_pos.le,
      FixedWeightBand.psiTilde_virasoroProblem hc_pos.le]
  have hr_ofReal_eta : ENNReal.ofReal (lowerEta virasoroProblem phi c g (r ^ 2)) ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal 2 * F1 r + ENNReal.ofReal (8 * Real.exp C_env) * F2 r) := by
    rw [← hG_eq] at heta_le hc1_int hc2_int
    rw [h_eta_eq]
    have h1 := ENNReal.ofReal_le_ofReal heta_le
    have hnn1 : ∀ φ : ℝ, 0 ≤ r * ‖G ((r : ℂ) * Complex.exp (φ * I))‖ :=
      fun _ => mul_nonneg hr_pos.le (norm_nonneg _)
    have hnn2 : ∀ φ : ℝ, 0 ≤ r * ‖G (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖ :=
      fun _ => mul_nonneg hr_pos.le (norm_nonneg _)
    have h_i1 : ENNReal.ofReal (∫ φ in (0 : ℝ)..π,
        r * ‖G ((r : ℂ) * Complex.exp (φ * I))‖) = F1 r :=
      ofReal_integral_eq_lintegral_Ioo hc1_int hnn1
    have h_i2 : ENNReal.ofReal (∫ φ in (0 : ℝ)..π,
        r * ‖G (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖) = F2 r :=
      ofReal_integral_eq_lintegral_Ioo hc2_int hnn2
    have h_int1_nn : 0 ≤ ∫ φ in (0 : ℝ)..π, r * ‖G ((r : ℂ) * Complex.exp (φ * I))‖ :=
      intervalIntegral.integral_nonneg Real.pi_pos.le fun φ _ => hnn1 φ
    have h_int2_nn : 0 ≤ ∫ φ in (0 : ℝ)..π,
        r * ‖G (lowerGoodWtilde phi c ((r : ℂ) * Complex.exp (φ * I)))‖ :=
      intervalIntegral.integral_nonneg Real.pi_pos.le fun φ _ => hnn2 φ
    have hexp : 0 ≤ 8 * Real.exp C_env := mul_nonneg (by norm_num) (Real.exp_pos _).le
    refine h1.trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_add (mul_nonneg (by norm_num) h_int1_nn) (mul_nonneg hexp h_int2_nn),
      ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul hexp,
      h_i1, h_i2]
  have heta_real : lowerEta virasoroProblem phi c g (r ^ 2) ≤ 2 * (M + 1) / (r₀ / 36) := by
    have hmark := hr_ofReal_eta.trans hr_H
    exact (ENNReal.ofReal_le_ofReal_iff
      (div_nonneg (by linarith only [hM_nn] : 0 ≤ 2 * (M + 1)) (by linarith only [hr₀_pos] : 0 ≤ r₀ / 36))).mp hmark
  have heta_c13 : 2 * (M + 1) / (r₀ / 36) = C_pass * c ^ (-(1 / 3 : ℝ)) := by
    rw [hC_pass, hr₀_eq, Real.rpow_neg hc_pos.le]
    field_simp [hc1_pos.ne', (Real.rpow_pos_of_pos hc_pos (1 / 3 : ℝ)).ne']
    ring
  exact ⟨N, r ^ 2, hN_good, hRange, heta_real.trans_eq heta_c13⟩

/-- **`ctl:pass2`** (`LowerPass2 virasoroProblem c1 phi`): for any Virasoro chart `LowerChart c0 γ0 c1 phi uhat`
with `c0 < 0`, `0 < c1`, and `10 * c1 ≤ virasoroBVChoice`, every large-`c` weakly feasible violator
on `T ≤ Δ(-virasoroAThr)` admits a good Airy circle `R ∈ [c1² c^{2/3}, 4 c1² c^{2/3}]` with
`lowerEta virasoroProblem phi c g R ≤ C c^{-1/3}`. -/
theorem lowerPass2_of_chart {c0 γ0 c1 : ℝ} {phi : ℝ → ℂ → ℂ} {uhat : ℝ → ℝ → ℝ}
    (hc0 : c0 < 0) (hc1_pos : 0 < c1) (hc1_small : 10 * c1 ≤ virasoroBVChoice)
    (hchart : LowerChart c0 γ0 c1 phi uhat) :
    LowerPass2 virasoroProblem c1 phi := by
  obtain ⟨c_a1, _, ha1⟩ := virasoro_a1_lt_uT_of_violator hc0 hchart
  obtain ⟨c_ch, Cφ, hCφ, hch⟩ := hchart
  obtain ⟨CSig, CS, c_top, hCSig, hCS, hc_top_Q, htop⟩ := virasoro_pass2_top_data
  obtain ⟨c_J, C_J, _, _, hJ⟩ := theoremJ_unconditional
  set C_env : ℝ := 5 * c1 * Cφ
  set ratio : ℝ := 2 * virasoroBV / c1
  set M_id : ℝ := 7 * CSig + 8 * (9 * π / 2) * CS * ratio / π
  set M_wt : ℝ := 7 * CSig + 8 * (72 * π) * CS * ratio / π
  set M : ℝ := 2 * (2 * M_id + 8 * Real.exp C_env * M_wt)
  set C_pass : ℝ := 72 * (M + 1) / c1
  have hr_pos : 0 < ratio := by have := virasoroBV_pos; positivity
  have hM_id_nn : 0 ≤ M_id := by have := Real.pi_pos; dsimp [M_id]; positivity
  have hM_wt_nn : 0 ≤ M_wt := by have := Real.pi_pos; dsimp [M_wt]; positivity
  have hM_nn : 0 ≤ M := by dsimp [M]; positivity
  have hev : ∀ᶠ c : ℝ in atTop,
      C_J ≤ Aopt * c ^ (1 / 3 : ℝ) ∧
      (10 / c1) ^ 3 ≤ c ∧
      256 * Cφ / c1 ^ 2 ≤ c ∧
      4 * Cφ ≤ c ∧
      virasoroAThr ≤ virasoroAC c ^ 2 ∧
      max (max c_a1 c_ch) (max c_top (max c_J (max virasoroCQEnv 10000))) ≤ c := by
    have hc13 : Tendsto (fun c : ℝ => c ^ (1 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hc23 : Tendsto (fun c : ℝ => c ^ (2 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hAC_ev : ∀ᶠ c : ℝ in atTop, virasoroAThr ≤ virasoroAC c ^ 2 := by
      have hvb : 0 < 2 * virasoroBV ^ 2 := by have := virasoroBV_pos; positivity
      filter_upwards [(hc23.const_mul_atTop hvb).eventually_ge_atTop virasoroAThr,
        eventually_ge_atTop (1 : ℝ)] with c hc_thr hc1
      rw [virasoroAC_sq c (by linarith only [hc1])]
      exact hc_thr
    filter_upwards [(hc13.const_mul_atTop Aopt_pos).eventually_ge_atTop C_J,
      eventually_ge_atTop ((10 / c1) ^ 3),
      eventually_ge_atTop (256 * Cφ / c1 ^ 2),
      eventually_ge_atTop (4 * Cφ),
      hAC_ev,
      eventually_ge_atTop (max (max c_a1 c_ch) (max c_top (max c_J (max virasoroCQEnv 10000))))] with
        c h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.1 hev
  refine ⟨max c_ev 1, C_pass, fun c hc T g hg hviol hT_hi => ?_⟩
  obtain ⟨hCJ_le, hc10, hcerr, hcder, hAC_thr, hmax⟩ := hc_ev c ((le_max_left _ _).trans hc)
  have hc1 : 1 ≤ c := (le_max_right _ _).trans hc
  have hc_a1 : c_a1 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hmax)
  have hc_ch : c_ch ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hmax)
  have hc_top : c_top ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have hc_J : c_J ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hmax))
  have hc_10000 : 10000 ≤ c := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hmax)))
  have hc_pos : 0 < c := by linarith only [hc1]
  have hc_1000 : 1000 ≤ c := by linarith only [hc_10000]
  have hT_lo : virasoroDeltaChart c 0 ≤ T := by
    rw [virasoroDeltaChart_zero]
    have hJc := hJ (by linarith only [hc_J] : c_J ≤ c + 1) (by simpa [add_sub_cancel_right] using hg)
    simp only [add_sub_cancel_right] at hJc; linarith only [hJc, hCJ_le]
  have ha1_uT : airyZero 1 < virasoroUT c T := ha1 hc_a1 hviol
  have hu_mem := virasoroUT_between hc_pos (by linarith only [hAC_thr] : -(virasoroAC c ^ 2) ≤ -virasoroAThr)
    (sq_nonneg _) (by linarith only [virasoroAThr_pos]) hT_lo hT_hi
  have hT_a1 : T < virasoroDeltaChart c (airyZero 1) := by
    rw [← hu_mem.2]
    have ha1_neg := airyZero_neg 1
    have hthr_eq : virasoroAThr = -airyZero 1 + 1 := by
      unfold virasoroAThr; rw [abs_of_neg ha1_neg]
    have ha1_abs : |airyZero 1| ≤ virasoroAC c ^ 2 := by
      rw [abs_of_neg ha1_neg]; linarith only [hAC_thr, hthr_eq]
    have hut_lo : -(virasoroAC c ^ 2) ≤ virasoroUT c T := by linarith only [hu_mem.1.1, hAC_thr]
    have hut_hi : virasoroUT c T ≤ virasoroAC c ^ 2 := hu_mem.1.2.trans (sq_nonneg _)
    exact (virasoroDeltaChart_strictAnti hc_pos) (abs_le.mp ha1_abs) ⟨hut_lo, hut_hi⟩ ha1_uT
  obtain ⟨A, hA_lo, hA_ub, hSig, hS2⟩ := htop hc_top hg hT_a1 hT_hi
  set r₀ : ℝ := c1 * c ^ (1 / 3 : ℝ)
  have hr₀_pos : 0 < r₀ := by positivity
  obtain ⟨hr₀_10, h_err, h_der⟩ := ct_regime hc1_pos hc1 hc10 hcerr hcder
  have hA9 : 9 * r₀ ≤ A := by
    have h9c1 : 9 * c1 ≤ pass2ScaleLo := by
      unfold pass2ScaleLo
      have := virasoroBVChoice_pos
      linarith only [hc1_small, this]
    have hc13_nn : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc_pos.le _
    calc 9 * r₀ = (9 * c1) * c ^ (1 / 3 : ℝ) := by dsimp [r₀]; ring
      _ ≤ pass2ScaleLo * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right h9c1 hc13_nn
      _ ≤ A := hA_lo
  have hA : 0 < A := by linarith only [hr₀_pos, hA9]
  have hAr₀ : A / r₀ ≤ ratio := by
    have hA_sq : A ^ 2 ≤ (ratio * r₀) ^ 2 := by
      have hAC2 : virasoroAC c ^ 2 = 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := virasoroAC_sq c hc_pos.le
      have hr₀_sq : r₀ ^ 2 = c1 ^ 2 * c ^ (2 / 3 : ℝ) := by
        dsimp [r₀]
        rw [mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
        norm_num
      have hrr : (ratio * r₀) ^ 2 = 4 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := by
        dsimp [ratio]; rw [mul_pow, hr₀_sq]; field_simp [hc1_pos.ne']; ring
      have hbv2 : 2 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) ≤ 4 * virasoroBV ^ 2 * c ^ (2 / 3 : ℝ) := by
        have hcr := Real.rpow_nonneg hc_pos.le (2 / 3 : ℝ)
        have hbvsq := sq_nonneg virasoroBV
        nlinarith only [hcr, hbvsq]
      linarith only [hA_ub, hAC2, hrr, hbv2]
    have h1 : A ≤ ratio * r₀ := by
      rwa [sq_le_sq, abs_of_pos hA, abs_of_pos (mul_pos hr_pos hr₀_pos)] at hA_sq
    rwa [div_le_iff₀ hr₀_pos]
  obtain ⟨hρ, him, hcl, _, _⟩ := hch c hc_ch
  exact virasoro_pass2_circle_of_top (Ψ := virasoroPsiTilde c g) (G := lowerGoodGReg A c g)
    hc1_pos hc_1000 hc_pos hCφ hA hA_ub hSig hS2
    rfl hr₀_10 h_err h_der hA9 hAr₀ rfl rfl rfl rfl hM_id_nn hM_wt_nn hM_nn rfl rfl rfl hg hρ him hcl

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerPass2_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerPass2_of_chart
