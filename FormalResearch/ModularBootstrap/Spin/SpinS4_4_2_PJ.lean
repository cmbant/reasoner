module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_Strip
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_Slit
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_StripCont
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen
public import FormalResearch.ModularBootstrap.TipFront.ComplexMajorant
public import FormalResearch.ModularBootstrap.Blowup.Majorant

/-!
# SPIN-S4 Lemma 4.2 (`s4:4.2`, `spinning_s4.tex`)

Proves `spinS4_4_2 : SpinS4_4_2`: for each `V > 0` and `R > 0`, there exist `C_RV > 0` and
`c₀ ≥ 40` such that for all `c ≥ c₀`, `Φ ∈ SpinTestClass ((c - 1) / 12)` with `spinM2 = 1`, and
all measurable selectors `0 ≤ χ ≤ 1` supported in `[-V, V]`, `spinHProfile c N Φ χ` is
holomorphic on `closedBall (0 : ℂ) R` and bounded in norm by `C_RV`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.Special

lemma spinQSlice_tip_pj_bound
    {c V C_r C_V ρ₁ C_T1 ρ₂ C_T2 : ℝ} (hc : 49 ≤ c) (hV : 0 < V)
    (hCr : 0 < C_r) (hCV : 0 < C_V) (hρ1_pos : 0 < ρ₁) (hCT1_nn : 0 ≤ C_T1)
    (hρ2_pos : 0 < ρ₂) (hCT2_nn : 0 ≤ C_T2)
    (hγ_34 : 3 / 4 ≤ spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)
    (hγ_1 : spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹ ≤ 1)
    (hV_eps : V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) ≤ xiStar / 4)
    (hM_edge : 16 * (2 * V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) * C_V *
      (Nat.ceil (Real.log (c - 1)) : ℝ) ^ 2) ≤ 1)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0)
    (h41_L1 : ∫ p in {q : ℝ × ℝ | xiStar / 4 ≤ q.1 ∧ xiStar / 4 ≤ q.2},
      |spinTruncInv ((c - 1) / 12) (Nat.ceil (Real.log (c - 1))) Φ p.1 p.2| *
        spinWc ((c - 1) / 12) p.1 * spinWc ((c - 1) / 12) p.2 ≤ C_r)
    (h41_poly : ∀ (d : ℝ) (b : ℂ), |d| ≤ V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) →
      |b.im| ≤ (spinGamma ((c - 1) / 12) *
        (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹) / 2 →
      ‖spinTruncInvC ((c - 1) / 12) (Nat.ceil (Real.log (c - 1))) Φ (b + (d : ℂ)) (b - (d : ℂ))‖ ≤
        C_V * (Nat.ceil (Real.log (c - 1)) : ℝ) ^ 2 * (1 + |b.re| ^ 2) ^ 2)
    (hT1_spec : ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
      tipEps c' * ‖ζ‖ ≤ ρ₁ →
      ∃ z_b : ℂ, 0 < z_b.im ∧ ‖z_b - (sigmaStar : ℂ)‖ ≤ 0.1 ∧
        slitBoundaryMapC z_b = bScale c' ζ ∧
        |z_b.im - √(tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re| ≤
          C_T1 * √(tipEps c' * ‖ζ‖) * (√(tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ∧
        |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - (tipEps c' / slitQ) * tipDist ζ| ≤
          C_T1 * √(tipEps c' * ‖ζ‖) * ((tipEps c' / slitQ) * tipDist ζ))
    (hT2_spec : ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
      tipEps c' * ‖ζ‖ ≤ ρ₂ →
      |c' * (majorant2D (bScale c' ζ) + (tipL (bScale c' ζ)).re) - tipH ζ| ≤
        C_T2 * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ))
    {w : ℂ} (hw_cut : ¬ (w.im = 0 ∧ 0 ≤ w.re))
    (hεw_ρ₁ : tipEps ((c - 1) * (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)) * ‖w‖ ≤ ρ₁)
    (hεw_ρ₂ : tipEps ((c - 1) * (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)) * ‖w‖ ≤ ρ₂)
    (hT1_half : C_T1 * √(tipEps ((c - 1) * (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)) * ‖w‖) ≤ 1 / 2)
    (hT2_one : C_T2 * tipEps ((c - 1) * (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)) *
      ‖w‖ ^ (5 / 2 : ℝ) ≤ 1)
    (hlog_a : (2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(tipEps ((c - 1) * (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)) / slitQ) * √‖w‖) *
      |Real.log ((c - 1) / 12)| ≤ 1)
    (hq_ne : spinQSlice c (Nat.ceil (Real.log (c - 1))) Φ χ
      (((spinGamma ((c - 1) / 12) *
        (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹ : ℝ) : ℂ) *
        bScale ((c - 1) * (spinGamma ((c - 1) / 12) *
          (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹)) w) ≠ 0) :
    let n := c - 1
    let a := n / 12
    let ε := n ^ (-(2 / 3 : ℝ))
    let N := Nat.ceil (Real.log n)
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    let c' := n * γN
    let B_slit := max 1 (8 * C_r / spinSlitConst0)
    Real.log (ε * a) + c' * (tipL (bScale c' w)).re +
        Real.log ‖spinQSlice c N Φ χ ((γN : ℂ) * bScale c' w)‖ ≤
      (Real.log 80 + Real.log B_slit + 1 + slitEntropyComplexConst + Real.log (2 * slitQ) + 2) +
        tipH w - Real.log (tipDist w) := by
  intro n a ε N γN c' B_slit
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha_pos : 0 < a := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hγN_pos : 0 < γN := by linarith
  have hc'_pos : 0 < c' := mul_pos hn_pos hγN_pos
  have hεc'_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have _ := hρ1_pos; have _ := hρ2_pos; have _ := hCT1_nn; have _ := hCT2_nn
  obtain ⟨z_b, hz_im, hz_tip, hzb_eq, hzb_im_bd, hzb_prod_bd⟩ :=
    hT1_spec hc'_pos hw_cut hεw_ρ₁
  have hT2_bd := hT2_spec hc'_pos hw_cut hεw_ρ₂
  set x₀ := z_b.re
  set y₀ := z_b.im
  have hm_pos : 0 < slitMass x₀ y₀ := slitMass_pos_s4 hz_im
  have hm_le : slitMass x₀ y₀ ≤ 1 := slitMass_le_one_s4 hz_im
  set m := slitMass x₀ y₀
  let E_coef : ℝ := 2 * V * Real.sqrt ε * C_V * (N : ℝ) ^ 2
  have hEcoef_nn : 0 ≤ E_coef := by dsimp [E_coef]; positivity
  let M_edge : ℝ := 16 * E_coef + 1
  have hMedge_ge1 : 1 ≤ M_edge := by dsimp [M_edge]; linarith
  have hMedge_le2 : M_edge ≤ 2 := by dsimp [M_edge, E_coef]; linarith
  have hMedge_pos : 0 < M_edge := by linarith
  let F : ℂ → ℂ := fun u =>
    (M_edge : ℂ)⁻¹ * ((confB u + I) ^ 4)⁻¹ * spinQSlice c N Φ χ ((γN : ℂ) * confB u)
  let F_bdy : ℝ → ℂ := fun σ =>
    (M_edge : ℂ)⁻¹ * ((confB (σ : ℂ) + I) ^ 4)⁻¹ * spinQSlice c N Φ χ ((γN : ℂ) * confB (σ : ℂ))
  have hQ_cont := continuousOn_spinQSlice_closedStrip hc hV hCV.le hΦ hχ_meas hχ_bd hχ_supp h41_poly
  have hQ_strip := spinQSlice_rescaled_strip_bound hc hV hCV.le hγ_1 hΦ hχ_meas hχ_bd hχ_supp h41_poly
  have hQ_slit := spinQSlice_rescaled_slit_bound hc hV hCr.le hV_eps (by linarith) hΦ hχ_meas hχ_bd
    hχ_supp h41_L1
  have hF_diff : DifferentiableOn ℂ F {u : ℂ | 0 < u.im} := by
    have hQ_diff := spinQSlice_differentiableOn hc hV hΦ hχ_meas hχ_bd hχ_supp
    have hopen : IsOpen {b : ℂ | |b.im| < γN / 2} := isOpen_lt Complex.continuous_im.abs continuous_const
    intro u hu
    have hcb := confB_mem_slitStrip hu
    have hc_diff : DifferentiableAt ℂ confB u := (hasDerivAt_confB hu).differentiableAt
    have hpow_ne : (confB u + I) ^ 4 ≠ 0 := pow_ne_zero 4 (confB_add_I_ne_zero_of_im hcb.1.le)
    have hinv_diff : DifferentiableAt ℂ (fun v => ((confB v + I) ^ 4)⁻¹) u :=
      (((hc_diff.add_const I).pow 4).inv hpow_ne)
    have hmem : (γN : ℂ) * confB u ∈ {b : ℂ | |b.im| < γN / 2} := by
      change |((γN : ℂ) * confB u).im| < γN / 2
      rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hγN_pos]
      exact (mul_lt_mul_of_pos_left hcb.1 hγN_pos).trans_eq (by ring)
    have hq_at : DifferentiableAt ℂ (fun v => spinQSlice c N Φ χ ((γN : ℂ) * confB v)) u :=
      ((hQ_diff _ hmem).differentiableAt (hopen.mem_nhds hmem)).comp u (hc_diff.const_mul _)
    exact ((differentiableAt_const _ |>.mul hinv_diff).mul hq_at).differentiableWithinAt
  have hF_bd_im : ∀ b : ℂ, |b.im| ≤ 1 / 2 →
      ‖(M_edge : ℂ)⁻¹ * ((b + I) ^ 4)⁻¹ * spinQSlice c N Φ χ ((γN : ℂ) * b)‖ ≤ 1 := fun b hb => by
    have h16 := confB_add_I_norm_fourth_lb hb
    have hst := hQ_strip b hb
    have hpos4 : 0 < ‖(b + I) ^ 4‖ := norm_pos_iff.mpr (pow_ne_zero 4 (confB_add_I_ne_zero_of_im hb))
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMedge_pos]
    calc M_edge⁻¹ * ‖(b + I) ^ 4‖⁻¹ * ‖spinQSlice c N Φ χ ((γN : ℂ) * b)‖
        ≤ M_edge⁻¹ * ‖(b + I) ^ 4‖⁻¹ * (E_coef * (1 + |b.re| ^ 2) ^ 2) := by gcongr
      _ ≤ M_edge⁻¹ * ‖(b + I) ^ 4‖⁻¹ * (E_coef * (16 * ‖(b + I) ^ 4‖)) := by gcongr
      _ = (16 * E_coef / M_edge) * (‖(b + I) ^ 4‖⁻¹ * ‖(b + I) ^ 4‖) := by ring
      _ = 16 * E_coef / M_edge := by rw [inv_mul_cancel₀ hpos4.ne', mul_one]
      _ ≤ 1 := by rw [div_le_one hMedge_pos]; dsimp [M_edge]; linarith
  have hF_bd : ∀ u : ℂ, 0 < u.im → ‖F u‖ ≤ 1 := fun u hu =>
    hF_bd_im (confB u) (confB_mem_slitStrip hu).1.le
  have hconfB_im_real : ∀ σ : ℝ, σ ∉ ({-1, 0, 1} : Set ℝ) → |(confB (σ : ℂ)).im| ≤ 1 / 2 := by
    intro σ hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_trichotomy σ (-1) with hm | rfl | hm1
    · rw [confB_real_im_of_lt_neg_one hm]; norm_num
    · exact absurd rfl hnot.1
    · rcases lt_trichotomy σ 0 with h0 | rfl | h0
      · rw [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]; norm_num
      · exact absurd rfl hnot.2.1
      · rcases lt_trichotomy σ 1 with h1 | rfl | h1
        · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
        · exact absurd rfl hnot.2.2
        · rw [confB_real_im_of_one_lt h1]; norm_num
  have hF_bdy : ∀ᵐ σ : ℝ ∂volume, Tendsto F (𝓝[{u : ℂ | 0 < u.im}] (σ : ℂ)) (𝓝 (F_bdy σ)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hnot
    have hnot' : σ ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have htend_B : Tendsto confB (𝓝[{u : ℂ | 0 < u.im}] (σ : ℂ))
        (𝓝[{b : ℂ | |b.im| ≤ 1 / 2}] (confB (σ : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).tendsto.mono_left
          (nhdsWithin_mono _ fun u (hu : 0 < u.im) => hu.le)
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (confB_mem_slitStrip hu).1.le
    have htend_inv : Tendsto (fun u => ((confB u + I) ^ 4)⁻¹)
        (𝓝[{u : ℂ | 0 < u.im}] (σ : ℂ)) (𝓝 (((confB (σ : ℂ) + I) ^ 4)⁻¹)) := by
      have hB_lim : Tendsto confB (𝓝[{u : ℂ | 0 < u.im}] (σ : ℂ)) (𝓝 (confB (σ : ℂ))) :=
        htend_B.mono_right nhdsWithin_le_nhds
      have hne : (confB (σ : ℂ) + I) ^ 4 ≠ 0 :=
        pow_ne_zero 4 (confB_add_I_ne_zero_of_im (hconfB_im_real σ hnot))
      exact (((hB_lim.add tendsto_const_nhds).pow 4).inv₀ hne)
    have hmap : MapsTo (fun b : ℂ => (γN : ℂ) * b)
        {b : ℂ | |b.im| ≤ 1 / 2} {b : ℂ | |b.im| ≤ γN / 2} := fun b hb => by
      change |((γN : ℂ) * b).im| ≤ γN / 2
      rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hγN_pos]
      exact (mul_le_mul_of_nonneg_left hb hγN_pos.le).trans_eq (by ring)
    have hQ_lim : Tendsto (fun u => spinQSlice c N Φ χ ((γN : ℂ) * confB u))
        (𝓝[{u : ℂ | 0 < u.im}] (σ : ℂ)) (𝓝 (spinQSlice c N Φ χ ((γN : ℂ) * confB (σ : ℂ)))) := by
      have h1 : Tendsto (fun b : ℂ => (γN : ℂ) * b) (𝓝[{b : ℂ | |b.im| ≤ 1 / 2}] (confB (σ : ℂ)))
          (𝓝[{b : ℂ | |b.im| ≤ γN / 2}] ((γN : ℂ) * confB (σ : ℂ))) :=
        (continuous_const.mul continuous_id).continuousAt.tendsto.tendsto_nhdsWithin hmap
      have h2 := hQ_cont _ (hmap (hconfB_im_real σ hnot))
      exact h2.tendsto.comp (h1.comp htend_B)
    exact (tendsto_const_nhds.mul htend_inv).mul hQ_lim
  have hb_eq : bScale c' w = confB z_b := by rw [← hzb_eq, slitBoundaryMapC_eq_confB hz_im]
  have hcb_z := confB_mem_slitStrip hz_im
  have hne4_z : (confB z_b + I) ^ 4 ≠ 0 := pow_ne_zero 4 (confB_add_I_ne_zero_of_im hcb_z.1.le)
  have hFz_ne : F z_b ≠ 0 := by
    dsimp [F]; rw [← hb_eq]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hMedge_pos.ne'))
      (inv_ne_zero (by rwa [hb_eq]))) hq_ne
  obtain ⟨hPJ_int, hPJ_le⟩ := halfPlane_poissonJensen zero_lt_one hF_diff hF_bd hF_bdy hz_im hFz_ne
  change Real.log ‖F z_b‖ ≤ ∫ σ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ at hPJ_le
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]; intro σ h1 h2
    rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2 <;> linarith [h1.1, h1.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    refine Filter.eventuallyEqSet_iff'.2 ?_
    change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
    rw [ae_iff]; refine measure_mono_null (fun σ hσ => ?_) hnull
    by_contra hnot; apply hσ; apply propext
    simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_or_gt_of_ne hnot.1 with hm | hm
    · exact Or.inr (Or.inl hm)
    · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
      · exact Or.inl (Or.inl ⟨hm, h0⟩)
      · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inr h1)
  have hsplit_eq : ∫ σ : ℝ, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) +
        (∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set hunion_ae]
    exact setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
      hPJ_int.integrableOn hPJ_int.integrableOn
  have hedge_le : ∫ σ in edgePreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ ≤ 0 := by
    refine setIntegral_nonpos (measurableSet_Iio.union measurableSet_Ioo) fun σ hσ => ?_
    have hnot : σ ∉ ({-1, 0, 1} : Set ℝ) := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      rcases hσ with (hlt : σ < -1) | ⟨h0, h1⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩
    have hbd1 : ‖F_bdy σ‖ ≤ 1 := hF_bd_im (confB (σ : ℂ)) (hconfB_im_real σ hnot)
    have hlog0 : Real.log ‖F_bdy σ‖ ≤ 0 := by
      by_cases h0 : ‖F_bdy σ‖ = 0
      · rw [h0, Real.log_zero]
      · exact Real.log_nonpos (norm_nonneg _) hbd1
    exact mul_nonpos_of_nonpos_of_nonneg hlog0 (poissonKernel_nonneg hz_im.le σ)
  have hslit_confB : ∀ σ ∈ slitPreimage, confB (σ : ℂ) = (slitBoundaryMap σ : ℂ) := fun σ hσ => by
    rcases hσ with hIoo | hIoi
    · exact Complex.ext (confB_real_re hIoo.2.ne (by linarith [hIoo.2]) hIoo.1.ne')
        (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
    · have hgt : 1 < σ := hIoi
      exact Complex.ext (confB_real_re (by linarith) hgt.ne' (by linarith)) (confB_real_im_of_one_lt hgt)
  let φ : ℝ → ℝ := fun t =>
    a * Real.exp (c' * slitL t) *
      (‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖ + ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-t : ℝ) : ℂ))‖)
  have hQ_real_cont : Continuous (fun t : ℝ => spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))) := by
    have hmap : MapsTo (fun t : ℝ => (γN : ℂ) * (t : ℂ)) univ {b : ℂ | |b.im| ≤ γN / 2} := fun t _ => by
      simp [Complex.mul_im, hγN_pos.le]
    rw [continuousOn_univ.symm]
    exact hQ_cont.comp (Continuous.mul continuous_const Complex.continuous_ofReal).continuousOn hmap
  have hφ_cont : Continuous φ := by
    have hL_cont : Continuous slitL := by unfold slitL; fun_prop
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL_cont))).mul
      (hQ_real_cont.norm.add ((hQ_real_cont.comp continuous_neg).norm))
  have hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t := fun t _ => by dsimp [φ]; positivity
  have hφ_int : IntegrableOn φ (Ioi xiStar) := by
    have hpos_int : IntegrableOn
        (fun t : ℝ => a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖)
        (Ioi xiStar) :=
      hQ_slit.1.mono_set fun t ht => le_trans (le_of_lt ht) (le_abs_self t)
    have hneg_map : IntegrableOn
        (fun t : ℝ => a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-t : ℝ) : ℂ))‖)
        (Ioi xiStar) := by
      have h1 : IntegrableOn
          (fun t : ℝ => a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖)
          (Iio (-xiStar)) :=
        hQ_slit.1.mono_set fun t (ht : t < -xiStar) => by
          change xiStar ≤ |t|; rw [abs_of_neg (by linarith [xiStar_pos])]; linarith
      have h2 := (integrableOn_comp_neg_iff (f := fun t : ℝ =>
        a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖) (s := Iio (-xiStar))).mpr h1
      rw [show -Iio (-xiStar) = Ioi xiStar by ext t; simp] at h2
      refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
      dsimp only; rw [show slitL (-t) = slitL t by unfold slitL; rw [abs_neg]]
    exact hpos_int.add hneg_map
  have hIφ_le : 2 * ∫ t in Ioi xiStar, φ t ≤ B_slit := by
    have hpos_int : IntegrableOn
        (fun t : ℝ => a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖)
        (Ioi xiStar) :=
      hQ_slit.1.mono_set fun t ht => le_trans (le_of_lt ht) (le_abs_self t)
    have hneg_int : IntegrableOn
        (fun t : ℝ => a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-t : ℝ) : ℂ))‖)
        (Ioi xiStar) := by
      have h1 : IntegrableOn
          (fun t : ℝ => a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖)
          (Iio (-xiStar)) :=
        hQ_slit.1.mono_set fun t (ht : t < -xiStar) => by
          change xiStar ≤ |t|; rw [abs_of_neg (by linarith [xiStar_pos])]; linarith
      have h2 := (integrableOn_comp_neg_iff (f := fun t : ℝ =>
        a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖) (s := Iio (-xiStar))).mpr h1
      rw [show -Iio (-xiStar) = Ioi xiStar by ext t; simp] at h2
      refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
      dsimp only; rw [show slitL (-t) = slitL t by unfold slitL; rw [abs_neg]]
    have hadd_eq : ∫ t in Ioi xiStar, φ t =
        (∫ t in Ioi xiStar, a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖) +
        (∫ t in Ioi xiStar, a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-t : ℝ) : ℂ))‖) := by
      have heq : EqOn φ (fun t =>
          a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖ +
          a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-t : ℝ) : ℂ))‖) (Ioi xiStar) :=
        fun t _ => by dsimp [φ]; ring
      rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_add hpos_int hneg_int]
    have hneg_eq : ∫ t in Ioi xiStar,
          a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-t : ℝ) : ℂ))‖ =
        ∫ t in Iio (-xiStar),
          a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖ := by
      rw [← integral_comp_neg_Ioi (-xiStar)]
      refine setIntegral_congr_fun measurableSet_Iio fun t _ => ?_
      dsimp only; simp only [neg_neg, slitL, abs_neg]
    have hpos_le : ∫ t in Ioi xiStar,
          a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖ ≤
        4 * C_r / spinSlitConst0 :=
      (setIntegral_mono_set hQ_slit.1 (Eventually.of_forall fun t => by positivity)
        (Eventually.of_forall fun t ht => le_trans (le_of_lt ht) (le_abs_self t))).trans hQ_slit.2
    have hneg_le : ∫ t in Iio (-xiStar),
          a * Real.exp (c' * slitL t) * ‖spinQSlice c N Φ χ ((γN : ℂ) * (t : ℂ))‖ ≤
        4 * C_r / spinSlitConst0 :=
      (setIntegral_mono_set hQ_slit.1 (Eventually.of_forall fun t => by positivity)
        (Eventually.of_forall fun t (ht : t < -xiStar) => by
          change xiStar ≤ |t|; rw [abs_of_neg (by linarith [xiStar_pos])]; linarith)).trans hQ_slit.2
    rw [hadd_eq, hneg_eq]
    calc 2 * ((∫ t in Ioi xiStar, _) + (∫ t in Iio (-xiStar), _))
        ≤ 2 * (4 * C_r / spinSlitConst0 + 4 * C_r / spinSlitConst0) := by gcongr
      _ = 8 * C_r / spinSlitConst0 := by ring
      _ ≤ B_slit := le_max_right _ _
  obtain ⟨hf_pull_int, hf_pull_eq⟩ :=
    setIntegral_slitPreimage_div_slitDensity (x := x₀) hz_im hφ_cont.measurable hφ_nn hφ_int
  let K_val : ℝ → ℝ := fun σ => Real.exp (c' * slitL (slitBoundaryMap σ))
  let f : ℝ → ℝ := fun σ => ‖F_bdy σ‖ * (a * K_val σ) / slitDensity x₀ y₀ σ
  have hK_ge1 : ∀ σ : ℝ, 1 ≤ K_val σ := fun σ =>
    Real.one_le_exp (mul_nonneg hc'_pos.le (by unfold slitL; positivity))
  have hK_pos : ∀ σ : ℝ, 0 < K_val σ := fun σ => lt_of_lt_of_le zero_lt_one (hK_ge1 σ)
  have hFbdy_le_Q : ∀ σ ∈ slitPreimage,
      ‖F_bdy σ‖ ≤ ‖spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))‖ := fun σ hσ => by
    dsimp [F_bdy]
    rw [hslit_confB σ hσ, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hMedge_pos, norm_pow]
    have hnorm1 : 1 ≤ ‖(slitBoundaryMap σ : ℂ) + I‖ := by
      rw [← sq_le_sq₀ zero_le_one (norm_nonneg _), one_pow, Complex.sq_norm, Complex.normSq_apply]
      simp [sq_nonneg]
    have hnorm4 : 1 ≤ ‖(slitBoundaryMap σ : ℂ) + I‖ ^ 4 := one_le_pow₀ hnorm1
    calc M_edge⁻¹ * (‖(slitBoundaryMap σ : ℂ) + I‖ ^ 4)⁻¹ *
          ‖spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))‖
        ≤ 1 * 1 * ‖spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))‖ := by
          gcongr
          · exact inv_le_one_of_one_le₀ hMedge_ge1
          · exact inv_le_one_of_one_le₀ hnorm4
      _ = _ := by ring
  have hf_le_pull : ∀ σ ∈ slitPreimage, f σ ≤ φ |slitBoundaryMap σ| / slitDensity x₀ y₀ σ := fun σ hσ => by
    dsimp [f, φ, K_val]
    have h_pos_om : 0 ≤ slitDensity x₀ y₀ σ := slitDensity_nonneg (x := x₀) hz_im σ
    have hQ_le : ‖spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))‖ ≤
        ‖spinQSlice c N Φ χ ((γN : ℂ) * (|slitBoundaryMap σ| : ℂ))‖ +
        ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-|slitBoundaryMap σ| : ℝ) : ℂ))‖ := by
      rcases le_or_gt 0 (slitBoundaryMap σ) with h | h
      · rw [abs_of_nonneg h]; exact le_add_of_nonneg_right (norm_nonneg _)
      · rw [abs_of_neg h, neg_neg]; exact le_add_of_nonneg_left (norm_nonneg _)
    have hle1 : ‖F_bdy σ‖ * (a * Real.exp (c' * slitL (slitBoundaryMap σ))) ≤
        a * Real.exp (c' * slitL |slitBoundaryMap σ|) *
          (‖spinQSlice c N Φ χ ((γN : ℂ) * (|slitBoundaryMap σ| : ℂ))‖ +
            ‖spinQSlice c N Φ χ ((γN : ℂ) * ((-|slitBoundaryMap σ| : ℝ) : ℂ))‖) := by
      rw [show slitL |slitBoundaryMap σ| = slitL (slitBoundaryMap σ) by unfold slitL; rw [abs_abs]]
      calc ‖F_bdy σ‖ * (a * Real.exp (c' * slitL (slitBoundaryMap σ)))
          ≤ ‖spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))‖ *
              (a * Real.exp (c' * slitL (slitBoundaryMap σ))) := by
            gcongr; exact hFbdy_le_Q σ hσ
        _ ≤ _ := by gcongr
        _ = _ := by ring
    exact div_le_div_of_nonneg_right hle1 h_pos_om
  have hsd_meas : Measurable (slitDensity x₀ y₀) := by
    have h1 : Measurable (rightSlitDensity x₀ y₀) := by
      unfold rightSlitDensity poissonKernel slitInv invJacobian; fun_prop
    have h2 : Measurable (leftSlitDensity x₀ y₀) := by
      unfold leftSlitDensity poissonKernel leftSlitInv invJacobian; fun_prop
    exact Measurable.ite measurableSet_Iio h1 h2
  have hf_int : IntegrableOn (fun σ => f σ * poissonKernel x₀ y₀ σ) slitPreimage := by
    let f_m : ℝ → ℝ := fun σ =>
      (M_edge⁻¹ * (‖(slitBoundaryMap σ : ℂ) + I‖ ^ 4)⁻¹ *
        ‖spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))‖) * (a * K_val σ) / slitDensity x₀ y₀ σ
    have hm_fm : Measurable f_m := by
      have hm1 : Measurable (fun σ : ℝ => (slitBoundaryMap σ : ℂ) + I) :=
        (Complex.continuous_ofReal.measurable.comp measurable_slitBoundaryMap).add measurable_const
      have hm2 : Measurable (fun σ : ℝ => spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ))) :=
        hQ_real_cont.measurable.comp measurable_slitBoundaryMap
      have hm_K : Measurable K_val :=
        Real.continuous_exp.measurable.comp (measurable_const.mul
          ((by unfold slitL; fun_prop : Continuous slitL).measurable.comp measurable_slitBoundaryMap))
      exact (((measurable_const.mul ((hm1.norm.pow_const 4).inv)).mul hm2.norm).mul
        (measurable_const.mul hm_K)).div hsd_meas
    have hae_m : AEStronglyMeasurable (fun σ => f σ * poissonKernel x₀ y₀ σ) (volume.restrict slitPreimage) := by
      refine (hm_fm.mul (continuous_poissonKernel x₀ hz_im).measurable).aestronglyMeasurable.congr ?_
      rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
      refine Eventually.of_forall fun σ hσ => ?_
      dsimp [f, f_m, F_bdy]
      rw [hslit_confB σ hσ, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hMedge_pos, norm_pow]
    refine hf_pull_int.mono' hae_m ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hσ
    have hP0 := poissonKernel_nonneg (x := x₀) hz_im.le σ
    have hf0 : 0 ≤ f σ := div_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg ha_pos.le (hK_pos σ).le))
      (slitDensity_nonneg (x := x₀) hz_im σ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 hP0)]
    exact mul_le_mul_of_nonneg_right (hf_le_pull σ hσ) hP0
  have hQ_ne_ae := spinQSlice_bdy_ne_zero_ae hc hV hΦ hχ_meas hχ_bd hχ_supp
    (by
      rw [hb_eq]
      have hcb := (confB_mem_slitStrip hz_im).1
      change |((γN : ℂ) * confB z_b).im| < γN / 2
      rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hγN_pos]
      exact (mul_lt_mul_of_pos_left hcb hγN_pos).trans_eq (by ring))
    (by rwa [← hb_eq] at hq_ne)
  have hFbdy_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < ‖F_bdy σ‖ := by
    filter_upwards [hQ_ne_ae, ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with σ hQ hσ
    dsimp [F_bdy]
    rw [hslit_confB σ hσ]
    have hne4 : ((slitBoundaryMap σ : ℂ) + I) ^ 4 ≠ 0 := by
      have : |((slitBoundaryMap σ : ℂ)).im| ≤ 1 / 2 := by simp
      exact pow_ne_zero 4 (confB_add_I_ne_zero_of_im this)
    exact norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hMedge_pos.ne'))
      (inv_ne_zero hne4)) hQ)
  have hf_pos_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ := by
    filter_upwards [hFbdy_pos_ae, slitDensity_pos_ae (x := x₀) hz_im] with σ hF hω
    exact div_pos (mul_pos hF (mul_pos ha_pos (hK_pos σ))) hω
  have hident : IntegrableOn (fun σ => slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    identification_integrand_integrable x₀ hz_im
  have hlogK_eq : (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) =
      fun σ => c' * (slitL (slitBoundaryMap σ) * poissonKernel x₀ y₀ σ) := by
    ext σ; dsimp [K_val]; rw [Real.log_exp]; ring
  have hlogK_int : IntegrableOn (fun σ => Real.log (K_val σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    rw [hlogK_eq]; exact hident.const_mul c'
  have hlogK_eval : ∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ =
      -c' * majorant2D (bScale c' w) := by
    rw [hlogK_eq, integral_const_mul, hb_eq, ← slitBoundaryMapC_eq_confB hz_im,
      harmonicMajorantIdentification_complex hz_im]
    ring
  have hlogω_int : IntegrableOn
      (fun σ => Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) slitPreimage :=
    (integrableOn_poisson_mul_log_slitDensity x₀ hz_im).congr_fun
      (fun _ _ => by dsimp only; ring) (measurableSet_Ioo.union measurableSet_Ioi)
  have hlogF_slit_int : IntegrableOn
      (fun σ => Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ) slitPreimage :=
    hPJ_int.integrableOn
  have hpk_slit : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
    (integrable_poissonKernel x₀ hz_im).integrableOn
  have hlogf_eq_ae : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x₀ y₀ σ =
        Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ -
          Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ +
          Real.log (K_val σ) * poissonKernel x₀ y₀ σ +
          Real.log a * poissonKernel x₀ y₀ σ := by
    filter_upwards [hFbdy_pos_ae, slitDensity_pos_ae (x := x₀) hz_im] with σ hF hω
    dsimp [f]
    rw [Real.log_div (mul_pos hF (mul_pos ha_pos (hK_pos σ))).ne' hω.ne',
      Real.log_mul hF.ne' (mul_pos ha_pos (hK_pos σ)).ne',
      Real.log_mul ha_pos.ne' (hK_pos σ).ne']
    ring
  have hlogf_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x₀ y₀ σ) slitPreimage := by
    refine (((hlogF_slit_int.sub hlogω_int).add hlogK_int).add (hpk_slit.const_mul _)).congr ?_
    filter_upwards [hlogf_eq_ae] with σ h; exact h.symm
  have hIf_le : ∫ σ in slitPreimage, f σ * poissonKernel x₀ y₀ σ ≤ B_slit := by
    refine (setIntegral_mono_on hf_int hf_pull_int (measurableSet_Ioo.union measurableSet_Ioi)
      fun σ hσ => mul_le_mul_of_nonneg_right (hf_le_pull σ hσ)
        (poissonKernel_nonneg hz_im.le σ)).trans ?_
    rw [hf_pull_eq]; exact hIφ_le
  have hBslit_ge1 : 1 ≤ B_slit := le_max_left _ _
  have hjensen := log_integral_jensen_slitPreimage_s4 hz_im hf_pos_ae hf_int hlogf_int
    (by linarith) hIf_le
  have hdecomp : ∫ σ in slitPreimage, Real.log ‖F_bdy σ‖ * poissonKernel x₀ y₀ σ =
      (∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x₀ y₀ σ) +
        (∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ) -
        (∫ σ in slitPreimage, Real.log (K_val σ) * poissonKernel x₀ y₀ σ) -
        m * Real.log a := by
    have h1 := ((hlogF_slit_int.sub hlogω_int).add hlogK_int)
    rw [integral_congr_ae hlogf_eq_ae, integral_add h1 (hpk_slit.const_mul _),
      integral_add (hlogF_slit_int.sub hlogω_int) hlogK_int,
      integral_sub hlogF_slit_int hlogω_int, integral_const_mul]
    change _ = _ - _ - _ - (∫ σ in slitPreimage, poissonKernel x₀ y₀ σ) * Real.log a
    ring
  have hent_le : ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ ≤
      slitEntropy x₀ y₀ := by
    calc ∫ σ in slitPreimage, Real.log (slitDensity x₀ y₀ σ) * poissonKernel x₀ y₀ σ
        = ∫ σ in slitPreimage, poissonKernel x₀ y₀ σ * Real.log (slitDensity x₀ y₀ σ) :=
          integral_congr_ae (Eventually.of_forall fun σ => by ring)
      _ ≤ slitEntropy x₀ y₀ := setIntegral_poisson_mul_log_slitDensity_le_entropy x₀ hz_im
  have hT4 := lemma_T4 hz_im hz_tip
  have hε_le_tip : ε ≤ tipEps c' := by
    dsimp [ε]; unfold tipEps
    exact Real.rpow_le_rpow_of_nonpos hc'_pos (mul_le_of_le_one_right hn_pos.le hγ_1) (by norm_num)
  have hlog_ε : Real.log ε ≤ Real.log (tipEps c') := Real.log_le_log hε_pos hε_le_tip
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr fun h0 => hw_cut (by simp [h0])
  have hprod_ge : (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist w) ≤ y₀ * ‖z_b - (sigmaStar : ℂ)‖ := by
    have h1 := (abs_le.mp hzb_prod_bd).1
    have hdist0 : 0 ≤ (tipEps c' / slitQ) * tipDist w :=
      mul_nonneg (div_nonneg hεc'_pos.le slitQ_pos.le) (tipDist_nonneg w)
    have h2 : C_T1 * √(tipEps c' * ‖w‖) * ((tipEps c' / slitQ) * tipDist w) ≤
        (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist w) :=
      mul_le_mul_of_nonneg_right hT1_half hdist0
    linarith
  have hd_pos : 0 < tipDist w := tipDist_pos_of_not_nonneg hw_cut
  have hzd_ne : z_b - (sigmaStar : ℂ) ≠ 0 := by
    intro h0
    have h0' : z_b.im = 0 := by
      have := congrArg Complex.im h0; simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
      exact this
    linarith
  have hzd_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := norm_pos_iff.mpr hzd_ne
  have hlog_ent_geom : Real.log (1 / y₀) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) ≤
      -Real.log (tipEps c') + Real.log (2 * slitQ) - Real.log (tipDist w) := by
    have hyz_pos : 0 < y₀ * ‖z_b - (sigmaStar : ℂ)‖ := mul_pos hz_im hzd_pos
    have hhalf_pos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist w) :=
      mul_pos (by positivity) (mul_pos (div_pos hεc'_pos slitQ_pos) hd_pos)
    have hl : Real.log ((1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist w)) ≤
        Real.log (y₀ * ‖z_b - (sigmaStar : ℂ)‖) := Real.log_le_log hhalf_pos hprod_ge
    rw [Real.log_div one_ne_zero hz_im.ne', Real.log_div one_ne_zero hzd_pos.ne', Real.log_one,
      zero_sub, zero_sub, Real.log_mul hz_im.ne' hzd_pos.ne'] at *
    rw [Real.log_mul (by positivity) (mul_pos (div_pos hεc'_pos slitQ_pos) hd_pos).ne',
      Real.log_mul (div_pos hεc'_pos slitQ_pos).ne' hd_pos.ne',
      Real.log_div hεc'_pos.ne' slitQ_pos.ne',
      Real.log_mul two_pos.ne' slitQ_pos.ne', Real.log_div one_ne_zero two_pos.ne', Real.log_one] at *
    linarith
  have hz_im_ub : y₀ ≤ (3 / 2 : ℝ) * √(tipEps c' / slitQ) * √‖w‖ := by
    have hre_le : ((-w) ^ (1 / 2 : ℂ)).re ≤ √‖w‖ := by
      calc ((-w) ^ (1 / 2 : ℂ)).re ≤ ‖(-w) ^ (1 / 2 : ℂ)‖ := Complex.abs_re_le_norm _ |>.trans' (le_abs_self _)
        _ = ‖-w‖ ^ (1 / 2 : ℝ) := Complex.norm_cpow_eq_rpow_re_of_nonneg (norm_ne_zero_iff.mpr (neg_ne_zero.mpr (norm_pos_iff.mp hw_pos))) (by norm_num)
        _ = √‖w‖ := by rw [norm_neg, Real.sqrt_eq_rpow]
    have h1 := (abs_le.mp hzb_im_bd).2
    have hsqrt_nn : 0 ≤ √(tipEps c' / slitQ) := Real.sqrt_nonneg _
    have hre_nonneg : 0 ≤ ((-w) ^ (1 / 2 : ℂ)).re := by
      have htd : 0 < tipDist w := tipDist_pos_of_not_nonneg hw_cut
      have hsq : 0 < √‖w‖ := Real.sqrt_pos.mpr hw_pos
      unfold tipDist at htd
      exact le_of_lt ((mul_pos_iff_of_pos_left hsq).mp htd)
    calc y₀ ≤ (1 + C_T1 * √(tipEps c' * ‖w‖)) * (√(tipEps c' / slitQ) * ((-w) ^ (1 / 2 : ℂ)).re) := by
          linarith
      _ ≤ (3 / 2 : ℝ) * (√(tipEps c' / slitQ) * √‖w‖) := by
          gcongr; linarith
      _ = (3 / 2 : ℝ) * √(tipEps c' / slitQ) * √‖w‖ := by ring
  have h1m_loga : (1 - m) * Real.log a ≤ 1 := by
    have h1m_nn : 0 ≤ 1 - m := by linarith
    calc (1 - m) * Real.log a ≤ (1 - m) * |Real.log a| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h1m_nn
      _ ≤ ((2 / (0.3 * π)) * y₀) * |Real.log a| := by gcongr; exact hT4.1
      _ ≤ ((2 / (0.3 * π)) * ((3 / 2 : ℝ) * √(tipEps c' / slitQ) * √‖w‖)) * |Real.log a| := by gcongr
      _ ≤ 1 := hlog_a
  have hMedge_cb_log : Real.log M_edge + Real.log ‖(confB z_b + I) ^ 4‖ ≤ Real.log 80 := by
    have hre_z : |(confB z_b).re| ≤ 1 := by
      have h1 := abs_confB_re_le_of_tip_ball hz_im hz_tip
      have hlog12 : Real.log 12 ≤ 2 * π := by
        have h12 : (12 : ℝ) ≤ Real.exp 3 := by
          have := Real.exp_one_gt_d9
          have hpow : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          nlinarith
        have := Real.log_le_log (by norm_num) h12
        rw [Real.log_exp] at this
        have := Real.pi_gt_three; linarith
      exact h1.trans ((div_le_one (by positivity)).mpr hlog12)
    have him_z : |(confB z_b + I).im| ≤ 3 / 2 := by
      have h2 := (abs_le.mp hcb_z.1.le)
      rw [Complex.add_im, Complex.I_im, abs_le]; constructor <;> linarith
    have hre_z' : |(confB z_b + I).re| ≤ 1 := by simpa [Complex.add_re] using hre_z
    have hnorm_le : ‖confB z_b + I‖ ≤ 5 / 2 := by
      calc ‖confB z_b + I‖ ≤ |(confB z_b + I).re| + |(confB z_b + I).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 1 + 3 / 2 := add_le_add hre_z' him_z
        _ = 5 / 2 := by ring
    have hpow_le : ‖(confB z_b + I) ^ 4‖ ≤ 40 := by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 4).trans (by norm_num)
    have hprod_le : M_edge * ‖(confB z_b + I) ^ 4‖ ≤ 80 := by nlinarith
    rw [← Real.log_mul hMedge_pos.ne' (norm_pos_iff.mpr hne4_z).ne']
    exact Real.log_le_log (mul_pos hMedge_pos (norm_pos_iff.mpr hne4_z)) hprod_le
  have hlogF_eq : Real.log ‖F z_b‖ =
      Real.log ‖spinQSlice c N Φ χ ((γN : ℂ) * bScale c' w)‖ -
        Real.log M_edge - Real.log ‖(confB z_b + I) ^ 4‖ := by
    dsimp [F]; rw [← hb_eq]
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMedge_pos,
      Real.log_mul (mul_pos (inv_pos.mpr hMedge_pos) (inv_pos.mpr (norm_pos_iff.mpr (by rwa [hb_eq])))).ne'
        (norm_pos_iff.mpr hq_ne).ne',
      Real.log_mul (inv_pos.mpr hMedge_pos).ne' (inv_pos.mpr (norm_pos_iff.mpr (by rwa [hb_eq]))).ne',
      Real.log_inv, Real.log_inv]
    ring
  have hlog_εa : Real.log (ε * a) = Real.log ε + Real.log a := Real.log_mul hε_pos.ne' ha_pos.ne'
  have hT2_ub : c' * (majorant2D (bScale c' w) + (tipL (bScale c' w)).re) ≤ tipH w + 1 := by
    linarith [(abs_le.mp hT2_bd).2]
  have hmB_le : m * Real.log B_slit ≤ Real.log B_slit :=
    mul_le_of_le_one_left (Real.log_nonneg hBslit_ge1) hm_le
  have h1m_le1 : 1 - m ≤ 1 := by linarith
  linarith [hPJ_le, hsplit_eq, hedge_le, hdecomp, hjensen, hmB_le, h1m_le1, hent_le, hlogK_eval,
    hT4.2, hlog_ent_geom, hlog_ε, h1m_loga, hMedge_cb_log, hlogF_eq, hlog_εa, hT2_ub]


end FormalResearch.ModularBootstrap.Spin
