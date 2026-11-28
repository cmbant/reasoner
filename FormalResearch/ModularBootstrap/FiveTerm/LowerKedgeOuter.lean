module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeOuterRegions

/-!
# Outer Band Edge-Kernel Asymptotic (`cts:Kedge-outer`)

Proves the uniform asymptotic for `virasoroKedgeEps` and uniform bound for `virasoroKedge1Eps`
for `x' ≥ xiStar + δ_hi` (`δ_hi > 0`) and `ε ∈ Ioo 0 (1 / 2)` (`virasoro_kedge_outer_of_delta`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
open FormalResearch.SignUncertainty.CtOsc

noncomputable section

private lemma kedge_outer_sp_part {v₀ δ_loc θ K_sp Kχ K_B vstar c' x' : ℝ}
    (hv₀_pos : 0 < v₀) (hδ_pos : 0 < δ_loc) (hδ1 : δ_loc ≤ 1)
    (hv_mδ : v₀ ≤ vstar - δ_loc) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (_hKsp0 : 0 ≤ K_sp) (hKχ_pos : 0 < Kχ) (hKB : 0 ≤ K_B)
    (hc'_pos : 0 < c') (hlam_ge : 1 ≤ c' * δ_loc ^ 2)
    (_hx_gt : xiStar < x') (hvstar_F : edgeF vstar = x')
    (hsp : ∀ {φ φ1 f f1 f2 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {KA lam : ℝ},
      Phase ((4 * π / 3) * edgeF' v₀) ((4 * π / 3) * (1 + 8 * π + 16 * π ^ 2)) φ φ1 f f1 f2 →
      D2 (Ioo (-1 : ℝ) 1) A A1 A2 KA → (∀ t, θ ≤ |t| → A t = 0) → 1 ≤ lam →
      ‖(∫ t : ℝ, A t * Complex.exp (Complex.I * (lam : ℂ) * ((φ t : ℝ) : ℂ))) -
          Complex.exp ((π : ℂ) / 4 * Complex.I) *
            ((√(2 * π / (lam * f 0)) : ℝ) : ℂ) * A 0‖ ≤ K_sp * KA / (lam * √lam))
    {χ χ1 χ2 : ℝ → ℝ} (hχ_D2 : D2 (univ : Set ℝ) (fun t => (χ t : ℂ)) (fun t => (χ1 t : ℂ))
      (fun t => (χ2 t : ℂ)) Kχ)
    (hχ_one : ∀ t, |t| ≤ θ / 2 → χ t = 1) (hχ_zero : ∀ t, θ ≤ |t| → χ t = 0 ∧ χ1 t = 0 ∧ χ2 t = 0)
    {B Bl1 Bl2 : ℝ → ℂ} (hBl : D2 (Ici v₀) B Bl1 Bl2 K_B)
    (hB_i : IntegrableOn (fun v => B v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi 0)) :
    let χv : ℝ → ℝ := fun v => χ ((v - vstar) / δ_loc)
    let e : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))
    IntegrableOn (fun v => (χv v : ℂ) * B v * e v) (Ioi 0) ∧
    ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        (∫ v in Ioi (0 : ℝ), (χv v : ℂ) * B v * e v) -
      Complex.I / (√(edgeF' vstar) : ℂ) * B vstar *
        Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))‖ ≤
      √(2 / 3) * (K_sp * (4 * Kχ * K_B) / δ_loc ^ 2) / c' := by
  intro χv e
  have hpi := Real.pi_pos
  have hχ_cont : Continuous χ := Complex.reCLM.continuous.comp
    (continuous_iff_continuousAt.mpr fun t => (hχ_D2.d1 t (mem_univ t)).continuousAt)
  have hχv_cont : Continuous χv := hχ_cont.comp ((continuous_id.sub continuous_const).div_const δ_loc)
  let χBs : ℝ → ℂ := fun v => (χv v : ℂ) * B v * e v
  have hχBs_int' : IntegrableOn (fun v => (χv v : ℂ) * (B v * e v)) (Ioi 0) :=
    hB_i.bdd_mul (Complex.continuous_ofReal.comp hχv_cont).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun v _ => by
        simpa using hχ_D2.b0 ((v - vstar) / δ_loc) (mem_univ _))
  have hχBs_int : IntegrableOn χBs (Ioi 0) :=
    hχBs_int'.congr_fun (fun v _ => by dsimp [χBs, e]; ring) measurableSet_Ioi
  have hχBs_supp : ∀ v, v ∉ Ioo (vstar - δ_loc) (vstar + δ_loc) → χBs v = 0 := fun v hv => by
    have hab : δ_loc ≤ |v - vstar| := by
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hv
      rcases hv with hv | hv
      · rw [abs_of_nonpos (sub_nonpos.mpr (by linarith))]; linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by linarith))]; linarith
    have ht : θ ≤ |(v - vstar) / δ_loc| := by
      rw [abs_div, abs_of_pos hδ_pos, le_div_iff₀ hδ_pos]
      exact (mul_le_of_le_one_left hδ_pos.le hθ1.le).trans hab
    dsimp [χBs, χv]; rw [(hχ_zero _ ht).1]; simp
  let A : ℝ → ℂ := fun t => (χ t : ℂ) * B (vstar + δ_loc * t)
  let A1 : ℝ → ℂ := fun t => (χ1 t : ℂ) * B (vstar + δ_loc * t) +
    (χ t : ℂ) * ((δ_loc : ℂ) * Bl1 (vstar + δ_loc * t))
  let A2 : ℝ → ℂ := fun t => (χ2 t : ℂ) * B (vstar + δ_loc * t) +
    2 * ((χ1 t : ℂ) * ((δ_loc : ℂ) * Bl1 (vstar + δ_loc * t))) +
    (χ t : ℂ) * (((δ_loc ^ 2 : ℝ) : ℂ) * Bl2 (vstar + δ_loc * t))
  have hD2_Bl_sc : D2 (Ioo (-1 : ℝ) 1) (fun t => B (vstar + δ_loc * t))
      (fun t => (δ_loc : ℂ) * Bl1 (vstar + δ_loc * t))
      (fun t => ((δ_loc ^ 2 : ℝ) : ℂ) * Bl2 (vstar + δ_loc * t)) K_B := by
    have hsc : ∀ t : ℝ, HasDerivAt (fun u => vstar + δ_loc * u) δ_loc t := fun t =>
      (((hasDerivAt_id t).const_mul δ_loc).const_add vstar).congr_deriv (by simp)
    have hmem : ∀ t ∈ Ioo (-1 : ℝ) 1, v₀ ≤ vstar + δ_loc * t := fun t ht => by nlinarith [ht.1, hv_mδ, hδ_pos]
    have hsc_c : Continuous fun t => vstar + δ_loc * t := continuous_const.add (continuous_const.mul continuous_id)
    have hδ2 : δ_loc ^ 2 ≤ 1 := pow_le_one₀ hδ_pos.le hδ1
    exact {
      d1 := fun t ht => by
        change HasDerivAt (B ∘ fun u => vstar + δ_loc * u) _ t
        exact ((hBl.d1 (vstar + δ_loc * t) (hmem t ht)).scomp t (hsc t)).congr_deriv (by rw [Complex.real_smul])
      d2 := fun t ht => by
        have h1 : HasDerivAt (Bl1 ∘ fun u => vstar + δ_loc * u) (δ_loc • Bl2 (vstar + δ_loc * t)) t :=
          (hBl.d2 (vstar + δ_loc * t) (hmem t ht)).scomp t (hsc t)
        exact (h1.const_mul (δ_loc : ℂ)).congr_deriv (by rw [Complex.real_smul]; push_cast; ring)
      c2 := continuousOn_const.mul (hBl.c2.comp hsc_c.continuousOn fun t ht => hmem t ht)
      K0 := hKB
      b0 := fun t ht => hBl.b0 (vstar + δ_loc * t) (hmem t ht)
      b1 := fun t ht => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
        exact (mul_le_mul hδ1 (hBl.b1 _ (hmem t ht)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      b2 := fun t ht => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (mul_le_mul hδ2 (hBl.b2 _ (hmem t ht)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _) }
  have hD2_A : D2 (Ioo (-1 : ℝ) 1) A A1 A2 (4 * Kχ * K_B) := by
    have hχ_Ioo : D2 (Ioo (-1 : ℝ) 1) (fun t => (χ t : ℂ)) (fun t => (χ1 t : ℂ)) (fun t => (χ2 t : ℂ)) Kχ := {
      d1 := fun t _ => hχ_D2.d1 t (mem_univ _)
      d2 := fun t _ => hχ_D2.d2 t (mem_univ _)
      c2 := hχ_D2.c2.mono fun _ _ => mem_univ _
      K0 := hχ_D2.K0
      b0 := fun t _ => hχ_D2.b0 t (mem_univ _)
      b1 := fun t _ => hχ_D2.b1 t (mem_univ _)
      b2 := fun t _ => hχ_D2.b2 t (mem_univ _) }
    have hd := D2_mulC hχ_Ioo hD2_Bl_sc
    exact {
      d1 := hd.d1
      d2 := hd.d2
      c2 := hd.c2
      K0 := hd.K0
      b0 := hd.b0
      b1 := hd.b1
      b2 := hd.b2 }
  let φ_sp := fun t => (phiDual (vstar + δ_loc * t) x' - phiDual vstar x') / δ_loc ^ 2
  let f_sp := fun t => (4 * π / 3) * edgeF' (vstar + δ_loc * t)
  have hph := phiDual_phase hv₀_pos hδ_pos hδ1 hv_mδ hvstar_F
  have hsp_bd := hsp hph hD2_A (fun t ht => by dsimp [A]; rw [(hχ_zero t ht).1]; simp) hlam_ge
  have hχBs_sp_eq : ∫ v in Ioi (0 : ℝ), χBs v =
      (δ_loc : ℂ) * Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ)) *
        ∫ t : ℝ, A t * Complex.exp (Complex.I * ((c' * δ_loc ^ 2 : ℝ) : ℂ) * ((φ_sp t : ℝ) : ℂ)) := by
    have hv_lo_pos : 0 < vstar - δ_loc := hv₀_pos.trans_le hv_mδ
    have h_set_eq : ∫ v in Ioi (0 : ℝ), χBs v = ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), χBs v := by
      have h1 : ∫ v in Ioi (0 : ℝ), χBs v = ∫ v : ℝ, χBs v :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
          hχBs_supp v fun hmem => hv (hv_lo_pos.trans hmem.1)
      have h2 : ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), χBs v = ∫ v : ℝ, χBs v :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
          hχBs_supp v fun hmem => hv ⟨hmem.1, hmem.2.le⟩
      rw [h1, h2]
    have h_int_eq : ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), χBs v =
        ∫ v in (vstar - δ_loc)..(vstar + δ_loc), χBs v := (intervalIntegral.integral_of_le (by linarith)).symm
    have h_cov := intervalIntegral.smul_integral_comp_mul_add χBs δ_loc vstar (a := -1) (b := 1)
    rw [show δ_loc * (-1) + vstar = vstar - δ_loc by ring, show δ_loc * 1 + vstar = vstar + δ_loc by ring] at h_cov
    have h_cov2 : ∫ v in (vstar - δ_loc)..(vstar + δ_loc), χBs v =
        (δ_loc : ℂ) * ∫ t in (-1 : ℝ)..1, χBs (vstar + δ_loc * t) := by
      rw [← h_cov, Complex.real_smul]; congr 2; ext t; rw [add_comm vstar]
    have h_int_t : ∫ t in (-1 : ℝ)..1, χBs (vstar + δ_loc * t) = ∫ t : ℝ, χBs (vstar + δ_loc * t) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hχBs_supp _ fun hmem => ht ?_
      rw [mem_Ioc]; exact ⟨by nlinarith [hmem.1], by nlinarith [hmem.2]⟩
    have h_pt : ∀ t : ℝ, χBs (vstar + δ_loc * t) =
        Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ)) *
          (A t * Complex.exp (Complex.I * ((c' * δ_loc ^ 2 : ℝ) : ℂ) * ((φ_sp t : ℝ) : ℂ))) := fun t => by
      dsimp [χBs, χv, A, e, φ_sp]
      rw [show (vstar + δ_loc * t - vstar) / δ_loc = t by field_simp [hδ_pos.ne']; ring]
      calc (χ t : ℂ) * B (vstar + δ_loc * t) *
            Complex.exp (Complex.I * ((c' * phiDual (vstar + δ_loc * t) x' : ℝ) : ℂ))
          = ((χ t : ℂ) * B (vstar + δ_loc * t)) *
              (Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ((c' * δ_loc ^ 2 : ℝ) : ℂ) *
                  (((phiDual (vstar + δ_loc * t) x' - phiDual vstar x') / δ_loc ^ 2 : ℝ) : ℂ))) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast; field_simp [hδ_pos.ne']; ring
        _ = _ := by ring
    rw [h_set_eq, h_int_eq, h_cov2, h_int_t]
    simp_rw [h_pt, integral_const_mul]; ring
  have hpref_norm : ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * (δ_loc : ℂ) *
      Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ))‖ = √(2 / 3) * √c' * δ_loc := by
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖(√(2 * c' / 3) : ℂ)‖ = √(2 / 3) * √c' := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        show 2 * c' / 3 = (2 / 3) * c' by ring, Real.sqrt_mul (by norm_num)]
    have h2 : ‖Complex.exp (Complex.I * (π : ℂ) / 4)‖ = 1 := by
      rw [show Complex.I * (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have h3 : ‖(δ_loc : ℂ)‖ = δ_loc := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
    have h4 : ‖Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
    rw [h1, h2, h3, h4]; ring
  have hmain_eq : √(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
      ((δ_loc : ℂ) * Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ)) *
        (Complex.exp ((π : ℂ) / 4 * Complex.I) *
          ((√(2 * π / ((c' * δ_loc ^ 2) * f_sp 0)) : ℝ) : ℂ) * A 0)) =
      Complex.I / (√(edgeF' vstar) : ℂ) * B vstar *
        Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)) := by
    have hA0 : A 0 = B vstar := by dsimp [A]; rw [mul_zero, add_zero, hχ_one 0 (by simp; positivity)]; simp
    have hf0 : f_sp 0 = (4 * π / 3) * edgeF' vstar := by dsimp [f_sp]; rw [mul_zero, add_zero]
    have hexp_i : Complex.exp (Complex.I * (π : ℂ) / 4) * Complex.exp ((π : ℂ) / 4 * Complex.I) = Complex.I := by
      rw [← Complex.exp_add, show Complex.I * (π : ℂ) / 4 + (π : ℂ) / 4 * Complex.I =
        ((π / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    have hvstar_pos : 0 < vstar := hv₀_pos.trans_le (hv_mδ.trans (by linarith))
    have hphi_v : phiDual vstar x' = -2 * π * cumulN x' := by
      rw [phiDual_eq hvstar_pos.le, hvstar_F, sub_self, mul_zero, zero_mul, zero_sub]; ring
    have hF'v_pos : 0 < edgeF' vstar := edgeF'_pos (hv₀_pos.trans_le (hv_mδ.trans (by linarith : vstar - δ_loc ≤ vstar)))
    have hrt_eq : √(2 * c' / 3) * δ_loc * √(2 * π / ((c' * δ_loc ^ 2) * ((4 * π / 3) * edgeF' vstar))) =
        (√(edgeF' vstar))⁻¹ := by
      rw [show (2 * π / ((c' * δ_loc ^ 2) * ((4 * π / 3) * edgeF' vstar))) =
          (3 / (2 * c')) * (δ_loc ^ 2)⁻¹ * (edgeF' vstar)⁻¹ by
          field_simp [hpi.ne', hc'_pos.ne', hδ_pos.ne', hF'v_pos.ne']; ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_inv, Real.sqrt_sq hδ_pos.le,
        Real.sqrt_inv, Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
      field_simp [(Real.sqrt_pos.mpr hc'_pos).ne', (Real.sqrt_pos.mpr zero_lt_three).ne',
        (Real.sqrt_pos.mpr zero_lt_two).ne', hδ_pos.ne', (Real.sqrt_pos.mpr hF'v_pos).ne']
    rw [hA0, hf0, hphi_v]
    have hpush : √(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        ((δ_loc : ℂ) * Complex.exp (Complex.I * ((c' * (-2 * π * cumulN x') : ℝ) : ℂ)) *
          (Complex.exp ((π : ℂ) / 4 * Complex.I) *
            ((√(2 * π / ((c' * δ_loc ^ 2) * ((4 * π / 3) * edgeF' vstar))) : ℝ) : ℂ) * B vstar)) =
        ((√(2 * c' / 3) * δ_loc * √(2 * π / ((c' * δ_loc ^ 2) * ((4 * π / 3) * edgeF' vstar))) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (π : ℂ) / 4) * Complex.exp ((π : ℂ) / 4 * Complex.I)) *
          B vstar * Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)) := by
      push_cast
      rw [show Complex.I * ((c' : ℂ) * (-2 * (π : ℂ) * (cumulN x' : ℂ))) =
          -Complex.I * (2 * (π : ℂ) * (c' : ℂ) * (cumulN x' : ℂ)) by ring]
      ring
    rw [hpush, hrt_eq, hexp_i]; push_cast; ring
  refine ⟨hχBs_int, ?_⟩
  change ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * (∫ v in Ioi (0 : ℝ), χBs v) -
      Complex.I / (√(edgeF' vstar) : ℂ) * B vstar *
        Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))‖ ≤ _
  rw [hχBs_sp_eq, ← hmain_eq]
  have hfac : √(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
      ((δ_loc : ℂ) * Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ)) *
        ∫ t : ℝ, A t * Complex.exp (Complex.I * ((c' * δ_loc ^ 2 : ℝ) : ℂ) * ((φ_sp t : ℝ) : ℂ))) -
      √(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        ((δ_loc : ℂ) * Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ)) *
          (Complex.exp ((π : ℂ) / 4 * Complex.I) *
            ((√(2 * π / ((c' * δ_loc ^ 2) * f_sp 0)) : ℝ) : ℂ) * A 0)) =
      (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * (δ_loc : ℂ) *
        Complex.exp (Complex.I * ((c' * phiDual vstar x' : ℝ) : ℂ))) *
        ((∫ t : ℝ, A t * Complex.exp (Complex.I * ((c' * δ_loc ^ 2 : ℝ) : ℂ) * ((φ_sp t : ℝ) : ℂ))) -
          Complex.exp ((π : ℂ) / 4 * Complex.I) *
            ((√(2 * π / ((c' * δ_loc ^ 2) * f_sp 0)) : ℝ) : ℂ) * A 0) := by ring
  rw [hfac, norm_mul, hpref_norm]
  have hcalc : (√(2 / 3) * √c' * δ_loc) * (K_sp * (4 * Kχ * K_B) / ((c' * δ_loc ^ 2) * √(c' * δ_loc ^ 2))) =
      √(2 / 3) * (K_sp * (4 * Kχ * K_B) / δ_loc ^ 2) / c' := by
    rw [Real.sqrt_mul hc'_pos.le, Real.sqrt_sq hδ_pos.le]
    field_simp [(Real.sqrt_pos.mpr hc'_pos).ne', hδ_pos.ne', hc'_pos.ne']
  calc (√(2 / 3) * √c' * δ_loc) * _
      ≤ (√(2 / 3) * √c' * δ_loc) * (K_sp * (4 * Kχ * K_B) / ((c' * δ_loc ^ 2) * √(c' * δ_loc ^ 2))) :=
        mul_le_mul_of_nonneg_left hsp_bd (by positivity)
    _ = √(2 / 3) * (K_sp * (4 * Kχ * K_B) / δ_loc ^ 2) / c' := hcalc

private def outerCsm (M0 M1 M2 δ_mid v₀ : ℝ) : ℝ :=
  M0 / δ_mid + M1 / δ_mid ^ 2 + M0 * (4 * π / 3) / δ_mid ^ 3 +
    2 * M2 / δ_mid ^ 2 + 6 * M1 * (4 * π / 3) * v₀ ^ (1 / 2 : ℝ) / δ_mid ^ 3 +
    (2 / 3) * M0 * v₀ ^ (3 / 2 : ℝ) * (32 * π ^ 2 / 3 / δ_mid ^ 3 + 3 * (4 * π / 3) ^ 2 / δ_mid ^ 4)

private def outerCout (Kχ K_B δ_loc θ v₀ : ℝ) : ℝ :=
  let K_χs := Kχ / δ_loc ^ 2
  let K_L := 4 * (1 + K_χs) * K_B
  let c0 := (4 * π / 3) * edgeF' v₀
  let η := (θ / 4) * δ_loc
  K_L * (1 / c0 ^ 2 + 3 * (4 * π / 3) / (c0 ^ 3 * η) + (32 * π ^ 2 / 3) / (c0 ^ 3 * η) +
    3 * (4 * π / 3) ^ 2 / (c0 ^ 4 * η ^ 2)) / η

private def outerCtail (Kχ δ_loc θ v₀ C0 C1 L2 : ℝ) : ℝ :=
  let K_χs := Kχ / δ_loc ^ 2
  let δ_tail := (4 * π / 3) * edgeF' v₀ * ((θ / 4) * δ_loc)
  let K0_R := (1 + Kχ) * C0
  let K1_R := K_χs * C0 + (1 + Kχ) * C1
  let L2_R := (1 + Kχ) * L2 + 2 * δ_loc * (K_χs * C0 + 2 * K_χs * C1)
  L2_R / δ_tail ^ 2 + (3 / 2 : ℝ) * K1_R / δ_tail ^ 2 +
    (1 / 2 : ℝ) * K0_R * ((2 * π) / edgeF' v₀) / δ_tail ^ 2 + (4 * π / 3) * K0_R / δ_tail ^ 3

private lemma outerCsm_nonneg {M0 M1 M2 δ_mid v₀ : ℝ}
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hδ : 0 < δ_mid) (hv₀ : 0 < v₀) :
    0 ≤ outerCsm M0 M1 M2 δ_mid v₀ := by
  unfold outerCsm; positivity

private lemma outerCout_nonneg {Kχ K_B δ_loc θ v₀ : ℝ}
    (hKχ : 0 < Kχ) (hKB : 0 ≤ K_B) (hδ : 0 < δ_loc) (hθ : 0 < θ) (hv₀ : 0 < v₀) :
    0 ≤ outerCout Kχ K_B δ_loc θ v₀ := by
  have := (edgeF'_pos hv₀).le
  unfold outerCout; positivity

private lemma outerCtail_nonneg {Kχ δ_loc θ v₀ C0 C1 L2 : ℝ}
    (hKχ : 0 < Kχ) (hδ : 0 < δ_loc) (hθ : 0 < θ) (hv₀ : 0 < v₀)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hL2 : 0 ≤ L2) :
    0 ≤ outerCtail Kχ δ_loc θ v₀ C0 C1 L2 := by
  have := (edgeF'_pos hv₀).le
  unfold outerCtail; positivity

private lemma kedge_outer_left_part {v_s v₀ vstar v_L δ_loc θ Kχ K_B M0 M1 M2 δ_mid c' x' : ℝ}
    (hvs : 0 < v_s) (hvs_le : v_s ≤ v₀) (hv₀_pos : 0 < v₀) (hv₀_L : v₀ ≤ v_L) (hv_L_lt : v_L < vstar)
    (hδ : 0 < δ_loc) (hδ1 : δ_loc ≤ 1) (hv_mδ : v₀ ≤ vstar - δ_loc)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hvL_eq : v_L = vstar - (θ / 4) * δ_loc)
    (hKχ_pos : 0 < Kχ) (hKB : 0 ≤ K_B) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hδ_pos : 0 < δ_mid) (hc' : 1 ≤ c') (hvs_eq : v_s = c'⁻¹) (hx' : edgeF vstar = x')
    (hδ_mid : ∀ v ∈ Icc v_s v₀, δ_mid ≤ (4 * π / 3) * (x' - edgeF v))
    {χ χ1 χ2 : ℝ → ℝ} (hdχ1 : ∀ t, HasDerivAt χ (χ1 t) t) (hdχ2 : ∀ t, HasDerivAt χ1 (χ2 t) t)
    (hχ_D2 : D2 (univ : Set ℝ) (fun t => (χ t : ℂ)) (fun t => (χ1 t : ℂ)) (fun t => (χ2 t : ℂ)) Kχ)
    (hχ_one : ∀ t, |t| ≤ θ / 2 → χ t = 1) (hχ_zero : ∀ t, θ ≤ |t| → χ t = 0 ∧ χ1 t = 0 ∧ χ2 t = 0)
    {B Bs1 Bs2 Bl1 Bl2 : ℝ → ℂ}
    (hBs_d : ∀ v ∈ Ioc (0 : ℝ) v₀, HasDerivAt B (Bs1 v) v ∧ HasDerivAt Bs1 (Bs2 v) v)
    (hBs_c : ContinuousOn Bs2 (Ioc (0 : ℝ) v₀))
    (hBs_bd : ∀ v ∈ Ioc (0 : ℝ) v₀,
      ‖B v‖ ≤ M0 * v ^ (1 / 2 : ℝ) ∧ ‖Bs1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)) ∧ ‖Bs2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ)))
    (hBl : D2 (Ici v₀) B Bl1 Bl2 K_B) :
    let χv : ℝ → ℝ := fun v => χ ((v - vstar) / δ_loc)
    let e : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))
    ‖(∫ v in v_s..v₀, B v * e v) + ∫ v in v₀..v_L, (1 - (χv v : ℂ)) * B v * e v‖ ≤
      outerCsm M0 M1 M2 δ_mid v₀ * c' ^ (-(3 / 2 : ℝ)) + outerCout Kχ K_B δ_loc θ v₀ * c' ^ (-2 : ℝ) := by
  intro χv e
  unfold outerCsm outerCout
  set K_χs : ℝ := Kχ / δ_loc ^ 2
  set K_L : ℝ := 4 * (1 + K_χs) * K_B
  set c0 : ℝ := (4 * π / 3) * edgeF' v₀
  set η : ℝ := (θ / 4) * δ_loc
  have hpi := Real.pi_pos
  have hKχs_pos : 0 < K_χs := div_pos hKχ_pos (pow_pos hδ 2)
  let χv1 := fun v : ℝ => χ1 ((v - vstar) / δ_loc) / δ_loc
  let χv2 := fun v : ℝ => χ2 ((v - vstar) / δ_loc) / δ_loc ^ 2
  have hχv_d1 : ∀ v, HasDerivAt χv (χv1 v) v := fun v =>
    ((hdχ1 ((v - vstar) / δ_loc)).comp v (((hasDerivAt_id v).sub_const vstar).div_const δ_loc)).congr_deriv
      (by dsimp [χv1]; ring)
  have hχv_d2 : ∀ v, HasDerivAt χv1 (χv2 v) v := fun v =>
    (((hdχ2 ((v - vstar) / δ_loc)).comp v (((hasDerivAt_id v).sub_const vstar).div_const δ_loc)).div_const
      δ_loc).congr_deriv (by dsimp [χv2]; ring)
  have hχv_zero : ∀ v, θ * δ_loc ≤ |v - vstar| → χv v = 0 ∧ χv1 v = 0 ∧ χv2 v = 0 := fun v hv => by
    have ht : θ ≤ |(v - vstar) / δ_loc| := by rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]; exact hv
    have hz := hχ_zero ((v - vstar) / δ_loc) ht
    refine ⟨hz.1, ?_, ?_⟩
    · dsimp [χv1]; rw [hz.2.1, zero_div]
    · dsimp [χv2]; rw [hz.2.2, zero_div]
  have hχv_zero_v0 : χv v₀ = 0 ∧ χv1 v₀ = 0 := by
    have h1 := hχv_zero v₀ (by
      rw [abs_of_neg (by linarith [hv_mδ, hδ])]
      exact (mul_le_of_le_one_left hδ.le hθ1.le).trans (by linarith [hv_mδ]))
    exact ⟨h1.1, h1.2.1⟩
  have hvL_in : χv v_L = 1 ∧ χv1 v_L = 0 := by
    have h1 : v_L ∈ Ioo (vstar - (θ / 2) * δ_loc) (vstar + (θ / 2) * δ_loc) := by
      have hpos : 0 < θ * δ_loc := mul_pos hθ hδ
      rw [hvL_eq]; dsimp [η]; constructor <;> linarith
    have hev : χv =ᶠ[𝓝 v_L] 1 := Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h1) fun u hu => by
      apply hχ_one; rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ, abs_le]
      constructor <;> linarith [hu.1, hu.2]
    exact ⟨hev.self_of_nhds, (hχv_d1 v_L).congr_of_eventuallyEq hev.symm |>.unique (hasDerivAt_const v_L 1)⟩
  let ϕ1 : ℝ → ℝ := fun v => (4 * π / 3) * (edgeF v - x')
  let ϕ2 : ℝ → ℝ := fun v => (4 * π / 3) * edgeF' v
  let BL := fun v => (1 - (χv v : ℂ)) * B v
  let BL1 := fun v => (-(χv1 v : ℝ) : ℂ) * B v + (1 - (χv v : ℂ)) * Bl1 v
  let BL2 := fun v => (-(χv2 v : ℝ) : ℂ) * B v + 2 * ((-(χv1 v : ℝ) : ℂ) * Bl1 v) + (1 - (χv v : ℂ)) * Bl2 v
  have h1χ_D2 : D2 (univ : Set ℝ) (fun v => (1 : ℂ) - (χv v : ℂ)) (fun v => (-(χv1 v : ℝ) : ℂ))
      (fun v => (-(χv2 v : ℝ) : ℂ)) (1 + K_χs) := by
    have hχv_D2 : D2 (univ : Set ℝ) (fun v => (χv v : ℂ)) (fun v => (χv1 v : ℂ)) (fun v => (χv2 v : ℂ)) K_χs := {
      d1 := fun v _ => (hχv_d1 v).ofReal_comp
      d2 := fun v _ => (hχv_d2 v).ofReal_comp
      c2 := by
        have hc2 : Continuous χ2 := Complex.reCLM.continuous.comp (continuousOn_univ.mp hχ_D2.c2)
        exact (Complex.continuous_ofReal.comp ((hc2.comp ((continuous_id.sub continuous_const).div_const δ_loc)).div_const
          (δ_loc ^ 2))).continuousOn
      K0 := hKχs_pos.le
      b0 := fun v _ => (hχ_D2.b0 ((v - vstar) / δ_loc) (mem_univ _)).trans (by
        dsimp [K_χs]
        have hδ2 : δ_loc ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
        exact (le_div_iff₀ (pow_pos hδ 2)).mpr (mul_le_of_le_one_right hKχ_pos.le hδ2))
      b1 := fun v _ => by
        dsimp [χv1]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hδ]
        have h1 := hχ_D2.b1 ((v - vstar) / δ_loc) (mem_univ _)
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        calc |χ1 ((v - vstar) / δ_loc)| / δ_loc ≤ Kχ / δ_loc := div_le_div_of_nonneg_right h1 hδ.le
          _ = Kχ * δ_loc / δ_loc ^ 2 := by field_simp [hδ.ne']
          _ ≤ Kχ * 1 / δ_loc ^ 2 := by gcongr
          _ = K_χs := by dsimp [K_χs]; ring
      b2 := fun v _ => by
        dsimp [χv2]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hδ 2)]
        have h2 := hχ_D2.b2 ((v - vstar) / δ_loc) (mem_univ _)
        rw [Complex.norm_real, Real.norm_eq_abs] at h2
        exact div_le_div_of_nonneg_right h2 (sq_nonneg _) }
    exact {
      d1 := fun v hv => ((hasDerivAt_const v (1 : ℂ)).sub (hχv_D2.d1 v hv)).congr_deriv (by rw [zero_sub])
      d2 := fun v hv => ((hχv_D2.d2 v hv).neg).congr_deriv (by rfl)
      c2 := by change ContinuousOn (fun v => -((χv2 v : ℝ) : ℂ)) univ; exact hχv_D2.c2.neg
      K0 := by linarith
      b0 := fun v hv => (norm_sub_le (1 : ℂ) (χv v : ℂ)).trans (by rw [norm_one]; linarith [hχv_D2.b0 v hv])
      b1 := fun v hv => by rw [norm_neg]; exact (hχv_D2.b1 v hv).trans (by linarith)
      b2 := fun v hv => by rw [norm_neg]; exact (hχv_D2.b2 v hv).trans (by linarith) }
  have hBL_D2 : D2 (Icc v₀ v_L) BL BL1 BL2 K_L := by
    have h1χ_I : D2 (Icc v₀ v_L) (fun v => (1 : ℂ) - (χv v : ℂ)) (fun v => (-(χv1 v : ℝ) : ℂ))
        (fun v => (-(χv2 v : ℝ) : ℂ)) (1 + K_χs) := {
      d1 := fun v _ => h1χ_D2.d1 v (mem_univ _)
      d2 := fun v _ => h1χ_D2.d2 v (mem_univ _)
      c2 := h1χ_D2.c2.mono fun _ _ => mem_univ _
      K0 := h1χ_D2.K0
      b0 := fun v _ => h1χ_D2.b0 v (mem_univ _)
      b1 := fun v _ => h1χ_D2.b1 v (mem_univ _)
      b2 := fun v _ => h1χ_D2.b2 v (mem_univ _) }
    have hBl_I : D2 (Icc v₀ v_L) B Bl1 Bl2 K_B := {
      d1 := fun v hv => hBl.d1 v hv.1
      d2 := fun v hv => hBl.d2 v hv.1
      c2 := hBl.c2.mono fun _ hv => hv.1
      K0 := hBl.K0
      b0 := fun v hv => hBl.b0 v hv.1
      b1 := fun v hv => hBl.b1 v hv.1
      b2 := fun v hv => hBl.b2 v hv.1 }
    have hmul := D2_mulC h1χ_I hBl_I
    exact {
      d1 := hmul.d1
      d2 := hmul.d2
      c2 := hmul.c2
      K0 := hmul.K0
      b0 := hmul.b0
      b1 := hmul.b1
      b2 := hmul.b2 }
  have hs1_eq : Bs1 v₀ = Bl1 v₀ := (hBs_d v₀ ⟨hv₀_pos, le_rfl⟩).1.unique (hBl.d1 v₀ le_rfl)
  have hb_mid := kedge_left_ibp_mid_bound hvs hvs_le hM0 hM1 hM2 hδ_pos hc' hvs_eq hδ_mid
    (fun v hv => (hBs_d v hv).1) (fun v hv => (hBs_d v hv).2) hBs_c
    (fun v hv => (hBs_bd v hv).1) (fun v hv => (hBs_bd v hv).2.1) (fun v hv => (hBs_bd v hv).2.2)
  have hb_out := kedge_left_ibp_outer_bound hv₀_pos hv₀_L hv_L_lt hδ hθ hvL_eq (by positivity) hc' hx'
    hBL_D2 ⟨by dsimp [BL]; rw [hvL_in.1]; simp, by dsimp [BL1]; rw [hvL_in.1, hvL_in.2]; simp⟩
  have hB0_match : BL v₀ = B v₀ ∧ BL1 v₀ = Bs1 v₀ :=
    ⟨by dsimp [BL]; rw [hχv_zero_v0.1]; simp,
     by dsimp [BL1]; rw [hχv_zero_v0.1, hχv_zero_v0.2, hs1_eq]; simp⟩
  have hsum_eq : (∫ v in v_s..v₀, B v * e v) + ∫ v in v₀..v_L, (1 - (χv v : ℂ)) * B v * e v =
      ((∫ v in v_s..v₀, B v * Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v x' : ℝ) : ℂ))) -
        ((1 / (Complex.I * (c' : ℂ))) * (B v₀ / (ϕ1 v₀ : ℂ) *
            Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v₀ x' : ℝ) : ℂ))) -
          (1 / (Complex.I * (c' : ℂ))) ^ 2 *
            (ibpH B Bs1 ϕ1 ϕ2 v₀ / (ϕ1 v₀ : ℂ) *
              Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v₀ x' : ℝ) : ℂ))))) +
      ((∫ v in v₀..v_L, BL v * Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v x' : ℝ) : ℂ))) +
        ((1 / (Complex.I * (c' : ℂ))) * (BL v₀ / (ϕ1 v₀ : ℂ) *
            Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v₀ x' : ℝ) : ℂ))) -
          (1 / (Complex.I * (c' : ℂ))) ^ 2 *
            (ibpH BL BL1 ϕ1 ϕ2 v₀ / (ϕ1 v₀ : ℂ) *
              Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v₀ x' : ℝ) : ℂ))))) := by
    have hev0 : BL v₀ / (ϕ1 v₀ : ℂ) * Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v₀ x' : ℝ) : ℂ)) =
        B v₀ / (ϕ1 v₀ : ℂ) * Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v₀ x' : ℝ) : ℂ)) := by
      rw [hB0_match.1]
    have hibp0 : ibpH BL BL1 ϕ1 ϕ2 v₀ = ibpH B Bs1 ϕ1 ϕ2 v₀ := by unfold ibpH; rw [hB0_match.1, hB0_match.2]
    have h_e : ∀ v, e v = Complex.exp (Complex.I * (c' : ℂ) * ((phiDual v x' : ℝ) : ℂ)) := fun v => by
      dsimp [e]; push_cast; rw [mul_assoc]
    rw [hev0, hibp0]; simp_rw [← h_e]; change _ = _; ring
  rw [hsum_eq]
  exact (norm_add_le _ _).trans (add_le_add hb_mid hb_out)

private lemma kedge_outer_tail_part {v₀ vstar v_R δ_loc θ Kχ C0 C1 C2 L1 L2 c' x' : ℝ}
    (hv₀_pos : 0 < v₀) (hvR_ge : v₀ ≤ v_R) (hv_mδ : v₀ ≤ vstar - δ_loc) (hvstar_R : vstar < v_R)
    (hδ_pos : 0 < δ_loc) (hδ1 : δ_loc ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hvR_eq : v_R = vstar + (θ / 4) * δ_loc)
    (hKχ_pos : 0 < Kχ) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (hc'_pos : 0 < c') (hx' : edgeF vstar = x')
    {χ χ1 χ2 : ℝ → ℝ} (hdχ1 : ∀ t, HasDerivAt χ (χ1 t) t) (hdχ2 : ∀ t, HasDerivAt χ1 (χ2 t) t)
    (hχ_D2 : D2 (univ : Set ℝ) (fun t => (χ t : ℂ)) (fun t => (χ1 t : ℂ)) (fun t => (χ2 t : ℂ)) Kχ)
    (hχ_one : ∀ t, |t| ≤ θ / 2 → χ t = 1) (hχ_zero : ∀ t, θ ≤ |t| → χ t = 0 ∧ χ1 t = 0 ∧ χ2 t = 0)
    {B F1 F2 : ℝ → ℂ} (h_osc : OscAmpBound v₀ B F1 F2) (hconsts : h_osc.HasConsts C0 C1 C2 L1 L2)
    (hint_R : IntegrableOn (fun v => (1 - (χ ((v - vstar) / δ_loc) : ℂ)) * B v *
      Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi v_R)) :
    let χv : ℝ → ℝ := fun v => χ ((v - vstar) / δ_loc)
    let e : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))
    ‖∫ v in Ioi v_R, (1 - (χv v : ℂ)) * B v * e v‖ ≤
      outerCtail Kχ δ_loc θ v₀ C0 C1 L2 * c' ^ (-2 : ℝ) := by
  intro χv e
  unfold outerCtail
  set K_χs : ℝ := Kχ / δ_loc ^ 2
  set δ_tail : ℝ := (4 * π / 3) * edgeF' v₀ * ((θ / 4) * δ_loc)
  set K0_R : ℝ := (1 + Kχ) * C0
  set K1_R : ℝ := K_χs * C0 + (1 + Kχ) * C1
  set K2_R : ℝ := K_χs * C0 + 2 * K_χs * C1 + (1 + Kχ) * C2
  set L1_R : ℝ := (1 + Kχ) * L1 + 2 * δ_loc * (K_χs * C0)
  set L2_R : ℝ := (1 + Kχ) * L2 + 2 * δ_loc * (K_χs * C0 + 2 * K_χs * C1)
  set C_tail : ℝ := L2_R / δ_tail ^ 2 + (3 / 2 : ℝ) * K1_R / δ_tail ^ 2 +
    (1 / 2 : ℝ) * K0_R * ((2 * π) / edgeF' v₀) / δ_tail ^ 2 + (4 * π / 3) * K0_R / δ_tail ^ 3
  have hpi := Real.pi_pos
  have hKχs_pos : 0 < K_χs := div_pos hKχ_pos (pow_pos hδ_pos 2)
  obtain ⟨hC0', hC1', hC2', hL1', hL2'⟩ := hconsts
  let χv1 := fun v : ℝ => χ1 ((v - vstar) / δ_loc) / δ_loc
  let χv2 := fun v : ℝ => χ2 ((v - vstar) / δ_loc) / δ_loc ^ 2
  have hχv_d1 : ∀ v, HasDerivAt χv (χv1 v) v := fun v =>
    ((hdχ1 ((v - vstar) / δ_loc)).comp v (((hasDerivAt_id v).sub_const vstar).div_const δ_loc)).congr_deriv
      (by dsimp [χv1]; ring)
  have hχv_d2 : ∀ v, HasDerivAt χv1 (χv2 v) v := fun v =>
    (((hdχ2 ((v - vstar) / δ_loc)).comp v (((hasDerivAt_id v).sub_const vstar).div_const δ_loc)).div_const
      δ_loc).congr_deriv (by dsimp [χv2]; ring)
  have hχ_cont : Continuous χ := Complex.reCLM.continuous.comp
    (continuous_iff_continuousAt.mpr fun t => (hχ_D2.d1 t (mem_univ t)).continuousAt)
  have hχ1_cont : Continuous χ1 := Complex.reCLM.continuous.comp
    (continuous_iff_continuousAt.mpr fun t => (hχ_D2.d2 t (mem_univ t)).continuousAt)
  have hχ2_cont : Continuous χ2 := Complex.reCLM.continuous.comp (continuousOn_univ.mp hχ_D2.c2)
  have hχv_cont : Continuous χv := hχ_cont.comp ((continuous_id.sub continuous_const).div_const δ_loc)
  have hχv1_cont : Continuous χv1 := (hχ1_cont.comp ((continuous_id.sub continuous_const).div_const δ_loc)).div_const δ_loc
  have hχv2_cont : Continuous χv2 :=
    (hχ2_cont.comp ((continuous_id.sub continuous_const).div_const δ_loc)).div_const (δ_loc ^ 2)
  have hBR_supp : ∀ v, v ∉ Ioc (vstar - δ_loc) (vstar + δ_loc) → χv v = 0 ∧ χv1 v = 0 ∧ χv2 v = 0 := fun v hv => by
    have hab : δ_loc ≤ |v - vstar| := by
      rw [mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_nonpos (sub_nonpos.mpr (by linarith))]; linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by linarith))]; linarith
    have ht : θ ≤ |(v - vstar) / δ_loc| := by
      rw [abs_div, abs_of_pos hδ_pos, le_div_iff₀ hδ_pos]
      exact (mul_le_of_le_one_left hδ_pos.le hθ1.le).trans hab
    have hz := hχ_zero ((v - vstar) / δ_loc) ht
    refine ⟨hz.1, ?_, ?_⟩
    · dsimp [χv1]; rw [hz.2.1, zero_div]
    · dsimp [χv2]; rw [hz.2.2, zero_div]
  have hvR_in : χv v_R = 1 ∧ χv1 v_R = 0 := by
    have h1 : v_R ∈ Ioo (vstar - (θ / 2) * δ_loc) (vstar + (θ / 2) * δ_loc) := by
      have hpos : 0 < θ * δ_loc := mul_pos hθ0 hδ_pos
      rw [hvR_eq]; constructor <;> linarith
    have hev : χv =ᶠ[𝓝 v_R] 1 := Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h1) fun u hu => by
      apply hχ_one; rw [abs_div, abs_of_pos hδ_pos, div_le_iff₀ hδ_pos, abs_le]
      constructor <;> linarith [hu.1, hu.2]
    exact ⟨hev.self_of_nhds, (hχv_d1 v_R).congr_of_eventuallyEq hev.symm |>.unique (hasDerivAt_const v_R 1)⟩
  let BR := fun v => (1 - (χv v : ℂ)) * B v
  let BR1 := fun v => (-(χv1 v : ℝ) : ℂ) * B v + (1 - (χv v : ℂ)) * F1 v
  let BR2 := fun v => (-(χv2 v : ℝ) : ℂ) * B v + 2 * ((-(χv1 v : ℝ) : ℂ) * F1 v) + (1 - (χv v : ℂ)) * F2 v
  have hc_1χ : Continuous fun v : ℝ => (1 : ℂ) - (χv v : ℂ) :=
    continuous_const.sub (Complex.continuous_ofReal.comp hχv_cont)
  have h1χ_bd : ∀ v : ℝ, ‖(1 : ℂ) - (χv v : ℂ)‖ ≤ 1 + Kχ := fun v =>
    (norm_sub_le (1 : ℂ) (χv v : ℂ)).trans (by rw [norm_one]; linarith [hχ_D2.b0 ((v - vstar) / δ_loc) (mem_univ _)])
  have hχ1_bd : ∀ v : ℝ, ‖(-(χv1 v : ℝ) : ℂ)‖ ≤ K_χs := fun v => by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    dsimp [χv1]; rw [abs_div, abs_of_pos hδ_pos]
    have h1 := hχ_D2.b1 ((v - vstar) / δ_loc) (mem_univ _)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    calc |χ1 ((v - vstar) / δ_loc)| / δ_loc ≤ Kχ / δ_loc := div_le_div_of_nonneg_right h1 hδ_pos.le
      _ = Kχ * δ_loc / δ_loc ^ 2 := by field_simp [hδ_pos.ne']
      _ ≤ Kχ * 1 / δ_loc ^ 2 := by gcongr
      _ = K_χs := by dsimp [K_χs]; ring
  have hχ2_bd : ∀ v : ℝ, ‖(-(χv2 v : ℝ) : ℂ)‖ ≤ K_χs := fun v => by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    dsimp [χv2]; rw [abs_div, abs_of_pos (pow_pos hδ_pos 2)]
    have h2 := hχ_D2.b2 ((v - vstar) / δ_loc) (mem_univ _)
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    exact div_le_div_of_nonneg_right h2 (sq_nonneg _)
  have h_zero_bd_int : ∀ (g : ℝ → ℂ) (M : ℝ), 0 ≤ M →
      (∀ v, v ∉ Ioc (vstar - δ_loc) (vstar + δ_loc) → g v = 0) →
      (∀ v, ‖g v‖ ≤ M) → AEStronglyMeasurable g (volume.restrict (Ioi v₀)) →
      IntegrableOn g (Ioi v₀) ∧ ∫ v in Ioi v₀, ‖g v‖ ≤ 2 * δ_loc * M := fun g M hM hgz hgb hgm => by
    have hsub_s : Ioc (vstar - δ_loc) (vstar + δ_loc) ⊆ Ioi v₀ := fun v hv => lt_of_le_of_lt hv_mδ hv.1
    have hint_ioc : IntegrableOn g (Ioc (vstar - δ_loc) (vstar + δ_loc)) :=
      IntegrableOn.of_bound measure_Ioc_lt_top (hgm.mono_set hsub_s) M
        ((ae_restrict_mem measurableSet_Ioc).mono fun v _ => hgb v)
    have hint_compl : IntegrableOn g (Ioi v₀ \ Ioc (vstar - δ_loc) (vstar + δ_loc)) :=
      (integrableOn_zero (μ := volume) (s := Ioi v₀ \ Ioc (vstar - δ_loc) (vstar + δ_loc))).congr_fun
        (fun v hv => (hgz v hv.2).symm) (measurableSet_Ioi.diff measurableSet_Ioc)
    have hint_ioi : IntegrableOn g (Ioi v₀) := by
      rw [← union_sdiff_cancel hsub_s]; exact hint_ioc.union hint_compl
    have hi_eq : ∫ v in Ioi v₀, ‖g v‖ = ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), ‖g v‖ := by
      have h1 : ∫ v in Ioi v₀, ‖g v‖ = ∫ v : ℝ, ‖g v‖ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
          rw [hgz v fun h => hv (hsub_s h), norm_zero]
      have h2 : ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), ‖g v‖ = ∫ v : ℝ, ‖g v‖ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
          rw [hgz v hv, norm_zero]
      rw [h1, h2]
    have hi_le : ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), ‖g v‖ ≤ 2 * δ_loc * M := by
      have h_c : IntegrableOn (fun _ : ℝ => M) (Ioc (vstar - δ_loc) (vstar + δ_loc)) :=
        integrableOn_const measure_Ioc_lt_top.ne
      calc ∫ v in Ioc (vstar - δ_loc) (vstar + δ_loc), ‖g v‖
          ≤ ∫ _ in Ioc (vstar - δ_loc) (vstar + δ_loc), M :=
            integral_mono_ae hint_ioc.norm h_c ((ae_restrict_mem measurableSet_Ioc).mono fun v _ => hgb v)
        _ = 2 * δ_loc * M := by
            rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith)]; ring
    exact ⟨hint_ioi, hi_eq ▸ hi_le⟩
  have hc_B : ContinuousOn B (Ici v₀) := fun v hv => (h_osc.hd1 v hv).continuousAt.continuousWithinAt
  have hsm_B : AEStronglyMeasurable B (volume.restrict (Ioi v₀)) :=
    (hc_B.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  have hsm_F1 : AEStronglyMeasurable F1 (volume.restrict (Ioi v₀)) := h_osc.i1.aestronglyMeasurable
  have hi_g1 := h_zero_bd_int (fun v => (-(χv1 v : ℝ) : ℂ) * B v) (K_χs * C0) (by positivity)
    (fun v hv => by rw [(hBR_supp v hv).2.1]; simp)
    (fun v => by
      by_cases hv : v ∈ Ioi v₀
      · rw [norm_mul]; exact mul_le_mul (hχ1_bd v) ((h_osc.b0 v hv.le).trans hC0') (norm_nonneg _) hKχs_pos.le
      · have hv' : v ∉ Ioc (vstar - δ_loc) (vstar + δ_loc) := fun h => hv (lt_of_le_of_lt hv_mδ h.1)
        rw [(hBR_supp v hv').2.1]; simp; positivity)
    ((continuous_neg.comp (Complex.continuous_ofReal.comp hχv1_cont)).aestronglyMeasurable.mul hsm_B)
  have hi_g2 := h_zero_bd_int (fun v => (-(χv2 v : ℝ) : ℂ) * B v) (K_χs * C0) (by positivity)
    (fun v hv => by rw [(hBR_supp v hv).2.2]; simp)
    (fun v => by
      by_cases hv : v ∈ Ioi v₀
      · rw [norm_mul]; exact mul_le_mul (hχ2_bd v) ((h_osc.b0 v hv.le).trans hC0') (norm_nonneg _) hKχs_pos.le
      · have hv' : v ∉ Ioc (vstar - δ_loc) (vstar + δ_loc) := fun h => hv (lt_of_le_of_lt hv_mδ h.1)
        rw [(hBR_supp v hv').2.2]; simp; positivity)
    ((continuous_neg.comp (Complex.continuous_ofReal.comp hχv2_cont)).aestronglyMeasurable.mul hsm_B)
  have hi_g3 := h_zero_bd_int (fun v => 2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)) (2 * (K_χs * C1)) (by positivity)
    (fun v hv => by rw [(hBR_supp v hv).2.1]; simp)
    (fun v => by
      by_cases hv : v ∈ Ioi v₀
      · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hχ1_bd v) ((h_osc.b1 v hv.le).trans hC1')
          (norm_nonneg _) hKχs_pos.le) zero_le_two
      · have hv' : v ∉ Ioc (vstar - δ_loc) (vstar + δ_loc) := fun h => hv (lt_of_le_of_lt hv_mδ h.1)
        rw [(hBR_supp v hv').2.1]; simp; positivity)
    (aestronglyMeasurable_const.mul ((continuous_neg.comp (Complex.continuous_ofReal.comp hχv1_cont)).aestronglyMeasurable.mul hsm_F1))
  have hi_1χF1 : IntegrableOn (fun v => ((1 : ℂ) - (χv v : ℂ)) * F1 v) (Ioi v₀) :=
    h_osc.i1.bdd_mul hc_1χ.aestronglyMeasurable (ae_of_all _ h1χ_bd)
  have hi_1χF2 : IntegrableOn (fun v => ((1 : ℂ) - (χv v : ℂ)) * F2 v) (Ioi v₀) :=
    h_osc.i2.bdd_mul hc_1χ.aestronglyMeasurable (ae_of_all _ h1χ_bd)
  have hi_BR1 : IntegrableOn BR1 (Ioi v₀) := hi_g1.1.add hi_1χF1
  have hi_BR2 : IntegrableOn BR2 (Ioi v₀) := (hi_g2.1.add hi_g3.1).add hi_1χF2
  let h_tail : OscAmpBound v₀ BR BR1 BR2 := {
    hd1 := fun v hv => (((hasDerivAt_const v (1 : ℂ)).sub (hχv_d1 v).ofReal_comp).mul (h_osc.hd1 v hv)).congr_deriv
      (by dsimp [BR1]; ring)
    hd2 := fun v hv => by
      have hd_pre : HasDerivAt (fun u => (-(χv1 u : ℝ) : ℂ)) (-(χv2 v : ℝ) : ℂ) v :=
        (((hχv_d2 v).ofReal_comp).neg).congr_deriv rfl
      have hd_c1 : HasDerivAt (fun u => (-(χv1 u : ℝ) : ℂ) * B u)
          ((-(χv2 v : ℝ) : ℂ) * B v + (-(χv1 v : ℝ) : ℂ) * F1 v) v :=
        hd_pre.mul (h_osc.hd1 v hv)
      have hd_c2 : HasDerivAt (fun u => ((1 : ℂ) - (χv u : ℂ)) * F1 u)
          ((-(χv1 v : ℝ) : ℂ) * F1 v + ((1 : ℂ) - (χv v : ℂ)) * F2 v) v :=
        ((((hasDerivAt_const v (1 : ℂ)).sub (hχv_d1 v).ofReal_comp).mul (h_osc.hd2 v hv))).congr_deriv
          (by simp only [Pi.sub_apply]; ring)
      exact (hd_c1.add hd_c2).congr_deriv (by dsimp [BR2]; ring)
    K0 := K0_R
    K1 := K1_R
    K2 := K2_R
    L1 := L1_R
    L2 := L2_R
    hK0 := by positivity
    hK1 := by positivity
    hK2 := by positivity
    hL1 := by positivity
    hL2 := by positivity
    b0 := fun v hv => by
      dsimp [BR]; rw [norm_mul]
      exact mul_le_mul (h1χ_bd v) ((h_osc.b0 v hv).trans hC0') (norm_nonneg _) (by positivity)
    b1 := fun v hv => by
      dsimp [BR1]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul (hχ1_bd v) ((h_osc.b0 v hv).trans hC0') (norm_nonneg _) hKχs_pos.le
      · rw [norm_mul]; exact mul_le_mul (h1χ_bd v) ((h_osc.b1 v hv).trans hC1') (norm_nonneg _) (by positivity)
    b2 := fun v hv => by
      dsimp [BR2]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_mul]; exact mul_le_mul (hχ2_bd v) ((h_osc.b0 v hv).trans hC0') (norm_nonneg _) hKχs_pos.le
      · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
        exact (mul_le_mul_of_nonneg_left (mul_le_mul (hχ1_bd v) ((h_osc.b1 v hv).trans hC1')
          (norm_nonneg _) hKχs_pos.le) zero_le_two).trans_eq (by ring)
      · rw [norm_mul]; exact mul_le_mul (h1χ_bd v) ((h_osc.b2 v hv).trans hC2') (norm_nonneg _) (by positivity)
    i1 := hi_BR1
    int1 := by
      have h1 : ∫ v in Ioi v₀, ‖BR1 v‖ ≤
          (∫ v in Ioi v₀, ‖(-(χv1 v : ℝ) : ℂ) * B v‖) + ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F1 v‖ := by
        calc ∫ v in Ioi v₀, ‖BR1 v‖
            ≤ ∫ v in Ioi v₀, (‖(-(χv1 v : ℝ) : ℂ) * B v‖ + ‖(1 - (χv v : ℂ)) * F1 v‖) :=
              integral_mono_ae hi_BR1.norm (hi_g1.1.norm.add hi_1χF1.norm)
                ((ae_restrict_mem measurableSet_Ioi).mono fun v _ => norm_add_le _ _)
          _ = (∫ v in Ioi v₀, ‖(-(χv1 v : ℝ) : ℂ) * B v‖) + ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F1 v‖ :=
              integral_add hi_g1.1.norm hi_1χF1.norm
      have h2 : ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F1 v‖ ≤ (1 + Kχ) * L1 := by
        calc ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F1 v‖
            ≤ ∫ v in Ioi v₀, (1 + Kχ) * ‖F1 v‖ :=
              integral_mono_ae hi_1χF1.norm (h_osc.i1.norm.const_mul (1 + Kχ))
                ((ae_restrict_mem measurableSet_Ioi).mono fun v _ => by
                  dsimp only; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h1χ_bd v) (norm_nonneg _))
          _ = (1 + Kχ) * ∫ v in Ioi v₀, ‖F1 v‖ := integral_const_mul _ _
          _ ≤ (1 + Kχ) * L1 := mul_le_mul_of_nonneg_left (h_osc.int1.trans hL1') (by positivity)
      dsimp [L1_R]; linarith [hi_g1.2]
    i2 := hi_BR2
    int2 := by
      have h1 : ∫ v in Ioi v₀, ‖BR2 v‖ ≤
          ((∫ v in Ioi v₀, ‖(-(χv2 v : ℝ) : ℂ) * B v‖) +
            ∫ v in Ioi v₀, ‖2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)‖) +
            ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F2 v‖ := by
        calc ∫ v in Ioi v₀, ‖BR2 v‖
            ≤ ∫ v in Ioi v₀, ((‖(-(χv2 v : ℝ) : ℂ) * B v‖ + ‖2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)‖) +
                ‖(1 - (χv v : ℂ)) * F2 v‖) :=
              integral_mono_ae hi_BR2.norm ((hi_g2.1.norm.add hi_g3.1.norm).add hi_1χF2.norm)
                ((ae_restrict_mem measurableSet_Ioi).mono fun v _ => by
                  dsimp only [BR2]
                  calc ‖(-(χv2 v : ℝ) : ℂ) * B v + 2 * ((-(χv1 v : ℝ) : ℂ) * F1 v) + (1 - (χv v : ℂ)) * F2 v‖
                      ≤ ‖(-(χv2 v : ℝ) : ℂ) * B v + 2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)‖ + ‖(1 - (χv v : ℂ)) * F2 v‖ :=
                        norm_add_le _ _
                    _ ≤ (‖(-(χv2 v : ℝ) : ℂ) * B v‖ + ‖2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)‖) + ‖(1 - (χv v : ℂ)) * F2 v‖ :=
                        add_le_add (norm_add_le _ _) le_rfl)
          _ = (∫ v in Ioi v₀, (‖(-(χv2 v : ℝ) : ℂ) * B v‖ + ‖2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)‖)) +
                ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F2 v‖ :=
              integral_add (hi_g2.1.norm.add hi_g3.1.norm) hi_1χF2.norm
          _ = ((∫ v in Ioi v₀, ‖(-(χv2 v : ℝ) : ℂ) * B v‖) +
                ∫ v in Ioi v₀, ‖2 * ((-(χv1 v : ℝ) : ℂ) * F1 v)‖) +
                ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F2 v‖ := by
              rw [integral_add hi_g2.1.norm hi_g3.1.norm]
      have h2 : ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F2 v‖ ≤ (1 + Kχ) * L2 := by
        calc ∫ v in Ioi v₀, ‖(1 - (χv v : ℂ)) * F2 v‖
            ≤ ∫ v in Ioi v₀, (1 + Kχ) * ‖F2 v‖ :=
              integral_mono_ae hi_1χF2.norm (h_osc.i2.norm.const_mul (1 + Kχ))
                ((ae_restrict_mem measurableSet_Ioi).mono fun v _ => by
                  dsimp only; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h1χ_bd v) (norm_nonneg _))
          _ = (1 + Kχ) * ∫ v in Ioi v₀, ‖F2 v‖ := integral_const_mul _ _
          _ ≤ (1 + Kχ) * L2 := mul_le_mul_of_nonneg_left (h_osc.int2.trans hL2') (by positivity)
      dsimp [L2_R]; linarith [hi_g2.2, hi_g3.2] }
  have hx_R : x' < edgeF v_R := by
    rw [← hx']
    exact edgeF_strictMonoOn (hv₀_pos.le.trans (hv_mδ.trans (by linarith : vstar - δ_loc ≤ vstar)))
      (hv₀_pos.le.trans hvR_ge) hvstar_R
  obtain ⟨ht_eq, _ht_int, ht_bd⟩ := phiDual_tail_ibp2 hv₀_pos hvR_ge hc'_pos hx_R h_tail hint_R
  have hδ_tail_le : δ_tail ≤ (4 * π / 3) * (edgeF v_R - x') := by
    have hsub := phiDual_edgeF_sub_ge hv₀_pos (hv_mδ.trans (by linarith)) hvstar_R.le
    rw [hx', hvR_eq] at hsub
    dsimp [δ_tail]; rw [hvR_eq]
    have h4 : 0 ≤ 4 * π / 3 := by positivity
    exact (mul_le_mul_of_nonneg_left hsub h4).trans_eq' (by ring)
  have hz1 : BR v_R = 0 := by dsimp [BR]; rw [hvR_in.1]; simp
  have hz2 : ibpH BR BR1 (fun v => (4 * π / 3) * (edgeF v - x')) (fun v => (4 * π / 3) * edgeF' v) v_R = 0 := by
    unfold ibpH; dsimp [BR, BR1]; rw [hvR_in.1, hvR_in.2]; simp
  change ‖∫ v in Ioi v_R, BR v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))‖ ≤ _
  rw [ht_eq, hz1, hz2]
  simp only [zero_div, zero_mul, mul_zero, zero_add, add_zero]
  rw [norm_mul, norm_pow]
  have hlam_norm : ‖(1 : ℂ) / (Complex.I * (c' : ℂ))‖ = c'⁻¹ := by
    rw [one_div, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc'_pos]
  rw [hlam_norm]
  have hci2 : (c'⁻¹) ^ 2 = c' ^ (-2 : ℝ) := by
    rw [← Real.rpow_neg_one c', ← Real.rpow_natCast, ← Real.rpow_mul hc'_pos.le]; norm_num
  rw [hci2, mul_comm (c' ^ (-2 : ℝ))]
  have hδt_pos : 0 < δ_tail := by dsimp [δ_tail]; have := edgeF'_pos hv₀_pos; positivity
  have hKχs_nn : 0 ≤ K_χs := hKχs_pos.le
  have hF'_pos := edgeF'_pos hv₀_pos
  have h_bd_tail : h_tail.L2 / ((4 * π / 3) * (edgeF v_R - x')) ^ 2 +
      (3 / 2 : ℝ) * h_tail.K1 / ((4 * π / 3) * (edgeF v_R - x')) ^ 2 +
      (1 / 2 : ℝ) * h_tail.K0 * ((2 * π) / edgeF' v₀) / ((4 * π / 3) * (edgeF v_R - x')) ^ 2 +
      (4 * π / 3) * h_tail.K0 / ((4 * π / 3) * (edgeF v_R - x')) ^ 3 ≤ C_tail := by
    change L2_R / ((4 * π / 3) * (edgeF v_R - x')) ^ 2 +
      (3 / 2 : ℝ) * K1_R / ((4 * π / 3) * (edgeF v_R - x')) ^ 2 +
      (1 / 2 : ℝ) * K0_R * ((2 * π) / edgeF' v₀) / ((4 * π / 3) * (edgeF v_R - x')) ^ 2 +
      (4 * π / 3) * K0_R / ((4 * π / 3) * (edgeF v_R - x')) ^ 3 ≤ _
    have hL2_nn : 0 ≤ L2_R := by dsimp [L2_R]; positivity
    have hK1_nn : 0 ≤ K1_R := by dsimp [K1_R]; positivity
    have hK0_nn : 0 ≤ K0_R := by dsimp [K0_R]; positivity
    dsimp [C_tail]
    gcongr
  exact mul_le_mul_of_nonneg_right (ht_bd.trans h_bd_tail) (by positivity)

private lemma kedge_outer_combine {c' M0 C_sm C_out C_tail C_sp : ℝ}
    (hc'_1 : 1 ≤ c') (hCout : 0 ≤ C_out) (hCtail : 0 ≤ C_tail)
    {I_all I_sp I_rem I_sm I_left I_tail L : ℂ}
    (hI : I_all = I_rem + I_sp) (hRem : I_rem = I_sm + I_left + I_tail)
    (h_sm : ‖I_sm‖ ≤ (2 / 3 : ℝ) * M0 * c' ^ (-(3 / 2 : ℝ)))
    (h_left : ‖I_left‖ ≤ C_sm * c' ^ (-(3 / 2 : ℝ)) + C_out * c' ^ (-2 : ℝ))
    (h_tail : ‖I_tail‖ ≤ C_tail * c' ^ (-2 : ℝ))
    (h_sp : ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * I_sp - L‖ ≤ √(2 / 3) * C_sp / c') :
    ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * I_all - L‖ ≤
      √(2 / 3) * ((2 / 3) * M0 + C_sm + C_out + C_sp + C_tail) / c' := by
  have hc'_pos : 0 < c' := by linarith
  have hpi := Real.pi_pos
  have hcm2 : c' ^ (-2 : ℝ) ≤ c' ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc'_1 (by norm_num)
  have hb_out' : (C_out + C_tail) * c' ^ (-2 : ℝ) ≤ (C_out + C_tail) * c' ^ (-(3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hcm2 (add_nonneg hCout hCtail)
  have hrem_tot : ‖I_rem‖ ≤ ((2 / 3) * M0 + C_sm + C_out + C_tail) * c' ^ (-(3 / 2 : ℝ)) := by
    rw [hRem]
    calc ‖I_sm + I_left + I_tail‖
        ≤ (‖I_sm‖ + ‖I_left‖) + ‖I_tail‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((2 / 3 : ℝ) * M0 * c' ^ (-(3 / 2 : ℝ)) + (C_sm * c' ^ (-(3 / 2 : ℝ)) + C_out * c' ^ (-2 : ℝ))) +
            C_tail * c' ^ (-2 : ℝ) := add_le_add (add_le_add h_sm h_left) h_tail
      _ = ((2 / 3) * M0 + C_sm) * c' ^ (-(3 / 2 : ℝ)) + (C_out + C_tail) * c' ^ (-2 : ℝ) := by ring
      _ ≤ ((2 / 3) * M0 + C_sm) * c' ^ (-(3 / 2 : ℝ)) + (C_out + C_tail) * c' ^ (-(3 / 2 : ℝ)) :=
          add_le_add le_rfl hb_out'
      _ = ((2 / 3) * M0 + C_sm + C_out + C_tail) * c' ^ (-(3 / 2 : ℝ)) := by ring
  have hrem_pref : ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * I_rem‖ ≤
      √(2 / 3) * ((2 / 3) * M0 + C_sm + C_out + C_tail) / c' := by
    rw [norm_mul, norm_mul]
    have h1 : ‖(√(2 * c' / 3) : ℂ)‖ = √(2 / 3) * √c' := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        show 2 * c' / 3 = (2 / 3) * c' by ring, Real.sqrt_mul (by norm_num)]
    have h2 : ‖Complex.exp (Complex.I * (π : ℂ) / 4)‖ = 1 := by
      rw [show Complex.I * (π : ℂ) / 4 = ((π / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [h1, h2, mul_one]
    have hprod : √c' * c' ^ (-(3 / 2 : ℝ)) = c'⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc'_pos, ← Real.rpow_neg_one c']; norm_num
    calc (√(2 / 3) * √c') * ‖I_rem‖
        ≤ (√(2 / 3) * √c') * (((2 / 3) * M0 + C_sm + C_out + C_tail) * c' ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hrem_tot (by positivity)
      _ = √(2 / 3) * ((2 / 3) * M0 + C_sm + C_out + C_tail) * (√c' * c' ^ (-(3 / 2 : ℝ))) := by ring
      _ = √(2 / 3) * ((2 / 3) * M0 + C_sm + C_out + C_tail) / c' := by rw [hprod, ← div_eq_mul_inv]
  have htot_eq : √(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * I_all - L =
      √(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * I_rem +
        (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) * I_sp - L) := by
    rw [hI]; ring
  rw [htot_eq]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hrem_pref h_sp).trans_eq ?_
  ring

private lemma virasoro_kedge_outer_kernel_asymp {δ_hi : ℝ} (hδ_hi : 0 < δ_hi)
    {M0 M1 M2 K_B C0 C1 C2 L1 L2 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hKB : 0 ≤ K_B) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2)
    (B : ℝ → ℝ → ℂ)
    (hB_sm : ∀ {ε}, ε ∈ Ioo (0 : ℝ) (1 / 2) → ∃ B1 B2 : ℝ → ℂ,
      (∀ v ∈ Ioc (0 : ℝ) (vTip (xiStar + δ_hi) / 2), HasDerivAt (B ε) (B1 v) v ∧ HasDerivAt B1 (B2 v) v) ∧
      ContinuousOn B2 (Ioc (0 : ℝ) (vTip (xiStar + δ_hi) / 2)) ∧
      (∀ v ∈ Ioc (0 : ℝ) (vTip (xiStar + δ_hi) / 2),
        ‖B ε v‖ ≤ M0 * v ^ (1 / 2 : ℝ) ∧ ‖B1 v‖ ≤ M1 * v ^ (-(1 / 2 : ℝ)) ∧
        ‖B2 v‖ ≤ M2 * v ^ (-(3 / 2 : ℝ))))
    (hB_lg : ∀ {ε}, ε ∈ Ioo (0 : ℝ) (1 / 2) → ∃ B1 B2 : ℝ → ℂ,
      D2 (Ici (vTip (xiStar + δ_hi) / 2)) (B ε) B1 B2 K_B)
    (hB_osc : ∀ {ε}, ε ∈ Ioo (0 : ℝ) (1 / 2) → ∃ F1 F2 : ℝ → ℂ,
      ∃ h : OscAmpBound (vTip (xiStar + δ_hi) / 2) (B ε) F1 F2, h.HasConsts C0 C1 C2 L1 L2)
    (hB_int : ∀ {c' ε x' : ℝ}, 1 ≤ c' → ε ∈ Ioo (0 : ℝ) (1 / 2) → xiStar + δ_hi ≤ x' →
      IntegrableOn (fun v => B ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi 0)) :
    ∃ c₀ C_ker : ℝ, 1 ≤ c₀ ∧ 0 ≤ C_ker ∧
      ∀ {c' ε x' : ℝ}, c₀ ≤ c' → ε ∈ Ioo (0 : ℝ) (1 / 2) → xiStar + δ_hi ≤ x' →
        ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
            (∫ v in Ioi (0 : ℝ), B ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) -
          Complex.I / (√(edgeF' (vTip x')) : ℂ) * B ε (vTip x') *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))‖ ≤ C_ker / c' := by
  have hpi := Real.pi_pos
  let v_min := vTip (xiStar + δ_hi)
  have hv_min_pos : 0 < v_min := vTip_pos (by linarith [xiStar_pos])
  let v₀ := v_min / 2
  have hv₀_pos : 0 < v₀ := half_pos hv_min_pos
  let δ_loc := min (v_min / 4) (1 / 2)
  have hδ_pos : 0 < δ_loc := lt_min (by positivity) (by norm_num)
  have hδ1 : δ_loc ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδ_vm : δ_loc ≤ v_min / 4 := min_le_left _ _
  let c_ph := (4 * π / 3) * edgeF' v₀
  have hc_ph : 0 < c_ph := mul_pos (by positivity) (edgeF'_pos hv₀_pos)
  let C_ph := (4 * π / 3) * (1 + 8 * π + 16 * π ^ 2)
  obtain ⟨θ, K_sp, hθ0, hθ1, hKsp0, hsp⟩ := stat_phase c_ph C_ph hc_ph
  obtain ⟨χ, χ1, χ2, Kχ, hKχ_pos, hdχ1, hdχ2, hχ_D2, hχ_one, hχ_zero⟩ := cutoff_D2_global hθ0
  let δ_mid := (4 * π / 3) * (edgeF v_min - edgeF v₀)
  have hδ_mid_pos : 0 < δ_mid := mul_pos (by positivity)
    (sub_pos.mpr (edgeF_strictMonoOn hv₀_pos.le hv_min_pos.le (by dsimp [v₀]; linarith)))
  let c₀ : ℝ := max 1 (max (2 / v₀) (δ_loc ^ (-2 : ℝ)))
  have hc₀_ge : 1 ≤ c₀ := le_max_left _ _
  let η : ℝ := (θ / 4) * δ_loc
  have hη_pos : 0 < η := by positivity
  let C_sm : ℝ := outerCsm M0 M1 M2 δ_mid v₀
  let C_out : ℝ := outerCout Kχ K_B δ_loc θ v₀
  let C_sp : ℝ := K_sp * (4 * Kχ * K_B) / δ_loc ^ 2
  let C_tail : ℝ := outerCtail Kχ δ_loc θ v₀ C0 C1 L2
  let C_ker : ℝ := √(2 / 3) * ((2 / 3) * M0 + C_sm + C_out + C_sp + C_tail)
  have hCsm : 0 ≤ C_sm := outerCsm_nonneg hM0 hM1 hM2 hδ_mid_pos hv₀_pos
  have hCout : 0 ≤ C_out := outerCout_nonneg hKχ_pos hKB hδ_pos hθ0 hv₀_pos
  have hCsp : 0 ≤ C_sp := div_nonneg (mul_nonneg hKsp0 (mul_nonneg (mul_nonneg (by norm_num) hKχ_pos.le) hKB)) (sq_nonneg _)
  have hCtail : 0 ≤ C_tail := outerCtail_nonneg hKχ_pos hδ_pos hθ0 hv₀_pos hC0 hC1 hL2
  have hC_ker_nn : 0 ≤ C_ker :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) hM0) hCsm) hCout) hCsp) hCtail)
  refine ⟨c₀, C_ker, hc₀_ge, hC_ker_nn, fun {c' ε x'} hc' hε hx' => ?_⟩
  have hc'_1 : 1 ≤ c' := hc₀_ge.trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hx_gt : xiStar < x' := lt_of_lt_of_le (by linarith [xiStar_pos]) hx'
  let vstar := vTip x'
  have hvstar_ge : v_min ≤ vstar := vTip_ge_of_ge (by linarith [xiStar_pos]) hx'
  have hvstar_F : edgeF vstar = x' := edgeF_vTip hx_gt.le
  let v_s := c'⁻¹
  have hvs_pos : 0 < v_s := inv_pos.mpr hc'_pos
  have hvs_le : v_s ≤ v₀ := by
    have h2 : 2 / v₀ ≤ c' := (le_max_left _ _).trans ((le_max_right 1 _).trans hc')
    calc v_s = c'⁻¹ := rfl
      _ ≤ (2 / v₀)⁻¹ := inv_anti₀ (by positivity) h2
      _ = v₀ / 2 := by field_simp
      _ ≤ v₀ := by linarith
  let v_L := vstar - η
  let v_R := vstar + η
  have hv₀_vL : v₀ ≤ v_L := by dsimp [v_L, η, v₀]; nlinarith [hδ_vm, hθ1]
  have hvL_vs : v_L < vstar := by linarith
  have hvs_vR : vstar < v_R := by linarith
  have hvR_ge : v₀ ≤ v_R := hv₀_vL.trans (hvL_vs.le.trans hvs_vR.le)
  have hv_mδ : v₀ ≤ vstar - δ_loc := by dsimp [v₀]; nlinarith [hδ_vm]
  have hlam_ge : 1 ≤ c' * δ_loc ^ 2 := by
    have h1 : δ_loc ^ (-2 : ℝ) ≤ c' := (le_max_right _ _).trans ((le_max_right 1 _).trans hc')
    have h2 : (δ_loc ^ 2)⁻¹ = δ_loc ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, Real.rpow_neg hδ_pos.le]; norm_num
    rw [← h2] at h1
    calc (1 : ℝ) = (δ_loc ^ 2)⁻¹ * δ_loc ^ 2 := (inv_mul_cancel₀ (pow_ne_zero 2 hδ_pos.ne')).symm
      _ ≤ c' * δ_loc ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  obtain ⟨Bs1, Bs2, hBs_d, hBs_c, hBs_bd⟩ := hB_sm hε
  obtain ⟨Bl1, Bl2, hBl⟩ := hB_lg hε
  obtain ⟨F1, F2, h_osc, hconsts⟩ := hB_osc hε
  let χv := fun v : ℝ => χ ((v - vstar) / δ_loc)
  let e : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))
  have hB_i := hB_int hc'_1 hε hx'
  obtain ⟨hχBs_int, hsp_err⟩ := kedge_outer_sp_part hv₀_pos hδ_pos hδ1 hv_mδ hθ0 hθ1 hKsp0 hKχ_pos hKB
    hc'_pos hlam_ge hx_gt hvstar_F hsp hχ_D2 hχ_one hχ_zero hBl hB_i
  let remF : ℝ → ℂ := fun v => (1 - (χv v : ℂ)) * B ε v * e v
  have hrem_int : IntegrableOn remF (Ioi 0) :=
    (hB_i.sub hχBs_int).congr_fun (fun v _ => by dsimp [remF, e]; ring) measurableSet_Ioi
  have hB_split : ∫ v in Ioi (0 : ℝ), B ε v * e v =
      (∫ v in Ioi (0 : ℝ), remF v) + ∫ v in Ioi (0 : ℝ), (χv v : ℂ) * B ε v * e v := by
    rw [← integral_add hrem_int hχBs_int]
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => by dsimp [remF, e]; ring
  have hχv_zero_left : ∀ v ≤ v₀, χv v = 0 := fun v hv => by
    apply (hχ_zero ((v - vstar) / δ_loc) _).1
    rw [abs_div, abs_of_pos hδ_pos, le_div_iff₀ hδ_pos, abs_of_neg (by linarith [hv_mδ, hδ_pos])]
    exact (mul_le_of_le_one_left hδ_pos.le hθ1.le).trans (by linarith [hv_mδ])
  have hrem_mid_zero : ∫ v in Ioc v_L v_R, remF v = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    have h1 : |v - vstar| ≤ (θ / 2) * δ_loc := by
      have hη_le : η ≤ (θ / 2) * δ_loc := by
        show (θ / 4) * δ_loc ≤ (θ / 2) * δ_loc
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hθ0.le (by norm_num) (by norm_num)) hδ_pos.le
      have h1 : -η ≤ v - vstar := by
        have hv1 : vstar - η ≤ v := hv.1.le
        show -η ≤ v - vstar; linarith only [hv1]
      have h2 : v - vstar ≤ η := by
        have hv2 : v ≤ vstar + η := hv.2
        show v - vstar ≤ η; linarith only [hv2]
      rw [abs_le]; exact ⟨(neg_le_neg hη_le).trans h1, h2.trans hη_le⟩
    have h2 : |(v - vstar) / δ_loc| ≤ θ / 2 := by
      rw [abs_div, abs_of_pos hδ_pos, div_le_iff₀ hδ_pos]; exact h1
    have hχ1 : χv v = 1 := hχ_one _ h2
    show remF v = 0
    change (1 - (χv v : ℂ)) * B ε v * e v = 0
    rw [hχ1]; simp
  have hrem_split : ∫ v in Ioi (0 : ℝ), remF v =
      (∫ v in Ioc (0 : ℝ) v_s, remF v) +
      ((∫ v in v_s..v₀, B ε v * e v) + ∫ v in v₀..v_L, remF v) +
      ∫ v in Ioi v_R, remF v := by
    have hs1 : Ioi (0 : ℝ) = Ioc 0 v_R ∪ Ioi v_R := (Ioc_union_Ioi_eq_Ioi (lt_of_lt_of_le hv₀_pos hvR_ge).le).symm
    have hs2 : Ioc (0 : ℝ) v_R = Ioc 0 v_L ∪ Ioc v_L v_R :=
      (Ioc_union_Ioc_eq_Ioc (hv₀_pos.le.trans hv₀_vL) (hvL_vs.le.trans hvs_vR.le)).symm
    have hs3 : Ioc (0 : ℝ) v_L = Ioc 0 v₀ ∪ Ioc v₀ v_L :=
      (Ioc_union_Ioc_eq_Ioc hv₀_pos.le hv₀_vL).symm
    have hs4 : Ioc (0 : ℝ) v₀ = Ioc 0 v_s ∪ Ioc v_s v₀ :=
      (Ioc_union_Ioc_eq_Ioc hvs_pos.le hvs_le).symm
    have hi_vs : IntegrableOn remF (Ioc 0 v_s) := hrem_int.mono_set Ioc_subset_Ioi_self
    have hi_v0 : IntegrableOn remF (Ioc 0 v₀) := hrem_int.mono_set Ioc_subset_Ioi_self
    have hi_vs0 : IntegrableOn remF (Ioc v_s v₀) := hrem_int.mono_set fun _ h => hvs_pos.trans h.1
    have hi_v0L : IntegrableOn remF (Ioc v₀ v_L) := hrem_int.mono_set fun _ h => hv₀_pos.trans h.1
    have hi_LR : IntegrableOn remF (Ioc v_L v_R) := hrem_int.mono_set fun _ h => (hv₀_pos.trans_le hv₀_vL).trans h.1
    have hi_R : IntegrableOn remF (Ioi v_R) := hrem_int.mono_set fun _ h => (lt_of_lt_of_le hv₀_pos hvR_ge).trans h
    have hi_0R : IntegrableOn remF (Ioc 0 v_R) := hrem_int.mono_set Ioc_subset_Ioi_self
    have hi_0L : IntegrableOn remF (Ioc 0 v_L) := hrem_int.mono_set Ioc_subset_Ioi_self
    have h1 : ∫ v in Ioi (0 : ℝ), remF v = (∫ v in Ioc 0 v_R, remF v) + ∫ v in Ioi v_R, remF v := by
      rw [hs1]; exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi_0R hi_R
    have h2 : ∫ v in Ioc (0 : ℝ) v_R, remF v = (∫ v in Ioc 0 v_L, remF v) + ∫ v in Ioc v_L v_R, remF v := by
      rw [hs2]; exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi_0L hi_LR
    have h3 : ∫ v in Ioc (0 : ℝ) v_L, remF v = (∫ v in Ioc 0 v₀, remF v) + ∫ v in Ioc v₀ v_L, remF v := by
      rw [hs3]; exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi_v0 hi_v0L
    have h4 : ∫ v in Ioc (0 : ℝ) v₀, remF v = (∫ v in Ioc 0 v_s, remF v) + ∫ v in Ioc v_s v₀, remF v := by
      rw [hs4]; exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi_vs hi_vs0
    have h_mid_eq : ∫ v in Ioc v_s v₀, remF v = ∫ v in v_s..v₀, B ε v * e v := by
      rw [intervalIntegral.integral_of_le hvs_le]
      refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
      dsimp [remF]; rw [hχv_zero_left v hv.2]; simp
    rw [h1, h2, hrem_mid_zero, add_zero, h3, h4, h_mid_eq, ← intervalIntegral.integral_of_le hv₀_vL]
    ring
  have hb_sm : ‖∫ v in Ioc (0 : ℝ) v_s, remF v‖ ≤ (2 / 3 : ℝ) * M0 * c' ^ (-(3 / 2 : ℝ)) := by
    have h_eq : ∫ v in Ioc (0 : ℝ) v_s, remF v = ∫ v in Ioc (0 : ℝ) v_s, B ε v * e v := by
      refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
      dsimp [remF]; rw [hχv_zero_left v (hv.2.trans hvs_le)]; simp
    rw [h_eq]
    refine (kedge_small_region_bound hvs_pos hM0 fun v hv => (hBs_bd v ⟨hv.1, hv.2.trans hvs_le⟩).1).trans_eq ?_
    rw [show v_s = c'⁻¹ from rfl, ← Real.rpow_neg_one c', ← Real.rpow_mul hc'_pos.le]; norm_num
  have hδ_mid_cond : ∀ v ∈ Icc v_s v₀, δ_mid ≤ (4 * π / 3) * (x' - edgeF v) := fun v hv => by
    have hFv : edgeF v ≤ edgeF v₀ := by
      rcases hv.2.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (edgeF_strictMonoOn (hvs_pos.le.trans hv.1) hv₀_pos.le hlt).le
    have hFmin : edgeF v_min ≤ x' := by
      rw [← hvstar_F]
      rcases hvstar_ge.eq_or_lt with h | hlt
      · rw [h]
      · exact (edgeF_strictMonoOn hv_min_pos.le (hv_min_pos.le.trans hvstar_ge) hlt).le
    exact mul_le_mul_of_nonneg_left (sub_le_sub hFmin hFv) (by positivity)
  have hb_left := kedge_outer_left_part hvs_pos hvs_le hv₀_pos hv₀_vL hvL_vs hδ_pos hδ1 hv_mδ hθ0 hθ1 rfl
    hKχ_pos hKB hM0 hM1 hM2 hδ_mid_pos hc'_1 rfl hvstar_F hδ_mid_cond hdχ1 hdχ2 hχ_D2 hχ_one hχ_zero
    hBs_d hBs_c hBs_bd hBl
  have hint_R : IntegrableOn remF (Ioi v_R) := hrem_int.mono_set fun _ h => (lt_of_lt_of_le hv₀_pos hvR_ge).trans h
  have hb_tail := kedge_outer_tail_part hv₀_pos hvR_ge hv_mδ hvs_vR hδ_pos hδ1 hθ0 hθ1 rfl
    hKχ_pos hC0 hC1 hC2 hL1 hL2 hc'_pos hvstar_F hdχ1 hdχ2 hχ_D2 hχ_one hχ_zero h_osc hconsts hint_R
  exact kedge_outer_combine (C_sm := C_sm) (C_out := C_out) (C_tail := C_tail) (C_sp := C_sp)
    hc'_1 hCout hCtail hB_split hrem_split hb_sm hb_left hb_tail hsp_err

/-- **`cts:Kedge-outer` (`virasoro_kedge_outer_of_delta`)**: for any fixed `δ_hi > 0`, uniformly for
`ε ∈ Ioo 0 (1 / 2)` and `x' ≥ xiStar + δ_hi`, `virasoroKedgeEps c' ε x'` matches
`lowerWeps ε (lowerY x') * Real.sin (lowerThetaEps Gout ε (lowerY x') - 2 * π * c' * cumulN x')`
up to `O(c'⁻¹)` and `virasoroKedge1Eps c' ε x'` is uniformly bounded `O(1)`. -/
theorem virasoro_kedge_outer_of_delta {δ_hi : ℝ} (hδ_hi : 0 < δ_hi) :
    ∃ c₀ C_k : ℝ, 1 ≤ c₀ ∧ 0 ≤ C_k ∧
      ∀ {c' ε x' : ℝ}, c₀ ≤ c' → ε ∈ Ioo (0 : ℝ) (1 / 2) → xiStar + δ_hi ≤ x' →
        |virasoroKedgeEps c' ε x' -
            lowerWeps ε (lowerY x') * Real.sin (lowerThetaEps Gout ε (lowerY x') - 2 * π * c' * cumulN x')| ≤
          C_k / c' ∧
        |virasoroKedge1Eps c' ε x'| ≤ C_k := by
  have hpi := Real.pi_pos
  let v_min := vTip (xiStar + δ_hi)
  have hv_min_pos : 0 < v_min := vTip_pos (by linarith [xiStar_pos])
  let v₀ := v_min / 2
  have hv₀_pos : 0 < v₀ := half_pos hv_min_pos
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hsm⟩ := kedgeAmp0_small_v_bounds hv₀_pos
  obtain ⟨K0, K1, hK0, hK1, hlg⟩ := kedgeAmp0_D2_of_ge hv₀_pos
  obtain ⟨⟨C0_0, C1_0, C2_0, L1_0, L2_0, hC00, hC10, hC20, hL10, hL20, hosc0⟩,
          ⟨C0_1, C1_1, C2_1, L1_1, L2_1, hC01, hC11, hC21, hL11, hL21, hosc1⟩⟩ :=
    virasoro_geps_deriv hv₀_pos
  have hint0 : ∀ {c' ε x' : ℝ}, 1 ≤ c' → ε ∈ Ioo (0 : ℝ) (1 / 2) → xiStar + δ_hi ≤ x' →
      IntegrableOn (fun v => kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi 0) := by
    intro c' ε x' _ hε hx'
    have hx2 : xiStar / 2 ≤ x' := by linarith [xiStar_pos]
    have hi := (kedgeEps_integrable_and_tau_eq c' hε hx2).1
    let Ex : ℝ := (1 - Real.exp (-(4 * π * x'))) ^ 2
    have hEx_pos : 0 < Ex := by
      dsimp [Ex]; rw [sq_pos_iff, sub_ne_zero]; exact (Real.exp_lt_one_iff.mpr (by nlinarith [xiStar_pos])).ne'
    have hmul : ∀ v : ℝ, (Ex : ℂ) * kedgeEpsIntegrand c' ε x' v =
        kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := fun v => by
      have hbase_ne : 1 - Real.exp (-(4 * π * x')) ≠ 0 :=
        sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [xiStar_pos])).ne'
      have hmul_id : (Ex : ℂ) * (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
          √(edgeF' v) : ℝ) : ℂ) = (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]; congr 1; dsimp [Ex]; field_simp [hbase_ne]
      unfold kedgeEpsIntegrand kedgeAmp0
      calc (Ex : ℂ) * (lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
              Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
              (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) : ℝ) : ℂ) *
              Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))
          = lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
              Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
              ((Ex : ℂ) * (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) : ℝ) : ℂ)) *
              Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by ring
        _ = _ := by rw [hmul_id]
    have hi_c : IntegrableOn (fun v => (Ex : ℂ) * kedgeEpsIntegrand c' ε x' v) (Ioi 0) := hi.const_mul (Ex : ℂ)
    exact hi_c.congr_fun (fun v _ => hmul v) measurableSet_Ioi
  have hint1 : ∀ {c' ε x' : ℝ}, 1 ≤ c' → ε ∈ Ioo (0 : ℝ) (1 / 2) → xiStar + δ_hi ≤ x' →
      IntegrableOn (fun v => kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) (Ioi 0) := by
    intro c' ε x' _ hε hx'
    have hx2 : xiStar / 2 ≤ x' := by linarith [xiStar_pos]
    have hi := (kedgeEps_integrable_and_tau_eq c' hε hx2).2.1
    let Ex : ℝ := (1 - Real.exp (-(4 * π * x'))) ^ 2
    have hEx_pos : 0 < Ex := by
      dsimp [Ex]; rw [sq_pos_iff, sub_ne_zero]; exact (Real.exp_lt_one_iff.mpr (by nlinarith [xiStar_pos])).ne'
    have hmul : ∀ v : ℝ, (Ex : ℂ) * (kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹) =
        kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := fun v => by
      have hbase_ne : 1 - Real.exp (-(4 * π * x')) ≠ 0 :=
        sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [xiStar_pos])).ne'
      have hmul_id : (Ex : ℂ) * (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
          √(edgeF' v) : ℝ) : ℂ) = (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]; congr 1; dsimp [Ex]; field_simp [hbase_ne]
      unfold kedgeEpsIntegrand kedgeAmp0Aux kedgeAmp0
      calc (Ex : ℂ) * (lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
              Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
              (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) : ℝ) : ℂ) *
              Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) *
              ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹)
          = lowerMt ε (Complex.I * (lowerY (edgeF v) : ℂ)) ^ 2 *
              Complex.exp (Complex.I * (thetaOut (lowerY (edgeF v)) : ℂ)) *
              ((Ex : ℂ) * (((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' v) : ℝ) : ℂ)) *
              Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) *
              ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹ := by ring
        _ = _ := by rw [hmul_id]; ring
    have hi_c : IntegrableOn (fun v => (Ex : ℂ) * (kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹)) (Ioi 0) :=
      hi.const_mul (Ex : ℂ)
    exact hi_c.congr_fun (fun v _ => hmul v) measurableSet_Ioi
  obtain ⟨c0_0, C_ker0, hc0_0, hCk0, hker0⟩ := virasoro_kedge_outer_kernel_asymp hδ_hi hM0 hM1 hM2
    hK0.le hC00 hC10 hC20 hL10 hL20 kedgeAmp0
    (fun {ε} hε => (hsm hε).1) (fun {ε} hε => (hlg hε).1) (fun {ε} hε => hosc0 hε) hint0
  obtain ⟨c0_1, C_ker1, hc0_1, hCk1, hker1⟩ := virasoro_kedge_outer_kernel_asymp hδ_hi hM0 hM1 hM2
    hK1.le hC01 hC11 hC21 hL11 hL21 kedgeAmp0Aux
    (fun {ε} hε => (hsm hε).2) (fun {ε} hε => (hlg hε).2) (fun {ε} hε => hosc1 hε) hint1
  let E_min : ℝ := (1 - Real.exp (-(4 * π * xiStar))) ^ 2
  have hE_min_pos : 0 < E_min := by
    dsimp [E_min]; rw [sq_pos_iff, sub_ne_zero]; exact (Real.exp_lt_one_iff.mpr (by nlinarith [xiStar_pos])).ne'
  let c₀ : ℝ := max c0_0 c0_1
  let C_k : ℝ := E_min⁻¹ * max C_ker0 (K1 / √(edgeF' v₀) + C_ker1)
  refine ⟨c₀, C_k, le_max_of_le_left hc0_0, by positivity, fun {c' ε x'} hc' hε hx' => ?_⟩
  have hc'_1 : 1 ≤ c' := (le_max_of_le_left hc0_0).trans hc'
  have hx_gt : xiStar < x' := lt_of_lt_of_le (by linarith [xiStar_pos]) hx'
  let Ex : ℝ := (1 - Real.exp (-(4 * π * x'))) ^ 2
  have hEx_ge : E_min ≤ Ex := by
    have h1 : Real.exp (-(4 * π * x')) ≤ Real.exp (-(4 * π * xiStar)) :=
      Real.exp_le_exp.mpr (by nlinarith [hx_gt])
    have h2 : 1 - Real.exp (-(4 * π * xiStar)) ≤ 1 - Real.exp (-(4 * π * x')) := by linarith
    have hnn : 0 ≤ 1 - Real.exp (-(4 * π * xiStar)) := by
      rw [sub_nonneg]; exact Real.exp_le_one_iff.mpr (by nlinarith [xiStar_pos])
    exact pow_le_pow_left₀ hnn h2 2
  have hEx_pos : 0 < Ex := hE_min_pos.trans_le hEx_ge
  have hEx_inv : Ex⁻¹ ≤ E_min⁻¹ := inv_anti₀ hE_min_pos hEx_ge
  let vstar := vTip x'
  have hvstar_ge : v₀ ≤ vstar := (by dsimp [v₀]; linarith : v₀ ≤ v_min).trans (vTip_ge_of_ge (by linarith [xiStar_pos]) hx')
  have hvstar_F : edgeF vstar = x' := edgeF_vTip hx_gt.le
  have hF'_v : edgeF' v₀ ≤ edgeF' vstar := (edgeF_deriv_bounds_of_ge hv₀_pos hvstar_ge).1
  have hF'_pos : 0 < edgeF' vstar := (edgeF'_pos hv₀_pos).trans_le hF'_v
  have hk0 := hker0 ((le_max_left _ _).trans hc') hε hx'
  have hk1 := hker1 ((le_max_right _ _).trans hc') hε hx'
  refine ⟨?_, ?_⟩
  · have h_ke : virasoroKedgeEps c' ε x' = -((Ex⁻¹ : ℂ) * (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re := by
      unfold virasoroKedgeEps
      have h_in : ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v =
          ((Ex⁻¹ : ℝ) : ℂ) * ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        have hdiv : ((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
            √(edgeF' v) : ℝ) = Ex⁻¹ * ((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v)) := by
          change _ / Ex * _ = _; ring
        unfold kedgeEpsIntegrand kedgeAmp0
        rw [hdiv, Complex.ofReal_mul]; ring
      rw [h_in]
      calc -√(2 * c' / 3) *
              (Complex.exp (Complex.I * (π : ℂ) / 4) *
                (((Ex⁻¹ : ℝ) : ℂ) * ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re
          = -(((√(2 * c' / 3) : ℝ) : ℂ) *
                (Complex.exp (Complex.I * (π : ℂ) / 4) *
                  (((Ex⁻¹ : ℝ) : ℂ) * ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))))).re := by
              rw [Complex.re_ofReal_mul]; ring
        _ = -((Ex⁻¹ : ℂ) * (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
                ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re := by
              congr 2; push_cast; ring
    have h_lead : -((Ex⁻¹ : ℂ) * (Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0 ε vstar *
          Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)))).re =
        lowerWeps ε (lowerY x') * Real.sin (lowerThetaEps Gout ε (lowerY x') - 2 * π * c' * cumulN x') := by
      have hK0_v : (Ex⁻¹ : ℂ) * (Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0 ε vstar) =
          Complex.I * (lowerMt ε (Complex.I * (lowerY x' : ℂ)) ^ 2 *
            Complex.exp (Complex.I * (thetaOut (lowerY x') : ℂ))) := by
        unfold kedgeAmp0
        rw [hvstar_F]
        have hF_rw : ((1 - Real.exp (-(4 * π * x'))) ^ 2 * √(edgeF' vstar) : ℝ) = Ex * √(edgeF' vstar) := rfl
        rw [hF_rw, Complex.ofReal_mul]
        have hs_ne : (√(edgeF' vstar) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hF'_pos).ne'
        have hex_ne : (Ex : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hEx_pos.ne'
        field_simp [hs_ne, hex_ne]
      have hy_mem : lowerY x' ∈ Ioo (0 : ℝ) 1 := yOfX_mem hx_gt
      have hG_polar := gout_polar hy_mem
      have hW_pos : 0 < Wslit (lowerY x') := Wslit_pos' hy_mem
      have hexp_G : Complex.exp (Complex.I * (thetaOut (lowerY x') : ℂ)) =
          Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ)) := by
        have hnorm : ‖Gout (Complex.I * (lowerY x' : ℂ))‖ = Wslit (lowerY x') := by
          rw [hG_polar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW_pos,
            mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
        have h1 := Complex.norm_mul_exp_arg_mul_I (Gout (Complex.I * (lowerY x' : ℂ)))
        rw [hnorm] at h1
        nth_rewrite 2 [hG_polar] at h1
        have h1' : ((Wslit (lowerY x') : ℝ) : ℂ) *
            Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ)) =
            ((Wslit (lowerY x') : ℝ) : ℂ) * Complex.exp (Complex.I * (thetaOut (lowerY x') : ℂ)) := by
          rwa [mul_comm Complex.I (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ)]
        exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hW_pos.ne') h1').symm
      have hmt_polar : lowerMt ε (Complex.I * (lowerY x' : ℂ)) ^ 2 =
          ((lowerWeps ε (lowerY x') : ℝ) : ℂ) *
            Complex.exp (Complex.I * (2 * Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ)) := by
        have h1 : lowerMt ε (Complex.I * (lowerY x' : ℂ)) =
            ((‖lowerMt ε (Complex.I * (lowerY x' : ℂ))‖ : ℝ) : ℂ) *
              Complex.exp ((Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ) * Complex.I) :=
          (Complex.norm_mul_exp_arg_mul_I _).symm
        calc lowerMt ε (Complex.I * (lowerY x' : ℂ)) ^ 2
            = ((‖lowerMt ε (Complex.I * (lowerY x' : ℂ))‖ ^ 2 : ℝ) : ℂ) *
                (Complex.exp ((Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ) * Complex.I)) ^ 2 := by
              conv_lhs => rw [h1]
              push_cast; ring
          _ = ((lowerWeps ε (lowerY x') : ℝ) : ℂ) *
                Complex.exp (Complex.I * (2 * Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ)) := by
              unfold lowerWeps
              rw [← Complex.exp_nat_mul]
              congr 2; push_cast; ring
      rw [show (Ex⁻¹ : ℂ) * (Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0 ε vstar *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))) =
          ((Ex⁻¹ : ℂ) * (Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0 ε vstar)) *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)) by ring]
      rw [hK0_v, hmt_polar, hexp_G]
      have hcombine : Complex.I * (((lowerWeps ε (lowerY x') : ℝ) : ℂ) *
            Complex.exp (Complex.I * (2 * Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ)) *
            Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ))) *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)) =
          ((lowerWeps ε (lowerY x') : ℝ) : ℂ) * (Complex.I *
            Complex.exp (((lowerThetaEps Gout ε (lowerY x') - 2 * π * c' * cumulN x' : ℝ) : ℂ) * Complex.I)) := by
        have h1 : Complex.exp (Complex.I * (2 * Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ)) *
            Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ)) *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)) =
            Complex.exp (((lowerThetaEps Gout ε (lowerY x') - 2 * π * c' * cumulN x' : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1; unfold lowerThetaEps; push_cast; ring
        calc Complex.I * (((lowerWeps ε (lowerY x') : ℝ) : ℂ) *
                Complex.exp (Complex.I * (2 * Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ)) *
                Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ))) *
                Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))
            = ((lowerWeps ε (lowerY x') : ℝ) : ℂ) * (Complex.I *
                (Complex.exp (Complex.I * (2 * Complex.arg (lowerMt ε (Complex.I * (lowerY x' : ℂ))) : ℂ)) *
                 Complex.exp (Complex.I * (Complex.arg (Gout (Complex.I * (lowerY x' : ℂ))) : ℂ)) *
                 Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)))) := by ring
          _ = _ := by rw [h1]
      rw [hcombine, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h_ke, ← h_lead]
    have hdiff : -((Ex⁻¹ : ℂ) * (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
          ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re -
        -((Ex⁻¹ : ℂ) * (Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0 ε vstar *
          Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)))).re =
        (-(Ex⁻¹ : ℂ) * ((√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
          ∫ v in Ioi (0 : ℝ), kedgeAmp0 ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) -
          Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0 ε vstar *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)))).re := by
      simp [Complex.sub_re, Complex.mul_re]; ring
    rw [hdiff]
    calc |(-(Ex⁻¹ : ℂ) * _).re| ≤ ‖-(Ex⁻¹ : ℂ) * _‖ := Complex.abs_re_le_norm _
      _ = Ex⁻¹ * ‖_‖ := by
          rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEx_pos]
      _ ≤ E_min⁻¹ * (C_ker0 / c') := mul_le_mul hEx_inv hk0 (norm_nonneg _) (by positivity)
      _ ≤ E_min⁻¹ * (max C_ker0 (K1 / √(edgeF' v₀) + C_ker1) / c') := by gcongr; exact le_max_left _ _
      _ = C_k / c' := by dsimp [C_k]; ring
  · have h_ke1 : virasoroKedge1Eps c' ε x' = -((Ex⁻¹ : ℂ) * (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re := by
      unfold virasoroKedge1Eps
      have h_in : ∫ v in Ioi (0 : ℝ), kedgeEpsIntegrand c' ε x' v * ((1 : ℂ) - 2 * Complex.I * (v : ℂ))⁻¹ =
          ((Ex⁻¹ : ℝ) : ℂ) * ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        have hdiv : ((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 / (1 - Real.exp (-(4 * π * x'))) ^ 2 *
            √(edgeF' v) : ℝ) = Ex⁻¹ * ((1 - Real.exp (-(4 * π * edgeF v))) ^ 2 * √(edgeF' v)) := by
          change _ / Ex * _ = _; ring
        unfold kedgeEpsIntegrand kedgeAmp0Aux kedgeAmp0
        rw [hdiv, Complex.ofReal_mul]; ring
      rw [h_in]
      calc -√(2 * c' / 3) *
              (Complex.exp (Complex.I * (π : ℂ) / 4) *
                (((Ex⁻¹ : ℝ) : ℂ) * ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re
          = -(((√(2 * c' / 3) : ℝ) : ℂ) *
                (Complex.exp (Complex.I * (π : ℂ) / 4) *
                  (((Ex⁻¹ : ℝ) : ℂ) * ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))))).re := by
              rw [Complex.re_ofReal_mul]; ring
        _ = -((Ex⁻¹ : ℂ) * (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
                ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ)))).re := by
              congr 2; push_cast; ring
    obtain ⟨A1, A2, hA⟩ := (hlg hε).2
    have hL1_bd : ‖Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0Aux ε vstar *
        Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))‖ ≤ K1 / √(edgeF' v₀) := by
      rw [norm_mul, norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.sqrt_pos.mpr hF'_pos),
        show -Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ) =
          ((-(2 * π * c' * cumulN x') : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      have hsq_ge : √(edgeF' v₀) ≤ √(edgeF' vstar) := Real.sqrt_le_sqrt hF'_v
      have hsq_pos : 0 < √(edgeF' v₀) := Real.sqrt_pos.mpr (edgeF'_pos hv₀_pos)
      calc (1 / √(edgeF' vstar)) * ‖kedgeAmp0Aux ε vstar‖ ≤ (1 / √(edgeF' v₀)) * K1 :=
            mul_le_mul (one_div_le_one_div_of_le hsq_pos hsq_ge) (hA.b0 vstar hvstar_ge) (norm_nonneg _) (by positivity)
        _ = K1 / √(edgeF' v₀) := by ring
    have hS1_bd : ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
        ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))‖ ≤
        K1 / √(edgeF' v₀) + C_ker1 := by
      have htr : ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
          ∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))‖ ≤
          ‖Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0Aux ε vstar *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))‖ +
          ‖√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
            (∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) -
            Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0Aux ε vstar *
              Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ))‖ := by
        simpa [add_sub_cancel] using norm_add_le
          (Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0Aux ε vstar *
            Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)))
          (√(2 * c' / 3) * Complex.exp (Complex.I * (π : ℂ) / 4) *
            (∫ v in Ioi (0 : ℝ), kedgeAmp0Aux ε v * Complex.exp (Complex.I * ((c' * phiDual v x' : ℝ) : ℂ))) -
            Complex.I / (√(edgeF' vstar) : ℂ) * kedgeAmp0Aux ε vstar *
              Complex.exp (-Complex.I * ((2 * π * c' * cumulN x' : ℝ) : ℂ)))
      have hk1' : C_ker1 / c' ≤ C_ker1 := div_le_self hCk1 hc'_1
      linarith
    rw [h_ke1, abs_neg]
    calc |((Ex⁻¹ : ℂ) * _).re| ≤ ‖(Ex⁻¹ : ℂ) * _‖ := Complex.abs_re_le_norm _
      _ = Ex⁻¹ * ‖_‖ := by
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEx_pos]
      _ ≤ E_min⁻¹ * (K1 / √(edgeF' v₀) + C_ker1) := mul_le_mul hEx_inv hS1_bd (norm_nonneg _) (by positivity)
      _ ≤ E_min⁻¹ * max C_ker0 (K1 / √(edgeF' v₀) + C_ker1) := by gcongr; exact le_max_right _ _
      _ = C_k := rfl

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_kedge_outer_of_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_kedge_outer_of_delta

end

end FormalResearch.ModularBootstrap.FiveTerm
