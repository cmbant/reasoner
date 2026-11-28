module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerPass2Window
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodArea
public import FormalResearch.ModularBootstrap.FiveTerm.LowerCorL
public import FormalResearch.SignUncertainty.CtDyadicGReg

/-!
# Top-Scale Two-Moment Bounds for `ctl:pass2` (`LowerPass2Top`)

Proves the top-scale arc-mass and second-moment bounds on `lowerGoodGReg A c g` at the Virasoro
top scale `R_J = A^2 ∈ [pass2ScaleLo^2 c^{2/3}, pass2ScaleHi^2 c^{2/3} - 1]`, for every weakly
feasible Virasoro violator `(T, g)` with `T < Δ(a₁)` and `T ≤ Δ(-virasoroAThr)`:

* `virasoro_top_moments`: `B₁(R_J) + B₂(R_J) ≤ K c^{-1/3}` from `virasoro_bootstrapHB_of_YVFor` +
  `teb_bootstrap_hb` (`corL_virasoro` gives `QuantC1B2Holds`);
* `virasoro_top_arcMass_le`: `hdArcMass A (lowerGoodGReg A c g) ≤ C_Σ / A` from
  `virasoro_cov_window_log` on the covered arc, `virasoroPsiTilde_conj` for reflection, and
  `virasoroPsiTilde_typeII_envelope` on the wedge `sin y < pass2AngleC2 A^{-3/2} √(log c)`;
* `virasoro_top_secondMoment_le`: `∫_{-A}^A t^2 ‖lowerGoodGReg A c g t‖ dt ≤ C_S A` via `v = t^2`,
  splitting at `u_T` and using `R_J B₁(R_J) ≤ C c^{1/3} ≤ C' A`;
* `virasoro_pass2_top_data`: bundled top-scale output consumed by `LowerPass2Main`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.TwoEdgeBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.HalfDiscCauchy
open FormalResearch.SignUncertainty

/-- Dimensionless lower scale `b_lo := (95/100) * virasoroBVChoice`. -/
noncomputable def pass2ScaleLo : ℝ := (95 / 100 : ℝ) * virasoroBVChoice

/-- Dimensionless upper scale `b_hi := √2 * virasoroBVChoice`. -/
noncomputable def pass2ScaleHi : ℝ := Real.sqrt 2 * virasoroBVChoice

lemma pass2ScaleLo_pos : 0 < pass2ScaleLo := by
  unfold pass2ScaleLo; have := virasoroBVChoice_pos; positivity

lemma pass2ScaleLo_le_choice : pass2ScaleLo ≤ virasoroBVChoice := by
  unfold pass2ScaleLo; have := virasoroBVChoice_pos; linarith

lemma pass2ScaleLo_le_hi : pass2ScaleLo ≤ pass2ScaleHi := by
  unfold pass2ScaleLo pass2ScaleHi
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  have := virasoroBVChoice_pos
  nlinarith

lemma pass2ScaleHi_sq : pass2ScaleHi ^ 2 = 2 * virasoroBVChoice ^ 2 := by
  unfold pass2ScaleHi; rw [mul_pow, Real.sq_sqrt zero_le_two]

/-! ### 1. Top-scale band moments via `virasoro_bootstrapHB_of_YVFor` -/

private lemma log_le_inv_alpha_rpow {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    Real.log c ≤ (1 / α) * c ^ α := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc α)
  rw [Real.log_rpow hc] at h
  have h1 : α * Real.log c ≤ c ^ α := by linarith only [h]
  calc Real.log c = (1 / α) * (α * Real.log c) := by field_simp [hα.ne']
    _ ≤ (1 / α) * c ^ α := by gcongr

private lemma virasoro_sigma_arc_eventually_b (b : ℝ) (hb : 0 < b) :
    ∀ᶠ c' : ℝ in atTop,
      (3 * π) ^ (12 : ℕ) ≤ c' ∧
      48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) ∧
      virasoroSigma c' ≤ 1 / 2 ∧
      virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
  have h1 : ∀ᶠ c' : ℝ in atTop, (3 * π) ^ (12 : ℕ) ≤ c' := eventually_ge_atTop _
  have h2 : ∀ᶠ c' : ℝ in atTop, 48 ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop (pow_pos hb 2)).eventually_ge_atTop 48
  have h3 : ∀ᶠ c' : ℝ in atTop, virasoroSigma c' ≤ 1 / 2 := by
    have ht : Tendsto (fun c' : ℝ => (6 * virasoroEnvC1) * c' ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul _
    filter_upwards [ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_ge_atTop (1 : ℝ)] with c' hmc' hc1
    have hc'0 : 0 < c' := by linarith
    have hlog : Real.log c' ≤ 6 * c' ^ (1 / 6 : ℝ) := by
      have h := log_le_inv_alpha_rpow (by norm_num : (0 : ℝ) < 1 / 6) hc'0
      norm_num at h
      exact h
    have hpow : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 6 : ℝ) = c' ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc'0]; norm_num
    have hC1 := virasoroEnvC1_pos.le
    calc virasoroSigma c' = virasoroEnvC1 * (c' ^ (-(1 / 3 : ℝ)) * Real.log c') := by
          unfold virasoroSigma; ring
      _ ≤ virasoroEnvC1 * (c' ^ (-(1 / 3 : ℝ)) * (6 * c' ^ (1 / 6 : ℝ))) := by gcongr
      _ = (6 * virasoroEnvC1) * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 6 : ℝ)) := by ring
      _ = (6 * virasoroEnvC1) * c' ^ (-(1 / 6 : ℝ)) := by rw [hpow]
      _ ≤ 1 / 2 := hmc'
  have h4 : ∀ᶠ c' : ℝ in atTop,
      virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤ 1 := by
    let M : ℝ := 24 * virasoroEnvC1 * (3 * π * √2 * b + 1)
    have ht : Tendsto (fun c' : ℝ => M * c' ^ (-(1 / 24 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 24)).const_mul M
    filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (Iic_mem_nhds zero_lt_one)] with
        c' hc' hMc'
    have hc'_pos : 0 < c' := by linarith
    have hlog : Real.log c' ≤ 24 * c' ^ (1 / 24 : ℝ) := by
      have h := log_le_inv_alpha_rpow (by norm_num : (0 : ℝ) < 1 / 24) hc'_pos
      norm_num at h
      exact h
    have hlog_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hc13_le : c' ^ (-(1 / 3 : ℝ)) ≤ c' ^ (-(1 / 12 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc' (by norm_num)
    have h12 : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ) = c' ^ (-(1 / 12 : ℝ)) := by
      rw [← Real.rpow_add hc'_pos]; norm_num
    have h24 : c' ^ (-(1 / 12 : ℝ)) * c' ^ (1 / 24 : ℝ) = c' ^ (-(1 / 24 : ℝ)) := by
      rw [← Real.rpow_add hc'_pos]; norm_num
    have hsig_le : virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1) ≤
        virasoroEnvC1 * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
      unfold virasoroSigma
      have hterm1 : (virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') *
          (3 * π * √2 * b * c' ^ (1 / 4 : ℝ)) =
          virasoroEnvC1 * (3 * π * √2 * b) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
        calc _ = virasoroEnvC1 * (3 * π * √2 * b) * ((c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 4 : ℝ)) * Real.log c') := by ring
          _ = _ := by rw [h12]
      have hterm2 : virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤
          virasoroEnvC1 * 1 * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := by
        have := virasoroEnvC1_pos.le
        nlinarith [mul_le_mul_of_nonneg_right hc13_le hlog_nn]
      linarith
    have hpos : 0 ≤ virasoroEnvC1 * (3 * π * √2 * b + 1) := by have := virasoroEnvC1_pos; positivity
    have hlog_c12 : c' ^ (-(1 / 12 : ℝ)) * Real.log c' ≤
        c' ^ (-(1 / 12 : ℝ)) * (24 * c' ^ (1 / 24 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hc'_pos.le _)
    calc virasoroSigma c' * (3 * π * √2 * b * c' ^ (1 / 4 : ℝ) + 1)
        ≤ virasoroEnvC1 * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * Real.log c') := hsig_le
      _ ≤ virasoroEnvC1 * (3 * π * √2 * b + 1) * (c' ^ (-(1 / 12 : ℝ)) * (24 * c' ^ (1 / 24 : ℝ))) :=
          mul_le_mul_of_nonneg_left hlog_c12 hpos
      _ = M * (c' ^ (-(1 / 12 : ℝ)) * c' ^ (1 / 24 : ℝ)) := by dsimp [M]; ring
      _ = M * c' ^ (-(1 / 24 : ℝ)) := by rw [h24]
      _ ≤ 1 := hMc'
  exact h1.and (h2.and (h3.and h4))

/-- **Top-scale band moments (`ctl:pass2`, `ct:dyadic` (1) at `R_J`)**:
for all sufficiently large `c`, any weakly feasible Virasoro violator `(T, g)` with
`T < Δ(a₁)` and `T ≤ Δ(-virasoroAThr)` has a radius `R_J` in
`[pass2ScaleLo^2 c^{2/3}, pass2ScaleHi^2 c^{2/3} - 1]` satisfying `B₁(R_J) + B₂(R_J) ≤ K c^{-1/3}`. -/
theorem virasoro_top_moments :
    ∃ K c₀ : ℝ, 0 ≤ K ∧ virasoroCQEnv ≤ c₀ ∧ ∀ {c T : ℝ}, c₀ ≤ c → ∀ {g : ℝ → ℝ},
      virasoroProblem.IsWeaklyFeasible (c / 12) T g →
      T < virasoroDeltaChart c (airyZero 1) →
      T ≤ virasoroDeltaChart c (-virasoroAThr) →
      ∃ R : ℝ,
        pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) ≤ R ∧
        R + 1 ≤ pass2ScaleHi ^ 2 * c ^ (2 / 3 : ℝ) ∧
        virasoroAThr ≤ R ∧
        virasoroBandB1 c R T g + virasoroBandB2 c R g ≤ K * c ^ (-(1 / 3 : ℝ)) := by
  have hb1_pos : 0 < pass2ScaleLo := pass2ScaleLo_pos
  have hb1_bv : pass2ScaleLo ≤ virasoroBV := pass2ScaleLo_le_choice.trans virasoroBVChoice_le
  have hb1_scale : 2 * pass2ScaleLo ^ 2 ≤ virasoroScaleThresh := by
    have hsq : pass2ScaleLo ^ 2 ≤ virasoroBVChoice ^ 2 :=
      pow_le_pow_left₀ hb1_pos.le pass2ScaleLo_le_choice 2
    exact (by linarith : 2 * pass2ScaleLo ^ 2 ≤ 2 * virasoroBVChoice ^ 2).trans virasoroBVChoice_scaleCompat
  obtain ⟨C_fb, c_YV, hC_fb, hc_YV_Q, hYV_at⟩ := yvInputFor_of_scaleCompat hb1_pos hb1_bv hb1_scale
  obtain ⟨c_Q1, C_gap, κ_gap, hc_Q1, hC_gap, hκ_gap, hQ1⟩ := lemmaQ_part1At hb1_pos hb1_bv
  obtain ⟨c_corL, _, hc_corL, _, hcorL⟩ := corL_virasoro
  let P := virasoroBootstrapParamsFor pass2ScaleLo hb1_pos C_fb hC_fb C_gap κ_gap hC_gap hκ_gap
  set Ls : ℝ := tebLSharpHB P 0
  set K : ℝ := tebCXHB P 0 * (1 + Real.log Ls)
  have hCX : 0 < tebCXHB P 0 := tebCXOf_pos P (tebLambdaN_nonneg P le_rfl)
  have hLs1 : 1 ≤ Ls := one_le_tebLogSharp (le_max_left _ _)
  have hK0 : 0 ≤ K := by have := Real.log_nonneg hLs1; dsimp [K]; positivity
  have hdiff_b : 0 < pass2ScaleHi ^ 2 - 2 * pass2ScaleLo ^ 2 := by
    rw [pass2ScaleHi_sq]; unfold pass2ScaleLo
    have := virasoroBVChoice_pos
    nlinarith [sq_pos_of_pos this]
  have hev : ∀ᶠ c : ℝ in atTop,
      ((3 * π) ^ (12 : ℕ) ≤ c ∧ 48 ≤ pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) ∧
        virasoroSigma c ≤ 1 / 2 ∧
        virasoroSigma c * (3 * π * √2 * pass2ScaleLo * c ^ (1 / 4 : ℝ) + 1) ≤ 1) ∧
      C_gap * Real.exp (-κ_gap * c) < 1 / 2 ∧
      2 ≤ (pass2ScaleHi ^ 2 - 2 * pass2ScaleLo ^ 2) * c ^ (2 / 3 : ℝ) ∧
      virasoroAThr ≤ pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) ∧
      max (max virasoroCQEnv (max c_YV c_Q1)) (max c_corL (tebC2 P)) ≤ c := by
    have hexp : ∀ᶠ c : ℝ in atTop, C_gap * Real.exp (-κ_gap * c) < 1 / 2 := by
      have ht : Tendsto (fun c : ℝ => C_gap * Real.exp (-κ_gap * c)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun c : ℝ => -κ_gap * c) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg (by linarith)
        simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp h1).const_mul C_gap
      exact ht.eventually (gt_mem_nhds (by norm_num))
    have hc23 : Tendsto (fun c : ℝ => c ^ (2 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    filter_upwards [virasoro_sigma_arc_eventually_b pass2ScaleLo hb1_pos, hexp,
      (hc23.const_mul_atTop hdiff_b).eventually_ge_atTop 2,
      (hc23.const_mul_atTop (pow_pos hb1_pos 2)).eventually_ge_atTop virasoroAThr,
      eventually_ge_atTop (max (max virasoroCQEnv (max c_YV c_Q1)) (max c_corL (tebC2 P)))] with
        c h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨K, max c₀ virasoroCQEnv, hK0, le_max_right _ _, fun {c T} hc {g} hg hT_a1 hT_hi => ?_⟩
  obtain ⟨⟨hc12, hb48, hς_half, hς_arc⟩, hgap, hroom, hAThr, hmax⟩ := hc₀ c ((le_max_left _ _).trans hc)
  have hc_Qenv : virasoroCQEnv ≤ c := (le_max_right _ _).trans hc
  have hc_YV : c_YV ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hmax)
  have hc_Q1 : c_Q1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hmax)
  have hc_corL : c_corL ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have hc_teb : tebC2 P ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hmax)
  have hc_pos : 0 < c := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc_Qenv
  obtain ⟨_, hdl_bd, _, hT_A2⟩ := hQ1 hc_Q1 hg
  have hdl_half : virasoroDeltaLobeAt pass2ScaleLo c g < 1 / 2 := hdl_bd.trans_lt hgap
  have hB2 := ((hcorL hc_corL hg).2 hT_a1).2.2.2.1
  let hbRes := virasoro_bootstrapHB_of_YVFor hb1_pos hb1_bv hC_fb hc_YV_Q hYV_at
    hC_gap hκ_gap hc_Qenv hc_YV hc12 hb48 hς_half hς_arc hg hdl_bd hdl_half hT_A2 hT_a1 hB2
  let I := hbRes.1
  have hB3 := hbRes.2.1
  have hIc : I.c = c := hbRes.2.2.1
  have hboot := teb_bootstrap_hb P I (by rw [hIc]; exact hc_teb)
  have hL_le : I.L ≤ Ls := (hboot.2 hB3).1
  have hlog : Real.log I.L ≤ Real.log Ls := Real.log_le_log (by linarith [I.hL_lb]) hL_le
  have hc_m13 : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc_pos.le _
  have hB_sum : I.B_1 + I.B_2 ≤ K * c ^ (-(1 / 3 : ℝ)) := by
    have h1 := hboot.1
    rw [hIc] at h1
    calc I.B_1 + I.B_2 ≤ tebCXHB P 0 * (1 + Real.log I.L) * c ^ (-(1 / 3 : ℝ)) := h1
      _ ≤ tebCXHB P 0 * (1 + Real.log Ls) * c ^ (-(1 / 3 : ℝ)) := by gcongr
  have hR_lo : pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) ≤ I.R := by
    have ha_lb : pass2ScaleLo * c ^ (1 / 3 : ℝ) ≤ I.a := by
      have ha' := I.ha_lb
      rw [hIc] at ha'
      exact ha'
    have hsq : (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ 2 ≤ I.a ^ 2 :=
      pow_le_pow_left₀ (by positivity) ha_lb 2
    rw [I.ha_sq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2,
      ← Real.rpow_mul hc_pos.le] at hsq
    simpa only [Nat.cast_ofNat, show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num] using hsq
  have hR_hi : I.R + 1 ≤ pass2ScaleHi ^ 2 * c ^ (2 / 3 : ℝ) := by
    have hub : I.R ≤ 2 * pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) + 1 := by
      have hub' := I.hR_ub
      rw [hIc] at hub'
      exact hub'
    linarith
  have hB1_eq : I.B_1 = virasoroBandB1 c I.R T g := rfl
  have hB2_eq : I.B_2 = virasoroBandB2 c I.R g := rfl
  refine ⟨I.R, hR_lo, hR_hi, hAThr.trans hR_lo, ?_⟩
  rw [← hB1_eq, ← hB2_eq]
  exact hB_sum

/-! ### 2. Arc mass and second moment of `lowerGoodGReg` at top scale -/

private lemma lowerGoodGReg_norm_arc {A : ℝ} (hA : 0 < A) (c : ℝ) (g : ℝ → ℝ)
    {y : ℝ} (hy : y ∈ Icc 0 π) :
    ‖lowerGoodGReg A c g ((A : ℂ) * Complex.exp (y * I))‖ =
      (2 * Real.sin y) ^ 2 * A * ‖virasoroPsiTilde c g (-(((A : ℂ) * Complex.exp (y * I)) ^ 2))‖ *
        ‖Complex.exp ((4 / 3 : ℂ) * I * ((A : ℂ) * Complex.exp (y * I)) ^ 3)‖ := by
  have hs : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
  unfold lowerGoodGReg
  rw [norm_mul, norm_mul, norm_mul, norm_pow, arc_sq_div hA, norm_one_sub_exp_two_mul, norm_arc hA,
    abs_of_nonneg hs]

private lemma lowerGoodGReg_norm_reflect {c : ℝ} (hc_Q : virasoroCQEnv ≤ c) {A : ℝ}
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    {w : ℂ} (hw : ‖w‖ ^ 2 ≤ virasoroAC c ^ 2) :
    ‖lowerGoodGReg A c g (-(star w))‖ = ‖lowerGoodGReg A c g w‖ := by
  have hc_pos : 0 < c := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc_Q
  have hshift : virasoroProblem.totalShift ≤ c / 12 := by
    rw [virasoroProblem_totalShift]; have := virasoroCQEnv_ge; linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm (c / 12) g :=
    cardyNorm_pos_of_nonzero hshift hg.1 hg.2.1
  have hmem : -(w ^ 2) ∈ closedBall (0 : ℂ) (virasoroAC c ^ 2) := by
    rw [mem_closedBall_zero_iff, norm_neg, norm_pow]; exact hw
  have hpsi : virasoroPsiTilde c g (-((-(star w)) ^ 2)) = star (virasoroPsiTilde c g (-(w ^ 2))) := by
    have h := virasoroPsiTilde_conj hc_Q hg.1 hM_pos hmem
    rw [← h]; congr 1; simp [star_pow]
  have hexp : ‖Complex.exp ((4 / 3 : ℂ) * I * (-(star w)) ^ 3)‖ =
      ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1; simp [Complex.mul_re, Complex.mul_im, pow_succ]; ring
  unfold lowerGoodGReg
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hpsi, norm_star, hexp, norm_neg, norm_star]
  congr 3
  rw [norm_pow, norm_pow]
  congr 1
  rw [← norm_star]
  congr 1
  simp [star_pow, star_sub, star_div₀]

private lemma lowerGoodGReg_norm_real (A c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    ‖lowerGoodGReg A c g (t : ℂ)‖ =
      (1 - t ^ 2 / A ^ 2) ^ 2 * |t| * ‖virasoroPsiTilde c g (-((t ^ 2 : ℝ) : ℂ))‖ := by
  unfold lowerGoodGReg
  have h1 : (1 - (t : ℂ) ^ 2 / (A : ℂ) ^ 2) = ((1 - t ^ 2 / A ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ‖Complex.exp ((4 / 3 : ℂ) * I * (t : ℂ) ^ 3)‖ = 1 := by
    rw [Complex.norm_exp]; simp [pow_succ, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, norm_mul, norm_mul, h2, mul_one, h1, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast; ring_nf

private lemma virasoro_top_secondMoment_le {c T R A : ℝ}
    (hc_Q : virasoroCQEnv ≤ c) (hA : 0 < A) (hAR : A ^ 2 = R)
    (hR_thr : virasoroAThr ≤ R) (hR_ub : R ≤ virasoroAC c ^ 2)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hT_lo : virasoroDeltaChart c 0 ≤ T) (hT_hi : T ≤ virasoroDeltaChart c (-virasoroAThr))
    (ha1_uT : airyZero 1 < virasoroUT c T) :
    ∫ t in (-A)..A, t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖ ≤
      R * virasoroBandB1 c R T g + virasoroAThr := by
  have hc_10000 : 10000 ≤ c := virasoroCQEnv_ge.trans hc_Q
  have hc_pos : 0 < c := by linarith only [hc_10000]
  have hc_24 : 24 ≤ c := by linarith only [hc_10000]
  have hc_1000 : 1000 ≤ c := by linarith only [hc_10000]
  have hA_ub : A ^ 2 ≤ virasoroAC c ^ 2 := hAR.symm ▸ hR_ub
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  have hPsi_cont : ContinuousOn (fun u : ℝ => ‖virasoroPsiTilde c g (u : ℂ)‖)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)) :=
    continuous_norm.comp_continuousOn
      ((virasoroPsiTilde_analyticOnNhd hc_1000 hg.1).continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr hv))
  set gv : ℝ → ℝ := fun v => v * ‖virasoroPsiTilde c g (-(v : ℂ))‖
  have hgv_cont : ContinuousOn gv (Icc 0 R) := by
    refine continuousOn_id.mul (ContinuousOn.norm ?_)
    refine ((virasoroPsiTilde_analyticOnNhd hc_1000 hg.1).continuousOn.comp
      (by fun_prop : Continuous fun v : ℝ => -(v : ℂ)).continuousOn fun v hv => ?_)
    exact virasoro_closedBall_subset_psiDom hc_pos (by
      rw [mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1]
      exact hv.2.trans hR_ub)
  set H : ℝ → ℝ := fun t => |t| * gv (t ^ 2)
  have hHc : ContinuousOn H (Icc (-A) A) := by
    refine continuous_abs.continuousOn.mul (hgv_cont.comp (continuous_pow 2).continuousOn fun t ht => ?_)
    refine ⟨sq_nonneg t, ?_⟩
    rw [← sq_abs t, ← hAR]
    exact pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) 2
  have hpt : ∀ t ∈ Icc (-A) A, t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖ ≤ H t := by
    intro t ht
    have hsq : t ^ 2 ≤ A ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ht) 2
    have hfac : (1 - t ^ 2 / A ^ 2) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ 1 - t ^ 2 / A ^ 2 := by rw [sub_nonneg, div_le_one (pow_pos hA 2)]; exact hsq
      have h1 : 1 - t ^ 2 / A ^ 2 ≤ 1 := by
        have ht2 : 0 ≤ t ^ 2 / A ^ 2 := by positivity
        linarith
      nlinarith
    rw [lowerGoodGReg_norm_real]
    dsimp [H, gv]
    have hcoe : -((t ^ 2 : ℝ) : ℂ) = -((t ^ 2 : ℂ)) := by push_cast; ring
    have hn : 0 ≤ t ^ 2 * (|t| * ‖virasoroPsiTilde c g (-((t ^ 2 : ℝ) : ℂ))‖) := by positivity
    calc t ^ 2 * ((1 - t ^ 2 / A ^ 2) ^ 2 * |t| * ‖virasoroPsiTilde c g (-((t ^ 2 : ℝ) : ℂ))‖)
        = (1 - t ^ 2 / A ^ 2) ^ 2 * (t ^ 2 * (|t| * ‖virasoroPsiTilde c g (-((t ^ 2 : ℝ) : ℂ))‖)) := by ring
      _ ≤ 1 * (t ^ 2 * (|t| * ‖virasoroPsiTilde c g (-((t ^ 2 : ℝ) : ℂ))‖)) := by gcongr
      _ = |t| * (t ^ 2 * ‖virasoroPsiTilde c g (-((t ^ 2 : ℝ) : ℂ))‖) := by ring
  have hGan := lowerGood_GReg_analytic hc_1000 hA hA_ub hg.1
  have hLc : ContinuousOn (fun t : ℝ => t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖) (Icc (-A) A) := by
    refine (continuous_pow 2).continuousOn.mul (ContinuousOn.norm ?_)
    exact hGan.continuousOn.comp Complex.continuous_ofReal.continuousOn fun t ht => by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.mpr ht
  have hAA : -A ≤ A := by linarith
  have step1 : ∫ t in (-A)..A, t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖ ≤ ∫ t in (-A)..A, H t :=
    intervalIntegral.integral_mono_on hAA (hLc.intervalIntegrable_of_Icc hAA)
      (hHc.intervalIntegrable_of_Icc hAA) hpt
  have hHeven : ∀ t, H (-t) = H t := fun t => by simp [H]
  have step2 : ∫ t in (-A)..A, H t = 2 * ∫ t in (0 : ℝ)..A, H t := by
    have hint0 : IntervalIntegrable H volume 0 A :=
      (hHc.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩ : Icc 0 A ⊆ Icc (-A) A)).intervalIntegrable_of_Icc hA.le
    have hintn : IntervalIntegrable H volume (-A) 0 :=
      (hHc.mono (fun t ht => ⟨ht.1, by linarith [ht.2]⟩ : Icc (-A) 0 ⊆ Icc (-A) A)).intervalIntegrable_of_Icc (by linarith)
    rw [← intervalIntegral.integral_add_adjacent_intervals hintn hint0]
    have hneg : ∫ t in (-A)..0, H t = ∫ t in (0 : ℝ)..A, H t := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := A) H
      simp only [hHeven, neg_zero] at h
      exact h.symm
    rw [hneg]; ring
  have step3 : 2 * ∫ t in (0 : ℝ)..A, H t = ∫ v in (0 : ℝ)..R, gv v := by
    rw [← hAR]
    have hcv := intervalIntegral.integral_comp_mul_deriv'' (a := 0) (b := A) (f := fun t : ℝ => t ^ 2)
      (f' := fun t => 2 * t) (g := gv) (continuous_pow 2).continuousOn
      (fun x _ => by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt)
      (by fun_prop) (hgv_cont.mono (by
        rintro _ ⟨t, ht, rfl⟩
        rw [uIcc_of_le hA.le] at ht
        refine ⟨sq_nonneg t, ?_⟩
        rw [← hAR]
        exact pow_le_pow_left₀ ht.1 ht.2 2))
    simp only [Function.comp_apply, zero_pow two_ne_zero] at hcv
    rw [← hcv, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hA.le] at ht
    simp only [H, abs_of_nonneg ht.1]; ring
  have step4 : ∫ v in (0 : ℝ)..R, gv v = ∫ u in (-R)..0, (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖ := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := R)
      (fun u : ℝ => (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖)
    simp only [neg_neg, neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun v _ => ?_
    dsimp [gv]; congr 2; push_cast; ring
  have hu_mem := virasoroUT_between hc_pos (by linarith : -(virasoroAC c ^ 2) ≤ -R)
    (sq_nonneg _) (by linarith : -R ≤ 0) hT_lo
    (hT_hi.trans ((virasoroDeltaChart_strictAnti hc_pos).antitoneOn
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith [virasoroAThr_pos]⟩ (by linarith)))
  set uT := virasoroUT c T
  have huT_le0 : uT ≤ 0 := hu_mem.1.2
  have huT_geR : -R ≤ uT := hu_mem.1.1
  have hcont_prod : ContinuousOn (fun u : ℝ => (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖) (Icc (-R) 0) :=
    continuousOn_id.neg.mul (hPsi_cont.mono (Icc_subset_Icc (by linarith) (sq_nonneg _)))
  have hI1 : IntervalIntegrable (fun u => (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖) volume (-R) uT :=
    (hcont_prod.mono (Icc_subset_Icc_right huT_le0)).intervalIntegrable_of_Icc huT_geR
  have hI2 : IntervalIntegrable (fun u => (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖) volume uT 0 :=
    (hcont_prod.mono (Icc_subset_Icc_left huT_geR)).intervalIntegrable_of_Icc huT_le0
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hband_eq : ∫ u in (-R)..uT, (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖ =
      R * virasoroBandB1 c R T g := by
    have hcongr : EqOn (fun u : ℝ => (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖)
        (fun u : ℝ => (-u) * (virasoroPsiTilde c g (u : ℂ)).re) (Icc (-R) uT) := fun u hu => by
      have hu_abs : |u| ≤ virasoroAC c ^ 2 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2, sq_nonneg (virasoroAC c)]⟩
      have him : (virasoroPsiTilde c g (u : ℂ)).im = 0 := by
        have hsh : virasoroProblem.totalShift ≤ c / 12 := by
          rw [virasoroProblem_totalShift]; linarith
        exact ((lemmaQ_part2 hc_Q hg.1 (cardyNorm_pos_of_nonzero hsh hg.1 hg.2.1)).2.1 u hu_abs).1
      have hre : 0 ≤ (virasoroPsiTilde c g (u : ℂ)).re := by
        refine (lemmaQ_part3 hc_Q hg).1 u hu_abs ?_
        rw [← hu_mem.2]
        exact (virasoroDeltaChart_strictAnti hc_pos).antitoneOn
          ⟨by linarith [hu.1], by linarith [hu.2, sq_nonneg (virasoroAC c)]⟩
          ⟨by linarith [huT_geR], by linarith [huT_le0, sq_nonneg (virasoroAC c)]⟩ hu.2
      have hnorm : ‖virasoroPsiTilde c g (u : ℂ)‖ = (virasoroPsiTilde c g (u : ℂ)).re := by
        rw [Complex.norm_def, Complex.normSq_apply, him, mul_zero, add_zero, Real.sqrt_mul_self hre]
      dsimp only
      rw [hnorm]
    rw [intervalIntegral.integral_congr (fun u hu => hcongr (by rwa [uIcc_of_le huT_geR] at hu))]
    have hmom := virasoroPsiTilde_moment_integral_eq hc_24 hg.1
      (by linarith : -(virasoroAC c ^ 2) ≤ -R) (by linarith [sq_nonneg (virasoroAC c)]) huT_geR
    rw [hu_mem.2] at hmom
    unfold virasoroBandB1
    rw [hmom]
    field_simp [hR_pos.ne']
  have hcore_le : ∫ u in uT..0, (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖ ≤ virasoroAThr := by
    have hAThr_eq : virasoroAThr = -airyZero 1 + 1 := by
      unfold virasoroAThr; rw [abs_of_neg (airyZero_neg 1)]
    have hpt2 : ∀ u ∈ Icc uT 0, (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖ ≤
        virasoroAThr * ‖virasoroPsiTilde c g (u : ℂ)‖ := fun u hu => by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      linarith [hu.1, hAThr_eq, ha1_uT]
    have hPsi_sub : IntervalIntegrable (fun u => ‖virasoroPsiTilde c g (u : ℂ)‖) volume uT 0 :=
      (hPsi_cont.mono (Icc_subset_Icc (by linarith) (sq_nonneg _))).intervalIntegrable_of_Icc huT_le0
    have hmono := intervalIntegral.integral_mono_on huT_le0 hI2 (hPsi_sub.const_mul virasoroAThr) hpt2
    rw [intervalIntegral.integral_const_mul] at hmono
    have hL1 : ∫ u in uT..0, ‖virasoroPsiTilde c g (u : ℂ)‖ ≤
        ∫ u in (-(virasoroAC c ^ 2))..(virasoroAC c ^ 2), ‖virasoroPsiTilde c g (u : ℂ)‖ :=
      intervalIntegral.integral_mono_interval (by linarith) huT_le0 (sq_nonneg _)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (hPsi_cont.intervalIntegrable_of_Icc (by linarith [sq_nonneg (virasoroAC c)]))
    have hL1_le1 := (lemmaQ_part3 hc_Q hg).2.1
    have hAThr_nn := virasoroAThr_pos.le
    calc ∫ u in uT..0, (-u) * ‖virasoroPsiTilde c g (u : ℂ)‖
        ≤ virasoroAThr * ∫ u in uT..0, ‖virasoroPsiTilde c g (u : ℂ)‖ := hmono
      _ ≤ virasoroAThr * 1 := mul_le_mul_of_nonneg_left (hL1.trans hL1_le1) hAThr_nn
      _ = virasoroAThr := mul_one _
  linarith [step1, step2, step3, step4, hsplit, hband_eq, hcore_le]

private lemma virasoro_top_arcMass_le {c T R A C_ang L_top CSig : ℝ} {g : ℝ → ℝ}
    (hc_Q : virasoroCQEnv ≤ c) (hc_1000 : 1000 ≤ c) (hc_ge1 : 1 ≤ c)
    (hA : 0 < A) (hAR : A ^ 2 = R) (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2)
    (hC_ang : 0 ≤ C_ang) (hL_top : 0 ≤ L_top)
    (hCSig : CSig = 4 * π * L_top + 4 * π * virasoroEnvC0 * Real.exp 1 * C_ang ^ 2)
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g)
    (hsig_le1 : virasoroSigma c ≤ 1)
    (hlog_le_A2 : Real.log c ≤ A ^ 2)
    (hAφ0_le : A * (C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)) ≤ 1)
    (hφ0_le : C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ 1)
    (hcov_pt : ∀ {u : ℂ}, 0 ≤ u.im → ‖u‖ = R →
      C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) * Real.sqrt ‖u‖ ≤ (u ^ (1 / 2 : ℂ)).re →
      ‖virasoroPsiTilde c g u‖ ≤
        L_top * airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) :
    hdArcMass A (lowerGoodGReg A c g) ≤ CSig / A := by
  set φ₀ : ℝ := C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)
  have hlog_nn : 0 ≤ Real.log c := Real.log_nonneg hc_ge1
  have hR_nn : 0 ≤ R := hAR ▸ sq_nonneg A
  have hφ0_nn : 0 ≤ φ₀ := by dsimp [φ₀]; positivity
  have h_cov_half : ∀ {y : ℝ}, y ∈ Icc (π / 2) π → φ₀ ≤ Real.sin y → 0 < Real.sin y →
      ‖lowerGoodGReg A c g ((A : ℂ) * Complex.exp (y * I))‖ * A ≤ 4 * L_top / A := by
    intro y hy hsin_ge hsin_pos
    have hy' : y ∈ Icc 0 π := ⟨by linarith only [hy.1, Real.pi_pos], hy.2⟩
    set w : ℂ := (A : ℂ) * Complex.exp (y * I)
    have hwim : 0 < w.im := by dsimp [w]; rw [im_arc]; positivity
    obtain ⟨hre, henv⟩ := lowerGood_airyEnv_neg_sq_of_im_pos hwim
    have him : w.im = A * Real.sin y := im_arc A y
    have hnorm : ‖-(w ^ 2)‖ = R := by rw [norm_neg, norm_pow, norm_arc hA, hAR]
    have hcos : Real.cos y ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hy.1 (by linarith only [hy.2, Real.pi_pos])
    have hure : 0 ≤ (-(w ^ 2)).im := by
      have hwre : w.re = A * Real.cos y := by
        dsimp [w]; rw [Complex.exp_mul_I]; simp [Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.neg_im, pow_two, Complex.mul_im]
      rw [hwre, him]; nlinarith only [mul_nonneg hA.le (neg_nonneg.2 hcos), mul_pos hA hsin_pos]
    have hsq : Real.sqrt ‖-(w ^ 2)‖ = A := by rw [hnorm, ← hAR, Real.sqrt_sq hA.le]
    have hang : C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) * Real.sqrt ‖-(w ^ 2)‖ ≤
        ((-(w ^ 2)) ^ (1 / 2 : ℂ)).re := by
      rw [hre, him, hsq, mul_comm A (Real.sin y)]
      exact mul_le_mul_of_nonneg_right (by simpa [φ₀] using hsin_ge) hA.le
    have hwv := hcov_pt hure hnorm hang
    rw [hre, him, henv, hnorm] at hwv
    have hX : 0 < ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
    have hAlg : (2 * Real.sin y) ^ 2 * A * ((A * Real.sin y) ^ (-(3 / 2 : ℝ)) * R ^ (-(3 / 4 : ℝ))) * A =
        4 * A⁻¹ * Real.sin y ^ (1 / 2 : ℝ) := by
      have hR_eq : R = A ^ (2 : ℝ) := by rw [← hAR, Real.rpow_two]
      have hR34 : R ^ (-(3 / 4 : ℝ)) = A ^ (-(3 / 2 : ℝ)) := by
        rw [hR_eq, ← Real.rpow_mul hA.le]; norm_num
      have hAp : A ^ (-(3 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) = A ^ (-3 : ℝ) := by
        rw [← Real.rpow_add hA]; norm_num
      have hA2 : A ^ (2 : ℝ) * A ^ (-3 : ℝ) = A⁻¹ := by
        rw [← Real.rpow_add hA, ← Real.rpow_neg_one]; norm_num
      have hs2 : Real.sin y ^ (2 : ℝ) * Real.sin y ^ (-(3 / 2 : ℝ)) = Real.sin y ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hsin_pos]; norm_num
      rw [hR34, Real.mul_rpow hA.le hsin_pos.le]
      calc (2 * Real.sin y) ^ 2 * A * (A ^ (-(3 / 2 : ℝ)) * Real.sin y ^ (-(3 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ))) * A
          = 4 * (A ^ 2 * (A ^ (-(3 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)))) *
              (Real.sin y ^ 2 * Real.sin y ^ (-(3 / 2 : ℝ))) := by ring
        _ = 4 * (A ^ (2 : ℝ) * A ^ (-3 : ℝ)) * (Real.sin y ^ (2 : ℝ) * Real.sin y ^ (-(3 / 2 : ℝ))) := by
            rw [hAp, Real.rpow_two, Real.rpow_two]
        _ = 4 * A⁻¹ * Real.sin y ^ (1 / 2 : ℝ) := by rw [hA2, hs2]
    have hs1 : Real.sin y ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one hsin_pos.le (Real.sin_le_one y) (by norm_num)
    calc ‖lowerGoodGReg A c g w‖ * A
        = ((2 * Real.sin y) ^ 2 * A * A) * (‖virasoroPsiTilde c g (-(w ^ 2))‖ *
            ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖) := by
          rw [lowerGoodGReg_norm_arc hA c g hy']; ring
      _ ≤ ((2 * Real.sin y) ^ 2 * A * A) *
            ((L_top * (‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖)⁻¹ *
              (A * Real.sin y) ^ (-(3 / 2 : ℝ)) * R ^ (-(3 / 4 : ℝ))) *
              ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖) := by
            have hk : 0 ≤ (2 * Real.sin y) ^ 2 * A * A := by positivity
            gcongr
      _ = L_top * ((2 * Real.sin y) ^ 2 * A * ((A * Real.sin y) ^ (-(3 / 2 : ℝ)) * R ^ (-(3 / 4 : ℝ))) * A) := by
            field_simp
      _ = L_top * (4 * A⁻¹ * Real.sin y ^ (1 / 2 : ℝ)) := by rw [hAlg]
      _ ≤ L_top * (4 * A⁻¹ * 1) := by gcongr
      _ = 4 * L_top / A := by ring
  have h_cov : ∀ {y : ℝ}, y ∈ Icc 0 π → φ₀ ≤ Real.sin y →
      ‖lowerGoodGReg A c g ((A : ℂ) * Complex.exp (y * I))‖ * A ≤ 4 * L_top / A := by
    intro y hy hsin_ge
    have hs0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
    rcases hs0.eq_or_lt with hs | hs
    · rw [lowerGoodGReg_norm_arc hA c g hy, ← hs]; simp; positivity
    · rcases le_total (π / 2) y with hh | hh
      · exact h_cov_half ⟨hh, hy.2⟩ hsin_ge hs
      · have hy2 : π - y ∈ Icc (π / 2) π := ⟨by linarith only [hh], by linarith only [hy.1]⟩
        have hs2 : Real.sin (π - y) = Real.sin y := Real.sin_pi_sub y
        have h1 := h_cov_half hy2 (by rw [hs2]; exact hsin_ge) (by rw [hs2]; exact hs)
        rw [arc_reflect, lowerGoodGReg_norm_reflect hc_Q hg (by rw [norm_arc hA]; exact hA_ub)] at h1
        exact h1
  have h_wedge : ∀ {y : ℝ}, y ∈ Icc 0 π → Real.sin y ≤ φ₀ →
      ‖lowerGoodGReg A c g ((A : ℂ) * Complex.exp (y * I))‖ * A ≤ 4 * virasoroEnvC0 * Real.exp 1 * φ₀ := by
    intro y hy hsin_le
    have hs0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
    rcases hs0.eq_or_lt with hs | hs
    · rw [lowerGoodGReg_norm_arc hA c g hy, ← hs]; simp; have := virasoroEnvC0_pos; positivity
    · set w : ℂ := (A : ℂ) * Complex.exp (y * I)
      have hwim : 0 < w.im := by dsimp [w]; rw [im_arc]; positivity
      obtain ⟨hre, henv⟩ := lowerGood_airyEnv_neg_sq_of_im_pos hwim
      have him : w.im = A * Real.sin y := im_arc A y
      have hnorm : ‖-(w ^ 2)‖ = A ^ 2 := by rw [norm_neg, norm_pow, norm_arc hA]
      have hu_mem : -(w ^ 2) ∈ closedBall (0 : ℂ) (virasoroAC c ^ 2) := by
        rw [mem_closedBall_zero_iff, hnorm]; exact hA_ub
      have hnotcut : ¬ ((-(w ^ 2)).im = 0 ∧ (-(w ^ 2)).re ≤ 0) := arc_data hwim
      have hM_pos : 0 < virasoroProblem.cardyNorm (c / 12) g := by
        have hsh : virasoroProblem.totalShift ≤ c / 12 := by
          rw [virasoroProblem_totalShift]; linarith only [hc_ge1, hc_1000]
        exact cardyNorm_pos_of_nonzero hsh hg.1 hg.2.1
      have hII := virasoroPsiTilde_typeII_envelope hc_Q hg.1 hM_pos hu_mem hnotcut
      have hsig_bd : virasoroSigma c * ((-(w ^ 2)) ^ (1 / 2 : ℂ)).re ≤ 1 := by
        rw [hre, him]
        have h1 : A * Real.sin y ≤ A * φ₀ := mul_le_mul_of_nonneg_left hsin_le hA.le
        have h2 : A * Real.sin y ≤ 1 := h1.trans hAφ0_le
        have h3 := mul_le_mul hsig_le1 h2 (mul_nonneg hA.le hs0) zero_le_one
        linarith only [h3]
      have hX : 0 < ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
      rw [hre, him, hnorm, henv] at hII
      have hA2_pos : 0 < A ^ 2 := pow_pos hA 2
      have hII' : ‖virasoroPsiTilde c g (-(w ^ 2))‖ * ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ ≤
          virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin y)⁻¹ := by
        have hexp_le : Real.exp (virasoroSigma c * (A * Real.sin y)) ≤ Real.exp 1 := by
          rw [hre, him] at hsig_bd
          exact Real.exp_le_exp.mpr hsig_bd
        have hpow : (A ^ 2) ^ (-(1 / 2 : ℝ)) = A⁻¹ := by
          rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hA.le]
          norm_num
          exact Real.rpow_neg_one A
        have hC0 := virasoroEnvC0_pos.le
        calc ‖virasoroPsiTilde c g (-(w ^ 2))‖ * ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖
            ≤ (virasoroEnvC0 * (‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖)⁻¹ *
                Real.exp (virasoroSigma c * (A * Real.sin y)) *
                (A ^ 2) ^ (-(1 / 2 : ℝ)) * (A * Real.sin y)⁻¹) *
                ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := by gcongr
          _ = virasoroEnvC0 * Real.exp (virasoroSigma c * (A * Real.sin y)) *
                ((A ^ 2) ^ (-(1 / 2 : ℝ)) * A⁻¹) * (Real.sin y)⁻¹ := by field_simp
          _ ≤ virasoroEnvC0 * Real.exp 1 * (A⁻¹ * A⁻¹) * (Real.sin y)⁻¹ := by rw [hpow]; gcongr
          _ = virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin y)⁻¹ := by
              rw [Real.rpow_neg hA.le, Real.rpow_two]; ring
      have hC0 := virasoroEnvC0_pos.le
      calc ‖lowerGoodGReg A c g w‖ * A
          = ((2 * Real.sin y) ^ 2 * A * A) * (‖virasoroPsiTilde c g (-(w ^ 2))‖ *
              ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖) := by
            rw [lowerGoodGReg_norm_arc hA c g hy]; ring
        _ ≤ ((2 * Real.sin y) ^ 2 * A * A) *
              (virasoroEnvC0 * Real.exp 1 * A ^ (-2 : ℝ) * (Real.sin y)⁻¹) := by
            have hk : 0 ≤ (2 * Real.sin y) ^ 2 * A * A := by positivity
            gcongr
        _ = 4 * virasoroEnvC0 * Real.exp 1 * Real.sin y * (A ^ 2 * A ^ (-2 : ℝ)) := by field_simp; ring
        _ = 4 * virasoroEnvC0 * Real.exp 1 * Real.sin y := by
            rw [Real.rpow_neg hA.le, Real.rpow_two, mul_inv_cancel₀ hA2_pos.ne', mul_one]
        _ ≤ 4 * virasoroEnvC0 * Real.exp 1 * φ₀ := by gcongr
  set F : ℝ → ℝ := fun y => ‖lowerGoodGReg A c g ((A : ℂ) * Complex.exp (y * I))‖ * A
  have hGan := lowerGood_GReg_analytic hc_1000 hA hA_ub hg.1
  have hF_cont : Continuous F := by
    have h1 : Continuous (fun y : ℝ => (A : ℂ) * Complex.exp (y * I)) := by fun_prop
    exact (hGan.continuousOn.comp_continuous h1 fun y => by
      rw [mem_closedBall_zero_iff, norm_arc hA]).norm.mul continuous_const
  set B : ℝ := 4 * L_top / A + 4 * virasoroEnvC0 * Real.exp 1 * φ₀
  have hFB : ∀ y ∈ Icc 0 π, F y ≤ B := fun y hy => by
    have hLA : 0 ≤ 4 * L_top / A := by positivity
    have hWd : 0 ≤ 4 * virasoroEnvC0 * Real.exp 1 * φ₀ := by have := virasoroEnvC0_pos; positivity
    rcases le_or_gt φ₀ (Real.sin y) with h | h
    · exact (h_cov hy h).trans (by linarith only [hWd])
    · exact (h_wedge hy h.le).trans (by linarith only [hLA])
  set a : ℝ := π / 2 * φ₀
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ≤ π / 2 := by dsimp [a]; nlinarith only [hφ0_le, Real.pi_pos]
  have hmid : ∀ y ∈ Icc a (π - a), F y ≤ 4 * L_top / A := by
    intro y hy
    refine h_cov ⟨by linarith only [ha0, hy.1], by linarith only [ha0, hy.2]⟩ ?_
    rcases le_total y (π / 2) with hh | hh
    · have hsin := Real.mul_le_sin (by linarith only [ha0, hy.1]) hh
      have h' : φ₀ ≤ 2 / π * y := by
        have := hy.1; dsimp [a] at this; field_simp; nlinarith only [this, Real.pi_pos]
      exact h'.trans hsin
    · have hsin := Real.mul_le_sin (x := π - y) (by linarith only [ha0, hy.2]) (by linarith only [hh])
      rw [Real.sin_pi_sub] at hsin
      have h' : φ₀ ≤ 2 / π * (π - y) := by
        have := hy.2; dsimp [a] at this; field_simp; nlinarith only [this, Real.pi_pos]
      exact h'.trans hsin
  have i1 : ∫ y in (0 : ℝ)..a, F y ≤ (a - 0) * B :=
    integral_le_const_mul hF_cont ha0 fun y hy => hFB y ⟨hy.1, by linarith only [hy.2, ha2, Real.pi_pos]⟩
  have i2 : ∫ y in a..(π - a), F y ≤ (π - a - a) * (4 * L_top / A) :=
    integral_le_const_mul hF_cont (by linarith only [ha2]) hmid
  have i3 : ∫ y in (π - a)..π, F y ≤ (π - (π - a)) * B :=
    integral_le_const_mul hF_cont (by linarith only [ha0]) fun y hy =>
      hFB y ⟨by linarith only [hy.1, ha2, Real.pi_pos], hy.2⟩
  have hsplit : ∫ y in (0 : ℝ)..π, F y =
      (∫ y in (0 : ℝ)..a, F y) + (∫ y in a..(π - a), F y) + ∫ y in (π - a)..π, F y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hF_cont.intervalIntegrable 0 (π - a))
      (hF_cont.intervalIntegrable (π - a) π), ← intervalIntegral.integral_add_adjacent_intervals
      (hF_cont.intervalIntegrable 0 a) (hF_cont.intervalIntegrable a (π - a))]
  have hsum : hdArcMass A (lowerGoodGReg A c g) ≤
      4 * π * L_top / A + 4 * π * virasoroEnvC0 * Real.exp 1 * φ₀ ^ 2 := by
    change ∫ y in (0 : ℝ)..π, F y ≤ _
    have he1 : (a - 0) * B + (π - a - a) * (4 * L_top / A) + (π - (π - a)) * B =
        4 * π * L_top / A + 4 * π * virasoroEnvC0 * Real.exp 1 * φ₀ ^ 2 := by
      dsimp [B, a]; ring
    linarith only [hsplit, i1, i2, i3, he1]
  have hφ0_sq : φ₀ ^ 2 ≤ C_ang ^ 2 / A := by
    have hR_eq : R = A ^ (2 : ℝ) := by rw [← hAR, Real.rpow_two]
    have hR32 : (R ^ (-(3 / 4 : ℝ))) ^ 2 = A ^ (-3 : ℝ) := by
      rw [hR_eq, ← Real.rpow_mul hA.le, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]
      congr 1; norm_num
    have hA3_A2 : A ^ (-3 : ℝ) * A ^ 2 = A⁻¹ := by
      rw [← Real.rpow_two A, ← Real.rpow_add hA, ← Real.rpow_neg_one]; norm_num
    calc φ₀ ^ 2 = C_ang ^ 2 * (R ^ (-(3 / 4 : ℝ))) ^ 2 * Real.sqrt (Real.log c) ^ 2 := by
          dsimp [φ₀]; ring
      _ = C_ang ^ 2 * A ^ (-3 : ℝ) * Real.log c := by rw [hR32, Real.sq_sqrt hlog_nn]
      _ ≤ C_ang ^ 2 * A ^ (-3 : ℝ) * A ^ 2 := by gcongr
      _ = C_ang ^ 2 / A := by rw [mul_assoc, hA3_A2, div_eq_mul_inv]
  have hC0 := virasoroEnvC0_pos.le
  calc hdArcMass A (lowerGoodGReg A c g)
      ≤ 4 * π * L_top / A + 4 * π * virasoroEnvC0 * Real.exp 1 * φ₀ ^ 2 := hsum
    _ ≤ 4 * π * L_top / A + 4 * π * virasoroEnvC0 * Real.exp 1 * (C_ang ^ 2 / A) := by gcongr
    _ = CSig / A := by rw [hCSig]; ring

/-- **Bundled top-scale data for `ctl:pass2`**:
for all sufficiently large `c`, every weakly feasible Virasoro test `(T, g)` with `T < Δ(a₁)` and
`T ≤ Δ(-virasoroAThr)` admits a radius `A` with `pass2ScaleLo * c^{1/3} ≤ A`, `A^2 ≤ virasoroAC c^2`,
`hdArcMass A (lowerGoodGReg A c g) ≤ CSig / A`, and `∫_{-A}^A t^2 ‖lowerGoodGReg A c g t‖ dt ≤ CS * A`. -/
theorem virasoro_pass2_top_data :
    ∃ CSig CS c₀ : ℝ, 0 ≤ CSig ∧ 0 ≤ CS ∧ virasoroCQEnv ≤ c₀ ∧
      ∀ {c T : ℝ}, c₀ ≤ c → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible (c / 12) T g →
        T < virasoroDeltaChart c (airyZero 1) →
        T ≤ virasoroDeltaChart c (-virasoroAThr) →
        ∃ A : ℝ, pass2ScaleLo * c ^ (1 / 3 : ℝ) ≤ A ∧ A ^ 2 ≤ virasoroAC c ^ 2 ∧
          hdArcMass A (lowerGoodGReg A c g) ≤ CSig / A ∧
          ∫ t in (-A)..A, t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖ ≤ CS * A := by
  have hb_lo : 0 < pass2ScaleLo := pass2ScaleLo_pos
  have hb_le : pass2ScaleLo ≤ pass2ScaleHi := pass2ScaleLo_le_hi
  have hb_hi_choice : pass2ScaleHi ≤ Real.sqrt 2 * virasoroBVChoice := le_rfl
  obtain ⟨K, c_mom, hK0, hc_mom_Q, hmom⟩ := virasoro_top_moments
  obtain ⟨c_cov, C_cov, hc_cov_Q, hC_cov, hcov⟩ :=
    virasoro_cov_window_log hb_lo hb_le hb_hi_choice
  obtain ⟨c_J, C_J, hc_J, _, hJ⟩ := theoremJ_unconditional
  obtain ⟨c_corL, _, hc_corL, _, hcorL⟩ := corL_virasoro
  set L_top : ℝ := C_cov * (K + 1)
  set C_ang : ℝ := pass2AngleC2
  set CSig : ℝ := 4 * π * L_top + 4 * π * virasoroEnvC0 * Real.exp 1 * C_ang ^ 2
  set CS : ℝ := pass2ScaleHi ^ 2 * K / pass2ScaleLo + virasoroAThr
  have hev : ∀ᶠ c : ℝ in atTop,
      1 ≤ pass2ScaleLo * c ^ (1 / 3 : ℝ) ∧
      C_J ≤ Aopt * c ^ (1 / 3 : ℝ) ∧
      C_ang * (pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ 1 ∧
      C_ang * (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log c) ≤ 1 ∧
      virasoroSigma c ≤ 1 ∧
      Real.log c ≤ pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) ∧
      max (max c_mom c_cov) (max c_J (max c_corL (max virasoroCQEnv 10000))) ≤ c := by
    have hc13 : Tendsto (fun c : ℝ => c ^ (1 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hc23 : Tendsto (fun c : ℝ => c ^ (2 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    have hlog_c23 : ∀ᶠ c : ℝ in atTop, Real.log c ≤ pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) := by
      let M := 6 / pass2ScaleLo ^ 2
      have h13 : Tendsto (fun c : ℝ => M * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul M
      filter_upwards [h13.eventually (Iic_mem_nhds zero_lt_one), eventually_gt_atTop (0 : ℝ)] with c hc1 hc0
      have hlog : Real.log c ≤ 6 * c ^ (1 / 3 : ℝ) := by
        have h := log_le_inv_alpha_rpow (by norm_num : (0 : ℝ) < 1 / 3) hc0
        norm_num at h
        have hc3 : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
        linarith only [h, hc3]
      have hc_eq : c ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hc_cancel : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add hc0, neg_add_cancel, Real.rpow_zero]
      have h6 : 6 ≤ pass2ScaleLo ^ 2 * c ^ (1 / 3 : ℝ) := by
        have h2 : 6 / pass2ScaleLo ^ 2 * c ^ (-(1 / 3 : ℝ)) ≤ 1 := hc1
        rw [div_mul_eq_mul_div, div_le_one (pow_pos hb_lo 2)] at h2
        calc 6 = (6 * c ^ (-(1 / 3 : ℝ))) * c ^ (1 / 3 : ℝ) := by rw [mul_assoc, hc_cancel, mul_one]
          _ ≤ pass2ScaleLo ^ 2 * c ^ (1 / 3 : ℝ) := by gcongr
      calc Real.log c ≤ 6 * c ^ (1 / 3 : ℝ) := hlog
        _ ≤ (pass2ScaleLo ^ 2 * c ^ (1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) := by gcongr
        _ = pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ) := by rw [mul_assoc, hc_eq]
    have hlog_sq1 : ∀ᶠ c : ℝ in atTop,
        C_ang * (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log c) ≤ 1 := by
      have ht : Tendsto (fun c : ℝ => (C_ang * pass2ScaleLo ^ (-(1 / 2 : ℝ)) * Real.sqrt 12) *
          c ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _
      filter_upwards [ht.eventually (Iic_mem_nhds zero_lt_one), eventually_ge_atTop (1 : ℝ)] with c hc1 hc_ge1
      have hc0 : 0 < c := by linarith
      have hlog : Real.log c ≤ 12 * c ^ (1 / 12 : ℝ) := by
        have h := log_le_inv_alpha_rpow (by norm_num : (0 : ℝ) < 1 / 12) hc0
        norm_num at h
        exact h
      have hsq : Real.sqrt (Real.log c) ≤ Real.sqrt 12 * c ^ (1 / 24 : ℝ) := by
        calc Real.sqrt (Real.log c) ≤ Real.sqrt (12 * c ^ (1 / 12 : ℝ)) := Real.sqrt_le_sqrt hlog
          _ = Real.sqrt 12 * Real.sqrt (c ^ (1 / 12 : ℝ)) := Real.sqrt_mul (by norm_num) _
          _ = Real.sqrt 12 * c ^ (1 / 24 : ℝ) := by
              rw [Real.sqrt_eq_rpow (c ^ (1 / 12 : ℝ)), ← Real.rpow_mul hc0.le]; norm_num
      have hpow1 : (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) =
          pass2ScaleLo ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by
        rw [Real.mul_rpow hb_lo.le (Real.rpow_nonneg hc0.le _), ← Real.rpow_mul hc0.le]; norm_num
      have hpow2 : c ^ (-(1 / 6 : ℝ)) * c ^ (1 / 24 : ℝ) = c ^ (-(1 / 8 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hCa := pass2AngleC2_pos.le
      calc C_ang * (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log c)
          ≤ C_ang * (pass2ScaleLo ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ))) *
              (Real.sqrt 12 * c ^ (1 / 24 : ℝ)) := by rw [hpow1]; gcongr
        _ = (C_ang * pass2ScaleLo ^ (-(1 / 2 : ℝ)) * Real.sqrt 12) * c ^ (-(1 / 8 : ℝ)) := by
              rw [← hpow2]; ring
        _ ≤ 1 := hc1
    have hlog_sq2 : ∀ᶠ c : ℝ in atTop,
        C_ang * (pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ 1 := by
      have ht : Tendsto (fun c : ℝ => (C_ang * (pass2ScaleLo ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt 12) *
          c ^ (-(11 / 24 : ℝ))) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 24)).const_mul _
      filter_upwards [ht.eventually (Iic_mem_nhds zero_lt_one), eventually_ge_atTop (1 : ℝ)] with c hc1 hc_ge1
      have hc0 : 0 < c := by linarith
      have hlog : Real.log c ≤ 12 * c ^ (1 / 12 : ℝ) := by
        have h := log_le_inv_alpha_rpow (by norm_num : (0 : ℝ) < 1 / 12) hc0
        norm_num at h
        exact h
      have hsq : Real.sqrt (Real.log c) ≤ Real.sqrt 12 * c ^ (1 / 24 : ℝ) := by
        calc Real.sqrt (Real.log c) ≤ Real.sqrt (12 * c ^ (1 / 12 : ℝ)) := Real.sqrt_le_sqrt hlog
          _ = Real.sqrt 12 * c ^ (1 / 24 : ℝ) := by
              rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (c ^ (1 / 12 : ℝ)),
                ← Real.rpow_mul hc0.le]; norm_num
      have hpow1 : (pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 4 : ℝ)) =
          (pass2ScaleLo ^ 2) ^ (-(3 / 4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
        rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg hc0.le _), ← Real.rpow_mul hc0.le]; norm_num
      have hpow2 : c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 24 : ℝ) = c ^ (-(11 / 24 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hCa := pass2AngleC2_pos.le
      calc C_ang * (pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)
          ≤ C_ang * ((pass2ScaleLo ^ 2) ^ (-(3 / 4 : ℝ)) * c ^ (-(1 / 2 : ℝ))) *
              (Real.sqrt 12 * c ^ (1 / 24 : ℝ)) := by rw [hpow1]; gcongr
        _ = (C_ang * (pass2ScaleLo ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt 12) * c ^ (-(11 / 24 : ℝ)) := by
              rw [← hpow2]; ring
        _ ≤ 1 := hc1
    have hsig1 : ∀ᶠ c : ℝ in atTop, virasoroSigma c ≤ 1 := by
      have ht : Tendsto (fun c : ℝ => (6 * virasoroEnvC1) * c ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul _
      filter_upwards [ht.eventually (Iic_mem_nhds zero_lt_one), eventually_ge_atTop (1 : ℝ)] with c hc1 hc_ge1
      have hc0 : 0 < c := by linarith
      have hlog : Real.log c ≤ 6 * c ^ (1 / 6 : ℝ) := by
        have h := log_le_inv_alpha_rpow (by norm_num : (0 : ℝ) < 1 / 6) hc0
        norm_num at h
        exact h
      have hpow : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 6 : ℝ) = c ^ (-(1 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hC1 := virasoroEnvC1_pos.le
      calc virasoroSigma c = virasoroEnvC1 * (c ^ (-(1 / 3 : ℝ)) * Real.log c) := by unfold virasoroSigma; ring
        _ ≤ virasoroEnvC1 * (c ^ (-(1 / 3 : ℝ)) * (6 * c ^ (1 / 6 : ℝ))) := by gcongr
        _ = (6 * virasoroEnvC1) * (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 6 : ℝ)) := by ring
        _ = (6 * virasoroEnvC1) * c ^ (-(1 / 6 : ℝ)) := by rw [hpow]
        _ ≤ 1 := hc1
    filter_upwards [(hc13.const_mul_atTop hb_lo).eventually_ge_atTop 1,
      (hc13.const_mul_atTop Aopt_pos).eventually_ge_atTop C_J,
      hlog_sq2, hlog_sq1, hsig1, hlog_c23,
      eventually_ge_atTop (max (max c_mom c_cov) (max c_J (max c_corL (max virasoroCQEnv 10000))))] with
        c h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.1 hev
  refine ⟨CSig, CS, max c_ev virasoroCQEnv, ?_, ?_, le_max_right _ _, ?_⟩
  · have := virasoroEnvC0_pos; have := Real.pi_pos; dsimp [CSig, L_top]; positivity
  · have := virasoroAThr_pos; dsimp [CS]; positivity
  intro c T hc g hg hT_a1 hT_hi
  obtain ⟨hA_ge1, hCJ_le, hφ0_le1, hAφ0_le1, hsig_le1, hlog_A2, hmax⟩ := hc_ev c ((le_max_left _ _).trans hc)
  have hc_mom : c_mom ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hmax)
  have hc_cov : c_cov ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hmax)
  have hc_J : c_J ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have hc_corL : c_corL ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hmax))
  have hc_Q : virasoroCQEnv ≤ c := (le_max_right _ _).trans hc
  have hc_10000 : 10000 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hmax)))
  have hc_pos : 0 < c := by linarith
  have hc_1000 : 1000 ≤ c := by linarith
  have hT_lo : virasoroDeltaChart c 0 ≤ T := by
    rw [virasoroDeltaChart_zero]
    have hJc := hJ (by linarith : c_J ≤ c + 1) (by simpa [add_sub_cancel_right] using hg)
    simp only [add_sub_cancel_right] at hJc; linarith
  have ha1_uT : airyZero 1 < virasoroUT c T := ((hcorL hc_corL hg).2 hT_a1).1
  obtain ⟨R, hR_lo, hR_hi, hR_thr, hB_sum⟩ := hmom hc_mom hg hT_a1 hT_hi
  have hR_pos : 0 < R := lt_of_lt_of_le virasoroAThr_pos hR_thr
  set A : ℝ := Real.sqrt R
  have hA : 0 < A := Real.sqrt_pos.mpr hR_pos
  have hAR : A ^ 2 = R := Real.sq_sqrt hR_pos.le
  have hA_lo : pass2ScaleLo * c ^ (1 / 3 : ℝ) ≤ A := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    simpa only [Nat.cast_ofNat, show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num] using hR_lo
  have hA_hi : A ≤ pass2ScaleHi * c ^ (1 / 3 : ℝ) := by
    have hb_hi : 0 < pass2ScaleHi := hb_lo.trans_le hb_le
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    rw [show (1 / 3 : ℝ) * (2 : ℕ) = 2 / 3 by norm_num]
    linarith
  have hR_ub_AC : R ≤ virasoroAC c ^ 2 := by
    rw [virasoroAC_sq c hc_pos.le]
    have h1 : pass2ScaleHi ^ 2 ≤ 2 * virasoroBV ^ 2 := by
      rw [pass2ScaleHi_sq]
      have := virasoroBVChoice_pos; have := virasoroBVChoice_le; gcongr
    have h2 : R ≤ pass2ScaleHi ^ 2 * c ^ (2 / 3 : ℝ) := by linarith
    exact h2.trans (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc_pos.le _))
  have hA_ub : A ^ 2 ≤ virasoroAC c ^ 2 := hAR.symm ▸ hR_ub_AC
  -- 1. Arc mass bound
  have hAφ0_le : A * (C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)) ≤ 1 := by
    have hR_eq : R = A ^ (2 : ℝ) := by rw [← hAR, Real.rpow_two]
    have hR34 : R ^ (-(3 / 4 : ℝ)) = A ^ (-(3 / 2 : ℝ)) := by
      rw [hR_eq, ← Real.rpow_mul hA.le]; norm_num
    have hAR34 : A * R ^ (-(3 / 4 : ℝ)) = A ^ (-(1 / 2 : ℝ)) := by
      rw [hR34]
      conv_lhs => arg 1; rw [← Real.rpow_one A]
      rw [← Real.rpow_add hA]
      congr 1; norm_num
    have hA_m12 : A ^ (-(1 / 2 : ℝ)) ≤ (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hA_lo (by norm_num)
    have hCa := pass2AngleC2_pos.le
    calc A * (C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c))
        = C_ang * (A * R ^ (-(3 / 4 : ℝ))) * Real.sqrt (Real.log c) := by ring
      _ = C_ang * A ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log c) := by rw [hAR34]
      _ ≤ C_ang * (pass2ScaleLo * c ^ (1 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log c) := by gcongr
      _ ≤ 1 := hAφ0_le1
  have hφ0_le : C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ 1 := by
    have h1 : R ^ (-(3 / 4 : ℝ)) ≤ (pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hR_lo (by norm_num)
    have hCa := pass2AngleC2_pos.le
    calc C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)
        ≤ C_ang * (pass2ScaleLo ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) := by gcongr
      _ ≤ 1 := hφ0_le1
  have hS_arc : hdArcMass A (lowerGoodGReg A c g) ≤ CSig / A := by
    refine virasoro_top_arcMass_le hc_Q hc_1000 (by linarith only [hc_10000]) hA hAR hA_ub
      pass2AngleC2_pos.le (by dsimp [L_top]; positivity) rfl hg hsig_le1 (by rw [hAR]; exact hlog_A2.trans hR_lo)
      hAφ0_le hφ0_le fun {u} hu_im hu_norm hu_ang => ?_
    have hL_le : C_cov * (c ^ (1 / 3 : ℝ) * (virasoroBandB1 c R T g + virasoroBandB2 c R g) + 1) ≤ L_top := by
      have hc13 : c ^ (1 / 3 : ℝ) * (virasoroBandB1 c R T g + virasoroBandB2 c R g) ≤ K := by
        have hcs : 0 ≤ c ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc_pos.le _
        calc c ^ (1 / 3 : ℝ) * (virasoroBandB1 c R T g + virasoroBandB2 c R g)
            ≤ c ^ (1 / 3 : ℝ) * (K * c ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hB_sum hcs
          _ = K * (c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by ring
          _ = K * 1 := by rw [← Real.rpow_add hc_pos, add_neg_cancel, Real.rpow_zero]
          _ = K := mul_one _
      dsimp [L_top]; gcongr
    have hu_re_nn : 0 ≤ (u ^ (1 / 2 : ℂ)).re := by
      have hCa := pass2AngleC2_pos.le
      have hR_nn : 0 ≤ R := hR_pos.le
      have hln : 0 ≤ Real.log c := Real.log_nonneg (by linarith only [hc_10000])
      exact (by positivity : 0 ≤ C_ang * R ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) * Real.sqrt ‖u‖).trans hu_ang
    have h0 : 0 ≤ airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ)) := by
      have := airyEnv_pos u; positivity
    exact (hcov hc_cov hR_lo hR_hi hR_thr hg hT_lo hT_hi hu_im hu_norm hu_ang).trans (by
      calc _ = C_cov * (c ^ (1 / 3 : ℝ) * (virasoroBandB1 c R T g + virasoroBandB2 c R g) + 1) *
            (airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) := by ring
        _ ≤ L_top * (airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(3 / 4 : ℝ))) := by gcongr
        _ = _ := by ring)
  -- 2. Second moment bound
  have hS2 : ∫ t in (-A)..A, t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖ ≤ CS * A := by
    have hm2 := virasoro_top_secondMoment_le hc_Q hA hAR hR_thr hR_ub_AC hg hT_lo hT_hi ha1_uT
    have hB1_le : virasoroBandB1 c R T g ≤ K * c ^ (-(1 / 3 : ℝ)) := by
      have := virasoroBandB2_nonneg hc_Q hR_thr hR_ub_AC hg hT_hi
      linarith
    have hR_le : R ≤ pass2ScaleHi ^ 2 * c ^ (2 / 3 : ℝ) := by linarith
    have hc23_pow : c ^ (2 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = c ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    have hc13_le : c ^ (1 / 3 : ℝ) ≤ A / pass2ScaleLo := by
      rw [le_div_iff₀ hb_lo]; linarith
    have hRB1 : R * virasoroBandB1 c R T g ≤ (pass2ScaleHi ^ 2 * K / pass2ScaleLo) * A := by
      calc R * virasoroBandB1 c R T g
          ≤ (pass2ScaleHi ^ 2 * c ^ (2 / 3 : ℝ)) * (K * c ^ (-(1 / 3 : ℝ))) := by
            have := virasoroBandB1_nonneg hc_Q hR_thr hR_ub_AC hg hT_lo hT_hi
            gcongr
        _ = pass2ScaleHi ^ 2 * K * (c ^ (2 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by ring
        _ = pass2ScaleHi ^ 2 * K * c ^ (1 / 3 : ℝ) := by rw [hc23_pow]
        _ ≤ pass2ScaleHi ^ 2 * K * (A / pass2ScaleLo) := by gcongr
        _ = (pass2ScaleHi ^ 2 * K / pass2ScaleLo) * A := by ring
    have hAThr_le : virasoroAThr ≤ virasoroAThr * A := by
      have := virasoroAThr_pos.le
      nlinarith [hA_ge1, hA_lo]
    calc ∫ t in (-A)..A, t ^ 2 * ‖lowerGoodGReg A c g (t : ℂ)‖
        ≤ R * virasoroBandB1 c R T g + virasoroAThr := hm2
      _ ≤ (pass2ScaleHi ^ 2 * K / pass2ScaleLo) * A + virasoroAThr * A := add_le_add hRB1 hAThr_le
      _ = CS * A := by dsimp [CS]; ring
  exact ⟨A, hA_lo, hA_ub, hS_arc, hS2⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_top_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_top_moments

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoro_pass2_top_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.virasoro_pass2_top_data

end FormalResearch.ModularBootstrap.FiveTerm
