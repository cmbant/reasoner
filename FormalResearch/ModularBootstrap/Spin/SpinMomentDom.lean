module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentMid

/-!
# Mid-band domination for `SPIN-M`

Source: `CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex`
(`sd:spinmoment-combbounds`, `sd:spinmoment-window-pair`).

* `spinMoment_mid_band_dom`: on `x ∈ [xiStar + λ Σ₀, xiStar + 1]`,
  `0 < g₁(c' x²/3)` and `|K^* g₅(c' x²/3)| ≤ C_mid c' g₁(c' x²/3)` where
  `g₁ = bumpG virasoroProblem (rpParams 0).bumpData 1 (1/4) (designSigma1 0) c'`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Upper
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Hankel
open FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Tail
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. Pointwise mid-band upper bound for `g₅` -/

private lemma bumpBc_combProfile_mid_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ Sg0 C_h : ℝ, 0 < Sg0 ∧ 0 < C_h ∧ ∀ᶠ c' in atTop, ∀ y : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ y → y ≤ xiStar + 1 →
        |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * y ^ 2 / 3)| ≤
          C_h * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
  set d5 := (rpParams 4).bumpData
  set M := supSigma1 σs N hN
  set Sg0 := max (4 * max (phiQuantile ((N : ℝ) + 2)) M) (phiQuantile 5 + 1)
  have hPhi5 : 0 < phiQuantile 5 := by
    rw [show (5 : ℝ) = ((3 : ℕ) : ℝ) + 2 by norm_num]
    exact phiQuantile_succ_succ_pos 3
  have hSg0 : 0 < Sg0 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨E, _, hwidth⟩ := designWidth1_bounds hη0 hη1
  obtain ⟨K, hK0, hnorm⟩ := designComb_norm_le_exp_ref 1 N le_rfl hN M E (η₀ := 1 / 4)
    (by norm_num) le_rfl
  obtain ⟨Cband, hCband, hband⟩ := refComb_band_bound (f := 1) le_rfl (η₀ := 1 / 4) (r₀ := 1)
    (by norm_num) le_rfl
  have hband4 := hband 4 (by omega)
  set C_ref_bnd := Cband * (4 * √2 * Real.cosh (π * 1 / 2) / π) ^ (3 / 2 : ℝ)
  have hCref : 0 < C_ref_bnd := by
    have := Real.pi_pos; have := Real.cosh_pos (π * 1 / 2)
    positivity
  set C_h := max (bumpC d5 (1 / 4)) 1 * 4 * Real.exp (K / Sg0) * C_ref_bnd
  have hCh : 0 < C_h := by positivity
  refine ⟨Sg0, C_h, hSg0, hCh, ?_⟩
  filter_upwards [combProfile_bumped_eq d5, bumpFactor_one_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl, hwidth, hnorm, hband4,
    eventually_gt_atTop (0 : ℝ)] with c' hval hbf1 hbfC hw hn hrf hc' y hy_lo hy_hi
  have hlam0 : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hyx : 0 < y - xiStar := by linarith [mul_pos hlam0 hSg0]
  have hy0 : 0 ≤ y := by linarith [xiStar_pos]
  have hNcut := le_bumpCut d5 N c'
  have hveq := hval N (bumpCut d5 N c') σs (designWidth1 c' η) hN hNcut (c' * y ^ 2 / 3)
  have hbc_eq : bumpBc d5 N η σs c' = bumpedComb d5 c' 1 N (bumpCut d5 N c') (1 / 4) σs
      (designWidth1 c' η) := rfl
  rw [← hbc_eq, xOf_mul_sq_div_three hc' hy0] at hveq
  have hbf0 : 0 ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') y :=
    zero_le_one.trans (hbf1 N (bumpCut d5 N c') y)
  have hbf_le : bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') y ≤ max (bumpC d5 (1 / 4)) 1 :=
    (hbfC N (bumpCut d5 N c') y hy0).trans (le_max_left _ _)
  have hys : xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ y := by
    have h1 : 4 * max (phiQuantile ((N : ℝ) + 2)) M ≤ Sg0 := le_max_left _ _
    have h2 : 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ lambdaComb c' * Sg0 := by
      rw [mul_comm (lambdaComb c') Sg0]
      exact mul_le_mul_of_nonneg_right h1 hlam0.le
    linarith
  have hn' := hn σs (designWidth1 c' η)
    (fun k hk1 hkN => abs_le_supSigma1 σs N hN hk1 hkN)
    (fun k hk1 _ => hw k hk1.le) y hys
  have hKx : K * (lambdaComb c' / (y - xiStar)) ≤ K / Sg0 := by
    have hdiv : lambdaComb c' / (y - xiStar) ≤ 1 / Sg0 := by
      rw [div_le_div_iff₀ hyx hSg0, one_mul]
      linarith
    calc K * (lambdaComb c' / (y - xiStar)) ≤ K * (1 / Sg0) := mul_le_mul_of_nonneg_left hdiv hK0
      _ = K / Sg0 := by ring
  have hχ5 : chiQuantile c' ((4 + 1 : ℕ) : ℝ) ≤ y := by
    have hs := (siteRadius_bounds hc' (by norm_num : (1 / 4 : ℝ) ≤ ((4 + 1 : ℕ) : ℝ))).2
    unfold siteRadius at hs
    have hphi : lambdaComb c' * phiQuantile ((4 + 1 : ℕ) : ℝ) ≤ lambdaComb c' * Sg0 := by
      have : phiQuantile ((4 + 1 : ℕ) : ℝ) ≤ Sg0 := by
        calc phiQuantile ((4 + 1 : ℕ) : ℝ) = phiQuantile 5 := by norm_num
          _ ≤ phiQuantile 5 + 1 := by linarith
          _ ≤ Sg0 := le_max_right _ _
      exact mul_le_mul_of_nonneg_left this hlam0.le
    linarith
  have hrf' := hrf y hχ5 hy_hi
  have hrf_exp : ‖refComb c' 1 (1 / 4) (y : ℂ)‖ ≤
      C_ref_bnd * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
    have h1 : ‖refComb c' 1 (1 / 4) (y : ℂ)‖ ≤
        (Cband * (4 * √2 * Real.cosh (π * 1 / 2) / (π * (y - xiStar))) ^ (2 * ((1 : ℝ) - 1 / 4))) *
          Real.exp (-c' * besselL y) := by
      calc ‖refComb c' 1 (1 / 4) (y : ℂ)‖
          = (‖refComb c' 1 (1 / 4) (y : ℂ)‖ * Real.exp (c' * besselL y)) * Real.exp (-c' * besselL y) := by
            rw [mul_assoc, ← Real.exp_add, show c' * besselL y + -c' * besselL y = 0 by ring,
              Real.exp_zero, mul_one]
        _ ≤ (Cband * (4 * √2 * Real.cosh (π * 1 / 2) / (π * (y - xiStar))) ^
              (2 * ((1 : ℝ) - 1 / 4))) * Real.exp (-c' * besselL y) := by
            simpa only [Nat.cast_one] using mul_le_mul_of_nonneg_right hrf' (Real.exp_pos _).le
    have h2 : (4 * √2 * Real.cosh (π * 1 / 2) / (π * (y - xiStar))) ^ (2 * ((1 : ℝ) - 1 / 4)) =
        (4 * √2 * Real.cosh (π * 1 / 2) / π) ^ (3 / 2 : ℝ) * (y - xiStar) ^ (-(3 / 2 : ℝ)) := by
      rw [show (2 * ((1 : ℝ) - 1 / 4) : ℝ) = 3 / 2 by norm_num]
      rw [show 4 * √2 * Real.cosh (π * 1 / 2) / (π * (y - xiStar)) =
          (4 * √2 * Real.cosh (π * 1 / 2) / π) * (y - xiStar)⁻¹ by field_simp]
      rw [Real.mul_rpow (by have := Real.pi_pos; positivity) (inv_nonneg.mpr hyx.le),
        Real.inv_rpow hyx.le, ← Real.rpow_neg hyx.le]
    rw [h2] at h1
    dsimp [C_ref_bnd]
    linarith
  have hsech : ‖sechSqProfile (y : ℂ)‖ ≤ 4 := by
    have hs := norm_sechSqProfile_ofReal_le y
    have hexp : Real.exp (-π * |y|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := Real.pi_pos; nlinarith [abs_nonneg y])
    linarith
  have hprof_le : |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η))
      (c' * y ^ 2 / 3)| ≤
      4 * Real.exp (K / Sg0) * (C_ref_bnd * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y)) := by
    unfold combProfile combH0
    rw [xOf_mul_sq_div_three hc' hy0]
    calc |(sechSqProfile (y : ℂ) * designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (y : ℂ)).re|
        ≤ ‖sechSqProfile (y : ℂ) * designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (y : ℂ)‖ :=
          Complex.abs_re_le_norm _
      _ = ‖sechSqProfile (y : ℂ)‖ * ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (y : ℂ)‖ :=
          norm_mul _ _
      _ ≤ 4 * (Real.exp (K * (lambdaComb c' / (y - xiStar))) * ‖refComb c' 1 (1 / 4) (y : ℂ)‖) :=
          mul_le_mul hsech hn' (norm_nonneg _) (by positivity)
      _ ≤ 4 * (Real.exp (K / Sg0) * (C_ref_bnd * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-c' * besselL y))) := by gcongr
      _ = _ := by ring
  rw [hveq, abs_mul, abs_of_nonneg hbf0]
  calc bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') y *
        |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) (c' * y ^ 2 / 3)|
      ≤ max (bumpC d5 (1 / 4)) 1 *
          (4 * Real.exp (K / Sg0) * (C_ref_bnd * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-c' * besselL y))) :=
        mul_le_mul hbf_le hprof_le (abs_nonneg _) (by positivity)
    _ = C_h * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
        dsimp [C_h]; ring

private lemma bumpBc_hankel_mid_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ C_hh > 0, ∀ᶠ c' in atTop, ∀ y : ℝ, xiStar < y → y ≤ xiStar + 1 →
      |hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
          (c' * y ^ 2 / 3)| ≤
        C_hh * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
  set d5 := (rpParams 4).bumpData
  obtain ⟨K₅, hK₅, hwin5⟩ := bump_hat_window_bound spinMomentW5Prob d5 N hN hη0 hη1 σs
  obtain ⟨c_K, hcK, hKlo⟩ := kernelK5_mul_deriv_lower
  obtain ⟨_, _, _, C_p, _, _, _, _, hCp, _, hpk⟩ :=
    phase_packageP 4 1 le_rfl (η₀ := 1 / 4) (P := 2) (θ := 2 / 5)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, hsdv⟩ := sdvPrefactor_mid_regionII_bound
  have hC_ev : ∀ᶠ c' in atTop, C_p * c' ^ (-1 + 3 * (2 / 5 : ℝ) / 2) ≤ 1 := by
    have h0 : Tendsto (fun c' : ℝ => C_p * c' ^ (-(2 / 5 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).const_mul C_p
    filter_upwards [h0.eventually_le_const zero_lt_one] with c' hc'
    rwa [show (-1 + 3 * (2 / 5 : ℝ) / 2 : ℝ) = -(2 / 5 : ℝ) by norm_num]
  refine ⟨max (K₅ / c_K) (2 * Cs) + 1, by positivity, ?_⟩
  filter_upwards [hwin5, hKlo, bumpSig_phaseHyp d5 N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (by norm_num) le_rfl,
    hpk, hsdv, hC_ev, eventually_ge_atTop (1 : ℝ)]
    with c' hw5 hKl hph hin hpkc hsdvc hCc hc1 y hy_gt hy_hi
  have hc' : 0 < c' := by linarith
  by_cases hy_reg : y ≤ xiStar + c' ^ (-(2 / 5 : ℝ))
  · have hy_mem : y ∈ Icc (xiStar / 2) (xiStar + 1) := ⟨by linarith [xiStar_pos], hy_hi⟩
    have hKl' := hKl y hy_mem
    have hw5' := hw5 (bumpCut d5 N c') (le_bumpCut d5 N c') y hy_mem.1
    rw [show bumpSigComb d5 c' N (bumpCut d5 N c') η σs = bumpBc d5 N η σs c' from rfl] at hw5'
    rw [spinMomentW5Prob_cardyV] at hw5'
    have hden_pos : 0 < c_K * √c' * Real.exp (c' * besselL y) := by positivity
    have hK5_pos : 0 < kernelK 5 (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) :=
      lt_of_lt_of_le hden_pos hKl'
    have habs_mul : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)| *
        (c_K * √c' * Real.exp (c' * besselL y)) ≤ K₅ * c' := by
      have h1 : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)| *
          (kernelK 5 (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3)) ≤ K₅ * c' := by
        have hw5'' : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3) *
            (kernelK 5 (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3))| ≤ K₅ * c' := by
          change |hankelTransform spinMomentW5Prob.w (combProfile c' (bumpBc d5 N η σs c'))
            (c' * y ^ 2 / 3) * (kernelK 5 (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3))| ≤ K₅ * c'
          simpa only [mul_assoc] using hw5'
        rw [abs_mul, abs_of_pos hK5_pos] at hw5''
        exact hw5''
      exact le_trans (mul_le_mul_of_nonneg_left hKl' (abs_nonneg _)) h1
    have hsqrt_le : √c' ≤ (y - xiStar) ^ (-(3 / 2 : ℝ)) := by
      have hyx : 0 < y - xiStar := sub_pos.mpr hy_gt
      have hsub : y - xiStar ≤ c' ^ (-(2 / 5 : ℝ)) := by linarith
      have hrpow1 : (c' ^ (-(2 / 5 : ℝ))) ^ (-(3 / 2 : ℝ)) ≤ (y - xiStar) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hyx hsub (by norm_num)
      have hrpow2 : (c' ^ (-(2 / 5 : ℝ))) ^ (-(3 / 2 : ℝ)) = c' ^ (3 / 5 : ℝ) := by
        rw [← Real.rpow_mul hc'.le]; norm_num
      have hrpow3 : √c' ≤ c' ^ (3 / 5 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      linarith
    have hbd : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)| ≤
        K₅ / c_K * √c' * Real.exp (-c' * besselL y) := by
      have h1 : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)| ≤
          (K₅ * c') / (c_K * √c' * Real.exp (c' * besselL y)) :=
        (le_div_iff₀ hden_pos).mpr habs_mul
      have h2 : (K₅ * c') / (c_K * √c' * Real.exp (c' * besselL y)) =
          K₅ / c_K * √c' * Real.exp (-c' * besselL y) := by
        have hsq : √c' ≠ 0 := (Real.sqrt_pos.mpr hc').ne'
        have he0 : Real.exp (c' * besselL y) ≠ 0 := (Real.exp_pos _).ne'
        rw [show -c' * besselL y = -(c' * besselL y) by ring, Real.exp_neg]
        field_simp
        rw [Real.sq_sqrt hc'.le]
      exact h1.trans_eq h2
    calc |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)|
        ≤ K₅ / c_K * √c' * Real.exp (-c' * besselL y) := hbd
      _ ≤ (K₅ / c_K) * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by gcongr
      _ ≤ (max (K₅ / c_K) (2 * Cs) + 1) * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-c' * besselL y) := by
          gcongr
          linarith [le_max_left (K₅ / c_K) (2 * Cs)]
  · push Not at hy_reg
    have hph_cut : PhaseHyp c' 1 (bumpCut d5 N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps d5 c' N (1 / 4) (designWidth1 c' η)) 2 := hph (bumpCut d5 N c') (le_bumpCut d5 N c')
    have hph_adm := hph_cut
    obtain ⟨hfN, hA, -⟩ := hph_adm
    have hI : InnerCombHyp c' (bumpBc d5 N η σs c') := hin (bumpCut d5 N c') _ _ hfN hA
    obtain ⟨_, _, hd⟩ := hI.combProfile_decay hc'
    have hy0 : 0 < y := xiStar_pos.trans hy_gt
    have ht : 0 < c' * y ^ 2 / 3 := by positivity
    have hH := hI.edgeHankelP_eq 4 hc' hd ht
    have hb_eq : bumpBc d5 N η σs c' =
        designComb c' 1 (bumpCut d5 N c') (1 / 4) (bumpSigma c' N σs)
          (bumpEps d5 c' N (1 / 4) (designWidth1 c' η)) := rfl
    have hprof : combH0 (bumpBc d5 N η σs c') =
        designProfile c' 1 (bumpCut d5 N c') (1 / 4) (bumpSigma c' N σs)
          (bumpEps d5 c' N (1 / 4) (designWidth1 c' η)) := by
      rw [hb_eq, combH0_designComb]
    rw [hprof] at hH
    obtain ⟨-, -, htrans, -⟩ := hpkc (bumpCut d5 N c') _ _ hph_cut
    have htrans' := htrans y hy_reg.le
    have hsdv' := hsdvc y hy_gt hy_hi
    have hhank_norm : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)| =
        ‖edgeHankelP 4 c' (designProfile c' 1 (bumpCut d5 N c') (1 / 4) (bumpSigma c' N σs)
          (bumpEps d5 c' N (1 / 4) (designWidth1 c' η))) (c' * y ^ 2 / 3)‖ := by
      rw [hH, Complex.norm_real, Real.norm_eq_abs]
    rw [hhank_norm]
    have hnonneg : 0 ≤ combAmplitude c' y * fwsdRatio 4 y := by
      unfold combAmplitude fwsdRatio sdvPrefactor
      positivity
    calc ‖edgeHankelP 4 c' _ (c' * y ^ 2 / 3)‖
        ≤ combAmplitude c' y * fwsdRatio 4 y * (1 + C_p * c' ^ (-1 + 3 * (2 / 5 : ℝ) / 2)) :=
          htrans'
      _ ≤ (Cs * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y)) * (1 + 1) := by
          gcongr
      _ = 2 * Cs * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by ring
      _ ≤ (max (K₅ / c_K) (2 * Cs) + 1) * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-c' * besselL y) := by
          gcongr
          linarith [le_max_right (K₅ / c_K) (2 * Cs)]

/-- Mid-band pointwise exponential bound on `bumpG` for `w = 5`:
`|g₅(c' y²/3)| ≤ C_g (y - ξ_*)^(-3/2) exp(-c' L(y))` on `ξ_* + λ Σ₀ ≤ y ≤ ξ_* + 1`. -/
theorem bumpG_mid_exp_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ Sg0 C_g : ℝ, 0 < Sg0 ∧ 0 < C_g ∧ ∀ᶠ c' in atTop, ∀ y : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ y → y ≤ xiStar + 1 →
        |bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' (c' * y ^ 2 / 3)| ≤
          C_g * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
  obtain ⟨Sg0, C_h, hSg0, hCh, hh⟩ := bumpBc_combProfile_mid_le N hN hη0 hη1 σs
  obtain ⟨C_hh, hChh, hh'⟩ := bumpBc_hankel_mid_le N hN hη0 hη1 σs
  refine ⟨Sg0, (C_h + C_hh) / 2, hSg0, by positivity, ?_⟩
  filter_upwards [hh, hh', eventually_gt_atTop (0 : ℝ)] with c' hc1 hc2 hc' y hy_lo hy_hi
  have hlam0 : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hy_gt : xiStar < y := lt_of_lt_of_le (by linarith [mul_pos hlam0 hSg0]) hy_lo
  unfold bumpG pairOdd
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have hsum := add_le_add (hc1 y hy_lo hy_hi) (hc2 y hy_gt hy_hi)
  calc |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * y ^ 2 / 3) -
          hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
            (c' * y ^ 2 / 3)| / 2
      ≤ (|combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * y ^ 2 / 3)| +
          |hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
            (c' * y ^ 2 / 3)|) / 2 :=
        div_le_div_of_nonneg_right (abs_sub _ _) zero_le_two
    _ ≤ (C_h * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) +
          C_hh * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y)) / 2 :=
        div_le_div_of_nonneg_right hsum zero_le_two
    _ = (C_h + C_hh) / 2 * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by ring

private lemma volterra_exp_dom (δ : ℝ) (hδ : 0 < δ) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (3 * r / 2 + t / 2) * Real.exp (-δ * √t) ≤
      8 * (3 * r / 2 + 1 / 2) * max 1 (720 / δ ^ 6) * (1 + t) ^ (-2 : ℝ) := by
  have hpow6 := Real.pow_div_factorial_le_exp (δ * √t) (by positivity) 6
  have hfact6 : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num
  rw [hfact6] at hpow6
  have ht3 : t ^ 3 * Real.exp (-δ * √t) ≤ 720 / δ ^ 6 := by
    have hpow_eq : (δ * √t) ^ 6 = δ ^ 6 * t ^ 3 := by
      rw [mul_pow, show (√t) ^ 6 = (√t ^ 2) ^ 3 by ring, Real.sq_sqrt ht]
    rw [hpow_eq] at hpow6
    have hpow6' : δ ^ 6 * t ^ 3 ≤ 720 * Real.exp (δ * √t) := by
      have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 720)).mp hpow6
      linarith
    have h1 : δ ^ 6 * t ^ 3 * Real.exp (-δ * √t) ≤ 720 := by
      calc δ ^ 6 * t ^ 3 * Real.exp (-δ * √t)
          ≤ (720 * Real.exp (δ * √t)) * Real.exp (-δ * √t) := by gcongr
        _ = 720 := by
            rw [mul_assoc, ← Real.exp_add, show δ * √t + -δ * √t = 0 by ring, Real.exp_zero,
              mul_one]
    have hδ6 : 0 < δ ^ 6 := pow_pos hδ 6
    calc t ^ 3 * Real.exp (-δ * √t) = (δ ^ 6 * t ^ 3 * Real.exp (-δ * √t)) / δ ^ 6 := by
          field_simp
      _ ≤ 720 / δ ^ 6 := div_le_div_of_nonneg_right h1 hδ6.le
  have hexp_le1 : Real.exp (-δ * √t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := mul_nonneg hδ.le (Real.sqrt_nonneg t); linarith)
  have ht_bd : t ≤ 1 + t ^ 3 := by
    by_cases ht1 : t ≤ 1
    · linarith [pow_nonneg ht 3]
    · have : 1 ≤ t := by linarith
      have h12 : 1 ≤ t ^ 2 := by nlinarith
      have hsq : t ≤ t ^ 3 := by nlinarith
      linarith
  have ht2_bd : t ^ 2 ≤ 1 + t ^ 3 := by
    by_cases ht1 : t ≤ 1
    · have : t ^ 2 ≤ 1 := by nlinarith
      linarith [pow_nonneg ht 3]
    · have : 1 ≤ t := by linarith
      nlinarith
  have hsub1 : (1 + t) ^ 2 * (3 * r / 2 + t / 2) ≤ 4 * (3 * r / 2 + 1 / 2) * (1 + t ^ 3) := by
    have hp0 : 0 ≤ t ^ 3 := pow_nonneg ht 3
    have hp1 : 1 + 2 * t + t ^ 2 ≤ 4 * (1 + t ^ 3) := by linarith
    have hp2 : t + 2 * t ^ 2 + t ^ 3 ≤ 4 * (1 + t ^ 3) := by linarith
    have hsum : (1 + t) ^ 2 * (3 * r / 2 + t / 2) =
        3 * r / 2 * (1 + 2 * t + t ^ 2) + 1 / 2 * (t + 2 * t ^ 2 + t ^ 3) := by ring
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ 3 * r / 2),
      mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ (1 / 2 : ℝ))]
  have hM1 : 1 ≤ max 1 (720 / δ ^ 6) := le_max_left _ _
  have hM2 : 720 / δ ^ 6 ≤ max 1 (720 / δ ^ 6) := le_max_right _ _
  have h1t3 : (1 + t) ^ 2 * ((3 * r / 2 + t / 2) * Real.exp (-δ * √t)) ≤
      8 * (3 * r / 2 + 1 / 2) * max 1 (720 / δ ^ 6) := by
    calc (1 + t) ^ 2 * ((3 * r / 2 + t / 2) * Real.exp (-δ * √t))
        = ((1 + t) ^ 2 * (3 * r / 2 + t / 2)) * Real.exp (-δ * √t) := by ring
      _ ≤ (4 * (3 * r / 2 + 1 / 2) * (1 + t ^ 3)) * Real.exp (-δ * √t) := by gcongr
      _ = 4 * (3 * r / 2 + 1 / 2) * (Real.exp (-δ * √t) + t ^ 3 * Real.exp (-δ * √t)) := by ring
      _ ≤ 4 * (3 * r / 2 + 1 / 2) * (1 + 720 / δ ^ 6) := by gcongr
      _ ≤ 4 * (3 * r / 2 + 1 / 2) * (2 * max 1 (720 / δ ^ 6)) := by gcongr; linarith
      _ = 8 * (3 * r / 2 + 1 / 2) * max 1 (720 / δ ^ 6) := by ring
  have h1t_pos : 0 < (1 + t) ^ 2 := by positivity
  rw [show (1 + t) ^ (-2 : ℝ) = ((1 + t) ^ 2)⁻¹ by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
      Real.rpow_natCast]]
  rw [← div_eq_mul_inv, le_div_iff₀ h1t_pos]
  calc (3 * r / 2 + t / 2) * Real.exp (-δ * √t) * (1 + t) ^ 2
      = (1 + t) ^ 2 * ((3 * r / 2 + t / 2) * Real.exp (-δ * √t)) := by ring
    _ ≤ 8 * (3 * r / 2 + 1 / 2) * max 1 (720 / δ ^ 6) := h1t3

private lemma spinVolterraAdjoint_mid_upper (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) :
    ∃ Sg0 C_V : ℝ, 0 < Sg0 ∧ 0 < C_V ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 →
        |spinVolterraAdjoint (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c')
            (c' * x ^ 2 / 3)| ≤
          C_V * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
  set d5 := (rpParams 4).bumpData
  obtain ⟨Sg0, C_h, hSg0, hCh, hh⟩ := bumpBc_combProfile_mid_le N hN hη0 hη1 σs
  obtain ⟨C_hh, hChh, hh'⟩ := bumpBc_hankel_mid_le N hN hη0 hη1 σs
  obtain ⟨C₀, hC₀, hfar⟩ := bumpG_far_exp_le N hN hη0 hη1 σs zero_lt_one
  set C_g := (C_h + C_hh) / 2
  set C_mid := C_g * ((xiStar + 1) ^ 3 / π) + C₀ * 16 * (1 + (xiStar + 1)) ^ 3
  have hCg : 0 < C_g := by positivity
  have hCmid : 0 < C_mid := by have := Real.pi_pos; have := xiStar_pos; positivity
  refine ⟨Sg0, C_mid, hSg0, hCmid, ?_⟩
  filter_upwards [hh, hh', hfar, bumpG_good spinMomentW5Prob d5 N hN hη0 hη1 σs,
    eventually_ge_atTop (1 : ℝ)] with c' hc1 hc2 hfg ⟨hc', htest, C_b, hCb, hdec⟩ hc1' x hx_lo hx_hi
  have hlam0 : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hx_gt : xiStar < x := by linarith [mul_pos hlam0 hSg0]
  have hx0 : 0 < x := xiStar_pos.trans hx_gt
  have hx1 : 0 < xiStar + 1 := by linarith [xiStar_pos]
  set r := c' * x ^ 2 / 3
  set r₁ := c' * (xiStar + 1) ^ 2 / 3
  have hrr₁ : r ≤ r₁ := by dsimp [r, r₁]; gcongr
  have hr0 : 0 ≤ r := by positivity
  set g := bumpG spinMomentW5Prob d5 N η σs c'
  have hInt_all : IntegrableOn (fun t => (3 * r - t) / 2 * g t) (Ici r) volume := by
    set δ := π * √(3 / c')
    have hδ : 0 < δ := by have := Real.pi_pos; positivity
    set M_d := max 1 (720 / δ ^ 6)
    have hMd1 : 1 ≤ M_d := le_max_left _ _
    have hMd2 : 720 / δ ^ 6 ≤ M_d := le_max_right _ _
    set C_dom := 8 * C_b * (3 * r / 2 + 1 / 2) * M_d
    have hm_g : AEStronglyMeasurable (fun t => (3 * r - t) / 2 * g t) (volume.restrict (Ici r)) :=
      (ContinuousOn.mul
        ((continuous_const.sub continuous_id).div_const 2).continuousOn
        (htest.cont.mono (Ici_subset_Ici.mpr hr0))).aestronglyMeasurable measurableSet_Ici
    refine (IntegrableOn.mono_set (integrableOn_one_add_rpow_neg_two.const_mul C_dom)
      (Ici_subset_Ici.mpr hr0)).mono' hm_g ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht_r : r ≤ t := mem_Ici.mp ht
    have ht0 : 0 ≤ t := hr0.trans ht_r
    have hgt := hdec t ht0
    have hbd1 : |g t| ≤ C_b * Real.exp (-δ * √t) := by
      have hsq_eq : π * √(3 * t / c') = δ * √t := by
        dsimp [δ]
        rw [show 3 * t / c' = (3 / c') * t by ring, Real.sqrt_mul (by positivity), mul_assoc]
      have hexp : Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c')) ≤ Real.exp (-δ * √t) := by
        apply Real.exp_le_exp.mpr
        rw [hsq_eq]
        have : 0 ≤ 4 * π * √(c' / 12 * t) := by have := Real.pi_pos; positivity
        linarith
      calc |g t| ≤ C_b * Real.exp (-4 * π * √(c' / 12 * t) - π * √(3 * t / c')) := hgt
        _ ≤ C_b * Real.exp (-δ * √t) := by gcongr
    have hpow6 := volterra_exp_dom δ hδ r t hr0 ht0
    have hdiff_le : |(3 * r - t) / 2| ≤ 3 * r / 2 + t / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs, abs_mul]
    calc |(3 * r - t) / 2| * |g t|
        ≤ (3 * r / 2 + t / 2) * (C_b * Real.exp (-δ * √t)) := by gcongr
      _ = C_b * ((3 * r / 2 + t / 2) * Real.exp (-δ * √t)) := by ring
      _ ≤ C_b * (8 * (3 * r / 2 + 1 / 2) * M_d * (1 + t) ^ (-2 : ℝ)) := by
          gcongr
      _ = C_dom * (1 + t) ^ (-2 : ℝ) := by dsimp [C_dom]; ring
  have hInt_abs : IntegrableOn (fun t => |(3 * r - t) / 2 * g t|) (Ici r) volume := hInt_all.norm
  have hsplit : ∫ t in Ici r, |(3 * r - t) / 2 * g t| =
      (∫ t in Ico r r₁, |(3 * r - t) / 2 * g t|) + ∫ t in Ici r₁, |(3 * r - t) / 2 * g t| := by
    rw [← Ico_union_Ici_eq_Ici hrr₁]
    exact setIntegral_union (Set.disjoint_iff.mpr fun t ⟨ht1, ht2⟩ => by
        simp only [mem_Ico, mem_Ici] at ht1 ht2; linarith)
      measurableSet_Ici (hInt_abs.mono_set Ico_subset_Ici_self)
      (hInt_abs.mono_set (Ici_subset_Ici.mpr hrr₁))
  have htail := spinVolterra_tail_integral_bound hc1' hx1 hr0 hrr₁ hC₀.le
    (fun y hy => hfg y (by linarith))
  have htail_le : ∫ t in Ici r₁, |(3 * r - t) / 2 * g t| ≤
      (C₀ * 16 * (1 + (xiStar + 1)) ^ 3) * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-c' * besselL x) := by
    have hyx : 0 < x - xiStar := sub_pos.mpr hx_gt
    have hyx1 : x - xiStar ≤ 1 := by linarith
    have hrpow_ge1 : 1 ≤ (x - xiStar) ^ (-(3 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hyx hyx1 (by norm_num)
    have hexp_le : Real.exp (-c' * besselL (xiStar + 1) - π * (xiStar + 1)) ≤
        Real.exp (-c' * besselL x) := by
      apply Real.exp_le_exp.mpr
      have hsub : besselL x ≤ besselL (xiStar + 1) := by
        unfold besselL
        have := Real.pi_pos
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx_hi (by positivity)) (by norm_num)
      have hcL : c' * besselL x ≤ c' * besselL (xiStar + 1) :=
        mul_le_mul_of_nonneg_left hsub hc'.le
      have hpx : 0 ≤ π * (xiStar + 1) := by have := Real.pi_pos; have := xiStar_pos; positivity
      rw [neg_mul, neg_mul]
      linarith
    calc ∫ t in Ici r₁, |(3 * r - t) / 2 * g t|
        ≤ C₀ * (16 * (1 + (xiStar + 1)) ^ 3 * c') *
            Real.exp (-c' * besselL (xiStar + 1) - π * (xiStar + 1)) := htail
      _ ≤ C₀ * (16 * (1 + (xiStar + 1)) ^ 3 * c') *
            ((x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x)) := by
          gcongr
          calc Real.exp (-c' * besselL (xiStar + 1) - π * (xiStar + 1))
              = 1 * Real.exp (-c' * besselL (xiStar + 1) - π * (xiStar + 1)) := (one_mul _).symm
            _ ≤ (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) :=
                mul_le_mul hrpow_ge1 hexp_le (Real.exp_pos _).le (by positivity)
      _ = (C₀ * 16 * (1 + (xiStar + 1)) ^ 3) * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-c' * besselL x) := by ring
  have hmid_le : ∫ t in Ico r r₁, |(3 * r - t) / 2 * g t| ≤
      (C_g * ((xiStar + 1) ^ 3 / π)) * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-c' * besselL x) := by
    have h1 : ∫ t in Ico r r₁, |(3 * r - t) / 2 * g t| ≤
        ∫ t in Icc r r₁, |(3 * r - t) / 2 * g t| :=
      setIntegral_mono_set (hInt_abs.mono_set Icc_subset_Ici_self)
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun _ ht => Ico_subset_Icc_self ht)
    rw [show r = c' * x ^ 2 / 3 from rfl, show r₁ = c' * (xiStar + 1) ^ 2 / 3 from rfl,
      integral_Icc_comp_sq hc' hx0 hx_hi (fun t => |(3 * r - t) / 2 * g t|)] at h1
    set q := 2 * π * c' / 3
    have hq : 0 < q := by positivity
    have hInt_exp : IntegrableOn (fun y : ℝ => Real.exp (-(q * y))) (Ioi x) volume := by
      simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hq) x
    have hI_exp : (∫ y in Ioi x, Real.exp (-(q * y))) = Real.exp (-c' * besselL x) / q := by
      have heq : (fun y : ℝ => Real.exp (-(q * y))) = fun y => Real.exp (-q * y) := by
        ext y; rw [neg_mul]
      rw [heq, integral_exp_mul_Ioi (neg_lt_zero.mpr hq) x, neg_div_neg_eq]
      congr 2; unfold besselL q; ring
    set K_c := 2 / 3 * (xiStar + 1) ^ 3 * c' ^ 2 * C_g * (x - xiStar) ^ (-(3 / 2 : ℝ))
    have hKc0 : 0 ≤ K_c := by have := sub_pos.mpr hx_gt; positivity
    have hpt : ∀ y ∈ Icc x (xiStar + 1),
        2 * c' * y / 3 * |(3 * r - c' * y ^ 2 / 3) / 2 * g (c' * y ^ 2 / 3)| ≤
          K_c * Real.exp (-(q * y)) := by
      intro y ⟨hyx, hyx1⟩
      have hy_lo : xiStar + lambdaComb c' * Sg0 ≤ y := hx_lo.trans hyx
      have hg_pt : |g (c' * y ^ 2 / 3)| ≤
          C_g * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
        dsimp [g, bumpG, pairOdd]
        rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
        have hsum := add_le_add (hc1 y hy_lo hyx1) (hc2 y (hx_gt.trans_le hyx) hyx1)
        calc |combProfile c' (bumpBc d5 N η σs c') (c' * y ^ 2 / 3) -
                hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)| / 2
            ≤ (|combProfile c' (bumpBc d5 N η σs c') (c' * y ^ 2 / 3)| +
                |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * y ^ 2 / 3)|) / 2 :=
              div_le_div_of_nonneg_right (abs_sub _ _) zero_le_two
          _ ≤ (C_h * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) +
                C_hh * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y)) / 2 :=
              div_le_div_of_nonneg_right hsum zero_le_two
          _ = C_g * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
              dsimp [C_g]; ring
      have hdiff : |(3 * r - c' * y ^ 2 / 3) / 2| ≤ c' * (xiStar + 1) ^ 2 := by
        have h0 : 0 ≤ c' * x ^ 2 := by positivity
        have hy2 : y ^ 2 ≤ (xiStar + 1) ^ 2 := pow_le_pow_left₀ (hx0.le.trans hyx) hyx1 2
        have hx2 : x ^ 2 ≤ (xiStar + 1) ^ 2 := pow_le_pow_left₀ hx0.le hx_hi 2
        exact abs_le.mpr ⟨by dsimp [r]; nlinarith, by dsimp [r]; nlinarith⟩
      have hrpow_y : (y - xiStar) ^ (-(3 / 2 : ℝ)) ≤ (x - xiStar) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hx_gt) (by linarith) (by norm_num)
      have heq_q : Real.exp (-c' * besselL y) = Real.exp (-(q * y)) := by
        congr 1; unfold besselL q; ring
      rw [abs_mul]
      calc 2 * c' * y / 3 * (|(3 * r - c' * y ^ 2 / 3) / 2| * |g (c' * y ^ 2 / 3)|)
          ≤ 2 * c' * (xiStar + 1) / 3 *
              ((c' * (xiStar + 1) ^ 2) * (C_g * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y))) := by
            gcongr
        _ ≤ 2 * c' * (xiStar + 1) / 3 *
              ((c' * (xiStar + 1) ^ 2) * (C_g * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-(q * y)))) := by
            rw [heq_q]; gcongr
        _ = K_c * Real.exp (-(q * y)) := by dsimp [K_c]; ring
    have h2 : ∫ y in Icc x (xiStar + 1),
          2 * c' * y / 3 * |(3 * r - c' * y ^ 2 / 3) / 2 * g (c' * y ^ 2 / 3)| ≤
        ∫ y in Icc x (xiStar + 1), K_c * Real.exp (-(q * y)) := by
      have hInt_K : IntegrableOn (fun y => K_c * Real.exp (-(q * y))) (Icc x (xiStar + 1)) volume :=
        ((Continuous.rexp (continuous_const.mul continuous_id).neg).const_mul K_c).integrableOn_Icc
      refine integral_mono_of_nonneg ?_ hInt_K ?_
      · exact (ae_restrict_iff' measurableSet_Icc).mpr
          (Eventually.of_forall fun y hy => by have := hx0.le.trans hy.1; positivity)
      · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hpt)
    have h3 : ∫ y in Icc x (xiStar + 1), K_c * Real.exp (-(q * y)) ≤
        K_c * (Real.exp (-c' * besselL x) / q) := by
      rw [integral_const_mul, ← hI_exp, ← MeasureTheory.integral_Ici_eq_integral_Ioi]
      have hInt_Ici : IntegrableOn (fun y : ℝ => Real.exp (-(q * y))) (Ici x) volume := by
        rw [integrableOn_Ici_iff_integrableOn_Ioi]
        exact hInt_exp
      exact mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hInt_Ici (Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (Eventually.of_forall fun _ hy => Icc_subset_Ici_self hy)) hKc0
    have hsimpl : K_c * (Real.exp (-c' * besselL x) / q) =
        (C_g * ((xiStar + 1) ^ 3 / π)) * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL x) := by
      dsimp [K_c, q]
      have hc0 : c' ≠ 0 := hc'.ne'
      have hpi : π ≠ 0 := Real.pi_ne_zero
      field_simp
    exact (h1.trans (h2.trans h3)).trans_eq hsimpl
  unfold spinVolterraAdjoint
  calc |∫ t in Ici r, (3 * r - t) / 2 * g t|
      ≤ ∫ t in Ici r, |(3 * r - t) / 2 * g t| := by
        have hle := MeasureTheory.norm_integral_le_integral_norm
          (μ := volume.restrict (Ici r)) (fun t => (3 * r - t) / 2 * g t)
        simpa only [Real.norm_eq_abs] using hle
    _ = (∫ t in Ico r r₁, |(3 * r - t) / 2 * g t|) + ∫ t in Ici r₁, |(3 * r - t) / 2 * g t| :=
        hsplit
    _ ≤ _ := by
        calc (∫ t in Ico r r₁, |(3 * r - t) / 2 * g t|) + ∫ t in Ici r₁, |(3 * r - t) / 2 * g t|
            ≤ (C_g * ((xiStar + 1) ^ 3 / π)) * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
                Real.exp (-c' * besselL x) +
              (C₀ * 16 * (1 + (xiStar + 1)) ^ 3) * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
                Real.exp (-c' * besselL x) := add_le_add hmid_le htail_le
          _ = C_mid * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
              dsimp [C_mid]; ring

/-! ### 2. Virasoro `w = 1` lower bound and mid-band domination -/

private lemma tanh_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.tanh y ≤ y := by
  rcases eq_or_lt_of_le hy with rfl | hy0
  · simp
  have ht_eq : Real.tanh = fun t : ℝ => Real.sinh t / Real.cosh t := by
    ext t; exact Real.tanh_eq_sinh_div_cosh t
  have hf : ∀ t : ℝ, HasDerivAt Real.tanh ((Real.cosh t * Real.cosh t -
      Real.sinh t * Real.sinh t) / Real.cosh t ^ 2) t := fun t => by
    rw [ht_eq]
    exact (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hcont : Continuous Real.tanh := by
    rw [ht_eq]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')
  obtain ⟨ξ, _, hξ⟩ := exists_hasDerivAt_eq_slope Real.tanh _ hy0 hcont.continuousOn (fun t _ => hf t)
  have hder : (Real.cosh ξ * Real.cosh ξ - Real.sinh ξ * Real.sinh ξ) / Real.cosh ξ ^ 2 ≤ 1 := by
    have hsq := Real.cosh_sq_sub_sinh_sq ξ
    have hc : 1 ≤ Real.cosh ξ := Real.one_le_cosh ξ
    have hc2 : 1 ≤ Real.cosh ξ ^ 2 := by nlinarith
    rw [show Real.cosh ξ * Real.cosh ξ - Real.sinh ξ * Real.sinh ξ = Real.cosh ξ ^ 2 - Real.sinh ξ ^ 2 by ring,
      hsq]
    exact div_le_one_of_le₀ hc2 (by positivity)
  rw [Real.tanh_zero, sub_zero, sub_zero] at hξ
  rw [hξ, div_le_one hy0] at hder
  exact hder

private lemma tanh_nonneg_of_nonneg' {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le

private lemma virasoro_bumpG_mid_lower :
    ∃ Sg0 c_low : ℝ, 0 < Sg0 ∧ 0 < c_low ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 →
        c_low * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) ≤
          bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) c'
            (c' * x ^ 2 / 3) := by
  set d1 := (rpParams 0).bumpData
  set M₁ := |designSigma1 0 1| + 1
  obtain ⟨E₁, _, hw1⟩ := designWidth1_bounds (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl
  obtain ⟨Sg0, cc, hSg0, hcc, hov⟩ := designProfile_overshoot_lower 1 1 le_rfl le_rfl M₁ E₁
  obtain ⟨K₁, hK₁, hwin1⟩ := bump_hat_window_bound virasoroProblem d1 1 le_rfl
    (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl (designSigma1 0)
  obtain ⟨c_V, hcV, hVlo⟩ := besselV_mul_deriv_lower
  have hRII := bumped_regionII 0 (rpParams 0) 1 1 le_rfl le_rfl M₁ E₁
  set c_low1 := cc * (2 / π) ^ (3 / 2 : ℝ) / 4
  set c_sech := 1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2
  set c_low2 := 1 / 40 * (4 * c_sech * (2 / π) ^ (3 / 2 : ℝ))
  have hc_low1 : 0 < c_low1 := by have := Real.pi_pos; positivity
  have hc_sech : 0 < c_sech := one_div_pos.mpr (pow_pos (Real.cosh_pos _) 2)
  have hc_low2 : 0 < c_low2 := by have := Real.pi_pos; positivity
  set c_low := min c_low1 c_low2
  have hc_low : 0 < c_low := lt_min hc_low1 hc_low2
  have hlam15 : ∀ᶠ c' in atTop, chiQuantile c' (1 + 1 / 2) < xiStar + c' ^ (-(2 / 5 : ℝ)) := by
    have hphi_lt : ∃ Kφ > 0, ∀ᶠ c' in atTop, phiQuantile (1 + 1 / 2) * lambdaComb c' < c' ^ (-(2 / 5 : ℝ)) := by
      set Bφ := max (phiQuantile (1 + 1 / 2)) 1
      have hBφ : 0 < Bφ := by positivity
      have h0 : Tendsto (fun c' : ℝ => (Bφ * kTip ^ (-(2 / 3 : ℝ))) * c' ^ (-(4 / 15 : ℝ)))
          atTop (nhds 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 15)).const_mul
          (Bφ * kTip ^ (-(2 / 3 : ℝ)))
      refine ⟨1, zero_lt_one, ?_⟩
      filter_upwards [h0.eventually_lt tendsto_const_nhds zero_lt_one, eventually_ge_atTop (1 : ℝ)]
        with c' hc0 hc1
      have hc' : 0 < c' := by linarith
      have hmul : (Bφ * kTip ^ (-(2 / 3 : ℝ))) * c' ^ (-(4 / 15 : ℝ)) =
          Bφ * lambdaComb c' * c' ^ (2 / 5 : ℝ) := by
        unfold lambdaComb
        rw [Real.mul_rpow (le_of_lt kTip_pos) hc'.le]
        have hr : c' ^ (-(2 / 3 : ℝ)) * c' ^ (2 / 5 : ℝ) = c' ^ (-(4 / 15 : ℝ)) := by
          rw [← Real.rpow_add hc']; norm_num
        rw [← hr]; ring
      rw [hmul] at hc0
      have hc25 : 0 < c' ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hc' _
      have hlt : Bφ * lambdaComb c' < 1 / c' ^ (2 / 5 : ℝ) := (lt_div_iff₀ hc25).mpr (by linarith)
      rw [one_div, ← Real.rpow_neg hc'.le] at hlt
      have hlam0 : 0 ≤ lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
      have hple : phiQuantile (1 + 1 / 2) ≤ Bφ := le_max_left _ _
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hple hlam0) hlt
    obtain ⟨_, _, hphi⟩ := hphi_lt
    filter_upwards [hphi, eventually_gt_atTop (0 : ℝ)] with c' hp hc'
    have hs := (siteRadius_bounds hc' (by norm_num : (1 / 4 : ℝ) ≤ 1 + 1 / 2)).2
    unfold siteRadius at hs
    linarith
  have hcut_hat1 : ∀ᶠ c' in atTop, K₁ / c_V ≤ (cc * (2 / π) ^ (3 / 2 : ℝ) / 2) * c' ^ (1 / 10 : ℝ) := by
    have htop : Tendsto (fun c' : ℝ => (cc * (2 / π) ^ (3 / 2 : ℝ) / 2) * c' ^ (1 / 10 : ℝ))
        atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).const_mul_atTop
        (by have := Real.pi_pos; positivity)
    exact htop.eventually_ge_atTop (K₁ / c_V)
  refine ⟨Sg0, c_low, hSg0, hc_low, ?_⟩
  filter_upwards [hov, hwin1, hVlo, hRII, hlam15, hcut_hat1,
    bumpSig_phaseHyp d1 1 le_rfl (by norm_num) le_rfl (designSigma1 0),
    designComb_innerCombHyp_of_admissible 1 le_rfl (by norm_num) le_rfl,
    combProfile_bumped_eq d1, bumpFactor_one_le d1 (η₀ := 1 / 4) (by norm_num) le_rfl,
    hw1, eventually_ge_atTop (1 : ℝ)]
    with c' hov' hw1' hVl hRII' h15' hcut1 hph hin hval hbf1 hwd1 hc1 x hx_lo hx_hi
  have hc' : 0 < c' := by linarith
  have hlam0 : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hx_gt : xiStar < x := by linarith [mul_pos hlam0 hSg0]
  have hx0 : 0 < x := xiStar_pos.trans hx_gt
  have hσ1 : ∀ k, 1 ≤ k → k ≤ 1 → |designSigma1 0 k| ≤ M₁ := fun k hk1 hk1' => by
    have : k = 1 := by omega
    subst this; dsimp [M₁]; linarith
  have hε1 : ∀ k, 1 < k → k ≤ 1 → 0 ≤ designWidth1 c' (1 / 4) k ∧
      designWidth1 c' (1 / 4) k ≤ E₁ * lambdaComb c' := fun k hk1 hk1' => by omega
  by_cases hx_reg : x ≤ xiStar + c' ^ (-(2 / 5 : ℝ))
  · have hov_pt := hov' (designSigma1 0) (designWidth1 c' (1 / 4)) hσ1 hε1 x hx_lo hx_reg
    have h2n1 : 2 * n1Comb 1 = (3 / 2 : ℝ) := by unfold n1Comb; norm_num
    rw [h2n1] at hov_pt
    have hyx : 0 < x - xiStar := sub_pos.mpr hx_gt
    have hpow_split : (2 / (π * (x - xiStar))) ^ (3 / 2 : ℝ) =
        (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) := by
      rw [show 2 / (π * (x - xiStar)) = (2 / π) * (x - xiStar)⁻¹ by field_simp,
        Real.mul_rpow (by have := Real.pi_pos; positivity) (inv_nonneg.mpr hyx.le),
        Real.inv_rpow hyx.le, ← Real.rpow_neg hyx.le]
    have hprof_lo : cc * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL x) ≤
        (designProfile c' 1 1 (1 / 4) (designSigma1 0) (designWidth1 c' (1 / 4)) (x : ℂ)).re := by
      have h1 : cc * (2 / (π * (x - xiStar))) ^ (3 / 2 : ℝ) * Real.exp (-c' * edgeL x) ≤
          (designProfile c' 1 1 (1 / 4) (designSigma1 0) (designWidth1 c' (1 / 4)) (x : ℂ)).re := by
        calc cc * (2 / (π * (x - xiStar))) ^ (3 / 2 : ℝ) * Real.exp (-c' * edgeL x)
            ≤ ((designProfile c' 1 1 (1 / 4) (designSigma1 0) (designWidth1 c' (1 / 4)) (x : ℂ)).re *
                Real.exp (c' * edgeL x)) * Real.exp (-c' * edgeL x) :=
              mul_le_mul_of_nonneg_right hov_pt (Real.exp_pos _).le
          _ = (designProfile c' 1 1 (1 / 4) (designSigma1 0) (designWidth1 c' (1 / 4)) (x : ℂ)).re := by
              rw [mul_assoc, ← Real.exp_add, show c' * edgeL x + -c' * edgeL x = 0 by ring,
                Real.exp_zero, mul_one]
      rw [hpow_split] at h1
      have hL : besselL x = edgeL x := rfl
      rw [hL]
      linarith
    have hprof_nn : 0 ≤ (designProfile c' 1 1 (1 / 4) (designSigma1 0) (designWidth1 c' (1 / 4))
        (x : ℂ)).re := by
      have hpos_lhs : 0 ≤ cc * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL x) := by have := Real.pi_pos; positivity
      exact hpos_lhs.trans hprof_lo
    have hh1_lo : cc * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL x) ≤
        combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c') (c' * x ^ 2 / 3) := by
      have hveq := hval 1 (bumpCut d1 1 c') (designSigma1 0) (designWidth1 c' (1 / 4))
        le_rfl (le_bumpCut d1 1 c') (c' * x ^ 2 / 3)
      have hbc_eq : bumpBc d1 1 (1 / 4) (designSigma1 0) c' =
          bumpedComb d1 c' 1 1 (bumpCut d1 1 c') (1 / 4) (designSigma1 0)
            (designWidth1 c' (1 / 4)) := rfl
      rw [← hbc_eq, xOf_mul_sq_div_three hc' hx0.le] at hveq
      have hdes_eq : combProfile c' (designComb c' 1 1 (1 / 4) (designSigma1 0)
            (designWidth1 c' (1 / 4))) (c' * x ^ 2 / 3) =
          (designProfile c' 1 1 (1 / 4) (designSigma1 0) (designWidth1 c' (1 / 4)) (x : ℂ)).re := by
        unfold combProfile
        rw [xOf_mul_sq_div_three hc' hx0.le, combH0_designComb]
      rw [hveq, hdes_eq]
      exact hprof_lo.trans (le_mul_of_one_le_left hprof_nn (hbf1 1 (bumpCut d1 1 c') x))
    -- Upper bound on `|ĥ₁(c' x²/3)|`
    have hx_mem : x ∈ Icc (xiStar / 2) (xiStar + 1) := ⟨by linarith [xiStar_pos], hx_hi⟩
    have hVl' := hVl x hx_mem
    have hw1_pt := hw1' (bumpCut d1 1 c') (le_bumpCut d1 1 c') x hx_mem.1
    rw [show bumpSigComb d1 c' 1 (bumpCut d1 1 c') (1 / 4) (designSigma1 0) =
      bumpBc d1 1 (1 / 4) (designSigma1 0) c' from rfl] at hw1_pt
    have hden_pos : 0 < c_V * √c' * Real.exp (c' * besselL x) := by positivity
    have hV1_pos : 0 < virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * (2 * c' * x / 3) :=
      lt_of_lt_of_le hden_pos hVl'
    have habs_hat1 : |hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c'))
          (c' * x ^ 2 / 3)| ≤ K₁ / c_V * √c' * Real.exp (-c' * besselL x) := by
      have hmul1 : |hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c'))
            (c' * x ^ 2 / 3)| * (c_V * √c' * Real.exp (c' * besselL x)) ≤ K₁ * c' := by
        have hw1'' : |hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c'))
              (c' * x ^ 2 / 3) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) * (2 * c' * x / 3))| ≤ K₁ * c' := by
          simpa only [mul_assoc] using hw1_pt
        rw [abs_mul, abs_of_pos hV1_pos] at hw1''
        exact le_trans (mul_le_mul_of_nonneg_left hVl' (abs_nonneg _)) hw1''
      have hdiv := (le_div_iff₀ hden_pos).mpr hmul1
      refine hdiv.trans_eq ?_
      have hsq : √c' ≠ 0 := (Real.sqrt_pos.mpr hc').ne'
      have he0 : Real.exp (c' * besselL x) ≠ 0 := (Real.exp_pos _).ne'
      rw [show -c' * besselL x = -(c' * besselL x) by ring, Real.exp_neg]
      field_simp; rw [Real.sq_sqrt hc'.le]
    have hhat1_half : |hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c'))
          (c' * x ^ 2 / 3)| ≤
        cc * (2 / π) ^ (3 / 2 : ℝ) / 2 * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
      have hsub : x - xiStar ≤ c' ^ (-(2 / 5 : ℝ)) := by linarith
      have hrpow1 : (c' ^ (-(2 / 5 : ℝ))) ^ (-(3 / 2 : ℝ)) ≤ (x - xiStar) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hyx hsub (by norm_num)
      have hrpow2 : (c' ^ (-(2 / 5 : ℝ))) ^ (-(3 / 2 : ℝ)) = c' ^ (3 / 5 : ℝ) := by
        rw [← Real.rpow_mul hc'.le]; norm_num
      have hc35 : c' ^ (1 / 10 : ℝ) * √c' = c' ^ (3 / 5 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc']; norm_num
      calc |hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c'))
              (c' * x ^ 2 / 3)|
          ≤ (K₁ / c_V) * √c' * Real.exp (-c' * besselL x) := habs_hat1
        _ ≤ ((cc * (2 / π) ^ (3 / 2 : ℝ) / 2) * c' ^ (1 / 10 : ℝ)) * √c' * Real.exp (-c' * besselL x) := by
            gcongr
        _ = (cc * (2 / π) ^ (3 / 2 : ℝ) / 2) * (c' ^ (1 / 10 : ℝ) * √c') * Real.exp (-c' * besselL x) := by
            ring
        _ ≤ (cc * (2 / π) ^ (3 / 2 : ℝ) / 2) * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
            rw [hc35]
            gcongr
            linarith
    have hhat_le := (abs_le.mp hhat1_half).2
    unfold bumpG pairOdd
    calc c_low * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x)
        ≤ c_low1 * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
          gcongr; exact min_le_left _ _
      _ = (cc * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) -
            cc * (2 / π) ^ (3 / 2 : ℝ) / 2 * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x)) / 2 := by
          dsimp [c_low1]; ring
      _ ≤ (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c') (c' * x ^ 2 / 3) -
            hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c'))
              (c' * x ^ 2 / 3)) / 2 := by linarith
  · push Not at hx_reg
    have hph_cut : PhaseHyp c' 1 (bumpCut d1 1 c') (1 / 4) (bumpSigma c' 1 (designSigma1 0))
        (bumpEps d1 c' 1 (1 / 4) (designWidth1 c' (1 / 4))) 2 :=
      hph (bumpCut d1 1 c') (le_bumpCut d1 1 c')
    obtain ⟨hfN, hA, -⟩ := hph_cut
    have hI : InnerCombHyp c' (bumpBc d1 1 (1 / 4) (designSigma1 0) c') :=
      hin (bumpCut d1 1 c') _ _ hfN hA
    have htwo := twoGW_zero_eq_two_mul_bumpG hc' hx0 1 le_rfl (designSigma1 0) hI
    have hII := hRII' (bumpCut d1 1 c') (designSigma1 0) (designWidth1 c' (1 / 4))
      (le_bumpCut d1 1 c') (bumpCut_spec d1 1 hc') hσ1 hε1 x hx_reg.le
    rw [htwo] at hII
    have hχ15 : chiQuantile c' ((1 : ℕ) + 1 / 2) < x :=
      lt_trans (by simpa only [Nat.cast_one] using h15') hx_reg
    have hexp_ge := exp_combPf_jEnd_ge hc' (f := 1) le_rfl hχ15
    have h2n1 : 2 * n1Comb 1 = (3 / 2 : ℝ) := by unfold n1Comb; norm_num
    have hyx : 0 < x - xiStar := sub_pos.mpr hx_gt
    have htip_pos : 0 < tanhTipK8 x := by
      unfold tanhTipK8
      rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
      have h1 : 0 < Real.sinh (π * (x - xiStar) / 2) :=
        Real.sinh_pos_iff.mpr (by have := Real.pi_pos; positivity)
      have h2 : 0 < Real.sinh (π * (x + xiStar) / 2) :=
        Real.sinh_pos_iff.mpr (by have := Real.pi_pos; have := xiStar_pos; positivity)
      have h3 := Real.cosh_pos (π * (x - xiStar) / 2)
      have h4 := Real.cosh_pos (π * (x + xiStar) / 2)
      positivity
    have htip_le : tanhTipK8 x ≤ (π / 2) * (x - xiStar) := by
      unfold tanhTipK8
      have h1 := tanh_le_self_of_nonneg (show 0 ≤ π * (x - xiStar) / 2 by have := Real.pi_pos; positivity)
      have h2 : Real.tanh (π * (x + xiStar) / 2) ≤ 1 := (Real.tanh_lt_one _).le
      have h0 : 0 ≤ Real.tanh (π * (x - xiStar) / 2) :=
        tanh_nonneg_of_nonneg' (by have := Real.pi_pos; positivity)
      calc Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2)
          ≤ Real.tanh (π * (x - xiStar) / 2) * 1 := mul_le_mul_of_nonneg_left h2 h0
        _ = Real.tanh (π * (x - xiStar) / 2) := mul_one _
        _ ≤ π * (x - xiStar) / 2 := h1
        _ = (π / 2) * (x - xiStar) := by ring
    have htip_rpow : (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) ≤
        (tanhTipK8 x) ^ (-(3 / 2 : ℝ)) := by
      rw [← h2n1]
      have h1 : (tanhTipK8 x) ^ (-(2 * n1Comb 1)) ≥ ((π / 2) * (x - xiStar)) ^ (-(2 * n1Comb 1)) :=
        Real.rpow_le_rpow_of_nonpos htip_pos htip_le (by rw [h2n1]; norm_num)
      have h2 : ((π / 2) * (x - xiStar)) ^ (-(3 / 2 : ℝ)) =
          (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by have := Real.pi_pos; positivity) hyx.le,
          Real.rpow_neg (by have := Real.pi_pos; positivity),
          ← Real.inv_rpow (by have := Real.pi_pos; positivity), inv_div]
      rw [h2n1] at h1 ⊢
      linarith
    have hexp_comb_lb : (tanhTipK8 x) ^ (-(3 / 2 : ℝ)) ≤
        Real.exp (c' * combPf c' 1 x + jEndComb c' x 1) := by
      rw [h2n1] at hexp_ge
      rw [Real.rpow_neg htip_pos.le]
      have htp : 0 < (tanhTipK8 x) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos htip_pos _
      rw [inv_le_iff_one_le_mul₀' htp]
      exact hexp_ge
    have hsech := sech_lower hx0.le hx_hi
    have hslit : slitL x = besselL x := by unfold slitL besselL; rw [abs_of_nonneg hx0.le]
    have hlev_lb : 4 * c_sech * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL x) ≤ levComb c' 1 x := by
      unfold levComb
      rw [hslit, show -c' * besselL x + c' * combPf c' 1 x + jEndComb c' x 1 =
          -(c' * besselL x) + (c' * combPf c' 1 x + jEndComb c' x 1) by ring, Real.exp_add]
      have hcsh0 : 0 ≤ c_sech := hc_sech.le
      have hexp_nn : 0 ≤ Real.exp (-(c' * besselL x)) := (Real.exp_pos _).le
      rw [show (-c' * besselL x) = -(c' * besselL x) by ring]
      calc 4 * c_sech * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-(c' * besselL x))
          = 4 * c_sech * Real.exp (-(c' * besselL x)) *
              ((2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ))) := by ring
        _ ≤ 4 * (1 / Real.cosh (π * x / 2) ^ 2) * Real.exp (-(c' * besselL x)) *
              Real.exp (c' * combPf c' 1 x + jEndComb c' x 1) := by
            gcongr
            exact htip_rpow.trans hexp_comb_lb
        _ = _ := by ring
    calc c_low * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x)
        ≤ c_low2 * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
          gcongr; exact min_le_right _ _
      _ = 1 / 40 * (4 * c_sech * (2 / π) ^ (3 / 2 : ℝ) * (x - xiStar) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-c' * besselL x)) := by dsimp [c_low2]; ring
      _ ≤ 1 / 40 * levComb c' 1 x := by gcongr
      _ ≤ bumpG virasoroProblem d1 1 (1 / 4) (designSigma1 0) c' (c' * x ^ 2 / 3) := by linarith

/-- **`sd:spinmoment-window-pair`** (mid-band domination): on `[xiStar + λ Σ₀, xiStar + 1]`,
`0 < g₁(c' x²/3)` and `|K^* g₅(c' x²/3)| ≤ C_mid c' g₁(c' x²/3)`. -/
theorem spinMoment_mid_band_dom (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) :
    ∃ Sg0 C_mid : ℝ, 0 < Sg0 ∧ 0 < C_mid ∧ ∀ᶠ c' in atTop, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 →
        0 < bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) c'
            (c' * x ^ 2 / 3) ∧
          |spinVolterraAdjoint (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c')
              (c' * x ^ 2 / 3)| ≤
            C_mid * c' * bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) c'
              (c' * x ^ 2 / 3) := by
  obtain ⟨Sg0_V, C_V, hSg0_V, hCV, hV⟩ := spinVolterraAdjoint_mid_upper N hN hη0.le hη1 σs
  obtain ⟨Sg0_1, c_low, hSg0_1, hclow, h1⟩ := virasoro_bumpG_mid_lower
  set Sg0 := max Sg0_V Sg0_1
  have hSg0 : 0 < Sg0 := lt_of_lt_of_le hSg0_V (le_max_left _ _)
  set C_mid := C_V / c_low
  have hCmid : 0 < C_mid := div_pos hCV hclow
  refine ⟨Sg0, C_mid, hSg0, hCmid, ?_⟩
  filter_upwards [hV, h1, eventually_gt_atTop (0 : ℝ)] with c' hVc' h1c' hc' x hx_lo hx_hi
  have hlam0 : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hx_V : xiStar + lambdaComb c' * Sg0_V ≤ x := by
    nlinarith [le_max_left Sg0_V Sg0_1]
  have hx_1 : xiStar + lambdaComb c' * Sg0_1 ≤ x := by
    nlinarith [le_max_right Sg0_V Sg0_1]
  have hV_pt := hVc' x hx_V hx_hi
  have h1_pt := h1c' x hx_1 hx_hi
  have hx_gt : xiStar < x := by linarith [mul_pos hlam0 hSg0]
  have hyx : 0 < x - xiStar := sub_pos.mpr hx_gt
  have hlow_pos : 0 < c_low * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := by
    positivity
  have hg1_pos : 0 < bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) c'
      (c' * x ^ 2 / 3) := lt_of_lt_of_le hlow_pos h1_pt
  refine ⟨hg1_pos, ?_⟩
  calc |spinVolterraAdjoint (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c')
          (c' * x ^ 2 / 3)|
      ≤ C_V * c' * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x) := hV_pt
    _ = C_mid * c' * (c_low * (x - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL x)) := by
        dsimp [C_mid]; field_simp
    _ ≤ C_mid * c' * bumpG virasoroProblem (rpParams 0).bumpData 1 (1 / 4) (designSigma1 0) c'
          (c' * x ^ 2 / 3) := by gcongr

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_mid_band_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_mid_band_dom

end FormalResearch.ModularBootstrap.Spin