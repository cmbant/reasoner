module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentVacLimit
public import FormalResearch.ModularBootstrap.Upper.Window.TailBand
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOne
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionII
public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIIIRegionII
public import FormalResearch.ModularBootstrap.Crossing.BesselBridge

/-!
# Comb tail bounds, Volterra tail bounds, and mid-band domination for `SPIN-M`

Source: `CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex`
(`sd:spinmoment-combbounds`, `sd:spinmoment-Vtail`, `sd:spinmoment-tail`, `sd:spinmoment-window-pair`).

* `bumpG_far_exp_le`: on `x ≥ xiStar + r₀` (`r₀ > 0`), `|g₅(c' x²/3)| ≤ C₀ exp (-c' L(x) - π x)`.
* `volterraAdjoint_bumpG_far_le`: on `x ≥ xiStar + r₀`, `|K^* g₅(c' x²/3)| ≤ C_V c' (1 + x)³ exp (-c' L(x) - π x)`.
* `spinRadMarginal_laplace_uniform`: charge-uniform bound on `∫ e^{-2π b r} dν₀(r)` for `0 < b ≤ 1`,
  independent of `c'` and the cone opening `B`.
* `spinMoment_volterra_tail_far`: the `x ≥ xiStar + 1` Volterra tail is `o(c' FKc 1 1 c')`.
* `spinMoment_mid_band_dom`: on `x ∈ [xiStar + λ Σ₀, xiStar + 1]`,
  `|K^* g₅(c' x²/3)| ≤ C_mid c' g₁(c' x²/3)` where `g₁` is the `w = 1` Virasoro design test.
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

/-! ### 1. Basic coordinate and comb identities -/

lemma xOf_mul_sq_div_three {c' x : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) :
    xOf c' (c' * x ^ 2 / 3) = x := by
  unfold xOf
  rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp]
  exact Real.sqrt_sq hx

lemma designWidth1_bounds {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ c' in atTop,
      ∀ k : ℕ, 1 ≤ k → 0 ≤ designWidth1 c' η k ∧ designWidth1 c' η k ≤ E * lambdaComb c' := by
  obtain ⟨C, _, hgap⟩ := siteGap_eventually_le
  refine ⟨C / 4 + 1, by positivity, ?_⟩
  filter_upwards [hgap, eventually_gt_atTop (0 : ℝ)] with c' ⟨hgk, hg1, hχC, _⟩ hc' k hk
  unfold designWidth1
  have hg_nn : 0 ≤ siteGap c' k := siteGap_nonneg hc' hk
  have hg_le : siteGap c' k ≤ C * lambdaComb c' := (hgk k hk).trans (hg1.trans hχC)
  refine ⟨mul_nonneg hη0 hg_nn, ?_⟩
  have hlam : 0 ≤ lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  calc η * siteGap c' k ≤ (1 / 4) * (C * lambdaComb c') :=
        mul_le_mul hη1 hg_le hg_nn (by norm_num)
    _ = (C / 4) * lambdaComb c' := by ring
    _ ≤ (C / 4 + 1) * lambdaComb c' := by nlinarith

noncomputable def supSigma1 (σs : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) : ℝ :=
  (Finset.Icc 1 N).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩ (fun k => |σs k|) + 1

lemma abs_le_supSigma1 (σs : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) : |σs k| ≤ supSigma1 σs N hN := by
  unfold supSigma1
  have hmem : k ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hk1, hkN⟩
  have hle := Finset.le_sup' (fun k => |σs k|) hmem
  linarith

lemma twoGW_zero_eq_two_mul_bumpG {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x)
    (N : ℕ) (_hN : 1 ≤ N) {η : ℝ} (σs : ℕ → ℝ)
    (hI : InnerCombHyp c' (bumpBc (rpParams 0).bumpData N η σs c')) :
    twoGW 0 c' 1 (bumpCut (rpParams 0).bumpData N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps (rpParams 0).bumpData c' N (1 / 4) (designWidth1 c' η)) x =
      2 * bumpG virasoroProblem (rpParams 0).bumpData N η σs c' (c' * x ^ 2 / 3) := by
  set d1 := (rpParams 0).bumpData
  have hb_eq : bumpBc d1 N η σs c' =
      designComb c' 1 (bumpCut d1 N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps d1 c' N (1 / 4) (designWidth1 c' η)) := rfl
  have hprof_eq : combH0 (bumpBc d1 N η σs c') =
      designProfile c' 1 (bumpCut d1 N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps d1 c' N (1 / 4) (designWidth1 c' η)) := by
    rw [hb_eq, combH0_designComb]
  obtain ⟨_, _, hd⟩ := hI.combProfile_decay hc'
  have ht : 0 < c' * x ^ 2 / 3 := by positivity
  have hH := hI.edgeHankelP_eq 0 hc' hd ht
  rw [hprof_eq] at hH
  have h1 : combProfile c' (bumpBc d1 N η σs c') (c' * x ^ 2 / 3) =
      (designProfile c' 1 (bumpCut d1 N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps d1 c' N (1 / 4) (designWidth1 c' η)) (x : ℂ)).re := by
    unfold combProfile
    rw [xOf_mul_sq_div_three hc' hx.le, hprof_eq]
  have h2 : hankelTransform virasoroProblem.w (combProfile c' (bumpBc d1 N η σs c')) (c' * x ^ 2 / 3) =
      (edgeHankelP 0 c' (designProfile c' 1 (bumpCut d1 N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps d1 c' N (1 / 4) (designWidth1 c' η))) (c' * x ^ 2 / 3)).re := by
    have hw : virasoroProblem.w = 0 + 1 := rfl
    rw [hw, hH, Complex.ofReal_re]
  unfold twoGW bumpG pairOdd
  rw [Complex.sub_re, h1, h2]
  ring

/-! ### 2. Far exponential decay of `g₅` (`sd:spinmoment-combbounds`(1)) -/

private lemma bumpBc_combProfile_far_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + r₀ ≤ x →
      |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * x ^ 2 / 3)| ≤
        C * Real.exp (-c' * besselL x - π * x) := by
  set d5 := (rpParams 4).bumpData
  set M := supSigma1 σs N hN
  obtain ⟨E, _, hwidth⟩ := designWidth1_bounds hη0 hη1
  obtain ⟨K, hK0, hnorm⟩ := designComb_norm_le_exp_ref 1 N le_rfl hN M E (η₀ := 1 / 4)
    (by norm_num) le_rfl
  obtain ⟨Cref, hCref, href⟩ := refComb_far_bound (f := 1) le_rfl (η₀ := 1 / 4) (r₀ := r₀)
    (by norm_num) le_rfl hr₀
  set s := max (phiQuantile ((N : ℝ) + 2)) M
  have hlam_s : ∀ᶠ c' in atTop, 4 * s * lambdaComb c' ≤ r₀ := by
    have h0 := tendsto_lambdaComb_atTop.const_mul (4 * s)
    rw [mul_zero] at h0
    exact h0.eventually_le_const hr₀
  have hlam_K : ∀ᶠ c' in atTop, K * (lambdaComb c' / r₀) ≤ 1 := by
    have h0 := (tendsto_lambdaComb_atTop.div_const r₀).const_mul K
    rw [zero_div, mul_zero] at h0
    exact h0.eventually_le_const zero_lt_one
  refine ⟨max (bumpC d5 (1 / 4)) 1 * 4 * Real.exp 1 * Cref, by positivity, ?_⟩
  filter_upwards [combProfile_bumped_eq d5, bumpFactor_one_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le d5 (η₀ := 1 / 4) (by norm_num) le_rfl, hwidth, hnorm, href, hlam_s, hlam_K,
    eventually_gt_atTop (0 : ℝ)] with c' hval hbf1 hbfC hw hn hrf hs1 hK1 hc' x hx
  have hx0 : 0 ≤ x := by linarith [xiStar_pos]
  have hNcut := le_bumpCut d5 N c'
  have hveq := hval N (bumpCut d5 N c') σs (designWidth1 c' η) hN hNcut (c' * x ^ 2 / 3)
  have hbc_eq : bumpBc d5 N η σs c' = bumpedComb d5 c' 1 N (bumpCut d5 N c') (1 / 4) σs
      (designWidth1 c' η) := rfl
  rw [← hbc_eq, xOf_mul_sq_div_three hc' hx0] at hveq
  have hbf0 : 0 ≤ bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') x :=
    zero_le_one.trans (hbf1 N (bumpCut d5 N c') x)
  have hbf_le : bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') x ≤ max (bumpC d5 (1 / 4)) 1 :=
    (hbfC N (bumpCut d5 N c') x hx0).trans (le_max_left _ _)
  have hxs : xiStar + 4 * s * lambdaComb c' ≤ x := by linarith
  have hn' := hn σs (designWidth1 c' η)
    (fun k hk1 hkN => abs_le_supSigma1 σs N hN hk1 hkN)
    (fun k hk1 _ => hw k hk1.le) x hxs
  have hKx : K * (lambdaComb c' / (x - xiStar)) ≤ 1 := by
    have hdiv : lambdaComb c' / (x - xiStar) ≤ lambdaComb c' / r₀ := by
      have hlam0 : 0 ≤ lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
      exact div_le_div_of_nonneg_left hlam0 hr₀ (by linarith)
    exact (mul_le_mul_of_nonneg_left hdiv hK0).trans hK1
  have hrf' := hrf x hx
  have hsech : ‖sechSqProfile (x : ℂ)‖ ≤ 4 * Real.exp (-π * x) := by
    simpa [abs_of_nonneg hx0] using norm_sechSqProfile_ofReal_le x
  have hprof_le : |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η))
      (c' * x ^ 2 / 3)| ≤
      4 * Real.exp (-π * x) * (Real.exp 1 * ‖refComb c' 1 (1 / 4) (x : ℂ)‖) := by
    unfold combProfile combH0
    rw [xOf_mul_sq_div_three hc' hx0]
    calc |(sechSqProfile (x : ℂ) * designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)).re|
        ≤ ‖sechSqProfile (x : ℂ) * designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ :=
          Complex.abs_re_le_norm _
      _ = ‖sechSqProfile (x : ℂ)‖ * ‖designComb c' 1 N (1 / 4) σs (designWidth1 c' η) (x : ℂ)‖ :=
          norm_mul _ _
      _ ≤ (4 * Real.exp (-π * x)) *
            (Real.exp (K * (lambdaComb c' / (x - xiStar))) * ‖refComb c' 1 (1 / 4) (x : ℂ)‖) :=
          mul_le_mul hsech hn' (norm_nonneg _) (by positivity)
      _ ≤ (4 * Real.exp (-π * x)) * (Real.exp 1 * ‖refComb c' 1 (1 / 4) (x : ℂ)‖) := by
          gcongr
  have hrf_exp : ‖refComb c' 1 (1 / 4) (x : ℂ)‖ ≤ Cref * Real.exp (-(c' * besselL x)) := by
    calc ‖refComb c' 1 (1 / 4) (x : ℂ)‖ ≤ Cref / Real.exp (c' * besselL x) :=
          (le_div_iff₀ (Real.exp_pos (c' * besselL x))).mpr hrf'
      _ = Cref * Real.exp (-(c' * besselL x)) := by rw [div_eq_mul_inv, Real.exp_neg]
  rw [hveq, abs_mul, abs_of_nonneg hbf0]
  calc bumpFactor d5 c' (1 / 4) N (bumpCut d5 N c') x *
        |combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) (c' * x ^ 2 / 3)|
      ≤ max (bumpC d5 (1 / 4)) 1 *
          (4 * Real.exp (-π * x) * (Real.exp 1 * (Cref * Real.exp (-(c' * besselL x))))) := by
        refine mul_le_mul hbf_le ?_ (abs_nonneg _) (by positivity)
        exact hprof_le.trans (by gcongr)
    _ = max (bumpC d5 (1 / 4)) 1 * 4 * Real.exp 1 * Cref * Real.exp (-c' * besselL x - π * x) := by
        rw [show -c' * besselL x - π * x = -(c' * besselL x) + -π * x by ring, Real.exp_add]
        ring

private lemma sdvPrefactor_far_bound {x₀ : ℝ} (hx₀ : xiStar < x₀) :
    ∃ Cs > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, x₀ ≤ x →
      combAmplitude c' x * fwsdRatio 4 x ≤ Cs * Real.exp (-c' * besselL x - π * x) := by
  have hx₀0 : 0 < x₀ := xiStar_pos.trans hx₀
  have hev_pos : 0 < edgeV x₀ := edgeV_pos hx₀
  have hFp : 0 < edgeF' (edgeV x₀) := edgeF'_pos hev_pos
  set Cs := (2 * 8 * 3 * 2 * √((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀))) *
      (1 + 1 / (2 * xiStar)) ^ 4
  have hCs : 0 < Cs :=
    mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (div_pos (by positivity) hFp)))
      (pow_pos (by have := xiStar_pos; positivity) 4)
  refine ⟨Cs, hCs, ?_⟩
  filter_upwards [eventually_ge_atTop (3 / (8 * π * x₀))] with c' hc' x hx
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc'
  have hk : 1 / 2 ≤ 4 * π * c' * x / 3 := by
    have h1 : 1 / 2 ≤ 4 * π * c' * x₀ / 3 := by
      have := Real.pi_pos
      calc (1 / 2 : ℝ) = 4 * π * (3 / (8 * π * x₀)) * x₀ / 3 := by field_simp; ring
        _ ≤ 4 * π * c' * x₀ / 3 := by gcongr
    have h2 : 4 * π * c' * x₀ / 3 ≤ 4 * π * c' * x / 3 := by gcongr
    linarith
  have hsdv := sdvPrefactor_le (Φ₁ := fun _ => 0) hc'0 hx₀ hx hk (fun _ => rfl)
  have hfws := fwsdRatio_le (p := 4) (lt_of_lt_of_le hx₀ hx)
  have hamp_le : combAmplitude c' x ≤
      2 * 8 * 3 * 2 * √((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀)) *
        Real.exp (-c' * besselL x - π * x) := by
    unfold combAmplitude besselL
    rw [show -c' * (2 * π * x / 3) - π * x = -(c' * (2 * π * x / 3)) - π * x by ring]
    exact hsdv
  have hfws0 : 0 ≤ fwsdRatio 4 x := by
    unfold fwsdRatio
    have := xiStar_pos
    positivity
  calc combAmplitude c' x * fwsdRatio 4 x
      ≤ (2 * 8 * 3 * 2 * √((1 + 1 / (2 * x₀)) / edgeF' (edgeV x₀)) *
          Real.exp (-c' * besselL x - π * x)) * (1 + 1 / (2 * xiStar)) ^ 4 :=
        mul_le_mul hamp_le hfws hfws0 (by positivity)
    _ = Cs * Real.exp (-c' * besselL x - π * x) := by ring

private lemma bumpBc_hankel_far_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + r₀ ≤ x →
      |hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
          (c' * x ^ 2 / 3)| ≤
        C * Real.exp (-c' * besselL x - π * x) := by
  set d5 := (rpParams 4).bumpData
  obtain ⟨_, _, _, C, _, _, _, _, _, _, hpk⟩ :=
    phase_packageP 4 1 le_rfl (η₀ := 1 / 4) (P := 2) (θ := 1 / 2)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, _, hsdv⟩ := sdvPrefactor_far_bound (x₀ := xiStar + r₀) (by linarith)
  have hr₀_ev : ∀ᶠ c' in atTop, c' ^ (-(1 / 2 : ℝ)) ≤ r₀ := by
    have h0 : Tendsto (fun c' : ℝ => c' ^ (-(1 / 2 : ℝ))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    exact h0.eventually_le_const hr₀
  have hC_ev : ∀ᶠ c' in atTop, C * c' ^ (-1 + 3 * (1 / 2 : ℝ) / 2) ≤ 1 := by
    have h0 : Tendsto (fun c' : ℝ => C * c' ^ (-(1 / 4 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C
    have h1 := h0.eventually_le_const zero_lt_one
    filter_upwards [h1] with c' hc'
    have he : (-1 + 3 * (1 / 2 : ℝ) / 2 : ℝ) = -(1 / 4 : ℝ) := by norm_num
    rwa [he]
  refine ⟨2 * Cs, by positivity, ?_⟩
  filter_upwards [bumpSig_phaseHyp d5 N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (by norm_num) le_rfl,
    hpk, hsdv, hr₀_ev, hC_ev, eventually_gt_atTop (0 : ℝ)]
    with c' hph hin hpkc hsdvc hrc' hCc hc' x hx
  have hph_cut : PhaseHyp c' 1 (bumpCut d5 N c') (1 / 4) (bumpSigma c' N σs)
      (bumpEps d5 c' N (1 / 4) (designWidth1 c' η)) 2 := hph (bumpCut d5 N c') (le_bumpCut d5 N c')
  have hph_adm := hph_cut
  obtain ⟨hfN, hA, -⟩ := hph_adm
  have hI : InnerCombHyp c' (bumpBc d5 N η σs c') := hin (bumpCut d5 N c') _ _ hfN hA
  obtain ⟨_, _, hd⟩ := hI.combProfile_decay hc'
  have hx0 : 0 < x := by linarith [xiStar_pos]
  have ht : 0 < c' * x ^ 2 / 3 := by positivity
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
  have htrans' := htrans x (by linarith)
  have hsdv' := hsdvc x hx
  have hhank_norm : |hankelTransform 5 (combProfile c' (bumpBc d5 N η σs c')) (c' * x ^ 2 / 3)| =
      ‖edgeHankelP 4 c' (designProfile c' 1 (bumpCut d5 N c') (1 / 4) (bumpSigma c' N σs)
        (bumpEps d5 c' N (1 / 4) (designWidth1 c' η))) (c' * x ^ 2 / 3)‖ := by
    rw [hH, Complex.norm_real, Real.norm_eq_abs]
  rw [hhank_norm]
  have hnonneg : 0 ≤ combAmplitude c' x * fwsdRatio 4 x := by
    unfold combAmplitude fwsdRatio sdvPrefactor
    positivity
  calc ‖edgeHankelP 4 c' _ (c' * x ^ 2 / 3)‖
      ≤ combAmplitude c' x * fwsdRatio 4 x * (1 + C * c' ^ (-1 + 3 * (1 / 2 : ℝ) / 2)) := htrans'
    _ ≤ (Cs * Real.exp (-c' * besselL x - π * x)) * (1 + 1) := by gcongr
    _ = 2 * Cs * Real.exp (-c' * besselL x - π * x) := by ring

/-- **`sd:spinmoment-combbounds`(1)** on `x ≥ xiStar + r₀` (`r₀ > 0`): exponential decay of `g₅`
in the `x`-variable: `|g₅(c' x²/3)| ≤ C₀ exp (-c' L(x) - π x)`. -/
theorem bumpG_far_exp_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C₀ > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + r₀ ≤ x →
      |bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' (c' * x ^ 2 / 3)| ≤
        C₀ * Real.exp (-c' * besselL x - π * x) := by
  obtain ⟨Ch, _, hh⟩ := bumpBc_combProfile_far_le N hN hη0 hη1 σs hr₀
  obtain ⟨Ch', _, hh'⟩ := bumpBc_hankel_far_le N hN hη0 hη1 σs hr₀
  refine ⟨(Ch + Ch') / 2, by positivity, ?_⟩
  filter_upwards [hh, hh'] with c' hc1 hc2 x hx
  unfold bumpG pairOdd
  change |(combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * x ^ 2 / 3) -
      hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
        (c' * x ^ 2 / 3)) / 2| ≤
    (Ch + Ch') / 2 * Real.exp (-c' * besselL x - π * x)
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  calc |combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * x ^ 2 / 3) -
          hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
            (c' * x ^ 2 / 3)| / 2
      ≤ (|combProfile c' (bumpBc (rpParams 4).bumpData N η σs c') (c' * x ^ 2 / 3)| +
          |hankelTransform 5 (combProfile c' (bumpBc (rpParams 4).bumpData N η σs c'))
            (c' * x ^ 2 / 3)|) / 2 :=
        div_le_div_of_nonneg_right (abs_sub _ _) zero_le_two
    _ ≤ (Ch * Real.exp (-c' * besselL x - π * x) +
          Ch' * Real.exp (-c' * besselL x - π * x)) / 2 := by
        gcongr
        · exact hc1 x hx
        · exact hc2 x hx
    _ = (Ch + Ch') / 2 * Real.exp (-c' * besselL x - π * x) := by ring

/-! ### 3. Volterra tail of `g₅` (`sd:spinmoment-Vtail`) -/

private lemma cube_mul_exp_neg_le {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-(r * s)) ≤ (48 / r ^ 3) * Real.exp (-(r / 2 * s)) := by
  have hu : 0 ≤ r / 2 * s := by positivity
  have hpow := Real.pow_div_factorial_le_exp (r / 2 * s) hu 3
  have h1 : (r / 2 * s) ^ 3 ≤ 6 * Real.exp (r / 2 * s) := by
    have hfact : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
    rw [hfact] at hpow
    linarith
  have h2 : s ^ 3 * Real.exp (-(r / 2 * s)) ≤ 48 / r ^ 3 := by
    have hmul : (r / 2 * s) ^ 3 * Real.exp (-(r / 2 * s)) ≤ 6 := by
      calc (r / 2 * s) ^ 3 * Real.exp (-(r / 2 * s))
          ≤ (6 * Real.exp (r / 2 * s)) * Real.exp (-(r / 2 * s)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 6 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hr3 : 0 < r ^ 3 := by positivity
    calc s ^ 3 * Real.exp (-(r / 2 * s))
        = (r / 2 * s) ^ 3 * Real.exp (-(r / 2 * s)) * (8 / r ^ 3) := by field_simp; ring
      _ ≤ 6 * (8 / r ^ 3) := by gcongr
      _ = 48 / r ^ 3 := by ring
  calc s ^ 3 * Real.exp (-(r * s))
      = (s ^ 3 * Real.exp (-(r / 2 * s))) * Real.exp (-(r / 2 * s)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2; ring
    _ ≤ (48 / r ^ 3) * Real.exp (-(r / 2 * s)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

lemma spinVolterra_tail_integral_bound {g : ℝ → ℝ} {c' r₀ x₀ C₀ : ℝ}
    (hc' : 1 ≤ c') (hx₀ : 0 < x₀) (hr₀0 : 0 ≤ r₀) (hr₀ : r₀ ≤ c' * x₀ ^ 2 / 3) (hC₀ : 0 ≤ C₀)
    (hg_exp : ∀ y : ℝ, x₀ ≤ y → |g (c' * y ^ 2 / 3)| ≤ C₀ * Real.exp (-c' * besselL y - π * y)) :
    (∫ t in Ici (c' * x₀ ^ 2 / 3), |(3 * r₀ - t) / 2 * g t|) ≤
      C₀ * (16 * (1 + x₀) ^ 3 * c') * Real.exp (-c' * besselL x₀ - π * x₀) := by
  have hc'0 : 0 < c' := by linarith
  have hr := integral_Ici_comp_sq hc'0 hx₀ (fun t => |(3 * r₀ - t) / 2 * g t|)
  rw [hr, MeasureTheory.integral_Ici_eq_integral_Ioi]
  set q := 2 * π * c' / 3
  have hq : 0 < q := by positivity
  have hq_ge : 2 * c' ≤ q := by
    have := Real.pi_gt_three
    dsimp [q]
    nlinarith
  have hq1 : 2 ≤ q := by linarith
  have hInt_q : IntegrableOn (fun y : ℝ => Real.exp (-(q * y))) (Ioi x₀) volume := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hq) x₀
  have hInt_q2 : IntegrableOn (fun y : ℝ => Real.exp (-(q / 2 * y))) (Ioi x₀) volume := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (half_pos hq)) x₀
  have hI_q : (∫ y in Ioi x₀, Real.exp (-(q * y))) = Real.exp (-(q * x₀)) / q := by
    have heq : (fun y : ℝ => Real.exp (-(q * y))) = fun y => Real.exp (-q * y) := by
      ext y; rw [neg_mul]
    rw [heq, integral_exp_mul_Ioi (neg_lt_zero.mpr hq) x₀, neg_div_neg_eq, neg_mul]
  have hI_q2 : (∫ y in Ioi x₀, Real.exp (-(q / 2 * y))) = 2 * Real.exp (-(q / 2 * x₀)) / q := by
    have heq : (fun y : ℝ => Real.exp (-(q / 2 * y))) = fun y => Real.exp (-(q / 2) * y) := by
      ext y; rw [neg_mul]
    rw [heq, integral_exp_mul_Ioi (neg_lt_zero.mpr (half_pos hq)) x₀, neg_div_neg_eq, neg_mul]
    ring
  set A1 := C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * x₀ ^ 3) * Real.exp (q * x₀)
  set A2 := C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * (48 / q ^ 3)) * Real.exp (q / 2 * x₀)
  have hDomInt : IntegrableOn (fun y : ℝ =>
      A1 * Real.exp (-(q * y)) + A2 * Real.exp (-(q / 2 * y))) (Ioi x₀) volume :=
    (hInt_q.const_mul A1).add (hInt_q2.const_mul A2)
  have hpt : ∀ y ∈ Ioi x₀,
      2 * c' * y / 3 * |(3 * r₀ - c' * y ^ 2 / 3) / 2 * g (c' * y ^ 2 / 3)| ≤
        A1 * Real.exp (-(q * y)) + A2 * Real.exp (-(q / 2 * y)) := by
    intro y hy
    have hyx₀ : x₀ ≤ y := (mem_Ioi.mp hy).le
    have hy0 : 0 ≤ y := hx₀.le.trans hyx₀
    have ht_lo : r₀ ≤ c' * y ^ 2 / 3 := hr₀.trans (by gcongr)
    have hdiff : |(3 * r₀ - c' * y ^ 2 / 3) / 2| ≤ 2 * (c' * y ^ 2 / 3) :=
      abs_le.mpr ⟨by nlinarith [hr₀], by nlinarith [ht_lo]⟩
    have hs0 : 0 ≤ y - x₀ := sub_nonneg.mpr hyx₀
    have hy3 : y ^ 3 ≤ 4 * (x₀ ^ 3 + (y - x₀) ^ 3) := by nlinarith [sq_nonneg (x₀ - (y - x₀))]
    have hexp_split : Real.exp (-c' * besselL y - π * y) ≤
        Real.exp (-c' * besselL x₀ - π * x₀) * Real.exp (-(q * (y - x₀))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      unfold besselL q
      nlinarith [Real.pi_pos, hs0]
    have hcube := cube_mul_exp_neg_le hq hs0
    have he1 : Real.exp (-(q * (y - x₀))) = Real.exp (q * x₀) * Real.exp (-(q * y)) := by
      rw [← Real.exp_add]; congr 1; ring
    have he2 : Real.exp (-(q / 2 * (y - x₀))) = Real.exp (q / 2 * x₀) * Real.exp (-(q / 2 * y)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [abs_mul]
    calc 2 * c' * y / 3 * (|(3 * r₀ - c' * y ^ 2 / 3) / 2| * |g (c' * y ^ 2 / 3)|)
        ≤ 2 * c' * y / 3 * ((2 * (c' * y ^ 2 / 3)) * (C₀ * Real.exp (-c' * besselL y - π * y))) := by
          gcongr
          exact hg_exp y hyx₀
      _ = C₀ * c' ^ 2 * (4 / 9 * y ^ 3) * Real.exp (-c' * besselL y - π * y) := by ring
      _ ≤ C₀ * c' ^ 2 * (8 / 3 * (x₀ ^ 3 + (y - x₀) ^ 3)) *
            (Real.exp (-c' * besselL x₀ - π * x₀) * Real.exp (-(q * (y - x₀)))) := by
          have h49 : 4 / 9 * y ^ 3 ≤ 8 / 3 * (x₀ ^ 3 + (y - x₀) ^ 3) := by nlinarith [hy3]
          have hx03 : 0 ≤ x₀ ^ 3 + (y - x₀) ^ 3 := by positivity
          gcongr
      _ = C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) *
            ((8 / 3 * x₀ ^ 3) * Real.exp (-(q * (y - x₀))) +
              8 / 3 * ((y - x₀) ^ 3 * Real.exp (-(q * (y - x₀))))) := by ring
      _ ≤ C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) *
            ((8 / 3 * x₀ ^ 3) * Real.exp (-(q * (y - x₀))) +
              8 / 3 * ((48 / q ^ 3) * Real.exp (-(q / 2 * (y - x₀))))) := by
          gcongr
      _ = A1 * Real.exp (-(q * y)) + A2 * Real.exp (-(q / 2 * y)) := by
          rw [he1, he2]; dsimp [A1, A2]; ring
  have hI_dom : (∫ y in Ioi x₀, A1 * Real.exp (-(q * y)) + A2 * Real.exp (-(q / 2 * y))) =
      C₀ * Real.exp (-c' * besselL x₀ - π * x₀) *
        (8 / 3 * x₀ ^ 3 * (c' ^ 2 / q) + 8 / 3 * (96 * c' ^ 2 / q ^ 4)) := by
    rw [integral_add (hInt_q.const_mul A1) (hInt_q2.const_mul A2),
      integral_const_mul, integral_const_mul, hI_q, hI_q2]
    dsimp [A1, A2]
    have e1 : Real.exp (q * x₀) * (Real.exp (-(q * x₀)) / q) = 1 / q := by
      rw [← mul_div_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have e2 : Real.exp (q / 2 * x₀) * (2 * Real.exp (-(q / 2 * x₀)) / q) = 2 / q := by
      calc Real.exp (q / 2 * x₀) * (2 * Real.exp (-(q / 2 * x₀)) / q)
          = 2 * (Real.exp (q / 2 * x₀) * Real.exp (-(q / 2 * x₀))) / q := by ring
        _ = 2 / q := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    calc (C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * x₀ ^ 3) * Real.exp (q * x₀)) *
            (Real.exp (-(q * x₀)) / q) +
          (C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * (48 / q ^ 3)) *
            Real.exp (q / 2 * x₀)) * (2 * Real.exp (-(q / 2 * x₀)) / q)
        = C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * x₀ ^ 3) *
            (Real.exp (q * x₀) * (Real.exp (-(q * x₀)) / q)) +
          C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * (48 / q ^ 3)) *
            (Real.exp (q / 2 * x₀) * (2 * Real.exp (-(q / 2 * x₀)) / q)) := by ring
      _ = C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * x₀ ^ 3) * (1 / q) +
          C₀ * c' ^ 2 * Real.exp (-c' * besselL x₀ - π * x₀) * (8 / 3 * (48 / q ^ 3)) * (2 / q) := by
          rw [e1, e2]
      _ = _ := by ring
  have h1 : c' ^ 2 / q ≤ c' := by
    rw [div_le_iff₀ hq]
    nlinarith
  have h2 : 96 * c' ^ 2 / q ^ 4 ≤ 6 * c' := by
    rw [div_le_iff₀ (by positivity)]
    have hq2 : 4 ≤ q ^ 2 := by nlinarith [hq1]
    have h12 : 4 * c' ^ 2 ≤ q ^ 2 := by nlinarith [hq_ge]
    calc 96 * c' ^ 2 = 24 * (4 * c' ^ 2) := by ring
      _ ≤ 24 * q ^ 2 := by gcongr
      _ = 6 * (4 * q ^ 2) := by ring
      _ ≤ 6 * (q ^ 2 * q ^ 2) := by gcongr
      _ = 6 * (1 * q ^ 4) := by ring
      _ ≤ 6 * (c' * q ^ 4) := by gcongr
      _ = 6 * c' * q ^ 4 := by ring
  have h3 : 8 / 3 * x₀ ^ 3 * (c' ^ 2 / q) + 8 / 3 * (96 * c' ^ 2 / q ^ 4) ≤ 16 * (1 + x₀) ^ 3 * c' := by
    have hx3 : x₀ ^ 3 ≤ (1 + x₀) ^ 3 := by nlinarith [sq_nonneg x₀]
    have h1x : 1 ≤ (1 + x₀) ^ 3 := by nlinarith [sq_nonneg x₀]
    have hpart : 8 / 3 * x₀ ^ 3 * c' + 8 / 3 * (6 * c') ≤ 16 * (1 + x₀) ^ 3 * c' := by nlinarith
    calc 8 / 3 * x₀ ^ 3 * (c' ^ 2 / q) + 8 / 3 * (96 * c' ^ 2 / q ^ 4)
        ≤ 8 / 3 * x₀ ^ 3 * c' + 8 / 3 * (6 * c') := by gcongr
      _ ≤ 16 * (1 + x₀) ^ 3 * c' := hpart
  calc ∫ y in Ioi x₀, 2 * c' * y / 3 * |(3 * r₀ - c' * y ^ 2 / 3) / 2 * g (c' * y ^ 2 / 3)|
      ≤ ∫ y in Ioi x₀, A1 * Real.exp (-(q * y)) + A2 * Real.exp (-(q / 2 * y)) := by
        refine integral_mono_of_nonneg ?_ hDomInt ?_
        · exact (ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun y hy => by have := hx₀.le.trans (mem_Ioi.mp hy).le; positivity)
        · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt)
    _ = C₀ * Real.exp (-c' * besselL x₀ - π * x₀) *
          (8 / 3 * x₀ ^ 3 * (c' ^ 2 / q) + 8 / 3 * (96 * c' ^ 2 / q ^ 4)) := hI_dom
    _ ≤ C₀ * (16 * (1 + x₀) ^ 3 * c') * Real.exp (-c' * besselL x₀ - π * x₀) := by
        calc C₀ * Real.exp (-c' * besselL x₀ - π * x₀) *
              (8 / 3 * x₀ ^ 3 * (c' ^ 2 / q) + 8 / 3 * (96 * c' ^ 2 / q ^ 4))
            ≤ C₀ * Real.exp (-c' * besselL x₀ - π * x₀) * (16 * (1 + x₀) ^ 3 * c') := by gcongr
          _ = C₀ * (16 * (1 + x₀) ^ 3 * c') * Real.exp (-c' * besselL x₀ - π * x₀) := by ring

/-- **`sd:spinmoment-Vtail`**: for `x ≥ xiStar + r₀` (`r₀ > 0`),
`|K^* g₅(c' x²/3)| ≤ C_V c' (1 + x)³ exp (-c' L(x) - π x)`. -/
theorem volterraAdjoint_bumpG_far_le (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ C_V > 0, ∀ᶠ c' in atTop, ∀ x : ℝ, xiStar + r₀ ≤ x →
      |spinVolterraAdjoint (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c')
          (c' * x ^ 2 / 3)| ≤
        C_V * c' * (1 + x) ^ 3 * Real.exp (-c' * besselL x - π * x) := by
  obtain ⟨C₀, hC₀, hbg⟩ := bumpG_far_exp_le N hN hη0 hη1 σs hr₀
  refine ⟨16 * C₀, by positivity, ?_⟩
  filter_upwards [hbg, eventually_ge_atTop (1 : ℝ)] with c' hg hc' x hx
  have hx0 : 0 < x := by linarith [xiStar_pos]
  have hr₀0 : 0 ≤ c' * x ^ 2 / 3 := by positivity
  have hbound := spinVolterra_tail_integral_bound
    (g := bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c')
    hc' hx0 hr₀0 le_rfl hC₀.le (fun y hy => hg y (hx.trans hy))
  have hnorm_le := MeasureTheory.norm_integral_le_integral_norm
    (μ := volume.restrict (Ici (c' * x ^ 2 / 3)))
    (fun t => (3 * (c' * x ^ 2 / 3) - t) / 2 *
      bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t)
  simp only [Real.norm_eq_abs] at hnorm_le
  unfold spinVolterraAdjoint
  calc |∫ t in Ici (c' * x ^ 2 / 3), (3 * (c' * x ^ 2 / 3) - t) / 2 *
          bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t|
      ≤ ∫ t in Ici (c' * x ^ 2 / 3), |(3 * (c' * x ^ 2 / 3) - t) / 2 *
          bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs c' t| := hnorm_le
    _ ≤ C₀ * (16 * (1 + x) ^ 3 * c') * Real.exp (-c' * besselL x - π * x) := hbound
    _ = 16 * C₀ * c' * (1 + x) ^ 3 * Real.exp (-c' * besselL x - π * x) := by ring

/-! ### 4. Charge-uniform Laplace bound and far `x ≥ xiStar + 1` Volterra tail -/

/-- **Charge-uniform Laplace bound** on the radial marginal `spinRadMarginal meas.ν` for `0 < b ≤ 1`:
using `spinOpA F₀ 1 = 0` (`spinOpA_sub_S5` at `b = 1`) together with `κ a ≤ 2π τ - 1/2`,
`∫ e^{-2π b r} dν₀(r) ≤ ((5π/κ + 1)/b) e^{2π a / b}` with a constant independent of `c'` and `B`. -/
theorem spinRadMarginal_laplace_uniform (κ : ℝ) (hκ : 0 < κ) {a B τ : ℝ} (ha : 2 ≤ a)
    (hB : 0 ≤ B) (hτ_pos : 0 < τ) (hτ_lin : κ * a ≤ 2 * π * τ - 1 / 2)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn a X) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∫ r in Ici (0 : ℝ), Real.exp (-2 * π * b * r) ∂(spinRadMarginal meas.ν) ≤
      (5 * π / κ + 1) / b * Real.exp (2 * π * a / b) := by
  have hX_cone : X ⊆ spinConeB B := hX.trans Set.inter_subset_left
  have hA1 : spinOpA (spinMomentF0 a meas.ν) 1 = 0 := by
    have hsub := spinOpA_sub_S5 hB hX_cone meas (one_pos : (0 : ℝ) < 1)
    simp only [Real.one_rpow, inv_one, one_mul, sub_self] at hsub
    linarith
  have hF0eq := spinOpA_F0_eq hB hX_cone meas one_pos
  rw [hA1] at hF0eq
  simp only [one_pow, mul_one, div_one] at hF0eq
  have hId :
      2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν -
        1 / 2 * ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν =
      spinVacuumV a 1 1 / 2 +
        2 * π * (a * Real.exp (2 * π * a) - 2 * (a - 1) * Real.exp (2 * π * (a - 1)) +
          (a - 2) * Real.exp (2 * π * (a - 2))) := by
    linarith [hF0eq]
  have hV1 : spinVacuumV a 1 1 ≤ Real.exp (2 * π * a) := by
    unfold spinVacuumV spinVacuumQ
    have hq1 : 0 ≤ 1 - Real.exp (-2 * π * 1) := by
      have : Real.exp (-2 * π * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by have := Real.pi_pos; linarith)
      linarith
    have hq2 : 1 - Real.exp (-2 * π * 1) ≤ 1 := by linarith [Real.exp_pos (-2 * π * 1)]
    have hQ : Real.exp (π * a * 1) * (1 - Real.exp (-2 * π * 1)) ≤ Real.exp (π * a) := by
      calc Real.exp (π * a * 1) * (1 - Real.exp (-2 * π * 1))
          ≤ Real.exp (π * a) * 1 := mul_le_mul (by simp) hq2 hq1 (Real.exp_pos _).le
        _ = Real.exp (π * a) := mul_one _
    have hQ0 : 0 ≤ Real.exp (π * a * 1) * (1 - Real.exp (-2 * π * 1)) := by positivity
    calc (Real.exp (π * a * 1) * (1 - Real.exp (-2 * π * 1))) *
          (Real.exp (π * a * 1) * (1 - Real.exp (-2 * π * 1)))
        ≤ Real.exp (π * a) * Real.exp (π * a) := mul_le_mul hQ hQ hQ0 (Real.exp_pos _).le
      _ = Real.exp (2 * π * a) := by rw [← Real.exp_add]; congr 1; ring
  have hRhs :
      spinVacuumV a 1 1 / 2 +
        2 * π * (a * Real.exp (2 * π * a) - 2 * (a - 1) * Real.exp (2 * π * (a - 1)) +
          (a - 2) * Real.exp (2 * π * (a - 2))) ≤ 5 * π * a * Real.exp (2 * π * a) := by
    have ha1 : 0 ≤ (a - 1) * Real.exp (2 * π * (a - 1)) := by
      have : 0 ≤ a - 1 := by linarith
      positivity
    have ha2 : (a - 2) * Real.exp (2 * π * (a - 2)) ≤ a * Real.exp (2 * π * a) := by
      have h1 : a - 2 ≤ a := by linarith
      have h2 : Real.exp (2 * π * (a - 2)) ≤ Real.exp (2 * π * a) := by
        apply Real.exp_le_exp.mpr
        have := Real.pi_pos
        linarith
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith)
    have h12 : 1 / 2 ≤ π * a := by
      have := Real.pi_gt_three
      nlinarith
    have hmain : spinVacuumV a 1 1 / 2 + 2 * π * (2 * a * Real.exp (2 * π * a)) ≤
        5 * π * a * Real.exp (2 * π * a) := by
      calc spinVacuumV a 1 1 / 2 + 2 * π * (2 * a * Real.exp (2 * π * a))
          ≤ Real.exp (2 * π * a) / 2 + 4 * π * a * Real.exp (2 * π * a) := by linarith
        _ = (1 / 2 + 4 * π * a) * Real.exp (2 * π * a) := by ring
        _ ≤ (5 * π * a) * Real.exp (2 * π * a) := by gcongr; linarith
        _ = 5 * π * a * Real.exp (2 * π * a) := by ring
    have hpar :
        a * Real.exp (2 * π * a) - 2 * (a - 1) * Real.exp (2 * π * (a - 1)) +
          (a - 2) * Real.exp (2 * π * (a - 2)) ≤ 2 * a * Real.exp (2 * π * a) := by
      nlinarith [ha1, ha2]
    have h2par := mul_le_mul_of_nonneg_left hpar (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith [hmain, h2par]
  have hInt_sum : Integrable (fun p : ℝ × ℝ => (p.1 + p.2) * Real.exp (-2 * π * (p.1 + p.2))) meas.ν := by
    simpa [mul_one] using spin_sum_exp_integrable hB hX_cone meas (one_pos : (0 : ℝ) < 1)
  have hInt_1 : Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * (p.1 + p.2))) meas.ν := by
    simpa [mul_one] using meas.finite_laplace (one_pos : (0 : ℝ) < 1)
  have hLHS :
      κ * a * ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν ≤
        2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν -
          1 / 2 * ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν := by
    have heq1 : ∫ p : ℝ × ℝ, (2 * π * (p.1 + p.2) - 1 / 2) * Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν =
        2 * π * ∫ p : ℝ × ℝ, (p.1 + p.2) * Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν -
          1 / 2 * ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν := by
      have hsub := integral_sub (hInt_sum.const_mul (2 * π)) (hInt_1.const_mul (1 / 2))
      rw [integral_const_mul, integral_const_mul] at hsub
      rw [← hsub]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      ring
    have hInt_diff : Integrable (fun p : ℝ × ℝ =>
        (2 * π * (p.1 + p.2) - 1 / 2) * Real.exp (-2 * π * (p.1 + p.2))) meas.ν := by
      refine ((hInt_sum.const_mul (2 * π)).sub (hInt_1.const_mul (1 / 2))).congr ?_
      refine Eventually.of_forall fun p => ?_
      simp only [Pi.sub_apply]
      ring
    rw [← heq1, ← integral_const_mul]
    refine integral_mono_ae (hInt_1.const_mul (κ * a)) hInt_diff ?_
    have hae : ∀ᵐ p ∂meas.ν, p ∈ X := ae_iff.mpr meas.supp
    filter_upwards [hae] with p hp
    have hptau : τ ≤ p.1 + p.2 := (hX hp).2
    have hkap : κ * a ≤ 2 * π * (p.1 + p.2) - 1 / 2 :=
      hτ_lin.trans (by have := Real.pi_pos; nlinarith)
    exact mul_le_mul_of_nonneg_right hkap (Real.exp_pos _).le
  have hInt1_le :
      ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν ≤ 5 * π / κ * Real.exp (2 * π * a) := by
    have h1 : κ * a * ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν ≤
        5 * π * a * Real.exp (2 * π * a) := hLHS.trans (hId ▸ hRhs)
    have hka : 0 < κ * a := by positivity
    have ha0 : a ≠ 0 := by linarith
    calc ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν
        ≤ (5 * π * a * Real.exp (2 * π * a)) / (κ * a) := (le_div_iff₀' hka).mpr h1
      _ = 5 * π / κ * Real.exp (2 * π * a) := by field_simp
  have hy1 : 1 ≤ b⁻¹ := (one_le_inv₀ hb0).mpr hb1
  have hy0 : 0 < b⁻¹ := inv_pos.mpr hb0
  have hInt_y :
      ∫ p : ℝ × ℝ, Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν ≤
        ∫ p : ℝ × ℝ, Real.exp (-2 * π * (p.1 + p.2)) ∂meas.ν := by
    refine integral_mono_ae (meas.finite_laplace hy0) (by simpa using hInt_1) ?_
    filter_upwards [ae_iff.mpr meas.supp] with p hp
    have hp0 : 0 ≤ p.1 + p.2 := hτ_pos.le.trans (hX hp).2
    apply Real.exp_le_exp.mpr
    have := Real.pi_pos
    have hmul : 2 * π * (p.1 + p.2) ≤ 2 * π * b⁻¹ * (p.1 + p.2) :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hy1) hp0
    linarith
  have hVy : spinVacuumV a b⁻¹ b⁻¹ ≤ Real.exp (2 * π * a / b) := by
    unfold spinVacuumV spinVacuumQ
    have hq1 : 0 ≤ 1 - Real.exp (-2 * π * b⁻¹) := by
      have : Real.exp (-2 * π * b⁻¹) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := Real.pi_pos; nlinarith)
      linarith
    have hq2 : 1 - Real.exp (-2 * π * b⁻¹) ≤ 1 := by linarith [Real.exp_pos (-2 * π * b⁻¹)]
    have hQ : Real.exp (π * a * b⁻¹) * (1 - Real.exp (-2 * π * b⁻¹)) ≤ Real.exp (π * a * b⁻¹) := by
      calc Real.exp (π * a * b⁻¹) * (1 - Real.exp (-2 * π * b⁻¹))
          ≤ Real.exp (π * a * b⁻¹) * 1 := mul_le_mul_of_nonneg_left hq2 (Real.exp_pos _).le
        _ = Real.exp (π * a * b⁻¹) := mul_one _
    have hQ0 : 0 ≤ Real.exp (π * a * b⁻¹) * (1 - Real.exp (-2 * π * b⁻¹)) := by positivity
    calc (Real.exp (π * a * b⁻¹) * (1 - Real.exp (-2 * π * b⁻¹))) *
          (Real.exp (π * a * b⁻¹) * (1 - Real.exp (-2 * π * b⁻¹)))
        ≤ Real.exp (π * a * b⁻¹) * Real.exp (π * a * b⁻¹) := mul_le_mul hQ hQ hQ0 (Real.exp_pos _).le
      _ = Real.exp (2 * π * a / b) := by rw [← Real.exp_add, div_eq_mul_inv]; congr 1; ring
  have hF0y : spinMomentF0 a meas.ν b⁻¹ ≤ (5 * π / κ + 1) * Real.exp (2 * π * a / b) := by
    unfold spinMomentF0
    have hexp1y : Real.exp (2 * π * a) ≤ Real.exp (2 * π * a / b) := by
      apply Real.exp_le_exp.mpr
      have : 2 * π * a ≤ 2 * π * a * b⁻¹ := le_mul_of_one_le_right (by positivity) hy1
      rwa [div_eq_mul_inv]
    calc ∫ p : ℝ × ℝ, Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν + spinVacuumV a b⁻¹ b⁻¹
        ≤ (5 * π / κ * Real.exp (2 * π * a)) + Real.exp (2 * π * a / b) :=
          add_le_add (hInt_y.trans hInt1_le) hVy
      _ ≤ 5 * π / κ * Real.exp (2 * π * a / b) + Real.exp (2 * π * a / b) := by gcongr
      _ = (5 * π / κ + 1) * Real.exp (2 * π * a / b) := by ring
  have hcross := meas.crossing hb0 hb0
  have hInt_b := meas.finite_laplace hb0
  have hInt_bi := meas.finite_laplace hy0
  have hF0_cross : spinMomentF0 a meas.ν b = b⁻¹ * spinMomentF0 a meas.ν b⁻¹ := by
    have hbb : (b * b) ^ (-(1 / 2 : ℝ)) = b⁻¹ := by
      rw [← sq, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      norm_num
      exact Real.rpow_neg_one b
    have hL : ∫ p : ℝ × ℝ, spinThermalX b b p.1 p.2 ∂meas.ν =
        (∫ p : ℝ × ℝ, Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν) -
          b⁻¹ * (∫ p : ℝ × ℝ, Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) ∂meas.ν) := by
      have heq : (fun p : ℝ × ℝ => spinThermalX b b p.1 p.2) =
          fun p : ℝ × ℝ => Real.exp (-2 * π * b * (p.1 + p.2)) -
            b⁻¹ * Real.exp (-2 * π * b⁻¹ * (p.1 + p.2)) := by
        ext p
        unfold spinThermalX
        have he1 : -2 * π * (b * p.1 + b * p.2) = -2 * π * b * (p.1 + p.2) := by ring
        have he2 : -2 * π * (p.1 / b + p.2 / b) = -2 * π * b⁻¹ * (p.1 + p.2) := by
          simp only [div_eq_mul_inv]; ring
        rw [he1, he2, hbb]
      rw [heq, integral_sub hInt_b (hInt_bi.const_mul b⁻¹), integral_const_mul]
    have hR : -spinThermalXVac a b b =
        -spinVacuumV a b b + b⁻¹ * spinVacuumV a b⁻¹ b⁻¹ := by
      unfold spinThermalXVac
      rw [hbb]; ring
    rw [hL, hR] at hcross
    unfold spinMomentF0
    linarith
  have hVb_nn : 0 ≤ spinVacuumV a b b := by
    unfold spinVacuumV
    exact mul_self_nonneg (spinVacuumQ a b)
  have hMap :
      ∫ r in Ici (0 : ℝ), Real.exp (-2 * π * b * r) ∂(spinRadMarginal meas.ν) =
        ∫ p : ℝ × ℝ, Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν := by
    have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
    have hmeas_exp : AEStronglyMeasurable (fun r : ℝ => Real.exp (-2 * π * b * r))
        (Measure.map (fun p : ℝ × ℝ => p.1 + p.2) meas.ν) :=
      (Continuous.stronglyMeasurable (by continuity)).aestronglyMeasurable
    have hae_nonneg : ∀ᵐ r ∂(spinRadMarginal meas.ν), r ∈ Ici (0 : ℝ) := by
      rw [ae_iff]
      unfold spinRadMarginal
      rw [show {a : ℝ | a ∉ Ici 0} = (Ici 0)ᶜ from rfl,
        Measure.map_apply hmeas_sum measurableSet_Ici.compl]
      refine measure_mono_null (fun p hp => ?_) meas.supp
      intro hpX
      exact hp (hτ_pos.le.trans (hX hpX).2)
    rw [MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero (by simpa [ae_iff] using hae_nonneg)]
    unfold spinRadMarginal
    rw [MeasureTheory.integral_map hmeas_sum.aemeasurable hmeas_exp]
  rw [hMap]
  calc ∫ p : ℝ × ℝ, Real.exp (-2 * π * b * (p.1 + p.2)) ∂meas.ν
      ≤ spinMomentF0 a meas.ν b := by unfold spinMomentF0; linarith
    _ = b⁻¹ * spinMomentF0 a meas.ν b⁻¹ := hF0_cross
    _ ≤ b⁻¹ * ((5 * π / κ + 1) * Real.exp (2 * π * a / b)) := by gcongr
    _ = (5 * π / κ + 1) / b * Real.exp (2 * π * a / b) := by ring

/-- info: 'FormalResearch.ModularBootstrap.Spin.bumpG_far_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpG_far_exp_le

/-- info: 'FormalResearch.ModularBootstrap.Spin.volterraAdjoint_bumpG_far_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms volterraAdjoint_bumpG_far_le

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinRadMarginal_laplace_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinRadMarginal_laplace_uniform

end FormalResearch.ModularBootstrap.Spin
