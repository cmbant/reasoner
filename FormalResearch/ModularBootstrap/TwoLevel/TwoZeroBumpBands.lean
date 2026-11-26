module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpLobe
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumBand

/-!
# The intermediate and far bands of the bumped two-zero comb at every weight (`ut:T2`, "Far band and assembly")

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`) at fixed `(w, Q)`, `h₂^{(p)} = sech² T_{χ(p)} B₁^{(p)}`.

* `twoZero_band_bound_w`: `twoZero_band_bound` without its unused weight-one hypothesis (the window bound
  `cardyWindowBound_prob` holds at every weight);
* `twoZeroBump_band_bound`: `∫_{χ_{N₁+1} ≤ x ≤ ξ_* + r₀} |h₂^{(p)}| V dt ≤ F_{2,c} C_T N₁^{-1}` for the bumped comb, from
  `|h₂^{(p)}| ≤ C_p |h₂|` (`combProfile_bump_ratio`), uniformly in the cut;
* `twoZero_norm_far`: `‖B₂(x)‖ e^{c L(x)} ≤ C_b` for `x ≥ ξ_* + r₀`;
* `twoZeroBump_far_bound`: `∫_{x ≥ ξ_* + r₀} |h₂^{(p)}| V dt ≤ C_far √c` at every weight (the factor `(1+x)^{w-1}`
  of `cardyFarBoundP_prob` is integrated against `e^{-πx}`, `farConstP`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Window.Tail FormalResearch.ModularBootstrap.Upper.Bump
open TwoZeroDesign

/-- **The band bound of `ut:T2` at every weight** (`twoZero_band_bound` without the unused `prob.w = 1`). -/
theorem twoZero_band_bound_w (prob : FixedWeightProblem) {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ N₂ : ℕ, ∃ C_T : ℝ, 0 ≤ C_T ∧ ∀ N₁ : ℕ, N₂ ≤ N₁ → ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) ≤
        twoZeroF prob c * C_T * (N₁ : ℝ)⁻¹ := by
  obtain ⟨N₂, C_T, hCT, h⟩ := twoZero_band_bound_of_cardy (qProb_pos prob) hr₀
    (cardyWindowBound_prob prob (qProb_pos prob) hr₀) hK hA
  refine ⟨N₂, C_T, hCT, fun N₁ hN₁ => ?_⟩
  filter_upwards [h N₁ hN₁, eventually_gt_atTop (0 : ℝ)] with c hc hc0 d hd
  rw [twoZeroF_eq_FVc prob hc0]
  exact hc d hd

/-- **The intermediate band of the bumped comb, every weight**: for `N₁ ≥ N₂`, `c` large, `d ∈ 𝒦` and every cut
`N' ≥ n + 2`, `∫_{χ_{N₁+1} ≤ x ≤ ξ_* + r₀} |h₂^{(p)}| V dt ≤ F_{2,c} C_T N₁^{-1}`. -/
theorem twoZeroBump_band_bound (prob : FixedWeightProblem) (bd : BumpData) {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ N₂ : ℕ, ∃ C_T : ℝ, 0 ≤ C_T ∧ ∀ N₁ : ℕ, N₂ ≤ N₁ → ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      (∫ t in Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3),
          |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) ≤
        twoZeroF prob c * C_T * (N₁ : ℝ)⁻¹ := by
  obtain ⟨N₂, C_T, hCT, h⟩ := twoZero_band_bound_w prob hr₀ hK hA
  obtain ⟨Cp, C', hrat⟩ := combProfile_bump_ratio (n := n) bd
  obtain ⟨Cp', hCp'⟩ : ∃ Cp' : ℝ, Cp' = max Cp 0 := ⟨_, rfl⟩
  have hCp'0 : 0 ≤ Cp' := by rw [hCp']; exact le_max_right _ _
  refine ⟨N₂, Cp' * C_T, by positivity, fun N₁ hN₁ => ?_⟩
  filter_upwards [h N₁ hN₁, hrat, twoZeroBump_innerCombHyp bd hK hA, twoZeroComb_innerCombHyp hK hA,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift)]
    with c hb hr hIb hI0 hc hcS d hd N' hN'
  have hξ := xiStar_pos
  have hχ : 0 ≤ c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3 := by positivity
  have hcb : ContinuousOn (fun t => |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) (Ici 0) :=
    ((hIb d hd N' hN').continuousOn_combProfile hc).abs.mul
      (Crossing.continuous_cardyV prob (c / 12)).continuousOn
  have hc0' : ContinuousOn (fun t => |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) (Ici 0) :=
    ((hI0 d hd).continuousOn_combProfile hc).abs.mul
      (Crossing.continuous_cardyV prob (c / 12)).continuousOn
  have hf : IntegrableOn (fun t => |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t)
      (Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3)) :=
    ContinuousOn.integrableOn_Icc (hcb.mono (fun t ht => (show (0 : ℝ) ≤ t from hχ.trans ht.1)))
  have hg0 : IntegrableOn (fun t => |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t)
      (Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3)) :=
    ContinuousOn.integrableOn_Icc (hc0'.mono (fun t ht => (show (0 : ℝ) ≤ t from hχ.trans ht.1)))
  have hg := hg0.const_mul Cp'
  calc (∫ t in Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3),
          |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t)
      ≤ ∫ t in Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3),
          Cp' * (|combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) := by
        refine setIntegral_mono_on hf hg measurableSet_Icc fun t ht => ?_
        have ht0 : 0 ≤ t := hχ.trans ht.1
        obtain ⟨R, hR1, hRC, -, hRe⟩ := hr d N' hN' t
        have hV0 : 0 ≤ prob.cardyV (c / 12) t := prob.cardyV_nonneg (by linarith) ht0
        rw [hRe, abs_mul, abs_of_nonneg (by linarith : 0 ≤ R)]
        have : R ≤ Cp' := hRC.trans (by rw [hCp']; exact le_max_left _ _)
        calc R * |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t
            = R * (|combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) := by ring
          _ ≤ Cp' * (|combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t) :=
              mul_le_mul_of_nonneg_right this (mul_nonneg (abs_nonneg _) hV0)
    _ = Cp' * ∫ t in Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * prob.cardyV (c / 12) t := integral_const_mul _ _
    _ ≤ Cp' * (twoZeroF prob c * C_T * (N₁ : ℝ)⁻¹) := mul_le_mul_of_nonneg_left (hb d hd) hCp'0
    _ = twoZeroF prob c * (Cp' * C_T) * (N₁ : ℝ)⁻¹ := by ring

/-- `‖B₂(x)‖ e^{c L(x)} ≤ C_b` for `x ≥ ξ_* + r₀` (`|T_{χ(p)}| ≤ 1`, Lemma `T` far band at `f = 2`),
uniformly on a compact family. -/
theorem twoZero_norm_far {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + r₀ ≤ x →
      ‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤ Cb := by
  obtain ⟨Cr, hCr, hrfar⟩ := refComb_far_bound (f := 2) (by norm_num) (η₀ := 1 / 4) (r₀ := r₀)
    (by norm_num) le_rfl hr₀
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨Kd, hKd0, hDev⟩ := designComb_norm_le_exp_ref 2 (n + 2) (by norm_num) (by omega) M E
    (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = max (phiQuantile (((n + 2 : ℕ) : ℝ) + 2)) M := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]; exact lt_of_lt_of_le (phiQuantile_succ_succ_pos (n + 2)) (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hξ := xiStar_pos
  refine ⟨2 * Cr, by positivity, ?_⟩
  have hlam_ev : ∀ᶠ c in atTop, lambdaComb c ≤ r₀ / (4 * s) ∧ Kd * lambdaComb c ≤ r₀ * Real.log 2 := by
    have e1 := tendsto_lambdaComb_atTop.eventually
      (eventually_le_nhds (show (0 : ℝ) < r₀ / (4 * s) by positivity))
    have h2 := tendsto_lambdaComb_atTop.const_mul Kd
    rw [mul_zero] at h2
    exact e1.and (h2.eventually (eventually_le_nhds (show (0 : ℝ) < r₀ * Real.log 2 by positivity)))
  filter_upwards [hDev, eventually_gt_atTop (0 : ℝ), hlam_ev, hrfar]
    with c hDev' hc hlam hrfar' d hd x hx'
  have hlampos := lambdaComb_pos' hc
  have hFb' := comb_family_bounds hlampos (hb d hd)
  have hxξ : r₀ ≤ x - xiStar := by linarith
  have hxξ0 : 0 < x - xiStar := by linarith
  have h4s : xiStar + 4 * max (phiQuantile (((n + 2 : ℕ) : ℝ) + 2)) M * lambdaComb c ≤ x := by
    rw [← hs_def]
    have : 4 * s * lambdaComb c ≤ r₀ := by
      have := hlam.1
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    linarith
  have hlog : Kd * (lambdaComb c / (x - xiStar)) ≤ Real.log 2 := by
    calc Kd * (lambdaComb c / (x - xiStar)) = (Kd * lambdaComb c) / (x - xiStar) := by ring
      _ ≤ (r₀ * Real.log 2) / (x - xiStar) := div_le_div_of_nonneg_right hlam.2 hxξ0.le
      _ ≤ (r₀ * Real.log 2) / r₀ :=
          div_le_div_of_nonneg_left (by positivity) hr₀ hxξ
      _ = Real.log 2 := by field_simp
  have hBn1 := norm_le_two_of_exp (norm_nonneg _)
    (hDev' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) hFb'.1 hFb'.2 x h4s) hlog
  rw [norm_twoZeroComb_ofReal]
  have hT1 := abs_tFac_le_one (d.chiP c) x
  have hB1 : ‖d.comb c (x : ℂ)‖ ≤ 2 * ‖refComb c 2 (1 / 4) (x : ℂ)‖ := hBn1
  have hre := hrfar' x hx'
  have hexp := (Real.exp_pos (c * Bessel.besselL x)).le
  calc |tFac (d.chiP c) x| * ‖d.comb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)
      ≤ 1 * (2 * ‖refComb c 2 (1 / 4) (x : ℂ)‖) * Real.exp (c * Bessel.besselL x) := by
        gcongr
    _ = 2 * (‖refComb c 2 (1 / 4) (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)) := by ring
    _ ≤ 2 * Cr := by linarith

/-- **The far band of the bumped comb, every weight**: `∫_{x ≥ ξ_* + r₀} |h₂^{(p)}| V dt ≤ C_far √c`, uniformly on a
compact family and in the cut (`rem:cardy`: `V e^{-cL} dt ≤ 2^p √c √x (1+x)^p dx`, integrated against `e^{-πx}`). -/
theorem twoZeroBump_far_bound (prob : FixedWeightProblem) (bd : BumpData) {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C_far : ℝ, 0 ≤ C_far ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      (∫ t in Ici (c * (xiStar + r₀) ^ 2 / 3), |combProfile c (d.bumpComb bd c N') t| *
          prob.cardyV (c / 12) t) ≤ C_far * √c := by
  have hξ := xiStar_pos
  have hx0 : 0 < xiStar + r₀ := by linarith
  obtain ⟨CF, cF, hCF, hFb⟩ := cardyFarBoundP_prob prob (x₀ := xiStar + r₀) hx0
  obtain ⟨Cb, hCb0, hnorm⟩ := twoZero_norm_far hr₀ hK hA
  obtain ⟨Cp, C', hbc⟩ := bumpComb_ofReal (n := n) bd
  obtain ⟨Cp', hCp'⟩ : ∃ Cp' : ℝ, Cp' = max Cp 0 := ⟨_, rfl⟩
  have hCp'0 : 0 ≤ Cp' := by rw [hCp']; exact le_max_right _ _
  refine ⟨4 * (Cp' * Cb) * CF * farConstP (prob.w - 1), ?_, ?_⟩
  · have := farConstP_nonneg (prob.w - 1)
    positivity
  filter_upwards [hnorm, hbc, eventually_ge_atTop cF, eventually_gt_atTop (0 : ℝ)]
    with c hnorm' hbc' hcF hc d hd N' hN'
  have hfin : ∀ x ∈ Ici (xiStar + r₀), 0 < x ∧
      0 ≤ |combProfile c (d.bumpComb bd c N') (c * x ^ 2 / 3)| * prob.cardyV (c / 12) (c * x ^ 2 / 3) ∧
      (2 * c * x / 3) * (|combProfile c (d.bumpComb bd c N') (c * x ^ 2 / 3)| *
          prob.cardyV (c / 12) (c * x ^ 2 / 3)) ≤
        4 * (Cp' * Cb) * CF * √c * (x ^ (1 / 2 : ℝ) * (1 + x) ^ (prob.w - 1) * Real.exp (-π * x)) := by
    intro x hx
    have hx' : xiStar + r₀ ≤ x := hx
    have hxpos : 0 < x := by linarith
    obtain ⟨hv0, hw⟩ := hFb c hcF x hx'
    refine ⟨hxpos, mul_nonneg (abs_nonneg _) hv0, ?_⟩
    obtain ⟨R, hR1, hRC, -, hRe⟩ := hbc' d N' hN' x hxpos.le
    have hB : ‖d.bumpComb bd c N' (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤ Cp' * Cb := by
      rw [norm_bumpComb_le hRe hR1]
      have h1 := hnorm' d hd x hx'
      have hRp : R ≤ Cp' := hRC.trans (by rw [hCp']; exact le_max_left _ _)
      calc R * ‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)
          = R * (‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x)) := by ring
        _ ≤ Cp' * Cb := mul_le_mul hRp h1 (by positivity) hCp'0
    exact integrand_far_leP (prob.w - 1) (B := d.bumpComb bd c N') hc hxpos hv0 hB hw
  have := far_integral_leP (prob.w - 1) (c' := c) (x1 := xiStar + r₀)
    (g := fun t => |combProfile c (d.bumpComb bd c N') t| * prob.cardyV (c / 12) t) hc hx0
    (by positivity : (0 : ℝ) ≤ 4 * (Cp' * Cb) * CF * √c) hfin
  refine this.trans (le_of_eq ?_)
  ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_band_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_band_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_far_bound

end FormalResearch.ModularBootstrap.TwoLevel
