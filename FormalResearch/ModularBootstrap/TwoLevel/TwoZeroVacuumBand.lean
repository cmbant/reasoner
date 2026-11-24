module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumPrelim
public import FormalResearch.ModularBootstrap.Upper.Window.Tail

/-!
# The intermediate and far bands for the two-zero comb (`upper_transfer.tex`, `ut:T2`, "Far band and assembly")

For `B₂ = T_{χ(p)} B₁` (`twoZeroComb`), `h₂ = sech² B₂`, `r₀ > 0` (`r₀ = 3/10` in the paper), the Cardy weight `V`
(an abstract weight with the window and far-band bounds of Lemma `A_V`, or `prob.cardyV (c/12)` for `prob.w = 1`), and
`F_{2,c} = twoZeroF`: uniformly on a compact family of admissible designs and for all large `c`,

* `twoZero_band_bound_of_cardy`, `twoZero_band_bound`: for `N₁ ≥ N₂`,
  `∫_{χ_{N₁+1} ≤ x ≤ ξ_* + r₀} |h₂| V dt ≤ F_{2,c} C_T N₁^{-1}` (`eq:ut:T2-right-tail`): the proof of Lemma `T`
  (`Window.Tail`, `K6`(a), `K4`, `K0`(c)) at `f = 2` with the extra factor `|T_{χ(p)}(x)| ≤ 2(x - ξ_*)`, which lowers
  the power `(x - ξ_*)^{-7/2}` of the reference comb to `(x - ξ_*)^{-5/2}`;
* `twoZero_far_bound_of_cardy`, `twoZero_far_bound`: `∫_{x ≥ ξ_* + r₀} |h₂| V dt ≤ C_far √c` (`|T_{χ(p)}| ≤ 1`, Lemma `T`
  far band at `f = 2`).

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
  FormalResearch.ModularBootstrap.Upper.Window.Tail
open TwoZeroDesign

/-- `|T_χ(x)| ≤ 2 (x - ξ_*)` for `χ = ξ_* + λ σ`, `|σ| ≤ s` and `x ≥ ξ_* + 4 s λ`. -/
lemma abs_tFac_le_two_mul {χ x lam s σ : ℝ} (hlam : 0 < lam) (hχ : χ = xiStar + lam * σ) (hσ : |σ| ≤ s)
    (hx : xiStar + 4 * s * lam ≤ x) : |tFac χ x| ≤ 2 * (x - xiStar) := by
  have hs0 : 0 ≤ s := (abs_nonneg _).trans hσ
  have hxξ0 : 0 ≤ x - xiStar := by nlinarith [mul_nonneg hs0 hlam.le]
  refine (abs_tFac_le _ _).trans ?_
  have hx1 : x - χ = (x - xiStar) - lam * σ := by rw [hχ]; ring
  have h1 : |x - χ| ≤ (x - xiStar) + lam * s := by
    rw [hx1]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hxξ0, abs_mul, abs_of_pos hlam]
    have := mul_le_mul_of_nonneg_left hσ hlam.le
    linarith
  have h2 : lam * s ≤ (x - xiStar) / 4 := by nlinarith
  have hpi : π < 3.15 := Real.pi_lt_d2
  have h5 : |x - χ| ≤ 5 / 4 * (x - xiStar) := by linarith
  calc π * |x - χ| / 2 ≤ π * (5 / 4 * (x - xiStar)) / 2 := by gcongr
    _ ≤ 2 * (x - xiStar) := by nlinarith

/-- The pointwise bound of the integrand on the intermediate band, with the extra factor of `T_{χ(p)}`. -/
lemma twoZero_band_pt {c x CR CR' CA W D lam rn v : ℝ} {B : ℂ → ℂ} (hc : 0 < c) (hx : 0 < x)
    (hxξ : 0 < x - xiStar) (hlam : lam = lambdaComb c) (hv0 : 0 ≤ v)
    (hw : v * Real.exp (-(c * Bessel.besselL x)) * (1 / Real.cosh (π * x / 2) ^ 2) *
      (2 / 3 * c * x * lambdaComb c) ≤ CA * W)
    (hBn : ‖B (x : ℂ)‖ ≤ 2 * (2 * (x - xiStar) * rn))
    (hRx : rn * Real.exp (c * Bessel.besselL x) ≤ CR * (D / (π * (x - xiStar))) ^ (7 / 2 : ℝ))
    (hD : 0 ≤ D) (hCR' : CR' = 2 * CR * D / π) :
    (2 * c * x / 3) * (|combProfile c B (c * x ^ 2 / 3)| * v) ≤
      2 * CR' * CA * (D / π) ^ (5 / 2 : ℝ) * W / lam * (x - xiStar) ^ (-(5 / 2 : ℝ)) := by
  have hπ := Real.pi_pos
  have hR : (2 * (x - xiStar) * rn) * Real.exp (c * Bessel.besselL x) ≤
      CR' * (D / (π * (x - xiStar))) ^ (5 / 2 : ℝ) := by
    rcases hD.eq_or_lt with hD0 | hD0
    · subst hD0
      have h0 : (2 * (x - xiStar) * rn) * Real.exp (c * Bessel.besselL x) ≤ 0 := by
        have h1 : rn * Real.exp (c * Bessel.besselL x) ≤ 0 := by
          refine hRx.trans (le_of_eq ?_)
          have : (0 : ℝ) / (π * (x - xiStar)) = 0 := zero_div _
          rw [this, Real.zero_rpow (by norm_num), mul_zero]
        nlinarith [mul_nonneg hxξ.le (Real.exp_pos (c * Bessel.besselL x)).le]
      refine h0.trans ?_
      rw [hCR']
      have : (0 : ℝ) / (π * (x - xiStar)) = 0 := zero_div _
      simp [this]
    · have hb0 : 0 < D / (π * (x - xiStar)) := by positivity
      have e1 : (D / (π * (x - xiStar))) ^ (7 / 2 : ℝ) =
          (D / (π * (x - xiStar))) ^ (5 / 2 : ℝ) * (D / (π * (x - xiStar))) := by
        rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.rpow_add hb0, Real.rpow_one]
      calc (2 * (x - xiStar) * rn) * Real.exp (c * Bessel.besselL x)
          = (2 * (x - xiStar)) * (rn * Real.exp (c * Bessel.besselL x)) := by ring
        _ ≤ (2 * (x - xiStar)) * (CR * (D / (π * (x - xiStar))) ^ (7 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hRx (by positivity)
        _ = CR' * (D / (π * (x - xiStar))) ^ (5 / 2 : ℝ) := by
            rw [e1, hCR']
            field_simp
  exact band_pointwise hc hx hxξ hlam hv0 hw hBn hR hD

/-- **The intermediate band of `ut:T2`** for an abstract Cardy weight `V` with `CardyWindowBound V q r₀`
(`F_{2,c} = FV_c (2√2/(πλ))^{5/2}` with `FV_c = FVc q c`). -/
theorem twoZero_band_bound_of_cardy {V : ℝ → ℝ → ℝ} {q r₀ : ℝ} (hq : 0 < q) (hr₀ : 0 < r₀)
    (hW : CardyWindowBound V q r₀) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ N₂ : ℕ, ∃ C_T : ℝ, 0 ≤ C_T ∧ ∀ N₁ : ℕ, N₂ ≤ N₁ → ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Icc (c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + r₀) ^ 2 / 3),
          |combProfile c (d.twoZeroComb c) t| * V c t) ≤
        FVc q c * (2 * √2 / (π * lambdaComb c)) ^ (5 / 2 : ℝ) * C_T * (N₁ : ℝ)⁻¹ := by
  obtain ⟨CA, cA, hCA, hWb⟩ := hW
  obtain ⟨CR, hCR, hRb⟩ := refComb_band_bound (f := 2) (by norm_num) (r₀ := r₀)
    (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨S₁, hS₁0, hS₁⟩ := hK.exists_sigmaP_bound
  obtain ⟨Kd, hKd0, hDev⟩ := designComb_norm_le_exp_ref 2 (n + 2) (by norm_num) (by omega) M E
    (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨s₀, hs₀_def⟩ : ∃ s₀ : ℝ, s₀ = max (phiQuantile (((n + 2 : ℕ) : ℝ) + 2)) M := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = max s₀ S₁ := ⟨_, rfl⟩
  have hs₀ : 0 < s₀ := by
    rw [hs₀_def]; exact lt_of_lt_of_le (phiQuantile_succ_succ_pos (n + 2)) (le_max_left _ _)
  have hs : 0 < s := lt_of_lt_of_le hs₀ (by rw [hs_def]; exact le_max_left _ _)
  have hs₀s : s₀ ≤ s := by rw [hs_def]; exact le_max_left _ _
  have hS₁s : S₁ ≤ s := by rw [hs_def]; exact le_max_right _ _
  have hκ : 0 < (1 + c1K0) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by linarith [c1K0_pos]) _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₂, hN₂⟩ := exists_N₂ (max (4 * s) (Kd / Real.log 2) / (1 + c1K0) ^ (-(2 / 3 : ℝ)))
  have hπ := Real.pi_pos
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = 4 * √2 * Real.cosh (π * r₀ / 2) := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hD_def]; have := Real.cosh_pos (π * r₀ / 2); positivity
  obtain ⟨CR', hCR'⟩ : ∃ CR' : ℝ, CR' = 2 * CR * D / π := ⟨_, rfl⟩
  have hCR'0 : 0 < CR' := by rw [hCR']; positivity
  obtain ⟨C_T, hCT_def⟩ : ∃ C_T : ℝ, C_T = 2 * CR' * CA * (D / (2 * √2)) ^ (5 / 2 : ℝ) *
      ((1 + c1K0) ^ (-(2 / 3 : ℝ))) ^ (1 - 5 / 2 : ℝ) / (5 / 2 - 1) := ⟨_, rfl⟩
  have hCT0 : 0 ≤ C_T := by rw [hCT_def]; positivity
  refine ⟨max N₂ 8, C_T, hCT0, fun N₁ hN₁ => ?_⟩
  have h8 : 8 ≤ N₁ := (le_max_right _ _).trans hN₁
  have hΘ := hN₂ N₁ ((le_max_left _ _).trans hN₁)
  have hN1 : 1 ≤ N₁ := by omega
  have hN1pos : (0 : ℝ) < N₁ := by exact_mod_cast hN1
  have hN14s : (1 / 4 : ℝ) < ((N₁ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
    linarith
  have hΦ : max (4 * s) (Kd / Real.log 2) ≤
      (1 + c1K0) ^ (-(2 / 3 : ℝ)) * phiQuantile ((N₁ + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hκ] at hΘ; linarith
  have hp27 : (2 * (((2 : ℕ) : ℝ) - 1 / 4)) = 7 / 2 := by norm_num
  filter_upwards [hRb N₁ (by omega), hDev, eventually_ge_atTop cA,
    eventually_siteRadius_le_one (((N₁ + 1 : ℕ) : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with c hRb' hDev' hcA hr1 hc
  intro d hd
  have hlam := lambdaComb_pos' hc
  have hξ := xiStar_pos
  have hgeo := band_geometry hc hKd0 hs hN1 (hr1 hN14s.le) hΦ
  have hξa : xiStar < chiQuantile c ((N₁ + 1 : ℕ) : ℝ) := xiStar_lt_chiQuantile hc hN14s
  have hW0 : 0 < FVc q c := FVc_pos hq hc
  have hFb := comb_family_bounds hlam (hb d hd)
  by_cases hab : chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ≤ xiStar + r₀
  · have hKc0 : 0 ≤ 2 * CR' * CA * (D / π) ^ (5 / 2 : ℝ) * FVc q c / lambdaComb c := by positivity
    have hfin : ∀ x ∈ Icc (chiQuantile c ((N₁ + 1 : ℕ) : ℝ)) (xiStar + r₀), 0 < x ∧
        0 ≤ V c (c * x ^ 2 / 3) ∧
        (2 * c * x / 3) * (|combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3)| * V c (c * x ^ 2 / 3)) ≤
          2 * CR' * CA * (D / π) ^ (5 / 2 : ℝ) * FVc q c / lambdaComb c * (x - xiStar) ^ (-(5 / 2 : ℝ)) := by
      intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      have hxξ0 : 0 < x - xiStar := by linarith [hx.1]
      obtain ⟨hv0, hw⟩ := hWb c hcA x (by linarith [hx.1]) hx.2
      obtain ⟨h4s, hlog⟩ := hgeo.2 x hx.1
      have h4s₀ : xiStar + 4 * s₀ * lambdaComb c ≤ x := by
        have := mul_le_mul_of_nonneg_right hs₀s hlam.le
        nlinarith
      have h4s₀' : xiStar + 4 * max (phiQuantile (((n + 2 : ℕ) : ℝ) + 2)) M * lambdaComb c ≤ x := by
        rw [← hs₀_def]; exact h4s₀
      have hBn1 := norm_le_two_of_exp (norm_nonneg _)
        (hDev' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) hFb.1 hFb.2 x h4s₀') hlog
      have hRx := hRb' x hx.1 hx.2
      rw [hp27, ← hD_def] at hRx
      have hσ : |d.sigmaP| ≤ s := (hS₁ d hd).trans hS₁s
      have h4sx : xiStar + 4 * s * lambdaComb c ≤ x := h4s
      have hTb : |tFac (d.chiP c) x| ≤ 2 * (x - xiStar) :=
        abs_tFac_le_two_mul hlam (chiP_eq d c |>.trans (by rw [neg_div]; simp [sigmaP, neg_div])) hσ h4sx
      have hBn : ‖d.twoZeroComb c (x : ℂ)‖ ≤ 2 * (2 * (x - xiStar) * ‖refComb c 2 (1 / 4) (x : ℂ)‖) := by
        rw [norm_twoZeroComb_ofReal]
        have hB1 : ‖d.comb c (x : ℂ)‖ ≤ 2 * ‖refComb c 2 (1 / 4) (x : ℂ)‖ := hBn1
        calc |tFac (d.chiP c) x| * ‖d.comb c (x : ℂ)‖
            ≤ (2 * (x - xiStar)) * (2 * ‖refComb c 2 (1 / 4) (x : ℂ)‖) :=
              mul_le_mul hTb hB1 (norm_nonneg _) (by positivity)
          _ = _ := by ring
      exact ⟨hxpos, hv0, twoZero_band_pt hc hxpos hxξ0 rfl hv0 hw hBn hRx hD.le hCR'⟩
    refine (band_integral_le (V := V) hc hξa hab (by norm_num : (1 : ℝ) < 5 / 2) hKc0 hfin).trans ?_
    have halg := band_final_algebra (p := 5 / 2) (lam := lambdaComb c)
      (κ := (1 + c1K0) ^ (-(2 / 3 : ℝ))) (W := FVc q c) (CR := CR') (CA := CA) (D := D)
      (N1 := (N₁ : ℝ)) (u0 := chiQuantile c ((N₁ + 1 : ℕ) : ℝ) - xiStar) (by norm_num) hlam hκ hN1pos
      hW0.le hCR'0.le hCA.le hD hgeo.1
    have hexp : (2 / 3 : ℝ) * (1 - 5 / 2) = -1 := by norm_num
    rw [hexp, Real.rpow_neg_one] at halg
    refine halg.trans (le_of_eq ?_)
    rw [hCT_def]
  · have hx1 : (c * (xiStar + r₀) ^ 2 / 3) < c * chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 / 3 := by
      have h1 : xiStar + r₀ < chiQuantile c ((N₁ + 1 : ℕ) : ℝ) := not_le.mp hab
      have h0' : 0 < xiStar + r₀ := by linarith
      have : (xiStar + r₀) ^ 2 < chiQuantile c ((N₁ + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      have := mul_lt_mul_of_pos_left this hc
      linarith
    rw [Set.Icc_eq_empty (not_le.mpr hx1), Measure.restrict_empty, integral_zero_measure]
    have : 0 < (2 * √2 / (π * lambdaComb c)) ^ (5 / 2 : ℝ) := by positivity
    positivity

/-- `|T_χ(x)| ≤ 1`. -/
lemma abs_tFac_le_one (χ x : ℝ) : |tFac χ x| ≤ 1 := by
  have h := norm_twoZeroT_le_one χ (b := (x : ℂ)) (by simp)
  rwa [tFac_eq, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The band bound of `ut:T2`** for every weight-one problem: `V = prob.cardyV (c/12)`, `F_{2,c} = twoZeroF`. -/
theorem twoZero_band_bound (prob : FixedWeightProblem) (hw : prob.w = 1) {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ}
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

/-- **The far band of `ut:T2`** for an abstract Cardy weight with `CardyFarBound V (ξ_* + r₀)`: `|T_{χ(p)}| ≤ 1` and
Lemma `T` (far band) at `f = 2`. -/
theorem twoZero_far_bound_of_cardy {V : ℝ → ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hF : CardyFarBound V (xiStar + r₀)) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C_far : ℝ, 0 ≤ C_far ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Ici (c * (xiStar + r₀) ^ 2 / 3), |combProfile c (d.twoZeroComb c) t| * V c t) ≤
        C_far * √c := by
  obtain ⟨CF, cF, hCF, hFb⟩ := hF
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
  have hx0 : 0 < xiStar + r₀ := by linarith
  refine ⟨4 * (2 * Cr) * CF * farConst, ?_, ?_⟩
  · have := farConst_nonneg
    positivity
  have hlam_ev : ∀ᶠ c in atTop, lambdaComb c ≤ r₀ / (4 * s) ∧ Kd * lambdaComb c ≤ r₀ * Real.log 2 := by
    have e1 := tendsto_lambdaComb_atTop.eventually
      (eventually_le_nhds (show (0 : ℝ) < r₀ / (4 * s) by positivity))
    have h2 := tendsto_lambdaComb_atTop.const_mul Kd
    rw [mul_zero] at h2
    exact e1.and (h2.eventually (eventually_le_nhds (show (0 : ℝ) < r₀ * Real.log 2 by positivity)))
  filter_upwards [hDev, eventually_ge_atTop cF, eventually_gt_atTop (0 : ℝ), hlam_ev, hrfar]
    with c hDev' hcF hc hlam hrfar' d hd
  have hlampos := lambdaComb_pos' hc
  have hFb' := comb_family_bounds hlampos (hb d hd)
  have hfin : ∀ x ∈ Ici (xiStar + r₀), 0 < x ∧ 0 ≤ V c (c * x ^ 2 / 3) ∧
      (2 * c * x / 3) * (|combProfile c (d.twoZeroComb c) (c * x ^ 2 / 3)| * V c (c * x ^ 2 / 3)) ≤
        4 * (2 * Cr) * CF * √c * (x ^ (1 / 2 : ℝ) * Real.exp (-π * x)) := by
    intro x hx
    have hx' : xiStar + r₀ ≤ x := hx
    have hxpos : 0 < x := by linarith
    have hxξ : r₀ ≤ x - xiStar := by linarith
    have hxξ0 : 0 < x - xiStar := by linarith
    obtain ⟨hv0, hw⟩ := hFb c hcF x hx'
    refine ⟨hxpos, hv0, ?_⟩
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
    have hB : ‖d.twoZeroComb c (x : ℂ)‖ * Real.exp (c * Bessel.besselL x) ≤ 2 * Cr := by
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
    exact integrand_far_le (B := d.twoZeroComb c) hc hxpos hv0 hB hw
  have := far_integral_le (B := d.twoZeroComb c) (V := V) hc hx0
    (by positivity : (0 : ℝ) ≤ 4 * (2 * Cr) * CF * √c) hfin
  refine this.trans (le_of_eq ?_)
  ring

/-- **The far band of `ut:T2`** for every weight-one problem. -/
theorem twoZero_far_bound (prob : FixedWeightProblem) (hw : prob.w = 1) {r₀ : ℝ} (hr₀ : 0 < r₀) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C_far : ℝ, 0 ≤ C_far ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦,
      (∫ t in Ici (c * (xiStar + r₀) ^ 2 / 3), |combProfile c (d.twoZeroComb c) t| *
          prob.cardyV (c / 12) t) ≤ C_far * √c :=
  twoZero_far_bound_of_cardy hr₀ (cardyFarBound_prob prob hw (by linarith [xiStar_pos])) hK hA

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_band_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_band_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_far_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_far_bound

end FormalResearch.ModularBootstrap.TwoLevel
