module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumPrelim

/-!
# The comb part of the window limit on `[-S, Φ_{N₁+1}]` (`upper_transfer.tex`, `ut:T2`, `eq:ut:T2-local`)

`twoZero_window_comb`: for a compact family `𝒦` of admissible designs, `S ≥ 0`, `N₁` and `ε > 0`, for `c` large, all `d ∈ 𝒦`
and `σ ∈ [-S, Φ_{N₁+1}]`, with `x = ξ_* + λσ`, `t = c x²/3`, `dt/dσ = (2 c x/3) λ`,
`|F_{2,c}^{-1} h₂(t) V(t) (dt/dσ) - C_* κ² W_2(-κσ)| ≤ ε`.
This is `twoZero_window_limit` without the transform term `ĥ₂` and on the longer interval `[-S, Φ_{N₁+1}]` needed for the
vacuum (the window is taken up to `σ = Φ_{N₁+1}`); the proof is that of `twoZero_window_limit` (Lemma `W` × the window form
of `T_{χ(p)}`, with `ut:ID`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window.Cardy
open TwoZeroDesign

/-- **The comb part of the window limit** on `[-S, Φ_{N₁+1}]`: see the module docstring. -/
theorem twoZero_window_comb (prob : FixedWeightProblem) (hw : prob.w = 1) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {S : ℝ} (hS : 0 ≤ S)
    (n1 : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ σ ∈ Icc (-S) (phiWKB (n1 + 1)),
      |(twoZeroF prob c)⁻¹ * (combProfile c (d.twoZeroComb c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) -
        CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ)| ≤ ε := by
  have hκ := kappaAiry_pos
  have hξ := xiStar_pos
  obtain ⟨S', hS'⟩ : ∃ S' : ℝ, S' = max S (phiWKB (n1 + 1)) := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ phiWKB (n1 + 1) := phiWKB_nonneg (by omega)
  have hS'0 : 0 ≤ S' := by rw [hS']; exact le_max_of_le_left hS
  have hSS' : S ≤ S' := by rw [hS']; exact le_max_left _ _
  have hΦS' : phiWKB (n1 + 1) ≤ S' := by rw [hS']; exact le_max_right _ _
  obtain ⟨S₁, hS₁0, hS₁⟩ := hK.exists_sigmaP_bound
  obtain ⟨CT, hCT0, hTev⟩ := twoZeroT_window_bound (S' + S₁) (by positivity)
  obtain ⟨B₀, hB₀, hBb⟩ := CompactCombFamily.tildeW_bound (toModifiedFamily hK hA) hS'0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε / 2 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ, ε₁ = e / (2 * (S' + S₁) + 1) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by rw [hε₁]; positivity
  obtain ⟨C₀, hC₀, hWm⟩ := lemma_W_measure prob (toModifiedFamily hK hA) hS n1 ε₁ hε₁0
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = CT * (2 * √2 / π) := ⟨_, rfl⟩
  have hM'0 : 0 ≤ M' := by rw [hM']; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (e / ((S' + S₁) * B₀ + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min one_pos (by positivity)
  filter_upwards [hTev, eventually_ge_atTop C₀, lambda_mul_le M' hδ0, eventually_gt_atTop (0 : ℝ),
    lambda_mul_le S (half_pos hξ)] with c hTc hc₀ hlM hc0 hlS d hd σ hσ
  have hlam := lambdaComb_pos' hc0
  have hσS' : |σ| ≤ S' := by
    rw [abs_le]
    exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hσI : σ ∈ Icc (-S) (phiWKB (n1 + 1)) := hσ
  have hσI' : σ ∈ Icc (-S') S' := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hx : xiStar / 2 ≤ xiStar + lambdaComb c * σ := by
    have := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    nlinarith
  have hx0 : 0 ≤ xiStar + lambdaComb c * σ := by linarith
  have hFKpos : 0 < windowMeasureNormK prob 2 c := by
    rw [windowMeasureNormK_eq_FKc prob hw 2 hc0]
    exact FKc_pos (qProb_pos prob) 2 hc0
  have hq₀pos : 0 < π * lambdaComb c / (2 * √2) := by positivity
  have hF : twoZeroF prob c = windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)) :=
    twoZeroF_eq_windowMeasureNormK prob hw hc0
  have hB := hWm hc₀ d.toModified (toModifiedFamily_mem hK hA hd) σ hσI
  simp only [] at hB
  have hWtb := hBb d.toModified (toModifiedFamily_mem hK hA hd) σ hσI'
  have hsb : |σ - d.sigmaP| ≤ S' + S₁ :=
    (abs_sub _ _).trans (add_le_add hσS' (hS₁ d hd))
  have hPb : |tFac (d.chiP c) (xiStar + lambdaComb c * σ) - π * lambdaComb c / (2 * √2) * (σ - d.sigmaP)| ≤
      (M' * lambdaComb c) * (π * lambdaComb c / (2 * √2)) * |σ - d.sigmaP| := by
    have h := hTc σ d.p (hσS'.trans (by linarith)) (by
      have := hS₁ d hd
      unfold sigmaP at this
      rw [neg_div, abs_neg] at this
      linarith)
    have e1 : ((xiStar + lambdaComb c * (-d.p / kappaAiry) : ℝ) : ℂ) = ((d.chiP c : ℝ) : ℂ) := rfl
    rw [e1, tFac_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    have e2 : (-d.p / kappaAiry) = d.sigmaP := rfl
    rw [e2] at h
    have : CT * lambdaComb c ^ 2 * |σ - d.sigmaP| =
        (M' * lambdaComb c) * (π * lambdaComb c / (2 * √2)) * |σ - d.sigmaP| := by
      rw [hM']
      have : √2 ≠ 0 := by positivity
      field_simp
    rw [← this]
    exact h
  have hl1 : M' * lambdaComb c ≤ δ := by rw [mul_comm]; exact hlM
  have ha0 : 0 ≤ M' * lambdaComb c := by positivity
  have ha1 : M' * lambdaComb c ≤ 1 := hl1.trans (by rw [hδ]; exact min_le_left _ _)
  have hID := tildeW_toModified_Wr d σ
  have hC : CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) =
      (σ - d.sigmaP) * tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim d.toModified.allEpsLim σ := by
    have : tildeW 2 d.toModified.sigmaFLim d.toModified.allSigmaLim d.toModified.allEpsLim σ *
        (σ - d.sigmaP) = CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) := hID
    linarith
  have hcomb := window_product_estimate hq₀pos hPb hsb ha0 ha1 hWtb hB
  have h1 : 2 * (S' + S₁) * ε₁ ≤ e := by
    rw [hε₁]; exact eps_split (by positivity) he0
  have h2 : (M' * lambdaComb c) * (S' + S₁) * B₀ ≤ e :=
    small_mul ha0 (by positivity) hB₀.le (hl1.trans (by rw [hδ]; exact min_le_right _ _))
  have hpsi : combProfile c (d.twoZeroComb c) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) =
      tFac (d.chiP c) (xiStar + lambdaComb c * σ) *
        modifiedH0 2 (n + 2) d.toModified c (xiStar + lambdaComb c * σ) :=
    twoZero_combProfile_eq d hc0 hx0
  rw [hpsi, hC, hF]
  have hrw : (windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)))⁻¹ *
      (tFac (d.chiP c) (xiStar + lambdaComb c * σ) *
          modifiedH0 2 (n + 2) d.toModified c (xiStar + lambdaComb c * σ) *
        prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
        ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) =
      tFac (d.chiP c) (xiStar + lambdaComb c * σ) / (π * lambdaComb c / (2 * √2)) *
        ((modifiedH0 2 (n + 2) d.toModified c (xiStar + lambdaComb c * σ) *
          prob.cardyV (c / 12) (c * (xiStar + lambdaComb c * σ) ^ 2 / 3) *
          ((2 * c * (xiStar + lambdaComb c * σ) / 3) * lambdaComb c)) / windowMeasureNormK prob 2 c) := by
    field_simp
  rw [hrw]
  have h3 : 2 * (S' + S₁) * ε₁ + (M' * lambdaComb c) * (S' + S₁) * B₀ ≤ ε := by
    rw [he] at h1 h2; linarith
  exact hcomb.trans h3

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_window_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_window_comb

end FormalResearch.ModularBootstrap.TwoLevel
