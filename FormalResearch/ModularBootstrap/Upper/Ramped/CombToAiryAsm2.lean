module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryAsm1

/-!
# Limits of the exact splitting: Steps 1-4 of Proposition 1.2(2) (`rem:P1.2`)

For a design, `x ∈ [ξ_*/2, ξ_* + 1/2]` not a site and `c'` large, `E_K(x) → log‖B_D(x)‖ - c'U(x)`
(`combEK_tendsto`, Lemma K2), `Sm_K → S` and `∑ Ξ_k → T` with `|S + (3/2)𝒦_*| ≤ Cλ`, `|T| ≤ Cλ`.  Hence
`P_K → L := log‖B_D(x)‖ - c'U + (3/2) log λ - S - T`, and the window approximants satisfy
`|M_K(σ)| = exp(P_K - 2πσ_-^{3/2}) → exp(L - 2πσ_-^{3/2})`, so the window limit `W̃(σ)` of Lemma W is non-zero
at every non-site `x` and `log|W̃(σ)| = L - 2πσ_-^{3/2}` (`abs_tildeW_eq`).
-/

@[expose] public section

open Filter Topology Set Finset MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Window

lemma kTip_mul_lam_rpow {c' : ℝ} (hc' : 0 < c') : kTip * c' * lambdaComb c' ^ (3 / 2 : ℝ) = 1 := by
  have hk := kTip_pos
  have hkc : 0 < kTip * c' := by positivity
  have : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
    unfold lambdaComb
    rw [← Real.rpow_mul hkc.le]
    norm_num [Real.rpow_neg_one]
  rw [this]; field_simp

/-- Lemma K2 at the real point: `c'(U + L)(x) = -2π σ_-^{3/2}`, `σ = τ(x)/λ`. -/
theorem riesz_UL {c' : ℝ} (hc' : 0 < c') {x : ℝ} (hx : x ∈ langerX (1 / 2)) :
    c' * (majorantReal x + slitL x) = -(2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ)) := by
  have hlp := lamPos hc'
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  by_cases hxs : xiStar ≤ x
  · have h1 := ((riesz_real_identities hc' hxpos.le 1 le_rfl).2.2.2.2 hxs).1
    have h2 : 0 ≤ sigmaOf c' x := div_nonneg (langerTau_nonneg hxs) hlp.le
    have h3 : max (-sigmaOf c' x) 0 = 0 := max_eq_right (by linarith)
    rw [h3, Real.zero_rpow (by norm_num), h1]; ring
  · have hxs' : x < xiStar := not_le.1 hxs
    have h1 := langerTau_spec.2.2.2.2.2 x hxpos hxs'.le
    have hτ : langerTau x < 0 := by
      have := langerTau_strictMonoOn (Set.mem_Ioi.2 hxpos) (Set.mem_Ioi.2 xiStar_pos) hxs'
      rwa [langerTau_xiStar] at this
    have hσ : sigmaOf c' x < 0 := div_neg_of_neg_of_pos hτ hlp
    have h3 : max (-sigmaOf c' x) 0 = -sigmaOf c' x := max_eq_left (by linarith)
    have h4 : |langerTau x| = lambdaComb c' * (-sigmaOf c' x) := by
      rw [abs_of_neg hτ, langerTau_eq_lam_sigmaOf hc' x]; ring
    rw [h3]
    have h5 : |langerTau x| ^ (3 / 2 : ℝ) = lambdaComb c' ^ (3 / 2 : ℝ) * (-sigmaOf c' x) ^ (3 / 2 : ℝ) := by
      rw [h4, Real.mul_rpow hlp.le (by linarith)]
    have h6 : majorantReal x + slitL x = -(2 * π * kTip * |langerTau x| ^ (3 / 2 : ℝ)) := by linarith
    rw [h6, h5]
    have := kTip_mul_lam_rpow hc'
    calc c' * -(2 * π * kTip * (lambdaComb c' ^ (3 / 2 : ℝ) * (-sigmaOf c' x) ^ (3 / 2 : ℝ)))
        = -(2 * π * ((kTip * c' * lambdaComb c' ^ (3 / 2 : ℝ)) * (-sigmaOf c' x) ^ (3 / 2 : ℝ))) := by ring
      _ = _ := by rw [this, one_mul]

/-- `E_K → log‖B_D(x)‖ - c' U(x)` (`K2`, `K1`). -/
theorem combEK_tendsto {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) {x : ℝ} (hx : x ∈ langerX (1 / 2))
    (hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k)
    (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) :
    Tendsto (fun n : ℕ => combEK c' σ η x (n + 1)) atTop
      (𝓝 (Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x)) := by
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have hy0 : ∀ k : ℕ, 1 ≤ k → 0 ≤ siteX c' σ k := fun k hk =>
    xiStar_pos.le.trans (xiStar_le_siteX hc' (h.nonneg k hk))
  obtain ⟨hlog, _, _⟩ := combBD_real hc' h hw x
  have hT : ‖blaschkeT (siteX c' σ 1 : ℂ) (x : ℂ)‖ ≠ 0 :=
    (Design.norm_blaschkeT_ofReal_pos hxpos.le (hy0 1 le_rfl) (hxk 1 le_rfl)).ne'
  have hq : ∀ m : ℕ, 0 < qPair c' σ η (m + 2) x := fun m => by
    have hε0 : 0 ≤ widthE c' η (m + 2) :=
      widthE_nonneg hc' (by omega) (h.height (m + 2) (by omega)).1
    have hε := (abs_le.1 (hw (m + 2) (by omega))).2
    exact Design.blaschkePairQ_pos (hy0 (m + 2) (by omega)) hxpos.le (hxk (m + 2) (by omega)) hε0
      (by linarith)
  have hlogB := log_norm_combBD hc' h hw x hT hq
  have h1 := hlog.hasSum.tendsto_sum_nat
  obtain ⟨_, hint, h2eq, _⟩ := riesz_real_identities hc' hxpos.le 1 le_rfl
  have hb : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1 / 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have h2 := intervalIntegral_tendsto_integral_Ioi (1 / 4 : ℝ) hint hb
  have h3 := (h1.const_add (realLogT x (siteX c' σ 1))).sub (h2.const_mul 2)
  have heq : ∀ n : ℕ, combEK c' σ η x (n + 1) =
      realLogT x (siteX c' σ 1) + ∑ i ∈ Finset.range n, Real.log (qPair c' σ η (i + 2) x) -
        2 * ∫ a in (1 / 4 : ℝ)..(((n + 1 : ℕ) : ℝ) + 1 / 2), realLogT x (chiQuantile c' a) := by
    intro n
    unfold combEK
    rw [← sum_range_add_two (fun k => Real.log (qPair c' σ η k x)) n]
  have hlim : Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x =
      realLogT x (siteX c' σ 1) + ∑' m : ℕ, Real.log (qPair c' σ η (m + 2) x) -
        2 * ∫ a in Ioi (1 / 4 : ℝ), realLogT x (chiQuantile c' a) := by
    rw [hlogB, ← h2eq]
  rw [hlim]
  exact h3.congr (fun n => (heq n).symm)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combEK_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combEK_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.riesz_UL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riesz_UL

end FormalResearch.ModularBootstrap.Upper.Ramped
