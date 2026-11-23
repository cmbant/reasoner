module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryAsm3

/-!
# Proposition 1.2(2) (`rem:P1.2`): the uniform comb-to-Airy identity

For every design (sites `σ_k`, `|σ_k - Φ_k| ≤ C_sh k^{-4/3}`, separation `σ_{k+1} - σ_k ≥ c_sep k^{-1/3}`, heights
`η_k ∈ [0, 1/4]`; constants uniform in `N`, `d` and the profile), every `c' ≥ c₀` and every
`x ∈ [ξ_*/2, ξ_* + 1/2]` that is not a site `χ'_k`,
`log‖B_D(x)‖ + c' L(x) = -(3/2) log λ - (3/2) 𝒦_*(x) + log(C_* κ ‖W_D(-κ τ(x)/λ)‖) + O(λ)`,
`λ = (k_tip c')^{-2/3}`; the Airy product `W_D` does not vanish there.  The proof follows `remainder.tex`: the
exact splitting `E_K = -(3/2) log λ + P_K + Sm_K + ∑ Ξ_k` (`combEK_eq`), the smooth part `Sm_K`
(`sm_design`, midpoint rule), the pair sum `∑ |Ξ_k| ≤ C λ` (`xi_sum`), Lemma W (`window_tendsto`) and Lemma ID
(`tildeW_design`).
-/

@[expose] public section

open Filter Topology Set Finset MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Window

/-- **Proposition 1.2(2), logarithmic form, off the sites.** -/
theorem combToAiry_nonsite (Csh csep : ℝ) (hcsep : 0 < csep) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2), (∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k) →
      0 < ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ ∧
      |Real.log ‖combBD c' σ η (x : ℂ)‖ + c' * slitL x -
        (-(3 / 2) * Real.log (lambdaComb c') - 3 / 2 * langerK x xiStar +
          Real.log (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖))| ≤
        C * lambdaComb c' := by
  obtain ⟨Csm, c0sm, hCsm, hc0sm, hsm⟩ := sm_design Csh
  obtain ⟨Cxi, c0xi, hCxi, hc0xi, hxi⟩ := xi_sum Csh csep hcsep
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_le_unif
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgev
  refine ⟨Csm + Cxi, max (max c0sm c0xi) (max N 1), by positivity,
    lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _)), ?_⟩
  intro c' hc' σ η h x hx hxk
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hcN : N ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  have hc1 : c0sm ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc2 : c0xi ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hlp := lamPos hc'0
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    obtain ⟨hη0, hη1⟩ := h.height k hk
    have hℓ1 := (hN c' hcN k hk1).2
    have hℓ0 : 0 ≤ siteGap c' k := Design.siteGap_nonneg hc'0 hk1
    have h0 : 0 ≤ widthE c' η k := widthE_nonneg hc'0 hk hη0
    rw [abs_of_nonneg h0]
    have := mul_le_mul_of_nonneg_right hη1 hℓ0
    unfold widthE
    linarith
  obtain ⟨_, S, hS, hSb⟩ := hsm hc1 h x hx
  have hsmT : Tendsto (fun n : ℕ => smPartial c' σ x (n + 1)) atTop (𝓝 S) :=
    hS.comp (tendsto_add_atTop_nat 1)
  -- the pair sum converges
  have hbound : ∀ n : ℕ, ∑ m ∈ Finset.range n, |xiPair c' σ η x (m + 2)| ≤ Cxi * lambdaComb c' := by
    intro n
    rw [sum_range_add_two (fun k => |xiPair c' σ η x k|) n]
    exact hxi hc2 h x hx (fun k hk => hxk k (by omega)) (n + 1)
  have hsumabs : Summable fun m : ℕ => |xiPair c' σ η x (m + 2)| :=
    summable_of_sum_range_le (fun m => abs_nonneg _) hbound
  have hsum : Summable fun m : ℕ => xiPair c' σ η x (m + 2) := hsumabs.of_abs
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑' m : ℕ, xiPair c' σ η x (m + 2) := ⟨_, rfl⟩
  have hTb : |T| ≤ Cxi * lambdaComb c' := by
    have h1 : |T| ≤ ∑' m : ℕ, |xiPair c' σ η x (m + 2)| := by
      have := norm_tsum_le_tsum_norm (f := fun m : ℕ => xiPair c' σ η x (m + 2)) hsum.norm
      rw [← hT] at this
      simpa only [Real.norm_eq_abs] using this
    exact h1.trans (Real.tsum_le_of_sum_range_le (fun m => abs_nonneg _) hbound)
  have hΞ : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 2 (n + 1), xiPair c' σ η x k) atTop (𝓝 T) := by
    have := hsum.hasSum.tendsto_sum_nat
    rw [← hT] at this
    refine this.congr fun n => ?_
    rw [sum_range_add_two (fun k => xiPair c' σ η x k) n]
  have habs := abs_tildeW_eq hc'0 h hx hxk hw hsmT hΞ
  have hid := tildeW_design h (sigmaOf c' x)
  have hre : |(designAiryW σ η (-kappaAiry * sigmaOf c' x)).re| =
      ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ :=
    Complex.abs_re_eq_norm.2 (designAiryW_im h _)
  have hκ := kappaAiry_pos
  have hCs := CStar_pos
  have hval : CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ =
      Real.exp (Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x +
        3 / 2 * Real.log (lambdaComb c') - S - T -
          2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ)) := by
    rw [← habs, hid, abs_mul, abs_of_pos (mul_pos hCs hκ), hre]
  have hWpos : 0 < ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ := by
    have : 0 < CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ := by
      rw [hval]; exact Real.exp_pos _
    exact pos_of_mul_pos_right this (mul_pos hCs hκ).le
  refine ⟨hWpos, ?_⟩
  have hlogW : Real.log (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖) =
      Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x +
        3 / 2 * Real.log (lambdaComb c') - S - T -
          2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ) := by
    rw [hval, Real.log_exp]
  have hUL := riesz_UL hc'0 hx
  rw [hlogW]
  have e : Real.log ‖combBD c' σ η (x : ℂ)‖ + c' * slitL x -
      (-(3 / 2) * Real.log (lambdaComb c') - 3 / 2 * langerK x xiStar +
        (Real.log ‖combBD c' σ η (x : ℂ)‖ - c' * majorantReal x +
          3 / 2 * Real.log (lambdaComb c') - S - T -
            2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ))) =
      (S + 3 / 2 * langerK x xiStar) + T := by
    have : c' * majorantReal x = -(c' * slitL x) - 2 * π * (max (-sigmaOf c' x) 0) ^ (3 / 2 : ℝ) := by
      linarith [hUL]
    rw [this]; ring
  rw [e]
  calc |(S + 3 / 2 * langerK x xiStar) + T| ≤ |S + 3 / 2 * langerK x xiStar| + |T| := abs_add_le _ _
    _ ≤ Csm * lambdaComb c' + Cxi * lambdaComb c' := add_le_add hSb hTb
    _ = (Csm + Cxi) * lambdaComb c' := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combToAiry_nonsite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combToAiry_nonsite

end FormalResearch.ModularBootstrap.Upper.Ramped
