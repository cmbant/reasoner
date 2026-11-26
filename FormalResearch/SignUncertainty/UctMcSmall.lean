module

public import FormalResearch.SignUncertainty.UctMcSmallA
public import FormalResearch.SignUncertainty.UctMcSmallE
public import FormalResearch.SignUncertainty.UctMcSmallPhi

/-!
# `(uct:Mc-small)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, proof of `uct:seed-asymp`, `(uct:Mc-small)`.  **Proved.**

`mc_small`: there are `c₀`, `K` such that for all `c ≥ c₀`, `0 ≤ δ ≤ 1`, the amplitude `M_c = e^{B_c(iτ)} (φ_{c,δ}(1-iτ)/φ_{c,δ}(1)) A_*(τ)`
(`uctMc`) is `C³` and on `|τ| ≤ 1/5`

`|M_c - 1| ≤ K(c^{-2/3}|τ| + τ²)`, `|M_c'| ≤ K(c^{-2/3} + |τ|)`, `|M_c''|, |M_c'''| ≤ K`

(`SmallBd (uctMc c δ) (c^{-2/3}) K`).  The TeX range `|τ| ≤ 0.2` is `1/5`.  Proof: `SmallBd.mul` for the three factors `e^{B_c}`
(`smallBd_binet`, from `ct_dual_id_part1`), `φ(1-iτ)/φ(1)` (`smallBd_phiQuot`, from `uct_airy_trans_phi`) and `A_*`
(`smallBd_of_even_real`: even, `C^∞`, `A_*(0) = 1`).
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.SignUncertainty

lemma one_div_le_rpow {c : ℝ} (hc : 1 ≤ c) : 1 / c ≤ c ^ (-(2 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  rw [Real.rpow_neg hc0.le, one_div]
  refine inv_anti₀ (Real.rpow_pos_of_pos hc0 _) ?_
  calc c ^ (2 / 3 : ℝ) ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc (by norm_num)
    _ = c := Real.rpow_one c

theorem mc_small : ∃ c₀ K : ℝ, 0 ≤ K ∧ ∀ c δ : ℝ, c₀ ≤ c → 0 ≤ δ → δ ≤ 1 →
    SmallBd (fun τ : ℝ => uctMc c δ τ) (c ^ (-(2 / 3 : ℝ))) K := by
  obtain ⟨KE, hKE0, hE⟩ := smallBd_binet
  obtain ⟨c1, KQ, hKQ0, hQ⟩ := smallBd_phiQuot
  obtain ⟨KA, hKA0, hA⟩ := smallBd_of_even_real contDiff_uctAstar uctAstar_zero uctAstar_neg
  refine ⟨max c1 8, 20 * (20 * (KE + 1) * (KQ + 1) + 1) * (KA + 1), by positivity, fun c δ hc hδ0 hδ1 => ?_⟩
  have hc1 : c1 ≤ c := (le_max_left _ _).trans hc
  have hc8 : 8 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hp0 : 0 ≤ c ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
  have hp1 : c ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hEc := hE c (by linarith) _ (one_div_le_rpow (by linarith))
  have hQc := hQ c δ hc1 hδ0 hδ1
  have hAc := hA _ hp0
  have h1 := SmallBd.mul hp0 hp1 hEc hQc
  have h2 := SmallBd.mul hp0 hp1 h1 hAc
  have hfun : (fun τ : ℝ => uctMc c δ τ) = fun τ : ℝ => (Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
      (uctPhi c δ (1 - (τ : ℂ) * Complex.I) / uctPhi c δ 1)) * (uctAstar τ : ℂ) := by
    funext τ; unfold uctMc; ring
  rw [hfun]
  exact h2

/-- info: 'FormalResearch.SignUncertainty.mc_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mc_small

end FormalResearch.SignUncertainty
