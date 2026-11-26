/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctNSymbol
public import FormalResearch.SignUncertainty.FctPhysicalBudgetConcrete

/-!
# `hN` of Lemma FCT.7b for the physical datum

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`) (a), fourth item: for
`a = c^{-1/12}`, `|L₁| ≤ K c^{-2/3} = K a⁸` (`physL1_le`), `δ_L ≍ c^{-1/2}` (`physDelta_bounds`):
`|1 - L₁ φ_kill(iτ₀(L̃); a)/L̃| - 1 ∈ SymW [3δ_L/2, ∞) (pw M (-1) 0)` uniformly in `c ≥ c₀`, `ε = ±1`.

`hN_physical` instantiates `N_symW_abstract` (all inequalities are proved: `|s| ≤ 3δ_L/4`, `3δ_L/2 ≤ 1/2`, and `|L₁| ≤ η δ_L` for large `c`
since `c^{-2/3} = o(c^{-1/2})`).  The only input is `hT1 : T₁ = Δ₅ + O(c⁻¹)` (the `warp_zero` clause of `fct:warp-asymp` (1)).

Class: proved under the explicit hypothesis `hT1` (the size input of `physL1_le`).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies

/-- **`hN` of Lemma FCT.7b for the physical datum.** -/
theorem hN_physical (T1 : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹) :
    ∃ (c₀ MN : ℝ) (KN : ℕ → ℝ), 0 ≤ MN ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MN (-1) 0) KN
        (fun x => ‖((x - physShift ε c : ℝ) : ℂ) - (physL1 T1 ε c : ℂ) * vacPhi (c ^ (-(1 / 12 : ℝ))) (x - physShift ε c)‖ /
          (x - physShift ε c) - 1) := by
  obtain ⟨η, hη, hN⟩ := N_symW_abstract
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨KL, cL, hcL1, hL⟩ := physL1_le T1 hT1
  set κ : ℝ := max KL 0 with hκ
  have hκ0 : 0 ≤ κ := le_max_right _ _
  obtain ⟨M, K, hM0, hMK⟩ := hN κ hκ0
  obtain ⟨cη, hcη1, hcη⟩ := exists_rpow_neg_le (p := 1 / 6) (η := η * a₀ / (κ + 1)) (by norm_num) (by positivity)
  refine ⟨max cs (max cL cη), M, K, hM0, fun ε c hε hc => ?_⟩
  have hcs' : cs ≤ c := (le_max_left _ _).trans hc
  have hcL' : cL ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcη' : cη ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  obtain ⟨hδ0, hδ1, hs, -, -, -, hδa₀, -, h6⟩ := hsc ε c hε hcs'
  have hc1 : 1 ≤ c := hcs.trans hcs'
  have hc0 : 0 < c := by linarith
  have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have ha1 : c ^ (-(1 / 12 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have ha8 : (c ^ (-(1 / 12 : ℝ))) ^ 8 = c ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hL1 : |physL1 T1 ε c| ≤ κ * (c ^ (-(1 / 12 : ℝ))) ^ 8 := by
    rw [ha8]
    exact (hL ε c hε (hcL'.trans' le_rfl)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hc0.le _))
  have hL2 : |physL1 T1 ε c| ≤ η * physDelta c := by
    have h1 := hL ε c hε hcL'
    have h2 : c ^ (-(1 / 6 : ℝ)) ≤ η * a₀ / (κ + 1) := hcη c hcη'
    have e : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hp : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hp6 : 0 ≤ c ^ (-(1 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
    calc |physL1 T1 ε c| ≤ KL * c ^ (-(2 / 3 : ℝ)) := h1
      _ ≤ κ * c ^ (-(2 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hc0.le _)
      _ = κ * c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by rw [e]; ring
      _ ≤ (η * a₀) * c ^ (-(1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hp
          have : κ * c ^ (-(1 / 6 : ℝ)) ≤ (κ + 1) * (η * a₀ / (κ + 1)) :=
            mul_le_mul (by linarith) h2 hp6 (by linarith)
          rwa [mul_div_cancel₀ _ (by positivity)] at this
      _ = η * (a₀ * c ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ η * physDelta c := mul_le_mul_of_nonneg_left hδa₀ hη.le
  refine hMK _ _ _ _ ha ha1 hδ0 (by linarith) ?_ hL1 hL2
  · have : |physShift ε c| ≤ 3 / 2 * physDelta c / 2 := hs
    linarith

/-- info: 'FormalResearch.SignUncertainty.FctSym.hN_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hN_physical

end FormalResearch.SignUncertainty.FctSym
