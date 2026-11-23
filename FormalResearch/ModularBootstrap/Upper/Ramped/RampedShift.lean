module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleComparison

/-!
# The site-shift cost outside the hole (`rem:thmU` Step (3), "Shifts")

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), "Shifts":
`|∂_y f_x(y)| ≤ 1/|x-y| + C` (`cmb:K1`(c)), and for `k ∉ H` the segment from `χ_k` to `χ'_k` stays at distance
`≥ ½|x - χ_k|` from `x`, so `S ≤ Σ_{k∉H} 2(2/|x-χ_k| + π)|Δ_k| + (2/|x-χ_1| + π)|Δ_1|`.

* `holeShiftCost_le_dist`: this reduction, proved from `holeShiftCost_le`: if `|Δ_k| ≤ a_k`, `2a_k ≤ D_k ≤ |x - χ_k|`
  for the first site and the sites outside the hole, then
  `S ≤ (2/D_f + π) a_f + Σ_{k∉H} 2 (2/D_k + π) a_k`.
* `ShiftSumEstimate`: the remaining analytic input, a named hypothesis: the right-hand side is
  `≤ C_S (n^{-2/3} + n^{-1} log n) + C_S λ` (with `a_k = C_sh λ k^{-4/3}` and `D_k ≍ λ n^{2/3}` for `k < n/2`,
  `λ k^{-1/3}|k - n|` for `|k - n| ≤ n/2`: the summation of Lemma E).  `shiftSumEstimate_zero` is the
  non-vacuity statement (a comb without displacement satisfies it) and `holeShiftCost_le_estimate` turns it
  into the bound `S ≤ C_S(...)` consumed by `Upper.Ramped.RampedFloor`.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Design

/-- The shift cost is bounded by the weighted displacements, given distances `D_k ≥ 2 a_k ≥ 2|Δ_k|`. -/
theorem holeShiftCost_le_dist {c' x : ℝ} (hx : xiStar ≤ x) (σ : ℕ → ℝ) {f N : ℕ} (hfN : f ≤ N) (n : ℕ)
    (a D : ℕ → ℝ) (hD : ∀ k, f ≤ k → k ≤ N → 0 < D k)
    (hnn : ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k ∧ 0 ≤ chiQuantile c' k)
    (ha : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) →
      |designSite c' σ k - chiQuantile c' k| ≤ a k)
    (h2a : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) → 2 * a k ≤ D k)
    (hdist : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) → D k ≤ |x - chiQuantile c' k|) :
    holeShiftCost c' x σ f N n 4 ≤
      (2 / D f + π) * a f +
        ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∉ holeSet n 4),
          2 * ((2 / D k + π) * a k) := by
  have hseg : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) →
      ∀ y ∈ Set.uIcc (designSite c' σ k) (chiQuantile c' k), D k / 2 ≤ |x - y| := by
    intro k hk1 hk2 hk y hy
    have h1 : |x - chiQuantile c' k| - |y - chiQuantile c' k| ≤ |x - y| := by
      have := abs_sub_abs_le_abs_sub (x - chiQuantile c' k) (y - chiQuantile c' k)
      simpa [sub_sub_sub_cancel_right] using this
    have h2 : |y - chiQuantile c' k| ≤ |designSite c' σ k - chiQuantile c' k| := by
      rcases Set.mem_uIcc.mp hy with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [abs_le]
        constructor
        · linarith [neg_abs_le (designSite c' σ k - chiQuantile c' k)]
        · linarith [abs_nonneg (designSite c' σ k - chiQuantile c' k)]
      · rw [abs_le]
        constructor
        · linarith [abs_nonneg (designSite c' σ k - chiQuantile c' k)]
        · linarith [le_abs_self (designSite c' σ k - chiQuantile c' k)]
    have := ha k hk1 hk2 hk
    have := h2a k hk1 hk2 hk
    have := hdist k hk1 hk2 hk
    linarith
  have h := holeShiftCost_le (c' := c') hx σ hfN n 4 (fun k => D k / 2)
    (fun k hk1 hk2 => by have := hD k hk1 hk2; positivity) hnn hseg
  refine h.trans ?_
  have hpos : ∀ k, f ≤ k → k ≤ N → 0 < D k := hD
  have hbound : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) →
      (1 / (D k / 2) + π) * |designSite c' σ k - chiQuantile c' k| ≤ (2 / D k + π) * a k := by
    intro k hk1 hk2 hk
    have e : 1 / (D k / 2) = 2 / D k := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (ha k hk1 hk2 hk) (by have := hpos k hk1 hk2; positivity)
  refine add_le_add (hbound f le_rfl hfN (Or.inl rfl)) (Finset.sum_le_sum fun k hk => ?_)
  have hk' := Finset.mem_filter.mp hk
  have hk2 := Finset.mem_Icc.mp hk'.1
  exact mul_le_mul_of_nonneg_left (hbound k (by omega) hk2.2 (Or.inr hk'.2)) (by norm_num)

/-- **The remaining analytic input of the shift bound** (named hypothesis): the weighted displacement sum is at
most `C_S (n^{-2/3} + n^{-1} log n) + C_S λ`. -/
def ShiftSumEstimate (C_S lam : ℝ) (f N n : ℕ) (a D : ℕ → ℝ) : Prop :=
  (2 / D f + π) * a f +
      ∑ k ∈ (Finset.Icc (f + 1) N).filter (fun k => k ∉ holeSet n 4), 2 * ((2 / D k + π) * a k) ≤
    C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) + C_S * lam

/-- Non-vacuity: without displacements the estimate holds for every `C_S ≥ 0`, `λ ≥ 0`, `n ≥ 1`. -/
theorem shiftSumEstimate_zero {C_S lam : ℝ} (hC : 0 ≤ C_S) (hlam : 0 ≤ lam) (f N n : ℕ)
    (hn : 1 ≤ n) (D : ℕ → ℝ) : ShiftSumEstimate C_S lam f N n (fun _ => 0) D := by
  unfold ShiftSumEstimate
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnr
  have h1 : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have h2 : 0 ≤ Real.log n / n := div_nonneg hlog (by linarith)
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  positivity

/-- `holeShiftCost ≤ C_S (n^{-2/3} + n^{-1} log n) + C_S λ` from the distances and the named estimate. -/
theorem holeShiftCost_le_estimate {c' x C_S lam : ℝ} (hx : xiStar ≤ x) (σ : ℕ → ℝ) {f N : ℕ}
    (hfN : f ≤ N) (n : ℕ) (a D : ℕ → ℝ) (hD : ∀ k, f ≤ k → k ≤ N → 0 < D k)
    (hnn : ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k ∧ 0 ≤ chiQuantile c' k)
    (ha : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) →
      |designSite c' σ k - chiQuantile c' k| ≤ a k)
    (h2a : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) → 2 * a k ≤ D k)
    (hdist : ∀ k, f ≤ k → k ≤ N → (k = f ∨ k ∉ holeSet n 4) → D k ≤ |x - chiQuantile c' k|)
    (hS : ShiftSumEstimate C_S lam f N n a D) :
    holeShiftCost c' x σ f N n 4 ≤ C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) + C_S * lam :=
  (holeShiftCost_le_dist hx σ hfN n a D hD hnn ha h2a hdist).trans hS

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.holeShiftCost_le_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.holeShiftCost_le_dist

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.shiftSumEstimate_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.shiftSumEstimate_zero

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.holeShiftCost_le_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.holeShiftCost_le_estimate

end FormalResearch.ModularBootstrap.Upper.Ramped
