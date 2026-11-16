module

public import FormalResearch.Special.AiryCft2Ball
public import FormalResearch.Special.AiryCft2ComboQuadrature

/-!
# Theorem D for `N = P·Ai + Q·Ai'` and `f` holomorphic only near the closed disc

`airyNC_defect_bound` (`AiryCft2ComboQuadrature`) for `f` holomorphic on an open disc `|w| < R'` containing the closed disc
`|w| ≤ R` (instead of entire): `‖Σ_{N(t)=0,|t|≤R} f(t) D(t)/N'(t)² - ∫_{-R}^{R} f‖ ≤ π R B` if `‖f (M/N ∓ i)‖ ≤ B` on the
upper/lower half circle.  Combination of `cft2_defect_ball` and the zero theory of `AiryCft2ComboZeros`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- **Theorem D for `N = P Ai + Q Ai'`, `f` holomorphic on `|w| < R'`, `R < R'`.** -/
theorem airyNC_defect_ball (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} {R R' : ℝ} (hr : 0 < R) (hRR : R < R')
    (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hN : ∀ u : ℂ, ‖u‖ = R → airyNC P Q u ≠ 0) {B : ℝ}
    (hp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖f w * (airyMC P Q w / airyNC P Q w - I)‖ ≤ B)
    (hm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖f w * (airyMC P Q w / airyNC P Q w + I)‖ ≤ B)
    (S : Finset ℂ) (hS : ∀ z : ℂ, z ∈ S ↔ airyNC P Q z = 0 ∧ ‖z‖ ≤ R) :
    ‖(∑ t ∈ S, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * B := by
  have hin : ∀ t ∈ S, ‖t‖ < R := by
    intro t ht
    obtain ⟨h0, h1⟩ := (hS t).mp ht
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd h0 (hN t h)
  have hder : ∀ t ∈ S, deriv (airyNC P Q) t ≠ 0 := by
    intro t ht
    obtain ⟨h0, -⟩ := (hS t).mp ht
    have him := airyNC_zero_im P Q hQ h0
    have e : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [e] at h0
    rw [deriv_airyNC, e]
    exact (airyNC_zero_weight_pos P Q hQ h0).2
  obtain ⟨c, s, hD, hsum⟩ := cft2_circleData_of_finset (differentiable_airyNC P Q) hr S hin
    (fun t ht => ((hS t).mp ht).1) hder (fun w hw h0 => (hS w).mpr ⟨h0, hw⟩)
  have h := cft2_defect_ball hD (differentiable_airyMC P Q) hRR hf hp hm
  rw [hsum (fun t => f t * airyMC P Q t / deriv (airyNC P Q) t)] at h
  have hsum' : (-(π : ℂ)) * (∑ t ∈ S, f t * airyMC P Q t / deriv (airyNC P Q) t) =
      ∑ t ∈ S, f t * (airyDC P Q t / airyNC' P Q t ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨h0, -⟩ := (hS t).mp ht
    have hd := hder t ht
    rw [deriv_airyNC] at hd ⊢
    have hw := airyNC_weight_eq P Q h0 hd
    rw [← hw]
    ring
  rw [hsum'] at h
  exact h

/-- info: 'FormalResearch.Special.airyNC_defect_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_defect_ball

end FormalResearch.Special
