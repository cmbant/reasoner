module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A uniform Taylor bound for smooth functions on both sides of the origin (F2a helper for `uct:bump-weighted`)

`taylor_poly_bound`: for `g : ℝ → ℂ` of class `C^∞` and `R > 0` there is `C ≥ 0` with
`‖g z - ∑_{l ≤ m} (g^{(l)}(0)/l!) z^l‖ ≤ C |z|^{m+1}` for `|z| ≤ R` (Mathlib's one-sided Taylor bound, reflected for `z < 0`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty

private lemma taylor_pos_side {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ) {R : ℝ} (hR : 0 < R) {C0 : ℝ}
    (hC0 : ∀ y ∈ Icc (0 : ℝ) R, ‖iteratedDeriv (m + 1) g y‖ ≤ C0) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) R) :
    ‖g z - ∑ l ∈ Finset.range (m + 1), ((iteratedDeriv l g 0 / (l.factorial : ℂ)) * (z : ℂ) ^ l)‖ ≤
      C0 / (m.factorial : ℝ) * |z| ^ (m + 1) := by
  have hcd : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) g (Icc 0 R) :=
    (hg.contDiffOn (s := Icc 0 R)).of_le (by exact_mod_cast le_top)
  have hU : UniqueDiffOn ℝ (Icc (0 : ℝ) R) := uniqueDiffOn_Icc hR
  have hC : ∀ y ∈ Icc (0 : ℝ) R, ‖iteratedDerivWithin (m + 1) g (Icc 0 R) y‖ ≤ C0 := by
    intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv hU (hg.contDiffAt.of_le (by exact_mod_cast le_top)) hy]
    exact hC0 y hy
  have := taylor_mean_remainder_bound hcd hz hC
  rw [taylor_within_apply] at this
  have hsum : ∑ k ∈ Finset.range (m + 1), (((k.factorial : ℝ))⁻¹ * (z - 0) ^ k) • iteratedDerivWithin k g (Icc 0 R) 0 =
      ∑ l ∈ Finset.range (m + 1), ((iteratedDeriv l g 0 / (l.factorial : ℂ)) * (z : ℂ) ^ l) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv hU (hg.contDiffAt.of_le (by exact_mod_cast le_top)) ⟨le_rfl, hR.le⟩, Complex.real_smul]
    push_cast
    ring
  rw [hsum] at this
  refine this.trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg hz.1]
  ring

theorem taylor_poly_bound {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |z| ≤ R →
      ‖g z - ∑ l ∈ Finset.range (m + 1), ((iteratedDeriv l g 0 / (l.factorial : ℂ)) * (z : ℂ) ^ l)‖ ≤ C * |z| ^ (m + 1) := by
  have hdc : ∀ k : ℕ, Continuous (iteratedDeriv k g) := fun k => by
    rw [iteratedDeriv_eq_iterate]; exact (hg.iterate_deriv k).continuous
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn (hdc (m + 1)).continuousOn
  set C0 : ℝ := max C1 0 with hC0
  have hC0n : 0 ≤ C0 := le_max_right _ _
  refine ⟨C0 / (m.factorial : ℝ), by positivity, fun z hz => ?_⟩
  rcases le_total 0 z with hz0 | hz0
  · exact taylor_pos_side hg m hR (C0 := C0)
      (fun y hy => (hC1 y ⟨by linarith [hy.1], hy.2⟩).trans (le_max_left _ _)) ⟨hz0, (abs_of_nonneg hz0 ▸ hz)⟩
  · set g' : ℝ → ℂ := fun y => g (-y) with hg'
    have hgd : ContDiff ℝ (⊤ : ℕ∞) g' := hg.comp contDiff_neg
    have hd : ∀ l : ℕ, iteratedDeriv l g' 0 = (-1 : ℝ) ^ l • iteratedDeriv l g 0 := fun l => by
      rw [hg', iteratedDeriv_comp_neg]; simp
    have := taylor_pos_side hgd m hR (C0 := C0) (z := -z)
      (fun y hy => by
        rw [hg', iteratedDeriv_comp_neg]
        simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact (hC1 (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩).trans (le_max_left _ _))
      ⟨by linarith, by have := abs_of_nonpos hz0; linarith⟩
    have hsum : ∑ l ∈ Finset.range (m + 1), ((iteratedDeriv l g' 0 / (l.factorial : ℂ)) * ((-z : ℝ) : ℂ) ^ l) =
        ∑ l ∈ Finset.range (m + 1), ((iteratedDeriv l g 0 / (l.factorial : ℂ)) * (z : ℂ) ^ l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hd l, Complex.real_smul]
      push_cast
      have : ((-1 : ℂ) ^ l) * ((-1 : ℂ) ^ l) = 1 := by rw [← mul_pow]; simp
      calc ((-1 : ℂ) ^ l * iteratedDeriv l g 0) / (l.factorial : ℂ) * (-(z : ℂ)) ^ l
          = ((-1 : ℂ) ^ l * (-1 : ℂ) ^ l) * (iteratedDeriv l g 0 / (l.factorial : ℂ) * (z : ℂ) ^ l) := by
            rw [neg_pow]; ring
        _ = _ := by rw [this, one_mul]
    rw [hsum] at this
    simpa [hg', abs_neg] using this

end FormalResearch.SignUncertainty
