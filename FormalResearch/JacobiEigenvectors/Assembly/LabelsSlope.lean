module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber

/-!
# Paper J: the quantitative slope of the bulk phase at `t = h` (thm:A (i), step 5 of the chain for `BulkWindowLabels`)

Source: Paper J `thmA.tex`, proof of `thm:A (i)`, "Bulk phases": `partial_X Sigma_0 <= -c` on the block (`bulk_slope`, at `t = 0`), and `Sigma` is `C^{2M+1}` in `(X, t)` with bounded norms (`Sigma_bdd`).

## Proved here (axiom-pinned)

* `block_slope_quant`: `Sigma_0(x, t) - Sigma_0(y, t) >= c (y - x) - C1 t` for `x <= y` in the block, `0 <= t <= t0`, uniformly in `mu in K`.  The slope at `t = 0` (hypothesis, `bulk_slope`) is integrated
  (mean value theorem on `[x, y]`); the `t`-dependence is the Lipschitz bound `|Sigma_0(x, t) - Sigma_0(x, 0)| <= Cb t` from `Sigma_bdd` (`i = 1`, `j = 0`) by the mean value theorem on the convex set `block x [-t0, t0]`.

## Differences from the paper

The paper takes `h` small so that the slope at `t = h` is `<= -c/2` (mean value in `t`); here the equivalent loss `C1 t` is kept explicit (it is `C1 h` at `t = h`).

## Not formalised

Nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

theorem block_slope_quant {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ}
    {Jlo Jhi : ℝ} {M : ℕ} {U V : ℝ → ℝ → ℝ} {CL : BulkWeberChart F P Jlo Jhi (max M 1) U V}
    {CR : BulkWeberChart (mirrorFamily F) P Jlo Jhi (max M 1) U V}
    (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) (ht0 : 0 < t0) (hlt : Jlo < Jhi)
    (hslope : ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ K, ∀ X ∈ Ioo Jlo Jhi, deriv (fun X' => PI.Sigma μ 0 X' 0) X ≤ -c) :
    ∃ c C1 : ℝ, 0 < c ∧ 0 ≤ C1 ∧ ∀ μ ∈ K, ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ Icc Jlo Jhi, ∀ y ∈ Icc Jlo Jhi, x ≤ y →
      c * (y - x) - C1 * t ≤ PI.Sigma μ 0 x t - PI.Sigma μ 0 y t := by
  obtain ⟨c, hc, hder⟩ := hslope
  obtain ⟨Cb, hCb⟩ := PI.Sigma_bdd
  refine ⟨c, 2 * |Cb|, hc, by positivity, fun μ hμ t ht x hx y hy hxy => ?_⟩
  have hreg := PI.Sigma_reg μ hμ 0 (Nat.zero_le _)
  -- the slope at `t = 0`
  have hg : ∀ x ∈ Icc Jlo Jhi, ∀ y ∈ Icc Jlo Jhi, x ≤ y → PI.Sigma μ 0 y 0 - PI.Sigma μ 0 x 0 ≤ -c * (y - x) := by
    intro x hx y hy hxy
    have hcont : ContinuousOn (fun X => PI.Sigma μ 0 X 0) (Icc Jlo Jhi) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2) (Icc Jlo Jhi ×ˢ Icc (-t0) t0) := hreg.continuousOn
      exact h1.comp (continuous_id.prodMk (continuous_const (y := (0 : ℝ)))).continuousOn
        (fun X hX => ⟨hX, ⟨by linarith [ht0], ht0.le⟩⟩)
    have hdiff : DifferentiableOn ℝ (fun X => PI.Sigma μ 0 X 0) (interior (Icc Jlo Jhi)) := by
      intro X hX
      rw [interior_Icc] at hX
      refine (differentiableAt_of_deriv_ne_zero ?_).differentiableWithinAt
      have := hder μ hμ X hX
      intro h0; rw [h0] at this; linarith
    have := (convex_Icc Jlo Jhi).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (fun X hX => by rw [interior_Icc] at hX; exact hder μ hμ X hX) x hx y hy hxy
    exact this
  -- the Lipschitz bound in `t`
  have hlip : ∀ z ∈ Icc Jlo Jhi, |PI.Sigma μ 0 z t - PI.Sigma μ 0 z 0| ≤ |Cb| * t := by
    intro z hz
    set s : Set (ℝ × ℝ) := Icc Jlo Jhi ×ˢ Icc (-t0) t0 with hs
    have hUD : UniqueDiffOn ℝ s := UniqueDiffOn.prod (uniqueDiffOn_Icc hlt) (uniqueDiffOn_Icc (by linarith))
    have hdiff : DifferentiableOn ℝ (fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2) s :=
      hreg.differentiableOn (Nat.cast_ne_zero.mpr (by omega))
    have hbound : ∀ p ∈ s, ‖fderivWithin ℝ (fun p : ℝ × ℝ => PI.Sigma μ 0 p.1 p.2) s p‖ ≤ Cb := by
      intro p hp
      have := hCb μ hμ 0 (Nat.zero_le _) 1 (by omega) p hp
      rwa [norm_iteratedFDerivWithin_one _ (hUD p hp)] at this
    have hxs : (z, (0 : ℝ)) ∈ s := ⟨hz, ⟨by linarith, ht0.le⟩⟩
    have hxt : (z, t) ∈ s := ⟨hz, ⟨by linarith [ht.1], ht.2⟩⟩
    have := (convex_Icc Jlo Jhi |>.prod (convex_Icc (-t0) t0)).norm_image_sub_le_of_norm_fderivWithin_le hdiff
      (fun p hp => (hbound p hp).trans (le_abs_self Cb)) hxs hxt
    have e : ‖((z, t) : ℝ × ℝ) - (z, 0)‖ = t := by simp [Prod.norm_def, abs_of_nonneg ht.1, ht.1]
    rw [e, Real.norm_eq_abs] at this
    exact this
  have h0 := hg x hx y hy hxy
  have h1 := (abs_le.mp (hlip x hx)).1
  have h2 := (abs_le.mp (hlip y hy)).2
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.block_slope_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.block_slope_quant

end FormalResearch.JacobiEigenvectors.TheoremA

end
