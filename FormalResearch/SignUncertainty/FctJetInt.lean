/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctJet
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Jet bounds of a parametric integral over `[0,1]` (F2a, `fct:comp-cfu`)

If `f(y,σ)` is `C^k` on `O × [0,1]` with all derivatives of order `≤ k` bounded by `b`, then `y ↦ ∫₀¹ f(y,σ) dσ` is `C^k`
on `O` with the same bound (Mathlib's Taylor series of a parametric integral).  Used for the Hadamard divided difference
`H_λ(z) = ∫₀¹ (1-σ) r''(B + σ(z-B)) dσ` of the scalar cubic chart.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section Int
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Parametric integral over `σ ∈ [0,1]`: smoothness and jet bounds pass to `y ↦ ∫₀¹ f(y,σ) dσ`. -/
lemma JB.integral01 {k : ℕ} {O : Set P} (hO : IsOpen O) {f : P → ℝ → V} {b : ℝ}
    (hf : ContDiffOn ℝ k (fun p : P × ℝ => f p.1 p.2) (O ×ˢ Icc (0 : ℝ) 1))
    (hb : JB k (O ×ˢ Icc (0 : ℝ) 1) (fun p : P × ℝ => f p.1 p.2) b) :
    ContDiffOn ℝ k (fun y => ∫ σ in Icc (0 : ℝ) 1, f y σ) O ∧
      JB k O (fun y => ∫ σ in Icc (0 : ℝ) 1, f y σ) b := by
  refine ⟨ContDiffOn.parametric_integral hO isCompact_Icc (subset_refl _) hf (by simp), ?_⟩
  have hOd : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  have hUd : UniqueDiffOn ℝ (O ×ˢ Icc (0 : ℝ) 1) := hOd.prod (uniqueDiffOn_Icc zero_lt_one)
  have hT := hf.ftaylorSeriesWithin hUd
  have hTay := hasFTaylorSeriesUpToOn_setIntegral_of_le_const (μ := (volume : Measure ℝ)) (n := (k : ℕ∞ω))
    (C := fun _ => b) (t := Icc (0 : ℝ) 1) hO isCompact_Icc.isSeparable measurableSet_Icc (by simp) hT
    (fun x hx a ha i hi => hb i (by exact_mod_cast hi) (x, a) ⟨hx, ha⟩)
  intro i hi y hy
  rw [← hTay.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hi) hOd hy]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Icc (0 : ℝ) 1) (C := b)
    (f := fun a => (ftaylorSeriesWithin ℝ (fun p : P × ℝ => f p.1 p.2) (O ×ˢ Icc (0 : ℝ) 1) (y, a) i).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inl ℝ P ℝ)) (by simp) ?_
  · simpa using h1
  · intro a ha
    have h2 : ‖ftaylorSeriesWithin ℝ (fun p : P × ℝ => f p.1 p.2) (O ×ˢ Icc (0 : ℝ) 1) (y, a) i‖ ≤ b :=
      hb i hi (y, a) ⟨hy, ha⟩
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h3 : ∏ j : Fin i, ‖ContinuousLinearMap.inl ℝ P ℝ‖ ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ P ℝ)
    calc _ ≤ b * 1 := mul_le_mul h2 h3 (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans h2)
      _ = b := mul_one b

end Int

/-- info: 'FormalResearch.SignUncertainty.JB.integral01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms JB.integral01

end FormalResearch.SignUncertainty
