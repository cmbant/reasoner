module

public import Mathlib
public import FormalResearch.JB.JBDefs
public import FormalResearch.MatrixAnalysis.JacobiOpRatio

/-!
# Paper J, Theorem B reduction: normalisation ratios (`lem:thb-ratio`)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Lemma `lem:thb-ratio`, in coordinates.
The coordinate projection `P` is the finite set `S` of rows; the Euclidean norm of the restriction of a
vector `v : ι → ℝ` to `S` is `√(∑ n ∈ S, v n ^ 2)`.

* `jb_ratio` : if `√∑_S Ψ² ≥ c₀ > 0`, `‖f − g‖_S ≤ ε ‖g‖_S` with `ε < 1`, `‖s f − Ψ‖_S ≤ δ`,
  `‖t g − Ψ‖_S ≤ δ` with `δ < c₀`, then `t ≠ 0` and
  `|s/t − 1| ≤ (ε + 2δ/(c₀ − δ))/(1 − ε)`.

Difference from the paper: the paper assumes `s, t ≠ 0`; here these are redundant (they follow from
`δ < c₀ ≤ ‖Ψ‖_S`) and are derived, and so is `0 < c0` (from `0 ≤ δ < c0`), which the brief listed (`s ≠ 0` is `jb_ratio_ne_zero_left`, `t ≠ 0` is part of the
conclusion).  The estimate itself is the Jacobi-operator package's `jop_normalisation_ratio`
(normed-space form), transported to `EuclideanSpace ℝ S`.
Not formalised: nothing from the lemma.
-/

@[expose] public section

namespace FormalResearch.JB

open FormalResearch.MatrixAnalysis

variable {ι : Type*}

/-- The vector of `ι → ℝ` restricted to `S`, in `EuclideanSpace`. -/
noncomputable def restrictVec (S : Finset ι) (v : ι → ℝ) : EuclideanSpace ℝ {n // n ∈ S} :=
  WithLp.toLp 2 fun i => v i

theorem norm_restrictVec (S : Finset ι) (v : ι → ℝ) :
    ‖restrictVec S v‖ = √(∑ n ∈ S, v n ^ 2) := by
  classical
  rw [restrictVec, EuclideanSpace.norm_eq]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  exact Finset.sum_coe_sort S (fun n => v n ^ 2)

theorem restrictVec_sub (S : Finset ι) (v w : ι → ℝ) :
    restrictVec S (fun n => v n - w n) = restrictVec S v - restrictVec S w := by
  ext i; simp [restrictVec]

theorem restrictVec_smul (S : Finset ι) (s : ℝ) (v : ι → ℝ) :
    restrictVec S (fun n => s * v n) = s • restrictVec S v := by
  ext i; simp [restrictVec]

/-- `s ≠ 0` is redundant in Paper J `lem:thb-ratio`: it follows from the hypotheses. -/
theorem jb_ratio_ne_zero_left (S : Finset ι) (Ψ f : ι → ℝ) {c0 δ s : ℝ}
    (hδ : δ < c0) (hΨ : c0 ≤ √(∑ n ∈ S, Ψ n ^ 2))
    (hs : √(∑ n ∈ S, (s * f n - Ψ n) ^ 2) ≤ δ) : s ≠ 0 := by
  rintro rfl
  have : √(∑ n ∈ S, Ψ n ^ 2) ≤ δ := by simpa using hs
  linarith

/-- **Normalisation ratios** (Paper J `lem:thb-ratio`).  Proved; the hypotheses `s, t ≠ 0` of the paper
are derived, not assumed. -/
theorem jb_ratio (S : Finset ι) (Ψ f g : ι → ℝ) {c0 δ ε s t : ℝ}
    (hΨ : c0 ≤ √(∑ n ∈ S, Ψ n ^ 2)) (hδ : δ < c0)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfg : √(∑ n ∈ S, (f n - g n) ^ 2) ≤ ε * √(∑ n ∈ S, g n ^ 2))
    (hs : √(∑ n ∈ S, (s * f n - Ψ n) ^ 2) ≤ δ)
    (ht : √(∑ n ∈ S, (t * g n - Ψ n) ^ 2) ≤ δ) :
    t ≠ 0 ∧ |s / t - 1| ≤ (ε + 2 * δ / (c0 - δ)) / (1 - ε) := by
  have hs0 := jb_ratio_ne_zero_left S Ψ f hδ hΨ hs
  have ht0 := jb_ratio_ne_zero_left S Ψ g hδ hΨ ht
  refine ⟨ht0, ?_⟩
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hs
  have key := jop_normalisation_ratio (restrictVec S f) (restrictVec S g) (restrictVec S Ψ)
    hs0 ht0 hε0 hε1 hδ0 hδ (by rwa [norm_restrictVec]) ?_ ?_ ?_
  · exact key
  · rw [← restrictVec_sub, norm_restrictVec, norm_restrictVec]; exact hfg
  · rw [← restrictVec_smul, ← restrictVec_sub, norm_restrictVec]; exact hs
  · rw [← restrictVec_smul, ← restrictVec_sub, norm_restrictVec]; exact ht

/-- info: 'FormalResearch.JB.jb_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_ratio

end FormalResearch.JB
