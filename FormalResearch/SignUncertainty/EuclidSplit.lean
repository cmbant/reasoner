module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import FormalResearch.SignUncertainty.HankelBessel

/-!
# Slicing `ℝ^{n+1} ≅ ℝ × ℝ^n` (radial Fourier transform, Euclidean-to-Hankel dictionary)

`EuclSplit n : EuclideanSpace ℝ (Fin (n+1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin n)` is measure preserving, with
`‖(u,y)‖² = u² + ‖y‖²` and `⟪(u,y), r e₀⟫ = u r`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- Euclidean space `ℝ^d` (shorthand). -/
abbrev EuclSp (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The splitting of the first coordinate. -/
noncomputable def euclSplit (n : ℕ) : EuclSp (n + 1) ≃ᵐ ℝ × EuclSp n :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin n → ℝ))))

lemma measurePreserving_euclSplit (n : ℕ) : MeasurePreserving (euclSplit n) volume volume := by
  unfold euclSplit
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))).trans ?_
  refine (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans ?_
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (μ := volume)).prod (PiLp.volume_preserving_toLp (Fin n))

lemma euclSplit_symm_apply_zero (n : ℕ) (u : ℝ) (y : EuclSp n) :
    ((euclSplit n).symm (u, y)) 0 = u := by
  simp [euclSplit]
  rfl

lemma euclSplit_symm_apply_succ (n : ℕ) (u : ℝ) (y : EuclSp n) (i : Fin n) :
    ((euclSplit n).symm (u, y)) i.succ = y i := by
  simp [euclSplit]
  rfl

lemma euclSplit_symm_norm_sq (n : ℕ) (u : ℝ) (y : EuclSp n) :
    ‖(euclSplit n).symm (u, y)‖ ^ 2 = u ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [euclSplit_symm_apply_zero, euclSplit_symm_apply_succ, Real.norm_eq_abs, sq_abs]

lemma euclSplit_symm_inner (n : ℕ) (u : ℝ) (y : EuclSp n) (r : ℝ) :
    inner ℝ ((euclSplit n).symm (u, y)) (EuclideanSpace.single (0 : Fin (n + 1)) r) = u * r := by
  rw [EuclideanSpace.inner_single_right, euclSplit_symm_apply_zero]
  simp [mul_comm]

end FormalResearch.SignUncertainty
