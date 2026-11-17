module

public import FormalResearch.MatrixAnalysis.Spectral.FanHoffman
public import FormalResearch.Racah.P2AnalyticL2PolarAbs

/-!
# Fan–Hoffman for `Racah.Polar.polarFactor`

Namespace `FormalResearch.MatrixAnalysis.Spectral`.  Claim class: **proved** (no hypothesis, no new axiom).

For an injective real linear map `T : V →ₗ[ℝ] W` between finite-dimensional real inner product spaces, the polar
factor `U = Racah.Polar.polarFactor T` satisfies `‖T - U‖_op ≤ ‖T - V'‖_op` for every linear isometry
`V' : V →ₗ[ℝ] W` (`fanHoffman_polarFactor`), by `Spectral.fanHoffman_polar` applied to
`T = U ∘ polarRoot T` (`Polar.polarFactor_root`, `Polar.polarRoot_pos`, `Polar.inner_polarFactor`).
This is the "nearest orthogonal/unitary matrix" statement used for polar repair.

Not formalised here: the complex case (the repository's `Polar.polarFactor` is real), the Frobenius-norm form.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis.Spectral

open FormalResearch.Racah

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The polar factor of an injective `T` is isometric. -/
theorem norm_polarFactor (T : V →ₗ[ℝ] W) (hT : Function.Injective T) (x : V) :
    ‖Polar.polarFactor T hT x‖ = ‖x‖ := by
  have h := Polar.inner_polarFactor T hT x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **Fan–Hoffman for the polar factor** (operator norm): if `‖(T - V') x‖ ≤ ε ‖x‖` for an isometry `V'`
then `‖(T - polarFactor T) x‖ ≤ ε ‖x‖`. -/
theorem fanHoffman_polarFactor (T : V →ₗ[ℝ] W) (hT : Function.Injective T) (V' : V →ₗ[ℝ] W)
    (hV' : ∀ x, ‖V' x‖ = ‖x‖) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ x, ‖(T - V') x‖ ≤ ε * ‖x‖) (x : V) :
    ‖(T - Polar.polarFactor T hT) x‖ ≤ ε * ‖x‖ :=
  fanHoffman_polar (N := Module.finrank ℝ V) rfl (Polar.polarRoot_pos T) (norm_polarFactor T hT) hV'
    (fun y => (Polar.polarFactor_root T hT y).symm) hε h x

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.norm_polarFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.norm_polarFactor

/-- info: 'FormalResearch.MatrixAnalysis.Spectral.fanHoffman_polarFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.Spectral.fanHoffman_polarFactor

end FormalResearch.MatrixAnalysis.Spectral
