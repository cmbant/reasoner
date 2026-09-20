import Mathlib

namespace FormalResearch.QIB

/-!
# QI-B finite-copy U(1) exponent-gap scalar certificate

This module matches the exact scalar identities in
`cmbant/QIprojects:QI-B/B4-orbit-bergman/notes/NEW_RESULTS_THIS_TURN.md`,
section 6, audited on current source head
`1c643e4db3a6be0e8b7826a2f45df4e27dad06b4`.

For the symmetric qubit family `q = 1-p`, the source analysis identifies the
invariant Chernoff exponent with `-log (2 * sqrt (p(1-p)))` and the maximal
compact-orbit squared overlap with `4p(1-p)`.  Lean formalizes the exact scalar
relation between those two quantities.  It does **not** rederive the common
`U(1)` twirl, the binomial law, or the classical Chernoff minimization that
identifies the scalar expression with the operational invariant exponent.
-/

/-- The source-side symmetric Bernoulli Chernoff coefficient. -/
noncomputable def u1InvariantCoefficient (p : ℝ) : ℝ :=
  2 * Real.sqrt (p * (1 - p))

/-- The compact-orbit maximal squared overlap for the symmetric family
`q = 1-p`. -/
def u1CompactOrbitFidelity (p : ℝ) : ℝ :=
  4 * p * (1 - p)

/-- Scalar exponent attached to the source-side invariant coefficient. -/
noncomputable def u1InvariantXi (p : ℝ) : ℝ :=
  -Real.log (u1InvariantCoefficient p)

/-- On the probability interval, compact-orbit fidelity is exactly the square
of the symmetric invariant coefficient. -/
theorem u1CompactOrbitFidelity_eq_coefficient_sq
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    u1CompactOrbitFidelity p = (u1InvariantCoefficient p) ^ 2 := by
  have hprod : 0 ≤ p * (1 - p) :=
    mul_nonneg hp0 (sub_nonneg.mpr hp1)
  unfold u1CompactOrbitFidelity u1InvariantCoefficient
  calc
    4 * p * (1 - p) = 4 * (p * (1 - p)) := by ring
    _ = 4 * (Real.sqrt (p * (1 - p))) ^ 2 := by
      rw [Real.sq_sqrt hprod]
    _ = (2 * Real.sqrt (p * (1 - p))) ^ 2 := by ring

/-- Exact factor-two relation from the source counterexample:
`-log F_K = 2 xi_inv` at the scalar-certificate level. -/
theorem u1CompactOrbit_log_eq_two_invariantXi
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    -Real.log (u1CompactOrbitFidelity p) = 2 * u1InvariantXi p := by
  have hcoeff : 0 < u1InvariantCoefficient p := by
    unfold u1InvariantCoefficient
    have h1p : 0 < 1 - p := sub_pos.mpr hp1
    positivity
  rw [u1CompactOrbitFidelity_eq_coefficient_sq hp0.le hp1.le]
  unfold u1InvariantXi
  rw [pow_two, Real.log_mul hcoeff.ne' hcoeff.ne']
  ring

/-- Away from the trivial midpoint `p=1/2`, the scalar invariant exponent is
strictly positive, so the compact-orbit exponent is genuinely twice rather
than equal to it. -/
theorem u1InvariantXi_pos
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpmid : p ≠ (1 : ℝ) / 2) :
    0 < u1InvariantXi p := by
  have hlin : 2 * p - 1 ≠ 0 := by
    intro h
    apply hpmid
    nlinarith
  have hsq : 0 < (2 * p - 1) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr hlin
  have hFlt : u1CompactOrbitFidelity p < 1 := by
    unfold u1CompactOrbitFidelity
    nlinarith
  have hcoeff0 : 0 ≤ u1InvariantCoefficient p := by
    unfold u1InvariantCoefficient
    positivity
  have hcoeffsq :
      (u1InvariantCoefficient p) ^ 2 = u1CompactOrbitFidelity p := by
    symm
    exact u1CompactOrbitFidelity_eq_coefficient_sq hp0.le hp1.le
  have hcoefflt : u1InvariantCoefficient p < 1 := by
    nlinarith
  have hcoeffpos : 0 < u1InvariantCoefficient p := by
    unfold u1InvariantCoefficient
    have h1p : 0 < 1 - p := sub_pos.mpr hp1
    positivity
  have hlog := Real.log_neg hcoeffpos hcoefflt
  unfold u1InvariantXi
  linarith

/-- The exact scalar certificate of the `U(1)` counterexample: at every
nontrivial symmetric parameter, the compact-orbit log fidelity differs from
the invariant scalar exponent by a factor of two. -/
theorem u1CompactOrbit_exponent_gap
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hpmid : p ≠ (1 : ℝ) / 2) :
    -Real.log (u1CompactOrbitFidelity p) = 2 * u1InvariantXi p ∧
    0 < u1InvariantXi p ∧
    -Real.log (u1CompactOrbitFidelity p) ≠ u1InvariantXi p := by
  have hdouble := u1CompactOrbit_log_eq_two_invariantXi hp0 hp1
  have hxi := u1InvariantXi_pos hp0 hp1 hpmid
  refine ⟨hdouble, hxi, ?_⟩
  intro heq
  rw [heq] at hdouble
  nlinarith

end FormalResearch.QIB
