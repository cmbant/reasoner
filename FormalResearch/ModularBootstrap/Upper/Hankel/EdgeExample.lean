module

public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound

/-!
# Non-vacuity of the hypotheses of Lemmas `SD_H` and `SD_G`

The reference profile `h₀(b) = sech²(π b/2)` (the case `B_D ≡ 1` of the TeX remark after
Lemma `SD_G`) satisfies every hypothesis: it is even, holomorphic and continuous on the closed
substrip `0 ≤ Im b ≤ 1/2` (its poles are at `Im b ∈ 2ℤ + 1`), `‖h₀(b)‖ ≤ 8 e^{-π|Re b|}` there, and the
`sech²` bound holds on `E₊` with `C_E = 1`.  Hence `edge_hankel_representation` and
`edge_global_bound` apply to it (`edge_hankel_representation_sech`, `edge_global_bound_sech`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- The reference profile `sech²(π b/2)`. -/
noncomputable def sechSqProfile (b : ℂ) : ℂ := (1 : ℂ) / Complex.cosh (π * b / 2) ^ 2

lemma cosh_ne_zero_strip {b : ℂ} (h0 : 0 ≤ b.im) (h1 : b.im ≤ 1 / 2) :
    Complex.cosh (π * b / 2) ≠ 0 := by
  intro h
  have := norm_cosh_sq_ge h0 h1
  rw [h, norm_zero] at this
  have hc := Real.cosh_pos (π * b.re / 2)
  nlinarith

/-- The reference profile `sech²(π b/2)` satisfies the hypotheses of Lemma `SD_H` (`a = π`, `C = 8`). -/
theorem edgeHankelHyp_sech : EdgeHankelHyp sechSqProfile π 8 where
  even := by
    intro r
    unfold sechSqProfile
    rw [show (π : ℂ) * -(r : ℂ) / 2 = -((π : ℂ) * r / 2) by ring, Complex.cosh_neg]
  holo := by
    unfold sechSqProfile
    intro b hb
    have hne := cosh_ne_zero_strip hb.1.le hb.2.le
    have : DifferentiableAt ℂ (fun b : ℂ => (1 : ℂ) / Complex.cosh (π * b / 2) ^ 2) b := by
      refine (differentiableAt_const _).div ?_ (pow_ne_zero 2 hne)
      fun_prop
    exact this.differentiableWithinAt
  cont := by
    unfold sechSqProfile
    intro b hb
    have hne := cosh_ne_zero_strip hb.1 hb.2
    have : ContinuousAt (fun b : ℂ => (1 : ℂ) / Complex.cosh (π * b / 2) ^ 2) b := by
      refine continuousAt_const.div ?_ (pow_ne_zero 2 hne)
      fun_prop
    exact this.continuousWithinAt
  decay := by
    intro b h0 h1
    exact sech_sq_le_strip h0 h1

/-- The `sech²` bound on `E₊` with `C_E = 1` for the reference profile. -/
theorem edgeSechBound_sech : EdgeSechBound sechSqProfile 1 := by
  intro v
  unfold sechSqProfile
  simp

/-- Lemma `SD_H` for the reference profile. -/
theorem edge_hankel_representation_sech {c' x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankel c' sechSqProfile (c' * x ^ 2 / 3) =
      (2 * π * c' / 3 : ℂ) * ∫ v : ℝ, sechSqProfile ((v : ℂ) + I / 2) *
        hankel0 (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2)) * ((v : ℂ) + I / 2) :=
  edge_hankel_representation Real.pi_pos edgeHankelHyp_sech hc hx

/-- Lemma `SD_G` for the reference profile, with `C_E = 1`. -/
theorem edge_global_bound_sech :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c' x : ℝ, 0 < c' → 0 < x →
      Real.exp (c' * edgeL x) * ‖edgeHankel c' sechSqProfile (c' * x ^ 2 / 3)‖ ≤ K * √(c' / x) := by
  obtain ⟨K, hK0, hK⟩ := edge_global_bound
  refine ⟨K, hK0, fun c' x hc hx => ?_⟩
  simpa using hK sechSqProfile π 8 1 Real.pi_pos edgeHankelHyp_sech zero_le_one edgeSechBound_sech c' x hc hx

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edgeHankelHyp_sech' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeHankelHyp_sech

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_global_bound_sech' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_global_bound_sech

end FormalResearch.ModularBootstrap.Upper.Hankel
