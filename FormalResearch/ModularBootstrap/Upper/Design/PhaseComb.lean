module

public import FormalResearch.ModularBootstrap.Upper.Design.AmplitudeLogDeriv
public import FormalResearch.ModularBootstrap.Upper.Saddle.EdgePhaseZero
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeGlobalBound

/-!
# The abstract phase decomposition `PhaseComb` and the amplitude `𝒜_x`

The data of a comb with a phase decomposition (`ut:Phi`, `ut:T2`): the facts about a pair `(B, Φ₁)` used for
Lemmas `SD_V`, `SD_G`, `FW-SD` and `Φ`, and the comb-independent amplitude `𝒜_x = combAmplitude` of `(SD.4)`.
The design combs, and the combs `T_{χ(p)} B_D` of `ut:T2`, are instances.  The consequences are in
`CombTransformAbs` (order `0`: `SD_V`) and `CombTransformP` (every order `p`: `FW-SD`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle

/-- The comb-independent amplitude `𝒜_x = 2 e^{-2πnx/3} |ℰ(b_x)| |1 + ε_H(k b_x)|
(|b_x|/(x F'(v_x)))^{1/2}` of `(SD.4)` for `ℰ = sech²(π b/2)` (the factor `e^{Re Φ₁(b_x)}` is `1`
for the combs of Lemma `Φ`, see `designPhi1_re_edge`). -/
noncomputable def combAmplitude (n x : ℝ) : ℝ :=
  sdvPrefactor n x sechSqProfile (fun _ => 0) hankelEps

lemma sechSqProfile_neg_conj (b : ℂ) :
    sechSqProfile (-(starRingEnd ℂ b)) = starRingEnd ℂ (sechSqProfile b) := by
  unfold sechSqProfile
  have h1 : (π : ℂ) * -(starRingEnd ℂ b) / 2 = -(starRingEnd ℂ ((π : ℂ) * b / 2)) := by
    rw [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]; ring
  rw [h1, Complex.cosh_neg, Complex.cosh_conj]
  simp

/-- The data of a comb with a phase decomposition: the facts about `(B, Φ₁)` used for Lemmas `SD_V`,
`SD_G` and `Φ`.  `|B| ≤ 1` on `|Im b| ≤ 1/2`, `B = exp (c' Φ₀ + Φ₁)` on `𝒩`, `Φ₁` differentiable on
`combNMid` with `‖Φ₁'‖, ‖Φ₁''‖ ≤ M_φ` on `𝒩`, `Re Φ₁ = 0` and `B(-b̄) = conj B(b)` on `E₊`. -/
structure PhaseComb (c' Mφ : ℝ) (B Φ₁ : ℂ → ℂ) : Prop where
  bound : ∀ b : ℂ, |b.im| ≤ 1 / 2 → ‖B b‖ ≤ 1
  eq : ∀ b ∈ combN, Complex.exp ((c' : ℂ) * edgePhi0Blaschke b + Φ₁ b) = B b
  diff : DifferentiableOn ℂ Φ₁ combNMid
  deriv_bound : ∀ b ∈ combN, ‖deriv Φ₁ b‖ ≤ Mφ ∧ ‖deriv (deriv Φ₁) b‖ ≤ Mφ
  re_edge : ∀ b : ℂ, b.im = 1 / 2 → (Φ₁ b).re = 0
  symm_edge : ∀ b : ℂ, b.im = 1 / 2 → B (-(starRingEnd ℂ b)) = starRingEnd ℂ (B b)

end FormalResearch.ModularBootstrap.Upper.Design
