module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionTwo
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionOneAssembly

/-!
# `g > 0` for `t ≥ t(q) + 1` in the two-simple-zero transfer (`upper_transfer.tex`, `ut:T2`)

Region I (`TwoZeroRegionOne`) together with Region II (`TwoZeroRegionTwo`, `twoZero_regionII_pos`): for every compact
family of admissible designs, `c'` large, `d ∈ 𝒦`: `2 g(c'x²/3) = twoZeroG d c' x > 0` whenever
`c' x²/3 ≥ t(q) + 1`, and `2 g(t) > 0` for `t ≥ tAiry c' q + 1` at `x = √(3t/c')`.  This is the `pos` field of
`TwoZeroTransferData` for the test `h₂ = sech² B₂`.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel

/-- **`g > 0` for `c' x²/3 ≥ t(q) + 1`** (`ut:T2`, first line of `eq:ut:T2`), at `w = 1`, uniformly on a compact family
of admissible designs. -/
theorem twoZero_pos_x {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, 0 ≤ x →
      c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 → 0 < d.twoZeroG c' x :=
  twoZero_pos_x_of_regionTwo hK hA (twoZero_regionII_pos hK hA)

/-- The same in the variable `t`: `2 g(t) > 0` for `t ≥ tAiry c' q + 1`. -/
theorem twoZero_pos_t {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ t : ℝ, tAiry c' d.q + 1 ≤ t →
      0 < (sechSqProfile ((xOf c' t : ℝ) : ℂ) * d.twoZeroComb c' ((xOf c' t : ℝ) : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) t).re :=
  twoZero_pos_of_regionTwo hK hA (twoZero_regionII_pos hK hA)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_pos_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_pos_x

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_pos_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_pos_t

end FormalResearch.ModularBootstrap.TwoLevel
