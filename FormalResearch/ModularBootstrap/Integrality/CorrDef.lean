module

public import FormalResearch.ModularBootstrap.Integrality.MidpointGrid

/-!
# The correction property `Corr` (interface of `int:cheb` and `int:cheb-explicit`)

`CFT/modular_bootstrap/paper/integrality.tex`, proof of Lemma INT-M: after cumulative rounding the
integer measure has a moment defect `Δ_m = ∑_i S_i (cos(mα_i) - cos(mα_{i+1}))`
(`0 ≤ S_i < 1`, angles `0 ≤ α_0 ≤ … ≤ α_L ≤ π`; `int:defect-ibp`), which is repaired exactly by moving
`R` integer units at each site of the midpoint grid of size `n` by angle shifts `h_j`.

`Corr n M R` says that this repair is possible, for every defect of the above shape.  The two
proofs of the paper provide it for `n = M + 1` and `R²(M+1) ≥ 16π²M²`
(Euclidean inverse, `int:cheb-explicit`; `CorrEuclid`) and for `n = 2(M+1)`, `R ≥ 320` (filtered
right inverse, `int:cheb`); the assembly `ChebMatching` takes `Corr` as its input.
-/

@[expose] public section

open Real Finset

namespace FormalResearch.ModularBootstrap.Integrality

/-- The grid correction property: every rounding defect (against `cos(mα)`, `1 ≤ m ≤ M`) is
removed, after division by `R`, by an angle shift of the midpoint grid of size `n`. -/
def Corr (n M : ℕ) (R : ℝ) : Prop :=
  ∀ (L : ℕ) (α S : ℕ → ℝ), (∀ i ≤ L, α i ∈ Set.Icc (0 : ℝ) π) → (∀ i < L, α i ≤ α (i + 1)) →
    (∀ i < L, 0 ≤ S i ∧ S i < 1) →
    ∃ h : ℕ → ℝ, ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∑ j ∈ range n, (cos ((m : ℝ) * (midAngle n j + h j)) - cos ((m : ℝ) * midAngle n j)) =
        (1 / R) * ∑ i ∈ range L, S i * (cos ((m : ℝ) * α i) - cos ((m : ℝ) * α (i + 1)))

end FormalResearch.ModularBootstrap.Integrality
