module

public import FormalResearch.ModularBootstrap.Upper.Assembly.TailLipschitz

/-!
# `DesignTailBounds` is proved: `Σ₀` at Virasoro for the extremal measures, unconditionally

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (`sr:Sigma0`, `sr:Sigma` Step 3),
`upper_transfer.tex` (`ut:E`, `ut:G`).

The two uniform estimates on `Q_k` that `Families.lean` collected in the named hypothesis
`DesignTailBounds` are proved:

* `Gd_upper` (`TailLipschitz.lean`): the Lipschitz bound `G_k(u) ≤ G_k(a_1)(1 + C|u - a_1|)` on
  `|u - a_1| ≤ 1`, from the uniform growth bound of `W_{k,0}`, the maximum modulus principle and the
  Schwarz lemma for the entire function `G_k = -dslope W_{k,0} a_1`;
* `Gd_lower` (`TailLower.lean`): `Q_k ≥ 1/2` on compacta below `a_1` for large `k`.

* **`designTailBounds`**: `DesignTailBounds`.
* **`sameSiteFamily_designClass_exists`**: `Nonempty (SameSiteFamily designClass)`.
* **`virasoro_sigmaZero_unconditional`**: `Σ₀` at Virasoro for the extremal measures, no hypothesis.
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- **`DesignTailBounds`** (`ut:E`(iv)–(v), `sr:Sigma0`, `sr:Sigma` Step 3): the Lipschitz bound and the
lower bound `Q_k ≥ 1/2` on compacta for the designs `D(N₀ + k, 1/(k + 4), d)`, for every `N₀`. -/
theorem designTailBounds : DesignTailBounds := fun N₀ _ => ⟨Gd_upper N₀, Gd_lower N₀⟩

/-- **`SameSiteFamily designClass`**, unconditionally. -/
theorem sameSiteFamily_designClass_exists : Nonempty (SameSiteFamily designClass) :=
  sameSiteFamily_designClass designTailBounds

/-- **`Σ₀` at Virasoro for the extremal measures, unconditionally.** -/
theorem virasoro_sigmaZero_unconditional :
    ∃ c₀ : ℝ, ∀ cSeq : ℕ → ℝ, Tendsto cSeq atTop atTop → (∀ j, c₀ ≤ cSeq j) →
      ∃ S : CrossingSequence virasoroProblem, S.c = cSeq ∧
        (∀ j, S.τ j = virasoroProblem.T_V (cSeq j)) ∧
        (∀ j, ∀ ε : ℝ, 0 < ε → 0 < (S.meas j).ν (Set.Iio (S.τ j + ε))) ∧
        SigmaZeroConclusion S.c S.τ S.μS :=
  virasoro_sigmaZero_of_tailBounds designTailBounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.designTailBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designTailBounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.sameSiteFamily_designClass_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sameSiteFamily_designClass_exists

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.virasoro_sigmaZero_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_sigmaZero_unconditional

end FormalResearch.ModularBootstrap.Upper.Assembly
