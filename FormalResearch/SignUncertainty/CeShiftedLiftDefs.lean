module

public import FormalResearch.SignUncertainty.AiryRationalSeeds
public import FormalResearch.SignUncertainty.HankelBessel
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# Lift seeds and the statement of `thm:ce-shifted-lift`

Source: `CFT/sign_uncertainty/paper/ce_shifted_witnesses.tex`, Theorem `thm:ce-shifted-lift`.

* `IsAiryLiftSeed S u_* H₀`: hypotheses (a)-(c) of `thm:ce-shifted-lift` on a real
  `H₀ ∈ ℛ_Ai^gen` (`InGenRationalAiry`, `(e22)`-(e23)`).
* `CeShiftedLift : Prop`: the Hankel-level conclusion of `thm:ce-shifted-lift`, for every compact `S`
  and every lift seed. **Not proved** (open M6 Mellin-Hankel lift work, parallel to
  `CeHbLiftAssembly.CeHankelPair`); it is the field `shifted_lift` of `CeCanonicalInputs`.

This file holds only definitions, so that `CeCanonicalDefs` can import it; the consequences
(`thm_al_rational_density`, `airyUStrict_eq_airyUSh`, `ce_airy_transfer_upper_of_shifted_lift`) are in
`AiryRationalDensity.lean`.
-/

@[expose] public section

open Real MeasureTheory Set FormalResearch.Special FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

/-- Rational-Airy lift seed at `(S, u_*)`: hypotheses (a)-(c) of `thm:ce-shifted-lift`
(`ce_shifted_witnesses.tex`). `H₀ ∈ ℛ_Ai^gen` (real on `ℝ` and integrable, by `InAiryClass`);
(a) `∫ H₀ = 0` and `H₀ < 0` on `S`; (b) either the strict cutoff `-H₀(u) ≥ c₀ (1 + |u|)^{-3/2}` on
`(-∞, u_*]`, or a simple first zero (`H₀ < 0` on `(-∞, u_*)`, `H₀(u_*) = 0 < H₀'(u_*)`, and
`-H₀(-x) ≥ c₀ (1 + x)^{-3/2}` for `x ≥ |u_*| + 1`); (c) `β_+(H₀) > 0` (`eq:ce-beta-plus`) and
`ℒ_y(H₀) ≥ 0` for every `y > 0`. -/
def IsAiryLiftSeed (S : Set ℝ) (u_star : ℝ) (H₀ : ℂ → ℂ) : Prop :=
  InGenRationalAiry H₀ ∧
  (∫ u : ℝ, (H₀ (u : ℂ)).re) = 0 ∧
  (∀ s ∈ S, (H₀ (s : ℂ)).re < 0) ∧
  ((∃ c₀ : ℝ, 0 < c₀ ∧ ∀ u : ℝ, u ≤ u_star →
      c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(H₀ (u : ℂ)).re) ∨
   ((∀ u : ℝ, u < u_star → (H₀ (u : ℂ)).re < 0) ∧
    (H₀ (u_star : ℂ)).re = 0 ∧ 0 < (deriv H₀ (u_star : ℂ)).re ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℝ, |u_star| + 1 ≤ x →
      c₀ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ -(H₀ ((-x : ℝ) : ℂ)).re)) ∧
  0 < airyBetaPlus H₀ ∧
  (∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (H₀ (u : ℂ)).re) y)

/-- **Statement of `thm:ce-shifted-lift`** (`ce_shifted_witnesses.tex`), at Hankel level; **not proved**
(open M6 Mellin-Hankel lift work, parallel to `CeHbLiftAssembly.CeHankelPair`).

For every compact `S ⊆ ℝ` (possibly empty), every `u_*` and every lift seed `IsAiryLiftSeed S u_* H₀`,
there are `K₀ > 0`, a radius `ρ₁ > 0` and `d₀` such that for every dimension `d ≥ d₀` (`c = d/2`) there is
a radial Cohn-Elkies Hankel pair `(G, 𝓗_{d/2} G)`: `G` continuous on `[0, ∞)`, both members integrable
against `ρ₀`, `𝓗_{d/2} G > 0` on `[0, ∞)`, `G(0) = 𝓗_{d/2} G(0) > 0`, `G(Δ) < 0` for
`Δ ≥ c/π² - (u_*/β₁) c^{1/3} + K₀`, and `G < 0` at every nonnegative point `c/π² - (s'/β₁) c^{1/3}` with
`dist(s', S) ≤ ρ₁`.

Relation to the paper: the paper's pair exists for every real `c ≥ c_⋆` and decays like
`O(Δ^{-c}(log Δ)^{-3/2})`; here only `c = d/2` with `d : ℕ` and integrability against `ρ₀` are asked, so
`CeShiftedLift` is implied by the paper's statement. The `ρ₁` clause is the paper's uniformity "for
`S^{(c)}` contained in a sufficiently small fixed neighbourhood of `S`" (equivalently, the paper's
statement applied to the compact neighbourhood `{s' : dist(s', S) ≤ ρ₁}`, on which `H₀ < 0` for small
`ρ₁` by continuity). -/
def CeShiftedLift : Prop :=
  ∀ (S : Set ℝ), IsCompact S → ∀ (u_star : ℝ) (H₀ : ℂ → ℂ), IsAiryLiftSeed S u_star H₀ →
    ∃ (K₀ ρ₁ : ℝ) (d₀ : ℕ), 0 < K₀ ∧ 0 < ρ₁ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ G : ℝ → ℝ,
        ContinuousOn G (Ici 0) ∧
        IntegrableOn (fun Δ => G Δ * hankelRho0 ((d : ℝ) / 2) Δ) (Ioi 0) ∧
        (∀ Δ : ℝ, 0 ≤ Δ → 0 < besselHankelTransform ((d : ℝ) / 2) G Δ) ∧
        IntegrableOn (fun Δ =>
          besselHankelTransform ((d : ℝ) / 2) G Δ * hankelRho0 ((d : ℝ) / 2) Δ) (Ioi 0) ∧
        0 < G 0 ∧ G 0 = besselHankelTransform ((d : ℝ) / 2) G 0 ∧
        (∀ Δ : ℝ,
          ((d : ℝ) / 2) / π ^ 2 - (u_star / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + K₀ ≤ Δ →
          G Δ < 0) ∧
        (∀ s' : ℝ, (∃ s ∈ S, |s' - s| ≤ ρ₁) →
          0 ≤ ((d : ℝ) / 2) / π ^ 2 - (s' / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) →
          G (((d : ℝ) / 2) / π ^ 2 - (s' / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ)) < 0)

end FormalResearch.SignUncertainty
