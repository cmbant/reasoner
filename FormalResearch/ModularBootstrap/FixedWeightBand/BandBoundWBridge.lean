module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundW
public import FormalResearch.ModularBootstrap.FixedWeightBand.EdgeKernelWBridge

/-!
# Bridge: Proposition `Y_V` at Weight `w` versus the Spinless Virasoro Version (`vlo:YV`)

* `proposition_YV_of_W`: the Virasoro `StripMultiplier.proposition_YV` (`virasoroProblem`,
  `W̃_V = tildeWV`) is the `w = 1` instance of `proposition_YV_W` (the threshold `c₀` differs: it is
  `ywThresh`, which contains the Virasoro threshold `yvThresh` and the weight-`w` scale).
-/

@[expose] public section

open Complex MeasureTheory Set

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart
open FormalResearch.ModularBootstrap.StripMultiplier (tildeWV langerDelta)

/-- The Virasoro Proposition `Y_V` is the `w = 1` instance of `proposition_YV_W`. -/
theorem proposition_YV_of_W {A_thr : ℝ} (hA_thr : 0 ≤ A_thr) :
    ∃ (c₀ C_Y b : ℝ), 10000 ≤ c₀ ∧ 0 < C_Y ∧ 0 < b ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R → R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 →
        langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' 0 ≤ T →
        T ≤ langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-A_thr) →
        ∀ {g : ℝ → ℝ}, TestClass virasoroProblem (c' / 12) g →
          0 < virasoroProblem.cardyNorm (c' / 12) g →
          (∀ t ∈ Ici T, 0 ≤ g t) →
          ∃ u_tilde : ℝ → ℝ,
            (∀ u ∈ Icc (-R) 0,
              u_tilde (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' u) = u) ∧
            let M := virasoroProblem.cardyNorm (c' / 12) g
            let B₁ := R⁻¹ * ∫ t in Icc T
                (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-R)),
              (-u_tilde t) * (g t * virasoroProblem.cardyV (c' / 12) t / M)
            let B₂ := ∫ t in Ici
                (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-R)),
              g t * virasoroProblem.cardyV (c' / 12) t / M
            0 ≤ B₁ ∧ 0 ≤ B₂ ∧
            ∀ {ζ₀ : ℂ} {ψ : ℝ},
              kappaV * c' ^ (-(1 / 3 : ℝ)) * √R / 3 ≤ ‖ζ₀‖ →
              ‖ζ₀‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √R) →
              ζ₀.re = ‖ζ₀‖ * Real.cos ψ →
              c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
              ‖tildeWV c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
              ‖tildeWV c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
  obtain ⟨c₀, C_Y, b, h1, h2, h3, H⟩ := proposition_YV_W virasoroProblem hA_thr
  refine ⟨c₀, C_Y, b, h1, h2, h3, fun {c' R T} hc' hR_lb hR_ub hT_lo hT_hi {g} hg hM hg_nn => ?_⟩
  obtain ⟨u, hu, rest⟩ := H hc' hR_lb hR_ub hT_lo hT_hi hg hM hg_nn
  have hfun : tildeWW virasoroProblem.w c' g = tildeWV c' g :=
    funext fun ζ => tildeWW_one_eq c' g ζ
  refine ⟨u, hu, ?_⟩
  simpa only [hfun] using rest

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.proposition_YV_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_YV_of_W

end FormalResearch.ModularBootstrap.FixedWeightBand
