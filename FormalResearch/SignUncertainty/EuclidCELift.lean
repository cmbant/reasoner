module

public import FormalResearch.SignUncertainty.EuclidHankelDictionary
public import FormalResearch.CohnElkies.CohnElkiesRadius

/-!
# Hankel pair to a Cohn--Elkies function on `ℝ^d` (M6, the Euclidean lift of `thm:ce-hb-lift`)

A radial profile `G` on `[0, ∞)` with Hankel transform `ĝ = 𝓗_{d/2} G`, such that `G(0) = ĝ(0) > 0`, `ĝ ≥ 0` and
`G ≤ 0` on `[T, ∞)`, gives the normalised continuous `L¹` Cohn--Elkies function `x ↦ G(‖x‖²/2)` of radius
`√(2T)` on `ℝ^d`, `d = n + 1 ≥ 2` (`ceAdmissible_of_hankelPair`).  The Fourier transform of the lift is the Hankel
transform (`fourier_radial_hankel`), integrability of both is `integrable_radialLift_iff`.

This is the converse direction of `signWitness_of_hankelFeasible` for the Cohn--Elkies class (`ĝ ≥ 0` instead of the
eigenfunction relation).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- **Hankel pair to Cohn--Elkies** (dimension `d = n + 1 ≥ 2`). -/
theorem ceAdmissible_of_hankelPair (n : ℕ) (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T) {G : ℝ → ℝ}
    (hcont : ContinuousOn G (Ici 0))
    (hint : IntegrableOn (fun Δ => G Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0))
    (hhat_nn : ∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ besselHankelTransform (((n : ℝ) + 1) / 2) G Δ)
    (hhat_int : IntegrableOn
      (fun Δ => besselHankelTransform (((n : ℝ) + 1) / 2) G Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0))
    (h0 : 0 < G 0) (horigin : G 0 = besselHankelTransform (((n : ℝ) + 1) / 2) G 0)
    (htail : ∀ Δ : ℝ, T ≤ Δ → G Δ ≤ 0) :
    IsContinuousL1CEAdmissible (n + 1) (√(2 * T)) (fun x : Euc (n + 1) => G (‖x‖ ^ 2 / 2)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (1 / 2 : ℝ) < ((n : ℝ) + 1) / 2 := by linarith
  have hnorm : ∀ x : Euc (n + 1), 0 ≤ ‖x‖ ^ 2 / 2 := fun x => by positivity
  have hGint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) :=
    (integrable_radialLift_iff n hn G).2 hint
  have hĜc : Continuous (besselHankelTransform (((n : ℝ) + 1) / 2) G) :=
    besselHankelTransform_continuous hc hint
  have hĜint : Integrable (fun x : EuclSp (n + 1) =>
      (besselHankelTransform (((n : ℝ) + 1) / 2) G (‖x‖ ^ 2 / 2) : ℂ)) :=
    (integrable_radialLift_iff n hn _).2 hhat_int
  have hF : ∀ y : Euc (n + 1), 𝓕 (fun x : Euc (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) y =
      ((besselHankelTransform (((n : ℝ) + 1) / 2) G (‖y‖ ^ 2 / 2) : ℝ) : ℂ) :=
    fun y => fourier_radial_hankel n hn hcont hGint y
  have hF0 : 𝓕 (fun x : Euc (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) 0 =
      ((besselHankelTransform (((n : ℝ) + 1) / 2) G 0 : ℝ) : ℂ) := by
    rw [hF 0]; simp
  refine ⟨⟨Real.sqrt_pos.mpr (by linarith), hcont.comp_continuous (by fun_prop) hnorm, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hGint.re
  · have : (𝓕 (fun x : Euc (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ))) = fun y : Euc (n + 1) =>
        ((besselHankelTransform (((n : ℝ) + 1) / 2) G (‖y‖ ^ 2 / 2) : ℝ) : ℂ) := funext hF
    rw [this]; exact hĜint
  · simpa using h0
  · rw [hF0]; simpa [← horigin] using h0
  · intro x hx
    refine htail _ ?_
    have h1 : √(2 * T) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    rw [Real.sq_sqrt (by linarith)] at h1
    linarith
  · intro y
    rw [hF y]
    exact ⟨by simp, by simpa using hhat_nn _ (by positivity)⟩
  · rw [hF0]; simpa using horigin

/-- info: 'FormalResearch.SignUncertainty.ceAdmissible_of_hankelPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceAdmissible_of_hankelPair

end FormalResearch.SignUncertainty
