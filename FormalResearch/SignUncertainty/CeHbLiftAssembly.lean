module

public import FormalResearch.SignUncertainty.Headlines
public import FormalResearch.SignUncertainty.EuclidCELift

/-!
# `thm:ce-hb-lift` at `m₀ = 1`, `N = Ai`: the Euclidean assembly from the Hankel pair (M6)

`CeHankelPair` is the Hankel-level content of `thm:ce-hb-lift` at `(P, Q) = (1, 0)`: under the strict Laplace
positivity of `-G_Ai`, for every large `d` there is a radial profile `G` on `[0, ∞)` with Hankel transform
`ĝ = 𝓗_{d/2} G ≥ 0`, `G(0) = ĝ(0) > 0`, `G ≤ 0` on `[T, ∞)` and `T ≤ c/π² + A c^{1/3} + K₀` (`c = d/2`).
`ce_hb_lift_airy_of_hankelPair` shows that this gives `CeHbLift ShellHBData.airy`: the pair lifts to `ℝ^d`
(`ceAdmissible_of_hankelPair`), the prescribed-shell conditions are vacuous at `m = 1` (`S = {a₁}`, `t_m = a₁`)
and the offsets play no role.

**`CeHankelPair` is not proved here.**  It is the open Mellin-lift construction of the paper (convolution source,
pre-edge, window and post-edge signs); this module only reduces `CeHbLift ShellHBData.airy` to it, so the headline
field `ce_hb_lift_m1` stays open until `CeHankelPair` is a theorem.  The Laplace premise of `CeHankelPair` is true
(`shellLaplaceF_m1_pos`) and is kept only to mirror `CeHbLift`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The Hankel-level statement of `thm:ce-hb-lift` at `m₀ = 1`, `N = Ai` (`c = d/2`, so the Hankel kernel index is
`d/2`): the Laplace hypothesis gives `K₀`, `d₀` and, in every dimension `d ≥ d₀`, a Cohn--Elkies pair
(`G`, `ĝ = 𝓗_{d/2} G`) of threshold `T ≤ c/π² + A c^{1/3} + K₀`. -/
def CeHankelPair : Prop :=
  (∀ y : ℝ, 0 < y → 0 < airyLaplace (fun u => -(ShellHBData.airy.G (u : ℂ)).re) y) →
    ∃ (K₀ : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∃ (T : ℝ) (G : ℝ → ℝ),
      ContinuousOn G (Ici 0) ∧
      IntegrableOn (fun Δ => G Δ * hankelRho0 ((d : ℝ) / 2) Δ) (Ioi 0) ∧
      (∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ besselHankelTransform ((d : ℝ) / 2) G Δ) ∧
      IntegrableOn (fun Δ => besselHankelTransform ((d : ℝ) / 2) G Δ * hankelRho0 ((d : ℝ) / 2) Δ) (Ioi 0) ∧
      0 < G 0 ∧ G 0 = besselHankelTransform ((d : ℝ) / 2) G 0 ∧
      (∀ Δ : ℝ, T ≤ Δ → G Δ ≤ 0) ∧
      T ≤ ((d : ℝ) / 2) / π ^ 2 + airyOrderCoeff * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + K₀

/-- **`ce_hb_lift_m1` from the Hankel pair** (`thm:ce-hb-lift`, `m₀ = 1`, `N = Ai`): `CeHankelPair → CeHbLift ShellHBData.airy`.
Conditional on the open `CeHankelPair`; the odd-card premise is `m = 1`, the shell conditions are vacuous and the offsets
unused. -/
theorem ce_hb_lift_airy_of_hankelPair (H : CeHankelPair) : CeHbLift ShellHBData.airy := by
  intro _ hlap R_off _
  obtain ⟨K₀, d₀, hd₀⟩ := H hlap
  have hA : -(ShellHBData.airy.tm / hankelBeta1) = airyOrderCoeff := by
    unfold airyOrderCoeff
    rw [abs_of_neg (airyZero_neg 1)]
    show -(airyZero 1 / hankelBeta1) = -airyZero 1 / hankelBeta1
    ring
  have hcard : ShellHBData.airy.S.card = 1 :=
    ShellHBData.airy.m_eq.elim (fun h => h.2) (fun h => False.elim (h.1 rfl))
  refine ⟨K₀, max d₀ 2, fun d hd r _ => ?_⟩
  obtain ⟨T, G, hcont, hint, hnn, hhint, h0, horigin, htail, hT⟩ := hd₀ d (le_trans (le_max_left _ _) hd)
  have hd2 : 2 ≤ d := le_trans (le_max_right _ _) hd
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc] at hint hnn hhint horigin hT
  have hTpos : 0 < T := by
    by_contra hneg
    push Not at hneg
    exact absurd (htail 0 (by linarith)) (not_le.mpr h0)
  have hadm := ceAdmissible_of_hankelPair n hn hTpos hcont hint hnn hhint h0 horigin htail
  have hshell : ∀ t ∈ ShellHBData.airy.S, t ≠ ShellHBData.airy.tm → False := by
    intro t ht htm
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have h1 : t = a := by rw [ha] at ht; exact Finset.mem_singleton.mp ht
    have h2 : ShellHBData.airy.tm = a := by
      have := ShellHBData.airy.tm_mem; rw [ha] at this; exact Finset.mem_singleton.mp this
    exact htm (h1.trans h2.symm)
  refine ⟨√(2 * T), ⟨fun x : Euc (n + 1) => G (‖x‖ ^ 2 / 2),
    ⟨hadm, fun x y hxy => by simp only [hxy], fun t ht htm x _ => (hshell t ht htm).elim⟩⟩, ?_⟩
  have e : ((n + 1 : ℕ) : ℝ) / (2 * π ^ 2) - (ShellHBData.airy.tm / hankelBeta1) * (((n + 1 : ℕ) : ℝ) / 2) ^ (1 / 3 : ℝ) + K₀ =
      ((n : ℝ) + 1) / 2 / π ^ 2 + airyOrderCoeff * (((n : ℝ) + 1) / 2) ^ (1 / 3 : ℝ) + K₀ := by
    rw [← hA, hc]; push_cast; ring
  rw [e, Real.sq_sqrt (by linarith)]
  linarith

/-- info: 'FormalResearch.SignUncertainty.ce_hb_lift_airy_of_hankelPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_hb_lift_airy_of_hankelPair

end FormalResearch.SignUncertainty
