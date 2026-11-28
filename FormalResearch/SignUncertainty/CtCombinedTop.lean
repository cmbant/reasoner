module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicCombined
public import FormalResearch.SignUncertainty.CtOuterBandFinal

/-!
# `ct:dyadic` (4): pointwise CFU outer-band estimate (`ct_outer_pointwise`)

`ct_outer_pointwise` (`ct:cfu` (2) for `dualK` at `ξ = e^L/π²`, identifying `dualK`, `boasX`
with the outer-band `τ₀`), consumed by `CtLowerLogFreeSkeleton.ct_combined_outer_sharp`.

**Proved**, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### The outer band -/

/-- **`ct:cfu` (2) for `dualK` in the variable `L`** (`(ct:K-outer)`): for `c ≥ 2`, `ε = ±1`, `L > 0` with `μ₀ = c min(1, L^{3/2}) ≥ M`,
`|K_ε(ξ(L);c) + sin X(L)| ≤ K'/μ₀`, `X = cΦ_Ph(τ₀;L) - θ_ε(τ₀)` (`boasX`). -/
theorem ct_outer_pointwise : ∃ M K' : ℝ, 0 < M ∧ 0 ≤ K' ∧ ∀ {c ε L : ℝ}, 2 ≤ c → (ε = 1 ∨ ε = -1) → 0 < L →
    M ≤ c * min 1 (L * Real.sqrt L) →
    |CtDual.dualK ε c (Real.exp L / π ^ 2) + Real.sin (boasX c ε L)| ≤ K' / (c * min 1 (L * Real.sqrt L)) := by
  have key : ∀ {ε : ℝ}, (ε = -1 ∨ ε = 1) → ∃ M K' : ℝ, 0 < M ∧ 0 ≤ K' ∧ ∀ {c L : ℝ}, 2 ≤ c → 0 < L →
      M ≤ c * min 1 (L * Real.sqrt L) →
      |CtDual.dualK ε c (Real.exp L / π ^ 2) + Real.sin (boasX c ε L)| ≤ K' / (c * min 1 (L * Real.sqrt L)) := by
    intro ε hε
    obtain ⟨M, K, hM, hK, H⟩ := CtOsc.ct_cfu_outer hε
    refine ⟨M, K, hM, hK, fun {c L} hc hL hlarge => ?_⟩
    obtain ⟨τ0, hτ0, hm, I, hI, hb⟩ := H hc hL hlarge
    have hτ : τ0 = tau0 L := hankelEdgeM_strictMonoOn.injOn (mem_Ici.2 hτ0.le) (mem_Ici.2 (tau0_pos hL).le)
      (hm.trans (hankelEdgeM_tau0 hL).symm)
    have hlog : Real.log (π ^ 2 * (Real.exp L / π ^ 2)) = L := by
      rw [show π ^ 2 * (Real.exp L / π ^ 2) = Real.exp L by field_simp, Real.log_exp]
    have hphase : ∀ τ : ℝ, CtSd.phaseL L τ = CtOsc.phaseP τ0 τ := by
      intro τ; unfold CtSd.phaseL CtOsc.phaseP; rw [hm]
    have hdI : CtDual.dualI ε c (Real.exp L / π ^ 2) = I := by
      refine Filter.Tendsto.limUnder_eq (hI.congr fun T => ?_)
      refine intervalIntegral.integral_congr fun τ _ => ?_
      simp only [CtDual.dualP_eq, hlog, hphase]
    have hK : CtDual.dualK ε c (Real.exp L / π ^ 2) = -Real.sqrt (π * c / 12) * I.re := by
      unfold CtDual.dualK; rw [hdI]
    have hX : boasX c ε L = c * (-CtOsc.phaseP τ0 τ0) - CtOuter.outerTheta ε τ0 := by
      unfold boasX
      rw [← hτ, CtCfu.edgePhi_eq]
      unfold CtOsc.phaseP; rw [hm]; ring_nf
    rw [hK, hX]
    have := hb
    rw [sub_neg_eq_add] at this
    exact this
  obtain ⟨M1, K1, hM1, hK1, H1⟩ := key (ε := 1) (Or.inr rfl)
  obtain ⟨M2, K2, hM2, hK2, H2⟩ := key (ε := -1) (Or.inl rfl)
  refine ⟨max M1 M2, max K1 K2, lt_max_of_lt_left hM1, le_max_of_le_left hK1, fun {c ε L} hc hε hL hlarge => ?_⟩
  have hc0 : 0 < c := by linarith
  have hmin : 0 < c * min 1 (L * Real.sqrt L) := by
    have : 0 < L * Real.sqrt L := mul_pos hL (Real.sqrt_pos.2 hL)
    positivity
  rcases hε with rfl | rfl
  · exact (H1 hc hL ((le_max_left _ _).trans hlarge)).trans (div_le_div_of_nonneg_right (le_max_left _ _) hmin.le)
  · exact (H2 hc hL ((le_max_right _ _).trans hlarge)).trans (div_le_div_of_nonneg_right (le_max_right _ _) hmin.le)

/-- info: 'FormalResearch.SignUncertainty.ct_outer_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_pointwise

end FormalResearch.SignUncertainty
