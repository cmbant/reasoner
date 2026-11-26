module

public import FormalResearch.ModularBootstrap.Mixtures.CrossingCommon

/-!
# `pmix:crossing` (a): the mixed crossing sum rule

`positive_mixtures.tex`, Lemma PM.3 (a), for an atomic common source at a charge with the floor (`FloorData.At a`).

* `ShiftSource.crossing_xi_iff`: the crossing equation `Ẑ(β) = β^{-w} Ẑ(1/β)`, `Ẑ(β) = v_a(β) + ∫ e^{-2πβt} dν`
  (`pmix:cross`) is equivalent, for a measure with finite Laplace transforms, to the Ξ-form
  `∫ Ξ_β dν = ∫ Ξ_β ρ dt` used by `SourceCrossingMeasure` (`ρ = 2π V` the Cardy density).
* `ZhatCrossingMeasure`: the mixed crossing measure of the paper in the original form, and its conversion
  `ZhatCrossingMeasure.toSource`.
* `pmix_crossing_a`: (1) the one-sided inequality, (2) the equality under decay, (3) the equality case, and the
  exclusion of a crossing measure supported on `[T, ∞)`.  Proved by the unconditional port of `Lemma FW-X`
  (`lemma_fwX_one_sided_src`, `lemma_fwX_equality_src`) fed by `FloorData.At.crossingBounds`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing

/-! ### The original form of the crossing equation -/

/-- **`pmix:cross` ⇔ Ξ-form.**  For a measure with finite positive-temperature Laplace transforms, the crossing
equation `v_a(β) + ∫ e^{-2πβt} dν = β^{-w} (v_a(1/β) + ∫ e^{-2πt/β} dν)` is equivalent to
`∫ Ξ_β dν = ∫ Ξ_β ρ dt`, `ρ = 2π V`. -/
theorem ShiftSource.crossing_xi_iff (src : ShiftSource) (a : ℝ) {ν : Measure ℝ}
    (hlap : ∀ {β : ℝ}, 0 < β → IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) ν)
    {β : ℝ} (hβ : 0 < β) :
    (∫ t in Ici 0, thermalDiff src.w β t ∂ν =
        ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t) ↔
      (src.srcFun a β + ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂ν =
        β ^ (-(src.w : ℝ)) *
          (src.srcFun a β⁻¹ + ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂ν)) := by
  have hβi : 0 < β⁻¹ := inv_pos.mpr hβ
  have h1 := src.cardyV_laplace a hβ
  have h2 := src.cardyV_laplace a hβi
  rw [inv_inv] at h2
  have hpow : β ^ (-(src.w : ℝ)) * (β⁻¹) ^ (-(src.w : ℝ)) = 1 := by
    rw [Real.inv_rpow hβ.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hβ _).ne'
  have hnu : ∫ t in Ici 0, thermalDiff src.w β t ∂ν =
      (∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂ν) -
        β ^ (-(src.w : ℝ)) * ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂ν := by
    have heq : (fun t => thermalDiff src.w β t) = fun t =>
        Real.exp (-2 * π * β * t) - β ^ (-(src.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
      ext t; unfold thermalDiff; rw [div_eq_mul_inv]; ring_nf
    rw [heq, integral_sub (hlap hβ) ((hlap hβi).const_mul _), integral_const_mul]
  have hrho : ∫ t in Ioi 0, thermalDiff src.w β t * src.cardyDensity a t =
      β ^ (-(src.w : ℝ)) * src.srcFun a β⁻¹ - src.srcFun a β := by
    have heq : (fun t => thermalDiff src.w β t * src.cardyDensity a t) = fun t =>
        (2 * π) * (src.cardyV a t * Real.exp (-2 * π * β * t)) -
          (2 * π) * β ^ (-(src.w : ℝ)) * (src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
      ext t
      unfold thermalDiff ShiftSource.cardyDensity
      rw [div_eq_mul_inv]; ring_nf
    rw [heq, integral_sub (h1.1.const_mul _) (h2.1.const_mul _), integral_const_mul,
      integral_const_mul, h1.2]
    have e2 : 2 * π * β ^ (-(src.w : ℝ)) *
        ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t) = src.srcFun a β := by
      calc 2 * π * β ^ (-(src.w : ℝ)) * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)
          = β ^ (-(src.w : ℝ)) * (2 * π * ∫ t in Ioi 0, src.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
            ring
        _ = β ^ (-(src.w : ℝ)) * ((β⁻¹) ^ (-(src.w : ℝ)) * src.srcFun a β) := by rw [h2.2]
        _ = src.srcFun a β := by rw [← mul_assoc, hpow, one_mul]
    rw [e2]
  rw [hnu, hrho]
  constructor
  · intro h
    linarith
  · intro h
    linarith

end FormalResearch.ModularBootstrap.Mixtures
