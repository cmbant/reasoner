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

/-! ### Mixed crossing measures in the original form -/

/-- A mixed crossing measure in the form of `pmix:cross`: a positive measure on `[0, ∞)` with finite
positive-temperature Laplace transforms and `Ẑ(β) = β^{-w} Ẑ(1/β)`, `Ẑ(β) = v_a(β) + ∫ e^{-2πβt} dν`. -/
structure ZhatCrossingMeasure (src : ShiftSource) (a : ℝ) where
  ν : Measure ℝ
  supp_nonneg : ν (Iio 0) = 0
  finite_laplace : ∀ {β : ℝ}, 0 < β → IntegrableOn (fun t => Real.exp (-2 * π * β * t)) (Ici 0) ν
  crossing : ∀ {β : ℝ}, 0 < β →
    src.srcFun a β + ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂ν =
      β ^ (-(src.w : ℝ)) * (src.srcFun a β⁻¹ + ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂ν)

/-- The original form of the crossing equation gives the Ξ-form. -/
noncomputable def ZhatCrossingMeasure.toSource {src : ShiftSource} {a : ℝ} (m : ZhatCrossingMeasure src a) :
    SourceCrossingMeasure src a where
  ν := m.ν
  supp_nonneg := m.supp_nonneg
  finite_laplace := m.finite_laplace
  crossing hβ := (src.crossing_xi_iff a m.finite_laplace hβ).2 (m.crossing hβ)

/-- The Ξ-form gives the original form of the crossing equation. -/
noncomputable def SourceCrossingMeasure.toZhat {src : ShiftSource} {a : ℝ} (m : SourceCrossingMeasure src a) :
    ZhatCrossingMeasure src a where
  ν := m.ν
  supp_nonneg := m.supp_nonneg
  finite_laplace := m.finite_laplace
  crossing hβ := (src.crossing_xi_iff a m.finite_laplace hβ).1 (m.crossing hβ)

/-! ### The sum rule -/

lemma SourceCrossingMeasure.restrict_Ici_eq {src : ShiftSource} {a : ℝ} (m : SourceCrossingMeasure src a) :
    m.ν.restrict (Ici 0) = m.ν := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff, show {t : ℝ | t ∉ Ici 0} = Iio 0 by ext t; simp]
  exact m.supp_nonneg

/-- **`pmix:crossing` (a)** (Lemma PM.3 (a), the mixed crossing sum rule), for an atomic common source at a charge
with the floor.  For a mixed crossing measure `ν` and a test function `g ∈ \overline{\mathcal A}_{w,\mathrm{mix}}`:
(1) if `g ≥ 0` on a terminal interval then `g` is `ν`-integrable and `g_vac + ∫ g dν ≤ 0`;
(2) if `|g(t)| ≤ C (1+t)^{-q} e^{-4π √(a t)}` with `q > (w+1)/2` then `g` is `ν`-integrable and
`g_vac + ∫ g dν = 0`;
(3) if `ν` is carried by `[τ, ∞)`, `g ≥ 0` on `[τ, ∞)` and `g_vac ≥ 0` then `g_vac = 0` and `g = 0` `ν`-a.e. -/
theorem pmix_crossing_a {src : ShiftSource} {F : FloorData src} {a : ℝ} (h : F.At a)
    (meas : SourceCrossingMeasure src a) {g : ℝ → ℝ} (hg : TestClass src a g) :
    ((∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 ≤ g t) →
      Integrable g meas.ν ∧ src.gVac a g + ∫ t, g t ∂meas.ν ≤ 0) ∧
    (∀ {q C : ℝ}, (src.w + 1 : ℝ) / 2 < q → 0 ≤ C →
      (∀ t : ℝ, 0 ≤ t → |g t| ≤ C * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) →
      Integrable g meas.ν ∧ src.gVac a g + ∫ t, g t ∂meas.ν = 0) ∧
    (∀ {τ : ℝ}, meas.ν (Iio τ) = 0 → (∀ t : ℝ, τ ≤ t → 0 ≤ g t) → 0 ≤ src.gVac a g →
      src.gVac a g = 0 ∧ ∀ᵐ t ∂meas.ν, g t = 0) := by
  have hcb := h.crossingBounds
  have hr := meas.restrict_Ici_eq
  have part1 : ∀ {T : ℝ}, (∀ t : ℝ, T ≤ t → 0 ≤ g t) →
      Integrable g meas.ν ∧ src.gVac a g + ∫ t, g t ∂meas.ν ≤ 0 := by
    intro T hT
    obtain ⟨hi, hle⟩ := lemma_fwX_one_sided_src src hcb h.pos meas hg hT
    rw [hr] at hle
    exact ⟨by simpa [IntegrableOn, hr] using hi, hle⟩
  refine ⟨fun ⟨T, hT⟩ => part1 hT, fun {q C} hq hC hdecay => ?_, fun {τ} hτ hgτ hvac => ?_⟩
  · obtain ⟨hi, heq⟩ := lemma_fwX_equality_src src hcb h.pos meas hg hq hC hdecay
    rw [hr] at heq
    exact ⟨by simpa [IntegrableOn, hr] using hi, heq⟩
  · obtain ⟨hint, hle⟩ := part1 hgτ
    have hae : ∀ᵐ t ∂meas.ν, τ ≤ t := by
      rw [ae_iff, show {t : ℝ | ¬ τ ≤ t} = Iio τ by ext t; simp]
      exact hτ
    have hnn : 0 ≤ᵐ[meas.ν] g := hae.mono fun t ht => hgτ t ht
    have hI : 0 ≤ ∫ t, g t ∂meas.ν := integral_nonneg_of_ae hnn
    have hI0 : ∫ t, g t ∂meas.ν = 0 := by linarith
    refine ⟨by linarith, ?_⟩
    exact ((integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hI0).mono fun t ht => ht

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_crossing_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_crossing_a

/-- **Exclusion** (`pmix:crossing` (a), last assertion): if `g ∈ \overline{\mathcal A}_{w,\mathrm{mix}}` satisfies
`g ≥ 0` on `[T, ∞)` and `g_vac > 0`, no mixed crossing measure is carried by `[T, ∞)`. -/
theorem pmix_crossing_a_exclusion {src : ShiftSource} {F : FloorData src} {a : ℝ} (h : F.At a)
    (meas : SourceCrossingMeasure src a) {g : ℝ → ℝ} (hg : TestClass src a g) {T : ℝ}
    (hT : ∀ t : ℝ, T ≤ t → 0 ≤ g t) (hvac : 0 < src.gVac a g) : ¬ meas.ν (Iio T) = 0 := by
  intro hν
  obtain ⟨hint, hle⟩ := (pmix_crossing_a h meas hg).1 ⟨T, hT⟩
  have hae : ∀ᵐ t ∂meas.ν, T ≤ t := by
    rw [ae_iff, show {t : ℝ | ¬ T ≤ t} = Iio T by ext t; simp]
    exact hν
  have hI : 0 ≤ ∫ t, g t ∂meas.ν := integral_nonneg_of_ae (hae.mono fun t ht => hT t ht)
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_crossing_a_exclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_crossing_a_exclusion

end FormalResearch.ModularBootstrap.Mixtures
