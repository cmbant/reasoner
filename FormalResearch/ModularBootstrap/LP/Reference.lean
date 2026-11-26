module

public import FormalResearch.ModularBootstrap.LP.PositiveRay
public import FormalResearch.ModularBootstrap.Crossing.Setup

/-!
# The Cardy reference measure `μ_C = e^{-2πt} ρ_C dt` and the standing source

`CFT/modular_bootstrap/paper/dual_spectrum.tex`, Section `ds:LPsec`: `μ_C := e^{-2πt} ρ_C dt` (on
`(0, ∞)`) with `ρ_C = 2π V` the Cardy density of `Crossing.Setup`, `𝓛(p) := ∫ p dμ_C`, and
`(e^{-2πt} p)_vac = -𝓛(p)` (`gVac_expPoly`).  With the source
`v(β) = e^{2πaβ} Q(e^{-2πβ})` (`srcV`, real analytic) the Laplace identity gives
`∫ Ξ_β ρ_C dt = β^{-w} v(1/β) - v(β)` (`integral_xiW_expTilt_ref`).  Also: `μ_C` has an `e^{ct}`
moment for every `c < 2π`, so every `P_k` is `μ_C`-integrable (`integrable_oddSpan_ref`).
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open FormalResearch.ModularBootstrap.Crossing

namespace FormalResearch.ModularBootstrap.LP

variable (prob : FixedWeightProblem) (a : ℝ)

/-- `μ_C = e^{-2πt} ρ_C(t) dt` on `(0, ∞)`. -/
noncomputable def refMeas : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (Real.exp (-2 * π * t) * prob.cardyDensity a t))

lemma measurable_refDensity :
    Measurable (fun t => ENNReal.ofReal (Real.exp (-2 * π * t) * prob.cardyDensity a t)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  have : Continuous fun t => Real.exp (-2 * π * t) * prob.cardyDensity a t := by
    unfold FixedWeightProblem.cardyDensity
    exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * π * t)).mul
      (continuous_const.mul (continuous_cardyV prob a))
  exact this.measurable

variable {prob a}

lemma refMeas_Iio : refMeas prob a (Iio 0) = 0 := by
  unfold refMeas
  rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have : (Iio (0 : ℝ)) ∩ Ioi 0 = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun h => h.le
  rw [this]; simp

lemma refMeas_ae_nonneg : ∀ᵐ t ∂(refMeas prob a), 0 ≤ t := by
  have : ∀ᵐ t ∂(refMeas prob a), t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 refMeas_Iio
  filter_upwards [this] with t ht using not_lt.1 ht

lemma refDensity_nonneg (ha : prob.totalShift ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Real.exp (-2 * π * t) * prob.cardyDensity a t := by
  unfold FixedWeightProblem.cardyDensity
  have := prob.cardyV_nonneg ha ht
  have := Real.pi_pos
  positivity

lemma integral_refMeas (ha : prob.totalShift ≤ a) (g : ℝ → ℝ) :
    ∫ t, g t ∂refMeas prob a =
      ∫ t in Ioi 0, Real.exp (-2 * π * t) * prob.cardyDensity a t * g t := by
  unfold refMeas
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_refDensity prob a)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (refDensity_nonneg ha (mem_Ioi.1 ht).le)]

lemma integrable_refMeas_iff (ha : prob.totalShift ≤ a) (g : ℝ → ℝ) :
    Integrable g (refMeas prob a) ↔
      IntegrableOn (fun t => Real.exp (-2 * π * t) * prob.cardyDensity a t * g t) (Ioi 0) := by
  unfold refMeas
  rw [integrable_withDensity_iff_integrable_smul' (measurable_refDensity prob a)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (refDensity_nonneg ha (mem_Ioi.1 ht).le)]

/-- `μ_C` has an `e^{ct}` moment for every `c < 2π`. -/
lemma integrable_exp_ref (ha : prob.totalShift ≤ a) {c : ℝ} (hc : c < 2 * π) :
    Integrable (fun t => Real.exp (c * t)) (refMeas prob a) := by
  rw [integrable_refMeas_iff ha]
  have hβ : 0 < (2 * π - c) / (2 * π) := div_pos (by linarith) (by positivity)
  have h := (prob.cardyV_laplace a hβ).1
  have h2 : IntegrableOn (fun t => 2 * π * (prob.cardyV a t *
      Real.exp (-2 * π * ((2 * π - c) / (2 * π)) * t))) (Ioi 0) := h.const_mul (2 * π)
  refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).1 h2
  unfold FixedWeightProblem.cardyDensity
  have e : Real.exp (-2 * π * t) * Real.exp (c * t) =
      Real.exp (-2 * π * ((2 * π - c) / (2 * π)) * t) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have : Real.exp (-2 * π * t) * (2 * π * prob.cardyV a t) * Real.exp (c * t) =
      2 * π * (prob.cardyV a t * (Real.exp (-2 * π * t) * Real.exp (c * t))) := by ring
  rw [this, e]

lemma integrable_exp_ref_pi (ha : prob.totalShift ≤ a) :
    Integrable (fun t => Real.exp (π * t)) (refMeas prob a) :=
  integrable_exp_ref ha (by linarith [Real.pi_pos])

/-- Every element of `O_N` is `μ_C`-integrable. -/
lemma integrable_oddSpan_ref (ha : prob.totalShift ≤ a) {N : ℕ} {p : ℝ → ℝ}
    (hp : p ∈ oddSpan (prob.w : ℝ) N) : Integrable p (refMeas prob a) := by
  have hw : 0 < (prob.w : ℝ) := by exact_mod_cast prob.hw
  refine Submodule.span_induction (p := fun p _ => Integrable p (refMeas prob a)) ?_ ?_ ?_ ?_ hp
  · rintro f ⟨k, hk, -, rfl⟩
    refine Integrable.mono' ((integrable_exp_ref_pi ha).const_mul ((2 * momM ((1 + (prob.w : ℝ)) / π) * k) ^ k))
      (continuous_lagP _ k).aestronglyMeasurable ?_
    filter_upwards [refMeas_ae_nonneg (prob := prob) (a := a)] with t ht
    rw [Real.norm_eq_abs]
    exact (lagP_oddFam hw).abs_le_exp hk ht
  · exact integrable_zero _ _ _
  · intro f g _ _ hf hg; exact hf.add hg
  · intro c f _ hf; exact hf.smul c

/-- `(e^{-2πt} p)_vac = -𝓛(p)` with `𝓛(p) = ∫ p dμ_C`. -/
lemma gVac_expPoly (ha : prob.totalShift ≤ a) (p : ℝ → ℝ) :
    prob.gVac a (fun t => Real.exp (-2 * π * t) * p t) = - ∫ t, p t ∂refMeas prob a := by
  rw [integral_refMeas ha]
  unfold FixedWeightProblem.gVac FixedWeightProblem.cardyDensity
  have : ∀ t : ℝ, Real.exp (-2 * π * t) * p t * prob.cardyV a t =
      (Real.exp (-2 * π * t) * (2 * π * prob.cardyV a t) * p t) / (2 * π) := fun t => by
    field_simp
  simp_rw [this]
  rw [integral_div]
  field_simp

/-- The standing source `v(β) = e^{2πaβ} Q(e^{-2πβ})`. -/
noncomputable def srcV (prob : FixedWeightProblem) (a β : ℝ) : ℝ :=
  Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))

lemma srcV_eq (prob : FixedWeightProblem) (a β : ℝ) :
    srcV prob a β = Real.exp (2 * π * a * β) * ∏ l : Fin prob.m, (1 - Real.exp (-2 * π * β * prob.μ l)) := by
  unfold srcV FixedWeightProblem.nullPoly
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← Real.exp_mul]

/-- `v` is real analytic (it is entire). -/
lemma analyticOnNhd_srcV (prob : FixedWeightProblem) (a : ℝ) : AnalyticOnNhd ℝ (srcV prob a) (Ioi 0) := by
  intro β _
  have h : AnalyticAt ℝ (fun x : ℝ => Real.exp (2 * π * a * x) *
      ∏ l : Fin prob.m, (1 - Real.exp (-2 * π * x * prob.μ l))) β := by
    refine (analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id)).mul ?_
    refine Finset.analyticAt_fun_prod _ fun l _ => ?_
    exact analyticAt_const.sub (analyticAt_rexp.comp
      ((analyticAt_const.mul analyticAt_id).mul analyticAt_const))
  have e : srcV prob a = fun x => Real.exp (2 * π * a * x) *
      ∏ l : Fin prob.m, (1 - Real.exp (-2 * π * x * prob.μ l)) := funext fun x => srcV_eq prob a x
  rw [e]; exact h

/-- `∫ Ξ_β d(e^{2πt} μ_C) = ∫_{(0,∞)} Ξ_β ρ_C dt` (the right-hand side of the crossing equation). -/
lemma integral_xiW_expTilt_ref' (ha : prob.totalShift ≤ a) (β : ℝ) :
    ∫ t, xiW (prob.w : ℝ) β t ∂expTilt (refMeas prob a) =
      ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t := by
  rw [integral_expTilt, integral_refMeas ha]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have : Real.exp (-2 * π * t) * Real.exp (2 * π * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc Real.exp (-2 * π * t) * prob.cardyDensity a t * (Real.exp (2 * π * t) * xiW (prob.w : ℝ) β t)
      = (Real.exp (-2 * π * t) * Real.exp (2 * π * t)) * (prob.cardyDensity a t * xiW (prob.w : ℝ) β t) := by ring
    _ = thermalDiff prob.w β t * prob.cardyDensity a t := by
        rw [this]; unfold thermalDiff xiW; ring

/-- `∫ Ξ_β d(e^{2πt} μ_C) = β^{-w} v(1/β) - v(β)`. -/
lemma integral_xiW_expTilt_ref (ha : prob.totalShift ≤ a) {β : ℝ} (hβ : 0 < β) :
    ∫ t, xiW (prob.w : ℝ) β t ∂expTilt (refMeas prob a) =
      β ^ (-(prob.w : ℝ)) * srcV prob a (1 / β) - srcV prob a β := by
  rw [integral_xiW_expTilt_ref' ha]
  have h1 : ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t =
      -(prob.gVac a (thermalDiff prob.w β)) := by
    unfold FixedWeightProblem.gVac FixedWeightProblem.cardyDensity
    have : ∀ t : ℝ, thermalDiff prob.w β t * (2 * π * prob.cardyV a t) =
        2 * π * (thermalDiff prob.w β t * prob.cardyV a t) := fun t => by ring
    simp_rw [this]
    rw [integral_const_mul]; ring
  rw [h1, prob.gVac_thermalDiff a hβ]
  unfold srcV
  have e1 : Real.exp (2 * π * a * (1 / β)) = Real.exp (2 * π * a / β) := by congr 1; ring
  have e2 : Real.exp (-2 * π * (1 / β)) = Real.exp (-2 * π / β) := by congr 1; ring
  rw [e1, e2]
  ring

end FormalResearch.ModularBootstrap.LP
