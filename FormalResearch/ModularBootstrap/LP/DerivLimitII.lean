module

public import FormalResearch.ModularBootstrap.LP.OddFunctional

/-!
# The infinite-order derivative limit, part (i) (`ds:LP`(i)), direction (a) ⇒ (b)

`CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem LP (`ds:LP`), (i): for a closed
`X ⊂ [T₀, ∞)`, `T₀ > 0`, if no finite odd-Laguerre test is feasible on `X`, there is a crossing measure
carried by `X` (`exists_crossingMeasure_of_not_oddFeasible`).

Proof (`dual_spectrum_limit.tex`, Section `dsl:LPproof`): the reference functional `𝓛` on
`⋃ O_N ∘ t` (`exists_functional`) is positive on `X`; the positive ray lemma `positive_ray` supplies the
majorant `p₀`; `poly_compact` gives a Radon measure `μ` on `X` with an exponential moment and the
odd moments of `μ_C`; `tilt_crossing` (`ds:cay`) turns `ν = e^{2πt} μ` into a solution of the crossing
identity near `β = 1`; `ds_cont` spreads it to every `β > 0`, and the Laplace identity for `ρ_C`
(`integral_xiW_expTilt_ref`) identifies the right-hand side.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open FormalResearch.ModularBootstrap.Crossing

namespace FormalResearch.ModularBootstrap.LP

lemma integrable_exp_mono {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) {ε ε' : ℝ}
    (h : Integrable (fun s => Real.exp (ε * s)) μ) (hle : ε' ≤ ε) :
    Integrable (fun s => Real.exp (ε' * s)) μ := by
  have hae : ∀ᵐ t ∂μ, 0 ≤ t := by
    have : ∀ᵐ t ∂μ, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hμ
    filter_upwards [this] with t ht using not_lt.1 ht
  refine Integrable.mono' h (by fun_prop : Continuous fun s : ℝ => Real.exp (ε' * s)).aestronglyMeasurable ?_
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by nlinarith only [ht, hle])

section AB

variable {prob : FixedWeightProblem} {a : ℝ}

/-- **`ds:LP`(i), (a) ⇒ (b)**. -/
theorem exists_crossingMeasure_of_not_oddFeasible (ha : prob.totalShift ≤ a) {T₀ : ℝ} (hT₀ : 0 < T₀)
    {X : Set ℝ} (hXc : IsClosed X) (hX : X ⊆ Ici T₀)
    (hno : ∀ N p, ¬ OddFeasible prob a N X p) :
    ∃ meas : AdmissibleCrossingMeasure prob a, meas.ν Xᶜ = 0 := by
  have hw : 0 < (prob.w : ℝ) := by exact_mod_cast prob.hw
  obtain ⟨t, htx⟩ : ∃ t : C(X, ℝ), ∀ x : X, t x = x.1 :=
    ⟨⟨fun x : X => x.1, continuous_subtype_val⟩, fun x => rfl⟩
  obtain ⟨L, hLf, hLpos⟩ := exists_functional ha hno t htx
  -- the majorant `p₀ ≥ 1` on the ray
  obtain ⟨N₀, p₀, hp₀, hp₀1⟩ := positive_ray hw hT₀
  obtain ⟨f₀, hf₀, hf₀p⟩ := exists_mem_OC_of_mem_oddSpan hp₀
  have hmaj : ∃ (N : ℕ) (f : C(ℝ, ℝ)) (η : ℝ), Odd N ∧ f ∈ OC (prob.w : ℝ) N ∧ 0 < η ∧
      ∀ x : X, η ≤ f (t x) :=
    ⟨2 * N₀ + 1, f₀, 1, ⟨N₀, rfl⟩, OC_mono _ (by omega) hf₀, one_pos, fun x => by
      rw [htx x, show f₀ x.1 = p₀ x.1 from congrFun hf₀p x.1]
      exact hp₀1 _ (hX x.2)⟩
  have hT := oddV_hyp hw hT₀.le (t := t) (fun x => by rw [htx x]; exact hX x.2)
    (by
      have : (t : X → ℝ) = Subtype.val := funext htx
      rw [this]; exact hXc.isClosedEmbedding_subtypeVal.isProperMap) hmaj
  have hodd : RefOdd (lagPC (prob.w : ℝ)) t (oddV (prob.w : ℝ) t) (refMeas prob a) L := by
    intro v j hj hvj
    have hmem : lagPC (prob.w : ℝ) j ∈ OCall (prob.w : ℝ) := Submodule.subset_span ⟨j, hj, rfl⟩
    have := hLf _ hmem
    have hv : v = ⟨compT t (lagPC (prob.w : ℝ) j), compT_mem_polyUnion _ hmem⟩ :=
      Subtype.ext hvj
    rw [hv, this]
  have : LocallyCompactSpace X := hXc.locallyCompactSpace
  obtain ⟨μ, hreg, hpoly, hrep, ε, hε, hexp⟩ := poly_compact hT (refMeas prob a) refMeas_Iio
    (integrable_exp_ref_pi ha) L hLpos hodd
  -- push forward to `ℝ`
  have hmeas : Measurable (fun x : X => x.1) := measurable_subtype_coe
  set μ₁ : Measure ℝ := μ.map (fun x : X => x.1) with hμ₁
  have hμ₁X : μ₁ Xᶜ = 0 := by
    rw [hμ₁, Measure.map_apply hmeas (hXc.measurableSet.compl)]
    have : (fun x : X => x.1) ⁻¹' Xᶜ = ∅ := by ext x; simp
    rw [this, measure_empty]
  have hμ₁T : μ₁ (Iio T₀) = 0 := by
    rw [hμ₁, Measure.map_apply hmeas measurableSet_Iio]
    have : (fun x : X => x.1) ⁻¹' Iio T₀ = ∅ := by ext x; simp [not_lt.2 (hX x.2)]
    rw [this, measure_empty]
  have hμ₁0 : μ₁ (Iio 0) = 0 := measure_mono_null (Iio_subset_Iio hT₀.le) hμ₁T
  have hexp₁ : Integrable (fun s => Real.exp (ε * s)) μ₁ := by
    rw [hμ₁, integrable_map_measure (by fun_prop) hmeas.aemeasurable]
    refine hexp.congr (Eventually.of_forall fun x => ?_)
    simp [htx x]
  have hodd₁ : ∀ k, Odd k → ∫ s, lagP (prob.w : ℝ) k s ∂μ₁ = ∫ s, lagP (prob.w : ℝ) k s ∂refMeas prob a := by
    intro k hk
    rw [hμ₁, integral_map hmeas.aemeasurable (continuous_lagP _ k).aestronglyMeasurable]
    have h1 := hrep ⟨pc (lagPC (prob.w : ℝ)) k t, hT.pc_mem hk⟩
    rw [hodd ⟨pc (lagPC (prob.w : ℝ)) k t, hT.pc_mem hk⟩ k hk rfl] at h1
    have h2 : ∫ x : X, lagP (prob.w : ℝ) k x.1 ∂μ = ∫ x : X, (pc (lagPC (prob.w : ℝ)) k t) x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by simp [htx x])
    rw [h2]; exact h1
  -- the tilted measure and the crossing identity near `β = 1`
  set ε' : ℝ := min ε π with hε'
  have hε'0 : 0 < ε' := lt_min hε Real.pi_pos
  obtain ⟨θ, hθ0, hθ1, hf, hf', hcr⟩ := tilt_crossing hw hμ₁0 (refMeas_Iio (prob := prob) (a := a)) hε'0
    (integrable_exp_mono hμ₁0 hexp₁ (min_le_left _ _))
    (integrable_exp_ref ha (c := ε') (by linarith [min_le_right ε π, Real.pi_pos]))
    hodd₁
  set ν : Measure ℝ := expTilt μ₁ with hν
  have hνIio : ν (Iio 0) = 0 := expTilt_apply_eq_zero hμ₁0
  have hs0 := sTheta_pos hθ0 hθ1
  have hs1 : sTheta θ < 1 := by
    unfold sTheta; rw [div_lt_one (by linarith)]; linarith
  have hcross : ∀ β, sTheta θ < β → β < 1 / sTheta θ →
      lapZ ν β + srcV prob a β = β ^ (-(prob.w : ℝ)) * (lapZ ν (1 / β) + srcV prob a (1 / β)) := by
    intro β h1 h2
    have hβ0 : 0 < β := hs0.trans h1
    have hinv : sTheta θ < 1 / β := by
      rw [lt_div_iff₀ hβ0]; rw [lt_div_iff₀ hs0] at h2; linarith
    have h := hcr β h1 h2
    rw [integral_xiW_lapZ (hf.mono hνIio h1.le) (hf.mono hνIio hinv.le),
      integral_xiW_expTilt_ref ha hβ0] at h
    linarith
  obtain ⟨hall, hid⟩ := ds_cont (analyticOnNhd_srcV prob a) hνIio hs0 hs1 hf hcross
  refine ⟨⟨ν, hνIio, fun {β} hβ => ?_, fun {β} hβ => ?_⟩, ?_⟩
  · exact (hall β hβ).integrableOn
  · have hrestr : ν.restrict (Ici 0) = ν := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hνIio
      filter_upwards [this] with t ht using not_lt.1 ht
    rw [hrestr, ← integral_xiW_expTilt_ref' ha β]
    show ∫ t, xiW (prob.w : ℝ) β t ∂ν = _
    rw [integral_xiW_lapZ (hall β hβ) (hall (1 / β) (by positivity)), integral_xiW_expTilt_ref ha hβ]
    have := hid β hβ
    linarith
  · show ν Xᶜ = 0
    exact expTilt_apply_eq_zero hμ₁X

end AB

end FormalResearch.ModularBootstrap.LP
