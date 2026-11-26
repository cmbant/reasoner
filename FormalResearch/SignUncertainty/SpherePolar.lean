module

public import FormalResearch.SignUncertainty.SphereInvariance

/-!
# Polar coordinates for integrable functions on `ℝ^{n+1}`

For `h` integrable on `ℝ^{n+1}`: `∫ h = ∫_{r>0} r^n ∫_{ω ∈ S^n} h(r ω) dω dr` (`integral_polar`), with the
radial integral integrable (`integrableOn_polar`). General (non-radial) version of
`MeasureTheory.integral_fun_norm_addHaar`, from `measurePreserving_homeomorphUnitSphereProd`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace Pointwise

namespace FormalResearch.SignUncertainty

variable {n : ℕ}

lemma finrank_euclSp_sub_one (n : ℕ) : Module.finrank ℝ (EuclSp (n + 1)) - 1 = n := by
  simp

/-- Polar coordinates on the product `S^n × (0,∞)` with the measure `σ × r^n dr`. -/
theorem polar_aux {h : EuclSp (n + 1) → ℂ} (hh : Integrable h) :
    Integrable (fun p : USph (n + 1) × Ioi (0 : ℝ) => h ((p.2 : ℝ) • (p.1 : EuclSp (n + 1))))
        ((sphMeas (n + 1)).prod (Measure.volumeIoiPow n)) ∧
      ∫ x, h x = ∫ p : USph (n + 1) × Ioi (0 : ℝ), h ((p.2 : ℝ) • (p.1 : EuclSp (n + 1)))
        ∂((sphMeas (n + 1)).prod (Measure.volumeIoiPow n)) := by
  unfold sphMeas
  have hmp := (volume : Measure (EuclSp (n + 1))).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclSp_sub_one] at hmp
  have hemb := (homeomorphUnitSphereProd (EuclSp (n + 1))).measurableEmbedding
  set φ := homeomorphUnitSphereProd (EuclSp (n + 1)) with hφ
  set g : USph (n + 1) × Ioi (0 : ℝ) → ℂ := fun p => h ((p.2 : ℝ) • (p.1 : EuclSp (n + 1))) with hg
  have hgφ : ∀ x : ({0}ᶜ : Set (EuclSp (n + 1))), g (φ x) = h x := by
    intro x
    have h1 : ∀ p, g p = h ((φ.symm p : ({0}ᶜ : Set (EuclSp (n + 1))) ) : EuclSp (n + 1)) := by
      intro p
      simp [hg, hφ, homeomorphUnitSphereProd_symm_apply_coe]
    rw [h1, φ.symm_apply_apply]
  have hint : Integrable (fun x : ({0}ᶜ : Set (EuclSp (n + 1))) => h x)
      (Measure.comap (↑) (volume : Measure (EuclSp (n + 1)))) := by
    have := (integrableOn_iff_comap_subtypeVal (μ := (volume : Measure (EuclSp (n + 1))))
      (s := ({0}ᶜ : Set (EuclSp (n + 1)))) (f := h) (measurableSet_singleton _).compl).1
      hh.integrableOn
    exact this
  constructor
  · rw [← hmp.integrable_comp_emb hemb]
    refine hint.congr (Eventually.of_forall fun x => ?_)
    exact (hgφ x).symm
  · rw [← hmp.integral_comp hemb g]
    simp_rw [hgφ]
    rw [integral_subtype_comap (measurableSet_singleton _).compl h,
      restrict_compl_singleton]

lemma integral_volumeIoiPow (n : ℕ) (G : ℝ → ℂ) :
    ∫ r : Ioi (0 : ℝ), G r ∂(Measure.volumeIoiPow n) = ∫ r in Ioi (0 : ℝ), (r ^ n : ℝ) • G r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (by exact (measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ n) • G a]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]

lemma integrable_volumeIoiPow_iff (n : ℕ) (G : ℝ → ℂ) :
    Integrable (fun r : Ioi (0 : ℝ) => G r) (Measure.volumeIoiPow n) ↔
      IntegrableOn (fun r : ℝ => (r ^ n : ℝ) • G r) (Ioi 0) := by
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi, Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul']
  · refine integrable_congr (Eventually.of_forall ?_)
    rintro ⟨x, hx : 0 < x⟩
    simp (disch := positivity) [ENNReal.toReal_ofReal]
  · fun_prop
  · simp

/-- **Polar coordinates for integrable functions**: `∫ h = ∫_{r>0} r^n ∫_{S^n} h(rω) dω dr`, and the
radial integral is integrable. -/
theorem integral_polar {h : EuclSp (n + 1) → ℂ} (hh : Integrable h) :
    ∫ x, h x = ∫ r in Ioi (0 : ℝ), (r ^ n : ℝ) •
        ∫ ω : USph (n + 1), h (r • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1) := by
  obtain ⟨hint, hI⟩ := polar_aux hh
  rw [hI, integral_prod_symm _ hint, integral_volumeIoiPow n
    (fun r => ∫ ω : USph (n + 1), h (r • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1))]

theorem integrableOn_polar {h : EuclSp (n + 1) → ℂ} (hh : Integrable h) :
    IntegrableOn (fun r : ℝ => (r ^ n : ℝ) •
        ∫ ω : USph (n + 1), h (r • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1)) (Ioi 0) := by
  obtain ⟨hint, -⟩ := polar_aux hh
  rw [← integrable_volumeIoiPow_iff n
    (fun r => ∫ ω : USph (n + 1), h (r • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1))]
  exact hint.integral_prod_right

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.integral_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_polar

end FormalResearch.SignUncertainty
