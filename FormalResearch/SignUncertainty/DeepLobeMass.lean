module

public import FormalResearch.SignUncertainty.DeepLobeRegionI

/-!
# Deep lobe mass (`lem:radial-compactness`, first field)

`deep_lobe_mass_thm`: for `c ≥ 56`, every Hankel eigenfunction `f` with `ε = ±1` and every `R ≥ 1` with
`R c^{1/3} < c/π²`,
`∫_0^{c/π² - R c^{1/3}} |f| ρ₀ ≤ 8 M[f] (e^{-5R^{3/2}} + e^{-c/25})`.
It splits the interval at `c(1/π² - 1/48)`: region II (`deepLobe_regionII`) below, region I
(`deepLobe_regionI`) above.
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

theorem deepLobe_regionI {c ε : ℝ} (hc : 56 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {R : ℝ} (hR : 1 ≤ R) :
    ∫ Δ in Ioo (c * (1 / Real.pi ^ 2 - 1 / 48)) (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ)),
        |f Δ| * hankelRho0 c Δ ≤ 8 * hankelMass c f * Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) := by
  have hc0 : 0 < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 48 := by nlinarith [Real.pi_lt_d2]
  set t : ℝ := c ^ (1 / 3 : ℝ) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hc0 _
  have htc : t ^ 3 = c := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  set M := hankelMass c f with hM
  have hM0 : 0 ≤ M := hankelMass_nonneg hc0 f
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  set U : ℝ := c / Real.pi ^ 2 - R * t with hU
  have hΔ₁pos : 0 < Δ₁ := by
    rw [hΔ₁]; refine mul_pos hc0 ?_
    rw [sub_pos, div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  by_cases hlt : Δ₁ < U
  · set P : ℝ := c / Real.pi ^ 2 with hP
    set K : ℝ := (80 * M / t) * Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) with hK
    have hK0 : 0 ≤ K := by positivity
    have hLint : IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioo Δ₁ U) :=
      (abs_mul_rho0_integrableOn hc0 hf.int).mono_set
        (fun x hx => lt_trans hΔ₁pos hx.1)
    have hGc : Continuous fun Δ : ℝ => K * Real.exp (-(10 * (P - Δ) / t)) := by fun_prop
    have hmono : ∫ Δ in Ioo Δ₁ U, |f Δ| * hankelRho0 c Δ ≤
        ∫ Δ in Ioo Δ₁ U, K * Real.exp (-(10 * (P - Δ) / t)) :=
      setIntegral_mono_on hLint (hGc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
        (fun Δ hΔ => regionI_pointwise hc hf hε ht0 htc hR hΔ.1 hΔ.2)
    refine hmono.trans ?_
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlt.le,
      intervalIntegral.integral_const_mul]
    have hd : ∀ Δ : ℝ, HasDerivAt (fun Δ => (t / 10) * Real.exp (-(10 * (P - Δ) / t)))
        (Real.exp (-(10 * (P - Δ) / t))) Δ := by
      intro Δ
      have h1 : HasDerivAt (fun Δ : ℝ => -(10 * (P - Δ) / t)) (10 / t) Δ := by
        have := (((hasDerivAt_id Δ).const_sub P).const_mul 10).div_const t |>.neg
        exact this.congr_deriv (by ring)
      have := (h1.exp).const_mul (t / 10)
      convert this using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun Δ _ => hd Δ)
      ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
    have : (t / 10) * Real.exp (-(10 * (P - U) / t)) - (t / 10) * Real.exp (-(10 * (P - Δ₁) / t)) ≤ t / 10 := by
      have h1 : Real.exp (-(10 * (P - U) / t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 10 * (P - U) / t := by
          have hPU : P - U = R * t := by rw [hU]; ring
          rw [hPU]; positivity
        linarith
      nlinarith [Real.exp_pos (-(10 * (P - Δ₁) / t)), Real.exp_pos (-(10 * (P - U) / t))]
    calc K * ((t / 10) * Real.exp (-(10 * (P - U) / t)) - (t / 10) * Real.exp (-(10 * (P - Δ₁) / t)))
        ≤ K * (t / 10) := mul_le_mul_of_nonneg_left this hK0
      _ = 8 * M * Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) := by rw [hK]; field_simp; ring
  · rw [Ioo_eq_empty hlt, Measure.restrict_empty, integral_zero_measure]
    positivity

theorem deep_lobe_mass_thm {c ε : ℝ} (hc : 56 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {R : ℝ} (hR : 1 ≤ R) :
    ∫ Δ in Ioo (0 : ℝ) (c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ)), |f Δ| * hankelRho0 c Δ ≤
      8 * hankelMass c f * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) := by
  have hc0 : 0 < c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < 48 := by nlinarith [Real.pi_lt_d2]
  set Δ₁ : ℝ := c * (1 / Real.pi ^ 2 - 1 / 48) with hΔ₁
  set U : ℝ := c / Real.pi ^ 2 - R * c ^ (1 / 3 : ℝ) with hU
  have hΔ₁pos : 0 < Δ₁ := by
    rw [hΔ₁]; refine mul_pos hc0 ?_
    rw [sub_pos, div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hint : IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioi 0) :=
    abs_mul_rho0_integrableOn hc0 hf.int
  have hsub : Ioo (0 : ℝ) U ⊆ Ioc 0 Δ₁ ∪ Ioo Δ₁ U := by
    intro x hx
    by_cases h : x ≤ Δ₁
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨not_le.mp h, hx.2⟩
  have hunion : Ioc 0 Δ₁ ∪ Ioo Δ₁ U ⊆ Ioi 0 := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact lt_trans hΔ₁pos hx.1
  have hI1 : IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioc 0 Δ₁) :=
    hint.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioo Δ₁ U) :=
    hint.mono_set (fun x hx => lt_trans hΔ₁pos hx.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 Δ₁ ∪ Ioo Δ₁ U)] fun Δ => |f Δ| * hankelRho0 c Δ := by
    refine (ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioo)).mpr (ae_of_all _ fun Δ hΔ => ?_)
    exact mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 (le_of_lt (hunion hΔ)))
  have hdisj : Disjoint (Ioc (0 : ℝ) Δ₁) (Ioo Δ₁ U) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  calc ∫ Δ in Ioo (0 : ℝ) U, |f Δ| * hankelRho0 c Δ
      ≤ ∫ Δ in Ioc 0 Δ₁ ∪ Ioo Δ₁ U, |f Δ| * hankelRho0 c Δ :=
        setIntegral_mono_set (hI1.union hI2) hnn (Eventually.of_forall hsub)
    _ = (∫ Δ in Ioc 0 Δ₁, |f Δ| * hankelRho0 c Δ) + ∫ Δ in Ioo Δ₁ U, |f Δ| * hankelRho0 c Δ :=
        setIntegral_union hdisj measurableSet_Ioo hI1 hI2
    _ ≤ 8 * hankelMass c f * Real.exp (-(1 / 25 * c)) + 8 * hankelMass c f * Real.exp (-(5 * R ^ ((3 : ℝ) / 2))) := by
        refine add_le_add ?_ (deepLobe_regionI hc hf hε hR)
        have := deepLobe_regionII hc hf hε
        rwa [show -(c / 25) = -(1 / 25 * c) by ring] at this
    _ = 8 * hankelMass c f * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) := by
        rw [show -(1 / 25) * c = -(1 / 25 * c) by ring, show -5 * R ^ (3 / 2 : ℝ) = -(5 * R ^ ((3 : ℝ) / 2)) by ring]
        ring

/-- info: 'FormalResearch.SignUncertainty.deepLobe_regionI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deepLobe_regionI

/-- info: 'FormalResearch.SignUncertainty.deep_lobe_mass_thm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deep_lobe_mass_thm

end FormalResearch.SignUncertainty
