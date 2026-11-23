module

public import FormalResearch.SignUncertainty.HardyMellinIntertwiner
public import FormalResearch.Special.BesselPoisson

/-!
# The concrete Hankel kernel `K^{(c)}` (`fourier_mellin.tex`, `eq:hankel`)

For real `c > 1/2` the normalised Hankel kernel is
`K^{(c)}(Δ,s) = Γ(c) (2π√(Δ s))^{1-c} J_{c-1}(4π√(Δ s)) = φ_c(Δ s)`, `φ_c(w) = besselNorm (c-1) (4π√w)`
(`FormalResearch/Special/BesselNormalized.lean`; Poisson integral and `|φ_c| ≤ 1` in
`FormalResearch/Special/BesselPoisson.lean`).

* `hankelPhi`, `hankelKernel`: the kernel; `hankelPhi_zero`, `hankelPhi_continuous`,
  `abs_hankelPhi_le_one`; `hankelPhi_eq_besselJ` (agreement with `Complex.besselJ`).
* `besselHankelTransform c f Δ = ∫_0^∞ f(s) ρ₀(s) K^{(c)}(Δ,s) ds`, with
  `abs_besselHankelTransform_le : |𝓗_c f(Δ)| ≤ M[f]` and continuity.
* `HankelAntiderivFacts c`: the two analytic facts about `φ_c` that `HankelKernelData` still asks
  for beyond the closed fields (`φ_c(0) = 1`, continuity, boundedness): the `w^{c/2-1}`-weighted
  antiderivative of `φ_c` is bounded and tends to `Γ(c)/(2π)^c`, i.e. `∫_0^R J_{c-1} → 1`.
  These are **not proved** here; they are an explicit hypothesis.
* `hankelKernelData c hc hA`: the concrete `HankelKernelData c`, from `hA : HankelAntiderivFacts c`.
  The classes `𝒜_c^ε` (`IsRadialEigenfn`), feasibility (`IsFeasible`) and the thresholds `T_c^ε`
  (`hankelThreshold`) of `HardyMellinIntertwiner` are then the paper's, for this kernel.
* `hankelAntiderivFacts_fiveHalves`: non-vacuity, the hypothesis holds at `c = 5/2`
  (from the explicit `J_{3/2}` computation); `hankelPhi_fiveHalves` shows the earlier
  `phi52` is `hankelPhi (5/2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- `φ_c(w) = Γ(c) (2π√w)^{1-c} J_{c-1}(4π√w)`, the Hankel kernel as a function of `w = Δ s`. -/
noncomputable def hankelPhi (c w : ℝ) : ℝ := besselNorm (c - 1) (4 * π * √w)

/-- The kernel `K^{(c)}(Δ, s) = φ_c(Δ s)` of `eq:hankel`. -/
noncomputable def hankelKernel (c Δ s : ℝ) : ℝ := hankelPhi c (Δ * s)

@[simp] lemma hankelPhi_zero {c : ℝ} (hc : 0 < c) : hankelPhi c 0 = 1 := by
  unfold hankelPhi
  rw [Real.sqrt_zero, mul_zero]
  exact besselNorm_zero (by linarith)

lemma hankelKernel_zero_left {c : ℝ} (hc : 0 < c) (s : ℝ) : hankelKernel c 0 s = 1 := by
  simp [hankelKernel, hankelPhi_zero hc]

lemma hankelPhi_continuous (c : ℝ) : Continuous (hankelPhi c) :=
  (besselNorm_continuous (c - 1)).comp
    (continuous_const.mul Real.continuous_sqrt)

/-- `|K^{(c)}| ≤ 1` for `c > 1/2` (`fourier_mellin.tex`, after `eq:hankel`). -/
theorem abs_hankelPhi_le_one {c : ℝ} (hc : 1 / 2 < c) (w : ℝ) : |hankelPhi c w| ≤ 1 :=
  abs_besselNorm_le_one (by linarith) _

theorem abs_hankelKernel_le_one {c : ℝ} (hc : 1 / 2 < c) (Δ s : ℝ) : |hankelKernel c Δ s| ≤ 1 :=
  abs_hankelPhi_le_one hc _

/-- Agreement with `Complex.besselJ`: for `c > 0` and `w > 0`,
`φ_c(w) = Γ(c) (2π√w)^{1-c} J_{c-1}(4π√w)`. -/
theorem hankelPhi_eq_besselJ {c : ℝ} (hc : 0 < c) {w : ℝ} (hw : 0 < w) :
    (hankelPhi c w : ℂ) = (Real.Gamma c : ℂ) * (((2 * π * √w) ^ (1 - c) : ℝ) : ℂ) *
      Complex.besselJ ((c - 1 : ℝ) : ℂ) ((4 * π * √w : ℝ) : ℂ) := by
  have hx : 0 < 4 * π * √w := by positivity
  have := besselNorm_eq_gamma_mul_rpow_neg_besselJ (ν := c - 1) (by linarith) hx
  unfold hankelPhi
  rw [this]
  have h1 : c - 1 + 1 = c := by ring
  have h2 : 4 * π * √w / 2 = 2 * π * √w := by ring
  rw [h1, h2, show -(c - 1) = 1 - c by ring]

/-! ### The Hankel transform -/

/-- `(𝓗_c f)(Δ) = ∫_0^∞ f(s) ρ₀(s) K^{(c)}(Δ,s) ds` (`eq:hankel`). -/
noncomputable def besselHankelTransform (c : ℝ) (f : ℝ → ℝ) (Δ : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s * hankelKernel c Δ s

lemma besselHankelTransform_zero {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    besselHankelTransform c f 0 = ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s := by
  simp [besselHankelTransform, hankelKernel_zero_left hc]

/-- The Hankel integrand is integrable when `f ρ₀` is (`c > 1/2`). -/
lemma integrableOn_mul_hankelKernel {c : ℝ} (hc : 1 / 2 < c) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun s => f s * hankelRho0 c s) (Ioi 0)) (Δ : ℝ) :
    IntegrableOn (fun s => f s * hankelRho0 c s * hankelKernel c Δ s) (Ioi 0) := by
  refine (hint.norm).mono'
    (hint.aestronglyMeasurable.mul
      ((hankelPhi_continuous c).comp (continuous_const_mul Δ)).aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_hankelKernel_le_one hc _ _)

/-- **`|𝓗_c f| ≤ M[f]`.** -/
theorem abs_besselHankelTransform_le {c : ℝ} (hc : 1 / 2 < c) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun s => f s * hankelRho0 c s) (Ioi 0)) (Δ : ℝ) :
    |besselHankelTransform c f Δ| ≤ hankelMass c f := by
  unfold besselHankelTransform hankelMass
  · have hc0 : 0 < c := by linarith
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on ?_ (abs_mul_rho0_integrableOn hc0 hint)
      measurableSet_Ioi fun s (hs : 0 < s) => ?_
    · refine (abs_mul_rho0_integrableOn hc0 hint).mono' ?_ ?_
      · exact (hint.aestronglyMeasurable.mul
          ((hankelPhi_continuous c).comp (continuous_const_mul Δ)).aestronglyMeasurable).norm
      · refine (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_
        rw [norm_norm, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs.le)]
        exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hs.le))
          (abs_hankelKernel_le_one hc _ _)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs.le)]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hs.le))
        (abs_hankelKernel_le_one hc _ _)


/-- `𝓗_c f` is continuous for `f` with finite mass. -/
theorem besselHankelTransform_continuous {c : ℝ} (hc : 1 / 2 < c) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun s => f s * hankelRho0 c s) (Ioi 0)) :
    Continuous (besselHankelTransform c f) := by
  have hc0 : 0 < c := by linarith
  unfold besselHankelTransform
  refine continuous_of_dominated (bound := fun s => |f s| * hankelRho0 c s)
    (fun Δ => ?_) (fun Δ => ?_) (abs_mul_rho0_integrableOn hc0 hint) ?_
  · exact hint.aestronglyMeasurable.mul
      ((hankelPhi_continuous c).comp (continuous_const_mul Δ)).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs.le)]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hs.le))
      (abs_hankelKernel_le_one hc _ _)
  · exact Eventually.of_forall fun s =>
      continuous_const.mul ((hankelPhi_continuous c).comp (continuous_id.mul continuous_const))

end FormalResearch.SignUncertainty
