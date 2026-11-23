module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Complex-parameter differentiation under an iterated integral over `(0,∞)²`

Source: `(e27)` symbol derivative bounds (`u1c_o1_upper.tex`, Lemma U.1); user: the differentiated Gaussian IBP expansion of
`gaussian_2d_ibp_asymp`, in which `ceF1`, `ceG1`, `ceG1Deriv` are written as `∫ t in Ioi 0, ∫ s in Ioi 0, ...`.

Mathlib already differentiates under the integral with a complex parameter
(`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, stated for `𝕜` an `RCLike` field, so `𝕜 = ℂ` is covered).
This module adds only the thin wrappers for the iterated integral over `(0,∞)` and `(0,∞)²`:

* `hasDerivAt_integral_Ioi`: the one-dimensional case with `μ = volume.restrict (Ioi 0)`;
* `hasDerivAt_iterated_integral_Ioi`: the iterated integral over `(0,∞) × (0,∞)`, with product measure `μ.prod μ`.

Status: proved, unconditional, except the extra hypothesis `hint_near` of the iterated wrapper (integrability of the
product integrand for `y` near `y₀`), which is not derived here. It is satisfiable (it is automatic for a Gaussian
integrand) and follows in general from `hint`, `hbd`, `hbi` and a convex ball in `s`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace FormalResearch.CohnElkies

/-- A property holding for all `(t, u) ∈ (0,∞)²` holds `μ.prod μ`-almost everywhere, with `μ = volume.restrict (Ioi 0)`. -/
lemma paramIt_ae_prod_Ioi {P : ℝ × ℝ → Prop}
    (h : ∀ t ∈ Ioi (0 : ℝ), ∀ u ∈ Ioi (0 : ℝ), P (t, u)) :
    ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))), P p := by
  rw [Measure.prod_restrict]
  exact ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp => h p.1 hp.1 p.2 hp.2

/-- One-dimensional wrapper: differentiation of `∫_{(0,∞)} F y t dt` in a complex parameter `y`, with a bound
uniform on a neighbourhood `s` of `y₀`. Negative regression: the hypothesis `hs : s ∈ 𝓝 y₀` cannot be replaced by
`y₀ ∈ s`, since the derivative bound must control the difference quotients for all `y` near `y₀`; for example, a
bound valid only on the closed half-plane `{Re y ≥ 0}` does not apply at the boundary points `Re y = 0`, where that
set is not a neighbourhood. -/
theorem hasDerivAt_integral_Ioi {F F' : ℂ → ℝ → ℂ} {y₀ : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 y₀) {bound : ℝ → ℝ}
    (hmeas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (F y) (volume.restrict (Ioi (0 : ℝ))))
    (hint : IntegrableOn (F y₀) (Ioi (0 : ℝ))) (hmeas' : AEStronglyMeasurable (F' y₀) (volume.restrict (Ioi (0 : ℝ))))
    (hbd : ∀ t ∈ Ioi (0 : ℝ), ∀ y ∈ s, ‖F' y t‖ ≤ bound t) (hbi : IntegrableOn bound (Ioi (0 : ℝ)))
    (hd : ∀ t ∈ Ioi (0 : ℝ), ∀ y ∈ s, HasDerivAt (fun y => F y t) (F' y t) y) :
    IntegrableOn (F' y₀) (Ioi (0 : ℝ)) ∧
      HasDerivAt (fun y => ∫ t in Ioi (0 : ℝ), F y t) (∫ t in Ioi (0 : ℝ), F' y₀ t) y₀ :=
  hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hmeas'
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht y hy => hbd t ht y hy) hbi
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hd t ht)

/-- Iterated wrapper: differentiation of `∫_{(0,∞)} ∫_{(0,∞)} F y t u du dt` in a complex parameter `y`, the bound
`bound t u` being uniform on a neighbourhood `s` of `y₀`. The product integral is converted to the iterated one by
`integral_prod`, which needs integrability for `y` near `y₀` (`hint_near`, the extra hypothesis of this wrapper).
Negative regression: as in `hasDerivAt_integral_Ioi`, `hs : s ∈ 𝓝 y₀` is needed, and a bound valid only on the
closed half-plane `{Re y ≥ 0}` does not give differentiability at the points with `Re y = 0`. -/
theorem hasDerivAt_iterated_integral_Ioi {F F' : ℂ → ℝ → ℝ → ℂ} {y₀ : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 y₀)
    {bound : ℝ → ℝ → ℝ}
    (hmeas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (Function.uncurry (F y))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hint : Integrable (Function.uncurry (F y₀))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hmeas' : AEStronglyMeasurable (Function.uncurry (F' y₀))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hbd : ∀ t ∈ Ioi (0 : ℝ), ∀ u ∈ Ioi (0 : ℝ), ∀ y ∈ s, ‖F' y t u‖ ≤ bound t u)
    (hbi : Integrable (Function.uncurry bound)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hd : ∀ t ∈ Ioi (0 : ℝ), ∀ u ∈ Ioi (0 : ℝ), ∀ y ∈ s, HasDerivAt (fun y => F y t u) (F' y t u) y)
    (hint_near : ∀ᶠ y in 𝓝 y₀, Integrable (Function.uncurry (F y))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :
    Integrable (Function.uncurry (F' y₀))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
      HasDerivAt (fun y => ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F y t u)
        (∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F' y₀ t u) y₀ := by
  have hbd' := paramIt_ae_prod_Ioi (P := fun p => ∀ y ∈ s, ‖F' y p.1 p.2‖ ≤ bound p.1 p.2)
    (fun t ht u hu y hy => hbd t ht u hu y hy)
  have hd' := paramIt_ae_prod_Ioi (P := fun p => ∀ y ∈ s,
      HasDerivAt (fun y => Function.uncurry (F y) p) (Function.uncurry (F' y) p) y)
    (fun t ht u hu y hy => hd t ht u hu y hy)
  obtain ⟨hI, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hmeas'
    (by filter_upwards [hbd'] with p hp using fun y hy => hp y hy) hbi
    (by filter_upwards [hd'] with p hp using hp)
  refine ⟨hI, ?_⟩
  have heq : (fun y => ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F y t u) =ᶠ[𝓝 y₀]
      (fun y => ∫ p, Function.uncurry (F y) p ∂((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ))))) := by
    filter_upwards [hint_near] with y hy
    exact (integral_prod _ hy).symm
  have hval : ∫ p, Function.uncurry (F' y₀) p ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))) = ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F' y₀ t u :=
    integral_prod _ hI
  exact (hD.congr_of_eventuallyEq heq).congr_deriv hval

/-- info: 'FormalResearch.CohnElkies.hasDerivAt_integral_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.hasDerivAt_integral_Ioi

/-- info: 'FormalResearch.CohnElkies.hasDerivAt_iterated_integral_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.hasDerivAt_iterated_integral_Ioi

end FormalResearch.CohnElkies
