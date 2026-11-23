module

public import FormalResearch.SignUncertainty.RadialDerivative

/-!
# `Ξ_{c_k}' → Ξ'` locally uniformly (`lem:radial-compactness`, Step 3)

The `s`-derivative `∫ radialdA c f s v dv` of `Ξ_c(s) = ∫ radialA c f s v dv` (`hasDerivAt_radialXi`) is continuous
in `s` (`continuous_radialXi_deriv`) and converges locally uniformly to `∫ radialdAlim W s v dv`
(`radial_deriv_limit`), with the extra factor `1 + |v|` absorbed by the decay `(1+|v|)^{-3}`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The limit of `radialdA`: `π² w radialAlim`. -/
noncomputable def radialdAlim (W : ℂ → ℂ) (s v : ℝ) : ℂ :=
  ((Real.pi ^ 2 : ℝ) : ℂ) * (1 + (v : ℂ) * Complex.I) * radialAlim W s v

lemma integrable_dom2 : Integrable (fun v : ℝ => 2 * 200 ^ 5 * (1 + |v|) ^ (-(2 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  simpa [Real.norm_eq_abs] using this.const_mul (2 * 200 ^ 5 : ℝ)

lemma radialdA_norm_le {c ε S s v M₀ : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f ≤ M₀) (hs : |s| ≤ S)
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * S ≤ 1 / 2) :
    ‖radialdA c f s v‖ ≤ 4 * Real.pi ^ 2 *
      (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
        (2 * 200 ^ 5 * (1 + |v|) ^ (-(2 : ℝ)))) := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_pos
  obtain ⟨hξ, hcoef⟩ := radialXi_facts hc0 hs hS
  have he0 := radialEps_pos hc0
  have he10 := radialEps_le_tenth hc
  have hA := radialA_norm_le (v := v) hc hf hε hM hs hS
  have hξinv : ‖((radialXi c s : ℝ) : ℂ)⁻¹‖ ≤ 2 * Real.pi ^ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hξ.le]
    rw [div_le_iff₀ (by positivity)] at hcoef
    rw [inv_le_comm₀ hξ (by positivity)]
    rw [inv_eq_one_div, div_le_iff₀ (by positivity)] at *
    nlinarith
  have hw : ‖1 + (v : ℂ) * Complex.I - ((radialEps c ^ 2 : ℝ) : ℂ)‖ ≤ 2 * (1 + |v|) := by
    have : (1 : ℂ) + (v : ℂ) * Complex.I - ((radialEps c ^ 2 : ℝ) : ℂ) =
        ((1 - radialEps c ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I := by push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖((1 - radialEps c ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> nlinarith
    have h2 : ‖(v : ℂ) * Complex.I‖ = |v| := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    linarith [abs_nonneg v]
  have hy : 0 < 1 + |v| := by positivity
  have hyy : (1 + |v|) * (1 + |v|) ^ (-(3 : ℝ)) = (1 + |v|) ^ (-(2 : ℝ)) := by
    rw [show (-(2 : ℝ)) = 1 + (-3) by norm_num, Real.rpow_add hy, Real.rpow_one]
  unfold radialdA
  rw [norm_mul, norm_mul]
  have hA0 := norm_nonneg (radialA c f s v)
  calc ‖1 + (v : ℂ) * Complex.I - ((radialEps c ^ 2 : ℝ) : ℂ)‖ * ‖((radialXi c s : ℝ) : ℂ)⁻¹‖ *
        ‖radialA c f s v‖
      ≤ (2 * (1 + |v|)) * (2 * Real.pi ^ 2) *
        (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
          (2 * 200 ^ 5 * (1 + |v|) ^ (-(3 : ℝ)))) := by gcongr
    _ = 4 * Real.pi ^ 2 * (Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
        (2 * 200 ^ 5 * ((1 + |v|) * (1 + |v|) ^ (-(3 : ℝ))))) := by ring
    _ = _ := by rw [hyy]

end FormalResearch.SignUncertainty
