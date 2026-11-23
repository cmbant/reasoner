module

public import FormalResearch.SignUncertainty.RadialIntegrand
public import FormalResearch.SignUncertainty.ParamIntegral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Domination of `Ξ_c` and the dominated-convergence limit (`lem:radial-compactness`, Step 3)

`radialA c f s v = (2π ξ_c(s))^{-1} K_c(1+iv,s) W_c(1+iv)`, so that `Ξ_c(s) = ∫ radialA c f s v dv`.  For
`c ≥ 1000`, `|s| ≤ S`, `π² ε_c² S ≤ 1/2`, `M[f] ≤ M₀`: `‖radialA‖ ≤ C_S M₀ (1+|v|)^{-3}`
(`radialA_norm_le`, `integrable_dom`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma dom_aux (v : ℝ) :
    (1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ)) * (2 + |v|) ^ (1 / 2 : ℝ) ≤
      2 * 200 ^ 5 * (1 + |v|) ^ (-(3 : ℝ)) := by
  set y : ℝ := 1 + |v| with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith [abs_nonneg v]
  set a : ℝ := 1 + v ^ 2 / 100 with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith [sq_nonneg v]
  have h1 : y ^ 2 ≤ 200 * a := by
    rw [hy, ha]; nlinarith [sq_abs v, abs_nonneg v, sq_nonneg (|v| - 1)]
  have h2 : a ^ (-(300 / 56 : ℝ)) ≤ a ^ (-(5 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)
  have h3 : a ^ (-(5 : ℝ)) = (a ^ 5)⁻¹ := by
    rw [Real.rpow_neg (by linarith)]; norm_cast
  have h4 : y ^ 10 ≤ 200 ^ 5 * a ^ 5 := by
    have : (y ^ 2) ^ 5 ≤ (200 * a) ^ 5 := by gcongr
    calc y ^ 10 = (y ^ 2) ^ 5 := by ring
      _ ≤ (200 * a) ^ 5 := this
      _ = 200 ^ 5 * a ^ 5 := by ring
  have h5 : (a ^ 5)⁻¹ ≤ 200 ^ 5 * (y ^ 10)⁻¹ := by
    have hinv := inv_anti₀ (by positivity : 0 < y ^ 10) h4
    calc (a ^ 5)⁻¹ = 200 ^ 5 * (200 ^ 5 * a ^ 5)⁻¹ := by field_simp
      _ ≤ 200 ^ 5 * (y ^ 10)⁻¹ := by gcongr
  have h6 : (2 + |v|) ^ (1 / 2 : ℝ) ≤ 2 * y := by
    have h7 : 2 + |v| ≤ 2 * y := by rw [hy]; linarith [abs_nonneg v]
    calc (2 + |v|) ^ (1 / 2 : ℝ) ≤ (2 * y) ^ (1 / 2 : ℝ) := by gcongr
      _ ≤ (2 * y) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 2 * y := Real.rpow_one _
  have h8 : (y ^ 10)⁻¹ * y ≤ y ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg (by linarith)]
    have : y ^ (3 : ℝ) = y ^ 3 := by norm_cast
    rw [this]
    have h9 : y ^ 3 ≤ y ^ 9 := pow_le_pow_right₀ hy1 (by norm_num)
    have : (y ^ 10)⁻¹ * y = (y ^ 9)⁻¹ := by field_simp
    rw [this]
    exact inv_anti₀ (by positivity) h9
  have hpos : 0 ≤ (2 + |v|) ^ (1 / 2 : ℝ) := by positivity
  calc a ^ (-(300 / 56 : ℝ)) * (2 + |v|) ^ (1 / 2 : ℝ)
      ≤ (200 ^ 5 * (y ^ 10)⁻¹) * (2 * y) := by
        gcongr
        · exact h2.trans (h3 ▸ h5)
      _ = 2 * 200 ^ 5 * ((y ^ 10)⁻¹ * y) := by ring
      _ ≤ 2 * 200 ^ 5 * y ^ (-(3 : ℝ)) := by gcongr

lemma integrable_dom : Integrable (fun v : ℝ => 2 * 200 ^ 5 * (1 + |v|) ^ (-(3 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by simp)
  simpa [Real.norm_eq_abs] using this.const_mul (2 * 200 ^ 5 : ℝ)

/-- The integrand of `Ξ_c(s) = ∫ radialA c f s v dv`. -/
noncomputable def radialA (c : ℝ) (f : ℝ → ℝ) (s v : ℝ) : ℂ :=
  ((1 / (2 * Real.pi * radialXi c s) : ℝ) : ℂ) *
    (radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I))

lemma radialXi_facts {c s S : ℝ} (hc : 0 < c) (hs : |s| ≤ S)
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * S ≤ 1 / 2) :
    0 < radialXi c s ∧ 1 / (2 * Real.pi * radialXi c s) ≤ Real.pi := by
  have hpi := Real.pi_pos
  have hπξ : Real.pi ^ 2 * radialXi c s = 1 + Real.pi ^ 2 * radialEps c ^ 2 * s := by
    simp only [radialXi]; field_simp
  have hs' : |Real.pi ^ 2 * radialEps c ^ 2 * s| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |Real.pi ^ 2 * radialEps c ^ 2| * |s| ≤ (Real.pi ^ 2 * radialEps c ^ 2) * S := by
          rw [abs_of_nonneg (by positivity)]; gcongr
      _ ≤ 1 / 2 := by nlinarith
  have h1 : 1 / 2 ≤ Real.pi ^ 2 * radialXi c s := by
    rw [hπξ]; have := neg_abs_le (Real.pi ^ 2 * radialEps c ^ 2 * s); linarith
  have hξ : 0 < radialXi c s := by
    have : 0 < Real.pi ^ 2 * radialXi c s := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  refine ⟨hξ, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma radialW_line_norm_le {c ε : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (v : ℝ) :
    ‖radialW c f (1 + (v : ℂ) * Complex.I)‖ ≤ hankelMass c f * (11 / 10) * (2 + |v|) ^ (1 / 2 : ℝ) := by
  have hc0 : 0 < c := by linarith
  have he0 := radialEps_pos hc0
  have he10 := radialEps_le_tenth hc
  have h := radialW_norm_le (by linarith) hf hε (w := 1 + (v : ℂ) * Complex.I) (by simp)
    (by simp; linarith)
  refine h.trans ?_
  have hM0 := hankelMass_nonneg hc0 f
  have h1 : ‖1 + (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I)‖ ≤ 2 + |v| := by
    have : (1 : ℂ) + (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I) =
        ((1 + radialEps c : ℝ) : ℂ) + ((radialEps c * v : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by linarith), abs_mul, abs_of_pos he0]
    nlinarith [abs_nonneg v]
  have h2 : ‖1 + (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I)‖ ^ (1 / 2 : ℝ) ≤ (2 + |v|) ^ (1 / 2 : ℝ) := by
    gcongr
  have h3 : Real.exp (1 / (6 * c)) ≤ 11 / 10 := exp_le_of_small (by positivity) (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  calc hankelMass c f * ‖1 + (radialEps c : ℂ) * (1 + (v : ℂ) * Complex.I)‖ ^ (1 / 2 : ℝ) *
        Real.exp (1 / (6 * c))
      ≤ hankelMass c f * (2 + |v|) ^ (1 / 2 : ℝ) * (11 / 10) := by gcongr
    _ = _ := by ring

lemma radialA_norm_le {c ε S s v M₀ : ℝ} (hc : 1000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f ≤ M₀) (hs : |s| ≤ S)
    (hS : Real.pi ^ 2 * radialEps c ^ 2 * S ≤ 1 / 2) :
    ‖radialA c f s v‖ ≤ Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
      (2 * 200 ^ 5 * (1 + |v|) ^ (-(3 : ℝ))) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hξ, hcoef⟩ := radialXi_facts hc0 hs hS
  have hM0 : 0 ≤ M₀ := (hankelMass_nonneg hc0 f).trans hM
  have hK := radialK_norm_le (v := v) hc hs hS
  have hW := radialW_line_norm_le hc hf hε v
  unfold radialA
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hd := dom_aux v
  calc 1 / (2 * Real.pi * radialXi c s) * (‖radialK c (1 + (v : ℂ) * Complex.I) s‖ *
        ‖radialW c f (1 + (v : ℂ) * Complex.I)‖)
      ≤ Real.pi * ((4 * Real.exp (4 / 9 + Real.pi ^ 2 * S) * (1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ))) *
        (hankelMass c f * (11 / 10) * (2 + |v|) ^ (1 / 2 : ℝ))) := by gcongr
    _ ≤ Real.pi * ((4 * Real.exp (4 / 9 + Real.pi ^ 2 * S) * (1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ))) *
        (M₀ * (11 / 10) * (2 + |v|) ^ (1 / 2 : ℝ))) := by gcongr
    _ = Real.pi * (4 * Real.exp (4 / 9 + Real.pi ^ 2 * S)) * (M₀ * (11 / 10)) *
        ((1 + v ^ 2 / 100) ^ (-(300 / 56 : ℝ)) * (2 + |v|) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ _ := by gcongr

end FormalResearch.SignUncertainty
