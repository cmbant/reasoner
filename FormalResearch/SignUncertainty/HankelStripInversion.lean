module

public import FormalResearch.SignUncertainty.RadialXiMain

/-!
# Exact inversion on a vertical line of the strip (`mat:T2`(2), `(e32)`)

`hankelWt c f ζ = W̃_c(ζ) = e^{-c ℋ(ζ)} M̃_f(c(1-ζ))` (`gt:7.4`).  For `f ∈ 𝒜_c^ε`, `c > 3/2`, `0 < σ < 1` with
`c σ > 1` (so that the Mellin line `Re z = c(1-σ)` satisfies `Re z + 1 < c` of `mellin_inversion_f`) and `ξ > 0`:
`(ρ₀ f)(cξ) = (2πξ)^{-1} ∫ K₀(σ+iτ, ξ) W̃_c(σ+iτ) dτ` (`hankel_inversion_line`).  `radial_xi_repr` is the case
`σ = ε_c`, rescaled.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `W̃_c(ζ) = e^{-c ℋ(ζ)} M̃_f(c (1 - ζ))`. -/
noncomputable def hankelWt (c : ℝ) (f : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (-((c : ℂ) * hInt ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ))

lemma radialW_eq_hankelWt (c : ℝ) (f : ℝ → ℝ) (w : ℂ) :
    radialW c f w = hankelWt c f ((radialEps c : ℂ) * w) := rfl

/-- **`(e32)`**: exact inversion on the line `Re ζ = σ`. -/
theorem hankel_inversion_line {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hcσ : 1 < c * σ) {ξ : ℝ} (hξ : 0 < ξ) :
    (((hankelRho0 c (c * ξ) * f (c * ξ) : ℝ)) : ℂ) =
      ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
        ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
          hankelWt c f ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hΔ : 0 < c * ξ := mul_pos hc0 hξ
  set Δ := c * ξ with hΔdef
  set σz : ℝ := c * (1 - σ) with hσzdef
  have hσz0 : 0 < σz := mul_pos hc0 (by linarith)
  have hσz1 : σz + 1 < c := by rw [hσzdef]; nlinarith
  have hinv := mellin_inversion_f hc hf hε hσz0 hσz1 hΔ
  set G : ℝ → ℂ := fun y => (Δ : ℂ)⁻¹ * (Complex.Gamma ((σz : ℂ) + (y : ℂ) * Complex.I) / Complex.Gamma (c : ℂ)) *
      ((2 * Real.pi * Δ : ℝ) : ℂ) ^ ((c : ℂ) - ((σz : ℂ) + (y : ℂ) * Complex.I)) *
        mellinStrip f ((σz : ℂ) + (y : ℂ) * Complex.I) with hG
  have h1 : (((hankelRho0 c Δ * f Δ : ℝ)) : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, G y := by
    have h0 : (((hankelRho0 c Δ * f Δ : ℝ)) : ℂ) = (hankelRho0 c Δ : ℂ) * (f Δ : ℂ) := by push_cast; ring
    rw [h0, hinv, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have := rho0_mul_term f hc0 hΔ (z := (σz : ℂ) + (y : ℂ) * Complex.I) (by simpa using hσz0)
    simpa [hG] using this
  have hcv := MeasureTheory.Measure.integral_comp_mul_left G (-c)
  have hne : (-c) ≠ 0 := by linarith
  have hcv' : ∫ y : ℝ, G y = c • ∫ τ : ℝ, G (-c * τ) := by
    have habs : |(-c)⁻¹| = c⁻¹ := by rw [abs_inv, abs_neg, abs_of_pos hc0]
    rw [habs] at hcv
    rw [hcv, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  have hper : ∀ τ : ℝ, G (-c * τ) =
      (Δ : ℂ)⁻¹ * (mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
        hankelWt c f ((σ : ℂ) + (τ : ℂ) * Complex.I)) := by
    intro τ
    set ζ : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hζ
    have hzv : (σz : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I = (c : ℂ) * (1 - ζ) := by
      rw [hζ, hσzdef]; push_cast; ring
    have hcz : (c : ℂ) - (c : ℂ) * (1 - ζ) = (c : ℂ) * ζ := by ring
    have hζre : ζ.re = σ := by rw [hζ]; simp
    have hkern := mellin_strip_kernel_eq (c := c) (ξ := ξ) hc0 hξ (ζ := ζ)
      (by rw [hζre]; exact hσ0.le) (by rw [hζre]; exact hσ1)
    have hH : hInt ζ = stripH ζ := hInt_eq_stripH (by rw [hζre]; exact hσ0.le) (by rw [hζre]; exact hσ1)
    have hW : hankelWt c f ζ =
        Complex.exp (-((c : ℂ) * stripH ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) := by
      show Complex.exp (-((c : ℂ) * hInt ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) = _
      rw [hH]
    have h2pi : ((2 * Real.pi * Δ : ℝ) : ℂ) = (2 * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ)) := by
      rw [hΔdef]; push_cast; ring
    simp only [hG]
    rw [hzv, hcz, hW, ← hkern, h2pi]
    have hexp : Complex.exp ((c : ℂ) * stripH ζ) * Complex.exp (-((c : ℂ) * stripH ζ)) = 1 := by
      rw [← Complex.exp_add]; simp
    calc _ = (Δ : ℂ)⁻¹ * (Complex.Gamma ((c : ℂ) * (1 - ζ)) / Complex.Gamma (c : ℂ) *
          (2 * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ)) ^ ((c : ℂ) * ζ) *
          (Complex.exp ((c : ℂ) * stripH ζ) * Complex.exp (-((c : ℂ) * stripH ζ))) *
          mellinStrip f ((c : ℂ) * (1 - ζ))) := by rw [hexp]; ring
      _ = _ := by ring
  have hint : ∫ τ : ℝ, G (-c * τ) =
      (Δ : ℂ)⁻¹ * ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
          hankelWt c f ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
    simp_rw [hper]; rw [integral_const_mul]
  have hΔc : (Δ : ℂ) = (c : ℂ) * (ξ : ℂ) := by rw [hΔdef]; push_cast; ring
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  push_cast
  have h1' : ((hankelRho0 c Δ : ℝ) : ℂ) * (f Δ : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, G y := by
    have := h1; push_cast at this; exact this
  rw [h1', hcv', hint, Complex.real_smul, hΔc]
  generalize (∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
          hankelWt c f ((σ : ℂ) + (τ : ℂ) * Complex.I)) = J
  field_simp

/-- info: 'FormalResearch.SignUncertainty.hankel_inversion_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_inversion_line

end FormalResearch.SignUncertainty
