module

public import FormalResearch.SignUncertainty.RadialXiRepr

/-!
# `Ξ_c(s) = (2π ξ_c(s))^{-1} ∫ K_c(1+iv, s) W_c(1+iv) dv` (`lem:radial-compactness`, Step 3)
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma rpow_third_mul_radialEps {c : ℝ} (hc : 0 < c) : c ^ (1 / 3 : ℝ) * radialEps c = 1 := by
  unfold radialEps
  rw [← Real.rpow_add hc]; norm_num

lemma radialEps_lt_one {c : ℝ} (hc : 1 < c) : radialEps c < 1 := by
  unfold radialEps
  exact Real.rpow_lt_one_of_one_lt_of_neg hc (by norm_num)

theorem radial_xi_repr {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {s : ℝ} (hξ : 0 < radialXi c s) :
    (((c ^ (1 / 3 : ℝ)) * (hankelRho0 c (c * radialXi c s) * f (c * radialXi c s)) : ℝ) : ℂ) =
      ((1 / (2 * Real.pi * radialXi c s) : ℝ) : ℂ) *
        ∫ v : ℝ, radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < c := by linarith
  set e := radialEps c with hedef
  set ξ := radialXi c s with hξdef
  have he0 : 0 < e := radialEps_pos hc0
  have he1 : e < 1 := radialEps_lt_one hc1
  have hcube : c * e ^ 3 = 1 := radialEps_cube hc0
  have hΔ : 0 < c * ξ := mul_pos hc0 hξ
  set Δ := c * ξ with hΔdef
  set σ : ℝ := c * (1 - e) with hσdef
  have hσ0 : 0 < σ := mul_pos hc0 (by linarith)
  have hce : 1 < c * e := by
    have : c * e = 1 / e ^ 2 := by field_simp; nlinarith [hcube]
    rw [this, lt_div_iff₀ (by positivity)]; nlinarith
  have hσ1 : σ + 1 < c := by rw [hσdef]; nlinarith
  have hinv := mellin_inversion_f hc hf hε hσ0 hσ1 hΔ
  have hρ0 : 0 < hankelRho0 c Δ := hankelRho0_pos hc0 hΔ
  -- the integrand after multiplying by ρ₀
  set G : ℝ → ℂ := fun y => (Δ : ℂ)⁻¹ * (Complex.Gamma ((σ : ℂ) + (y : ℂ) * Complex.I) / Complex.Gamma (c : ℂ)) *
      ((2 * Real.pi * Δ : ℝ) : ℂ) ^ ((c : ℂ) - ((σ : ℂ) + (y : ℂ) * Complex.I)) *
        mellinStrip f ((σ : ℂ) + (y : ℂ) * Complex.I) with hG
  have h1 : (((hankelRho0 c Δ * f Δ : ℝ)) : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, G y := by
    have h0 : (((hankelRho0 c Δ * f Δ : ℝ)) : ℂ) = (hankelRho0 c Δ : ℂ) * (f Δ : ℂ) := by push_cast; ring
    rw [h0, hinv, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have := rho0_mul_term f hc0 hΔ (z := (σ : ℂ) + (y : ℂ) * Complex.I) (by simpa using hσ0)
    simpa [hG] using this
  have hcv := MeasureTheory.Measure.integral_comp_mul_left G (-(c * e))
  have hne : (-(c * e)) ≠ 0 := by have := mul_pos hc0 he0; linarith
  have hcv' : ∫ y : ℝ, G y = (c * e) • ∫ v : ℝ, G (-(c * e) * v) := by
    have habs : |(-(c * e))⁻¹| = (c * e)⁻¹ := by
      rw [abs_inv, abs_neg, abs_of_pos (mul_pos hc0 he0)]
    rw [habs] at hcv
    have hce0 : c * e ≠ 0 := (mul_pos hc0 he0).ne'
    rw [hcv, smul_smul, mul_inv_cancel₀ hce0, one_smul]
  have hper : ∀ v : ℝ, G (-(c * e) * v) =
      (Δ : ℂ)⁻¹ * (radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I)) := by
    intro v
    set ζ : ℂ := (e : ℂ) * (1 + (v : ℂ) * Complex.I) with hζ
    have hzv : (σ : ℂ) + ((-(c * e) * v : ℝ) : ℂ) * Complex.I = (c : ℂ) * (1 - ζ) := by
      rw [hζ, hσdef]; push_cast; ring
    have hcz : (c : ℂ) - (c : ℂ) * (1 - ζ) = (c : ℂ) * ζ := by ring
    have hζre : ζ.re = e := by rw [hζ]; simp
    have hkern := mellin_strip_kernel_eq (c := c) (ξ := ξ) hc0 hξ (ζ := ζ) (by rw [hζre]; exact he0.le)
      (by rw [hζre]; exact he1)
    have hH : hInt ζ = stripH ζ := hInt_eq_stripH (by rw [hζre]; exact he0.le) (by rw [hζre]; exact he1)
    have hK : radialK c (1 + (v : ℂ) * Complex.I) s = mellinK0 c ζ ξ := by
      simp only [radialK, hζ, hedef, hξdef]
    have hW : radialW c f (1 + (v : ℂ) * Complex.I) =
        Complex.exp (-((c : ℂ) * stripH ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) := by
      show Complex.exp (-((c : ℂ) * hInt ζ)) * mellinStrip f ((c : ℂ) * (1 - ζ)) = _
      rw [hH]
    have h2pi : ((2 * Real.pi * Δ : ℝ) : ℂ) = (2 * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ)) := by
      rw [hΔdef]; push_cast; ring
    simp only [hG]
    rw [hzv, hcz, hK, hW, ← hkern, h2pi]
    have hexp : Complex.exp ((c : ℂ) * stripH ζ) * Complex.exp (-((c : ℂ) * stripH ζ)) = 1 := by
      rw [← Complex.exp_add]; simp
    calc _ = (Δ : ℂ)⁻¹ * (Complex.Gamma ((c : ℂ) * (1 - ζ)) / Complex.Gamma (c : ℂ) *
          (2 * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ)) ^ ((c : ℂ) * ζ) *
          (Complex.exp ((c : ℂ) * stripH ζ) * Complex.exp (-((c : ℂ) * stripH ζ))) *
          mellinStrip f ((c : ℂ) * (1 - ζ))) := by rw [hexp]; ring
      _ = _ := by ring
  have hce : c ^ (1 / 3 : ℝ) * e = 1 := rpow_third_mul_radialEps hc0
  have hint : ∫ v : ℝ, G (-(c * e) * v) =
      (Δ : ℂ)⁻¹ * ∫ v : ℝ, radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I) := by
    simp_rw [hper]; rw [integral_const_mul]
  have hΔc : (Δ : ℂ) = (c : ℂ) * (ξ : ℂ) := by rw [hΔdef]; push_cast; ring
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have hce' : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (e : ℂ) = 1 := by exact_mod_cast hce
  push_cast
  have h1' : ((hankelRho0 c Δ : ℝ) : ℂ) * (f Δ : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, G y := by
    have := h1; push_cast at this; exact this
  rw [h1', hcv', hint, Complex.real_smul, hΔc]
  push_cast
  generalize (∫ v : ℝ, radialK c (1 + (v : ℂ) * Complex.I) s * radialW c f (1 + (v : ℂ) * Complex.I)) = J
  field_simp
  rw [hce', one_mul]

/-- info: 'FormalResearch.SignUncertainty.radial_xi_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radial_xi_repr

end FormalResearch.SignUncertainty
