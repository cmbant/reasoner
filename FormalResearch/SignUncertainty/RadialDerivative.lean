module

public import FormalResearch.SignUncertainty.RadialValueMain

/-!
# The `s`-derivative of `Ξ_c` (`lem:radial-compactness`, Step 3)

`∂_s radialA c f s v = radialdA c f s v := (w - ε_c²) ξ_c(s)^{-1} radialA c f s v`, `w = 1 + iv`
(`hasDerivAt_radialA`, from `hasDerivAt_xi_inv_radialKernel`), and `‖radialdA‖ ≤ C_S M₀ (1+|v|)^{-2}`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `(w - ε_c²) ξ_c(s)^{-1} · radialA`, the `s`-derivative of `radialA`. -/
noncomputable def radialdA (c : ℝ) (f : ℝ → ℝ) (s v : ℝ) : ℂ :=
  ((1 + (v : ℂ) * Complex.I - ((radialEps c ^ 2 : ℝ) : ℂ)) * ((radialXi c s : ℝ) : ℂ)⁻¹) *
    radialA c f s v

lemma radialK_eq_radialKernel {c : ℝ} (hc : 0 < c) {s : ℝ} (hξ : 0 < radialXi c s) {w : ℂ}
    (hw0 : 0 ≤ w.re) (hw1 : radialEps c * w.re < 1) :
    radialK c w s = radialKernel c stripH w s := by
  have he0 := radialEps_pos hc
  have hζre : ((radialEps c : ℂ) * w).re = radialEps c * w.re := by simp
  have hkern := mellin_strip_kernel_eq (c := c) (ξ := radialXi c s) hc hξ (ζ := (radialEps c : ℂ) * w)
    (by rw [hζre]; positivity) (by rw [hζre]; exact hw1)
  unfold radialK radialKernel
  rw [← hkern]
  have : ((2 * Real.pi * c * radialXi c s : ℝ) : ℂ) = (2 * (Real.pi : ℂ) * (c : ℂ) * (radialXi c s : ℂ)) := by
    push_cast; ring
  rw [this]
  have h2 : (c : ℂ) * ((radialEps c : ℂ) * w) = (c : ℂ) * (radialEps c : ℂ) * w := by ring
  rw [h2]

lemma hasDerivAt_radialA {c : ℝ} (hc : 0 < c) (hc1 : 1 < c) (f : ℝ → ℝ) {s₀ : ℝ}
    (hξ : 0 < radialXi c s₀) (v : ℝ) :
    HasDerivAt (fun s => radialA c f s v) (radialdA c f s₀ v) s₀ := by
  have he0 := radialEps_pos hc
  have he1 := radialEps_lt_one hc1
  set w : ℂ := 1 + (v : ℂ) * Complex.I with hw
  have hw0 : 0 ≤ w.re := by simp [hw]
  have hw1 : radialEps c * w.re < 1 := by simpa [hw] using he1
  have hcont : Continuous fun s : ℝ => radialXi c s := by unfold radialXi; fun_prop
  have hnear : ∀ᶠ s in 𝓝 s₀, 0 < radialXi c s := hcont.continuousAt.eventually (lt_mem_nhds hξ)
  have hd := hasDerivAt_xi_inv_radialKernel hc stripH w hξ
  have hd2 := (hd.mul_const (radialW c f w)).const_mul ((1 / (2 * Real.pi) : ℂ))
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hξ0 : ((radialXi c s₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  refine (hd2.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold radialdA radialA
    rw [radialK_eq_radialKernel hc hξ hw0 hw1]
    push_cast
    field_simp
    simp only [hw]
    ring
  · filter_upwards [hnear] with s hs
    unfold radialA
    rw [radialK_eq_radialKernel hc hs hw0 hw1]
    have hξs : ((radialXi c s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    simp only [hw]

end FormalResearch.SignUncertainty
