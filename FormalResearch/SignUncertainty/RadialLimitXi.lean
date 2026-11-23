module

public import FormalResearch.SignUncertainty.RadialLimitW
public import FormalResearch.SignUncertainty.RadialValueMain
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The limit function `Ξ(s) = (π/2) ∫ e^{π²w³/36 + π² s w} W(w) dv` (`lem:radial-compactness`, Step 4)

For `W` holomorphic on `Re w > 0` with `‖W‖ ≤ M₀`, `limInt W u v s = e^{π²w³/36 + π² s w} W(w)`, `w = u + iv`.
`XiL W s = ∫ (π/2) limInt W 1 v s dv` is entire in `s` (`differentiable_XiL`) and agrees with
`∫ radialAlim W s v dv` for real `s`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `e^{π²w³/36 + π² s w} W(w)` at `w = u + iv`. -/
noncomputable def limInt (W : ℂ → ℂ) (u v : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((Real.pi ^ 2 / 36 : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 3 +
    (Real.pi ^ 2 : ℂ) * s * ((u : ℂ) + (v : ℂ) * Complex.I)) * W ((u : ℂ) + (v : ℂ) * Complex.I)

/-- `Ξ(s) = ∫ (π/2) limInt W 1 v s dv`. -/
noncomputable def XiL (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∫ v : ℝ, ((Real.pi / 2 : ℝ) : ℂ) * limInt W 1 v s

lemma radialAlim_eq_limInt (W : ℂ → ℂ) (s v : ℝ) :
    radialAlim W s v = ((Real.pi / 2 : ℝ) : ℂ) * limInt W 1 v (s : ℂ) := by
  unfold radialAlim radialKlim limInt
  push_cast; ring_nf

lemma XiL_ofReal (W : ℂ → ℂ) (s : ℝ) : XiL W (s : ℂ) = ∫ v : ℝ, radialAlim W s v := by
  unfold XiL
  exact integral_congr_ae (Eventually.of_forall fun v => (radialAlim_eq_limInt W s v).symm)

lemma re_cube_line (u v : ℝ) : (((u : ℂ) + (v : ℂ) * Complex.I) ^ 3).re = u ^ 3 - 3 * u * v ^ 2 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

lemma norm_limInt_le {W : ℂ → ℂ} {M₀ : ℝ} (hW : ∀ w : ℂ, 0 < w.re → ‖W w‖ ≤ M₀) {u : ℝ} (hu : 0 < u)
    (v : ℝ) (s : ℂ) :
    ‖limInt W u v s‖ ≤ M₀ * Real.exp (Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u -
      Real.pi ^ 2 * u * v ^ 2 / 12 - Real.pi ^ 2 * s.im * v) := by
  unfold limInt
  rw [norm_mul, Complex.norm_exp, mul_comm]
  have hre : (((Real.pi ^ 2 / 36 : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 3 +
      (Real.pi ^ 2 : ℂ) * s * ((u : ℂ) + (v : ℂ) * Complex.I))).re =
      Real.pi ^ 2 * u ^ 3 / 36 + Real.pi ^ 2 * s.re * u -
      Real.pi ^ 2 * u * v ^ 2 / 12 - Real.pi ^ 2 * s.im * v := by
    have h3 := re_cube_line u v
    have e1 : (Real.pi ^ 2 / 36 : ℂ) = ((Real.pi ^ 2 / 36 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (Real.pi ^ 2 : ℂ) = ((Real.pi ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hpr : ((Real.pi : ℂ) ^ 2).re = Real.pi ^ 2 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
    have hpi : ((Real.pi : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
    rw [Complex.add_re, e1, Complex.re_ofReal_mul, h3]
    simp [Complex.mul_re, Complex.mul_im, hpr, hpi]; ring
  rw [hre]
  gcongr
  exact hW _ (by simpa using hu)

/-- info: 'FormalResearch.SignUncertainty.norm_limInt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_limInt_le

end FormalResearch.SignUncertainty
