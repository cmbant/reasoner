module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The `s`-derivative of the rescaled Mellin kernel (`lem:radial-compactness`, Step 3)

`CFT/sign_uncertainty/paper/fourier_mellin_proofs.tex`, proof of `lem:radial-compactness`, Step 3:
with `ε_c = c^{-1/3}`, `ξ_c(s) = 1/π² + ε_c² s` and
`K_c(w,s) = Γ(c(1 - ε_c w)) Γ(c)^{-1} (2π c ξ_c(s))^{c ε_c w} e^{c ℋ(ε_c w)}`,
the identity `∂_s (ξ_c^{-1} K_c(w,s)) = ξ_c^{-1} (w - ε_c²) ξ_c^{-1} K_c(w,s)` (which uses `c ε_c³ = 1`),
`hasDerivAt_xi_inv_radialKernel`.  The function `ℋ` enters only through the `s`-independent factor
`e^{c ℋ(ε_c w)}`, so it is a parameter `H : ℂ → ℂ` here.  Only the kernel identity is formalised: the
Montel/dominated-convergence argument that uses it is not.
-/

@[expose] public section

open Complex
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `ε_c = c^{-1/3}`. -/
noncomputable def radialEps (c : ℝ) : ℝ := c ^ (-(1 / 3 : ℝ))

/-- `ξ_c(s) = 1/π² + ε_c² s`. -/
noncomputable def radialXi (c s : ℝ) : ℝ := 1 / π ^ 2 + radialEps c ^ 2 * s

lemma radialEps_pos {c : ℝ} (hc : 0 < c) : 0 < radialEps c := Real.rpow_pos_of_pos hc _

/-- `c ε_c³ = 1`. -/
lemma radialEps_cube {c : ℝ} (hc : 0 < c) : c * radialEps c ^ 3 = 1 := by
  unfold radialEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num
  rw [Real.rpow_neg_one]
  exact mul_inv_cancel₀ hc.ne'

/-- The kernel `K_c(w, s)` of Step 3, with `ℋ` a parameter. -/
noncomputable def radialKernel (c : ℝ) (H : ℂ → ℂ) (w : ℂ) (s : ℝ) : ℂ :=
  Complex.Gamma (c * (1 - radialEps c * w)) / Complex.Gamma c *
    ((2 * π * c * radialXi c s : ℝ) : ℂ) ^ ((c : ℂ) * radialEps c * w) *
    Complex.exp (c * H (radialEps c * w))

/-- **Step 3 kernel identity** (`lem:radial-compactness`): where `ξ_c(s) > 0`,
`∂_s (ξ_c^{-1} K_c(w,s)) = ξ_c^{-1} (w - ε_c²) ξ_c^{-1} K_c(w,s)`. -/
theorem hasDerivAt_xi_inv_radialKernel {c : ℝ} (hc : 0 < c) (H : ℂ → ℂ) (w : ℂ) {s : ℝ}
    (hs : 0 < radialXi c s) :
    HasDerivAt (fun s : ℝ => ((radialXi c s : ℝ) : ℂ)⁻¹ * radialKernel c H w s)
      (((radialXi c s : ℝ) : ℂ)⁻¹ * (w - ((radialEps c ^ 2 : ℝ) : ℂ)) *
        (((radialXi c s : ℝ) : ℂ)⁻¹ * radialKernel c H w s)) s := by
  set ε : ℝ := radialEps c with hε
  have hε0 : 0 < ε := radialEps_pos hc
  have hcube : (c : ℂ) * (ε : ℂ) ^ 3 = 1 := by exact_mod_cast radialEps_cube hc
  set B : ℂ := Complex.Gamma (c * (1 - ε * w)) / Complex.Gamma c *
    Complex.exp (c * H (ε * w)) with hB
  set p : ℂ := (c : ℂ) * ε * w with hp
  -- complex-variable version
  let ξC : ℂ → ℂ := fun z => 1 / (π : ℂ) ^ 2 + (ε : ℂ) ^ 2 * z
  let QC : ℂ → ℂ := fun z => 2 * π * c * ξC z
  have hξC : ∀ z, HasDerivAt ξC ((ε : ℂ) ^ 2) z := fun z => by
    exact (((hasDerivAt_id z).const_mul ((ε : ℂ) ^ 2)).const_add (1 / (π : ℂ) ^ 2)).congr_deriv
      (by ring)
  have hξs : ξC (s : ℂ) = ((radialXi c s : ℝ) : ℂ) := by
    simp [ξC, radialXi, hε]
  have hQs : QC (s : ℂ) = ((2 * π * c * radialXi c s : ℝ) : ℂ) := by
    simp only [QC, hξs]; push_cast; ring
  have hxipos : (radialXi c s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hQpos : 0 < 2 * π * c * radialXi c s := by positivity
  have hQne : QC (s : ℂ) ≠ 0 := by
    rw [hQs]; exact_mod_cast hQpos.ne'
  have hQslit : QC (s : ℂ) ∈ slitPlane := by
    rw [hQs]; exact ofReal_mem_slitPlane.2 hQpos
  have hQ' : HasDerivAt QC (2 * π * c * (ε : ℂ) ^ 2) (s : ℂ) := by
    simpa [QC, mul_assoc] using (hξC (s : ℂ)).const_mul (2 * (π : ℂ) * c)
  have hpow := (hQ'.cpow_const (c := p) hQslit)
  have hfull : HasDerivAt (fun z : ℂ => (ξC z)⁻¹ * (B * QC z ^ p))
      (-((ε : ℂ) ^ 2) / (ξC (s : ℂ)) ^ 2 * (B * QC (s : ℂ) ^ p) +
        (ξC (s : ℂ))⁻¹ * (B * (p * QC (s : ℂ) ^ (p - 1) * (2 * π * c * (ε : ℂ) ^ 2)))) (s : ℂ) := by
    have hxne : ξC (s : ℂ) ≠ 0 := by rw [hξs]; exact hxipos
    have h1 := ((hξC (s : ℂ)).inv hxne).mul ((hpow.const_mul B))
    convert h1 using 1
  have hreal := hfull.comp_ofReal
  have hfun : (fun s : ℝ => ((radialXi c s : ℝ) : ℂ)⁻¹ * radialKernel c H w s) =
      fun y : ℝ => (ξC (y : ℂ))⁻¹ * (B * QC (y : ℂ) ^ p) := by
    funext y
    have e1 : ξC (y : ℂ) = ((radialXi c y : ℝ) : ℂ) := by simp [ξC, radialXi, hε]
    have e2 : QC (y : ℂ) = ((2 * π * c * radialXi c y : ℝ) : ℂ) := by
      simp only [QC, e1]; push_cast; ring
    rw [e1, e2, radialKernel, hB]
    ring
  rw [hfun]
  refine hreal.congr_deriv ?_
  have hxne : ξC (s : ℂ) ≠ 0 := by rw [hξs]; exact hxipos
  have hK : radialKernel c H w s = B * QC (s : ℂ) ^ p := by
    rw [radialKernel, hB, ← hQs]; ring
  have hpe : (ε : ℂ) ^ 2 * p = w := by
    have : (ε : ℂ) ^ 2 * p = ((c : ℂ) * (ε : ℂ) ^ 3) * w := by simp only [hp]; ring
    rw [this, hcube, one_mul]
  have hQ2 : QC (s : ℂ) = 2 * π * c * ((radialXi c s : ℝ) : ℂ) := by simp only [QC, hξs]
  have hπc : (2 * (π : ℂ) * c) ≠ 0 := by
    have : (0 : ℝ) < 2 * π * c := by positivity
    exact_mod_cast this.ne'
  rw [cpow_sub _ _ hQne, cpow_one, hξs, hK]
  generalize QC (s : ℂ) ^ p = P
  rw [hQ2]
  generalize ((radialXi c s : ℝ) : ℂ) = X at *
  have hε2 : (((radialEps c ^ 2 : ℝ)) : ℂ) = (ε : ℂ) ^ 2 := by push_cast; rfl
  rw [hε2, ← hpe]
  clear_value B p
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp
  ring

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_xi_inv_radialKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_xi_inv_radialKernel

end FormalResearch.SignUncertainty
