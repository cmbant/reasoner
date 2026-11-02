import FormalResearch.FourQubitEntropy.CriticalOrbitIdentity
import FormalResearch.FourQubitEntropy.CriticalOrbitPhi

/-!
# Null-critical states: the two auxiliary Bloch spheres (`eq:fqe-null-critical-bloch`)

Paper E, `critical_orbit_stability.tex`, `thm:fqe-critical-orbit-sharp`, null-critical refinement
`eq:fqe-null-critical-sharp`.  For a critical normal vector `v` (`Gv v`) with `Σ v_k² = 0` the auxiliary
two-qubit vector `w = B v` has coefficient matrix of determinant `Σ v_k²/2 = 0`, so `w = a ⊗ b`; the Bloch
vectors `r, s` of `a, b` give the closed forms of the paper:

* `|v_j|² = (1 + Σ_α χ_{jα} r_α s_α)/4` (`normSq_vOf`),
* `Q = 1/2 + (27/2) r₁r₂r₃ s₁s₂s₃` (`Qv_vOf`),
* each of the 32 overlaps `q_η = |⟨η, v⟩|²` equals `(1 + ε·r/√3)(1 + η'·s/√3)/4` for the cube-vertex pair
  `(ε, η')` of opposite parity attached to `η` (`qH_vOf`).

All identities are exact polynomial identities (`ring`); the existence of the factorisation is
`exists_vOf`.
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- `√2 · v`, where `v = B† (a ⊗ b)` is the critical normal vector of the product `a ⊗ b`
(`a = (a0,a1)`, `b = (b0,b1)`) in the magic basis. -/
def uOf (a0 a1 b0 b1 : ℂ) : V := fun k =>
  match k with
  | (0, 0) => a0 * b0 + a1 * b1
  | (0, 1) => -Complex.I * (a0 * b1 + a1 * b0)
  | (1, 0) => a0 * b1 - a1 * b0
  | (1, 1) => -Complex.I * (a0 * b0 - a1 * b1)

/-- The critical normal vector `v = B† (a ⊗ b)`, with `v = rt • u`. -/
noncomputable def vOf (a0 a1 b0 b1 : ℂ) : V := fun k => rt * uOf a0 a1 b0 b1 k

/-- Unnormalised Bloch vector of `(a0, a1)`. -/
def bl (a0 a1 : ℂ) : Fin 3 → ℝ :=
  ![2 * (a0.re * a1.re + a0.im * a1.im), 2 * (a0.re * a1.im - a0.im * a1.re),
    Complex.normSq a0 - Complex.normSq a1]

theorem rt_re : rt.re = (Real.sqrt 2)⁻¹ := by unfold rt; exact Complex.ofReal_re _
theorem rt_im : rt.im = 0 := by unfold rt; exact Complex.ofReal_im _

theorem rt_sq : rt.re * rt.re = 1 / 2 := by
  rw [rt_re]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith

theorem normSq_rt : Complex.normSq rt = 1 / 2 := by
  rw [Complex.normSq_apply, rt_im, rt_sq]; ring

theorem normSq_vOf (a0 a1 b0 b1 : ℂ) (k : Fin 2 × Fin 2) :
    Complex.normSq (vOf a0 a1 b0 b1 k) = 1 / 2 * Complex.normSq (uOf a0 a1 b0 b1 k) := by
  simp only [vOf, Complex.normSq_mul, normSq_rt]

theorem cvv (a0 a1 b0 b1 : ℂ) (i j : Fin 2 × Fin 2) :
    (vOf a0 a1 b0 b1 i).re * (vOf a0 a1 b0 b1 j).re + (vOf a0 a1 b0 b1 i).im * (vOf a0 a1 b0 b1 j).im
      = 1 / 2 * ((uOf a0 a1 b0 b1 i).re * (uOf a0 a1 b0 b1 j).re +
          (uOf a0 a1 b0 b1 i).im * (uOf a0 a1 b0 b1 j).im) := by
  simp only [vOf, Complex.mul_re, Complex.mul_im, rt_im]
  have := rt_sq
  linear_combination ((uOf a0 a1 b0 b1 i).re * (uOf a0 a1 b0 b1 j).re +
          (uOf a0 a1 b0 b1 i).im * (uOf a0 a1 b0 b1 j).im) * this

theorem normSq_vOf_00 (a0 a1 b0 b1 : ℂ) :
    Complex.normSq (vOf a0 a1 b0 b1 (0, 0)) = (1 / 4) * ((Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1) + bl a0 a1 0 * bl b0 b1 0 - bl a0 a1 1 * bl b0 b1 1 + bl a0 a1 2 * bl b0 b1 2) := by
  rw [normSq_vOf]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem normSq_vOf_01 (a0 a1 b0 b1 : ℂ) :
    Complex.normSq (vOf a0 a1 b0 b1 (0, 1)) = (1 / 4) * ((Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1) + bl a0 a1 0 * bl b0 b1 0 + bl a0 a1 1 * bl b0 b1 1 - bl a0 a1 2 * bl b0 b1 2) := by
  rw [normSq_vOf]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem normSq_vOf_10 (a0 a1 b0 b1 : ℂ) :
    Complex.normSq (vOf a0 a1 b0 b1 (1, 0)) = (1 / 4) * ((Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1) - bl a0 a1 0 * bl b0 b1 0 - bl a0 a1 1 * bl b0 b1 1 - bl a0 a1 2 * bl b0 b1 2) := by
  rw [normSq_vOf]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem normSq_vOf_11 (a0 a1 b0 b1 : ℂ) :
    Complex.normSq (vOf a0 a1 b0 b1 (1, 1)) = (1 / 4) * ((Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1) - bl a0 a1 0 * bl b0 b1 0 + bl a0 a1 1 * bl b0 b1 1 + bl a0 a1 2 * bl b0 b1 2) := by
  rw [normSq_vOf]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem cvv_vOf_00_01 (a0 a1 b0 b1 : ℂ) :
    (vOf a0 a1 b0 b1 (0, 0)).re * (vOf a0 a1 b0 b1 (0, 1)).re +
      (vOf a0 a1 b0 b1 (0, 0)).im * (vOf a0 a1 b0 b1 (0, 1)).im =
    (1 / 4) * (bl a0 a1 1 * bl b0 b1 2 + bl a0 a1 2 * bl b0 b1 1) := by
  rw [cvv]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem cvv_vOf_00_10 (a0 a1 b0 b1 : ℂ) :
    (vOf a0 a1 b0 b1 (0, 0)).re * (vOf a0 a1 b0 b1 (1, 0)).re +
      (vOf a0 a1 b0 b1 (0, 0)).im * (vOf a0 a1 b0 b1 (1, 0)).im =
    (1 / 4) * (-bl a0 a1 0 * bl b0 b1 2 + bl a0 a1 2 * bl b0 b1 0) := by
  rw [cvv]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem cvv_vOf_00_11 (a0 a1 b0 b1 : ℂ) :
    (vOf a0 a1 b0 b1 (0, 0)).re * (vOf a0 a1 b0 b1 (1, 1)).re +
      (vOf a0 a1 b0 b1 (0, 0)).im * (vOf a0 a1 b0 b1 (1, 1)).im =
    (1 / 4) * (-bl a0 a1 0 * bl b0 b1 1 - bl a0 a1 1 * bl b0 b1 0) := by
  rw [cvv]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem cvv_vOf_01_10 (a0 a1 b0 b1 : ℂ) :
    (vOf a0 a1 b0 b1 (0, 1)).re * (vOf a0 a1 b0 b1 (1, 0)).re +
      (vOf a0 a1 b0 b1 (0, 1)).im * (vOf a0 a1 b0 b1 (1, 0)).im =
    (1 / 4) * (-bl a0 a1 0 * bl b0 b1 1 + bl a0 a1 1 * bl b0 b1 0) := by
  rw [cvv]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem cvv_vOf_01_11 (a0 a1 b0 b1 : ℂ) :
    (vOf a0 a1 b0 b1 (0, 1)).re * (vOf a0 a1 b0 b1 (1, 1)).re +
      (vOf a0 a1 b0 b1 (0, 1)).im * (vOf a0 a1 b0 b1 (1, 1)).im =
    (1 / 4) * (bl a0 a1 0 * bl b0 b1 2 + bl a0 a1 2 * bl b0 b1 0) := by
  rw [cvv]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem cvv_vOf_10_11 (a0 a1 b0 b1 : ℂ) :
    (vOf a0 a1 b0 b1 (1, 0)).re * (vOf a0 a1 b0 b1 (1, 1)).re +
      (vOf a0 a1 b0 b1 (1, 0)).im * (vOf a0 a1 b0 b1 (1, 1)).im =
    (1 / 4) * (bl a0 a1 1 * bl b0 b1 2 - bl a0 a1 2 * bl b0 b1 1) := by
  rw [cvv]
  simp only [uOf, bl, Complex.normSq_apply]
  simp
  ring

theorem Nv_vOf (a0 a1 b0 b1 : ℂ) :
    Nv (vOf a0 a1 b0 b1) = (Complex.normSq a0 + Complex.normSq a1) * (Complex.normSq b0 + Complex.normSq b1) := by
  simp only [Nv, Fintype.sum_prod_type, Fin.sum_univ_two, normSq_vOf_00, normSq_vOf_01, normSq_vOf_10,
    normSq_vOf_11]
  ring

/-- **`Q = 1/2 + (27/2) r₁r₂r₃ s₁s₂s₃`** (`eq:fqe-null-critical-bloch`) for the product vector
`v = B†(a ⊗ b)` with unit `a, b`. -/
theorem Qv_vOf (a0 a1 b0 b1 : ℂ) (ha : Complex.normSq a0 + Complex.normSq a1 = 1)
    (hb : Complex.normSq b0 + Complex.normSq b1 = 1) :
    Qv (vOf a0 a1 b0 b1) = 1 / 2 + 27 / 2 * (bl a0 a1 0 * bl a0 a1 1 * bl a0 a1 2) *
      (bl b0 b1 0 * bl b0 b1 1 * bl b0 b1 2) := by
  rw [Qv_three_term, Nv_vOf, ha, hb]
  simp only [normSq_vOf_00, normSq_vOf_01, normSq_vOf_10, normSq_vOf_11, cvv_vOf_00_01, cvv_vOf_00_10,
    cvv_vOf_00_11, cvv_vOf_01_10, cvv_vOf_01_11, cvv_vOf_10_11, ha, hb]
  ring

end FormalResearch.FourQubitEntropy.CO
