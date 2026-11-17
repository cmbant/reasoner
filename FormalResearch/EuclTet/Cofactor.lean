module

public import Mathlib
public import FormalResearch.EuclTet.Gram

/-!
# Cayley--Menger cofactors of a tetrahedron

Sources: Weyl/P5 `cayley_menger_trichotomy.tex`, `thm:smooth` (`eq:dD`: `∂D/∂x_{ij} = 2 cof_{ij}(M)`),
`thm:sin2` (`eq:sin2`: `f₁f₂ - n² = x_{ij} det CM / 8`), `eq:gramcos`; Weyl/P3 `lem:racah-cayley-menger`.

Notation: `x_{ij}` are the six squared edge lengths of the vertices `0,1,2,3`, `M = cmMat2 x` the
bordered `5×5` Cayley--Menger matrix (border = index `0`, vertex `v` = index `v+1`), `D = det M`.
`C_{ij}` (`i,j ∈ {0,..,3}`) is the cofactor of the entry `(i+1, j+1)` of `M`, i.e.
`adjugate M (i+1) (j+1)` (the adjugate of the symmetric `M` is symmetric).  `C_{ii}` is the
bordered Cayley--Menger determinant of the face opposite the vertex `i`.

## What is formalised (exact, polynomial identities in the six `x`)

* `cofM x : Matrix (Fin 4) (Fin 4) ℝ` with explicit entries; `cofM_eq_adjugate`: `cofM x i j =
  adjugate (cmMat2 x) (i+1) (j+1)`.
* `cofM_row_sum`: `∑_j C_{ij} = 0` (the vertex block of `adj M · (0,1,1,1,1)ᵀ = D e₀`; the algebraic
  form of "the four area vectors sum to zero", see `FormalResearch.EuclTet.AreaVec`).
* `cofM_diag_eq`: `C_{ii} = -(2(ab+bc+ca) - a² - b² - c²) ` for the three squared edges `a,b,c` of
  the opposite face (`-16 ·` squared area, Heron: `cofM00_eq_heron`).
* `cofM_jacobi_*` (**`eq:sin2`, Jacobi's complementary-minor identity**): for the two faces `i,j` that
  share the edge `kl`, `C_{ii} C_{jj} - C_{ij}² = 2 x_{kl} D`.
* `hasDerivAt_cmDet2_*` (**`eq:dD`**): `∂D/∂x_{ij} = 2 C_{ij}` for each of the six edges.

## Not formalised

The planar wall formula `C_ij = -16 λ_iλ_j` (`eq:dDlambda`) is in
`FormalResearch.EuclTet.Radon` (vertex block and kernel only; the border row/column of `adj M = c v vᵀ` and
corank exactly one are not formalised); Hypothesis `hyp:faces` and the wall `det CM = 0` as a stratified
set are not formalised as sets.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Matrix

/-- Cofactor `C_00` of the Cayley--Menger matrix (vertex block). -/
def cof00 (_x01 _x02 _x03 x12 x13 x23 : ℝ) : ℝ :=
  x12^2 - 2*x12*x13 - 2*x12*x23 + x13^2 - 2*x13*x23 + x23^2

/-- Cofactor `C_01` of the Cayley--Menger matrix (vertex block). -/
def cof01 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  -2*x01*x23 - x02*x12 + x02*x13 + x02*x23 + x03*x12 - x03*x13 + x03*x23 + x12*x23 + x13*x23 - x23^2

/-- Cofactor `C_02` of the Cayley--Menger matrix (vertex block). -/
def cof02 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  -x01*x12 + x01*x13 + x01*x23 - 2*x02*x13 + x03*x12 + x03*x13 - x03*x23 + x12*x13 - x13^2 + x13*x23

/-- Cofactor `C_03` of the Cayley--Menger matrix (vertex block). -/
def cof03 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  x01*x12 - x01*x13 + x01*x23 + x02*x12 + x02*x13 - x02*x23 - 2*x03*x12 - x12^2 + x12*x13 + x12*x23

/-- Cofactor `C_11` of the Cayley--Menger matrix (vertex block). -/
def cof11 (_x01 x02 x03 _x12 _x13 x23 : ℝ) : ℝ :=
  x02^2 - 2*x02*x03 - 2*x02*x23 + x03^2 - 2*x03*x23 + x23^2

/-- Cofactor `C_12` of the Cayley--Menger matrix (vertex block). -/
def cof12 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  -x01*x02 + x01*x03 + x01*x23 + x02*x03 + x02*x13 - x03^2 - 2*x03*x12 + x03*x13 + x03*x23 - x13*x23

/-- Cofactor `C_13` of the Cayley--Menger matrix (vertex block). -/
def cof13 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  x01*x02 - x01*x03 + x01*x23 - x02^2 + x02*x03 + x02*x12 - 2*x02*x13 + x02*x23 + x03*x12 - x12*x23

/-- Cofactor `C_22` of the Cayley--Menger matrix (vertex block). -/
def cof22 (x01 _x02 x03 _x12 x13 _x23 : ℝ) : ℝ :=
  x01^2 - 2*x01*x03 - 2*x01*x13 + x03^2 - 2*x03*x13 + x13^2

/-- Cofactor `C_23` of the Cayley--Menger matrix (vertex block). -/
def cof23 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  -x01^2 + x01*x02 + x01*x03 + x01*x12 + x01*x13 - 2*x01*x23 - x02*x03 + x02*x13 + x03*x12 - x12*x13

/-- Cofactor `C_33` of the Cayley--Menger matrix (vertex block). -/
def cof33 (x01 x02 _x03 x12 _x13 _x23 : ℝ) : ℝ :=
  x01^2 - 2*x01*x02 - 2*x01*x12 + x02^2 - 2*x02*x12 + x12^2

/-- The vertex block of the Cayley--Menger adjugate. -/
def cofM (x01 x02 x03 x12 x13 x23 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![cof00 x01 x02 x03 x12 x13 x23, cof01 x01 x02 x03 x12 x13 x23,
      cof02 x01 x02 x03 x12 x13 x23, cof03 x01 x02 x03 x12 x13 x23;
     cof01 x01 x02 x03 x12 x13 x23, cof11 x01 x02 x03 x12 x13 x23,
      cof12 x01 x02 x03 x12 x13 x23, cof13 x01 x02 x03 x12 x13 x23;
     cof02 x01 x02 x03 x12 x13 x23, cof12 x01 x02 x03 x12 x13 x23,
      cof22 x01 x02 x03 x12 x13 x23, cof23 x01 x02 x03 x12 x13 x23;
     cof03 x01 x02 x03 x12 x13 x23, cof13 x01 x02 x03 x12 x13 x23,
      cof23 x01 x02 x03 x12 x13 x23, cof33 x01 x02 x03 x12 x13 x23]

theorem cofM_eq_adjugate (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) :
    cofM x01 x02 x03 x12 x13 x23 i j = (cmMat2 x01 x02 x03 x12 x13 x23).adjugate i.succ j.succ := by
  fin_cases i <;> fin_cases j <;>
    simp [cofM, cmMat2, Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Fin.succAbove, cof00, cof01, cof02, cof03, cof11, cof12, cof13, cof22,
      cof23, cof33] <;> ring


/-- Row sums of the vertex block vanish. -/
theorem cofM_row_sum (x01 x02 x03 x12 x13 x23 : ℝ) (i : Fin 4) :
    ∑ j, cofM x01 x02 x03 x12 x13 x23 i j = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, cofM, cof00, cof01, cof02, cof03, cof11, cof12, cof13, cof22, cof23,
      cof33] <;> ring

/-- Heron form: `C_{00} = -(2(ab+bc+ca) - a² - b² - c²)` with `a,b,c = x12,x13,x23`. -/
theorem cof00_eq_heron (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof00 x01 x02 x03 x12 x13 x23 = -(2 * (x12 * x13 + x13 * x23 + x23 * x12) - x12 ^ 2 - x13 ^ 2 - x23 ^ 2) := by
  unfold cof00; ring

theorem cof11_eq_heron (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof11 x01 x02 x03 x12 x13 x23 = -(2 * (x02 * x03 + x03 * x23 + x23 * x02) - x02 ^ 2 - x03 ^ 2 - x23 ^ 2) := by
  unfold cof11; ring

theorem cof22_eq_heron (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof22 x01 x02 x03 x12 x13 x23 = -(2 * (x01 * x03 + x03 * x13 + x13 * x01) - x01 ^ 2 - x03 ^ 2 - x13 ^ 2) := by
  unfold cof22; ring

theorem cof33_eq_heron (x01 x02 x03 x12 x13 x23 : ℝ) :
    cof33 x01 x02 x03 x12 x13 x23 = -(2 * (x01 * x02 + x02 * x12 + x12 * x01) - x01 ^ 2 - x02 ^ 2 - x12 ^ 2) := by
  unfold cof33; ring

section Jacobi

variable (x01 x02 x03 x12 x13 x23 : ℝ)

/-- **`eq:sin2`** (Jacobi's identity for the `2×2` minor of the adjugate): the faces `0,1` share
the edge `23`: `C₀₀C₁₁ - C₀₁² = 2 x₂₃ D`. -/
theorem cof_jacobi01 : cof00 x01 x02 x03 x12 x13 x23 * cof11 x01 x02 x03 x12 x13 x23
    - cof01 x01 x02 x03 x12 x13 x23 ^ 2 = 2 * x23 * cmDet2 x01 x02 x03 x12 x13 x23 := by
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cof00, cof01, cof11]; ring

theorem cof_jacobi02 : cof00 x01 x02 x03 x12 x13 x23 * cof22 x01 x02 x03 x12 x13 x23
    - cof02 x01 x02 x03 x12 x13 x23 ^ 2 = 2 * x13 * cmDet2 x01 x02 x03 x12 x13 x23 := by
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cof00, cof02, cof22]; ring

theorem cof_jacobi03 : cof00 x01 x02 x03 x12 x13 x23 * cof33 x01 x02 x03 x12 x13 x23
    - cof03 x01 x02 x03 x12 x13 x23 ^ 2 = 2 * x12 * cmDet2 x01 x02 x03 x12 x13 x23 := by
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cof00, cof03, cof33]; ring

theorem cof_jacobi12 : cof11 x01 x02 x03 x12 x13 x23 * cof22 x01 x02 x03 x12 x13 x23
    - cof12 x01 x02 x03 x12 x13 x23 ^ 2 = 2 * x03 * cmDet2 x01 x02 x03 x12 x13 x23 := by
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cof11, cof12, cof22]; ring

theorem cof_jacobi13 : cof11 x01 x02 x03 x12 x13 x23 * cof33 x01 x02 x03 x12 x13 x23
    - cof13 x01 x02 x03 x12 x13 x23 ^ 2 = 2 * x02 * cmDet2 x01 x02 x03 x12 x13 x23 := by
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cof11, cof13, cof33]; ring

theorem cof_jacobi23 : cof22 x01 x02 x03 x12 x13 x23 * cof33 x01 x02 x03 x12 x13 x23
    - cof23 x01 x02 x03 x12 x13 x23 ^ 2 = 2 * x01 * cmDet2 x01 x02 x03 x12 x13 x23 := by
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    cof22, cof23, cof33]; ring

end Jacobi

section Derivative

/-- A function equal to `c₀ + d₀ (s - x₀) + e₀ (s - x₀)²` has derivative `d₀` at `x₀`. -/
theorem hasDerivAt_of_quad {f : ℝ → ℝ} (x0 c0 d0 e0 : ℝ)
    (h : ∀ s, f s = c0 + d0 * (s - x0) + e0 * (s - x0) ^ 2) : HasDerivAt f d0 x0 := by
  have h1 : HasDerivAt (fun s : ℝ => c0 + d0 * (s - x0) + e0 * (s - x0) ^ 2) d0 x0 := by
    have h3 : HasDerivAt (fun s : ℝ => s - x0) 1 x0 := (hasDerivAt_id x0).sub_const x0
    have h4 : HasDerivAt (fun s : ℝ => (s - x0) ^ 2) (2 * (x0 - x0)) x0 := by
      refine (h3.pow 2).congr_deriv ?_
      simp
    have := ((h3.const_mul d0).const_add c0).add (h4.const_mul e0)
    refine this.congr_deriv ?_
    simp
  exact (funext h : f = _) ▸ h1

/-- **`eq:dD`** (`thm:smooth`): `∂D/∂x01 = 2 C_01`, the other five squared edges fixed. -/
theorem hasDerivAt_cmDet2_x01 (x01 x02 x03 x12 x13 x23 : ℝ) :
    HasDerivAt (fun s => cmDet2 s x02 x03 x12 x13 x23) (2 * cof01 x01 x02 x03 x12 x13 x23) x01 := by
  refine hasDerivAt_of_quad x01 (cmDet2 x01 x02 x03 x12 x13 x23) _ (-2 * x23) fun s => ?_
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cof01]
  ring

/-- **`eq:dD`** (`thm:smooth`): `∂D/∂x02 = 2 C_02`, the other five squared edges fixed. -/
theorem hasDerivAt_cmDet2_x02 (x01 x02 x03 x12 x13 x23 : ℝ) :
    HasDerivAt (fun s => cmDet2 x01 s x03 x12 x13 x23) (2 * cof02 x01 x02 x03 x12 x13 x23) x02 := by
  refine hasDerivAt_of_quad x02 (cmDet2 x01 x02 x03 x12 x13 x23) _ (-2 * x13) fun s => ?_
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cof02]
  ring

/-- **`eq:dD`** (`thm:smooth`): `∂D/∂x03 = 2 C_03`, the other five squared edges fixed. -/
theorem hasDerivAt_cmDet2_x03 (x01 x02 x03 x12 x13 x23 : ℝ) :
    HasDerivAt (fun s => cmDet2 x01 x02 s x12 x13 x23) (2 * cof03 x01 x02 x03 x12 x13 x23) x03 := by
  refine hasDerivAt_of_quad x03 (cmDet2 x01 x02 x03 x12 x13 x23) _ (-2 * x12) fun s => ?_
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cof03]
  ring

/-- **`eq:dD`** (`thm:smooth`): `∂D/∂x12 = 2 C_12`, the other five squared edges fixed. -/
theorem hasDerivAt_cmDet2_x12 (x01 x02 x03 x12 x13 x23 : ℝ) :
    HasDerivAt (fun s => cmDet2 x01 x02 x03 s x13 x23) (2 * cof12 x01 x02 x03 x12 x13 x23) x12 := by
  refine hasDerivAt_of_quad x12 (cmDet2 x01 x02 x03 x12 x13 x23) _ (-2 * x03) fun s => ?_
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cof12]
  ring

/-- **`eq:dD`** (`thm:smooth`): `∂D/∂x13 = 2 C_13`, the other five squared edges fixed. -/
theorem hasDerivAt_cmDet2_x13 (x01 x02 x03 x12 x13 x23 : ℝ) :
    HasDerivAt (fun s => cmDet2 x01 x02 x03 x12 s x23) (2 * cof13 x01 x02 x03 x12 x13 x23) x13 := by
  refine hasDerivAt_of_quad x13 (cmDet2 x01 x02 x03 x12 x13 x23) _ (-2 * x02) fun s => ?_
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cof13]
  ring

/-- **`eq:dD`** (`thm:smooth`): `∂D/∂x23 = 2 C_23`, the other five squared edges fixed. -/
theorem hasDerivAt_cmDet2_x23 (x01 x02 x03 x12 x13 x23 : ℝ) :
    HasDerivAt (fun s => cmDet2 x01 x02 x03 x12 x13 s) (2 * cof23 x01 x02 x03 x12 x13 x23) x23 := by
  refine hasDerivAt_of_quad x23 (cmDet2 x01 x02 x03 x12 x13 x23) _ (-2 * x01) fun s => ?_
  simp [cmDet2, cmMat2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cof23]
  ring

end Derivative

/-- info: 'FormalResearch.EuclTet.cofM_eq_adjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofM_eq_adjugate

/-- info: 'FormalResearch.EuclTet.cofM_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofM_row_sum

/-- info: 'FormalResearch.EuclTet.cof_jacobi01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi01

/-- info: 'FormalResearch.EuclTet.cof_jacobi02' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi02

/-- info: 'FormalResearch.EuclTet.cof_jacobi03' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi03

/-- info: 'FormalResearch.EuclTet.cof_jacobi12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi12

/-- info: 'FormalResearch.EuclTet.cof_jacobi13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi13

/-- info: 'FormalResearch.EuclTet.cof_jacobi23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cof_jacobi23

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x01

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x02' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x02

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x03' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x03

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x12

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x13

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x23

end FormalResearch.EuclTet
