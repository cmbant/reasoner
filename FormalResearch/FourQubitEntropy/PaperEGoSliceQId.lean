module

public import FormalResearch.FourQubitEntropy.PaperEGoSliceMain

/-!
# `eq:fqe-global-intrinsic`: `Q` of a state from its magic matrix (general `Z`)

The adjugate route to `sexticQ (ψ_Z) = 27 n tr[(ZZ†)²] - 18 tr[(ZZ†)³] - 18 ‖ZZᵀZ - sZ/2‖² - 4 n³`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

abbrev M4C := Matrix (Fin 4) (Fin 4) ℂ

theorem trace_adj_fin4 (A : M4C) :
    6 * Matrix.trace A.adjugate = Matrix.trace A ^ 3 - 3 * Matrix.trace A * Matrix.trace (A * A) +
      2 * Matrix.trace (A * A * A) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.adjugate_fin_succ_eq_det_submatrix,
    Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_four]
  simp [Fin.succAbove]
  ring

theorem Ipow3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
theorem Ipow4 : Complex.I ^ 4 = 1 := by rw [pow_succ, Ipow3]; simp
theorem Ipow5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, Ipow4]; simp
theorem Ipow6 : Complex.I ^ 6 = -1 := by rw [pow_succ, Ipow5]; simp

/-- `√2` times the magic basis matrix (columns `(0,0),(0,1),(1,0),(1,1)`). -/
def Bp : M4C := !![1, 0, 0, Complex.I; 0, Complex.I, 1, 0; 0, Complex.I, -1, 0; 1, 0, 0, -Complex.I]

/-- `W = B Z Bᵀ = (1/2) B' Z B'ᵀ`. -/
def Wf (Z : M4C) : M4C := (1 / 2 : ℂ) • (Bp * Z * Bpᵀ)

/-- Row/column code tables of the `13` and `14` cut matrices of a `4 × 4` array `W = zmat ψ`. -/
def r13 : Fin 4 → Fin 4 → Fin 4 := ![![0, 0, 1, 1], ![0, 0, 1, 1], ![2, 2, 3, 3], ![2, 2, 3, 3]]
def c13 : Fin 4 → Fin 4 → Fin 4 := ![![0, 1, 0, 1], ![2, 3, 2, 3], ![0, 1, 0, 1], ![2, 3, 2, 3]]
def c14 : Fin 4 → Fin 4 → Fin 4 := ![![0, 2, 0, 2], ![1, 3, 1, 3], ![0, 2, 0, 2], ![1, 3, 1, 3]]

def M13f (Z : M4C) : M4C := Matrix.of fun i j => Wf Z (r13 i j) (c13 i j)
def M14f (Z : M4C) : M4C := Matrix.of fun i j => Wf Z (r13 i j) (c14 i j)

/-- `N = Z Zᵀ Z - (tr ZᵀZ / 2) Z`. -/
def Nf (Z : M4C) : M4C := Z * Zᵀ * Z - (Matrix.trace (Zᵀ * Z) / 2) • Z

def alpha13 (a n : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![((1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 0 + ((-1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 0 + ((-1/4 : ℝ) : ℂ) * n 3 3, (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 0 + ((-1/4 : ℝ) : ℂ) * a 1 3 + ((-1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((-1/4 : ℝ) : ℂ) * n 0 2 + ((-1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 2, (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 1 + ((-1/4 : ℝ) : ℂ) * a 0 2 + ((-1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((-1/4 : ℝ) : ℂ) * n 1 3 + ((-1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 3, ((-1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 1 + ((1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 1 + ((1/4 : ℝ) : ℂ) * n 2 2;
     (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 0 + ((-1/4 : ℝ) : ℂ) * a 1 3 + ((1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((1/4 : ℝ) : ℂ) * n 0 2 + ((-1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 2, ((1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 0 + ((1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 0 + ((1/4 : ℝ) : ℂ) * n 3 3, ((-1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 1 + ((-1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 1 + ((-1/4 : ℝ) : ℂ) * n 2 2, (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 1 + ((-1/4 : ℝ) : ℂ) * a 0 2 + ((1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((1/4 : ℝ) : ℂ) * n 1 3 + ((-1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 3;
     (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 1 + ((1/4 : ℝ) : ℂ) * a 0 2 + ((-1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((-1/4 : ℝ) : ℂ) * n 1 3 + ((1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 3, ((-1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 1 + ((-1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 1 + ((-1/4 : ℝ) : ℂ) * n 2 2, ((1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 0 + ((1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 0 + ((1/4 : ℝ) : ℂ) * n 3 3, (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 0 + ((1/4 : ℝ) : ℂ) * a 1 3 + ((-1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((-1/4 : ℝ) : ℂ) * n 0 2 + ((1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 2;
     ((-1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 1 + ((1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 1 + ((1/4 : ℝ) : ℂ) * n 2 2, (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 1 + ((1/4 : ℝ) : ℂ) * a 0 2 + ((1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((1/4 : ℝ) : ℂ) * n 1 3 + ((1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 3, (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 0 + ((1/4 : ℝ) : ℂ) * a 1 3 + ((1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((1/4 : ℝ) : ℂ) * n 0 2 + ((1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 2, ((1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 0 + ((-1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 0 + ((-1/4 : ℝ) : ℂ) * n 3 3]

def alpha14 (a n : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![((-1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 0 + ((1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 0 + ((-1/4 : ℝ) : ℂ) * n 3 3, (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 0 + ((1/4 : ℝ) : ℂ) * a 1 3 + ((-1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((1/4 : ℝ) : ℂ) * n 0 2 + ((-1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 2, (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 1 + ((1/4 : ℝ) : ℂ) * a 0 2 + ((1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((-1/4 : ℝ) : ℂ) * n 1 3 + ((-1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 3, ((1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 1 + ((1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 1 + ((-1/4 : ℝ) : ℂ) * n 2 2;
     (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 0 + ((1/4 : ℝ) : ℂ) * a 1 3 + ((1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((-1/4 : ℝ) : ℂ) * n 0 2 + ((-1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 2, ((-1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 0 + ((-1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 0 + ((1/4 : ℝ) : ℂ) * n 3 3, ((1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 1 + ((-1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 1 + ((1/4 : ℝ) : ℂ) * n 2 2, (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 1 + ((1/4 : ℝ) : ℂ) * a 0 2 + ((-1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((1/4 : ℝ) : ℂ) * n 1 3 + ((-1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 3;
     (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 1 + ((-1/4 : ℝ) : ℂ) * a 0 2 + ((1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((-1/4 : ℝ) : ℂ) * n 1 3 + ((1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 3, ((1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 1 + ((-1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 1 + ((1/4 : ℝ) : ℂ) * n 2 2, ((-1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 3 0 + ((-1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 0 + ((1/4 : ℝ) : ℂ) * n 3 3, (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 0 + ((-1/4 : ℝ) : ℂ) * a 1 3 + ((-1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((1/4 : ℝ) : ℂ) * n 0 2 + ((1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 2;
     ((1/4 : ℝ) : ℂ) * a 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 2 1 + ((1/4 : ℝ) : ℂ) * a 2 2 + ((-1/4 : ℝ) : ℂ) * n 1 1 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 1 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 2 1 + ((-1/4 : ℝ) : ℂ) * n 2 2, (Complex.I * ((1/4 : ℝ) : ℂ)) * a 0 1 + ((-1/4 : ℝ) : ℂ) * a 0 2 + ((-1/4 : ℝ) : ℂ) * a 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 2 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 1 0 + ((1/4 : ℝ) : ℂ) * n 1 3 + ((1/4 : ℝ) : ℂ) * n 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 2 3, (Complex.I * ((1/4 : ℝ) : ℂ)) * a 1 0 + ((-1/4 : ℝ) : ℂ) * a 1 3 + ((1/4 : ℝ) : ℂ) * a 2 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * a 2 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 0 1 + ((-1/4 : ℝ) : ℂ) * n 0 2 + ((1/4 : ℝ) : ℂ) * n 3 1 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * n 3 2, ((-1/4 : ℝ) : ℂ) * a 0 0 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 0 3 + (Complex.I * ((-1/4 : ℝ) : ℂ)) * a 3 0 + ((1/4 : ℝ) : ℂ) * a 3 3 + ((1/4 : ℝ) : ℂ) * n 0 0 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 0 3 + (Complex.I * ((1/4 : ℝ) : ℂ)) * n 3 0 + ((-1/4 : ℝ) : ℂ) * n 3 3]


theorem adj13_eq (Z : M4C) : (M13f Z).adjugate = alpha13 Z.adjugate (Nf Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [alpha13]
     simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three]
     simp only [M13f, Wf, Nf, Matrix.of_apply, Matrix.submatrix_apply, Matrix.smul_apply,
       Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, Fin.sum_univ_four, Matrix.trace,
       Matrix.diag_apply, smul_eq_mul]
     simp [Bp, r13, c13, c14, Fin.succAbove]
     ring_nf
     simp only [Complex.I_sq, Ipow3, Ipow4, Ipow5, Ipow6]
     ring_nf)

theorem adj14_eq (Z : M4C) : (M14f Z).adjugate = alpha14 Z.adjugate (Nf Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [alpha14]
     simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three]
     simp only [M14f, Wf, Nf, Matrix.of_apply, Matrix.submatrix_apply, Matrix.smul_apply,
       Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, Fin.sum_univ_four, Matrix.trace,
       Matrix.diag_apply, smul_eq_mul]
     simp [Bp, r13, c13, c14, Fin.succAbove]
     ring_nf
     simp only [Complex.I_sq, Ipow3, Ipow4, Ipow5, Ipow6]
     ring_nf)

theorem quad_identity (a n : M4C) :
    ∑ i, ∑ j, Complex.normSq (alpha13 a n i j) + ∑ i, ∑ j, Complex.normSq (alpha14 a n i j) =
      (1 / 2) * (∑ i, ∑ j, Complex.normSq (a i j) + ∑ i, ∑ j, Complex.normSq (n i j)) := by
  simp only [alpha13, alpha14, Fin.sum_univ_four, Complex.normSq_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

end

end FormalResearch.FourQubitEntropy.GO
