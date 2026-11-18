module

public import Mathlib
public import FormalResearch.JB.JBDefs
public import FormalResearch.MatrixAnalysis.JacobiOpPolar
public import FormalResearch.MatrixAnalysis.JacobiOpFrobenius

/-!
# Paper J, Theorem B reduction: polar repair (`lem:thb-polar`)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Lemma `lem:thb-polar`.

`jb_polar` restates the Jacobi-operator package's `jop_polar_repair_matrix` /
`jop_polar_repair_frobenius_of_close` (`FormalResearch.MatrixAnalysis`) in the paper's form: `Q` is written
`G (GᵀG)^{-1/2}` with the continuous-functional-calculus square root `CFC.sqrt`, and is shown to be the unique
orthogonal matrix with `Qᵀ G` positive semidefinite (`polar_eq_formula`, new here).  Both operator and
Frobenius norms.  The paper's proof via singular values (Weyl / Hoffman–Wielandt) is not reproduced: the package
proves the estimates directly from the polar decomposition.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix FormalResearch.MatrixAnalysis
open scoped Matrix.Norms.L2Operator MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem isUnit_of_close {G U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (hGU : ‖G - U‖ < 1) : IsUnit G := by
  have hinj := jop_injective_of_close hU hGU
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have := @hinj (WithLp.toLp 2 x) (WithLp.toLp 2 y) (by simpa [Matrix.toLpLin_apply] using hxy)
  simpa using this

/-- An orthogonal `Q` with `Qᵀ G` positive semidefinite, for invertible `G`, is `G (GᵀG)^{-1/2}`
(`CFC.sqrt` is the positive square root).  In particular the polar factor is unique. -/
theorem polar_eq_formula {G Q : Matrix n n ℝ} (hG : IsUnit G) (hQ : Qᵀ * Q = 1)
    (hP : (Qᵀ * G).PosSemidef) : Q = G * (CFC.sqrt (Gᵀ * G))⁻¹ := by
  have hQQ : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQ
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hGGt : (0 : Matrix n n ℝ) ≤ Gᵀ * G := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self G
  have hPnn : (0 : Matrix n n ℝ) ≤ Qᵀ * G := Matrix.nonneg_iff_posSemidef.2 hP
  have hsq : (Qᵀ * G) * (Qᵀ * G) = Gᵀ * G := by
    have hPh : (Qᵀ * G)ᵀ = Qᵀ * G := by simpa using hP.isHermitian.eq
    calc (Qᵀ * G) * (Qᵀ * G) = (Qᵀ * G)ᵀ * (Qᵀ * G) := by rw [hPh]
      _ = Gᵀ * (Q * Qᵀ) * G := by simp [Matrix.mul_assoc]
      _ = Gᵀ * G := by rw [hQQ]; simp
  have hsqrt : CFC.sqrt (Gᵀ * G) = Qᵀ * G := (CFC.sqrt_eq_iff _ _ hGGt hPnn).2 hsq
  rw [hsqrt]
  have hinv : (Qᵀ * G)⁻¹ = G⁻¹ * Q := by
    refine Matrix.inv_eq_right_inv ?_
    calc Qᵀ * G * (G⁻¹ * Q) = Qᵀ * (G * G⁻¹) * Q := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hGG]; simpa using hQ
  rw [hinv, ← Matrix.mul_assoc, hGG, Matrix.one_mul]

/-- **Polar repair** (Paper J, `lem:thb-polar`).  Let `U` be a real orthogonal matrix and `G` a real
matrix with `‖G − U‖ < 1` (spectral norm).  Then `G` is invertible, the polar factor
`Q = G (GᵀG)^{-1/2}` (with `CFC.sqrt` the positive square root) is orthogonal, it is the *unique*
orthogonal matrix with `Qᵀ G` positive semidefinite, and
`‖G − Q‖ ≤ ‖G − U‖`, `‖Q − U‖ ≤ 2‖G − U‖` in the spectral norm and
`‖G − Q‖_F ≤ ‖G − U‖_F`, `‖Q − U‖_F ≤ 2‖G − U‖_F` in the Frobenius norm (`√ frobSq`).

Index type `n` is any finite type (the paper's `Fin D` is a special case).  This is a restatement of
`jop_polar_repair_matrix` and `jop_polar_repair_frobenius_of_close` (Jacobi-operator package) plus the one
thing the paper's formula needs and the package left open: the identification of its polar matrix with the
functional-calculus formula `G (GᵀG)^{-1/2}` and the uniqueness of the polar factor
(`polar_eq_formula`).  The paper's remark that the Frobenius statement needs only `‖G-U‖_F < ∞` (no
`< 1`) is not restated; the package proves it (`jop_polar_repair_frobenius`). -/
theorem jb_polar (G U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (hGU : ‖G - U‖ < 1) :
    IsUnit G ∧
      (G * (CFC.sqrt (Gᵀ * G))⁻¹)ᵀ * (G * (CFC.sqrt (Gᵀ * G))⁻¹) = 1 ∧
      (∀ Q : Matrix n n ℝ, Qᵀ * Q = 1 → (Qᵀ * G).PosSemidef → Q = G * (CFC.sqrt (Gᵀ * G))⁻¹) ∧
      ‖G - G * (CFC.sqrt (Gᵀ * G))⁻¹‖ ≤ ‖G - U‖ ∧
      ‖G * (CFC.sqrt (Gᵀ * G))⁻¹ - U‖ ≤ 2 * ‖G - U‖ ∧
      √(frobSq (G - G * (CFC.sqrt (Gᵀ * G))⁻¹)) ≤ √(frobSq (G - U)) ∧
      √(frobSq (G * (CFC.sqrt (Gᵀ * G))⁻¹ - U)) ≤ 2 * √(frobSq (G - U)) := by
  have hG := isUnit_of_close hU hGU
  have hinj := jop_injective_of_close hU hGU
  have hQ := polar_eq_formula hG (jop_polarMatrix_orth G hinj) (jop_polarMatrix_posSemidef G hinj)
  obtain ⟨-, -, h1, h2⟩ := jop_polar_repair_matrix G U hU hGU
  obtain ⟨f1, f2⟩ := jop_polar_repair_frobenius_of_close G U hU hGU
  have ho := jop_polarMatrix_orth G hinj
  have uniq : ∀ Q : Matrix n n ℝ, Qᵀ * Q = 1 → (Qᵀ * G).PosSemidef →
      Q = G * (CFC.sqrt (Gᵀ * G))⁻¹ := fun Q h1 h2 => polar_eq_formula hG h1 h2
  rw [hQ] at ho h1 h2 f1 f2
  exact ⟨hG, ho, uniq, h1, h2, f1, f2⟩

/-- info: 'FormalResearch.JB.jb_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_polar

end FormalResearch.JB
