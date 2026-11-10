module

public import FormalResearch.PPTThreeQubit.Witness
public import FormalResearch.PPTThreeQubit.PartialTranspose

/-!
# Local filters and product vectors (for `cor:ppt3-chirality`)

Source: `QI/hidden_entanglement/ppt_three_qubit/appendix_family.tex`, proof of
`cor:ppt3-chirality` (b), and `family.tex`.

Conventions as in `Basic.lean` (`|abc⟩` has index `4a + 2b + c`).  `tri a b c` is the product vector
`a ⊗ b ⊗ c`; `locMat FA FB FC` is the local filter `F_A ⊗ F_B ⊗ F_C` on `ℂ⁸`; `Rs s = ran B_s`
as a set of vectors, `Rsbar s` its complex conjugate.  `phiS s z` is the `2 × 2` coefficient matrix
of the `BC` part of `B_s q_s(z) = (|0⟩ + z|1⟩) ⊗ φ_s(z)`, and `det_phiS` is
`det φ_s(z) = -3 (z² + s)²`.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- The bit of qubit `A` (most significant) of an index. -/
def bitA (i : Fin 8) : Fin 2 := ⟨i.val / 4, by omega⟩

/-- The bit of qubit `B` of an index. -/
def bitB (i : Fin 8) : Fin 2 := ⟨i.val / 2 % 2, by omega⟩

/-- The bit of qubit `C` (least significant) of an index. -/
def bitC (i : Fin 8) : Fin 2 := ⟨i.val % 2, by omega⟩

/-- The product vector `a ⊗ b ⊗ c`. -/
def tri (a b c : Fin 2 → ℂ) : Fin 8 → ℂ := fun i => a (bitA i) * b (bitB i) * c (bitC i)

/-- A fully product vector. -/
def IsFullProd (x : Fin 8 → ℂ) : Prop := ∃ a b c : Fin 2 → ℂ, x = tri a b c

/-- The local filter `F_A ⊗ F_B ⊗ F_C` as an `8 × 8` matrix. -/
def locMat (FA FB FC : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => FA (bitA i) (bitA j) * FB (bitB i) (bitB j) * FC (bitC i) (bitC j)

/-- The vector `|0⟩ + z|1⟩`. -/
def chi (z : ℂ) : Fin 2 → ℂ := ![1, z]

/-- The range `R_s = ran B_s`, as a set of vectors. -/
def Rs (s : ℝ) : Set (Fin 8 → ℂ) := Set.range (Bs s).mulVec

/-- The complex conjugate `conj(R_s)`. -/
def Rsbar (s : ℝ) : Set (Fin 8 → ℂ) := {y | star y ∈ Rs s}

theorem Rs_add {s : ℝ} {x y : Fin 8 → ℂ} (hx : x ∈ Rs s) (hy : y ∈ Rs s) : x + y ∈ Rs s := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  exact ⟨c + d, mulVec_add _ _ _⟩

theorem Rs_smul {s : ℝ} (l : ℂ) {x : Fin 8 → ℂ} (hx : x ∈ Rs s) : l • x ∈ Rs s := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨l • c, mulVec_smul _ _ _⟩

theorem tri_apply (a b c : Fin 2 → ℂ) (i : Fin 8) :
    tri a b c i = a (bitA i) * b (bitB i) * c (bitC i) := rfl

theorem star_tri (a b c : Fin 2 → ℂ) : star (tri a b c) = tri (star a) (star b) (star c) := by
  ext i; simp [tri_apply, star_mul']

theorem tri_smul_left (l : ℂ) (a b c : Fin 2 → ℂ) : tri (l • a) b c = l • tri a b c := by
  ext i; simp [tri_apply]; ring

theorem tri_smul_mid (l : ℂ) (a b c : Fin 2 → ℂ) : tri a (l • b) c = l • tri a b c := by
  ext i; simp [tri_apply]; ring

theorem tri_smul_right (l : ℂ) (a b c : Fin 2 → ℂ) : tri a b (l • c) = l • tri a b c := by
  ext i; simp [tri_apply]; ring

/-- The local filter acts factorwise on product vectors. -/
theorem locMat_mulVec_tri (FA FB FC : Matrix (Fin 2) (Fin 2) ℂ) (a b c : Fin 2 → ℂ) :
    locMat FA FB FC *ᵥ tri a b c = tri (FA *ᵥ a) (FB *ᵥ b) (FC *ᵥ c) := by
  ext i
  simp only [mulVec, dotProduct, locMat, tri_apply, of_apply, Fin.sum_univ_eight, Fin.sum_univ_two]
  fin_cases i <;> simp [bitA, bitB, bitC] <;> ring

theorem locMat_mul (A B C A' B' C' : Matrix (Fin 2) (Fin 2) ℂ) :
    locMat A B C * locMat A' B' C' = locMat (A * A') (B * B') (C * C') := by
  ext i k
  simp only [mul_apply, locMat, of_apply, Fin.sum_univ_eight, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k <;> simp [bitA, bitB, bitC] <;> ring

theorem locMat_one : locMat 1 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [locMat, bitA, bitB, bitC, Matrix.one_apply, Fin.ext_iff]

/-- An invertible local filter is injective. -/
theorem locMat_injective {FA FB FC : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit FA.det)
    (hB : IsUnit FB.det) (hC : IsUnit FC.det) : Function.Injective (locMat FA FB FC).mulVec := by
  have h : locMat FA⁻¹ FB⁻¹ FC⁻¹ * locMat FA FB FC = 1 := by
    rw [locMat_mul, Matrix.nonsing_inv_mul _ hA, Matrix.nonsing_inv_mul _ hB,
      Matrix.nonsing_inv_mul _ hC, locMat_one]
  intro x y hxy
  have := congrArg (locMat FA⁻¹ FB⁻¹ FC⁻¹).mulVec hxy
  rwa [mulVec_mulVec, mulVec_mulVec, h, one_mulVec, one_mulVec] at this

/-- The cyclic shift of the qubits on vectors, `(Πx)(i) = x(cycShift i)`. -/
def shiftVec (x : Fin 8 → ℂ) : Fin 8 → ℂ := fun i => x (cycShift i)

/-- `F ⊗ F' ⊗ F''` with all factors proportional to one matrix commutes with the cyclic shift. -/
theorem locMat_shift (FA : Matrix (Fin 2) (Fin 2) ℂ) (l m : ℂ) (x : Fin 8 → ℂ) :
    shiftVec (locMat FA (l • FA) (m • FA) *ᵥ x) = locMat FA (l • FA) (m • FA) *ᵥ shiftVec x := by
  ext i
  simp only [shiftVec, mulVec, dotProduct, locMat, of_apply, Fin.sum_univ_eight, cycShift,
    Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [bitA, bitB, bitC] <;> ring

/-- The `BC` coefficient matrix of `B_s q_s(z) = (|0⟩ + z|1⟩) ⊗ φ_s(z)`. -/
def phiS (s : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2 * z, (z ^ 2 - s) + ω ^ 2 * (z ^ 2 + s); (z ^ 2 - s) + ω * (z ^ 2 + s),
    -(z * (z ^ 2 + 3 * s))]

/-- `B_s q_s(z) = (|0⟩ + z|1⟩) ⊗ φ_s(z)`. -/
theorem Bs_qs_eq (s : ℝ) (z : ℂ) :
    Bs s *ᵥ qs s z = fun i => chi z (bitA i) * phiS s z (bitB i) (bitC i) := by
  ext i
  rw [Bs_mulVec]
  fin_cases i <;> simp [qs, chi, phiS, bitA, bitB, bitC] <;>
    first | ring1 | linear_combination (-z * (z ^ 2 + s)) * ω_sq_add_ω_add_one

/-- **`det φ_s(z) = -3 (z² + s)²`** (proof of `cor:ppt3-chirality` (b)). -/
theorem det_phiS (s : ℝ) (z : ℂ) : (phiS s z).det = -3 * (z ^ 2 + s) ^ 2 := by
  rw [det_fin_two]
  simp only [phiS, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  linear_combination (-(z ^ 2 - s) * (z ^ 2 + s)) * ω_sq_add_ω_add_one -
    (z ^ 2 + s) ^ 2 * ω_cube

end

/-- info: 'FormalResearch.PPTThreeQubit.det_phiS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms det_phiS

/-- info: 'FormalResearch.PPTThreeQubit.locMat_mulVec_tri' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms locMat_mulVec_tri

/-- info: 'FormalResearch.PPTThreeQubit.locMat_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms locMat_injective

end FormalResearch.PPTThreeQubit
