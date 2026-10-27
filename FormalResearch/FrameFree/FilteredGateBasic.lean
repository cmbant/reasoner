import Mathlib

/-!
# Filtered-gate law: Pauli and Cartan-gate basics

Paper P `cor:ftg` (recalled from QI-B `thm:ftg`).  Notation: `M2`, `M4` are `2×2` and `4×4` complex
matrices (`M4` indexed by `Fin 2 × Fin 2`); `kr A B = A ⊗ₖ B`; `sig μ` are the Pauli matrices
`σ_0 = 1, σ_1 = X, σ_2 = Y, σ_3 = Z`; `Pm j = σ_{j+1} ⊗ σ_{j+1}`; `Ug c` is the Cartan gate
`exp(-i ∑ c_j σ_j ⊗ σ_j) = ∏_j (cos c_j - i sin c_j P_j)`.
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev M4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The Pauli matrices `1, X, Y, Z`. -/
def sig : Fin 4 → M2 := ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

theorem sig_herm (μ : Fin 4) : (sig μ)ᴴ = sig μ := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [sig, Matrix.conjTranspose_apply]

theorem sig_sq (μ : Fin 4) : sig μ * sig μ = 1 := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sig, Matrix.mul_apply, Fin.sum_univ_two]

theorem sig_anticomm (a b : Fin 3) (h : a ≠ b) :
    sig a.succ * sig b.succ = -(sig b.succ * sig a.succ) := by
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl h |
    (ext i j; fin_cases i <;> fin_cases j <;> simp [sig, Matrix.mul_apply, Fin.sum_univ_two])

theorem sig_conj_same (a b : Fin 3) :
    sig a.succ * sig b.succ * sig a.succ = (if a = b then (1:ℂ) else -1) • sig b.succ := by
  fin_cases a <;> fin_cases b <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [sig, Matrix.mul_apply, Fin.sum_univ_two])

theorem sig_trace (μ ν : Fin 4) : (sig μ * sig ν).trace = if μ = ν then 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;> simp [sig, Matrix.trace, Fin.sum_univ_two] <;> norm_num

/-- Kronecker product of two `2×2` matrices. -/
abbrev kr (A B : M2) : M4 := A ⊗ₖ B

theorem kr_apply (A B : M2) (i k j l : Fin 2) : kr A B (i, k) (j, l) = A i j * B k l := rfl

theorem kr_mul (A B C D : M2) : kr A B * kr C D = kr (A * C) (B * D) := by
  unfold kr; rw [Matrix.mul_kronecker_mul]

theorem kr_one : kr 1 1 = (1 : M4) := Matrix.one_kronecker_one

theorem kr_neg_left (A B : M2) : kr (-A) B = -kr A B := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp

theorem kr_neg_right (A B : M2) : kr A (-B) = -kr A B := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp

theorem kr_smul_left (c : ℂ) (A B : M2) : kr (c • A) B = c • kr A B := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp [mul_assoc]

theorem kr_smul_right (c : ℂ) (A B : M2) : kr A (c • B) = c • kr A B := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp; ring

theorem kr_add_left (A A' B : M2) : kr (A + A') B = kr A B + kr A' B := Matrix.add_kronecker _ _ _
theorem kr_add_right (A B B' : M2) : kr A (B + B') = kr A B + kr A B' := Matrix.kronecker_add _ _ _

theorem kr_trace (A B : M2) : (kr A B).trace = A.trace * B.trace := Matrix.trace_kronecker _ _

theorem kr_conjTranspose (A B : M2) : (kr A B)ᴴ = kr Aᴴ Bᴴ := Matrix.conjTranspose_kronecker _ _

theorem kr_transpose (A B : M2) : (kr A B)ᵀ = kr Aᵀ Bᵀ := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp

theorem kr_conj (A B : M2) : (kr A B).map conj = kr (A.map conj) (B.map conj) := by
  ext ⟨i, k⟩ ⟨j, l⟩; simp

/-- `P_j = σ_j ⊗ σ_j`. -/
def Pm (j : Fin 3) : M4 := kr (sig j.succ) (sig j.succ)

theorem Pm_sq (j : Fin 3) : Pm j * Pm j = 1 := by
  unfold Pm
  rw [kr_mul, sig_sq, kr_one]

theorem Pm_comm (j k : Fin 3) : Pm j * Pm k = Pm k * Pm j := by
  by_cases h : j = k
  · rw [h]
  · unfold Pm
    rw [kr_mul, kr_mul, sig_anticomm j k h, kr_neg_left, kr_neg_right]
    simp

theorem Pm_herm (j : Fin 3) : (Pm j)ᴴ = Pm j := by
  unfold Pm; rw [kr_conjTranspose, sig_herm]

theorem Pm_trace (j : Fin 3) : (Pm j).trace = 0 := by
  unfold Pm
  rw [kr_trace]
  fin_cases j <;> simp [sig, Matrix.trace, Fin.sum_univ_two]

/-- One Cartan factor `exp(-iθ P_j) = cos θ - i sin θ P_j`. -/
noncomputable def Uk (θ : ℝ) (j : Fin 3) : M4 :=
  (Real.cos θ : ℂ) • (1 : M4) - (Complex.I * (Real.sin θ : ℂ)) • Pm j

theorem Uk_conjTranspose (θ : ℝ) (j : Fin 3) : (Uk θ j)ᴴ = Uk (-θ) j := by
  unfold Uk
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Pm_herm]
  simp only [Complex.star_def, Complex.conj_ofReal, map_mul, Complex.conj_I, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg, sub_eq_add_neg, neg_smul, smul_neg, mul_neg, neg_neg, neg_mul]

theorem Uk_mul (θ φ : ℝ) (j : Fin 3) : Uk θ j * Uk φ j = Uk (θ + φ) j := by
  unfold Uk
  have h := Pm_sq j
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h,
    Real.cos_add, Real.sin_add]
  push_cast
  match_scalars <;> (ring_nf; try simp [Complex.I_sq]; try ring)

theorem Uk_zero (j : Fin 3) : Uk 0 j = 1 := by
  simp [Uk]

theorem Uk_comm (θ φ : ℝ) (j k : Fin 3) : Commute (Uk θ j) (Uk φ k) := by
  unfold Uk
  have h : Commute (Pm j) (Pm k) := Pm_comm j k
  have h1 : Commute (Pm j) ((Real.cos φ : ℂ) • (1 : M4) - (Complex.I * (Real.sin φ : ℂ)) • Pm k) :=
    Commute.sub_right ((Commute.one_right _).smul_right _) (h.smul_right _)
  have h2 : Commute (1 : M4)
      ((Real.cos φ : ℂ) • (1 : M4) - (Complex.I * (Real.sin φ : ℂ)) • Pm k) :=
    Commute.one_left _
  exact Commute.sub_left (h2.smul_left _) (h1.smul_left _)

theorem Uk_mul_conjT (θ : ℝ) (j : Fin 3) : Uk θ j * (Uk θ j)ᴴ = 1 := by
  rw [Uk_conjTranspose, Uk_mul, add_neg_cancel, Uk_zero]

theorem Uk_conjT_mul (θ : ℝ) (j : Fin 3) : (Uk θ j)ᴴ * Uk θ j = 1 := by
  rw [Uk_conjTranspose, Uk_mul, neg_add_cancel, Uk_zero]

/-- The Cartan gate `U_c = exp(-i ∑ c_j σ_j ⊗ σ_j)`. -/
noncomputable def Ug (c : Fin 3 → ℝ) : M4 := Uk (c 0) 0 * Uk (c 1) 1 * Uk (c 2) 2

theorem Ug_conjTranspose (c : Fin 3 → ℝ) :
    (Ug c)ᴴ = Uk (-c 2) 2 * Uk (-c 1) 1 * Uk (-c 0) 0 := by
  unfold Ug
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Uk_conjTranspose, Uk_conjTranspose,
    Uk_conjTranspose, Matrix.mul_assoc]

theorem Ug_mul_conjT (c : Fin 3 → ℝ) : Ug c * (Ug c)ᴴ = 1 := by
  rw [Ug_conjTranspose]; unfold Ug
  calc Uk (c 0) 0 * Uk (c 1) 1 * Uk (c 2) 2 * (Uk (-c 2) 2 * Uk (-c 1) 1 * Uk (-c 0) 0)
      = Uk (c 0) 0 * Uk (c 1) 1 * (Uk (c 2) 2 * Uk (-c 2) 2) * Uk (-c 1) 1 * Uk (-c 0) 0 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Uk_mul, add_neg_cancel, Uk_zero, Matrix.mul_one]
        calc Uk (c 0) 0 * Uk (c 1) 1 * Uk (-c 1) 1 * Uk (-c 0) 0
            = Uk (c 0) 0 * (Uk (c 1) 1 * Uk (-c 1) 1) * Uk (-c 0) 0 := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by
              rw [Uk_mul, add_neg_cancel, Uk_zero, Matrix.mul_one, Uk_mul, add_neg_cancel, Uk_zero]

theorem Ug_conjT_mul (c : Fin 3 → ℝ) : (Ug c)ᴴ * Ug c = 1 := by
  rw [Ug_conjTranspose]; unfold Ug
  calc Uk (-c 2) 2 * Uk (-c 1) 1 * Uk (-c 0) 0 * (Uk (c 0) 0 * Uk (c 1) 1 * Uk (c 2) 2)
      = Uk (-c 2) 2 * Uk (-c 1) 1 * (Uk (-c 0) 0 * Uk (c 0) 0) * Uk (c 1) 1 * Uk (c 2) 2 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Uk_mul, neg_add_cancel, Uk_zero, Matrix.mul_one]
        calc Uk (-c 2) 2 * Uk (-c 1) 1 * Uk (c 1) 1 * Uk (c 2) 2
            = Uk (-c 2) 2 * (Uk (-c 1) 1 * Uk (c 1) 1) * Uk (c 2) 2 := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by
              rw [Uk_mul, neg_add_cancel, Uk_zero, Matrix.mul_one, Uk_mul, neg_add_cancel, Uk_zero]

/-- Squared Frobenius norm. -/
noncomputable def fro2 (M : M4) : ℝ := (Mᴴ * M).trace.re

theorem fro2_mul_unitary_right (M R : M4) (h : R * Rᴴ = 1) : fro2 (M * R) = fro2 M := by
  unfold fro2
  rw [Matrix.conjTranspose_mul]
  have : Rᴴ * Mᴴ * (M * R) = Rᴴ * (Mᴴ * M) * R := by simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem fro2_mul_unitary_left (M R : M4) (h : Rᴴ * R = 1) : fro2 (R * M) = fro2 M := by
  unfold fro2
  rw [Matrix.conjTranspose_mul]
  have : Mᴴ * Rᴴ * (R * M) = Mᴴ * (Rᴴ * R) * M := by simp only [Matrix.mul_assoc]
  rw [this, h, Matrix.mul_one]

theorem fro2_one : fro2 (1 : M4) = 4 := by
  unfold fro2
  simp [Matrix.trace, Fintype.sum_prod_type]

/-- Reordering a product of three pairwise-commuting-across factors. -/
theorem prod3 (x₀ x₁ x₂ y₀ y₁ y₂ : M4) (h10 : Commute x₁ y₀) (h20 : Commute x₂ y₀)
    (h21 : Commute x₂ y₁) : x₀ * x₁ * x₂ * (y₀ * y₁ * y₂) = (x₀ * y₀) * (x₁ * y₁) * (x₂ * y₂) := by
  have e1 : x₂ * y₀ = y₀ * x₂ := h20.eq
  have e2 : x₁ * y₀ = y₀ * x₁ := h10.eq
  have e3 : x₂ * y₁ = y₁ * x₂ := h21.eq
  calc x₀ * x₁ * x₂ * (y₀ * y₁ * y₂) = x₀ * x₁ * (x₂ * y₀) * y₁ * y₂ := by
        simp only [Matrix.mul_assoc]
    _ = x₀ * (x₁ * y₀) * x₂ * y₁ * y₂ := by rw [e1]; simp only [Matrix.mul_assoc]
    _ = x₀ * y₀ * x₁ * (x₂ * y₁) * y₂ := by rw [e2]; simp only [Matrix.mul_assoc]
    _ = (x₀ * y₀) * (x₁ * y₁) * (x₂ * y₂) := by rw [e3]; simp only [Matrix.mul_assoc]

end FormalResearch.FrameFree.FTG
