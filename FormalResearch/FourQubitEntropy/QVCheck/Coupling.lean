import Mathlib

/-!
# Generic linear algebra of the coupled contraction (K3, K4)

For matrices over a commutative ring `R` on finite index types `ιA`, `ιB`:

`S4 W P V R' = ∑_{i,j,k,l} W_{ij} P_{ik} V_{kl} R'_{jl} = tr (Wᵀ P V R'ᵀ)`.

* `det_ne_zero_of_left_inv`: `U A = c 1`, `c ≠ 0` gives `det A ≠ 0` over `ℤ` (pivot minors).
* `S4_coupled`: with `T_A Tinv_A = Tinv_A T_A = δ_A 1` (similarly for `B`),
  `δ_A² δ_B² · S4 W P V R' = S4 W' P̃ V' R̃` for `W' = Tinv_Aᵀ W Tinv_B`, `V' = T_A V T_Bᵀ`,
  `P̃ = T_A P Tinv_A`, `R̃ = T_B R' Tinv_B`.
* `S4` is bilinear in `(W, V)` and linear in `P`, `R'` (`S4_add_left`, ...), and evaluates on elementary matrices
  (`S4_single`).
-/

open Finset
open scoped Matrix

namespace QVCheck

set_option linter.unusedSectionVars false

theorem det_ne_zero_of_left_inv {n : ℕ} (A U : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (hc : c ≠ 0)
    (h : U * A = c • 1) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  simp only [Fintype.card_fin] at this
  exact pow_ne_zero n hc this.symm

section S4
variable {R : Type*} [CommRing R] {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]

/-- `∑_{i,j,k,l} W_{ij} P_{ik} V_{kl} R'_{jl}` -/
def S4 (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R) : R :=
  ∑ i, ∑ j, ∑ k, ∑ l, W i j * P i k * V k l * R' j l

theorem S4_eq_trace (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R) :
    S4 W P V R' = (Wᵀ * P * V * R'ᵀ).trace := by
  simp only [S4, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, W i j * P i k * V k l * R' j l := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ l, ∑ k, W i j * P i k * V k l * R' j l :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, ∑ k, W i j * P i k * V k l * R' j l :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm


theorem S4_coupled {ιA ιB : Type*} [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB]
    (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R)
    (TA TiA : Matrix ιA ιA R) (TB TiB : Matrix ιB ιB R) (dA dB : R)
    (hA2 : TiA * TA = dA • 1) (hB2 : TiB * TB = dB • 1) :
    dA ^ 2 * dB ^ 2 * S4 W P V R' =
      S4 (TiAᵀ * W * TiB) (TA * P * TiA) (TA * V * TBᵀ) (TB * R' * TiB) := by
  rw [S4_eq_trace, S4_eq_trace]
  have hB1' : TBᵀ * TiBᵀ = dB • 1 := by rw [← Matrix.transpose_mul, hB2]; simp
  have e : ((TiAᵀ * W * TiB)ᵀ * (TA * P * TiA) * (TA * V * TBᵀ) * (TB * R' * TiB)ᵀ) =
      TiBᵀ * (Wᵀ * (TiA * TA) * P * (TiA * TA) * V * (TBᵀ * TiBᵀ) * R'ᵀ) * TBᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, hA2, hB1']
  have e2 : Wᵀ * (dA • (1 : Matrix ιA ιA R)) * P * (dA • (1 : Matrix ιA ιA R)) * V * (dB • (1 : Matrix ιB ιB R)) * R'ᵀ =
      (dA * dA * dB) • (Wᵀ * P * V * R'ᵀ) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
    rw [show dB * (dA * dA) = dA * dA * dB by ring]
  rw [e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.trace_mul_cycle TiBᵀ (Wᵀ * P * V * R'ᵀ) TBᵀ, hB1']
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  ring


theorem S4_add_left (W1 W2 : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R) :
    S4 (W1 + W2) P V R' = S4 W1 P V R' + S4 W2 P V R' := by
  simp only [S4, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem S4_add_right (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V1 V2 : Matrix ιA ιB R) (R' : Matrix ιB ιB R) :
    S4 W P (V1 + V2) R' = S4 W P V1 R' + S4 W P V2 R' := by
  simp only [S4, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem S4_smul_left (c : R) (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R) :
    S4 (c • W) P V R' = c * S4 W P V R' := by
  simp only [S4, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem S4_smul_right (c : R) (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R) :
    S4 W P (c • V) R' = c * S4 W P V R' := by
  simp only [S4, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem S4_single (i0 k0 : ιA) (j0 l0 : ιB) (w v : R) (P : Matrix ιA ιA R) (R' : Matrix ιB ιB R) :
    S4 (Matrix.single i0 j0 w) P (Matrix.single k0 l0 v) R' = w * P i0 k0 * v * R' j0 l0 := by
  simp only [S4, Matrix.single_apply]
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single k0]
      · rw [Finset.sum_eq_single l0]
        · simp
        · intro l _ hl; simp [hl, Ne.symm hl]
        · simp
      · intro k _ hk; simp [hk, Ne.symm hk]
      · simp
    · intro j _ hj; simp [hj, Ne.symm hj]
    · simp
  · intro i _ hi; simp [hi, Ne.symm hi]
  · simp

theorem S4_zero_left (P : Matrix ιA ιA R) (V : Matrix ιA ιB R) (R' : Matrix ιB ιB R) :
    S4 (0 : Matrix ιA ιB R) P V R' = 0 := by
  simp [S4]

theorem S4_zero_right (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (R' : Matrix ιB ιB R) :
    S4 W P (0 : Matrix ιA ιB R) R' = 0 := by
  simp [S4]

theorem S4_sum_left {κ : Type*} (s : Finset κ) (W : κ → Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : Matrix ιA ιB R)
    (R' : Matrix ιB ιB R) : S4 (∑ k ∈ s, W k) P V R' = ∑ k ∈ s, S4 (W k) P V R' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S4_zero_left P V R'
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, S4_add_left, ih]

theorem S4_sum_right {κ : Type*} (s : Finset κ) (W : Matrix ιA ιB R) (P : Matrix ιA ιA R) (V : κ → Matrix ιA ιB R)
    (R' : Matrix ιB ιB R) : S4 W P (∑ k ∈ s, V k) R' = ∑ k ∈ s, S4 W P (V k) R' := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S4_zero_right W P R'
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, S4_add_right, ih]

end S4

end QVCheck
