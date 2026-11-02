import FormalResearch.FourQubitEntropy.QVCheck.Final

/-!
# Placed bilinear forms of Kronecker products
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- A Kronecker product in the sector `p` is the placed form of the permuted product in the sector `p ∘ σ`. -/
theorem bilN_kron_placed (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4))
    (M : ∀ q, Matrix (Fin (multF (p q))) (Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (kronPi M) A B = bilPl p σ (kronPi (fun r => M (σ r))) A B := by
  unfold bilN bilPl
  let e := Equiv.piCongrLeft (fun q => Fin (multF (p q))) σ
  have hk : ∀ x y : (∀ r, Fin (multF (p (σ r)))), kronPi (fun r => M (σ r)) x y = kronPi M (e x) (e y) := by
    intro x y
    rw [kronPi_apply, kronPi_apply]
    rw [← Equiv.prod_comp σ (fun q => M q ((e x) q) ((e y) q))]
    refine Finset.prod_congr rfl fun r _ => ?_
    simp only [e, Equiv.piCongrLeft_apply_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hk]

theorem bilN_add (p : Fin 4 → Spin) (M N : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (M + N) A B = bilN p M A B + bilN p N A B := by
  unfold bilN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.add_apply]; ring

theorem bilN_smul (p : Fin 4 → Spin) (c : ℤ) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (c • M) A B = c * bilN p M A B := by
  unfold bilN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem bilN_zero (p : Fin 4 → Spin) (A B : ℕ) :
    bilN p (0 : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) A B = 0 := by
  unfold bilN; simp

theorem bilN_list_sum {α : Type*} (p : Fin 4 → Spin) (L : List α)
    (f : α → Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (L.map f).sum A B = (L.map fun x => bilN p (f x) A B).sum := by
  induction L with
  | nil => simpa using bilN_zero p A B
  | cons a t ih => simp only [List.map_cons, List.sum_cons, bilN_add, ih]

theorem bilN_finset_sum {ι : Type*} (p : Fin 4 → Spin) (s : Finset ι)
    (f : ι → Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : ℕ) :
    bilN p (∑ i ∈ s, f i) A B = ∑ i ∈ s, bilN p (f i) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bilN_zero p A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bilN_add, ih]

theorem bilPl_add (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4))
    (M N : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (M + N) A B = bilPl p σ M A B + bilPl p σ N A B := by
  unfold bilPl
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.add_apply]; ring

theorem bilPl_smul (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (c : ℤ)
    (M : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (c • M) A B = c * bilPl p σ M A B := by
  unfold bilPl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem bilPl_zero (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (A B : ℕ) :
    bilPl p σ (0 : Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) A B = 0 := by
  unfold bilPl; simp

theorem bilPl_list_sum {α : Type*} (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (L : List α)
    (f : α → Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (L.map f).sum A B = (L.map fun x => bilPl p σ (f x) A B).sum := by
  induction L with
  | nil => simpa using bilPl_zero p σ A B
  | cons a t ih => simp only [List.map_cons, List.sum_cons, bilPl_add, ih]

end QVCheck
