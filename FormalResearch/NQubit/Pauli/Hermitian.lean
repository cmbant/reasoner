module

public import FormalResearch.NQubit.Pauli.Weight

/-!
# Hermitian Pauli strings

* `pauliMat`: the Hermitian Pauli matrices `I, X, Y, Z`; `pauliSU_eq`: `pauliSU b = (-i)^{[b ≠ 0]} pauliMat b`;
* `pauliExp ψ a = ⟨ψ|P_a|ψ⟩` for the Hermitian Pauli string `P_a = ⊗ᵢ pauliMat (aᵢ)`, which is real
  (`pauliExp_im`); `pexp_eq` relates it to `pexp` (the phase-adjusted `pauliSU` expectation);
* `pauliSq_eq_pauliExp_sq`: `pauliSq ψ a = ⟨ψ|P_a|ψ⟩²`, so `weightEnum ψ j = Σ_{pauliWeight P = j} ⟨ψ|P|ψ⟩²`
  (`weightEnum_eq_sum_pauliExp`);
* `weightEnum_zero_of_unit`: `A_0 = 1` for a unit vector.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators

namespace FormalResearch.NQubit.Pauli

/-- The genuine Hermitian Pauli matrices `I, X, Y, Z`. -/
def pauliMat : Fin 4 → Op1 :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- `pauliSU b = (-i)^{[b ≠ 0]} · pauliMat b`. -/
theorem pauliSU_eq (b : Fin 4) :
    pauliSU b = (if b = 0 then (1 : ℂ) else -Complex.I) • pauliMat b := by
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pauliSU, pauliMat]

theorem conj_pauliMat (b : Fin 4) (x y : Fin 2) : conj (pauliMat b x y) = pauliMat b y x := by
  fin_cases b <;> fin_cases x <;> fin_cases y <;> simp [pauliMat]

/-- `⟨ψ| P_a |ψ⟩` for the Hermitian Pauli string `P_a = ⊗ᵢ pauliMat (a i)`. -/
noncomputable def pauliExp {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : ℂ :=
  ip ψ (rot (fun i => pauliMat (a i)) ψ)

theorem pexp_eq {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    pexp ψ a = (∏ i, (if a i = 0 then (1 : ℂ) else -Complex.I)) * pauliExp ψ a := by
  unfold pexp pauliExp ip rot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [pauliSU_eq, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem normSq_phase {n : ℕ} (a : Fin n → Fin 4) :
    Complex.normSq (∏ i, (if a i = 0 then (1 : ℂ) else -Complex.I)) = 1 := by
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs <;> simp

/-- `⟨ψ|P_a|ψ⟩` is real. -/
theorem pauliExp_im {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : (pauliExp ψ a).im = 0 := by
  have h : conj (pauliExp ψ a) = pauliExp ψ a := by
    unfold pauliExp ip rot
    simp only [map_sum, map_mul, map_prod, Complex.conj_conj, conj_pauliMat]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have := congrArg Complex.im h
  simp at this
  linarith

/-- **`SpinFlip.pw` is `⟨ψ|P|ψ⟩²`** for the genuine Hermitian Pauli string. -/
theorem pauliSq_eq_pauliExp_sq {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    pauliSq ψ a = (pauliExp ψ a).re ^ 2 := by
  unfold pauliSq
  rw [pexp_eq, map_mul, normSq_phase, one_mul, Complex.normSq_apply, pauliExp_im]
  ring

/-- `A_j = Σ_{pauliWeight P = j} ⟨ψ|P|ψ⟩²` with genuine Pauli strings. -/
theorem weightEnum_eq_sum_pauliExp {n : ℕ} (ψ : Ψ n) (j : ℕ) :
    weightEnum ψ j = ∑ a ∈ Finset.univ.filter (fun a : Fin n → Fin 4 => pauliWeight a = j), (pauliExp ψ a).re ^ 2 := by
  unfold weightEnum
  exact Finset.sum_congr rfl fun a _ => pauliSq_eq_pauliExp_sq ψ a

theorem pauliWeight_eq_zero_iff {n : ℕ} (a : Fin n → Fin 4) : pauliWeight a = 0 ↔ a = fun _ => 0 := by
  unfold pauliWeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; by_contra hi; exact h (Finset.mem_univ i) hi
  · rintro rfl i _; simp

/-- `A_0 = 1` for a unit vector. -/
theorem weightEnum_zero_of_unit {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) : weightEnum ψ 0 = 1 := by
  unfold weightEnum
  have : Finset.univ.filter (fun a : Fin n → Fin 4 => pauliWeight a = 0) = {fun _ => 0} := by
    ext a; simp [pauliWeight_eq_zero_iff]
  rw [this, Finset.sum_singleton]
  unfold pauliSq pexp
  have h1 : (fun i : Fin n => pauliSU ((fun _ => (0 : Fin 4)) i)) = fun _ => (1 : Op1) := by
    funext i; rfl
  rw [h1, rot_one, ip_self, hψ]
  simp

end FormalResearch.NQubit.Pauli
