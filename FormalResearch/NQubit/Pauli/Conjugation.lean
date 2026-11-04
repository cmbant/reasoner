module

public import FormalResearch.NQubit.Pauli.Weight

/-!
# Complex conjugation and time reversal of Pauli expectations

For every `ψ : Ψ n` and Pauli word `a`:

* `conj_pexp`: `conj (pexp ψ a) = (-1)^{pauliWeight a} pexp ψ a`;
* `pexp_Θ`: `pexp (Θ ψ) a = conj (pexp ψ a)`;
* `pexp_smul`: `pexp (c • ψ) a = |c|² pexp ψ a`;
* `weightEnum_zero`: `weightEnum ψ 0 = ‖ψ‖⁴`.

Auxiliary lemmas: `conj_ip`, `ip_rot_adj` (adjoint of a local operator in the inner product), `rot_smul_fam`,
`pauliSU_adj`.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open scoped Matrix

namespace FormalResearch.NQubit.Pauli

theorem conj_ip {n : ℕ} (ψ φ : Ψ n) : conj (ip ψ φ) = ip φ ψ := by
  unfold ip; simp [map_sum, mul_comm]

/-- Adjoint of a local operator inside the inner product. -/
theorem ip_rot_adj {n : ℕ} (u : Fin n → Op1) (ψ φ : Ψ n) :
    ip (rot u ψ) φ = ip ψ (rot (fun i => (u i)ᴴ) φ) := by
  unfold ip rot
  simp only [map_sum, map_mul, map_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have : ∏ i, conj (u i (x i) (y i)) = ∏ i, (u i)ᴴ (y i) (x i) := by
    simp [Matrix.conjTranspose_apply]
  rw [this]; ring

theorem rot_smul_fam {n : ℕ} (c : Fin n → ℂ) (u : Fin n → Op1) (ψ : Ψ n) :
    rot (fun i => c i • u i) ψ = (∏ i, c i) • rot u ψ := by
  funext x
  simp only [rot, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.prod_mul_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem pauliSU_adj (a : Fin 4) :
    (pauliSU a)ᴴ = (if a = 0 then (1 : ℂ) else -1) • pauliSU a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliSU, Matrix.conjTranspose_apply]

theorem conj_pexp {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) :
    conj (pexp ψ a) = (-1 : ℂ) ^ pauliWeight a * pexp ψ a := by
  unfold pexp
  rw [conj_ip, ip_rot_adj]
  have : (fun i => (pauliSU (a i))ᴴ) = fun i => (if a i = 0 then (1 : ℂ) else -1) • pauliSU (a i) := by
    funext i; exact pauliSU_adj _
  rw [this, rot_smul_fam, signprod_eq]
  simp [ip, Finset.mul_sum, mul_left_comm]

theorem pexp_Θ {n : ℕ} (ψ : Ψ n) (a : Fin n → Fin 4) : pexp (Θ ψ) a = conj (pexp ψ a) := by
  unfold pexp
  rw [← Θ_rot _ (fun i => pauliSU_su2 _), ip_Θ_Θ]

theorem pexp_smul {n : ℕ} (c : ℂ) (ψ : Ψ n) (a : Fin n → Fin 4) :
    pexp (c • ψ) a = (conj c * c) * pexp ψ a := by
  unfold pexp ip rot
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `A_0 = ‖ψ‖⁴`. -/
theorem weightEnum_zero {n : ℕ} (ψ : Ψ n) : weightEnum ψ 0 = nsq ψ * nsq ψ := by
  have hset : (Finset.univ.filter fun a : Fin n → Fin 4 => pauliWeight a = 0) = {fun _ => 0} := by
    ext a
    simp [pauliWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff, funext_iff]
  unfold weightEnum
  rw [hset, Finset.sum_singleton]
  unfold pauliSq pexp
  have : (fun i => pauliSU (((fun _ => 0 : Fin n → Fin 4)) i)) = fun _ => (1 : Op1) := rfl
  rw [this, rot_one, ip_self, Complex.normSq_ofReal]

end FormalResearch.NQubit.Pauli
