import FormalResearch.FrameFree.FilteredGateReal
import FormalResearch.FrameFree.FilteredGateBasic

/-!
# Filtered-gate law: the Bloch rotation of a unitary

For `φ ∈ U(2)`, `rot φ = (½ tr(σ_p φ σ_r φ†))_{p,r=1..3}` is a real `3×3` matrix (`rb_succ_eq`) with
`Orth (rot φ)` (`rot_orth`), `cofm (rot φ) = rot φ` (`rot_cof`: `Ad_φ` is an algebra automorphism, so
`ρ e_a × ρ e_b = ρ e_c`), and for a unit real vector `n` and `n̂ = Σ n_l σ_l`,
`rot (φ n̂) = ρ (2 n nᵀ - 1)` (`rot_refl`).
-/

open scoped Matrix ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

theorem pauli_expand (M : M2) :
    M = ∑ p : Fin 4, ((1 / 2 : ℂ) * (sig p * M).trace) • sig p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig, Fin.sum_univ_four, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp only [Complex.I_sq] <;> ring

theorem sig_zero : sig 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [sig]

theorem tr3 (r p q : Fin 3) : (sig r.succ * sig p.succ * sig q.succ).trace =
    if p = r + 1 ∧ q = r + 2 then 2 * Complex.I
    else if p = r + 2 ∧ q = r + 1 then -(2 * Complex.I) else 0 := by
  fin_cases r <;> fin_cases p <;> fin_cases q <;>
    simp [sig, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sig_prod_cyc (j : Fin 3) : sig j.succ * sig (j + 1).succ = Complex.I • sig (j + 2).succ := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [sig, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli components of `φ σ_r φ†`. -/
noncomputable def rb (φ : M2) (p r : Fin 4) : ℂ := (1 / 2 : ℂ) * (sig p * φ * sig r * φᴴ).trace

theorem conj_expand (φ : M2) (r : Fin 4) : φ * sig r * φᴴ = ∑ p : Fin 4, rb φ p r • sig p := by
  have h := pauli_expand (φ * sig r * φᴴ)
  conv_lhs => rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [rb, Matrix.mul_assoc]

theorem rb_star (φ : M2) (p r : Fin 4) : star (rb φ p r) = rb φ p r := by
  unfold rb
  have e : (sig p * φ * sig r * φᴴ)ᴴ = φ * sig r * φᴴ * sig p := by
    simp [Matrix.conjTranspose_mul, sig_herm, Matrix.mul_assoc]
  have h : star (sig p * φ * sig r * φᴴ).trace = (sig p * φ * sig r * φᴴ).trace := by
    rw [← Matrix.trace_conjTranspose, e,
      show sig p * φ * sig r * φᴴ = sig p * (φ * sig r * φᴴ) by simp only [Matrix.mul_assoc]]
    exact Matrix.trace_mul_comm _ _
  simp [h]

/-- The real `3×3` rotation of `φ`: `ρ_{pr} = ½ tr(σ_p φ σ_r φ†)`. -/
noncomputable def rot (φ : M2) (p r : Fin 3) : ℝ := (rb φ p.succ r.succ).re

theorem rb_succ_eq (φ : M2) (p r : Fin 3) : rb φ p.succ r.succ = (rot φ p r : ℂ) := by
  apply Complex.ext
  · simp [rot]
  · have h := congrArg Complex.im (rb_star φ p.succ r.succ)
    simp at h
    simp [rot]
    linarith

theorem trace_sig_succ (p : Fin 3) : (sig p.succ).trace = 0 := by
  fin_cases p <;> simp [sig, Matrix.trace, Fin.sum_univ_two]

theorem rb_00 (φ : M2) (h : φ * φᴴ = 1) : rb φ 0 0 = 1 := by
  unfold rb
  rw [sig_zero, Matrix.one_mul, Matrix.mul_one, h]
  simp [Matrix.trace_one]

theorem rb_0s (φ : M2) (h : φᴴ * φ = 1) (r : Fin 3) : rb φ 0 r.succ = 0 := by
  unfold rb
  rw [sig_zero, Matrix.one_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul,
    trace_sig_succ]
  simp

theorem rb_s0 (φ : M2) (h : φ * φᴴ = 1) (p : Fin 3) : rb φ p.succ 0 = 0 := by
  unfold rb
  rw [sig_zero, Matrix.mul_one, Matrix.mul_assoc, h, Matrix.mul_one, trace_sig_succ]
  simp

theorem trace_expand2 (φ : M2) (j k : Fin 4) :
    (φ * sig j * φᴴ * (φ * sig k * φᴴ)).trace = 2 * ∑ p : Fin 4, rb φ p j * rb φ p k := by
  rw [conj_expand, conj_expand]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, sig_trace, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem trace_expand3 (φ : M2) (hU : φᴴ * φ = 1) (r j k : Fin 3) :
    (sig r.succ * (φ * sig j.succ * φᴴ) * (φ * sig k.succ * φᴴ)).trace =
      ∑ p : Fin 3, ∑ q : Fin 3, ((rot φ p j : ℂ) * (rot φ q k : ℂ)) *
        (sig r.succ * sig p.succ * sig q.succ).trace := by
  rw [conj_expand, conj_expand]
  simp only [Fin.sum_univ_succ (n := 3), rb_0s φ hU, zero_smul, zero_add, rb_succ_eq]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem rot_orth (φ : M2) (hU : φᴴ * φ = 1) : Orth (rot φ) := by
  intro j k
  have h1 : (φ * sig j.succ * φᴴ * (φ * sig k.succ * φᴴ)).trace = (sig j.succ * sig k.succ).trace := by
    have : φ * sig j.succ * φᴴ * (φ * sig k.succ * φᴴ) = φ * (sig j.succ * sig k.succ) * φᴴ := by
      calc _ = φ * sig j.succ * (φᴴ * φ) * sig k.succ * φᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [trace_expand2, sig_trace] at h1
  simp only [Fin.sum_univ_succ (n := 3), rb_0s φ hU, zero_mul, zero_add, rb_succ_eq] at h1
  apply Complex.ofReal_injective
  push_cast
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte, Complex.ofReal_one] at h1 ⊢
    linear_combination h1 / 2
  · have : j.succ ≠ k.succ := fun h => hjk (Fin.succ_injective _ h)
    simp only [hjk, this, ↓reduceIte, Complex.ofReal_zero] at h1 ⊢
    linear_combination h1 / 2

theorem rot_cross (φ : M2) (hU : φᴴ * φ = 1) (r j : Fin 3) :
    rot φ (r + 1) j * rot φ (r + 2) (j + 1) - rot φ (r + 2) j * rot φ (r + 1) (j + 1) =
      rot φ r (j + 2) := by
  have hA := trace_expand3 φ hU r j (j + 1)
  have hB : (sig r.succ * (φ * sig j.succ * φᴴ) * (φ * sig (j + 1).succ * φᴴ)).trace =
      2 * Complex.I * (rot φ r (j + 2) : ℂ) := by
    have e1 : φ * sig j.succ * φᴴ * (φ * sig (j + 1).succ * φᴴ) =
        Complex.I • (φ * sig (j + 2).succ * φᴴ) := by
      calc _ = φ * (sig j.succ * sig (j + 1).succ) * φᴴ := by
            calc _ = φ * sig j.succ * (φᴴ * φ) * sig (j + 1).succ * φᴴ := by simp only [Matrix.mul_assoc]
              _ = _ := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [sig_prod_cyc]; simp [Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.mul_assoc, e1, Matrix.mul_smul, Matrix.trace_smul]
    have : (sig r.succ * (φ * sig (j + 2).succ * φᴴ)).trace = 2 * rb φ r.succ (j + 2).succ := by
      unfold rb; simp only [Matrix.mul_assoc]; ring
    rw [this, rb_succ_eq]; simp [smul_eq_mul]; ring
  rw [hB] at hA
  simp only [tr3, Fin.sum_univ_three] at hA
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  apply Complex.ofReal_injective
  push_cast
  fin_cases r <;> simp at hA ⊢ <;> exact mul_left_cancel₀ h2I (by linear_combination -hA)

theorem rot_cof (φ : M2) (hU : φᴴ * φ = 1) (i j : Fin 3) : cofm (rot φ) i j = rot φ i j := by
  have h := rot_cross φ hU i (j + 1)
  have e : j + 1 + 2 = j := by fin_cases j <;> decide
  have e2 : j + 1 + 1 = j + 2 := by fin_cases j <;> decide
  rw [e, e2] at h
  unfold cofm
  linarith

/-- `n̂ = Σ n_l σ_l`. -/
noncomputable def nh (n : V3) : M2 := ∑ l : Fin 3, (n l : ℂ) • sig l.succ

theorem nh_herm (n : V3) : (nh n)ᴴ = nh n := by
  unfold nh
  simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, sig_herm]

theorem nh_anti (n : V3) (j : Fin 3) :
    nh n * sig j.succ + sig j.succ * nh n = (2 * (n j : ℂ)) • (1 : M2) := by
  unfold nh
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [sig, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp only [Complex.I_sq] <;> ring

theorem nh_sq (n : V3) (hn : sq3 n = 1) : nh n * nh n = 1 := by
  have hn' : (n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2 + (n 2 : ℂ) ^ 2 = 1 := by
    rw [sq3_eq] at hn; exact_mod_cast hn
  unfold nh
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sig, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp only [Complex.I_sq] <;> ring_nf <;> linear_combination hn'

theorem nh_conj (n : V3) (hn : sq3 n = 1) (j : Fin 3) :
    nh n * sig j.succ * nh n = (2 * (n j : ℂ)) • nh n - sig j.succ := by
  have h := nh_anti n j
  have hs := nh_sq n hn
  have e : nh n * sig j.succ = (2 * (n j : ℂ)) • (1 : M2) - sig j.succ * nh n := by
    rw [← h]; abel
  rw [e, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hs, Matrix.mul_one]

theorem trace_nh (φ : M2) (n : V3) (p : Fin 3) :
    (sig p.succ * φ * nh n * φᴴ).trace = 2 * ∑ l : Fin 3, (n l : ℂ) * rb φ p.succ l.succ := by
  unfold nh rb
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.mul_assoc]
  ring

theorem rot_refl (φ : M2) (n : V3) (hn : sq3 n = 1) (i j : Fin 3) :
    rot (φ * nh n) i j = 2 * mv (rot φ) n i * n j - rot φ i j := by
  apply Complex.ofReal_injective
  rw [← rb_succ_eq]
  have e1 : (sig i.succ * (φ * nh n) * sig j.succ * (φ * nh n)ᴴ) =
      sig i.succ * φ * ((2 * (n j : ℂ)) • nh n - sig j.succ) * φᴴ := by
    rw [Matrix.conjTranspose_mul, nh_herm, ← nh_conj n hn j]
    simp only [Matrix.mul_assoc]
  have e2 : ((sig i.succ * φ * ((2 * (n j : ℂ)) • nh n - sig j.succ) * φᴴ)).trace =
      (2 * (n j : ℂ)) * (sig i.succ * φ * nh n * φᴴ).trace - (sig i.succ * φ * sig j.succ * φᴴ).trace := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul]
  unfold rb
  rw [e1, e2, trace_nh]
  simp only [rb_succ_eq, mv, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum]
  have : (1 / 2 : ℂ) * (sig i.succ * φ * sig j.succ * φᴴ).trace = rb φ i.succ j.succ := rfl
  rw [rb_succ_eq] at this
  push_cast
  have h3 : (sig i.succ * φ * sig j.succ * φᴴ).trace = 2 * (rot φ i j : ℂ) := by
    rw [← this]; ring
  have h4 : ∑ x, (n x : ℂ) * (rot φ i x : ℂ) = ∑ x, (rot φ i x : ℂ) * (n x : ℂ) :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [h3, h4]
  ring

end FormalResearch.FrameFree.FTG
