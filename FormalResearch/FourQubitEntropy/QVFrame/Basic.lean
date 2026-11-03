module

public import FormalResearch.FourQubitEntropy.QVBlock.Symmetriser
public import FormalResearch.FourQubitEntropy.QVCert.Covariants

/-!
# Conventions of the frame calculus (QV, Route D, T1–T3)

* `Site = Fin 4 → Fin 2`: a four-qubit basis state; `Psi` is the curried form used in `Statement.lean`
  and `zf z : Site → ℂ` its uncurried form.
* `Wd n = Fin n → Fin 2`: the word of one qubit across `n` copies ("slots"); `Cfg n = Fin 4 → Wd n` is the
  qubit-major index of `(ℂ¹⁶)^{⊗n}` (the index type of `QVBlock.copyPower`).
* `col β t : Site` is the four-qubit basis state sitting in copy `t` of the configuration `β`.
* `eps c = (-1)^{Σ c_q}`, `rev' c = 1 - c`, `Jv y = J^{⊗4} y` (`J = ((0,1),(-1,0))`).
* `bitsOf n : Wd 6` and `numOf w : ℕ`: the bit convention of `sixCopy` (copy `k` is bit `5 - k`).
-/

@[expose] public section


open scoped ComplexConjugate
open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

/-- A four-qubit basis state. -/
abbrev Site := Fin 4 → Fin 2
/-- The word of one qubit across `n` copies. -/
abbrev Wd (n : ℕ) := Fin n → Fin 2
/-- The qubit-major index of `(ℂ¹⁶)^{⊗n}`. -/
abbrev Cfg (n : ℕ) := Fin 4 → Wd n

/-- The uncurried form of a four-qubit vector. -/
def zf (z : Psi) : Site → ℂ := fun c => z (c 0) (c 1) (c 2) (c 3)

/-- The basis state in copy `t` of a configuration. -/
def col {n : ℕ} (β : Cfg n) (t : Fin n) : Site := fun q => β q t

/-- `(-1)^{c_0 + c_1 + c_2 + c_3}`. -/
def eps (c : Site) : ℤ := ∏ q, (-1) ^ (c q).val

/-- Bitwise complement of a four-qubit state. -/
def rev' (c : Site) : Site := fun q => (c q).rev

/-- Bitwise complement of a word. -/
def revW {n : ℕ} (α : Wd n) : Wd n := fun t => (α t).rev

/-- `J^{⊗4} y` for `J = ((0,1),(-1,0))`: `(J y)(c) = (-1)^{Σ c} y(1 - c)`. -/
def Jv (y : Site → ℂ) : Site → ℂ := fun c => (eps c : ℂ) * y (rev' c)

theorem rev'_rev' (c : Site) : rev' (rev' c) = c := by
  funext q; simp [rev']

theorem eps_rev' (c : Site) : eps (rev' c) = eps c := by
  revert c; decide

/-- The four-qubit tensor power `u^{⊗n}` written qubit-major is `QVBlock.copyPower`. -/
theorem copyPower_eq_prod {n : ℕ} (u : Site → ℂ) (β : Cfg n) :
    copyPower u n β = ∏ t : Fin n, u (col β t) := rfl

/-! ### Bit convention of `sixCopy` -/

/-- Copy `t` of the basis index `n ∈ [0, 64)` is bit `5 - t` of `n` (the convention of `sixCopy`). -/
def bitsOf (n : ℕ) : Wd 6 := fun t => QVCert.bitF n (5 - t.val)

/-- The basis index of a word: `Σ_t w_t 2^{5 - t}`. -/
def numOf (w : Wd 6) : ℕ := ∑ t : Fin 6, (w t).val * 2 ^ (5 - t.val)

theorem bitsOf_numOf : ∀ w : Wd 6, bitsOf (numOf w) = w := by decide +kernel

theorem numOf_bitsOf : ∀ n : Fin 64, numOf (bitsOf n.val) = n.val := by decide +kernel

theorem numOf_lt : ∀ w : Wd 6, numOf w < 64 := by decide +kernel

/-- The bijection `Fin 64 ≃ Wd 6` of the bit convention. -/
def wordEquiv : Fin 64 ≃ Wd 6 where
  toFun n := bitsOf n.val
  invFun w := ⟨numOf w, numOf_lt w⟩
  left_inv n := Fin.ext (numOf_bitsOf n)
  right_inv w := bitsOf_numOf w

theorem wordEquiv_apply (n : Fin 64) : wordEquiv n = bitsOf n.val := rfl

/-! ### Bilinear forms -/

/-- The bilinear form `Σ_{α,β} u_α A_{αβ} v_β`. -/
def qf {ι : Type*} [Fintype ι] (u : ι → ℂ) (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ∑ α, ∑ β, u α * A α β * v β

theorem qf_eq_dot {ι : Type*} [Fintype ι] (u : ι → ℂ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    qf u A v = u ⬝ᵥ (A *ᵥ v) := by
  simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem qf_add {ι : Type*} [Fintype ι] (u : ι → ℂ) (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    qf u (A + B) v = qf u A v + qf u B v := by
  simp only [qf, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem qf_smul {ι : Type*} [Fintype ι] (u : ι → ℂ) (c : ℂ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    qf u (c • A) v = c * qf u A v := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem qf_neg {ι : Type*} [Fintype ι] (u : ι → ℂ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    qf u (-A) v = - qf u A v := by
  simpa using qf_smul u (-1) A v

theorem qf_sub {ι : Type*} [Fintype ι] (u : ι → ℂ) (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    qf u (A - B) v = qf u A v - qf u B v := by
  rw [sub_eq_add_neg, qf_add, qf_neg]; ring

theorem qf_zero {ι : Type*} [Fintype ι] (u : ι → ℂ) (v : ι → ℂ) :
    qf u (0 : Matrix ι ι ℂ) v = 0 := by simp [qf]

theorem qf_sum {ι κ : Type*} [Fintype ι] (u : ι → ℂ) (s : Finset κ) (A : κ → Matrix ι ι ℂ)
    (v : ι → ℂ) : qf u (∑ k ∈ s, A k) v = ∑ k ∈ s, qf u (A k) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qf_zero]
  | insert a s ha ih => simp [Finset.sum_insert ha, qf_add, ih]

end FormalResearch.FourQubitEntropy.QVFrame
