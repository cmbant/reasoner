import FormalResearch.FourQubitEntropy.QVBlock.Kron

/-!
# Copy symmetriser and `z^{⊗n}` (QV block calculus, T4)

`n` copies of a system of `Q`-many parties with local index set `σ`.  A word of one party is
`Fin n → σ`; the space of the `n` copies is indexed by `Q → Fin n → σ` (party-major regrouping).
For `z : (Q → σ) → 𝕜`, `copyPower z a = ∏ t, z (fun q => a q t)` is the vector `z^{⊗n}`.

* `slotPerm π`: the slot permutation operator of one party; `slotPerm_mul`, `slotPerm_one`.
* `copySym`: the `S_n` copy-symmetriser `(1/n!) ∑_π ⊗_q slotPerm π` (T4).
* `copySym_mulVec_copyPower`, `copyPower_vecMul_copySym`: `P ψ = ψ`, `ψᵀ P = ψᵀ`.
* `copyPower_quad_eq_zero` (T4): `P K P = 0 → ψᵀ K ψ = 0`.
-/

open scoped Matrix BigOperators

namespace FormalResearch.FourQubitEntropy.QVBlock

set_option linter.unusedSectionVars false

section
variable {𝕜 : Type*} [Field 𝕜]
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The left action of a slot permutation on a word: `(π • c) t = c (π⁻¹ t)`. -/
def slotAct (π : Equiv.Perm (Fin n)) (c : Fin n → σ) : Fin n → σ := c ∘ π.symm

/-- The slot permutation operator of one party, `|c⟩ ↦ |π • c⟩`.  It is a representation
(`slotPerm_mul`).  For an involution `π` it is `|c⟩ ↦ |c ∘ π⟩`. -/
def slotPerm (𝕜 : Type*) [Zero 𝕜] [One 𝕜] (π : Equiv.Perm (Fin n)) :
    Matrix (Fin n → σ) (Fin n → σ) 𝕜 :=
  Matrix.of fun a c => if a = slotAct π c then 1 else 0

theorem slotPerm_apply (π : Equiv.Perm (Fin n)) (a c : Fin n → σ) :
    slotPerm 𝕜 π a c = if a = slotAct π c then 1 else 0 := rfl

theorem slotPerm_mul (π τ : Equiv.Perm (Fin n)) :
    slotPerm 𝕜 (π * τ) = (slotPerm 𝕜 π * slotPerm 𝕜 τ : Matrix (Fin n → σ) (Fin n → σ) 𝕜) := by
  ext a c
  simp only [slotPerm_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single (slotAct τ c)]
  · have : slotAct (π * τ) c = slotAct π (slotAct τ c) := rfl
    simp [this]
  · intro b _ hb
    simp [hb]
  · simp

theorem slotPerm_one :
    slotPerm 𝕜 (1 : Equiv.Perm (Fin n)) = (1 : Matrix (Fin n → σ) (Fin n → σ) 𝕜) := by
  ext a c
  have h : slotAct (1 : Equiv.Perm (Fin n)) c = c := rfl
  simp [slotPerm_apply, h, Matrix.one_apply]

/-- The diagonal slot permutation on all parties. -/
def copyPerm (𝕜 : Type*) [Field 𝕜] (Q σ : Type*) [Fintype Q] [DecidableEq Q]
    [Fintype σ] [DecidableEq σ] {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Matrix (Q → Fin n → σ) (Q → Fin n → σ) 𝕜 :=
  kronPi (fun _ : Q => slotPerm 𝕜 π)

/-- The `S_n` copy-symmetriser (T4). -/
noncomputable def copySym (𝕜 : Type*) [Field 𝕜] (Q σ : Type*) [Fintype Q] [DecidableEq Q]
    [Fintype σ] [DecidableEq σ] (n : ℕ) :
    Matrix (Q → Fin n → σ) (Q → Fin n → σ) 𝕜 :=
  ((Fintype.card (Equiv.Perm (Fin n)) : 𝕜)⁻¹) • ∑ π : Equiv.Perm (Fin n), copyPerm 𝕜 Q σ π

/-- The vector `z^{⊗n}` regrouped party-wise. -/
def copyPower (z : (Q → σ) → 𝕜) (n : ℕ) : (Q → Fin n → σ) → 𝕜 :=
  fun a => ∏ t : Fin n, z (fun q => a q t)

theorem copyPerm_apply (π : Equiv.Perm (Fin n)) (a c : Q → Fin n → σ) :
    copyPerm 𝕜 Q σ π a c = if a = fun q => slotAct π (c q) then 1 else 0 := by
  simp only [copyPerm, kronPi_apply, slotPerm_apply]
  rw [Finset.prod_ite_zero]
  · simp [funext_iff]

theorem copyPerm_mulVec_copyPower (π : Equiv.Perm (Fin n)) (z : (Q → σ) → 𝕜) :
    copyPerm 𝕜 Q σ π *ᵥ copyPower z n = copyPower z n := by
  ext a
  simp only [Matrix.mulVec, dotProduct, copyPerm_apply]
  rw [Finset.sum_eq_single (fun q => (a q) ∘ π)]
  · have h1 : (fun q => slotAct π ((a q) ∘ π)) = a := by
      ext q t; simp [slotAct]
    simp only [h1, ite_true, one_mul, copyPower]
    exact Equiv.prod_comp π (fun t => z (fun q => a q t))
  · intro c _ hc
    have : ¬ a = fun q => slotAct π (c q) := by
      intro h
      apply hc
      ext q t
      have := congrFun (congrFun h q) (π t)
      simpa [slotAct] using this.symm
    simp [this]
  · simp

theorem copyPower_vecMul_copyPerm (π : Equiv.Perm (Fin n)) (z : (Q → σ) → 𝕜) :
    copyPower z n ᵥ* copyPerm 𝕜 Q σ π = copyPower z n := by
  ext c
  simp only [Matrix.vecMul, dotProduct, copyPerm_apply]
  rw [Finset.sum_eq_single (fun q => slotAct π (c q))]
  · simp only [ite_true, mul_one, copyPower]
    exact Equiv.prod_comp π.symm (fun t => z (fun q => c q t))
  · intro a _ ha
    simp [ha]
  · simp

theorem copySym_mulVec_copyPower [CharZero 𝕜] (z : (Q → σ) → 𝕜) :
    copySym 𝕜 Q σ n *ᵥ copyPower z n = copyPower z n := by
  unfold copySym
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [copyPerm_mulVec_copyPower, Finset.sum_const, Finset.card_univ]
  have h : (Fintype.card (Equiv.Perm (Fin n)) : 𝕜) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem copyPower_vecMul_copySym [CharZero 𝕜] (z : (Q → σ) → 𝕜) :
    copyPower z n ᵥ* copySym 𝕜 Q σ n = copyPower z n := by
  unfold copySym
  rw [Matrix.vecMul_smul, Matrix.vecMul_sum]
  simp only [copyPower_vecMul_copyPerm, Finset.sum_const, Finset.card_univ]
  have h : (Fintype.card (Equiv.Perm (Fin n)) : 𝕜) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The bilinear form of `K` on `ψ', ψ` equals that of `P K P` when `ψ` is `P`-fixed on the right
and `ψ'` on the left. -/
theorem quad_eq_of_fixed {ι : Type*} [Fintype ι] (ψ' ψ : ι → 𝕜) (P K : Matrix ι ι 𝕜)
    (hr : P *ᵥ ψ = ψ) (hl : ψ' ᵥ* P = ψ') :
    ψ' ⬝ᵥ (K *ᵥ ψ) = ψ' ⬝ᵥ ((P * K * P) *ᵥ ψ) := by
  have : ψ' ⬝ᵥ ((P * K * P) *ᵥ ψ) = ψ' ⬝ᵥ (P *ᵥ (K *ᵥ (P *ᵥ ψ))) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [this, hr, Matrix.dotProduct_mulVec ψ' P, hl]

/-- **T4 (easy polarisation, bilinear form).** If `P K P = 0` for the copy-symmetriser `P`, then
`⟨z'^{⊗n}, K z^{⊗n}⟩ = 0` for all `z', z` (two independent vectors, so also the sesquilinear
form `⟨conj z^{⊗n}, K z^{⊗n}⟩`). -/
theorem copyPower_quad_eq_zero [CharZero 𝕜] (K : Matrix (Q → Fin n → σ) (Q → Fin n → σ) 𝕜)
    (hK : copySym 𝕜 Q σ n * K * copySym 𝕜 Q σ n = 0) (z' z : (Q → σ) → 𝕜) :
    copyPower z' n ⬝ᵥ (K *ᵥ copyPower z n) = 0 := by
  rw [quad_eq_of_fixed (copyPower z' n) (copyPower z n) _ K (copySym_mulVec_copyPower z)
    (copyPower_vecMul_copySym z'), hK]
  simp

end

end FormalResearch.FourQubitEntropy.QVBlock
