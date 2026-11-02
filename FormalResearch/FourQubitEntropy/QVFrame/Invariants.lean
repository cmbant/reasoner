import FormalResearch.FourQubitEntropy.QVFrame.Twist

/-!
# Permutation invariants (T3, generic part)

For a family `s : Fin 4 → Perm ι` of per-qubit slot permutations and `z : Site → ℂ`,

`invG ι s z = Σ_{c : ι → Site} ∏_t conj z(q ↦ c_{s_q⁻¹ t}(q)) · z(c_t)`

is the Hermitian form `⟨z^{⊗ι}, (⊗_q Π_{s_q}) z^{⊗ι}⟩` of the slot-permutation operator (`qf_slot`).
It is invariant under relabelling the slots (`invG_equiv`), multiplicative over disjoint slot blocks
(`invG_sum`, `invG_bsum`), equals `N^{|ι|}` for the identity (`invG_one`) and transforms under a relabelling
of the qubits (`invG_qperm`).
-/

open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

/-- `Σ_{c : ι → Site} ∏_t conj z(…) z(c_t)`: the permutation invariant of `(s_q)_q`. -/
def invG (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Fin 4 → Equiv.Perm ι) (z : Site → ℂ) : ℂ :=
  ∑ c : ι → Site, ∏ t : ι, conj (z (fun q => c ((s q).symm t) q)) * z (c t)

section generic
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem permCongr_symm_apply {ι κ : Type*} (e : ι ≃ κ) (p : Equiv.Perm ι) (t : ι) :
    (e.permCongr p).symm (e t) = e (p.symm t) := by
  rw [Equiv.symm_apply_eq]; simp [Equiv.permCongr_apply]

/-- Relabelling the slots does not change the invariant. -/
theorem invG_equiv (e : ι ≃ κ) (s : Fin 4 → Equiv.Perm ι) (z : Site → ℂ) :
    invG κ (fun q => e.permCongr (s q)) z = invG ι s z := by
  unfold invG
  let E : (ι → Site) ≃ (κ → Site) := Equiv.arrowCongr e (Equiv.refl _)
  rw [← E.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [E, permCongr_symm_apply, Equiv.arrowCongr_apply]

/-- The invariant of two disjoint slot blocks is the product. -/
theorem invG_sum (s : Fin 4 → Equiv.Perm ι) (s' : Fin 4 → Equiv.Perm κ) (z : Site → ℂ) :
    invG (ι ⊕ κ) (fun q => Equiv.sumCongr (s q) (s' q)) z = invG ι s z * invG κ s' z := by
  unfold invG
  rw [← (Equiv.sumArrowEquivProdArrow ι κ Site).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
  rw [Fintype.prod_sum_type]
  simp [Equiv.sumArrowEquivProdArrow]

/-- The identity invariant is `N^{|ι|}`. -/
theorem invG_one (z : Site → ℂ) :
    invG ι (fun _ => 1) z = (∑ c : Site, conj (z c) * z c) ^ Fintype.card ι := by
  unfold invG
  have := Fintype.prod_sum (fun (_ : ι) (c : Site) => conj (z c) * z c)
  rw [Finset.prod_const, Finset.card_univ] at this
  have h : ∀ (c : ι → Site) (t : ι), (fun q => c ((1 : Equiv.Perm ι).symm t) q) = c t := fun c t => rfl
  simp only [h]
  exact this.symm

/-- Relabelling the qubits transforms `z` by the same permutation. -/
theorem invG_qperm (ρ : Equiv.Perm (Fin 4)) (s : Fin 4 → Equiv.Perm ι) (z : Site → ℂ) :
    invG ι (fun q => s (ρ q)) z = invG ι s (fun y => z (fun q => y (ρ q))) := by
  unfold invG
  let E : (ι → Site) ≃ (ι → Site) := Equiv.piCongrRight fun _ => Equiv.arrowCongr ρ.symm (Equiv.refl (Fin 2))
  rw [← E.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.prod_congr rfl fun t _ => ?_
  rfl

end generic

/-- Block sum of slot permutation families. -/
def bsum {a b : ℕ} (sa : Fin 4 → Equiv.Perm (Fin a)) (sb : Fin 4 → Equiv.Perm (Fin b)) :
    Fin 4 → Equiv.Perm (Fin (a + b)) :=
  fun q => finSumFinEquiv.permCongr (Equiv.sumCongr (sa q) (sb q))

theorem invG_bsum {a b : ℕ} (sa : Fin 4 → Equiv.Perm (Fin a)) (sb : Fin 4 → Equiv.Perm (Fin b))
    (z : Site → ℂ) : invG (Fin (a + b)) (bsum sa sb) z = invG (Fin a) sa z * invG (Fin b) sb z :=
  (invG_equiv finSumFinEquiv (fun q => Equiv.sumCongr (sa q) (sb q)) z).trans (invG_sum sa sb z)

/-! ### The operator side -/

/-- The Hermitian form of `⊗_q slotPerm (s q)` on `z^{⊗n}` is `invG`. -/
theorem qf_slot {n : ℕ} (s : Fin 4 → Equiv.Perm (Fin n)) (z : Site → ℂ) :
    qf (copyPower (fun c => conj (z c)) n) (kronPi fun q => (slotPerm ℂ (s q) : Matrix (Wd n) (Wd n) ℂ))
      (copyPower z n) = invG (Fin n) s z := by
  classical
  unfold qf
  have hker : ∀ β α : Cfg n, (∏ q, (slotPerm ℂ (s q) : Matrix (Wd n) (Wd n) ℂ) (β q) (α q)) =
      if β = (fun q => slotAct (s q) (α q)) then 1 else 0 := by
    intro β α
    simp only [slotPerm_apply]
    rw [Finset.prod_ite_zero]
    · simp [funext_iff]
  simp only [kronPi_apply, hker]
  have h1 : ∀ α : Cfg n, ∑ β : Cfg n, copyPower (fun c => conj (z c)) n β *
      (if β = (fun q => slotAct (s q) (α q)) then 1 else 0) * copyPower z n α =
      copyPower (fun c => conj (z c)) n (fun q => slotAct (s q) (α q)) * copyPower z n α := by
    intro α
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [h1]
  unfold invG
  let e : Cfg n ≃ (Fin n → Site) := Equiv.piComm (fun _ _ => Fin 2)
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [copyPower_eq_prod, copyPower_eq_prod, ← Finset.prod_mul_distrib]
  rfl

end FormalResearch.FourQubitEntropy.QVFrame
