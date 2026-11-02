import FormalResearch.FourQubitEntropy.QVCheck.Qtot

/-!
# Placements (K5): the 24 qubit permutations
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- the `pii`-th permutation of the checker as a function on `Fin 4` -/
def permSigma (pii : ℕ) : Fin 4 → Fin 4 := fun q => ⟨(perms4.getD pii #[]).getD q.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩

theorem permSigma_bij : ∀ pii : Fin 24, Function.Bijective (permSigma pii.val) := by native_decide

theorem permSigma_inj : ∀ a b : Fin 24, permSigma a.val = permSigma b.val → a = b := by native_decide

theorem perms4_entry : ∀ pii : Fin 24, ∀ q : Fin 4,
    (perms4.getD pii.val #[]).getD q.val 0 < 4 ∧ (perms4.getD pii.val #[]).size = 4 := by native_decide

/-- the permutation of `Fin 4` -/
noncomputable def sg (pii : Fin 24) : Equiv.Perm (Fin 4) := Equiv.ofBijective (permSigma pii.val) (permSigma_bij pii)

theorem sg_apply (pii : Fin 24) (q : Fin 4) : (sg pii) q = permSigma pii.val q := rfl

theorem sg_inj : Function.Injective sg := by
  intro a b h
  apply permSigma_inj
  funext q
  exact congrArg (fun σ : Equiv.Perm (Fin 4) => σ q) h

theorem sg_bij : Function.Bijective sg := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨sg_inj, ?_⟩
  simp [Fintype.card_perm]; rfl

theorem sum_perm4 (F : Equiv.Perm (Fin 4) → ℤ) : ∑ σ : Equiv.Perm (Fin 4), F σ = ∑ pii : Fin 24, F (sg pii) := by
  exact (Fintype.sum_bijective sg sg_bij (fun pii => F (sg pii)) F (fun _ => rfl)).symm


/-- strides of the mixed-radix flattening -/
def strideM (m : Fin 4 → ℕ) : Fin 4 → ℕ := ![m 1 * m 2 * m 3, m 2 * m 3, m 3, 1]

theorem stride_pcode (p : Fin 4 → Spin) (q : Fin 4) : stride (pcode p) q.val = strideM (radix p) q := by
  obtain ⟨h0, h1, h2, h3⟩ := stride_eq (pcode p)
  have d0 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  have d1 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have d2 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  fin_cases q
  · simp only [strideM]; show stride (pcode p) 0 = _
    rw [h0, d0, d1, d2]; rfl
  · simp only [strideM]; show stride (pcode p) 1 = _
    rw [h1, d1, d2]; rfl
  · simp only [strideM]; show stride (pcode p) 2 = _
    rw [h2, d2]; rfl
  · simp only [strideM]; show stride (pcode p) 3 = _
    rw [h3]; rfl

theorem digit_lem (a r b m s : ℕ) (hr : r < m) (hb : b < s) : ((a * m + r) * s + b) / s % m = r := by
  have hs : 0 < s := by omega
  have : ((a * m + r) * s + b) / s = a * m + r := by
    rw [Nat.mul_comm (a * m + r) s, Nat.mul_add_div hs, Nat.div_eq_of_lt hb]; simp
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem flatIx_digit (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) (q : Fin 4) :
    flatIx m x / strideM m q % m q = (x q).val := by
  have b0 := (x 0).2; have b1 := (x 1).2; have b2 := (x 2).2; have b3 := (x 3).2
  have hB0 : ((x 1).val * m 2 + (x 2).val) * m 3 + (x 3).val < m 1 * m 2 * m 3 := by
    have := flat4_lt (m0 := 1) (m1 := m 1) (m2 := m 2) (m3 := m 3) (a := 0) (b := (x 1).val) (c := (x 2).val)
      (d := (x 3).val) (by omega) b1 b2 b3
    unfold flat4 at this; simpa using this
  have hB1 : (x 2).val * m 3 + (x 3).val < m 2 * m 3 := by
    have := flat4_lt (m0 := 1) (m1 := 1) (m2 := m 2) (m3 := m 3) (a := 0) (b := 0) (c := (x 2).val)
      (d := (x 3).val) (by omega) (by have := (x 1).2; omega) b2 b3
    unfold flat4 at this; simpa using this
  rw [flatIx_eq]
  fin_cases q
  · simp only [strideM]
    show _ / (m 1 * m 2 * m 3) % m 0 = (x 0).val
    rw [show ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
      (0 * m 0 + (x 0).val) * (m 1 * m 2 * m 3) + (((x 1).val * m 2 + (x 2).val) * m 3 + (x 3).val) by ring]
    exact digit_lem 0 (x 0).val _ (m 0) (m 1 * m 2 * m 3) b0 hB0
  · simp only [strideM]
    show _ / (m 2 * m 3) % m 1 = (x 1).val
    rw [show ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
      ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) from rfl]
    exact digit_lem (x 0).val (x 1).val _ (m 1) (m 2 * m 3) b1 hB1
  · simp only [strideM]
    show _ / m 3 % m 2 = (x 2).val
    rw [show ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
      (((x 0).val * m 1 + (x 1).val) * m 2 + (x 2).val) * m 3 + (x 3).val by ring]
    exact digit_lem ((x 0).val * m 1 + (x 1).val) (x 2).val (x 3).val (m 2) (m 3) b2 b3
  · simp only [strideM]
    show _ / 1 % m 3 = (x 3).val
    rw [Nat.div_one]
    have : ((x 0).val * m 1 + (x 1).val) * (m 2 * m 3) + ((x 2).val * m 3 + (x 3).val) =
        ((((x 0).val * m 1 + (x 1).val) * m 2 + (x 2).val)) * m 3 + (x 3).val := by ring
    rw [this, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt b3]


theorem flatIx_sum (m : Fin 4 → ℕ) (x : ∀ q : Fin 4, Fin (m q)) :
    flatIx m x = ∑ q : Fin 4, (x q).val * strideM m q := by
  rw [flatIx_eq, Fin.sum_univ_four]
  simp only [strideM]
  simp
  ring

theorem placed_eq (p : Fin 4 → Spin) (pii : Fin 24) :
    placedCode (pcode p) (perms4.getD pii.val #[]) = pcode (fun r => p (sg pii r)) := by
  have e : ∀ q : Fin 4, spinDigit (pcode p) ((perms4.getD pii.val #[]).getD q.val 0) = (p (sg pii q)).val := by
    intro q
    have h1 := (perms4_entry pii q).1
    have : (perms4.getD pii.val #[]).getD q.val 0 = ((sg pii) q).val := by
      rw [sg_apply]; unfold permSigma; simp only; exact (Nat.mod_eq_of_lt h1).symm
    rw [this, spinDigit_pcode p (sg pii q)]
  have e0 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 0 0) = (p (sg pii 0)).val := e 0
  have e1 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 1 0) = (p (sg pii 1)).val := e 1
  have e2 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 2 0) = (p (sg pii 2)).val := e 2
  have e3 : spinDigit (pcode p) ((perms4.getD pii.val #[]).getD 3 0) = (p (sg pii 3)).val := e 3
  unfold placedCode
  rw [e0, e1, e2, e3]
  rfl


theorem foldl_range4 (g : ℕ → ℕ) : (List.range 4).foldl (fun acc q => acc + g q) 0 = g 0 + g 1 + g 2 + g 3 := by
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]; simp [List.foldl]

theorem flat_perm (p : Fin 4 → Spin) (pii : Fin 24) (x : ∀ r : Fin 4, Fin (multF (p (sg pii r)))) :
    flatIx (radix p) (Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x) =
      permFlatIdx (pcode p) (perms4.getD pii.val #[]) (flatIx (radix (fun r => p (sg pii r))) x) := by
  unfold permFlatIdx
  rw [placed_eq p pii, foldl_range4]
  rw [flatIx_sum, ← Equiv.sum_comp (sg pii)]
  have hsum : ∀ g : ℕ → ℕ, g 0 + g 1 + g 2 + g 3 = ∑ q : Fin 4, g q.val := by
    intro g; rw [Fin.sum_univ_four]; rfl
  have key : ∀ q : Fin 4,
      (flatIx (radix (fun r => p (sg pii r))) x / stride (pcode (fun r => p (sg pii r))) q.val %
        mult (spinDigit (pcode (fun r => p (sg pii r))) q.val)) *
        stride (pcode p) ((perms4.getD pii.val #[]).getD q.val 0) =
      ((Equiv.piCongrLeft (fun q => Fin (multF (p q))) (sg pii) x) (sg pii q)).val * strideM (radix p) (sg pii q) := by
    intro q
    have hd := flatIx_digit (radix (fun r => p (sg pii r))) x q
    rw [stride_pcode, spinDigit_pcode]
    have hm : mult ((p (sg pii q)).val) = radix (fun r => p (sg pii r)) q := rfl
    rw [hm, hd]
    have h1 := (perms4_entry pii q).1
    have : (perms4.getD pii.val #[]).getD q.val 0 = ((sg pii) q).val := by
      rw [sg_apply]; unfold permSigma; simp only; exact (Nat.mod_eq_of_lt h1).symm
    rw [this, stride_pcode, Equiv.piCongrLeft_apply_apply]
  refine (Finset.sum_congr rfl fun q _ => (key q).symm).trans ?_
  exact (hsum (fun q => flatIx (radix (fun r => p (sg pii r))) x / stride (pcode (fun r => p (sg pii r))) q %
    mult (spinDigit (pcode (fun r => p (sg pii r))) q) * stride (pcode p) ((perms4.getD pii.val #[]).getD q 0))).symm

end QVCheck
