import FormalResearch.FourQubitEntropy.QVCheck.RhsWords
import FormalResearch.FourQubitEntropy.QVFrame.FinalQV

/-!
# Assembly of the checker semantics with the block calculus
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

abbrev Bk (k : Fin 14) : QVCert.Block := QVCert.blk k

/-- absorb a coefficient into qubit `0` -/
def absorb {α : Type*} [SMul ℤ α] (c : ℤ) (f : Fin 4 → α) : Fin 4 → α := fun q => if q = 0 then c • f q else f q

theorem kronPi_absorb {m n : Fin 4 → Type*} [∀ q, Fintype (m q)] [∀ q, Fintype (n q)] (c : ℤ)
    (M : ∀ q, Matrix (m q) (n q) ℤ) :
    kronPi (fun q => if q = 0 then c • M q else M q) = c • kronPi M := by
  ext a b
  simp only [kronPi_apply, Matrix.smul_apply, smul_eq_mul, Fin.prod_univ_four]
  simp
  ring

theorem blk_smulZ (c : ℤ) (X : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ) :
    blk dimF (fun j => c • X j) = c • blk dimF X := by
  ext ⟨j, k, μ⟩ ⟨j', k', μ'⟩
  by_cases h : j = j'
  · subst h
    simp only [blk_same, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  · simp [blk_ne dimF _ h]

theorem blk_a_mem : ∀ k : Fin 14, (Bk k).a ∈ ({3, 4} : Finset ℕ) := by decide +kernel

/-- the spins of a block as elements of `Spin` -/
def spB (k : Fin 14) : Fin 4 → Spin := spf (toBlockD (Bk k))

theorem two_mul_spB (k : Fin 14) (q : Fin 4) : 2 * (spB k q).val = (Bk k).spins q :=
  two_mul_spf _ (blk_spins_le k) q

theorem mult_spB (k : Fin 14) (q : Fin 4) : QVCert.mult ((Bk k).spins q) = multF (spB k q) := by
  rw [← two_mul_spB, mult_bridge]

abbrev vlen (k : Fin 14) (i : ℕ) : ℕ := ((Bk k).vecs.getD i []).length

/-- the certificate part of the index set: block, covariant, qubit permutation, entries of the multiplicity vector -/
abbrev CertIdx : Type :=
  Σ k : Fin 14, Σ i : Fin (Bk k).weights.length, Equiv.Perm (Fin 4) × Fin (vlen k i.val) × Fin (vlen k i.val)

abbrev KIdx : Type := RhsIdx ⊕ CertIdx

def ent (k : Fin 14) (i : ℕ) (s : Fin (vlen k i)) : ℕ × ℤ := ((Bk k).vecs.getD i []).get s

def ccf (k : Fin 14) (i : ℕ) (s s' : Fin (vlen k i)) : ℤ := (Bk k).q i * ((ent k i s).2 * (ent k i s').2)

/-- the per-qubit factor of a certificate term (frame-6 operator) -/
def Tm (k : Fin 14) (i : ℕ) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i)) (q : Fin 4) : Matrix (Wd 6) (Wd 6) ℤ :=
  tau (Bk k).a (Eop ((Bk k).spins (σ.symm q)) (QVCert.muDigit (Bk k).spins (ent k i s).1 (σ.symm q))
    (QVCert.muDigit (Bk k).spins (ent k i s').1 (σ.symm q)))

/-- its block data -/
def Th (k : Fin 14) (i : ℕ) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i)) (q : Fin 4) (j : Spin) :
    Matrix (Fin (multF j)) (Fin (multF j)) ℤ :=
  psiMat (Bk k).a (spB k (σ.symm q)) j (QVCert.muDigit (Bk k).spins (ent k i s).1 (σ.symm q))
    (QVCert.muDigit (Bk k).spins (ent k i s').1 (σ.symm q))

def Xk : KIdx → Fin 4 → Matrix (Wd 6) (Wd 6) ℤ
  | .inl i => absorb (2 * QVCert.certD * rhsCoef i) fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ)
  | .inr ⟨k, i, σ, s, s'⟩ => absorb (-ccf k i.val s s') fun q => Tm k i.val σ s s' q

def Xhk : KIdx → Fin 4 → ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ
  | .inl i => absorb (2 * QVCert.certD * rhsCoef i) fun q j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod
  | .inr ⟨k, i, σ, s, s'⟩ => absorb (-ccf k i.val s s') fun q j => Th k i.val σ s s' q j

theorem hX_absorb (c : ℤ) (M : Fin 4 → Matrix (Wd 6) (Wd 6) ℤ)
    (Mh : Fin 4 → ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)
    (h : ∀ q, Cmat * M q = blk dimF (Mh q) * Cmat) (q : Fin 4) :
    Cmat * absorb c M q = blk dimF (absorb c Mh q) * Cmat := by
  unfold absorb
  by_cases hq : q = 0
  · simp only [hq, if_true]
    rw [Matrix.mul_smul, h, ← Matrix.smul_mul]
    congr 1
    exact (blk_smulZ c (Mh 0)).symm
  · simp only [hq, if_false]
    exact h q

theorem muDigit_lt (k : Fin 14) (c : ℕ) (r : Fin 4) : QVCert.muDigit (Bk k).spins c r < multF (spB k r) := by
  rw [← mult_spB]
  unfold QVCert.muDigit
  exact Nat.mod_lt _ (by rw [mult_spB]; exact multF_pos _)

theorem Xk_inl (i : RhsIdx) : Xk (.inl i) =
    absorb (2 * QVCert.certD * rhsCoef i) fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ) := rfl

theorem Xhk_inl (i : RhsIdx) : Xhk (.inl i) =
    absorb (2 * QVCert.certD * rhsCoef i) fun q j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod := rfl

theorem Xk_inr (k : Fin 14) (i : Fin (Bk k).weights.length) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i.val)) :
    Xk (.inr ⟨k, i, σ, s, s'⟩) = absorb (-ccf k i.val s s') fun q => Tm k i.val σ s s' q := rfl

theorem Xhk_inr (k : Fin 14) (i : Fin (Bk k).weights.length) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i.val)) :
    Xhk (.inr ⟨k, i, σ, s, s'⟩) = absorb (-ccf k i.val s s') fun q j => Th k i.val σ s s' q j := rfl

theorem hX_rhs (hS : checkSlots () = true) (i : RhsIdx) (q : Fin 4) :
    Cmat * (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ) =
      blk dimF (fun j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod) * Cmat := by
  have h := blk_word hS (wordOf (rhsPerm i q))
  rw [wordOf_spec i q] at h
  have e : (fun j : Spin => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod) =
      ((wordOf (rhsPerm i q)).map fun n => (fun j : Spin => rho0 n j : ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ)).prod :=
    funext fun j => (blk_word_apply (wordOf (rhsPerm i q)) j).symm
  rw [h, e]

theorem hX_cert (hP : checkPsi () = true) (k : Fin 14) (i : ℕ) (σ : Equiv.Perm (Fin 4)) (s s' : Fin (vlen k i))
    (q : Fin 4) : Cmat * Tm k i σ s s' q = blk dimF (fun j => Th k i σ s s' q j) * Cmat := by
  unfold Tm
  rw [← two_mul_spB k (σ.symm q)]
  exact hPsi_of_check hP _ (blk_a_mem k) (spB k (σ.symm q)) _ _ (muDigit_lt k _ _) (muDigit_lt k _ _)

theorem hXk (hS : checkSlots () = true) (hP : checkPsi () = true) (κ : KIdx) (q : Fin 4) :
    Cmat * Xk κ q = blk dimF (Xhk κ q) * Cmat := by
  rcases κ with i | ⟨k, i, σ, s, s'⟩
  · rw [Xk_inl, Xhk_inl]
    exact hX_absorb _ _ _ (hX_rhs hS i) q
  · rw [Xk_inr, Xhk_inr]
    exact hX_absorb _ _ _ (hX_cert hP k i.val σ s s') q

theorem lsum_eq_fin (v : List (ℕ × ℤ)) (f : ℕ × ℤ → Matrix (Cfg 6) (Cfg 6) ℤ) :
    lsum v f = ∑ s : Fin v.length, f (v.get s) := by
  unfold lsum
  rw [← Fin.sum_univ_fun_getElem]
  rfl

theorem cert_ki (k : Fin 14) (i : ℕ) :
    ∑ σ : Equiv.Perm (Fin 4), ∑ s : Fin (vlen k i), ∑ s' : Fin (vlen k i),
        (-ccf k i s s') • kronPi (fun q => Tm k i σ s s' q) =
      -((Bk k).q i • tauGram (Bk k).a (Bk k).spins ((Bk k).vecs.getD i [])) := by
  unfold tauGram
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [lsum_eq_fin, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lsum_eq_fin, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  unfold ccf Tm ent
  rw [smul_smul, neg_smul]

theorem Xsum : ∑ κ : KIdx, kronPi (Xk κ) =
    Kfam (fun k : Fin 14 => Bk k) (fun k => (Bk k).weights.length) (fun k i => (Bk k).q i) QVCert.certD := by
  unfold Kfam certFam rhsOp
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : RhsIdx, kronPi (Xk (.inl i)) =
      (2 * QVCert.certD) • ∑ i : RhsIdx, rhsCoef i •
        kronPi (fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Xk_inl]
    unfold absorb
    rw [kronPi_absorb (m := fun _ => Wd 6) (n := fun _ => Wd 6) (2 * QVCert.certD * rhsCoef i)
      (fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ)), smul_smul]
  have h2 : ∑ c : CertIdx, kronPi (Xk (.inr c)) =
      -∑ k : Fin 14, ∑ i ∈ range (Bk k).weights.length, (Bk k).q i • tauGram (Bk k).a (Bk k).spins ((Bk k).vecs.getD i []) := by
    rw [Fintype.sum_sigma, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_sigma, Finset.sum_range, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cert_ki k i.val, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [Xk_inr]
    unfold absorb
    rw [kronPi_absorb (m := fun _ => Wd 6) (n := fun _ => Wd 6) (-ccf k i.val s s')
      (fun q => Tm k i.val σ s s' q)]
  rw [h1, h2, sub_eq_add_neg]

end QVCheck
