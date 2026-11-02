import FormalResearch.FourQubitEntropy.QVCheck.Sector2

/-!
# `hcheck`: the contraction `Wᵀ K̂ V = 0` in every sector
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

theorem bilPl_termKron (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (A B : ℕ) (a : ℕ) (sp : Fin 4 → Spin)
    (spA : Array ℕ) (e e' : ℕ × ℤ) :
    bilPl p σ (termKron (fun r => p (σ r)) a sp spA e e') A B =
      (e.2 * e'.2) * bilN p (kronPi fun q => psiMat a (sp (σ.symm q)) (p q) (muDig spA e.1 (σ.symm q).val)
        (muDig spA e'.1 (σ.symm q).val)) A B := by
  unfold termKron
  rw [bilPl_smul, bilN_kron_placed p σ]
  congr 2
  refine congrArg kronPi (funext fun r => ?_)
  simp only [Equiv.symm_apply_apply]

theorem hs_toBlockD (k : Fin 14) (r : Fin 4) :
    mult ((blkSp (toBlockD (Bk k))).getD r.val 0) = QVCert.mult ((Bk k).spins r) := by
  rw [blkSp_toBlockD, mult_spB k r]
  have h1 := spf_toBlockD (Bk k) (fun r => (blk_spins_le k r).1) r
  have h2 : (spB k r).val = (Bk k).spins r / 2 := h1
  rw [← h2]
  rfl

theorem muDig_blk (k : Fin 14) (c : ℕ) (r : Fin 4) :
    muDig (blkSp (toBlockD (Bk k))) c r.val = QVCert.muDigit (Bk k).spins c r :=
  muDig_eq _ _ (hs_toBlockD k) c r

theorem sum_pairsList (v : List (ℕ × ℤ)) (F : (ℕ × ℤ) → (ℕ × ℤ) → ℤ) :
    ((pairsList v).map fun pr => F pr.1 pr.2).sum = ∑ s : Fin v.length, ∑ s' : Fin v.length, F (v.get s) (v.get s') := by
  unfold pairsList
  rw [sum_flatMap_map]
  have h : ∀ e : ℕ × ℤ, (((v.map fun e' => (e, e')).map fun pr => F pr.1 pr.2)).sum = (v.map fun e' => F e e').sum := by
    intro e
    rw [List.map_map]
    rfl
  simp_rw [h]
  rw [← Fin.sum_univ_fun_getElem v (fun e => (v.map fun e' => F e e').sum)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Fin.sum_univ_fun_getElem v (fun e' => F v[s.1] e')]
  rfl

theorem bilPl_termY (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (A B : ℕ) (k : Fin 14) (ti : ℕ) :
    bilPl p σ (termY (fun r => p (σ r)) (Bk k).a (spB k) (blkSp (toBlockD (Bk k))) ((Bk k).vecs.getD ti [])) A B =
      ∑ s : Fin (vlen k ti), ∑ s' : Fin (vlen k ti),
        (ent k ti s).2 * (ent k ti s').2 * bilN p (kronPi fun q => Th k ti σ s s' q (p q)) A B := by
  unfold termY
  rw [bilPl_list_sum]
  have := sum_pairsList ((Bk k).vecs.getD ti []) (fun e e' =>
    bilPl p σ (termKron (fun r => p (σ r)) (Bk k).a (spB k) (blkSp (toBlockD (Bk k))) e e') A B)
  refine this.trans (Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_)
  rw [bilPl_termKron]
  simp only [muDig_blk]
  rfl

theorem bilPl_finset_sum {ι : Type*} (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (s : Finset ι)
    (f : ι → Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ) (A B : ℕ) :
    bilPl p σ (∑ i ∈ s, f i) A B = ∑ i ∈ s, bilPl p σ (f i) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bilPl_zero p σ A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bilPl_add, ih]

theorem bilPl_Gm (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (A B : ℕ) :
    bilPl p σ (Gm p σ) A B = ∑ k : Fin 14, ∑ i : Fin (Bk k).weights.length, (Bk k).q i.val *
      ∑ s : Fin (vlen k i.val), ∑ s' : Fin (vlen k i.val),
        (ent k i.val s).2 * (ent k i.val s').2 * bilN p (kronPi fun q => Th k i.val σ s s' q (p q)) A B := by
  unfold Gm
  rw [bilPl_list_sum, blocksQ, List.map_map, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp]
  rw [bilPl_finset_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilPl_smul]
  exact congrArg (fun z => (Bk k).q i.val * z) (bilPl_termY p σ A B k i.val)

theorem mul_apply_bil (p : Fin 4 → Spin) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ)
    (A B : Fin (nnF p)) : ((Wmat p)ᵀ * M * Vmat p) A B = bil p M A B := by
  unfold bil
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem bil_Xh_rhs (p : Fin 4 → Spin) (i : RhsIdx) (A B : Fin (nnF p)) :
    bil p (kronPi fun q => Xhk (.inl i) q (p q)) A B =
      (2 * QVCert.certD * rhsCoef i) *
        bilN p (kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod)) A.val B.val := by
  rw [Xhk_inl]
  have : (fun q => (absorb (2 * QVCert.certD * rhsCoef i)
        (fun q j => ((wordOf (rhsPerm i q)).map fun n => rho0 n j).prod) : Fin 4 → ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ) q (p q)) =
      fun q => if q = 0 then (2 * QVCert.certD * rhsCoef i) • ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod
        else ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod := by
    funext q
    unfold absorb
    split_ifs <;> rfl
  rw [this, kronPi_absorb (m := fun q => Fin (multF (p q))) (n := fun q => Fin (multF (p q)))]
  rw [bil_smul]
  rfl

theorem bil_Xh_cert (p : Fin 4 → Spin) (k : Fin 14) (i : Fin (Bk k).weights.length) (σ : Equiv.Perm (Fin 4))
    (s s' : Fin (vlen k i.val)) (A B : Fin (nnF p)) :
    bil p (kronPi fun q => Xhk (.inr ⟨k, i, σ, s, s'⟩) q (p q)) A B =
      (-ccf k i.val s s') * bilN p (kronPi fun q => Th k i.val σ s s' q (p q)) A.val B.val := by
  rw [Xhk_inr]
  have : (fun q => (absorb (-ccf k i.val s s') (fun q j => Th k i.val σ s s' q j) :
        Fin 4 → ∀ j : Spin, Matrix (Fin (multF j)) (Fin (multF j)) ℤ) q (p q)) =
      fun q => if q = 0 then (-ccf k i.val s s') • Th k i.val σ s s' q (p q) else Th k i.val σ s s' q (p q) := by
    funext q
    unfold absorb
    split_ifs <;> rfl
  rw [this, kronPi_absorb (m := fun q => Fin (multF (p q))) (n := fun q => Fin (multF (p q)))]
  rw [bil_smul]
  rfl

theorem bil_Khat (p : Fin 4 → Spin) (A B : Fin (nnF p)) :
    bil p (∑ κ : KIdx, kronPi fun q => Xhk κ q (p q)) A B =
      2 * QVCert.certD * ∑ i : RhsIdx, rhsCoef i *
          bilN p (kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod)) A.val B.val -
        ∑ σ : Equiv.Perm (Fin 4), bilPl p σ (Gm p σ) A.val B.val := by
  rw [bil_finset_sum, Fintype.sum_sum_type]
  have h1 : ∑ i : RhsIdx, bil p (kronPi fun q => Xhk (.inl i) q (p q)) A B =
      2 * QVCert.certD * ∑ i : RhsIdx, rhsCoef i *
          bilN p (kronPi (fun q => ((wordOf (rhsPerm i q)).map fun n => rho0 n (p q)).prod)) A.val B.val := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bil_Xh_rhs]; ring
  have h2 : ∑ c : CertIdx, bil p (kronPi fun q => Xhk (.inr c) q (p q)) A B =
      -∑ σ : Equiv.Perm (Fin 4), bilPl p σ (Gm p σ) A.val B.val := by
    simp only [bilPl_Gm]
    simp only [Fintype.sum_sigma, Fintype.sum_prod_type, bil_Xh_cert]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    unfold ccf
    ring
  rw [h1, h2, sub_eq_add_neg]

theorem certD_eq : QVCert.certD = DataStr.certDen := rfl

theorem hcheck_of_check (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true) (p : Fin 4 → Spin) :
    (Wmat p)ᵀ * (∑ κ : KIdx, kronPi fun q => Xhk κ q (p q)) * Vmat p = 0 := by
  ext A B
  rw [mul_apply_bil, bil_Khat]
  have hn : 0 < nn (pcode p) := by
    have := A.2
    unfold nnF at this
    omega
  have h := sector_identity hall p hn A.val B.val A.2 B.2
  rw [rhs_sum] at h
  rw [certD_eq, h]
  simp

end QVCheck
