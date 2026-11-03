module

public import FormalResearch.FourQubitEntropy.QVBlock.IntCert
public import FormalResearch.FourQubitEntropy.QVCert.Reduction
public import FormalResearch.FourQubitEntropy.QVCheck.Bridge
public import FormalResearch.FourQubitEntropy.QVFrame.Assembly

/-!
# The certificate from `checkAll`

`sector_identity`: in every sector the placed `Qtot` agrees with the right-hand side; `hcheck_of_check`: the contraction
`Wᵀ K̂ V = 0`; `kfam_bilinear`: every hypothesis of `QVBlock.quad_eq_zero_of_int_certificate` follows from
`checkAll blocksQ rhsTermsQ certDen () = true`, whence the bilinear form of `Kfam` vanishes on all `u^{⊗6}, v^{⊗6}`.
-/

@[expose] public section


open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame
open scoped Matrix

namespace QVCheck

/-!
## The sector identity from the checker
-/

/-- the covariant operator of all blocks, placed in the sector `p ∘ σ` -/
def Gm (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) :
    Matrix (∀ r, Fin (multF (p (σ r)))) (∀ r, Fin (multF (p (σ r)))) ℤ :=
  (blocksQ.map fun b => ∑ ti ∈ range b.2.2.1.length,
    b.2.2.1.getD ti 0 • termY (fun r => p (σ r)) b.1 (spf b) (blkSp b) (b.2.2.2.getD ti [])).sum

theorem Qsem_eq_bilN (p : Fin 4 → Spin) (σ : Equiv.Perm (Fin 4)) (A B : ℕ) :
    Qsem blocksQ spf (fun r => p (σ r)) A B = bilN (fun r => p (σ r)) (Gm p σ) A B := by
  unfold Qsem Gm
  rw [bilN_list_sum]
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  rw [bilN_finset_sum]
  refine Finset.sum_congr rfl fun ti _ => ?_
  rw [bilN_smul]

theorem checkAll_parts (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true) :
    checkT () = true ∧ checkU () = true ∧ checkStructure () = true ∧ checkPlacements () = true ∧
    blocksQ.all rowsOk = true ∧ (qtotAll (runAll blocksQ)).2 = true ∧
    checkFinal rhsTermsQ (qtotAll (runAll blocksQ)).1 DataStr.certDen = true := by
  unfold checkAll at hall
  simp only [Bool.and_eq_true] at hall
  exact ⟨hall.1.1.1.1.1.2, hall.1.1.1.1.2, hall.1.1.1.2, hall.1.1.2, hall.1.2, hall.2.1, hall.2.2⟩

theorem hbs_blocksQ (hrows : blocksQ.all rowsOk = true) :
    ∀ b ∈ blocksQ, rowsOk b = true ∧ b.2.2.2.length = b.2.2.1.length ∧
      ∀ r : Fin 4, (blkSp b).getD r.val 0 = (spf b r).val := by
  intro b hb
  refine ⟨List.all_eq_true.1 hrows b hb, ?_⟩
  unfold blocksQ at hb
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hb
  refine ⟨blk_vecs_length k, fun r => ?_⟩
  rw [blkSp_toBlockD, spf_toBlockD _ (fun r => (blk_spins_le k r).1)]

theorem sector_identity (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true)
    (p : Fin 4 → Spin) (hn : 0 < nn (pcode p)) (A B : ℕ) (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    2 * DataStr.certDen * ∑ ti ∈ range rhsTermsQ.size,
        (rhsTermsQ.getD ti default).1 * bilN p (rhsKron p (rhsTermsQ.getD ti default)) A B =
      ∑ σ : Equiv.Perm (Fin 4), bilPl p σ (Gm p σ) A B := by
  obtain ⟨hT, hU, hS, hP, hrows, hq, hfin⟩ := checkAll_parts hall
  obtain ⟨Dn, hDn, hdvd, hD⟩ := checkFinal_spec rhsTermsQ _ DataStr.certDen hfin hP p hn A B hA hB
  rw [← rhsCoords_apply rhsTermsQ p A B hA hB]
  have hpii : ∀ pii : Fin 24, (Dn / (pden (pcode p) pii.val * pden (pcode p) pii.val)) *
      (∑ A' ∈ range (nn (pcode p)), ∑ B' ∈ range (nn (pcode p)),
        pSW (pcode p) pii.val A A' *
          gt ((qtotAll (runAll blocksQ)).1.getD (pcode (fun r => p (sg pii r))) #[]) (A' * nn (pcode p) + B') *
          pSV (pcode p) pii.val B B') = Dn * bilPl p (sg pii) (Gm p (sg pii)) A B := by
    intro pii
    obtain ⟨hnn, hd0, -⟩ := checkPlacements_spec hP p pii hn
    have hpt := place_transfer hP p pii hn (Gm p (sg pii)) A B hA hB
    have hin : ∀ A' ∈ range (nn (pcode p)), ∀ B' ∈ range (nn (pcode p)),
        gt ((qtotAll (runAll blocksQ)).1.getD (pcode (fun r => p (sg pii r))) #[]) (A' * nn (pcode p) + B') =
          bilN (fun r => p (sg pii r)) (Gm p (sg pii)) A' B' := by
      intro A' hA' B' hB'
      have hA'' := Finset.mem_range.1 hA'
      have hB'' := Finset.mem_range.1 hB'
      rw [← hnn] at hA'' hB''
      have := Qtot_sem blocksQ spf hT hU hS (hbs_blocksQ hrows) hq (fun r => p (sg pii r))
        (by rw [hnn]; exact hn) A' B' hA'' hB''
      rw [hnn] at this
      rw [this, Qsem_eq_bilN]
    have hsum : (∑ A' ∈ range (nn (pcode p)), ∑ B' ∈ range (nn (pcode p)),
        pSW (pcode p) pii.val A A' *
          gt ((qtotAll (runAll blocksQ)).1.getD (pcode (fun r => p (sg pii r))) #[]) (A' * nn (pcode p) + B') *
          pSV (pcode p) pii.val B B') =
        pden (pcode p) pii.val ^ 2 * bilPl p (sg pii) (Gm p (sg pii)) A B := by
      rw [hpt]
      refine Finset.sum_congr rfl fun A' hA' => Finset.sum_congr rfl fun B' hB' => ?_
      rw [hin A' hA' B' hB']
      ring
    rw [hsum, ← mul_assoc, pow_two, Int.ediv_mul_cancel (hdvd pii)]
  have hfin2 : Dn * (2 * DataStr.certDen * gt (rhsCoords rhsTermsQ (pcode p)) (A * nn (pcode p) + B)) =
      Dn * ∑ σ : Equiv.Perm (Fin 4), bilPl p σ (Gm p σ) A B := by
    rw [sum_perm4 (fun σ => bilPl p σ (Gm p σ) A B), Finset.mul_sum]
    rw [← Finset.sum_congr rfl fun pii _ => hpii pii]
    rw [← hD]
    ring
  exact mul_left_cancel₀ hDn hfin2

/-!
## `hcheck`: the contraction `Wᵀ K̂ V = 0` in every sector
-/

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

/-!
## The bilinear form of `Kfam` vanishes
-/

theorem checkAll_all (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true) :
    checkChars () = true ∧ checkSlots () = true ∧ checkInv () = true ∧ checkPsi () = true ∧
    checkInvariant () = true ∧ checkPivots true = true ∧ checkPivots false = true := by
  unfold checkAll at hall
  simp only [Bool.and_eq_true] at hall
  exact ⟨hall.1.1.1.1.1.1.1.1.1.1.1.1, hall.1.1.1.1.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.1.1.1.1.2,
    hall.1.1.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.1.2, hall.1.1.1.1.1.1.2⟩

/-- the bilinear form of `Kfam` vanishes on all `u^{⊗6}, v^{⊗6}` -/
theorem kfam_bilinear (hall : checkAll blocksQ rhsTermsQ DataStr.certDen () = true) (z' z : Site → ℂ) :
    copyPower z' 6 ⬝ᵥ (((Kfam (fun k : Fin 14 => QVCert.blk k) (fun k => (QVCert.blk k).weights.length)
      (fun k i => (QVCert.blk k).q i) QVCert.certD).map (Int.castRingHom ℂ)) *ᵥ copyPower z 6) = 0 := by
  obtain ⟨hChars, hSlots, hInv, hPsi, hInvt, hPivV, hPivW⟩ := checkAll_all hall
  have key := quad_eq_zero_of_int_certificate (𝕜 := ℂ) (σ := Fin 2) (n := 6) (Q := Fin 4) (J := Spin)
    dimF (mult := multF) (fun j => by unfold dimF; omega) Cmat CinvMat DataStr.cDen cDen_ne
    (hCi_of_check hInv) (hiC_of_check hInv) gens wF hw_of rho0 (hrho0_of_check hSlots)
    Xk Xhk (hXk hSlots hPsi) nnF Vmat Wmat (fun p i => hV_of_check hInvt p i) (fun p i => hW_of_check hInvt p i)
    (fun p => Classical.choose (hdetV_of_check hPivV p)) (fun p => Classical.choose (hdetW_of_check hPivW p))
    (fun p => Classical.choose_spec (hdetV_of_check hPivV p))
    (fun p => Classical.choose_spec (hdetW_of_check hPivW p))
    (fun p => hchar_of_check hChars p) (fun p => hcheck_of_check hall p) z' z
  rw [Xsum] at key
  exact key

end QVCheck
