import FormalResearch.FourQubitEntropy.QVCheck.Assemble

/-!
# The sector identity from the checker
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock FormalResearch.FourQubitEntropy.QVFrame

namespace QVCheck

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

end QVCheck
