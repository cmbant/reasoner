import FormalResearch.FourQubitEntropy.QVCheck.Rhs
import FormalResearch.FourQubitEntropy.QVCheck.RunBlock
import FormalResearch.FourQubitEntropy.QVCheck.Qtot

/-!
# `Qtot` as the semantic sum over the covariants (K4 + quotient)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- the semantic `Σ_t q_t · Bil(Y_t)` over the blocks -/
def Qsem (bs : List BlockD) (spf : BlockD → Fin 4 → Spin) (p : Fin 4 → Spin) (A B : ℕ) : ℤ :=
  (bs.map fun b => ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
    bilN p (termY p b.1 (spf b) (blkSp b) (b.2.2.2.getD ti [])) A B).sum

theorem list_sum_sum2' {α : Type*} (L : List α) (s s' : Finset ℕ) (f : α → ℕ → ℕ → ℤ) :
    ∑ u ∈ s, ∑ u' ∈ s', (L.map fun x => f x u u').sum = (L.map fun x => ∑ u ∈ s, ∑ u' ∈ s', f x u u').sum :=
  (list_sum_sum2 L s s' f).symm

theorem mem_allPairs (b : BlockD) (ti : ℕ) (hti : ti < b.2.2.2.length) (pr : (ℕ × ℤ) × (ℕ × ℤ))
    (h : pr ∈ pairsList (b.2.2.2.getD ti [])) : pr ∈ allPairs b := by
  unfold allPairs
  rw [List.mem_flatMap]
  refine ⟨b.2.2.2.getD ti [], ?_, h⟩
  rw [List.getD_eq_getElem _ _ hti]
  exact List.getElem_mem hti

theorem block_term_sum (b : BlockD) (spf : BlockD → Fin 4 → Spin)
    (hT : checkT () = true) (hU : checkU () = true) (hS : checkStructure () = true)
    (hb : rowsOk b = true ∧ b.2.2.2.length = b.2.2.1.length ∧ ∀ r : Fin 4, (blkSp b).getD r.val 0 = (spf b r).val)
    (p : Fin 4 → Spin) (A B : ℕ) (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    Zc (pcode p) * (∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
        bilN p (termY p b.1 (spf b) (blkSp b) (b.2.2.2.getD ti [])) A B) =
    ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
      gt omArr (nnOff (pcode p) + A * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B * nn (pcode p) + u') *
        ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
          gt (ctil (pcode p) (blockTab01 b (pA (pcode p))) (blockTab23 b (pB (pcode p))) ((blockPairs b).getD ti #[]))
            (u * nn (pcode p) + u') := by
  obtain ⟨hrows, hlen, hsp⟩ := hb
  have hA' : A < nnF p := hA
  have hB' : B < nnF p := hB
  have key : ∀ ti ∈ range b.2.2.1.length,
      Zc (pcode p) * (b.2.2.1.getD ti 0 * bilN p (termY p b.1 (spf b) (blkSp b) (b.2.2.2.getD ti [])) A B) =
      ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
        gt omArr (nnOff (pcode p) + A * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B * nn (pcode p) + u') *
          (b.2.2.1.getD ti 0 *
            gt (ctil (pcode p) (blockTab01 b (pA (pcode p))) (blockTab23 b (pB (pcode p))) ((blockPairs b).getD ti #[]))
              (u * nn (pcode p) + u')) := by
    intro ti hti
    have hti := Finset.mem_range.1 hti
    have hti2 : ti < b.2.2.2.length := by omega
    have hrw : ∀ pr ∈ pairsList (b.2.2.2.getD ti []),
        rowOf (letters01Of b) (letter01 (blkSp b) pr.1 pr.2) < (letters01Of b).size ∧
        rowOf (letters23Of b) (letter23 (blkSp b) pr.1 pr.2) < (letters23Of b).size ∧
        (letters01Of b).getD (rowOf (letters01Of b) (letter01 (blkSp b) pr.1 pr.2)) (0, 0, 0, 0) = letter01 (blkSp b) pr.1 pr.2 ∧
        (letters23Of b).getD (rowOf (letters23Of b) (letter23 (blkSp b) pr.1 pr.2)) (0, 0, 0, 0) = letter23 (blkSp b) pr.1 pr.2 := by
      intro pr hpr
      have hm := mem_allPairs b ti hti2 pr hpr
      have h := List.all_eq_true.1 hrows pr hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
    have hti_id := term_identity hT hU hS p b.1 (spf b) (blkSp b) (fun r => hsp r) (letters01Of b) (letters23Of b)
      (b.2.2.2.getD ti []) hrw ⟨A, hA'⟩ ⟨B, hB'⟩
    have hbp : (blockPairs b).getD ti #[] = pairsOf (letters01Of b) (letters23Of b) (blkSp b) (b.2.2.2.getD ti []) := by
      unfold blockPairs
      simp [Array.getD, hti]
    rw [hbp]
    have hbl : bil p (termY p b.1 (spf b) (blkSp b) (b.2.2.2.getD ti [])) ⟨A, hA'⟩ ⟨B, hB'⟩ =
        bilN p (termY p b.1 (spf b) (blkSp b) (b.2.2.2.getD ti [])) A B := rfl
    rw [hbl] at hti_id
    unfold blockTab01 blockTab23
    rw [show Zc (pcode p) = delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 from rfl,
      mul_left_comm, hti_id, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' _ => ?_
  rw [← Finset.mul_sum]

theorem Qtot_sem_aux (bs : List BlockD) (spf : BlockD → Fin 4 → Spin)
    (hT : checkT () = true) (hU : checkU () = true) (hS : checkStructure () = true)
    (hbs : ∀ b ∈ bs, rowsOk b = true ∧ b.2.2.2.length = b.2.2.1.length ∧ ∀ r : Fin 4, (blkSp b).getD r.val 0 = (spf b r).val)
    (hok : (qtotAll (runAll bs)).2 = true) (p : Fin 4 → Spin) (hn : 0 < nn (pcode p)) (A B : ℕ)
    (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    Zc (pcode p) * gt ((qtotAll (runAll bs)).1.getD (pcode p) #[]) (A * nn (pcode p) + B) = Zc (pcode p) * Qsem bs spf p A B := by
  obtain ⟨hq1, hq2⟩ := qtotAll_spec (runAll bs) hok (pcode p) (pcode_lt p) hn
  obtain ⟨hZ, hQ⟩ := qtotOf_spec (runAll bs) (pcode p) hq2 A B hA hB
  rw [hq1, hQ]
  have hrun : ∀ u u', u < nn (pcode p) → u' < nn (pcode p) →
      gtt (runAll bs) (pcode p) (u * nn (pcode p) + u') = ctilSum bs (pcode p) (u * nn (pcode p) + u') := by
    intro u u' hu hu'
    exact runAll_spec bs _ _ (pcode_lt p) (by nlinarith) hn
  have h1 : ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
        gt omArr (nnOff (pcode p) + A * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B * nn (pcode p) + u') *
          gtt (runAll bs) (pcode p) (u * nn (pcode p) + u') =
      ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
        (bs.map fun b => gt omArr (nnOff (pcode p) + A * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B * nn (pcode p) + u') *
          ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
            gt (ctil (pcode p) (blockTab01 b (pA (pcode p))) (blockTab23 b (pB (pcode p))) ((blockPairs b).getD ti #[]))
              (u * nn (pcode p) + u')).sum := by
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
    rw [hrun u u' (Finset.mem_range.1 hu) (Finset.mem_range.1 hu')]
    unfold ctilSum
    rw [List.sum_map_mul_left]
  rw [h1]
  refine (list_sum_sum2' bs _ _ (fun b u u' =>
    gt omArr (nnOff (pcode p) + A * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B * nn (pcode p) + u') *
      ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
        gt (ctil (pcode p) (blockTab01 b (pA (pcode p))) (blockTab23 b (pB (pcode p))) ((blockPairs b).getD ti #[]))
          (u * nn (pcode p) + u'))).trans ?_
  unfold Qsem
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  exact (block_term_sum b spf hT hU hS (hbs b hb) p A B hA hB).symm

theorem Qtot_sem (bs : List BlockD) (spf : BlockD → Fin 4 → Spin)
    (hT : checkT () = true) (hU : checkU () = true) (hS : checkStructure () = true)
    (hbs : ∀ b ∈ bs, rowsOk b = true ∧ b.2.2.2.length = b.2.2.1.length ∧ ∀ r : Fin 4, (blkSp b).getD r.val 0 = (spf b r).val)
    (hok : (qtotAll (runAll bs)).2 = true) (p : Fin 4 → Spin) (hn : 0 < nn (pcode p)) (A B : ℕ)
    (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    gt ((qtotAll (runAll bs)).1.getD (pcode p) #[]) (A * nn (pcode p) + B) = Qsem bs spf p A B := by
  obtain ⟨hq1, hq2⟩ := qtotAll_spec (runAll bs) hok (pcode p) (pcode_lt p) hn
  obtain ⟨hZ, -⟩ := qtotOf_spec (runAll bs) (pcode p) hq2 A B hA hB
  exact mul_left_cancel₀ hZ (Qtot_sem_aux bs spf hT hU hS hbs hok p hn A B hA hB)

end QVCheck
