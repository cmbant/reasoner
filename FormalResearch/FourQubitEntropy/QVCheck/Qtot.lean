import FormalResearch.FourQubitEntropy.QVCheck.RunBlock

/-!
# From the accumulated `Ctil` to `Qtot` (quotient by `Z`)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem gt_replicate_zero (n e : ℕ) : gt (Array.replicate n (0 : Int)) e = 0 := by
  unfold gt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

theorem gtt_accZero (c e : ℕ) : gtt accZero c e = 0 := by
  unfold gtt accZero
  by_cases hc : c < 256
  · have : ((List.range 256).toArray.map fun code => Array.replicate (nn code * nn code) (0 : Int)).getD c #[] =
        Array.replicate (nn c * nn c) 0 := by
      simp [Array.getD, hc]
    rw [this, gt_replicate_zero]
  · have : ((List.range 256).toArray.map fun code => Array.replicate (nn code * nn code) (0 : Int)).getD c #[] = #[] := by
      simp [Array.getD, hc]
    rw [this]; unfold gt; simp

theorem wellSized_runBlock (b : BlockD) (acc : Array (Array Int)) (h : WellSized acc) : WellSized (runBlock b acc) := by
  unfold runBlock
  dsimp only
  exact wellSized_foldl _ (fun pjA acc => blockStep2 b (blockPairs b) ((List.range 16).toArray.map (blockTab23 b)) pjA acc)
    (fun pjA acc hh => wellSized_blockStep2 b _ _ pjA acc hh) acc h

/-- the semantic content of the accumulators: `Σ_{b, ti} w · Ctil` -/
def ctilSum (bs : List BlockD) (c e : ℕ) : ℤ :=
  (bs.map fun b => ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
    gt (ctil c (blockTab01 b (pA c)) (blockTab23 b (pB c)) ((blockPairs b).getD ti #[])) e).sum

theorem runAll_spec (bs : List BlockD) (c e : ℕ) (hc : c < 256) (he : e < nn c * nn c) (hn : 0 < nn c) :
    gtt (runAll bs) c e = ctilSum bs c e := by
  unfold runAll ctilSum
  have hadd := foldl_additive c e bs (fun b acc => runBlock b acc)
    (fun b => ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
      gt (ctil c (blockTab01 b (pA c)) (blockTab23 b (pB c)) ((blockPairs b).getD ti #[])) e)
    (fun b acc hacc => by rw [runBlock_spec b acc hacc c e hc he, if_pos hn])
    (fun b acc h => wellSized_runBlock b acc h) accZero accZero_wellSized
  rw [hadd, gtt_accZero]; simp


/-- `Z` of a sector -/
def Zc (code : ℕ) : ℤ := delta (pA code) ^ 2 * delta (pB code) ^ 2 * DataStr.lc ^ 2

theorem qtotOf_spec (acc : Array (Array Int)) (code : ℕ) (hok : (qtotOf acc code).2 = true) (A B : ℕ)
    (hA : A < nn code) (hB : B < nn code) :
    Zc code ≠ 0 ∧ Zc code * gt (qtotOf acc code).1 (A * nn code + B) =
      ∑ u ∈ range (nn code), ∑ u' ∈ range (nn code),
        gt omArr (nnOff code + A * nn code + u) * gt xiArr (nnOff code + B * nn code + u') *
          gtt acc code (u * nn code + u') := by
  unfold qtotOf at hok ⊢
  dsimp only at hok ⊢
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨hZ, hall⟩ := hok
  refine ⟨hZ, ?_⟩
  rw [show Zc code = delta (pA code) ^ 2 * delta (pB code) ^ 2 * DataStr.lc ^ 2 from rfl]
  have hlt : A * nn code + B < nn code * nn code := by nlinarith
  have h1 := (allTo_iff _ _).1 hall (A * nn code + B) hlt
  simp only [beq_iff_eq] at h1
  rw [h1]
  -- unfold Qs
  rw [gt_tab, if_pos hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux A B (nn code) hB
  simp only [d1, d2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' hu' => ?_
  have hu' := Finset.mem_range.1 hu'
  have hlt2 : A * nn code + u' < nn code * nn code := by nlinarith
  rw [gt_tab, if_pos hlt2, sumTo_eq]
  obtain ⟨e1, e2⟩ := div_mod_aux A u' (nn code) hu'
  simp only [e1, e2]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu1 := Finset.mem_range.1 hu
  have hlt3 : A * nn code + u < nn code * nn code := by nlinarith
  have hlt4 : B * nn code + u' < nn code * nn code := by nlinarith
  unfold slice
  rw [gt_tab, if_pos hlt3, gt_tab, if_pos hlt4]
  unfold gtt
  have e3 : nnOff code + (A * nn code + u) = nnOff code + A * nn code + u := by ring
  have e4 : nnOff code + (B * nn code + u') = nnOff code + B * nn code + u' := by ring
  rw [e3, e4]; ring


theorem getD_push {α : Type*} (arr : Array α) (x d : α) (i : ℕ) :
    (arr.push x).getD i d = if i < arr.size then arr.getD i d else if i = arr.size then x else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : i < arr.size
  · have h' : i ≠ arr.size := by omega
    simp [h, h', Array.getElem?_eq_getElem h]
  · by_cases h2 : i = arr.size
    · simp [h2]
    · simp [h, h2, Array.getElem?_eq_none (by omega : arr.size ≤ i)]

theorem qtotFold (acc : Array (Array Int)) (N : ℕ) :
    ((List.range N).foldl (qtotStep acc) (#[], true)).1.size = N ∧
    (∀ code < N, ((List.range N).foldl (qtotStep acc) (#[], true)).1.getD code #[] =
      if nn code == 0 then #[] else (qtotOf acc code).1) ∧
    (((List.range N).foldl (qtotStep acc) (#[], true)).2 = true → ∀ code < N, nn code ≠ 0 → (qtotOf acc code).2 = true) := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set r := (List.range N).foldl (qtotStep acc) (#[], true) with hr
    unfold qtotStep
    by_cases hz : nn N == 0
    · rw [if_pos hz]
      refine ⟨by simp [h1], fun code hcode => ?_, fun hb code hcode hnz => ?_⟩
      · rw [getD_push]
        by_cases hcN : code < N
        · rw [if_pos (by omega), h2 code hcN]
        · have : code = N := by omega
          subst this
          rw [if_neg (by omega), if_pos (by omega), if_pos hz]
      · by_cases hcN : code < N
        · exact h3 hb code hcN hnz
        · have : code = N := by omega
          subst this
          exact absurd (by simpa using hz) hnz
    · rw [if_neg hz]
      refine ⟨by simp [h1], fun code hcode => ?_, fun hb code hcode hnz => ?_⟩
      · rw [getD_push]
        by_cases hcN : code < N
        · rw [if_pos (by omega), h2 code hcN]
        · have : code = N := by omega
          subst this
          rw [if_neg (by omega), if_pos (by omega), if_neg hz]
      · have hb' : r.2 = true ∧ (qtotOf acc N).2 = true := by simpa using hb
        by_cases hcN : code < N
        · exact h3 hb'.1 code hcN hnz
        · have : code = N := by omega
          subst this
          exact hb'.2

theorem qtotAll_spec (acc : Array (Array Int)) (hok : (qtotAll acc).2 = true) (code : ℕ) (hc : code < 256)
    (hn : 0 < nn code) :
    (qtotAll acc).1.getD code #[] = (qtotOf acc code).1 ∧ (qtotOf acc code).2 = true := by
  obtain ⟨_, h2, h3⟩ := qtotFold acc 256
  have hnz : nn code ≠ 0 := by omega
  refine ⟨?_, h3 hok code hc hnz⟩
  unfold qtotAll
  rw [h2 code hc, if_neg (by simpa using hnz)]

end QVCheck
