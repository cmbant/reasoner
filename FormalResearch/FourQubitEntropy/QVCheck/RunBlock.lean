import FormalResearch.FourQubitEntropy.QVCheck.Term

/-!
# Semantics of the accumulation loops of `runBlock` / `runAll`
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- entry `e` of accumulator `c` -/
def gtt (acc : Array (Array Int)) (c e : ℕ) : ℤ := gt (acc.getD c #[]) e

/-- all accumulators have the sector sizes -/
def WellSized (acc : Array (Array Int)) : Prop := ∀ c, (acc.getD c #[]).size = nn c * nn c

theorem gt_oob (A : Array Int) (e : ℕ) (h : A.size ≤ e) : gt A e = 0 := by
  unfold gt; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]; rfl

theorem accAdd_getD (acc : Array (Array Int)) (code : ℕ) (q : ℤ) (x : Array Int) (c : ℕ) :
    (accAdd acc code q x).getD c #[] =
      if c = code then tab (acc.getD code #[]).size (fun i => gt (acc.getD code #[]) i + q * gt x i) else acc.getD c #[] := by
  unfold accAdd
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hc : c = code
  · subst hc
    simp only [if_true]
    cases h : acc[c]? with
    | none => simp [tab, tabAux, Array.getD_eq_getD_getElem?, h]
    | some a => simp [h]
  · simp [hc, Ne.symm hc]

theorem accAdd_gtt (acc : Array (Array Int)) (code : ℕ) (q : ℤ) (x : Array Int) (c e : ℕ) :
    gtt (accAdd acc code q x) c e =
      gtt acc c e + (if c = code ∧ e < (acc.getD code #[]).size then q * gt x e else 0) := by
  unfold gtt
  rw [accAdd_getD]
  by_cases hc : c = code
  · subst hc
    rw [if_pos rfl, gt_tab]
    by_cases he : e < (acc.getD c #[]).size
    · rw [if_pos he, if_pos ⟨rfl, he⟩]
    · rw [if_neg he, if_neg (fun h => he h.2)]
      rw [gt_oob _ _ (by omega)]; simp
  · rw [if_neg hc, if_neg (fun h => hc h.1)]; simp

theorem accAdd_size (acc : Array (Array Int)) (code : ℕ) (q : ℤ) (x : Array Int) (c : ℕ) :
    ((accAdd acc code q x).getD c #[]).size = (acc.getD c #[]).size := by
  rw [accAdd_getD]
  by_cases hc : c = code
  · subst hc; rw [if_pos rfl, tab_size]
  · rw [if_neg hc]


theorem list_range_sum (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem foldl_additive {κ : Type*} (c e : ℕ) (L : List κ) (f : κ → Array (Array Int) → Array (Array Int)) (δ : κ → ℤ)
    (hf : ∀ k acc, WellSized acc → gtt (f k acc) c e = gtt acc c e + δ k)
    (hs : ∀ k acc, WellSized acc → WellSized (f k acc)) :
    ∀ acc, WellSized acc → gtt (L.foldl (fun acc k => f k acc) acc) c e = gtt acc c e + (L.map δ).sum := by
  induction L with
  | nil => intro acc _; simp
  | cons a t ih =>
    intro acc hacc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (f a acc) (hs a acc hacc), hf a acc hacc]; ring

theorem wellSized_accAdd (acc : Array (Array Int)) (h : WellSized acc) (code : ℕ) (q : ℤ) (x : Array Int) :
    WellSized (accAdd acc code q x) := fun c => by rw [accAdd_size]; exact h c

theorem nn_ge (c : ℕ) (hc : 256 ≤ c) : nn c = 0 := by
  unfold nn nnArr
  simp [Array.getD, Nat.not_lt.2 hc]

theorem accZero_wellSized : WellSized accZero := by
  intro c
  unfold accZero
  by_cases hc : c < 256
  · simp [Array.getD, hc]
  · have h0 := nn_ge c (by omega)
    rw [h0]
    simp [Array.getD, hc]


theorem pA_lt16 (c : ℕ) : pA c < 16 := by
  unfold pA pairIdx spinDigit
  have h1 : c / 4 ^ (3 - 0) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h2 : c / 4 ^ (3 - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  omega

theorem pB_lt16 (c : ℕ) : pB c < 16 := by
  unfold pB pairIdx spinDigit
  have h1 : c / 4 ^ (3 - 2) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h2 : c / 4 ^ (3 - 3) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  omega

theorem blockStep1_spec (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : ℕ) (T01 : Array (Array Int)) (code : ℕ) (acc : Array (Array Int)) (hacc : WellSized acc) (c e : ℕ)
    (he : e < nn c * nn c) :
    gtt (blockStep1 b pairs tabs23 pjA T01 code acc) c e = gtt acc c e +
      (if 0 < nn code ∧ pA code = pjA ∧ c = code then
        ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
          gt (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[])) e else 0) := by
  unfold blockStep1
  by_cases hcond : nn code > 0 ∧ pA code = pjA
  · have hb : (nn code > 0 && pA code == pjA) = true := by simp [hcond.1, hcond.2]
    rw [if_pos hb]
    have hadd := foldl_additive c e (List.range b.2.2.1.length)
      (fun ti acc => accAdd acc code (b.2.2.1.getD ti 0) (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[])))
      (fun ti => if c = code ∧ e < nn code * nn code then
        b.2.2.1.getD ti 0 * gt (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[])) e else 0)
      (by
        intro ti acc hacc
        rw [accAdd_gtt, hacc code])
      (fun ti acc hacc => wellSized_accAdd acc hacc _ _ _) acc hacc
    rw [hadd]
    by_cases hc : c = code
    · subst hc
      rw [if_pos ⟨hcond.1, hcond.2, rfl⟩, list_range_sum]
      congr 1
      refine Finset.sum_congr rfl fun ti _ => ?_
      rw [if_pos ⟨rfl, he⟩]
    · rw [if_neg (fun h => hc h.2.2)]
      have : ((List.range b.2.2.1.length).map fun ti => if c = code ∧ e < nn code * nn code then
          b.2.2.1.getD ti 0 * gt (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[])) e else 0).sum = 0 := by
        rw [list_range_sum]
        exact Finset.sum_eq_zero fun ti _ => by rw [if_neg (fun h => hc h.1)]
      rw [this]
  · have hb : ¬ (nn code > 0 && pA code == pjA) = true := by
      intro h; apply hcond; simpa using h
    rw [if_neg hb, if_neg (fun h => hcond ⟨h.1, h.2.1⟩)]; simp

theorem wellSized_foldl {κ : Type*} (L : List κ) (f : κ → Array (Array Int) → Array (Array Int))
    (hs : ∀ k acc, WellSized acc → WellSized (f k acc)) :
    ∀ acc, WellSized acc → WellSized (L.foldl (fun acc k => f k acc) acc) := by
  induction L with
  | nil => intro acc h; exact h
  | cons a t ih => intro acc h; exact ih (f a acc) (hs a acc h)

theorem wellSized_blockStep1 (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : ℕ) (T01 : Array (Array Int)) (code : ℕ) (acc : Array (Array Int)) (h : WellSized acc) :
    WellSized (blockStep1 b pairs tabs23 pjA T01 code acc) := by
  unfold blockStep1
  split
  · exact wellSized_foldl _ (fun ti acc => accAdd acc code (b.2.2.1.getD ti 0)
      (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[])))
      (fun ti acc hh => wellSized_accAdd acc hh _ _ _) acc h
  · exact h

theorem wellSized_blockStep2 (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : ℕ) (acc : Array (Array Int)) (h : WellSized acc) : WellSized (blockStep2 b pairs tabs23 pjA acc) := by
  unfold blockStep2
  dsimp only
  exact wellSized_foldl _ (fun code acc => blockStep1 b pairs tabs23 pjA (blockTab01 b pjA) code acc)
    (fun code acc hh => wellSized_blockStep1 b pairs tabs23 pjA _ code acc hh) acc h

theorem blockStep2_spec (b : BlockD) (pairs : Array (Array (Nat × Nat × Int))) (tabs23 : Array (Array (Array Int)))
    (pjA : ℕ) (acc : Array (Array Int)) (hacc : WellSized acc) (c e : ℕ) (hc : c < 256) (he : e < nn c * nn c) :
    gtt (blockStep2 b pairs tabs23 pjA acc) c e = gtt acc c e +
      (if 0 < nn c ∧ pA c = pjA then
        ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
          gt (ctil c (blockTab01 b pjA) (tabs23.getD (pB c) #[]) (pairs.getD ti #[])) e else 0) := by
  unfold blockStep2
  dsimp only
  have hadd := foldl_additive c e (List.range 256) (fun code acc => blockStep1 b pairs tabs23 pjA (blockTab01 b pjA) code acc)
    (fun code => if 0 < nn code ∧ pA code = pjA ∧ c = code then
        ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
          gt (ctil code (blockTab01 b pjA) (tabs23.getD (pB code) #[]) (pairs.getD ti #[])) e else 0)
    (fun code acc hacc => blockStep1_spec b pairs tabs23 pjA _ code acc hacc c e he)
    (fun code acc h => wellSized_blockStep1 b pairs tabs23 pjA _ code acc h) acc hacc
  rw [hadd, list_range_sum]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases hcd : 0 < nn c ∧ pA c = pjA
    · rw [if_pos ⟨hcd.1, hcd.2, rfl⟩, if_pos hcd]
    · rw [if_neg (fun h => hcd ⟨h.1, h.2.1⟩), if_neg hcd]
  · intro code _ hne
    rw [if_neg (fun h => hne h.2.2.symm)]
  · intro h; exact absurd (Finset.mem_range.2 hc) h

theorem runBlock_spec (b : BlockD) (acc : Array (Array Int)) (hacc : WellSized acc) (c e : ℕ) (hc : c < 256)
    (he : e < nn c * nn c) :
    gtt (runBlock b acc) c e = gtt acc c e +
      (if 0 < nn c then ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
        gt (ctil c (blockTab01 b (pA c)) (blockTab23 b (pB c)) ((blockPairs b).getD ti #[])) e else 0) := by
  unfold runBlock
  dsimp only
  have hP23 : ((List.range 16).toArray.map (blockTab23 b)).getD (pB c) #[] = blockTab23 b (pB c) := by
    have := pB_lt16 c
    simp [Array.getD, this]
  have hadd := foldl_additive c e (List.range 16) (fun pjA acc => blockStep2 b (blockPairs b)
      ((List.range 16).toArray.map (blockTab23 b)) pjA acc)
    (fun pjA => if 0 < nn c ∧ pA c = pjA then
        ∑ ti ∈ range b.2.2.1.length, b.2.2.1.getD ti 0 *
          gt (ctil c (blockTab01 b pjA) (((List.range 16).toArray.map (blockTab23 b)).getD (pB c) #[])
            ((blockPairs b).getD ti #[])) e else 0)
    (fun pjA acc hacc => blockStep2_spec b _ _ pjA acc hacc c e hc he)
    (fun pjA acc h => wellSized_blockStep2 b _ _ pjA acc h) acc hacc
  rw [hadd, list_range_sum, hP23]
  congr 1
  rw [Finset.sum_eq_single (pA c)]
  · by_cases hcd : 0 < nn c
    · rw [if_pos ⟨hcd, rfl⟩, if_pos hcd]
    · rw [if_neg (fun h => hcd h.1), if_neg hcd]
  · intro pj _ hne
    rw [if_neg (fun h => hne h.2.symm)]
  · intro h; exact absurd (Finset.mem_range.2 (pA_lt16 c)) h

end QVCheck
