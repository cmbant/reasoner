import FormalResearch.FourQubitEntropy.QVCheck.Pair3

/-!
# One covariant term in one sector: `Z · Bil(Y_t) = Σ_{u,u'} Ω Ξ Ctil` (K4 for a term)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- the bilinear form of the invariant bases -/
def bil (p : Fin 4 → Spin) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : Fin (nnF p)) : ℤ :=
  ∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))), Wmat p x A * M x y * Vmat p y B

theorem bil_add (p : Fin 4 → Spin) (M N : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : Fin (nnF p)) :
    bil p (M + N) A B = bil p M A B + bil p N A B := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.add_apply]; ring

theorem bil_smul (p : Fin 4 → Spin) (c : ℤ) (M : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : Fin (nnF p)) :
    bil p (c • M) A B = c * bil p M A B := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

theorem bil_zero (p : Fin 4 → Spin) (A B : Fin (nnF p)) :
    bil p (0 : Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) A B = 0 := by
  unfold bil; simp

theorem bil_list_sum {α : Type*} (p : Fin 4 → Spin) (L : List α)
    (f : α → Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : Fin (nnF p)) :
    bil p (L.map f).sum A B = (L.map fun x => bil p (f x) A B).sum := by
  induction L with
  | nil => simpa using bil_zero p A B
  | cons a t ih => simp only [List.map_cons, List.sum_cons, bil_add, ih]

theorem bil_finset_sum {ι : Type*} (p : Fin 4 → Spin) (s : Finset ι)
    (f : ι → Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ) (A B : Fin (nnF p)) :
    bil p (∑ i ∈ s, f i) A B = ∑ i ∈ s, bil p (f i) A B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bil_zero p A B
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add, ih]

/-- identity-placement operator of one pair of entries -/
def termKron (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (spA : Array ℕ) (e e' : ℕ × ℤ) :
    Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ :=
  (e.2 * e'.2) • kronPi (fun r => psiMat a (sp r) (p r) (muDig spA e.1 r.val) (muDig spA e'.1 r.val))

/-- identity-placement operator of a sparse vector -/
def termY (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (spA : Array ℕ) (v : List (ℕ × ℤ)) :
    Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ :=
  ((pairsList v).map fun pr => termKron p a sp spA pr.1 pr.2).sum


theorem arr_sum {α β : Type*} (L : List α) (f : α → β) (g : β → ℤ) (d0 : β) :
    ∑ pi ∈ range (L.map f).toArray.size, g ((L.map f).toArray.getD pi d0) = (L.map (fun x => g (f x))).sum := by
  have h : ∀ pi, (L.map f).toArray.getD pi d0 = (L.map f).getD pi d0 := by
    intro pi
    simp only [Array.getD, List.getD_eq_getElem?_getD, List.size_toArray, List.length_map, List.getElem_toArray,
      List.getElem?_map]
    by_cases hp : pi < L.length
    · simp [hp]
    · simp [hp, List.getElem?_eq_none (by omega : L.length ≤ pi)]
  simp only [h]
  have hl : (L.map f).toArray.size = (L.map f).length := by simp
  rw [hl, sum_range_getD (L.map f) g d0, List.map_map]
  rfl


theorem list_sum_sum2 {α : Type*} (L : List α) (s s' : Finset ℕ) (f : α → ℕ → ℕ → ℤ) :
    (L.map fun x => ∑ u ∈ s, ∑ u' ∈ s', f x u u').sum = ∑ u ∈ s, ∑ u' ∈ s', (L.map fun x => f x u u').sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]

theorem mkTable_getD (ai sp0 sp1 pj : ℕ) (L : Array Letter) (r : ℕ) (hr : r < L.size) :
    (mkTable ai sp0 sp1 pj L).getD r #[] = tableLetter ai sp0 sp1 pj (L.getD r (0, 0, 0, 0)) := by
  unfold mkTable
  simp [Array.getD, hr]

theorem term_identity (hT : checkT () = true) (hU : checkU () = true) (hS : checkStructure () = true)
    (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (spA : Array ℕ) (hsp : ∀ r : Fin 4, spA.getD r.val 0 = (sp r).val)
    (L01 L23 : Array Letter) (v : List (ℕ × ℤ))
    (hrows : ∀ pr ∈ pairsList v,
      rowOf L01 (letter01 spA pr.1 pr.2) < L01.size ∧ rowOf L23 (letter23 spA pr.1 pr.2) < L23.size ∧
      L01.getD (rowOf L01 (letter01 spA pr.1 pr.2)) (0, 0, 0, 0) = letter01 spA pr.1 pr.2 ∧
      L23.getD (rowOf L23 (letter23 spA pr.1 pr.2)) (0, 0, 0, 0) = letter23 spA pr.1 pr.2)
    (A B : Fin (nnF p)) :
    delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 * bil p (termY p a sp spA v) A B =
    ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
      gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') *
        gt (ctil (pcode p) (mkTable (a - 3) (spA.getD 0 0) (spA.getD 1 0) (pA (pcode p)) L01)
          (mkTable (a - 3) (spA.getD 2 0) (spA.getD 3 0) (pB (pcode p)) L23) (pairsOf L01 L23 spA v))
          (u * nn (pcode p) + u') := by
  have hsz : (uInfo (pcode p)).size = nn (pcode p) :=
    (checkStructure_spec hS (pcode p) (pcode_lt p) A.val A.2).1
  have hAn : A.val < nn (pcode p) := A.2
  have hBn : B.val < nn (pcode p) := B.2
  -- RHS entry of ctil
  have hct : ∀ u u', u < nn (pcode p) → u' < nn (pcode p) →
      gt (ctil (pcode p) (mkTable (a - 3) (spA.getD 0 0) (spA.getD 1 0) (pA (pcode p)) L01)
        (mkTable (a - 3) (spA.getD 2 0) (spA.getD 3 0) (pB (pcode p)) L23) (pairsOf L01 L23 spA v))
        (u * nn (pcode p) + u') =
      ((pairsList v).map fun pr => (pr.1.2 * pr.2.2) *
        ctPair (pcode p)
          ((mkTable (a - 3) (spA.getD 0 0) (spA.getD 1 0) (pA (pcode p)) L01).getD (rowOf L01 (letter01 spA pr.1 pr.2)) #[])
          ((mkTable (a - 3) (spA.getD 2 0) (spA.getD 3 0) (pB (pcode p)) L23).getD (rowOf L23 (letter23 spA pr.1 pr.2)) #[])
          ((uInfo (pcode p)).getD u default) ((uInfo (pcode p)).getD u' default)).sum := by
    intro u u' hu hu'
    unfold ctil
    dsimp only
    rw [hsz]
    have hlt : u * nn (pcode p) + u' < nn (pcode p) * nn (pcode p) := by nlinarith
    rw [gt_tab, if_pos hlt]
    obtain ⟨d1, d2⟩ := div_mod_aux u u' (nn (pcode p)) hu'
    simp only [d1, d2]
    rw [sumTo_eq]
    unfold pairsOf
    rw [arr_sum (pairsList v) (fun pr => (rowOf L01 (letter01 spA pr.1 pr.2), rowOf L23 (letter23 spA pr.1 pr.2), pr.1.2 * pr.2.2))
      (fun r => r.2.2 * ctPair (pcode p)
        ((mkTable (a - 3) (spA.getD 0 0) (spA.getD 1 0) (pA (pcode p)) L01).getD r.1 #[])
        ((mkTable (a - 3) (spA.getD 2 0) (spA.getD 3 0) (pB (pcode p)) L23).getD r.2.1 #[])
        ((uInfo (pcode p)).getD u default) ((uInfo (pcode p)).getD u' default)) (0, 0, 0)]
  have hL : ∀ pr ∈ pairsList v,
      delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 *
        bil p (termKron p a sp spA pr.1 pr.2) A B =
      ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
        gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') *
          ((pr.1.2 * pr.2.2) * ctPair (pcode p)
            ((mkTable (a - 3) (spA.getD 0 0) (spA.getD 1 0) (pA (pcode p)) L01).getD (rowOf L01 (letter01 spA pr.1 pr.2)) #[])
            ((mkTable (a - 3) (spA.getD 2 0) (spA.getD 3 0) (pB (pcode p)) L23).getD (rowOf L23 (letter23 spA pr.1 pr.2)) #[])
            ((uInfo (pcode p)).getD u default) ((uInfo (pcode p)).getD u' default)) := by
    intro pr hpr
    obtain ⟨h1, h2, h3, h4⟩ := hrows pr hpr
    unfold termKron
    rw [bil_smul]
    have hpi := pair_identity hT hU hS p a sp (fun r => muDig spA pr.1.1 r.val) (fun r => muDig spA pr.2.1 r.val) A B
    have hz : ∀ (z c : ℤ), z * (c * bil p (kronPi (fun r => psiMat a (sp r) (p r) (muDig spA pr.1.1 r.val) (muDig spA pr.2.1 r.val))) A B)
        = c * (z * bil p (kronPi (fun r => psiMat a (sp r) (p r) (muDig spA pr.1.1 r.val) (muDig spA pr.2.1 r.val))) A B) := by
      intro z c; ring
    rw [hz]
    have hb : bil p (kronPi (fun r => psiMat a (sp r) (p r) (muDig spA pr.1.1 r.val) (muDig spA pr.2.1 r.val))) A B =
        ∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
          Wmat p x A * kronPi (fun r => psiMat a (sp r) (p r) (muDig spA pr.1.1 r.val) (muDig spA pr.2.1 r.val)) x y * Vmat p y B := rfl
    rw [hb, hpi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [mkTable_getD _ _ _ _ _ _ h1, mkTable_getD _ _ _ _ _ _ h2, h3, h4]
    have e1 : spA.getD 0 0 = (sp 0).val := hsp 0
    have e2 : spA.getD 1 0 = (sp 1).val := hsp 1
    have e3 : spA.getD 2 0 = (sp 2).val := hsp 2
    have e4 : spA.getD 3 0 = (sp 3).val := hsp 3
    rw [e1, e2, e3, e4]
    unfold letter01 letter23
    have z0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    have z1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have z2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have z3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [z0, z1, z2, z3]
    ring
  unfold termY
  rw [bil_list_sum]
  calc delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 *
        ((pairsList v).map fun pr => bil p (termKron p a sp spA pr.1 pr.2) A B).sum
      = ((pairsList v).map fun pr => delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 *
          bil p (termKron p a sp spA pr.1 pr.2) A B).sum := (List.sum_map_mul_left _ _ _).symm
    _ = ((pairsList v).map fun pr => ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
        gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') *
          ((pr.1.2 * pr.2.2) * ctPair (pcode p)
            ((mkTable (a - 3) (spA.getD 0 0) (spA.getD 1 0) (pA (pcode p)) L01).getD (rowOf L01 (letter01 spA pr.1 pr.2)) #[])
            ((mkTable (a - 3) (spA.getD 2 0) (spA.getD 3 0) (pB (pcode p)) L23).getD (rowOf L23 (letter23 spA pr.1 pr.2)) #[])
            ((uInfo (pcode p)).getD u default) ((uInfo (pcode p)).getD u' default))).sum :=
        congrArg List.sum (List.map_congr_left hL)
    _ = _ := by
      rw [list_sum_sum2]
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
      rw [hct u u' (Finset.mem_range.1 hu) (Finset.mem_range.1 hu'), ← List.sum_map_mul_left]

end QVCheck
