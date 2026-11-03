module

public import FormalResearch.FourQubitEntropy.QVCheck.Coupled

/-!
# One covariant term, the accumulation and `Qtot` (K4)

`term_identity`: `Z · Bil(Y_t) = Σ_{u,u'} Ω Ξ Ctil_t` for one covariant term `t` in a sector; `runBlock_spec`,
`runAll_spec`: the accumulation loops of `runBlock`/`runAll` sum the terms of all blocks; `qtotAll_spec`: the quotient
by `Z` is exact and gives `Qtot`.
-/

@[expose] public section


open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock
open scoped Matrix

namespace QVCheck

/-!
## One covariant term in one sector: `Z · Bil(Y_t) = Σ_{u,u'} Ω Ξ Ctil` (K4 for a term)
-/

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
    simp only [Array.getD, List.getD_eq_getElem?_getD, List.size_toArray, List.length_map,
      List.getElem?_map]
    by_cases hp : pi < L.length
    · simp [hp]
    · simp [hp]
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
    rw [gt_tab, ite_eq_left hlt]
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

/-!
## The accumulation loops `runBlock` / `runAll`
-/

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
    simp only [ite_true]
    cases h : acc[c]? with
    | none => simp [tab, tabAux]
    | some a => simp
  · simp [hc, Ne.symm hc]

theorem accAdd_gtt (acc : Array (Array Int)) (code : ℕ) (q : ℤ) (x : Array Int) (c e : ℕ) :
    gtt (accAdd acc code q x) c e =
      gtt acc c e + (if c = code ∧ e < (acc.getD code #[]).size then q * gt x e else 0) := by
  unfold gtt
  rw [accAdd_getD]
  by_cases hc : c = code
  · subst hc
    rw [ite_eq_left rfl, gt_tab]
    by_cases he : e < (acc.getD c #[]).size
    · rw [ite_eq_left he, ite_eq_left ⟨rfl, he⟩]
    · rw [ite_eq_right he, ite_eq_right (fun h => he h.2)]
      rw [gt_oob _ _ (by omega)]; simp
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.1)]; simp

theorem accAdd_size (acc : Array (Array Int)) (code : ℕ) (q : ℤ) (x : Array Int) (c : ℕ) :
    ((accAdd acc code q x).getD c #[]).size = (acc.getD c #[]).size := by
  rw [accAdd_getD]
  by_cases hc : c = code
  · subst hc; rw [ite_eq_left rfl, tab_size]
  · rw [ite_eq_right hc]


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
    rw [ite_eq_left hb]
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
      rw [ite_eq_left ⟨hcond.1, hcond.2, rfl⟩, list_range_sum]
      congr 1
      refine Finset.sum_congr rfl fun ti _ => ?_
      rw [ite_eq_left ⟨rfl, he⟩]
    · rw [ite_eq_right (fun h => hc h.2.2)]
      have : ((List.range b.2.2.1.length).map fun ti => if c = code ∧ e < nn code * nn code then
          b.2.2.1.getD ti 0 * gt (ctil code T01 (tabs23.getD (pB code) #[]) (pairs.getD ti #[])) e else 0).sum = 0 := by
        rw [list_range_sum]
        exact Finset.sum_eq_zero fun ti _ => by rw [ite_eq_right (fun h => hc h.1)]
      rw [this]
  · have hb : ¬ (nn code > 0 && pA code == pjA) = true := by
      intro h; apply hcond; simpa using h
    rw [ite_eq_right hb, ite_eq_right (fun h => hcond ⟨h.1, h.2.1⟩)]; simp

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
    · rw [ite_eq_left ⟨hcd.1, hcd.2, rfl⟩, ite_eq_left hcd]
    · rw [ite_eq_right (fun h => hcd ⟨h.1, h.2.1⟩), ite_eq_right hcd]
  · intro code _ hne
    rw [ite_eq_right (fun h => hne h.2.2.symm)]
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
    · rw [ite_eq_left ⟨hcd, rfl⟩, ite_eq_left hcd]
    · rw [ite_eq_right (fun h => hcd h.1), ite_eq_right hcd]
  · intro pj _ hne
    rw [ite_eq_right (fun h => hne h.2.symm)]
  · intro h; exact absurd (Finset.mem_range.2 (pA_lt16 c)) h

/-!
## From the accumulated `Ctil` to `Qtot` (quotient by `Z`)
-/

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
    (fun b acc hacc => by rw [runBlock_spec b acc hacc c e hc he, ite_eq_left hn])
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
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux A B (nn code) hB
  simp only [d1, d2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u' hu' => ?_
  have hu' := Finset.mem_range.1 hu'
  have hlt2 : A * nn code + u' < nn code * nn code := by nlinarith
  rw [gt_tab, ite_eq_left hlt2, sumTo_eq]
  obtain ⟨e1, e2⟩ := div_mod_aux A u' (nn code) hu'
  simp only [e1, e2]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu1 := Finset.mem_range.1 hu
  have hlt3 : A * nn code + u < nn code * nn code := by nlinarith
  have hlt4 : B * nn code + u' < nn code * nn code := by nlinarith
  unfold slice
  rw [gt_tab, ite_eq_left hlt3, gt_tab, ite_eq_left hlt4]
  unfold gtt
  have e3 : nnOff code + (A * nn code + u) = nnOff code + A * nn code + u := by ring
  have e4 : nnOff code + (B * nn code + u') = nnOff code + B * nn code + u' := by ring
  rw [e3, e4]; ring


theorem getD_push {α : Type*} (arr : Array α) (x d : α) (i : ℕ) :
    (arr.push x).getD i d = if i < arr.size then arr.getD i d else if i = arr.size then x else d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : i < arr.size
  · have h' : i ≠ arr.size := by omega
    simp [h, h']
  · by_cases h2 : i = arr.size
    · simp [h2]
    · simp [h, h2]

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
    · rw [ite_eq_left hz]
      refine ⟨by simp [h1], fun code hcode => ?_, fun hb code hcode hnz => ?_⟩
      · rw [getD_push]
        by_cases hcN : code < N
        · rw [ite_eq_left (by omega), h2 code hcN]
        · have : code = N := by omega
          subst this
          rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hz]
      · by_cases hcN : code < N
        · exact h3 hb code hcN hnz
        · have : code = N := by omega
          subst this
          exact absurd (by simpa using hz) hnz
    · rw [ite_eq_right hz]
      refine ⟨by simp [h1], fun code hcode => ?_, fun hb code hcode hnz => ?_⟩
      · rw [getD_push]
        by_cases hcN : code < N
        · rw [ite_eq_left (by omega), h2 code hcN]
        · have : code = N := by omega
          subst this
          rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right hz]
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
  rw [h2 code hc, ite_eq_right (by simpa using hnz)]

end QVCheck
