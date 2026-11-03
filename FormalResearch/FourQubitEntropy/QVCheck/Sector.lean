module

public import FormalResearch.FourQubitEntropy.QVCheck.Placement
public import FormalResearch.FourQubitEntropy.QVCheck.Terms

/-!
# Right-hand side, `Qtot` and the final comparison (K6, K7)

`rhsCoords_apply`: the coordinates of the right-hand side `K_RHS` in a sector; `Qtot_sem`: `Qtot` is the semantic sum over
the covariants; `checkFinal_spec`: the final comparison `checkFinal` is the sector identity up to the placement
denominators.
-/

@[expose] public section


open Finset FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock
open scoped Matrix

namespace QVCheck

/-!
## The right-hand side coordinates (K6)
-/

theorem flatIx_inj (m : Fin 4 → ℕ) : Function.Injective (flatIx m) := by
  intro x y h
  funext q
  apply Fin.ext
  have h1 := flatIx_digit m x q
  have h2 := flatIx_digit m y q
  rw [h] at h1
  exact h1.symm.trans h2

theorem sum_flat (p : Fin 4 → Spin) (g : ℕ → ℤ) :
    ∑ f ∈ range (sdim (pcode p)), g f = ∑ x : (∀ q, Fin (multF (p q))), g (flatIx (radix p) x) := by
  rw [sdim_pcode]
  symm
  refine Finset.sum_nbij (flatIx (radix p)) (fun x _ => Finset.mem_range.2 (flatIx_lt _ x))
    (fun x _ y _ h => flatIx_inj _ h) (fun f hf => ?_) (fun _ _ => rfl)
  obtain ⟨x, hx⟩ := exists_flatIx (radix p) f (Finset.mem_range.1 hf)
  exact ⟨x, Finset.mem_univ _, hx⟩

theorem kronRep_eq_kron4 (code : ℕ) (ms : Array (Array Int)) (X : Array Int) :
    kronRep code ms X =
      kron4 (ms.getD 0 #[]) (ms.getD 1 #[]) (ms.getD 2 #[]) (ms.getD 3 #[]) (mult (spinDigit code 0))
        (mult (spinDigit code 1)) (mult (spinDigit code 2)) (mult (spinDigit code 3)) false X := by
  obtain ⟨h0, h1, h2, h3⟩ := stride_eq code
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  unfold kronRep kron4
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h0, h1, h2, h3]


/-- the Kronecker product of the `ρ`-matrices of a right-hand-side term in sector `p` -/
noncomputable def rhsKron (p : Fin 4 → Spin) (t : RhsTerm) :
    Matrix (∀ q, Fin (multF (p q))) (∀ q, Fin (multF (p q))) ℤ :=
  kronPi (fun q => ofMat (multF (p q)) (repProd (p q).val (t.2.getD q.val [])))

theorem kron4_eq_sum_gt (m : Fin 4 → ℕ) (Ms : Fin 4 → Array Int) (tr : Bool) (X : Array Int)
    (hX : X.size = m 0 * m 1 * m 2 * m 3) (x : ∀ q : Fin 4, Fin (m q)) :
    gt (kron4 (Ms 0) (Ms 1) (Ms 2) (Ms 3) (m 0) (m 1) (m 2) (m 3) tr X) (flatIx m x) =
      ∑ y : (∀ q : Fin 4, Fin (m q)), (∏ q, mEnt tr (Ms q) (m q) (x q) (y q)) * gt X (flatIx m y) :=
  kron4_eq_sum m Ms tr X hX x

theorem repMats_getD (c : ℕ) (t : RhsTerm) (q : ℕ) (hq : q < 4) :
    (repMats c t).getD q #[] = repProd (spinDigit c q) (t.2.getD q []) := by
  unfold repMats
  simp [Array.getD, hq]

theorem getD_map_lt {α β : Type*} (arr : Array α) (f : α → β) (i : ℕ) (hi : i < arr.size) (d : α) (d' : β) :
    (arr.map f).getD i d' = f (arr.getD i d) := by
  simp [Array.getD, hi]

theorem rhsCoords_apply (terms : Array RhsTerm) (p : Fin 4 → Spin) (A B : ℕ) (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    gt (rhsCoords terms (pcode p)) (A * nn (pcode p) + B) =
      ∑ ti ∈ range terms.size, (terms.getD ti default).1 * bilN p (rhsKron p (terms.getD ti default)) A B := by
  unfold rhsCoords
  dsimp only
  have hlt : A * nn (pcode p) + B < nn (pcode p) * nn (pcode p) := by nlinarith
  rw [gt_tab, ite_eq_left hlt, sumTo_eq]
  obtain ⟨d1, d2⟩ := div_mod_aux A B (nn (pcode p)) hB
  simp only [d1, d2]
  refine Finset.sum_congr rfl fun ti hti => ?_
  have hti' := Finset.mem_range.1 hti
  congr 1
  have hsz : terms.size > ti := hti'
  have hX1 : (((terms.map fun t => (List.range (nn (pcode p))).toArray.map fun b =>
        kronRep (pcode p) (repMats (pcode p) t) (slice vArr (vOff (pcode p) + b * sdim (pcode p)) (sdim (pcode p)))).getD ti #[]).getD B #[]) =
      kronRep (pcode p) (repMats (pcode p) (terms.getD ti default))
        (slice vArr (vOff (pcode p) + B * sdim (pcode p)) (sdim (pcode p))) := by
    rw [getD_map_lt terms _ ti hsz default #[]]
    have hB' : B < (List.range (nn (pcode p))).toArray.size := by simpa using hB
    rw [getD_map_lt _ _ B hB' 0 #[]]
    simp [hB]
  rw [hX1, kronRep_eq_kron4, sumTo_eq, sum_flat]
  unfold bilN
  refine Finset.sum_congr rfl fun x _ => ?_
  have hsize : (slice vArr (vOff (pcode p) + B * sdim (pcode p)) (sdim (pcode p))).size =
      radix p 0 * radix p 1 * radix p 2 * radix p 3 := by rw [slice_size, sdim_pcode]
  have hk := kron4_eq_sum_gt (radix p) (fun q => (repMats (pcode p) (terms.getD ti default)).getD q.val #[]) false
    (slice vArr (vOff (pcode p) + B * sdim (pcode p)) (sdim (pcode p))) hsize x
  have hm : ∀ q : Fin 4, mult (spinDigit (pcode p) q.val) = radix p q := fun q => by rw [spinDigit_pcode p q]; rfl
  have hm0 := hm 0; have hm1 := hm 1; have hm2 := hm 2; have hm3 := hm 3
  simp only [Fin.val_zero] at hm0
  rw [show ((1 : Fin 4) : ℕ) = 1 from rfl] at hm1
  rw [show ((2 : Fin 4) : ℕ) = 2 from rfl] at hm2
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl] at hm3
  rw [hm0, hm1, hm2, hm3]
  refine (congrArg (fun z => wAt (pcode p) A (flatIx (radix p) x) * z) hk).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hV : gt (slice vArr (vOff (pcode p) + B * sdim (pcode p)) (sdim (pcode p))) (flatIx (radix p) y) =
      vAt (pcode p) B (flatIx (radix p) y) := gt_flat_slice vArr p _ y
  rw [hV]
  have hP : ∏ q : Fin 4, mEnt false ((repMats (pcode p) (terms.getD ti default)).getD q.val #[]) (radix p q) (x q).val (y q).val =
      rhsKron p (terms.getD ti default) x y := by
    unfold rhsKron
    rw [kronPi_apply]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [repMats_getD _ _ q.val q.2, spinDigit_pcode p q]
    rfl
  rw [hP]; ring

/-!
## `Qtot` as the semantic sum over the covariants (K4 + quotient)
-/

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

/-!
## K7: the final comparison, semantically
-/

theorem foldl_add_range (f : ℕ → ℤ) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp

theorem dvd_lcmAll_aux (xs : List ℕ) (a : ℕ) : a ∣ xs.foldl Nat.lcm a := by
  induction xs generalizing a with
  | nil => exact dvd_rfl
  | cons x t ih => exact (Nat.dvd_lcm_left a x).trans (ih _)

theorem dvd_lcmAll (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x ∣ lcmAll xs := by
  unfold lcmAll
  induction xs generalizing x with
  | nil => simp at hx
  | cons y t ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | h
    · exact (Nat.dvd_lcm_right 1 x).trans (dvd_lcmAll_aux t _)
    · -- fold starting from lcm 1 y
      have : ∀ (t : List ℕ) (a : ℕ) (x : ℕ), x ∈ t → x ∣ t.foldl Nat.lcm a := by
        intro t
        induction t with
        | nil => intro a x hx; simp at hx
        | cons y t ih2 =>
          intro a x hx
          rw [List.foldl_cons]
          rcases List.mem_cons.1 hx with rfl | h
          · exact (Nat.dvd_lcm_right a x).trans (dvd_lcmAll_aux t _)
          · exact ih2 _ _ h
      exact this t _ x h

theorem lcmAll_ne_zero_aux (xs : List ℕ) (a : ℕ) (ha : a ≠ 0) (hx : ∀ x ∈ xs, x ≠ 0) : xs.foldl Nat.lcm a ≠ 0 := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x t ih =>
    rw [List.foldl_cons]
    exact ih _ (Nat.lcm_ne_zero ha (hx x (List.mem_cons_self))) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem lcmAll_ne_zero (xs : List ℕ) (hx : ∀ x ∈ xs, x ≠ 0) : lcmAll xs ≠ 0 :=
  lcmAll_ne_zero_aux xs 1 one_ne_zero hx

/-- K7, semantically: for every sector and basis pair the right-hand side coordinate equals the sum over the
`24` placements of the `Q`-coordinates, transported to the sector by the placement matrices. -/
theorem checkFinal_spec (rhs : Array RhsTerm) (Q : Array (Array Int)) (Dnum : Int)
    (hok : checkFinal rhs Q Dnum = true) (hP : checkPlacements () = true)
    (p : Fin 4 → Spin) (hn : 0 < nn (pcode p)) (A B : ℕ) (hA : A < nn (pcode p)) (hB : B < nn (pcode p)) :
    ∃ Dn : ℤ, Dn ≠ 0 ∧ (∀ pii : Fin 24, pden (pcode p) pii.val * pden (pcode p) pii.val ∣ Dn) ∧
      Dn * 2 * Dnum * gt (rhsCoords rhs (pcode p)) (A * nn (pcode p) + B) =
        ∑ pii : Fin 24, (Dn / (pden (pcode p) pii.val * pden (pcode p) pii.val)) *
          ∑ A' ∈ range (nn (pcode p)), ∑ B' ∈ range (nn (pcode p)),
            pSW (pcode p) pii.val A A' *
              gt (Q.getD (pcode (fun r => p (sg pii r))) #[]) (A' * nn (pcode p) + B') *
              pSV (pcode p) pii.val B B' := by
  unfold checkFinal at hok
  have h1 := (allTo_iff _ _).1 hok (pcode p) (pcode_lt p)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · omega
  have hlt : A * nn (pcode p) + B < nn (pcode p) * nn (pcode p) := by nlinarith
  have h2 := (allTo_iff _ _).1 h1 (A * nn (pcode p) + B) hlt
  simp only [beq_iff_eq] at h2
  obtain ⟨d1, d2⟩ := div_mod_aux A B (nn (pcode p)) hB
  simp only [d1, d2] at h2
  rw [foldl_add_range] at h2
  have hpd : ∀ pii : Fin 24, pden (pcode p) pii.val ≠ 0 := fun pii =>
    (checkPlacements_spec hP p pii hn).2.1
  refine ⟨(lcmAll ((List.range 24).map fun pii => (pden (pcode p) pii * pden (pcode p) pii).toNat) : ℤ), ?_, ?_, ?_⟩
  · have := lcmAll_ne_zero ((List.range 24).map fun pii => (pden (pcode p) pii * pden (pcode p) pii).toNat) ?_
    · exact_mod_cast this
    · intro x hx
      obtain ⟨pii, hpii, rfl⟩ := List.mem_map.1 hx
      have := hpd ⟨pii, List.mem_range.1 hpii⟩
      have h3 : pden (pcode p) pii * pden (pcode p) pii ≠ 0 := mul_ne_zero this this
      have h4 : 0 ≤ pden (pcode p) pii * pden (pcode p) pii := mul_self_nonneg _
      omega
  · intro pii
    have h4 : 0 ≤ pden (pcode p) pii.val * pden (pcode p) pii.val := mul_self_nonneg _
    have h5 := dvd_lcmAll ((List.range 24).map fun pii => (pden (pcode p) pii * pden (pcode p) pii).toNat)
      (pden (pcode p) pii.val * pden (pcode p) pii.val).toNat
      (List.mem_map.2 ⟨pii.val, List.mem_range.2 pii.2, rfl⟩)
    have h6 := Int.natCast_dvd_natCast.2 h5
    rwa [Int.toNat_of_nonneg h4] at h6
  · simp only [sumTo_eq] at h2
    rw [Finset.sum_range] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun pii _ => ?_
    rw [placed_eq]

end QVCheck
