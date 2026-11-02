import FormalResearch.FourQubitEntropy.QVCheck.Place2

/-!
# The right-hand side coordinates (K6) and the final comparison (K7)
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

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
  rw [gt_tab, if_pos hlt, sumTo_eq]
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
    simp [hB, Array.getElem?_range]
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

end QVCheck
