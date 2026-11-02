import FormalResearch.FourQubitEntropy.QVCheck.Pair

/-!
# Specifications extracted from the structural checks (K3, `checkU`) and the sector arithmetic
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem pA_pcode (p : Fin 4 → Spin) : pA (pcode p) = (p 0).val * 4 + (p 1).val := by
  have h0 : spinDigit (pcode p) 0 = (p 0).val := spinDigit_pcode p 0
  have h1 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  unfold pA pairIdx; rw [h0, h1]

theorem pB_pcode (p : Fin 4 → Spin) : pB (pcode p) = (p 2).val * 4 + (p 3).val := by
  have h0 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have h1 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  unfold pB pairIdx; rw [h0, h1]

theorem pA_div (p : Fin 4 → Spin) : pA (pcode p) / 4 = (p 0).val := by
  rw [pA_pcode]; have := (p 1).2; omega

theorem pA_mod (p : Fin 4 → Spin) : pA (pcode p) % 4 = (p 1).val := by
  rw [pA_pcode]; have := (p 1).2; omega

theorem pB_div (p : Fin 4 → Spin) : pB (pcode p) / 4 = (p 2).val := by
  rw [pB_pcode]; have := (p 3).2; omega

theorem pB_mod (p : Fin 4 → Spin) : pB (pcode p) % 4 = (p 3).val := by
  rw [pB_pcode]; have := (p 3).2; omega

theorem pA_lt (p : Fin 4 → Spin) : pA (pcode p) < 16 := by rw [pA_pcode]; have := (p 0).2; have := (p 1).2; omega
theorem pB_lt (p : Fin 4 → Spin) : pB (pcode p) < 16 := by rw [pB_pcode]; have := (p 2).2; have := (p 3).2; omega

theorem pairDim_pA (p : Fin 4 → Spin) : pairDim (pA (pcode p)) = radix p 0 * radix p 1 := by
  unfold pairDim; rw [pA_div, pA_mod]; rfl

theorem pairDim_pB (p : Fin 4 → Spin) : pairDim (pB (pcode p)) = radix p 2 * radix p 3 := by
  unfold pairDim; rw [pB_div, pB_mod]; rfl

theorem checkU_spec (h : checkU () = true) (code : ℕ) (hc : code < 256) (k : ℕ) (hk : k < (uInfo code).size) :
    let e := (uInfo code).getD k default
    e.s < e.gA ∧ e.t < e.gB ∧ ∀ x < e.d, e.oA + x * e.gA + e.s < pairDim (pA code) ∧ e.oB + x * e.gB + e.t < pairDim (pB code) := by
  unfold checkU at h
  have h1 := (allTo_iff _ _).1 h code (by rw [hide_eq]; exact hc)
  have h2 := (allTo_iff _ _).1 h1 k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨h2.1.1, h2.1.2, fun x hx => ?_⟩
  have := (allTo_iff _ _).1 h2.2 x hx
  simpa using this

theorem hatEntry_eq (isW : Bool) (code u i j : ℕ) :
    hatEntry isW code u i j =
      ∑ x ∈ range ((uInfo code).getD u default).d,
        if i = ((uInfo code).getD u default).oA + x * ((uInfo code).getD u default).gA + ((uInfo code).getD u default).s ∧
           j = ((uInfo code).getD u default).oB + x * ((uInfo code).getD u default).gB + ((uInfo code).getD u default).t
        then (if isW then wc ((uInfo code).getD u default).lab x else vc ((uInfo code).getD u default).lab x) else 0 := by
  unfold hatEntry
  rw [sumTo_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : i = ((uInfo code).getD u default).oA + x * ((uInfo code).getD u default).gA + ((uInfo code).getD u default).s ∧
           j = ((uInfo code).getD u default).oB + x * ((uInfo code).getD u default).gB + ((uInfo code).getD u default).t
  · rw [if_pos h]; rw [if_pos]; simp [h.1, h.2]
  · rw [if_neg h, if_neg]; simpa using h

theorem checkStructure_spec (h : checkStructure () = true) (code : ℕ) (hc : code < 256) (b : ℕ) (hb : b < nn code) :
    (uInfo code).size = nn code ∧
    (∀ i < pairDim (pA code), ∀ j < pairDim (pB code),
      DataStr.lc * gt (coupledW code b) (i * pairDim (pB code) + j) =
        ∑ u ∈ range (nn code), gt omArr (nnOff code + b * nn code + u) * hatEntry true code u i j) ∧
    (∀ i < pairDim (pA code), ∀ j < pairDim (pB code),
      DataStr.lc * gt (coupledV code b) (i * pairDim (pB code) + j) =
        ∑ u ∈ range (nn code), gt xiArr (nnOff code + b * nn code + u) * hatEntry false code u i j) := by
  unfold checkStructure at h
  have h1 := (allTo_iff _ _).1 h code (by rw [hide_eq]; exact hc)
  have h2 := (allTo_iff _ _).1 h1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  have hsz : (uInfo code).size = nn code := h2.1
  refine ⟨hsz, fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · have h3 := (allTo_iff _ _).1 h2.2 (i * pairDim (pB code) + j) (by nlinarith)
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    have e1 := h3.1
    obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
    simp only [d1, d2] at e1
    rw [e1]
    unfold reconEntry
    rw [sumTo_eq, hsz]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold slice
    rw [gt_tab, if_pos (Finset.mem_range.1 hu)]
  · have h3 := (allTo_iff _ _).1 h2.2 (i * pairDim (pB code) + j) (by nlinarith)
    simp only [Bool.and_eq_true, beq_iff_eq] at h3
    have e1 := h3.2
    obtain ⟨d1, d2⟩ := div_mod_aux i j (pairDim (pB code)) hj
    simp only [d1, d2] at e1
    rw [e1]
    unfold reconEntry
    rw [sumTo_eq, hsz]
    refine Finset.sum_congr rfl fun u hu => ?_
    unfold slice
    rw [gt_tab, if_pos (Finset.mem_range.1 hu)]

end QVCheck
