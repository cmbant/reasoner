import FormalResearch.FourQubitEntropy.QVCheck.Pair2

/-!
# The coupled identity for one pair of letters in a sector `p`
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

theorem qe_psiMat (a : ℕ) (jx j' : Spin) (mu mup x y : ℕ) (hx : x < multF j') (hy : y < multF j') :
    qe (psiMat a jx j' mu mup) x y = psiAt (a - 3) jx.val j'.val mu mup x y := by
  unfold qe; rw [dif_pos ⟨hx, hy⟩]; rfl

theorem pairKron_A (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (mu mu' : Fin 4 → ℕ) (e e' : ℕ)
    (he : e < radix p 0 * radix p 1) (he' : e' < radix p 0 * radix p 1) :
    pairKron (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1) e e' =
      qe (psiMat a (sp 0) (p 0) (mu 0) (mu' 0)) (e / radix p 1) (e' / radix p 1) *
        qe (psiMat a (sp 1) (p 1) (mu 1) (mu' 1)) (e % radix p 1) (e' % radix p 1) := by
  unfold pairKron
  rw [pA_div, pA_mod]
  have h1 : e / radix p 1 < radix p 0 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have h2 : e' / radix p 1 < radix p 0 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he')
  have hpos : 0 < radix p 1 := by
    rcases Nat.eq_zero_or_pos (radix p 1) with h | h
    · rw [h] at he; omega
    · exact h
  have h3 : e % radix p 1 < radix p 1 := Nat.mod_lt _ hpos
  have h4 : e' % radix p 1 < radix p 1 := Nat.mod_lt _ hpos
  rw [qe_psiMat _ _ _ _ _ _ _ h1 h2, qe_psiMat _ _ _ _ _ _ _ h3 h4]
  rfl

theorem pairKron_B (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (mu mu' : Fin 4 → ℕ) (e e' : ℕ)
    (he : e < radix p 2 * radix p 3) (he' : e' < radix p 2 * radix p 3) :
    pairKron (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3) e e' =
      qe (psiMat a (sp 2) (p 2) (mu 2) (mu' 2)) (e / radix p 3) (e' / radix p 3) *
        qe (psiMat a (sp 3) (p 3) (mu 3) (mu' 3)) (e % radix p 3) (e' % radix p 3) := by
  unfold pairKron
  rw [pB_div, pB_mod]
  have h1 : e / radix p 3 < radix p 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have h2 : e' / radix p 3 < radix p 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he')
  have hpos : 0 < radix p 3 := by
    rcases Nat.eq_zero_or_pos (radix p 3) with h | h
    · rw [h] at he; omega
    · exact h
  have h3 : e % radix p 3 < radix p 3 := Nat.mod_lt _ hpos
  have h4 : e' % radix p 3 < radix p 3 := Nat.mod_lt _ hpos
  rw [qe_psiMat _ _ _ _ _ _ _ h1 h2, qe_psiMat _ _ _ _ _ _ _ h3 h4]
  rfl

theorem pair_identity (hT : checkT () = true) (hU : checkU () = true) (hS : checkStructure () = true)
    (p : Fin 4 → Spin) (a : ℕ) (sp : Fin 4 → Spin) (mu mu' : Fin 4 → ℕ) (A B : Fin (nnF p)) :
    delta (pA (pcode p)) ^ 2 * delta (pB (pcode p)) ^ 2 * DataStr.lc ^ 2 *
      (∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
        Wmat p x A * kronPi (fun r => psiMat a (sp r) (p r) (mu r) (mu' r)) x y * Vmat p y B) =
    ∑ u ∈ range (nn (pcode p)), ∑ u' ∈ range (nn (pcode p)),
      gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) * gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') *
        ctPair (pcode p)
          (tableLetter (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1))
          (tableLetter (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3))
          ((uInfo (pcode p)).getD u default) ((uInfo (pcode p)).getD u' default) := by
  have hcl : pcode p < 256 := pcode_lt p
  have hAn : A.val < nn (pcode p) := A.2
  have hBn : B.val < nn (pcode p) := B.2
  obtain ⟨hsz, hWs, -⟩ := checkStructure_spec hS (pcode p) hcl A.val hAn
  obtain ⟨-, -, hVs⟩ := checkStructure_spec hS (pcode p) hcl B.val hBn
  obtain ⟨hdA, hTA⟩ := checkT_spec hT (pA (pcode p)) (pA_lt p)
  obtain ⟨hdB, hTB⟩ := checkT_spec hT (pB (pcode p)) (pB_lt p)
  have hDA : pairDim (pA (pcode p)) = radix p 0 * radix p 1 := pairDim_pA p
  have hDB : pairDim (pB (pcode p)) = radix p 2 * radix p 3 := pairDim_pB p
  have e0 : (∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
        Wmat p x A * kronPi (fun r => psiMat a (sp r) (p r) (mu r) (mu' r)) x y * Vmat p y B) =
      ∑ x : (∀ q, Fin (multF (p q))), ∑ y : (∀ q, Fin (multF (p q))),
        (fun f => wAt (pcode p) A.val f) (flatIx (radix p) x) * kronPi (fun r => psiMat a (sp r) (p r) (mu r) (mu' r)) x y *
          (fun f => vAt (pcode p) B.val f) (flatIx (radix p) y) := rfl
  rw [e0, contr_eq_S4 (radix p) (fun r => psiMat a (sp r) (p r) (mu r) (mu' r))]
  have hA2 : ∀ i < radix p 0 * radix p 1, ∀ j < radix p 0 * radix p 1,
      ∑ k ∈ range (radix p 0 * radix p 1), tiAt (pA (pcode p)) i k * tAt (pA (pcode p)) k j =
        if i = j then delta (pA (pcode p)) else 0 := by
    intro i hi j hj
    rw [← hDA] at hi hj ⊢
    exact hTA i j hi hj
  have hB2 : ∀ i < radix p 2 * radix p 3, ∀ j < radix p 2 * radix p 3,
      ∑ k ∈ range (radix p 2 * radix p 3), tiAt (pB (pcode p)) i k * tAt (pB (pcode p)) k j =
        if i = j then delta (pB (pcode p)) else 0 := by
    intro i hi j hj
    rw [← hDB] at hi hj ⊢
    exact hTB i j hi hj
  have hbd : ∀ u < nn (pcode p), ∀ x < ((uInfo (pcode p)).getD u default).d,
      ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA + ((uInfo (pcode p)).getD u default).s
        < radix p 0 * radix p 1 ∧
      ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB + ((uInfo (pcode p)).getD u default).t
        < radix p 2 * radix p 3 := by
    intro u hu x hx
    have := (checkU_spec hU (pcode p) hcl u (by rw [hsz]; exact hu)).2.2 x hx
    rw [hDA, hDB] at this
    exact this
  have hW : ∀ i < radix p 0 * radix p 1, ∀ j < radix p 2 * radix p 3,
      DataStr.lc * (∑ l ∈ range (radix p 2 * radix p 3), (∑ k ∈ range (radix p 0 * radix p 1),
        tiAt (pA (pcode p)) k i * wAt (pcode p) A.val (k * (radix p 2 * radix p 3) + l)) * tiAt (pB (pcode p)) l j) =
      ∑ u ∈ range (nn (pcode p)), gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) *
        ∑ x ∈ range ((uInfo (pcode p)).getD u default).d,
          if i = ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA +
              ((uInfo (pcode p)).getD u default).s ∧
            j = ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB +
              ((uInfo (pcode p)).getD u default).t
          then wc ((uInfo (pcode p)).getD u default).lab x else 0 := by
    intro i hi j hj
    have h1 := hWs i (by rw [hDA]; exact hi) j (by rw [hDB]; exact hj)
    rw [coupledW_entry (pcode p) A.val i j (by rw [hDA]; exact hi) (by rw [hDB]; exact hj)] at h1
    simp only [hDA, hDB, hatEntry_eq] at h1
    simpa using h1
  have hV : ∀ i < radix p 0 * radix p 1, ∀ j < radix p 2 * radix p 3,
      DataStr.lc * (∑ l ∈ range (radix p 2 * radix p 3), (∑ k ∈ range (radix p 0 * radix p 1),
        tAt (pA (pcode p)) i k * vAt (pcode p) B.val (k * (radix p 2 * radix p 3) + l)) * tAt (pB (pcode p)) j l) =
      ∑ u ∈ range (nn (pcode p)), gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u) *
        ∑ x ∈ range ((uInfo (pcode p)).getD u default).d,
          if i = ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA +
              ((uInfo (pcode p)).getD u default).s ∧
            j = ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB +
              ((uInfo (pcode p)).getD u default).t
          then vc ((uInfo (pcode p)).getD u default).lab x else 0 := by
    intro i hi j hj
    have h1 := hVs i (by rw [hDA]; exact hi) j (by rw [hDB]; exact hj)
    rw [coupledV_entry (pcode p) B.val i j (by rw [hDA]; exact hi) (by rw [hDB]; exact hj)] at h1
    simp only [hDA, hDB, hatEntry_eq] at h1
    simpa using h1
  have key := coupled_generic (radix p 0 * radix p 1) (radix p 2 * radix p 3) (nn (pcode p))
    (tAt (pA (pcode p))) (tiAt (pA (pcode p))) (tAt (pB (pcode p))) (tiAt (pB (pcode p)))
    (fun i j => wAt (pcode p) A.val (i * (radix p 2 * radix p 3) + j))
    (fun i j => vAt (pcode p) B.val (i * (radix p 2 * radix p 3) + j))
    (fun i k => qe (psiMat a (sp 0) (p 0) (mu 0) (mu' 0)) (i / radix p 1) (k / radix p 1) *
      qe (psiMat a (sp 1) (p 1) (mu 1) (mu' 1)) (i % radix p 1) (k % radix p 1))
    (fun j l => qe (psiMat a (sp 2) (p 2) (mu 2) (mu' 2)) (j / radix p 3) (l / radix p 3) *
      qe (psiMat a (sp 3) (p 3) (mu 3) (mu' 3)) (j % radix p 3) (l % radix p 3))
    (delta (pA (pcode p))) (delta (pB (pcode p))) DataStr.lc
    (fun u => gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u))
    (fun u => gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u))
    (fun u => ((uInfo (pcode p)).getD u default).d)
    (fun u x => ((uInfo (pcode p)).getD u default).oA + x * ((uInfo (pcode p)).getD u default).gA +
      ((uInfo (pcode p)).getD u default).s)
    (fun u x => ((uInfo (pcode p)).getD u default).oB + x * ((uInfo (pcode p)).getD u default).gB +
      ((uInfo (pcode p)).getD u default).t)
    (fun u x => wc ((uInfo (pcode p)).getD u default).lab x) (fun u x => vc ((uInfo (pcode p)).getD u default).lab x)
    hA2 hB2 hbd hW hV
  refine Eq.trans key ?_
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
  refine congrArg (fun z => gt omArr (nnOff (pcode p) + A.val * nn (pcode p) + u) *
    gt xiArr (nnOff (pcode p) + B.val * nn (pcode p) + u') * z) ?_
  have hu1 := Finset.mem_range.1 hu
  have hu2 := Finset.mem_range.1 hu'
  unfold ctPair
  simp only [sumTo_eq]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  have hx' := Finset.mem_range.1 hx
  have hy' := Finset.mem_range.1 hy
  obtain ⟨b1, b2⟩ := hbd u hu1 x hx'
  obtain ⟨b3, b4⟩ := hbd u' hu2 y hy'
  have t1 := tableLetter_apply (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1) _ _
    (by rw [← pairDim]; rw [hDA]; exact b1) (by rw [← pairDim]; rw [hDA]; exact b3)
  have t2 := tableLetter_apply (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3) _ _
    (by rw [← pairDim]; rw [hDB]; exact b2) (by rw [← pairDim]; rw [hDB]; exact b4)
  change gt _ (_ * pairDim (pA (pcode p)) + _) = _ at t1
  change gt _ (_ * pairDim (pB (pcode p)) + _) = _ at t2
  rw [t1, t2]
  have hrA : mult (pA (pcode p) / 4) * mult (pA (pcode p) % 4) = radix p 0 * radix p 1 := hDA
  have hrB : mult (pB (pcode p) / 4) * mult (pB (pcode p) % 4) = radix p 2 * radix p 3 := hDB
  rw [hrA, hrB]
  have hSA : ∀ row col : ℕ, (∑ e ∈ range (radix p 0 * radix p 1), ∑ e' ∈ range (radix p 0 * radix p 1),
      tAt (pA (pcode p)) row e * (qe (psiMat a (sp 0) (p 0) (mu 0) (mu' 0)) (e / radix p 1) (e' / radix p 1) *
        qe (psiMat a (sp 1) (p 1) (mu 1) (mu' 1)) (e % radix p 1) (e' % radix p 1)) * tiAt (pA (pcode p)) e' col) =
      ∑ e ∈ range (radix p 0 * radix p 1), ∑ e' ∈ range (radix p 0 * radix p 1),
        tAt (pA (pcode p)) row e * pairKron (a - 3) (sp 0).val (sp 1).val (pA (pcode p)) (mu 0, mu' 0, mu 1, mu' 1) e e' *
          tiAt (pA (pcode p)) e' col := by
    intro row col
    refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun e' he' => ?_
    rw [pairKron_A p a sp mu mu' e e' (Finset.mem_range.1 he) (Finset.mem_range.1 he')]
  have hSB : ∀ row col : ℕ, (∑ e ∈ range (radix p 2 * radix p 3), ∑ e' ∈ range (radix p 2 * radix p 3),
      tAt (pB (pcode p)) row e * (qe (psiMat a (sp 2) (p 2) (mu 2) (mu' 2)) (e / radix p 3) (e' / radix p 3) *
        qe (psiMat a (sp 3) (p 3) (mu 3) (mu' 3)) (e % radix p 3) (e' % radix p 3)) * tiAt (pB (pcode p)) e' col) =
      ∑ e ∈ range (radix p 2 * radix p 3), ∑ e' ∈ range (radix p 2 * radix p 3),
        tAt (pB (pcode p)) row e * pairKron (a - 3) (sp 2).val (sp 3).val (pB (pcode p)) (mu 2, mu' 2, mu 3, mu' 3) e e' *
          tiAt (pB (pcode p)) e' col := by
    intro row col
    refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun e' he' => ?_
    rw [pairKron_B p a sp mu mu' e e' (Finset.mem_range.1 he) (Finset.mem_range.1 he')]
  rw [hSA, hSB]

end QVCheck
