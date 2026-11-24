module

public import FormalResearch.SignUncertainty.O4CertCheck
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Soundness of the box test

`box_sound`: if `checkBox i j = true`, then for all reals `L, s, a, t` (and tail errors `er, ei`) in the rational intervals of the box `(i, j)`, the
numerator `num` and denominator `den` of the quotient at `θ = (1/4)(1 - t² + 2it)/(1 + t²)` satisfy `10000 |num|² ≤ 169 |den|²` and `|den|² > 0`
(in the form `boxSq`, i.e. `(re² + im²)` times the integer).  Nothing is assumed about `L, s, a` beyond the interval membership; the analytic meaning
of `num/den` as the paper's quotient is proved in `O4QuotientBound.lean`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty.O4Cert

/-- The Horner coefficients as reals. -/
noncomputable def csReal : List ℝ := csData.map fun pq => (pq.1 : ℝ) / pq.2

lemma EncL_rat : ∀ l : List (ℤ × ℕ), (∀ pq ∈ l, 0 < pq.2) →
    EncL (l.map fun pq => (pq.1 : ℝ) / pq.2) (l.map fun pq => Ball.rat pq.1 pq.2)
  | [], _ => EncL.nil
  | pq :: l, h => EncL.cons (Enc.rat pq.1 pq.2 (h pq (by simp))) (EncL_rat l fun x hx => h x (by simp [hx]))

lemma csData_pos : ∀ pq ∈ csData, 0 < pq.2 := by decide +kernel

/-- The real inputs of a box. -/
noncomputable def realInp (L s a t er ei : ℝ) : Inp ℝ :=
  ⟨L, s, a, t, (1 + t * t)⁻¹, Real.pi, Real.pi⁻¹, (Real.pi * Real.pi)⁻¹, ((1 : ℤ) : ℝ) / ((4 : ℕ) : ℝ),
    ((1 : ℤ) : ℝ) / ((36 : ℕ) : ℝ), er, ei, csReal⟩

lemma Ball.pos_of_leMul {k : ℕ} {a b : Ball} (h : Ball.leMul k a b = true) : b.pos = true := by
  simp only [Ball.leMul, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Ball.pos, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h.1.1.2, h.1.2⟩

theorem box_sound {i j : ℕ} (h : checkBox i j = true) {L s a t er ei : ℝ}
    (hL1 : 2 * (i : ℝ) / (1000 * NL) ≤ L) (hL2 : L ≤ 2 * ((i : ℝ) + 1) / (1000 * NL))
    (hs1 : (4000 * (NL : ℝ) - ((i : ℝ) + 1)) / (4000 * NL) ≤ s)
    (hs2 : s ≤ (500000 * (NL : ℝ) + 606 * ((i : ℝ) + 1)) / (500000 * NL))
    (ha1 : 2 * (i : ℝ) / (1000 * NL) ≤ a)
    (ha2 : a ≤ ((i : ℝ) + 1) * (2000 * (NL : ℝ) + ((i : ℝ) + 1)) / (1000000 * NL * NL))
    (ht1 : (j : ℝ) / NT ≤ t) (ht2 : t ≤ ((j : ℝ) + 1) / NT)
    (her : |er| ≤ (tailR : ℝ) / SC) (hei : |ei| ≤ (tailR : ℝ) / SC) :
    boxSq (boxEval (realInp L s a t er ei)).1 10000 ≤ boxSq (boxEval (realInp L s a t er ei)).2 169 ∧
      0 < boxSq (boxEval (realInp L s a t er ei)).2 169 := by
  have hNL : (0 : ℝ) < NL := by unfold NL; norm_num
  have hNT : (0 : ℝ) < NT := by unfold NT; norm_num
  have hSC := SC_real_pos
  have ht : Enc t (boxInp i j).t := by
    refine Enc.hullQ (by unfold NT; norm_num) (by unfold NT; norm_num) ?_ ?_
    · simpa using ht1
    · simpa using ht2
  have hpi : Enc Real.pi piB := by
    refine Enc.hullQ (by norm_num) (by norm_num) ?_ ?_
    · have := Real.pi_gt_d20
      push_cast; rw [div_le_iff₀ (by norm_num)]; norm_num at this ⊢; linarith
    · have := Real.pi_lt_d20
      push_cast; rw [le_div_iff₀ (by norm_num)]; norm_num at this ⊢; linarith
  have hE : ∀ e : ℝ, |e| ≤ (tailR : ℝ) / SC → Enc e (⟨0, tailR, true⟩ : Ball) := by
    intro e he _
    show |e * (SC : ℝ) - ((0 : ℤ) : ℝ)| ≤ (tailR : ℝ)
    rw [Int.cast_zero, sub_zero, abs_mul, abs_of_pos hSC]
    rwa [le_div_iff₀ hSC] at he
  have hone : Enc (1 : ℝ) (ic 1 : Ball) := by
    have h1 := Enc.intCast (1 : ℤ)
    rwa [Int.cast_one] at h1
  have hI : InpEnc (realInp L s a t er ei) (boxInp i j) := by
    refine ⟨?_, ?_, ?_, ht, ?_, hpi, Enc.inv hpi, Enc.inv (Enc.mul hpi hpi), Enc.rat 1 4 (by norm_num),
      Enc.rat 1 36 (by norm_num), hE er her, hE ei hei, EncL_rat csData csData_pos⟩
    · refine Enc.hullQ (by unfold NL; norm_num) (by unfold NL; norm_num) ?_ ?_
      · push_cast; exact hL1
      · push_cast; exact hL2
    · refine Enc.hullQ (by unfold NL; norm_num) (by unfold NL; norm_num) ?_ ?_
      · push_cast; exact hs1
      · push_cast; exact hs2
    · refine Enc.hullQ (by unfold NL; norm_num) (by unfold NL; norm_num) ?_ ?_
      · push_cast; exact ha1
      · push_cast; exact ha2
    · exact Enc.inv (Enc.add hone (Enc.mul ht ht))
  obtain ⟨hn, hd⟩ := boxEval_enc hI
  have hsn := boxSq_enc hn 10000
  have hsd := boxSq_enc hd 169
  have h' : Ball.leMul 1 (boxSq (boxEval (boxInp i j)).1 10000) (boxSq (boxEval (boxInp i j)).2 169) = true := h
  refine ⟨?_, Enc.pos hsd (Ball.pos_of_leMul h')⟩
  have := Enc.le_of_leMul hsn hsd h'
  simpa using this

/-- info: 'FormalResearch.SignUncertainty.O4Cert.box_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms box_sound

end FormalResearch.SignUncertainty.O4Cert
