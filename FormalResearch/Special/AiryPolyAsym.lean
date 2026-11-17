module

public import FormalResearch.Special.AiryPolyAlg

/-!
# Leading-term bounds for a real polynomial at large complex argument, and the dominance dichotomy

Elementary inputs for `AiryPolyCircle` (`general_theorems.tex` Lemma 1.0′: `|P(u)| r^{-1/4} ≍ r^{p-1/4}`,
`|Q(u)| r^{1/4} ≍ r^{q+1/4}`, so one of the two terms of `N = P Ai + Q Ai'` dominates by a factor `r^{1/2}`).

* `airyPQ_asymp`: for a nonzero real polynomial `p` of degree `d` and leading coefficient `c` there are `T ≥ 1`, `L ≥ 0` with, for
  every complex `u`, `‖u‖ ≥ T`: `(|c|/2) ‖u‖^d ≤ ‖p(u)‖ ≤ 2|c| ‖u‖^d` and `‖p'(u)‖ ‖u‖ ≤ L ‖p(u)‖`.
* `airyPQ_dominance` (`P`, `Q` with `Q = 0 ∧ P ≠ 0` or `P ≠ 0 ∧ Q ≠ 0 ∧ deg Q < deg P`: **P-dominant**;
  `Q ≠ 0 ∧ (P = 0 ∨ deg P ≤ deg Q)`: **Q-dominant**): for `‖u‖ ≥ T`, `16 ‖Q(u)‖ √‖u‖ ≤ ‖P(u)‖` in the first case and
  `16 ‖P(u)‖ ≤ ‖Q(u)‖ √‖u‖` in the second.

All proved.
-/

@[expose] public section

open Complex Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

lemma airyPQc_eq_sum' (p : ℝ[X]) {n : ℕ} (hn : p.natDegree < n) (z : ℂ) :
    airyPQc p z = ∑ k ∈ Finset.range n, (p.coeff k : ℂ) * z ^ k := by
  unfold airyPQc
  rw [Polynomial.eval_eq_sum_range' (n := n)]
  · simp [Polynomial.coeff_map]
  · exact lt_of_le_of_lt (Polynomial.natDegree_map_le) hn

/-- Crude bound for a polynomial of degree `≤ e` on `‖u‖ ≥ 1`. -/
lemma airyPQc_norm_le (q : ℝ[X]) (e : ℕ) (hq : q.natDegree ≤ e) {u : ℂ} (hu : 1 ≤ ‖u‖) :
    ‖airyPQc q u‖ ≤ (∑ k ∈ Finset.range (e + 1), |q.coeff k|) * ‖u‖ ^ e := by
  rw [airyPQc_eq_sum' q (Nat.lt_succ_of_le hq), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    (abs_nonneg _)

/-- **Leading-term bounds.** -/
theorem airyPQ_asymp (p : ℝ[X]) (hp : p ≠ 0) : ∃ T L : ℝ, 1 ≤ T ∧ 0 ≤ L ∧ ∀ u : ℂ, T ≤ ‖u‖ →
    |p.leadingCoeff| / 2 * ‖u‖ ^ p.natDegree ≤ ‖airyPQc p u‖ ∧
    ‖airyPQc p u‖ ≤ 2 * |p.leadingCoeff| * ‖u‖ ^ p.natDegree ∧
    ‖airyPQc (derivative p) u‖ * ‖u‖ ≤ L * ‖airyPQc p u‖ := by
  set d := p.natDegree with hd
  set c := p.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hca : 0 < |c| := abs_pos.mpr hc0
  set S : ℝ := ∑ k ∈ Finset.range d, |p.coeff k| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set S' : ℝ := ∑ k ∈ Finset.range (d - 1 + 1), |(derivative p).coeff k| with hS'
  have hS'0 : 0 ≤ S' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨max 1 (2 * S / |c|), 2 * S' / |c|, le_max_left _ _, by positivity, fun u hu => ?_⟩
  have hu1 : 1 ≤ ‖u‖ := (le_max_left _ _).trans hu
  have hu2 : 2 * S / |c| ≤ ‖u‖ := (le_max_right _ _).trans hu
  have hdec : airyPQc p u = (c : ℂ) * u ^ d + ∑ k ∈ Finset.range d, (p.coeff k : ℂ) * u ^ k := by
    rw [airyPQc_eq_sum' p (Nat.lt_succ_self d), Finset.sum_range_succ, add_comm]
    have e : p.coeff d = c := Polynomial.coeff_natDegree
    rw [e]
  have hR : ‖∑ k ∈ Finset.range d, (p.coeff k : ℂ) * u ^ k‖ ≤ S * ‖u‖ ^ (d - 1) := by
    rw [hS, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu1 (by have := Finset.mem_range.mp hk; omega))
      (abs_nonneg _)
  have hSle : S * ‖u‖ ^ (d - 1) ≤ |c| / 2 * ‖u‖ ^ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · have : S = 0 := by rw [hS, h0]; simp
      rw [this, zero_mul]; positivity
    · have e1 : ‖u‖ ^ d = ‖u‖ * ‖u‖ ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e1]
      have : S ≤ |c| / 2 * ‖u‖ := by
        have := (div_le_iff₀ hca).mp hu2
        nlinarith
      calc S * ‖u‖ ^ (d - 1) ≤ (|c| / 2 * ‖u‖) * ‖u‖ ^ (d - 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
  have hlow : |c| / 2 * ‖u‖ ^ d ≤ ‖airyPQc p u‖ := by
    have h1 := norm_sub_norm_le ((c : ℂ) * u ^ d) (-(∑ k ∈ Finset.range d, (p.coeff k : ℂ) * u ^ k))
    rw [sub_neg_eq_add, ← hdec, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at h1
    nlinarith
  have hup : ‖airyPQc p u‖ ≤ 2 * |c| * ‖u‖ ^ d := by
    have h1 := norm_add_le ((c : ℂ) * u ^ d) (∑ k ∈ Finset.range d, (p.coeff k : ℂ) * u ^ k)
    rw [← hdec, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at h1
    nlinarith
  refine ⟨hlow, hup, ?_⟩
  -- derivative
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [derivative_of_natDegree_zero h0, airyPQc_zero]
    simp only [norm_zero, zero_mul]
    positivity
  · have hdn : (derivative p).natDegree ≤ d - 1 := natDegree_derivative_le p
    have h1 := airyPQc_norm_le (derivative p) (d - 1) hdn hu1
    have e1 : ‖u‖ ^ d = ‖u‖ * ‖u‖ ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hnu : 0 < ‖u‖ := by linarith
    calc ‖airyPQc (derivative p) u‖ * ‖u‖ ≤ S' * ‖u‖ ^ (d - 1) * ‖u‖ := by gcongr
      _ = S' * ‖u‖ ^ d := by rw [e1]; ring
      _ ≤ S' * (2 / |c| * ‖airyPQc p u‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hS'0
          rw [div_mul_eq_mul_div, le_div_iff₀ hca]
          nlinarith
      _ = 2 * S' / |c| * ‖airyPQc p u‖ := by ring

/-- The two cases of the dominance dichotomy. -/
def AiryPQDomP (P Q : ℝ[X]) : Prop :=
  (Q = 0 ∧ P ≠ 0) ∨ (P ≠ 0 ∧ Q ≠ 0 ∧ Q.natDegree < P.natDegree)

def AiryPQDomQ (P Q : ℝ[X]) : Prop :=
  Q ≠ 0 ∧ (P = 0 ∨ (P ≠ 0 ∧ P.natDegree ≤ Q.natDegree))

lemma airyPQ_domP_or_domQ (P Q : ℝ[X]) (h : P ≠ 0 ∨ Q ≠ 0) : AiryPQDomP P Q ∨ AiryPQDomQ P Q := by
  by_cases hQ : Q = 0
  · left; left; exact ⟨hQ, h.resolve_right (not_not.mpr hQ)⟩
  · by_cases hP : P = 0
    · right; exact ⟨hQ, Or.inl hP⟩
    · by_cases hd : Q.natDegree < P.natDegree
      · left; right; exact ⟨hP, hQ, hd⟩
      · right; exact ⟨hQ, Or.inr ⟨hP, not_lt.mp hd⟩⟩

lemma airyPQ_not_domP_domQ (P Q : ℝ[X]) : ¬ (AiryPQDomP P Q ∧ AiryPQDomQ P Q) := by
  rintro ⟨hP, hQ⟩
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact hQ.1 h1
  · rcases hQ.2 with h | ⟨-, h⟩
    · exact h1 h
    · omega

/-- **Dominance.** -/
theorem airyPQ_dominance (P Q : ℝ[X]) : ∃ T : ℝ, 1 ≤ T ∧ ∀ u : ℂ, T ≤ ‖u‖ →
    (AiryPQDomP P Q → 16 * ‖airyPQc Q u‖ * √‖u‖ ≤ ‖airyPQc P u‖) ∧
    (AiryPQDomQ P Q → 16 * ‖airyPQc P u‖ ≤ ‖airyPQc Q u‖ * √‖u‖) := by
  by_cases hP : P = 0
  · by_cases hQ : Q = 0
    · exact ⟨1, le_rfl, fun u _ => ⟨fun h => by simp [hP, hQ, airyPQc_zero], fun h => by simp [hP, hQ, airyPQc_zero]⟩⟩
    · obtain ⟨T, L, hT1, -, hT⟩ := airyPQ_asymp Q hQ
      refine ⟨T, hT1, fun u hu => ⟨fun h => ?_, fun _ => ?_⟩⟩
      · rcases h with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact absurd h2 (by simp [hP])
        · exact absurd hP h1
      · simp only [hP, airyPQc_zero, norm_zero, mul_zero]; positivity
  · by_cases hQ : Q = 0
    · obtain ⟨T, L, hT1, -, hT⟩ := airyPQ_asymp P hP
      refine ⟨T, hT1, fun u hu => ⟨fun _ => ?_, fun h => ?_⟩⟩
      · simp [hQ, airyPQc_zero]
      · exact absurd hQ h.1
    · obtain ⟨T1, L1, hT11, -, hT1⟩ := airyPQ_asymp P hP
      obtain ⟨T2, L2, hT21, -, hT2⟩ := airyPQ_asymp Q hQ
      set cP := |P.leadingCoeff| with hcP
      set cQ := |Q.leadingCoeff| with hcQ
      have hcP0 : 0 < cP := abs_pos.mpr (leadingCoeff_ne_zero.mpr hP)
      have hcQ0 : 0 < cQ := abs_pos.mpr (leadingCoeff_ne_zero.mpr hQ)
      set Tm : ℝ := max (max T1 T2) (max 1 ((64 * cQ / cP) ^ 2 + (64 * cP / cQ) ^ 2)) with hTm
      have hT1m : T1 ≤ Tm := (le_max_left T1 T2).trans (le_max_left _ _)
      have hT2m : T2 ≤ Tm := (le_max_right T1 T2).trans (le_max_left _ _)
      have hT3m : (64 * cQ / cP) ^ 2 + (64 * cP / cQ) ^ 2 ≤ Tm :=
        (le_max_right 1 ((64 * cQ / cP) ^ 2 + (64 * cP / cQ) ^ 2)).trans (le_max_right _ _)
      refine ⟨Tm, hT11.trans hT1m, fun u hu => ?_⟩
      have hu1 : T1 ≤ ‖u‖ := hT1m.trans hu
      have hu2 : T2 ≤ ‖u‖ := hT2m.trans hu
      have hu3 : (64 * cQ / cP) ^ 2 + (64 * cP / cQ) ^ 2 ≤ ‖u‖ := hT3m.trans hu
      have hr1 : 1 ≤ ‖u‖ := hT11.trans hu1
      have hsq0 : 0 ≤ √‖u‖ := Real.sqrt_nonneg _
      have hsq1 : 1 ≤ √‖u‖ := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hr1
      obtain ⟨hPl, hPu, -⟩ := hT1 u hu1
      obtain ⟨hQl, hQu, -⟩ := hT2 u hu2
      have hsqr : √‖u‖ ^ 2 = ‖u‖ := Real.sq_sqrt (by linarith)
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, -, hlt⟩)
        · exact absurd h1 hQ
        · -- 16 ‖Q‖ √r ≤ 2 cQ r^{dQ} 16 √r ≤ cP/2 r^{dP}
          have hm : (64 * cQ / cP) ≤ √‖u‖ := by
            apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg (64 * cP / cQ)]
          have hdp : ‖u‖ ^ (Q.natDegree + 1) ≤ ‖u‖ ^ P.natDegree := pow_le_pow_right₀ hr1 hlt
          have e1 : ‖u‖ ^ (Q.natDegree + 1) = ‖u‖ ^ Q.natDegree * √‖u‖ * √‖u‖ := by
            rw [mul_assoc, Real.mul_self_sqrt (by linarith), pow_succ]
          have hpowpos : 0 < ‖u‖ ^ Q.natDegree := pow_pos (by linarith) _
          have : 16 * (2 * cQ * ‖u‖ ^ Q.natDegree) * √‖u‖ ≤ cP / 2 * ‖u‖ ^ P.natDegree := by
            calc 16 * (2 * cQ * ‖u‖ ^ Q.natDegree) * √‖u‖ = (32 * cQ) * (‖u‖ ^ Q.natDegree * √‖u‖) := by ring
              _ ≤ (cP / 2 * √‖u‖) * (‖u‖ ^ Q.natDegree * √‖u‖) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  rw [div_le_iff₀ hcP0] at hm; nlinarith
              _ = cP / 2 * ‖u‖ ^ (Q.natDegree + 1) := by rw [e1]; ring
              _ ≤ _ := by gcongr
          calc 16 * ‖airyPQc Q u‖ * √‖u‖ ≤ 16 * (2 * cQ * ‖u‖ ^ Q.natDegree) * √‖u‖ := by gcongr
            _ ≤ _ := this
            _ ≤ _ := hPl
      · rintro ⟨-, (h1 | ⟨-, hle⟩)⟩
        · exact absurd h1 hP
        · have hm : (64 * cP / cQ) ≤ √‖u‖ := by
            apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg (64 * cQ / cP)]
          have hdp : ‖u‖ ^ P.natDegree ≤ ‖u‖ ^ Q.natDegree := pow_le_pow_right₀ hr1 hle
          have hpowpos : 0 < ‖u‖ ^ Q.natDegree := pow_pos (by linarith) _
          calc 16 * ‖airyPQc P u‖ ≤ 16 * (2 * cP * ‖u‖ ^ P.natDegree) := by gcongr
            _ ≤ 16 * (2 * cP * ‖u‖ ^ Q.natDegree) := by gcongr
            _ ≤ cQ / 2 * ‖u‖ ^ Q.natDegree * √‖u‖ := by
                have : 32 * cP ≤ cQ / 2 * √‖u‖ := by
                  rw [div_le_iff₀ hcQ0] at hm; nlinarith
                nlinarith
            _ ≤ ‖airyPQc Q u‖ * √‖u‖ := by gcongr

/-- info: 'FormalResearch.Special.airyPQ_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_asymp

/-- info: 'FormalResearch.Special.airyPQ_dominance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_dominance

end FormalResearch.Special
