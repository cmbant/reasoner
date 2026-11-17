module

public import FormalResearch.Special.AiryPolyAlg

/-!
# Hermite-Biehler pairs of real polynomials: the Herglotz inequality and the positive Wronskian

`SOFT_EDGE_THEOREMS.md` Lemma 4.6: `P, Q` real polynomials such that `Q + iP` has all its roots in the open lower half plane
(**Hermite-Biehler**, `AiryPQHB`).  Algebraic consequences used for the zero theory of `N = P Ai + Q Ai'` (`AiryPolyZeros`):

* `airyPQHB_norm_le` (**Herglotz inequality**): for `Im z ≥ 0`, `‖Q(z) - i P(z)‖ ≤ ‖Q(z) + i P(z)‖` (the Blaschke product
  `B = (Q + iP)^#/(Q + iP)` of the note has `|B| ≤ 1` on the upper half plane);
* `airyPQHB_wronskian` (**positive Wronskian**): `P(x) Q'(x) - Q(x) P'(x) ≥ 0` for real `x` (this is `Φ' ≤ 0` for the argument
  `Φ` of `Q + iP`, `Φ = arg c + Σ_j arg(x - w̄_j)` in the note), and `> 0` as soon as `Q + iP` is not constant;
* the real zeros of `P` and `Q` do not meet (`airyPQHB_ne_zero_real`: `(Q(x), P(x)) ≠ (0, 0)`).

Proof: `Q + iP = c Π (z - w_j)` over `ℂ` (`Splits.eval_eq_prod_roots`), `Im w_j < 0`; `‖z̄ - w‖ ≤ ‖z - w‖` for `Im z ≥ 0 > Im w` factorwise, and
`(Q' + iP')/(Q + iP) = Σ 1/(x - w_j)` (`Splits.eval_derivative_div_eval_of_ne_zero`) has imaginary part `Σ Im w_j/|x - w_j|² ≤ 0`.
All proved.
-/

@[expose] public section

open Complex Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

/-- The complex polynomial `Q + iP`. -/
noncomputable def airyPQF (P Q : ℝ[X]) : ℂ[X] :=
  Q.map (algebraMap ℝ ℂ) + Polynomial.C I * P.map (algebraMap ℝ ℂ)

lemma airyPQF_eval (P Q : ℝ[X]) (z : ℂ) :
    (airyPQF P Q).eval z = airyPQc Q z + I * airyPQc P z := by
  simp [airyPQF, airyPQc]

lemma airyPQF_derivative_eval (P Q : ℝ[X]) (z : ℂ) :
    (airyPQF P Q).derivative.eval z = airyPQc (derivative Q) z + I * airyPQc (derivative P) z := by
  simp [airyPQF, airyPQc, Polynomial.derivative_map]

lemma airyPQF_conj (P Q : ℝ[X]) (z : ℂ) :
    (starRingEnd ℂ) ((airyPQF P Q).eval ((starRingEnd ℂ) z)) = airyPQc Q z - I * airyPQc P z := by
  rw [airyPQF_eval, map_add, map_mul, conj_airyPQc, conj_airyPQc, Complex.conj_I, Complex.conj_conj]
  ring

/-- **Hermite-Biehler**: all roots of `Q + iP` lie in the open lower half plane. -/
def AiryPQHB (P Q : ℝ[X]) : Prop :=
  ∀ z : ℂ, airyPQc Q z + I * airyPQc P z = 0 → z.im < 0

lemma AiryPQHB.F_ne_zero {P Q : ℝ[X]} (h : AiryPQHB P Q) : airyPQF P Q ≠ 0 := by
  intro h0
  have := h 0 (by rw [← airyPQF_eval, h0]; simp)
  simp at this

lemma AiryPQHB.roots_im {P Q : ℝ[X]} (h : AiryPQHB P Q) {w : ℂ} (hw : w ∈ (airyPQF P Q).roots) : w.im < 0 := by
  have := (Polynomial.mem_roots h.F_ne_zero).mp hw
  exact h w (by rw [← airyPQF_eval]; exact this)

/-- The two coefficient values cannot vanish together at a real point. -/
lemma airyPQHB_ne_zero_real {P Q : ℝ[X]} (h : AiryPQHB P Q) (x : ℝ) :
    ¬ (Q.eval x = 0 ∧ P.eval x = 0) := by
  rintro ⟨h1, h2⟩
  have := h (x : ℂ) (by rw [airyPQc_ofReal, airyPQc_ofReal, h1, h2]; simp)
  simp at this

/-- Factorwise: `‖z̄ - w‖ ≤ ‖z - w‖` for `Im z ≥ 0`, `Im w < 0`. -/
lemma airyPQ_norm_conj_sub_le {z w : ℂ} (hz : 0 ≤ z.im) (hw : w.im < 0) :
    ‖(starRingEnd ℂ) z - w‖ ≤ ‖z - w‖ := by
  have h : ‖(starRingEnd ℂ) z - w‖ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    rw [sq_norm_eq, sq_norm_eq]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_nonneg hz (neg_nonneg.mpr hw.le)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma airyPQ_prod_norm_le {z : ℂ} (hz : 0 ≤ z.im) (s : Multiset ℂ) (hs : ∀ w ∈ s, w.im < 0) :
    ‖(s.map ((starRingEnd ℂ) z - ·)).prod‖ ≤ ‖(s.map (z - ·)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_mul (airyPQ_norm_conj_sub_le hz (hs a (Multiset.mem_cons_self _ _)))
      (ih fun w hw => hs w (Multiset.mem_cons_of_mem hw)) (norm_nonneg _) (norm_nonneg _)

/-- **Herglotz inequality**: for `Im z ≥ 0`, `‖Q(z) - iP(z)‖ ≤ ‖Q(z) + iP(z)‖`. -/
theorem airyPQHB_norm_le {P Q : ℝ[X]} (h : AiryPQHB P Q) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖airyPQc Q z - I * airyPQc P z‖ ≤ ‖airyPQc Q z + I * airyPQc P z‖ := by
  have hs := IsAlgClosed.splits (airyPQF P Q)
  rw [← airyPQF_conj, Complex.norm_conj, ← airyPQF_eval]
  rw [hs.eval_eq_prod_roots, hs.eval_eq_prod_roots, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (airyPQ_prod_norm_le hz _ fun w hw => h.roots_im hw) (norm_nonneg _)

lemma airyPQ_sum_im_nonpos (x : ℝ) (s : Multiset ℂ) (hs : ∀ w ∈ s, w.im < 0) :
    ((s.map fun w => 1 / ((x : ℂ) - w)).sum).im ≤ 0 ∧
      (s ≠ 0 → ((s.map fun w => 1 / ((x : ℂ) - w)).sum).im < 0) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hs w (Multiset.mem_cons_of_mem hw)
    have hterm : (1 / ((x : ℂ) - a)).im < 0 := by
      rw [one_div, Complex.inv_im]
      have : 0 < Complex.normSq ((x : ℂ) - a) := by
        rw [Complex.normSq_pos]
        intro h0
        have := congrArg Complex.im h0
        simp at this
        linarith
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
      have : (a.im) / Complex.normSq ((x : ℂ) - a) < 0 := div_neg_of_neg_of_pos ha this
      simpa using this
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
    exact ⟨by linarith, fun _ => by linarith⟩

/-- The real polynomial `P Q' - Q P'`. -/
noncomputable def airyPQWr (P Q : ℝ[X]) : ℝ[X] := P * derivative Q - Q * derivative P

/-- **Positive Wronskian of a Hermite-Biehler pair**: `(P Q' - Q P')(x) ≥ 0` for real `x`;
strictly positive if `Q + iP` has a root (is not constant). -/
theorem airyPQHB_wronskian {P Q : ℝ[X]} (h : AiryPQHB P Q) (x : ℝ) :
    0 ≤ (airyPQWr P Q).eval x ∧ ((airyPQF P Q).roots ≠ 0 → 0 < (airyPQWr P Q).eval x) := by
  have hs := IsAlgClosed.splits (airyPQF P Q)
  set c0 := (airyPQF P Q).eval (x : ℂ) with hc0
  set c1 := (airyPQF P Q).derivative.eval (x : ℂ) with hc1
  have hc0re : c0.re = Q.eval x := by
    rw [hc0, airyPQF_eval, airyPQc_ofReal, airyPQc_ofReal]; simp
  have hc0im : c0.im = P.eval x := by
    rw [hc0, airyPQF_eval, airyPQc_ofReal, airyPQc_ofReal]; simp
  have hc1re : c1.re = (derivative Q).eval x := by
    rw [hc1, airyPQF_derivative_eval, airyPQc_ofReal, airyPQc_ofReal]; simp
  have hc1im : c1.im = (derivative P).eval x := by
    rw [hc1, airyPQF_derivative_eval, airyPQc_ofReal, airyPQc_ofReal]; simp
  have hc0ne : c0 ≠ 0 := by
    intro h0
    have := h (x : ℂ) (by rw [← airyPQF_eval]; exact h0)
    simp at this
  have hns : 0 < Complex.normSq c0 := Complex.normSq_pos.mpr hc0ne
  have hdiv := hs.eval_derivative_div_eval_of_ne_zero hc0ne
  obtain ⟨hn1, hn2⟩ := airyPQ_sum_im_nonpos x (airyPQF P Q).roots fun w hw => h.roots_im hw
  have him : (c1 / c0).im = (c1.im * c0.re - c1.re * c0.im) / Complex.normSq c0 := by
    rw [Complex.div_im]; ring
  have hW : (airyPQWr P Q).eval x = -(Complex.normSq c0 * (c1 / c0).im) := by
    rw [him]
    have : Complex.normSq c0 * ((c1.im * c0.re - c1.re * c0.im) / Complex.normSq c0) =
        c1.im * c0.re - c1.re * c0.im := by field_simp
    rw [this, hc0re, hc0im, hc1re, hc1im]
    simp [airyPQWr]
    ring
  rw [hdiv] at hW
  refine ⟨?_, fun hr => ?_⟩
  · rw [hW]; nlinarith
  · rw [hW]
    have := hn2 hr
    nlinarith

lemma airyPQHB_wronskian_nonneg {P Q : ℝ[X]} (h : AiryPQHB P Q) (x : ℝ) :
    0 ≤ P.eval x * (derivative Q).eval x - Q.eval x * (derivative P).eval x := by
  have := (airyPQHB_wronskian h x).1
  simpa [airyPQWr] using this

/-- info: 'FormalResearch.Special.airyPQHB_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQHB_norm_le

/-- info: 'FormalResearch.Special.airyPQHB_wronskian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQHB_wronskian

end FormalResearch.Special
