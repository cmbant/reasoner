module

public import FormalResearch.Special.AiryPolySample

/-!
# Special cases and the positivity consequence of the Airy quadrature for Hermite-Biehler pairs

Consequences of `airyPQ_hasSum_unc` (`AiryPolySample`) used by the soft-edge notes (`SOFT_EDGE_THEOREMS.md` Lemmas 4.4, 4.6, Theorems 4.5, 4.7):

* `airyPQ_C_N`, `airyPQ_C_D`: for constant polynomials `N`, `D` are `airyNC`, `airyDC` of `AiryCft2ComboAlg` (the constant case is a special case);
  `airyPQHB_C` : a constant pair `(p, q) ≠ (0, 0)` is Hermite-Biehler, so `airyPQ_hasSum_unc` contains `airyNC_hasSum_unc`, `airyClark_hasSum_unc`
  (it does not replace them: the older theorems keep their stated form).
* `airyPQHB_lemma44`: **Lemma 4.4** of `SOFT_EDGE_THEOREMS.md`: `P = u - b_r`, `Q = -b_i`, `b_i > 0`
  (`Q + iP = i(u - b̄)`, root `b̄ = b_r - i b_i`), `D = (u - b_r)² + b_i - b_i² u` (`airyPQD_lemma44`), so for every `f` of the class
  `∫ f = Σ_{N(t)=0} D(t) f(t)/N'(t)²` (`airyPQ_lemma44_hasSum`).
* `airyPQ_nonneg_zeros_vanish`: **the positivity step of Theorems 4.5, 4.7** (and of Theorem 1.2/Theorem B of the notes): `f` of the class, real on `ℝ`, with
  `f(t) ≥ 0` at every zero `t` of `N` and `∫ f ≤ 0` vanishes at every zero of `N` (the weights `D/N'²` are positive and real).

Not formalised: the rest of the proof of Theorem 4.7 (the extremal `F = N²/Π(u - t_j)` is entire, `F ≍ |u|^{-3/2}` on the band, then the polynomial
`f Π(u - t_j)/N²` is bounded on the good circles — for which the lower bound of `airyPQ_good_circle_kappa` is the input — hence a polynomial; and its
constancy needs the non-integrability of `(polynomial)·N²` on the band, the analogue of `airy_poly_sq_not_integrable` for `N`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

/-! ### Constant coefficients -/

lemma airyPQ_C_N (p q : ℝ) (z : ℂ) : airyPQN (Polynomial.C p) (Polynomial.C q) z = airyNC p q z := by
  simp [airyPQN, airyNC, airyPQc_C]

lemma airyPQ_C_D (p q : ℝ) (z : ℂ) : airyPQD (Polynomial.C p) (Polynomial.C q) z = airyDC p q z := by
  simp [airyPQD, airyDC, airyPQc_C, airyPQc_zero]
  ring

/-- A constant pair `(p, q) ≠ (0, 0)` is Hermite-Biehler (`Q + iP` is a nonzero constant, no roots). -/
lemma airyPQHB_C (p q : ℝ) (h : p ≠ 0 ∨ q ≠ 0) : AiryPQHB (Polynomial.C p) (Polynomial.C q) := by
  intro z hz
  exfalso
  rw [airyPQc_C, airyPQc_C] at hz
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp at h1 h2
  rcases h with h | h
  · exact h h2
  · exact h h1

/-! ### Lemma 4.4 -/

lemma airyPQHB_lemma44 (b_r b_i : ℝ) (hb : 0 < b_i) :
    AiryPQHB (Polynomial.X - Polynomial.C b_r) (Polynomial.C (-b_i)) := by
  intro z hz
  have e : airyPQc (Polynomial.X - Polynomial.C b_r) z = z - (b_r : ℂ) := by
    simp [airyPQc]
  rw [e, airyPQc_C] at hz
  have him := congrArg Complex.im hz
  have hre := congrArg Complex.re hz
  simp at him hre
  linarith

lemma airyPQD_lemma44 (b_r b_i : ℝ) (z : ℂ) :
    airyPQD (Polynomial.X - Polynomial.C b_r) (Polynomial.C (-b_i)) z =
      (z - (b_r : ℂ)) ^ 2 + (b_i : ℂ) - (b_i : ℂ) ^ 2 * z := by
  have e : airyPQc (Polynomial.X - Polynomial.C b_r) z = z - (b_r : ℂ) := by simp [airyPQc]
  have e' : airyPQc (derivative (Polynomial.X - Polynomial.C b_r)) z = 1 := by simp [airyPQc]
  have e'' : airyPQc (derivative (Polynomial.C (-b_i))) z = 0 := by simp [airyPQc]
  unfold airyPQD
  rw [e, e', e'', airyPQc_C]
  push_cast
  ring

/-- **Lemma 4.4 of `SOFT_EDGE_THEOREMS.md`** (rank-one-extension Airy summation): `b_r ∈ ℝ`, `b_i > 0`,
`N = (u - b_r) Ai - b_i Ai'`, `D = (u - b_r)² + b_i - b_i² u`: `∫ f = Σ_{N(t)=0} D(t) f(t)/N'(t)²` (absolutely convergent). -/
theorem airyPQ_lemma44_hasSum (b_r b_i : ℝ) (hb : 0 < b_i) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb' : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun z : {z : ℂ // airyPQN (Polynomial.X - Polynomial.C b_r) (Polynomial.C (-b_i)) z = 0} =>
        f z * (((z : ℂ) - (b_r : ℂ)) ^ 2 + (b_i : ℂ) - (b_i : ℂ) ^ 2 * z) /
          airyPQN' (Polynomial.X - Polynomial.C b_r) (Polynomial.C (-b_i)) z ^ 2)
      (∫ x : ℝ, f (x : ℂ)) := by
  have hQ : Polynomial.C (-b_i) ≠ (0 : ℝ[X]) := by
    simpa using hb.ne'
  have h := airyPQ_hasSum_unc (airyPQHB_lemma44 b_r b_i hb) hQ hf hfi hC hb'
  convert h using 2 with z
  rw [airyPQD_lemma44]
  ring

/-! ### Positivity: nonnegative at the zeros forces vanishing -/

lemma airyPQN'_ofReal (P Q : ℝ[X]) (x : ℝ) :
    airyPQN' P Q (x : ℂ) = (((derivative P).eval x * airyAi x + (P.eval x + (derivative Q).eval x) * airyAi' x +
      x * Q.eval x * airyAi x : ℝ) : ℂ) := by
  unfold airyPQN'
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal]
  simp only [airyPQc_ofReal]
  push_cast; ring

/-- **Positivity step** (Theorems 4.5, 4.7 of `SOFT_EDGE_THEOREMS.md`): if `f` is of the class, real on `ℝ`, `f(t) ≥ 0` at every zero `t` of
the Hermite-Biehler combination `N` and `∫ f ≤ 0`, then `f` vanishes at every zero of `N`. -/
theorem airyPQ_nonneg_zeros_vanish {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hnn : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → 0 ≤ (f (x : ℂ)).re)
    (hint : (∫ x : ℝ, f (x : ℂ)).re ≤ 0) :
    ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → f (x : ℂ) = 0 := by
  have h := airyPQ_hasSum_unc hHB hQ hf hfi hC hb
  have hre := Complex.hasSum_re h
  -- the real weights
  have hw : ∀ z : {z : ℂ // airyPQN P Q z = 0},
      (f z * (airyPQD P Q z / airyPQN' P Q z ^ 2)).re =
        (f z).re * (airyPQDr P Q z.1.re / ((airyPQN' P Q (z.1.re : ℂ)).re) ^ 2) := by
    intro z
    have hzeq := airyPQ_zero_eq_ofReal hHB z.2
    have e1 : airyPQD P Q z.1 = ((airyPQDr P Q z.1.re : ℝ) : ℂ) :=
      (congrArg (airyPQD P Q) hzeq).trans (airyPQD_ofReal P Q z.1.re)
    have e2 : airyPQN' P Q z.1 = (((airyPQN' P Q (z.1.re : ℂ)).re : ℝ) : ℂ) := by
      have := congrArg (airyPQN' P Q) hzeq
      rw [this, airyPQN'_ofReal, Complex.ofReal_re]
    rw [e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.re_mul_ofReal]
  have hpos : ∀ z : {z : ℂ // airyPQN P Q z = 0}, 0 < airyPQDr P Q z.1.re / ((airyPQN' P Q (z.1.re : ℂ)).re) ^ 2 := by
    intro z
    have hz0 := airyPQ_zero_ofReal hHB z
    obtain ⟨hD, hd⟩ := airyPQ_zero_weight_pos hHB hQ hz0
    have : (airyPQN' P Q (z.1.re : ℂ)).re ≠ 0 := by
      intro h0
      apply hd
      rw [airyPQN'_ofReal] at h0 ⊢
      rw [Complex.ofReal_re] at h0
      rw [h0]; simp
    positivity
  intro x hx
  have hxz : airyPQN P Q ((x : ℂ)) = 0 := hx
  set z : {z : ℂ // airyPQN P Q z = 0} := ⟨(x : ℂ), hx⟩ with hzdef
  have hnonneg : ∀ w : {z : ℂ // airyPQN P Q z = 0}, 0 ≤ (f w * (airyPQD P Q w / airyPQN' P Q w ^ 2)).re := by
    intro w
    rw [hw]
    have := hnn w.1.re (airyPQ_zero_ofReal hHB w)
    have hzeq := airyPQ_zero_eq_ofReal hHB w.2
    rw [← hzeq] at this
    exact mul_nonneg this (hpos w).le
  have hle := le_hasSum hre z (fun w _ => hnonneg w)
  have hz_re : (f (x : ℂ)).re * (airyPQDr P Q x / ((airyPQN' P Q (x : ℂ)).re) ^ 2) ≤ 0 := by
    have h1 := hw z
    have e : (z.1.re) = x := by simp [hzdef]
    have hh : (f z * (airyPQD P Q z / airyPQN' P Q z ^ 2)).re ≤ 0 := hle.trans hint
    rw [h1] at hh
    simpa [hzdef] using hh
  have hp := hpos z
  have hp' : 0 < airyPQDr P Q x / ((airyPQN' P Q (x : ℂ)).re) ^ 2 := by simpa [hzdef] using hp
  have hr0 : (f (x : ℂ)).re ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos hcon hp'
    linarith
  have hr1 : (f (x : ℂ)).re = 0 := le_antisymm hr0 (hnn x hx)
  exact Complex.ext hr1 (hreal x)

/-- info: 'FormalResearch.Special.airyPQ_lemma44_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_lemma44_hasSum

/-- info: 'FormalResearch.Special.airyPQ_nonneg_zeros_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_nonneg_zeros_vanish

end FormalResearch.Special
