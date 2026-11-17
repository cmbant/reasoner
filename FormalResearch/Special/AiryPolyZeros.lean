module

public import FormalResearch.Special.AiryPolyHB
public import FormalResearch.Special.AiryPolyCircle
public import FormalResearch.Special.AiryCft2ComboZeros

/-!
# The zeros of `N = P·Ai + Q·Ai'` for a Hermite-Biehler pair `(P, Q)`

Formalises `SOFT_EDGE_THEOREMS.md` Lemma 4.6 (first sentence): for real polynomials `P`, `Q ≠ 0` with `Q + iP` having all its roots in the
open lower half plane (`AiryPQHB`), **`N` has only real, simple zeros and `D > 0` at each of them**.  (The note proves it with the Prüfer angle
`Λ = ϑ - Φ`, `Λ' = D/(P²+Q²)`; here, as in `AiryCft2ComboZeros` for constants, it follows from the Mittag-Leffler expansion of `m = Ai'/Ai`:
no Prüfer or de Branges theory is used.)

* `airyPQ_zero_im`: every zero of `N` in `ℂ` is real.  At a zero with `Ai(z) ≠ 0` and `Im z > 0`, `Q(z) m(z) = -P(z)` gives
  `|Q|² Im m = Im(Q P̄) ≥ 0` (Herglotz inequality, `airyPQHB_norm_le`), against `Im m(z) = -Im z Σ|z - a_n|^{-2} < 0`.
* `airyPQ_zero_weight_pos`: at a real zero `x`: `D(x) = P(P+Q') - Q(P'+xQ) > 0` and `N'(x) ≠ 0`.  Two cases: `Ai(x) ≠ 0` (then `Q(x) ≠ 0`,
  `D = Q²(m² - x) + (PQ' - QP') = Q² Σ (x-a_n)^{-2} + (PQ'-QP') > 0` by the positive Wronskian) and `Ai(x) = 0` (then `Q(x) = 0 ≠ P(x)`,
  `D = P² + PQ' > 0`, strict positivity of the Wronskian since `Q` is not constant).
* `airyPQ_zeros_finite`: finitely many zeros in every disc (a nonzero entire function; `N(i) ≠ 0`);
  `airyPQ_no_zero_sector`: no zero with `‖u‖ ≥ T`, `Re u ≥ -‖u‖/2` (the sector bound of `AiryPolySector`), hence all but finitely many real zeros are negative.
* `airyPQ_injOn_far`: **at most one zero of `N` per gap of the zeros of `Ai` beyond the real roots of `Q`**: for zeros `t₁, t₂ ≤ -T₀` (`T₀` beyond
  the real roots of `Q`) with the same index `airyNIdx` one has `t₁ = t₂`: `m = Ai'/Ai` is strictly decreasing on the gap, `-P/Q` has derivative
  `(PQ'-QP')/Q² ≥ 0`.

All proved.  Not formalised: the monotonicity `Λ' > 0` of the Prüfer angle, the existence of a zero of `N` in each gap of `Ai` (only the
at-most-one half, `airyPQ_injOn_far`), and `Q = 0` for the weight statements (`airyPQ_zero_weight_pos` needs `Q ≠ 0`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

/-! ### `Im (Ai'/Ai) < 0` in the upper half plane -/

lemma airyPQ_logDeriv_im_neg {z : ℂ} (hz : 0 < z.im) (hA : airyAiC z ≠ 0) :
    (deriv airyAiC z / airyAiC z).im < 0 := by
  have hs := airyAiC_logDeriv_mittagLeffler hA
  have hs' := Complex.hasSum_im hs
  have e0 : (deriv airyAiC 0 / airyAiC 0).im = 0 := by
    have h1 : deriv airyAiC ((0 : ℝ) : ℂ) = (airyAi' 0 : ℂ) := deriv_airyAiC_ofReal 0
    have h2 : airyAiC ((0 : ℝ) : ℂ) = (airyAi 0 : ℂ) := airyAiC_ofReal 0
    simp only [Complex.ofReal_zero] at h1 h2
    rw [h1, h2, ← Complex.ofReal_div]; simp
  have hterm : ∀ n : ℕ, (1 / (z - (airyZero (n + 1) : ℂ)) + 1 / (airyZero (n + 1) : ℂ)).im =
      -(z.im / Complex.normSq (z - (airyZero (n + 1) : ℂ))) := by
    intro n
    rw [Complex.add_im, one_div, one_div, Complex.inv_im, ← Complex.ofReal_inv, Complex.ofReal_im]
    simp
    ring
  simp_rw [hterm] at hs'
  rw [Complex.sub_im, e0, sub_zero] at hs'
  have hpos : ∀ n : ℕ, 0 ≤ z.im / Complex.normSq (z - (airyZero (n + 1) : ℂ)) := fun n =>
    div_nonneg hz.le (Complex.normSq_nonneg _)
  have h0 : 0 < z.im / Complex.normSq (z - (airyZero (0 + 1) : ℂ)) := by
    apply div_pos hz
    rw [Complex.normSq_pos]
    intro h0
    have := congrArg Complex.im (sub_eq_zero.mp h0)
    simp at this
    linarith
  have hs2 : HasSum (fun n : ℕ => z.im / Complex.normSq (z - (airyZero (n + 1) : ℂ)))
      (-(deriv airyAiC z / airyAiC z).im) := by
    have := hs'.neg
    simpa using this
  have := le_hasSum hs2 0 (fun j _ => hpos j)
  linarith

/-! ### Zeros are real -/

lemma airyPQ_zero_im_pos {P Q : ℝ[X]} (hHB : AiryPQHB P Q) {z : ℂ} (hz : 0 < z.im) (h : airyPQN P Q z = 0) :
    False := by
  by_cases hA : airyAiC z = 0
  · obtain ⟨n, -, rfl⟩ := (airyAiC_eq_zero_iff z).mp hA
    simp at hz
  · set m := deriv airyAiC z / airyAiC z with hm
    have hm' := airyPQ_logDeriv_im_neg hz hA
    have hQP : airyPQc Q z * m = -airyPQc P z := by
      have : airyPQc P z * airyAiC z + airyPQc Q z * deriv airyAiC z = 0 := h
      rw [hm]; field_simp; linear_combination this
    have hher := airyPQHB_norm_le hHB hz.le
    set a := airyPQc Q z with ha
    set b := airyPQc P z with hb
    -- a1 b2 ≤ a2 b1  (Im (a b̄) ≥ 0)
    have hcmp : a.re * b.im ≤ a.im * b.re := by
      have h2 : ‖a - I * b‖ ^ 2 ≤ ‖a + I * b‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hher 2
      rw [sq_norm_eq, sq_norm_eq] at h2
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im] at h2
      nlinarith
    -- |a|² Im m = Im (a b̄)
    have hQ0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hQP
      have hb0 : b = 0 := by linear_combination hQP
      have : a + I * b = 0 := by rw [h0, hb0]; simp
      have := hHB z this
      linarith
    have hnq : 0 < Complex.normSq a := Complex.normSq_pos.mpr hQ0
    have key : Complex.normSq a * m.im = a.im * b.re - a.re * b.im := by
      have h1 : a * m = -b := hQP
      have hre := congrArg Complex.re h1
      have him := congrArg Complex.im h1
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im] at hre him
      rw [Complex.normSq_apply]
      linear_combination a.re * him - a.im * hre
    have : 0 ≤ Complex.normSq a * m.im := by rw [key]; linarith
    nlinarith

/-- **Every zero of `N = P Ai + Q Ai'` is real** (Hermite-Biehler `(P, Q)`). -/
theorem airyPQ_zero_im {P Q : ℝ[X]} (hHB : AiryPQHB P Q) {z : ℂ} (h : airyPQN P Q z = 0) : z.im = 0 := by
  rcases lt_trichotomy z.im 0 with hlt | h0 | hgt
  · exfalso
    have hc : airyPQN P Q ((starRingEnd ℂ) z) = 0 := by rw [← conj_airyPQN, h, map_zero]
    exact airyPQ_zero_im_pos hHB (by simpa using hlt) hc
  · exact h0
  · exact (airyPQ_zero_im_pos hHB hgt h).elim

lemma airyPQ_zero_eq_ofReal {P Q : ℝ[X]} (hHB : AiryPQHB P Q) {z : ℂ} (h : airyPQN P Q z = 0) :
    z = ((z.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [airyPQ_zero_im hHB h])

/-! ### Real zeros: positive weights, simplicity -/

/-- The real value of `D` on `ℝ`. -/
noncomputable def airyPQDr (P Q : ℝ[X]) (x : ℝ) : ℝ :=
  P.eval x * (P.eval x + (derivative Q).eval x) - Q.eval x * ((derivative P).eval x + x * Q.eval x)

lemma airyPQD_ofReal (P Q : ℝ[X]) (x : ℝ) : airyPQD P Q (x : ℂ) = ((airyPQDr P Q x : ℝ) : ℂ) := by
  unfold airyPQD airyPQDr
  simp only [airyPQc_ofReal]
  push_cast; ring

lemma airyPQN_ofReal (P Q : ℝ[X]) (x : ℝ) :
    airyPQN P Q (x : ℂ) = ((P.eval x * airyAi x + Q.eval x * airyAi' x : ℝ) : ℂ) := by
  unfold airyPQN
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal, airyPQc_ofReal, airyPQc_ofReal]
  push_cast; ring

lemma airyPQ_nonconst_of_root {P Q : ℝ[X]} (hQ : Q ≠ 0) {x : ℝ} (hx : Q.eval x = 0) :
    (airyPQF P Q).roots ≠ 0 := by
  intro h0
  have hs := IsAlgClosed.splits (airyPQF P Q)
  have hdeg : (airyPQF P Q).natDegree = 0 := by rw [hs.natDegree_eq_card_roots, h0]; simp
  have hd0 : (airyPQF P Q).derivative = 0 := Polynomial.derivative_of_natDegree_zero hdeg
  have hQ' : derivative Q = 0 := by
    apply Polynomial.funext
    intro r
    have := airyPQF_derivative_eval P Q (r : ℂ)
    rw [hd0, Polynomial.eval_zero, airyPQc_ofReal, airyPQc_ofReal] at this
    have := congrArg Complex.re this
    simpa using this.symm
  have hQc := Polynomial.eq_C_of_derivative_eq_zero hQ'
  apply hQ
  rw [hQc] at hx ⊢
  simp only [Polynomial.eval_C] at hx
  rw [hx]; simp

/-- **Positive weights and simple zeros.** -/
theorem airyPQ_zero_weight_pos {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {x : ℝ}
    (h : airyPQN P Q (x : ℂ) = 0) : 0 < airyPQDr P Q x ∧ airyPQN' P Q (x : ℂ) ≠ 0 := by
  rw [airyPQN_ofReal, Complex.ofReal_eq_zero] at h
  have hW := airyPQHB_wronskian hHB x
  have hDW : airyPQDr P Q x = P.eval x ^ 2 - x * Q.eval x ^ 2 +
      (P.eval x * (derivative Q).eval x - Q.eval x * (derivative P).eval x) := by
    unfold airyPQDr; ring
  have hWe : (airyPQWr P Q).eval x = P.eval x * (derivative Q).eval x - Q.eval x * (derivative P).eval x := by
    simp [airyPQWr]
  have hD : 0 < airyPQDr P Q x := by
    by_cases hAx : airyAi x = 0
    · have hQx : Q.eval x = 0 := by
        rw [hAx, mul_zero, zero_add] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact h1
        · exact absurd hAx (airyAi_ne_zero_of_deriv_zero h1)
      have hPx : P.eval x ≠ 0 := fun hP => airyPQHB_ne_zero_real hHB x ⟨hQx, hP⟩
      have hpos := hW.2 (airyPQ_nonconst_of_root hQ hQx)
      rw [hWe] at hpos
      rw [hQx] at hpos
      rw [hDW, hQx]
      have : 0 < P.eval x ^ 2 := by positivity
      nlinarith
    · have hQx : Q.eval x ≠ 0 := by
        intro hq
        rw [hq, zero_mul, add_zero] at h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact airyPQHB_ne_zero_real hHB x ⟨hq, h1⟩
        · exact hAx h1
      have hQ2 : 0 < Q.eval x ^ 2 := by positivity
      have hm : airyAi' x = -(P.eval x / Q.eval x) * airyAi x := by
        field_simp; linarith
      have hs := airyAi_sq_series_real hAx
      have hpos : 0 < (airyAi' x / airyAi x) ^ 2 - x := by
        have h0 := le_hasSum hs 0 (fun j _ => by positivity)
        have : 0 < ((x - airyZero (0 + 1)) ^ 2)⁻¹ := by
          have : x - airyZero (0 + 1) ≠ 0 := by
            intro h1
            have hx : x = airyZero 1 := by linarith
            rw [hx, airyAi_airyZero] at hAx
            exact hAx rfl
          positivity
        linarith
      have hdiv : airyAi' x / airyAi x = -(P.eval x / Q.eval x) := by
        rw [hm]; field_simp
      rw [hdiv] at hpos
      have hD0 : 0 < P.eval x ^ 2 - x * Q.eval x ^ 2 := by
        have : (-(P.eval x / Q.eval x)) ^ 2 = P.eval x ^ 2 / Q.eval x ^ 2 := by ring
        rw [this] at hpos
        have h2 := mul_pos hpos hQ2
        have e : (P.eval x ^ 2 / Q.eval x ^ 2 - x) * Q.eval x ^ 2 = P.eval x ^ 2 - x * Q.eval x ^ 2 := by
          field_simp
        linarith
      rw [hDW]
      linarith [hW.1, hWe]
  refine ⟨hD, ?_⟩
  intro hN'
  have := airyPQ_mul_at_zero (P := P) (Q := Q) (t := (x : ℂ)) (by rw [airyPQN_ofReal, h]; simp)
  rw [hN', zero_mul, airyPQD_ofReal] at this
  have hpi : ((1 / π : ℝ) : ℂ) ≠ 0 := by
    have : (1 / π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hne : ((airyPQDr P Q x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have h0 : ((airyPQDr P Q x : ℝ) : ℂ) * ((1 / π : ℝ) : ℂ) = 0 := by linear_combination this
  exact mul_ne_zero hne hpi h0

/-! ### Finiteness -/

/-- A nonzero entire function has finitely many zeros in every disc. -/
theorem airy_entire_zeros_finite {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (R : ℝ) :
    {z : ℂ | f z = 0 ∧ ‖z‖ ≤ R}.Finite := by
  by_contra hinf
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  obtain ⟨z₀, -, hz₀⟩ := Set.Infinite.exists_accPt_of_subset_isCompact (s := {z : ℂ | f z = 0 ∧ ‖z‖ ≤ R}) hinf hK
    (fun z hz => by simpa using hz.2)
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz₀
    exact hz₀.mono fun z hz => hz.1
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ z₀) hfreq
  obtain ⟨z1, hz1⟩ := hne
  exact hz1 (this (Set.mem_univ z1))

theorem airyPQ_zeros_finite {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (R : ℝ) :
    {z : ℂ | airyPQN P Q z = 0 ∧ ‖z‖ ≤ R}.Finite := by
  refine airy_entire_zeros_finite (differentiable_airyPQN P Q) ⟨I, fun h => ?_⟩ R
  have := airyPQ_zero_im hHB h
  simp at this

/-- **No zeros in the sector `Re u ≥ -‖u‖/2` for large `‖u‖`.** -/
theorem airyPQ_no_zero_sector (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ u : ℂ, T ≤ ‖u‖ → -(‖u‖ / 2) ≤ u.re → airyPQN P Q u ≠ 0 := by
  obtain ⟨T, hT1, hT⟩ := airyPQ_dominance P Q
  refine ⟨max T 10, le_trans hT1 (le_max_left _ _), fun u hu hre h0 => ?_⟩
  have hTu : T ≤ ‖u‖ := (le_max_left _ _).trans hu
  have h10 : 10 ≤ ‖u‖ := (le_max_right _ _).trans hu
  obtain ⟨hdP, hdQ⟩ := hT u hTu
  have hsr : 0 < √‖u‖ := Real.sqrt_pos.mpr (by linarith)
  have hdom' : 16 * ‖airyPQc Q u‖ * √‖u‖ ≤ ‖airyPQc P u‖ ∨ 16 * ‖airyPQc P u‖ ≤ ‖airyPQc Q u‖ * √‖u‖ := by
    rcases airyPQ_domP_or_domQ P Q hPQ with h | h
    · exact Or.inl (hdP h).1
    · exact Or.inr (hdQ h).1
  have hmax : 0 < max ‖airyPQc P u‖ (‖airyPQc Q u‖ * √‖u‖) := by
    rcases airyPQ_domP_or_domQ P Q hPQ with h | h
    · exact lt_of_lt_of_le (hdP h).2.2 (le_max_left _ _)
    · exact lt_of_lt_of_le (mul_pos (hdQ h).2.2 hsr) (le_max_right _ _)
  have := airyAB_sector_ge (airyPQc P u) (airyPQc Q u) hre h10 hdom'
  have hN : airyPQc P u * airyAiC u + airyPQc Q u * deriv airyAiC u = 0 := h0
  rw [hN, norm_zero] at this
  have hen := airyEnv_pos u
  have : 0 < max ‖airyPQc P u‖ (‖airyPQc Q u‖ * √‖u‖) ^ 2 * airyEnv u / (16 * π * √‖u‖) := by positivity
  linarith

/-! ### At most one zero per gap beyond the real roots of `Q` -/

/-- `Q` has no real root `≤ -T₀` for some `T₀ ≥ 1`. -/
lemma airyPQ_far_ex {Q : ℝ[X]} (hQ : Q ≠ 0) : ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, t ≤ -T₀ → Q.eval t ≠ 0 := by
  obtain ⟨T, hT1, hT⟩ := airyPQ_lower_ex Q
  refine ⟨T, hT1, fun t ht h0 => ?_⟩
  have := (hT (t : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs]; linarith [neg_abs_le t]) hQ).2
  rw [airyPQc_ofReal, h0] at this
  simp at this

lemma airyPQ_logDeriv_at_zero_real {P Q : ℝ[X]} {t : ℝ} (hQt : Q.eval t ≠ 0)
    (h : airyPQN P Q (t : ℂ) = 0) : airyAi' t / airyAi t = -(P.eval t / Q.eval t) := by
  rw [airyPQN_ofReal, Complex.ofReal_eq_zero] at h
  have hAx : airyAi t ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_add] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact hQt h1
    · exact airyAi_ne_zero_of_deriv_zero h1 h0
  field_simp
  linarith

/-- **At most one zero of `N` per gap of `Ai`, beyond the real roots of `Q`.** -/
theorem airyPQ_injOn_far {P Q : ℝ[X]} (hHB : AiryPQHB P Q) {T₀ : ℝ} (hT₀ : ∀ t : ℝ, t ≤ -T₀ → Q.eval t ≠ 0)
    {t₁ t₂ : ℝ} (h₁t : t₁ ≤ -T₀) (h₂t : t₂ ≤ -T₀) (h₁ : airyPQN P Q (t₁ : ℂ) = 0) (h₂ : airyPQN P Q (t₂ : ℂ) = 0)
    (hidx : airyNIdx t₁ = airyNIdx t₂) : t₁ = t₂ := by
  have key : ∀ t₁ t₂ : ℝ, t₁ ≤ -T₀ → t₂ ≤ -T₀ → airyPQN P Q (t₁ : ℂ) = 0 → airyPQN P Q (t₂ : ℂ) = 0 →
      t₁ < t₂ → airyNIdx t₁ = airyNIdx t₂ → False := by
    intro t₁ t₂ h₁t h₂t h₁ h₂ hlt hidx
    have hA : ∀ t : ℝ, t ≤ -T₀ → airyPQN P Q (t : ℂ) = 0 → airyAi t ≠ 0 := by
      intro t ht hN h0
      rw [airyPQN_ofReal, Complex.ofReal_eq_zero, h0, mul_zero, zero_add] at hN
      rcases mul_eq_zero.mp hN with h1 | h1
      · exact hT₀ t ht h1
      · exact airyAi_ne_zero_of_deriv_zero h1 h0
    set n := airyNIdx t₂ with hn
    have hfree : ∀ x ∈ Icc t₁ t₂, airyAi x ≠ 0 := by
      intro x hx h0
      have hz : airyAiC (x : ℂ) = 0 := by rw [airyAiC_ofReal, h0]; simp
      obtain ⟨j, hj, hxj⟩ := (airyAiC_eq_zero_iff _).mp hz
      have hxj' : x = airyZero j := by exact_mod_cast hxj
      by_cases hjn : j ≤ n
      · have := (airyNIdx_gap (hA t₂ h₂t h₂) hj).1 hjn
        linarith [hx.2]
      · have := (airyNIdx_gap (hA t₁ h₁t h₁) hj).2 (by rw [hidx]; omega)
        linarith [hx.1]
    have hanti := airy_m_strictAntiOn hfree
    have e1 := airyPQ_logDeriv_at_zero_real (hT₀ t₁ h₁t) h₁
    have e2 := airyPQ_logDeriv_at_zero_real (hT₀ t₂ h₂t) h₂
    -- monotonicity of `-P/Q`
    have hQne : ∀ x ∈ Icc t₁ t₂, Q.eval x ≠ 0 := fun x hx => hT₀ x (hx.2.trans h₂t)
    have hd : ∀ x ∈ Icc t₁ t₂, HasDerivAt (fun x : ℝ => -(P.eval x / Q.eval x))
        ((P.eval x * (derivative Q).eval x - Q.eval x * (derivative P).eval x) / Q.eval x ^ 2) x := by
      intro x hx
      have := ((Polynomial.hasDerivAt P x).div (Polynomial.hasDerivAt Q x) (hQne x hx)).neg
      refine this.congr_deriv ?_
      field_simp
      ring
    have hmono : MonotoneOn (fun x : ℝ => -(P.eval x / Q.eval x)) (Icc t₁ t₂) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc t₁ t₂)
        (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_
      · intro x hx
        rw [interior_Icc] at hx
        exact (hd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' := Ioo_subset_Icc_self hx
        rw [(hd x hx').deriv]
        exact div_nonneg (airyPQHB_wronskian_nonneg hHB x) (sq_nonneg _)
    have hm := hanti ⟨le_refl t₁, hlt.le⟩ ⟨hlt.le, le_refl t₂⟩ hlt
    have hh := hmono ⟨le_refl t₁, hlt.le⟩ ⟨hlt.le, le_refl t₂⟩ hlt.le
    simp only at hm hh
    rw [e1, e2] at hm
    linarith
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact (key t₁ t₂ h₁t h₂t h₁ h₂ h hidx).elim
  · exact h
  · exact (key t₂ t₁ h₂t h₁t h₂ h₁ h hidx.symm).elim

/-- info: 'FormalResearch.Special.airyPQ_zero_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_zero_im

/-- info: 'FormalResearch.Special.airyPQ_zero_weight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_zero_weight_pos

/-- info: 'FormalResearch.Special.airyPQ_zeros_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_zeros_finite

/-- info: 'FormalResearch.Special.airyPQ_no_zero_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_no_zero_sector

/-- info: 'FormalResearch.Special.airyPQ_injOn_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_injOn_far

end FormalResearch.Special
