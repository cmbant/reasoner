module

public import FormalResearch.Special.AiryPolySector
public import FormalResearch.Special.AiryPolyAsym

/-!
# Good circles for `N = P·Ai + Q·Ai'` with real **polynomial** `P`, `Q`

Formalises `CFT/notes/general_theorems.tex` Lemma 1.0′ (E2$_N$) (= `SE5_FIVE_LEVEL_AIRY.md` §0.3) for every pair of real polynomials
`P, Q`, not both zero: with `W(u) = max(‖P(u)‖, ‖Q(u)‖ √‖u‖)` and `e(u) = exp(-(4/3) Re u^{3/2})`,

`airyPQ_good_circle`: there is `k₀` such that every `[k, k+1]`, `k ≥ k₀`, contains a radius `r` with, on the whole circle `|u| = r`,

* `W(u) > 0` and `W(u)² e(u) / (64 π √r) ≤ ‖N(u)‖²` (so `N ≠ 0` there);
* `‖M(u)/N(u) - i‖ e(u) ≤ 168 √π` for `Im u ≥ 0`, and `‖M(u)/N(u) + i‖ e(u) ≤ 168 √π` for `Im u ≤ 0`

(`M = P Bi + Q Bi'`).  The ratio constant is **universal** (independent of `P`, `Q`).  `airyPQ_good_circle_kappa` rewrites the first
bullet in the form of the note: `c r^{2κ} e(u) ≤ ‖N(u)‖²`, with `2κ = 2 deg P - 1/2` if `P` dominates (`deg Q < deg P`) and
`2κ = 2 deg Q + 1/2` otherwise (`κ = p - 1/4` resp. `q + 1/4` in the note).

Proof: the two terms `P(u) Ai` and `Q(u) Ai'` differ by the factor `√r` in size (`AiryPolyAsym`: dominance `16 ‖Q(u)‖ √r ≤ ‖P(u)‖` or
`16 ‖P(u)‖ ≤ ‖Q(u)‖ √r` on `‖u‖ ≥ T`), and the sector bounds of `AiryPolySector` apply with `a = P(u)`, `b = Q(u)`; the radii are
`(2/3) r^{3/2} = π/4 + mπ` (cosine dominant, `P` dominates) or `3π/4 + mπ` (sine dominant) — the same for every point of the circle;
the numerator is `AiryPolyAlg.airyPQ_sub_I_mul_sq_le`.

Numerical check (mpmath, 20 digits; `P = u + 0.3, Q = -1`; `P = 0.7, Q = u + 0.5`; `P = -0.64-0.41u+1.7u², Q = 0.83-2.96u-1.1u²+u³`;
`P = 0.4, Q = -1`; `P = 1, Q = u`; radii with `m ∈ {12, 30, 80}`, 121 angles on the upper half circle): the minimum of
`‖N‖² 64π√r/(W² e)` is `15.1` (proved `≥ 1`), and the maximum of `‖M/N - i‖ e` is `2.1` (proved `≤ 168√π ≈ 298`), the numerator computed from
`M - iN = 2ε̄(P Ai(ω²u) + Q ω² Ai'(ω²u))` (the direct difference `M/N - i` is not meaningful in double precision).  The constants are not optimised.

Not formalised: the explicit threshold `k₀` (it exists by `airyPQ_dominance`), uniformity of the constants in `(P, Q)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

/-- The size `W(u) = max(‖P(u)‖, ‖Q(u)‖ √‖u‖)` of the dominant term of `N(u)`. -/
noncomputable def airyPQW (P Q : ℝ[X]) (u : ℂ) : ℝ := max ‖airyPQc P u‖ (‖airyPQc Q u‖ * √‖u‖)

lemma airyPQW_nonneg (P Q : ℝ[X]) (u : ℂ) : 0 ≤ airyPQW P Q u :=
  (norm_nonneg _).trans (le_max_left _ _)

lemma airyPQ_ratio_le {a b e W r : ℝ} (hb : 0 < b) (he : 0 < e) (hsr : 0 < √r)
    (ha : a ^ 2 * e ≤ 441 * W ^ 2 / √r) (hb2 : W ^ 2 * e / (64 * π * √r) ≤ b ^ 2) (ha0 : 0 ≤ a) :
    a / b * e ≤ 168 * √π := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  have hpi := Real.pi_pos
  have hC : 0 ≤ 168 * √π * b := by positivity
  refine (pow_le_pow_iff_left₀ (by positivity) hC two_ne_zero).mp ?_
  have e1 : (a * e) ^ 2 = (a ^ 2 * e) * e := by ring
  have e2 : (168 * √π * b) ^ 2 = 28224 * π * b ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hpi.le]; ring
  rw [e1, e2]
  have h5 : (a ^ 2 * e) * e ≤ (441 * W ^ 2 / √r) * e := mul_le_mul_of_nonneg_right ha he.le
  have h6 : 28224 * π * (W ^ 2 * e / (64 * π * √r)) ≤ 28224 * π * b ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 (by positivity)
  have h7 : 28224 * π * (W ^ 2 * e / (64 * π * √r)) = (441 * W ^ 2 / √r) * e := by
    field_simp; ring
  linarith

lemma airyPQ_one_add_rpow_half_le {r : ℝ} (hr : 1 ≤ r) : (1 + r) ^ (1 / 2 : ℝ) ≤ 3 / 2 * √r := by
  have : (1 + r) ^ (1 / 2 : ℝ) = √(1 + r) := (Real.sqrt_eq_rpow _).symm
  rw [this]
  have : √(1 + r) ≤ √(2 * r) := Real.sqrt_le_sqrt (by linarith)
  refine this.trans ?_
  rw [Real.sqrt_mul (by norm_num)]
  have : √2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)

/-- The numerator bound in terms of `W`: for `Im u ≥ 0` and `‖u‖ = r ≥ 1`:
`‖M - iN‖² e ≤ 441 W² / √r`. -/
lemma airyPQ_num_le (P Q : ℝ[X]) {u : ℂ} (hu : 0 ≤ u.im) (hr : 1 ≤ ‖u‖) :
    ‖airyPQM P Q u - I * airyPQN P Q u‖ ^ 2 * airyEnv u ≤ 441 * airyPQW P Q u ^ 2 / √‖u‖ := by
  refine (airyPQ_sub_I_mul_sq_le P Q hu).trans ?_
  set r := ‖u‖ with hrdef
  set x := ‖airyPQc P u‖
  set y := ‖airyPQc Q u‖ * √r
  have hr0 : 0 < r := by linarith
  have hsr : 0 < √r := Real.sqrt_pos.mpr hr0
  set W := airyPQW P Q u with hW
  have hxW : x ≤ W := le_max_left _ _
  have hyW : y ≤ W := le_max_right _ _
  have hp1 : (1 + r) ^ (1 / 4 : ℝ) = (1 + r) ^ (-(1 / 4) : ℝ) * (1 + r) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h1r := airyPQ_one_add_rpow_half_le hr
  have hq0 : 0 < (1 + r) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hbound : 3 * x * (1 + r) ^ (-(1 / 4) : ℝ) + 5 * ‖airyPQc Q u‖ * (1 + r) ^ (1 / 4 : ℝ) ≤
      21 / 2 * W * (1 + r) ^ (-(1 / 4) : ℝ) := by
    rw [hp1]
    have : 5 * ‖airyPQc Q u‖ * ((1 + r) ^ (-(1 / 4) : ℝ) * (1 + r) ^ (1 / 2 : ℝ)) ≤
        5 * ‖airyPQc Q u‖ * ((1 + r) ^ (-(1 / 4) : ℝ) * (3 / 2 * √r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1r hq0.le) (by positivity)
    have e : 5 * ‖airyPQc Q u‖ * ((1 + r) ^ (-(1 / 4) : ℝ) * (3 / 2 * √r)) =
        15 / 2 * y * (1 + r) ^ (-(1 / 4) : ℝ) := by ring
    nlinarith [mul_le_mul_of_nonneg_right hxW hq0.le, mul_le_mul_of_nonneg_right hyW hq0.le]
  have hneg : ((1 + r) ^ (-(1 / 4) : ℝ)) ^ 2 ≤ 1 / √r := by
    have h2 : ((1 + r) ^ (-(1 / 4) : ℝ)) ^ 2 = (1 + r) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [h2]
    exact airyOnePlus_rpow_le hr0
  have hnn : 0 ≤ 3 * x * (1 + r) ^ (-(1 / 4) : ℝ) + 5 * ‖airyPQc Q u‖ * (1 + r) ^ (1 / 4 : ℝ) := by positivity
  calc 4 * (3 * x * (1 + r) ^ (-(1 / 4) : ℝ) + 5 * ‖airyPQc Q u‖ * (1 + r) ^ (1 / 4 : ℝ)) ^ 2
      ≤ 4 * (21 / 2 * W * (1 + r) ^ (-(1 / 4) : ℝ)) ^ 2 := by
        gcongr
    _ = 441 * W ^ 2 * ((1 + r) ^ (-(1 / 4) : ℝ)) ^ 2 := by ring
    _ ≤ 441 * W ^ 2 * (1 / √r) := by gcongr
    _ = _ := by ring

/-- **Good circles for `N = P Ai + Q Ai'`, real polynomials `P`, `Q`, not both zero**
(`general_theorems.tex` Lemma 1.0′; `κ`-form: `airyPQ_good_circle_kappa`). -/
theorem airyPQ_good_circle (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧
      ∀ u : ℂ, ‖u‖ = r → 0 < airyPQW P Q u ∧
        airyPQW P Q u ^ 2 * airyEnv u / (64 * π * √r) ≤ ‖airyPQN P Q u‖ ^ 2 ∧
        (0 ≤ u.im → ‖airyPQM P Q u / airyPQN P Q u - I‖ * airyEnv u ≤ 168 * √π) ∧
        (u.im ≤ 0 → ‖airyPQM P Q u / airyPQN P Q u + I‖ * airyEnv u ≤ 168 * √π) := by
  obtain ⟨T, hT1, hT⟩ := airyPQ_dominance P Q
  refine ⟨max ⌈T⌉₊ 100, fun k hk => ?_⟩
  have hk100 : (100 : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
  have hkT : T ≤ (k : ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast (le_max_left _ _).trans hk)
  have hk10 : 10 ≤ k := by exact_mod_cast (by linarith : (10 : ℝ) ≤ k)
  -- the radius, according to the dominant term
  obtain ⟨c, hc0, hcπ, hdom⟩ : ∃ c : ℝ, 0 ≤ c ∧ c ≤ π ∧ ∀ (r : ℝ) (m : ℕ), 2 / 3 * r ^ (3 / 2 : ℝ) = c + m * π →
      T ≤ r → 25 ≤ r →
      (AiryPQDomP P Q → ∀ ξ : ℂ, 0 ≤ ξ.re → ‖ξ‖ = 2 / 3 * r ^ (3 / 2 : ℝ) →
        Real.exp |ξ.im| / 4 ≤ ‖Complex.cos (ξ - (π / 4 : ℂ))‖) ∧
      (AiryPQDomQ P Q → ∀ ξ : ℂ, 0 ≤ ξ.re → ‖ξ‖ = 2 / 3 * r ^ (3 / 2 : ℝ) →
        Real.exp |ξ.im| / 4 ≤ ‖Complex.sin (ξ - (π / 4 : ℂ))‖) := by
    rcases airyPQ_domP_or_domQ P Q hPQ with hP | hQ
    · refine ⟨π / 4, by positivity, by linarith [Real.pi_pos], fun r m hm hrT hr25 => ⟨fun _ ξ hre hξ => ?_, fun hq => ?_⟩⟩
      · refine airyPQ_cos_good hre ?_ m (by rw [hξ, hm])
        rw [hξ]
        have hr32 := airyRpow_three_halves_eq (by linarith : 0 < r)
        have : 5 ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
        rw [hr32]; nlinarith
      · exact absurd ⟨hP, hq⟩ (airyPQ_not_domP_domQ P Q)
    · refine ⟨3 * π / 4, by positivity, by linarith [Real.pi_pos], fun r m hm hrT hr25 => ⟨fun hp => ?_, fun _ ξ hre hξ => ?_⟩⟩
      · exact absurd ⟨hp, hQ⟩ (airyPQ_not_domP_domQ P Q)
      · refine airyC2_sin_good hre m (by rw [hξ, hm])
  obtain ⟨r, hr1, hr2, m, hm⟩ := airyC2_radius_exists k hk10 hc0 hcπ
  have hrT : T ≤ r := hkT.trans hr1
  have hr100 : (100 : ℝ) ≤ r := hk100.trans hr1
  have hrpos : 0 < r := by linarith
  have hsr : 10 ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsr0 : 0 < √r := by linarith
  have hD := hdom r m hm hrT (by linarith)
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  -- the lower bound
  have hlow : ∀ v : ℂ, ‖v‖ = r →
      airyPQW P Q v ^ 2 * airyEnv v / (64 * π * √r) ≤ ‖airyPQN P Q v‖ ^ 2 := by
    intro v hv
    obtain ⟨hdP, hdQ⟩ := hT v (by rw [hv]; exact hrT)
    have hdom' : 16 * ‖airyPQc Q v‖ * √‖v‖ ≤ ‖airyPQc P v‖ ∨ 16 * ‖airyPQc P v‖ ≤ ‖airyPQc Q v‖ * √‖v‖ := by
      rcases airyPQ_domP_or_domQ P Q hPQ with h | h
      · exact Or.inl (hdP h).1
      · exact Or.inr (hdQ h).1
    have hW : airyPQW P Q v = max ‖airyPQc P v‖ (‖airyPQc Q v‖ * √‖v‖) := rfl
    by_cases hcase : -(‖v‖ / 2) ≤ v.re
    · have := airyAB_sector_ge (airyPQc P v) (airyPQc Q v) hcase (by rw [hv]; linarith) hdom'
      rw [hv] at this hW
      rw [hW]
      refine le_trans ?_ this
      have hh : 0 ≤ max ‖airyPQc P v‖ (‖airyPQc Q v‖ * √r) ^ 2 * airyEnv v := by
        have := airyEnv_pos v; positivity
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hh (mul_nonneg Real.pi_pos.le hsr0.le)]
    · have hlt : v.re < -(‖v‖ / 2) := not_le.mp hcase
      set q : ℂ := (-v) ^ (1 / 2 : ℂ) with hqdef
      have hq : NegSector q := NegSector_of_re_lt hlt
      have hq2 : q ^ 2 = -v := cpow_half_sq _
      have hqn : ‖q‖ ^ 2 = r := by rw [hqdef, norm_cpow_half_sq, norm_neg, hv]
      have hq3 : ‖q‖ ^ 3 = r ^ (3 / 2 : ℝ) := by
        rw [hqdef, airyNorm_cpow_half_pow_three, norm_neg, hv]
      have hqs : ‖q‖ = √r := by rw [← hqn, Real.sqrt_sq (norm_nonneg _)]
      have hξre : 0 ≤ ((2 / 3 : ℂ) * q ^ 3).re := by
        have h1 := hq.re_sq_ge
        have h0 := hq.re_nonneg
        have : ((2 / 3 : ℂ) * q ^ 3).re = 2 / 3 * (q.re * (q.re ^ 2 - 3 * q.im ^ 2)) := by
          simp [Complex.mul_re, re_cube]; ring
        rw [this]
        have : 0 ≤ q.re * (q.re ^ 2 - 3 * q.im ^ 2) := mul_nonneg h0 (by linarith)
        positivity
      have hnξ : ‖(2 / 3 : ℂ) * q ^ 3‖ = 2 / 3 * r ^ (3 / 2 : ℝ) := by
        rw [norm_mul, norm_pow, hq3]; norm_num
      have hsq5 : 5 ≤ ‖q‖ := by rw [hqs]; linarith
      have hdom2 : (Real.exp |((2 / 3 : ℂ) * q ^ 3).im| / 4 ≤ ‖Complex.cos ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ∧
          16 * ‖airyPQc Q v‖ * ‖q‖ ≤ ‖airyPQc P v‖) ∨
          (Real.exp |((2 / 3 : ℂ) * q ^ 3).im| / 4 ≤ ‖Complex.sin ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ∧
          16 * ‖airyPQc P v‖ ≤ ‖airyPQc Q v‖ * ‖q‖) := by
        rw [hqs, ← hv]
        rcases airyPQ_domP_or_domQ P Q hPQ with h | h
        · exact Or.inl ⟨(hD.1 h) _ hξre (by rw [hnξ]), (hdP h).1⟩
        · exact Or.inr ⟨(hD.2 h) _ hξre (by rw [hnξ]), (hdQ h).1⟩
      have := airyAB_neg_sq_ge (airyPQc P v) (airyPQc Q v) hq hsq5 hdom2
      have e : -(q ^ 2) = v := by rw [hq2, neg_neg]
      rw [e, hqs] at this
      have hW' : airyPQW P Q v = max ‖airyPQc P v‖ (‖airyPQc Q v‖ * √r) := by rw [airyPQW, hv]
      rw [hW']
      refine le_trans (le_of_eq ?_) this
      ring
  have hL := hlow u hu
  have hWposAll : ∀ v : ℂ, ‖v‖ = r → 0 < airyPQW P Q v := by
    intro v hv
    obtain ⟨hdP, hdQ⟩ := hT v (by rw [hv]; exact hrT)
    rcases airyPQ_domP_or_domQ P Q hPQ with h | h
    · exact lt_of_lt_of_le (hdP h).2.2 (le_max_left _ _)
    · have h2 := (hdQ h).2.2
      exact lt_of_lt_of_le (mul_pos h2 (by rw [hv]; exact hsr0)) (le_max_right _ _)
  have hup : ∀ v : ℂ, ‖v‖ = r → 0 ≤ v.im →
      ‖airyPQM P Q v / airyPQN P Q v - I‖ * airyEnv v ≤ 168 * √π := by
    intro v hv hvi
    have hLv := hlow v hv
    have hen := airyEnv_pos v
    have hWpos := hWposAll v hv
    have hN2 : 0 < ‖airyPQN P Q v‖ ^ 2 := by
      refine lt_of_lt_of_le ?_ hLv
      positivity
    have hN : 0 < ‖airyPQN P Q v‖ := by
      rcases (norm_nonneg (airyPQN P Q v)).lt_or_eq with h | h
      · exact h
      · rw [← h] at hN2; simp at hN2
    have hne : airyPQN P Q v ≠ 0 := norm_pos_iff.mp hN
    have hnum := airyPQ_num_le P Q hvi (by rw [hv]; linarith)
    rw [hv] at hnum
    have e : airyPQM P Q v / airyPQN P Q v - I = (airyPQM P Q v - I * airyPQN P Q v) / airyPQN P Q v := by
      field_simp
    rw [e, norm_div]
    exact airyPQ_ratio_le hN hen hsr0 hnum hLv (norm_nonneg _)
  refine ⟨hWposAll u hu, hL, fun hi => hup u hu hi, fun hi => ?_⟩
  have hci : 0 ≤ ((starRingEnd ℂ) u).im := by simpa using hi
  have hcu : ‖(starRingEnd ℂ) u‖ = r := by rw [Complex.norm_conj, hu]
  have h := hup ((starRingEnd ℂ) u) hcu hci
  have e : ‖airyPQM P Q u / airyPQN P Q u + I‖ =
      ‖airyPQM P Q ((starRingEnd ℂ) u) / airyPQN P Q ((starRingEnd ℂ) u) - I‖ := by
    have : airyPQM P Q ((starRingEnd ℂ) u) / airyPQN P Q ((starRingEnd ℂ) u) - I =
        (starRingEnd ℂ) (airyPQM P Q u / airyPQN P Q u + I) := by
      rw [map_add, map_div₀, conj_airyPQM, conj_airyPQN, Complex.conj_I]; ring
    rw [this, Complex.norm_conj]
  rw [e, ← airyEnv_conj u]
  exact h

open Classical in
/-- Twice the exponent `κ` of the note: `2κ = 2 deg P - 1/2` if `P` dominates, `2 deg Q + 1/2` otherwise. -/
noncomputable def airyPQkappa (P Q : ℝ[X]) : ℝ :=
  if AiryPQDomP P Q then 2 * (P.natDegree : ℝ) - 1 / 2 else 2 * (Q.natDegree : ℝ) + 1 / 2

lemma airyPQ_pow_div_sqrt {r : ℝ} (hr : 0 < r) (d : ℕ) : r ^ (2 * d) / √r = r ^ ((2 * (d : ℝ)) - 1 / 2) := by
  rw [Real.rpow_sub hr, Real.sqrt_eq_rpow]
  congr 1
  rw [show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

lemma airyPQ_pow_mul_sqrt {r : ℝ} (hr : 0 < r) (d : ℕ) : r ^ (2 * d) * √r = r ^ ((2 * (d : ℝ)) + 1 / 2) := by
  rw [Real.rpow_add hr, Real.sqrt_eq_rpow]
  congr 1
  rw [show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- The lower bound of the dominant term in the power form `c r^{2κ}`. -/
lemma airyPQW_lower (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    ∃ c T : ℝ, 0 < c ∧ 1 ≤ T ∧ ∀ u : ℂ, T ≤ ‖u‖ →
      c * ‖u‖ ^ airyPQkappa P Q ≤ airyPQW P Q u ^ 2 / (64 * π * √‖u‖) := by
  obtain ⟨T, hT1, hT⟩ := airyPQ_dominance P Q
  rcases airyPQ_domP_or_domQ P Q hPQ with h | h
  · have hlc : 0 < |P.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr (by
      rcases h with ⟨-, h⟩ | ⟨h, -⟩ <;> exact h))
    refine ⟨|P.leadingCoeff| ^ 2 / (256 * π), T, by positivity, hT1, fun u hu => ?_⟩
    have hr : 0 < ‖u‖ := by linarith
    have hl := ((hT u hu).1 h).2.1
    have hWP : ‖airyPQc P u‖ ≤ airyPQW P Q u := le_max_left _ _
    have h2 : (|P.leadingCoeff| / 2 * ‖u‖ ^ P.natDegree) ^ 2 ≤ airyPQW P Q u ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hl.trans hWP) 2
    have e : airyPQkappa P Q = 2 * (P.natDegree : ℝ) - 1 / 2 := by unfold airyPQkappa; simp [h]
    rw [e, ← airyPQ_pow_div_sqrt hr]
    have hsr : 0 < √‖u‖ := Real.sqrt_pos.mpr hr
    rw [le_div_iff₀ (by positivity)]
    have : (|P.leadingCoeff| / 2 * ‖u‖ ^ P.natDegree) ^ 2 = |P.leadingCoeff| ^ 2 / 4 * ‖u‖ ^ (2 * P.natDegree) := by
      rw [mul_pow, div_pow, pow_mul']; ring
    rw [this] at h2
    have key : |P.leadingCoeff| ^ 2 / (256 * π) * (‖u‖ ^ (2 * P.natDegree) / √‖u‖) * (64 * π * √‖u‖) =
        |P.leadingCoeff| ^ 2 / 4 * ‖u‖ ^ (2 * P.natDegree) := by
      field_simp; ring
    rw [key]; exact h2
  · have hlc : 0 < |Q.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr h.1)
    refine ⟨|Q.leadingCoeff| ^ 2 / (256 * π), T, by positivity, hT1, fun u hu => ?_⟩
    have hr : 0 < ‖u‖ := by linarith
    have hsr : 0 < √‖u‖ := Real.sqrt_pos.mpr hr
    have hl := ((hT u hu).2 h).2.1
    have hWQ : ‖airyPQc Q u‖ * √‖u‖ ≤ airyPQW P Q u := le_max_right _ _
    have h2 : (|Q.leadingCoeff| / 2 * ‖u‖ ^ Q.natDegree * √‖u‖) ^ 2 ≤ airyPQW P Q u ^ 2 :=
      pow_le_pow_left₀ (by positivity) ((mul_le_mul_of_nonneg_right hl hsr.le).trans hWQ) 2
    have hnd : ¬ AiryPQDomP P Q := fun hp => airyPQ_not_domP_domQ P Q ⟨hp, h⟩
    have e : airyPQkappa P Q = 2 * (Q.natDegree : ℝ) + 1 / 2 := by unfold airyPQkappa; simp [hnd]
    rw [e, ← airyPQ_pow_mul_sqrt hr]
    rw [le_div_iff₀ (by positivity)]
    have hsq : √‖u‖ ^ 2 = ‖u‖ := Real.sq_sqrt hr.le
    have : (|Q.leadingCoeff| / 2 * ‖u‖ ^ Q.natDegree * √‖u‖) ^ 2 =
        |Q.leadingCoeff| ^ 2 / 4 * ‖u‖ ^ (2 * Q.natDegree) * ‖u‖ := by
      rw [mul_pow, mul_pow, div_pow, pow_mul', hsq]; ring
    rw [this] at h2
    have key : |Q.leadingCoeff| ^ 2 / (256 * π) * (‖u‖ ^ (2 * Q.natDegree) * √‖u‖) * (64 * π * √‖u‖) =
        |Q.leadingCoeff| ^ 2 / 4 * ‖u‖ ^ (2 * Q.natDegree) * ‖u‖ := by
      have h3 : √‖u‖ * √‖u‖ = ‖u‖ := Real.mul_self_sqrt hr.le
      calc _ = |Q.leadingCoeff| ^ 2 / 4 * ‖u‖ ^ (2 * Q.natDegree) * (√‖u‖ * √‖u‖) := by
            field_simp; ring
        _ = _ := by rw [h3]
    rw [key]; exact h2

/-- **Good circles, `κ`-form** (`general_theorems.tex` Lemma 1.0′: `|N(u)| ≥ c r^κ e(u)^{1/2}`). -/
theorem airyPQ_good_circle_kappa (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧
      ∀ u : ℂ, ‖u‖ = r → 0 < airyPQW P Q u ∧
        c * r ^ airyPQkappa P Q * airyEnv u ≤ ‖airyPQN P Q u‖ ^ 2 ∧
        (0 ≤ u.im → ‖airyPQM P Q u / airyPQN P Q u - I‖ * airyEnv u ≤ 168 * √π) ∧
        (u.im ≤ 0 → ‖airyPQM P Q u / airyPQN P Q u + I‖ * airyEnv u ≤ 168 * √π) := by
  obtain ⟨c, T, hc, hT1, hT⟩ := airyPQW_lower P Q hPQ
  obtain ⟨k₀, hk₀⟩ := airyPQ_good_circle P Q hPQ
  refine ⟨c, hc, max k₀ ⌈T⌉₊, fun k hk => ?_⟩
  obtain ⟨r, hr1, hr2, hr⟩ := hk₀ k ((le_max_left _ _).trans hk)
  have hkT : T ≤ (k : ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast (le_max_right _ _).trans hk)
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := hr u hu
  refine ⟨h0, ?_, h2, h3⟩
  have hTu : T ≤ ‖u‖ := by rw [hu]; exact hkT.trans hr1
  have := hT u hTu
  rw [hu] at this
  have hen := airyEnv_pos u
  calc c * r ^ airyPQkappa P Q * airyEnv u ≤ (airyPQW P Q u ^ 2 / (64 * π * √r)) * airyEnv u := by
        gcongr
    _ = airyPQW P Q u ^ 2 * airyEnv u / (64 * π * √r) := by ring
    _ ≤ _ := h1

lemma airyPQkappa_ge (P Q : ℝ[X]) : -(1 / 2 : ℝ) ≤ airyPQkappa P Q := by
  unfold airyPQkappa
  split_ifs
  · have : (0 : ℝ) ≤ P.natDegree := Nat.cast_nonneg _
    linarith
  · have : (0 : ℝ) ≤ Q.natDegree := Nat.cast_nonneg _
    linarith

/-- **Good circles in the form `(E2_N)` of `SE5_FIVE_LEVEL_AIRY.md` §0.3**: `|N(u)|² ≥ c (1+|u|)^{-1/2} e(u)` on the circles
(`A = max(0, -2κ) ≤ 1/2`), with `|M/N ∓ i| ≤ 168√π/e`. -/
theorem airyPQ_good_circle_SE5 (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧
      ∀ u : ℂ, ‖u‖ = r →
        c * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * airyEnv u ≤ ‖airyPQN P Q u‖ ^ 2 ∧
        (0 ≤ u.im → ‖airyPQM P Q u / airyPQN P Q u - I‖ * airyEnv u ≤ 168 * √π) ∧
        (u.im ≤ 0 → ‖airyPQM P Q u / airyPQN P Q u + I‖ * airyEnv u ≤ 168 * √π) := by
  obtain ⟨c, hc, k₀, hk₀⟩ := airyPQ_good_circle_kappa P Q hPQ
  refine ⟨c, hc, max k₀ 1, fun k hk => ?_⟩
  obtain ⟨r, hr1, hr2, hr⟩ := hk₀ k ((le_max_left _ _).trans hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hr u hu
  refine ⟨?_, h2, h3⟩
  have hr1' : 1 ≤ r := hk1.trans hr1
  have hen := airyEnv_pos u
  have h4 : (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) ≤ r ^ airyPQkappa P Q := by
    rw [hu]
    calc (1 + r) ^ (-(1 / 2 : ℝ)) ≤ r ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
      _ ≤ r ^ airyPQkappa P Q := Real.rpow_le_rpow_of_exponent_le hr1' (airyPQkappa_ge P Q)
  calc c * (1 + ‖u‖) ^ (-(1 / 2 : ℝ)) * airyEnv u ≤ c * r ^ airyPQkappa P Q * airyEnv u := by gcongr
    _ ≤ _ := h1

/-- info: 'FormalResearch.Special.airyPQ_good_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_good_circle

/-- info: 'FormalResearch.Special.airyPQ_good_circle_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_good_circle_kappa

/-- info: 'FormalResearch.Special.airyPQ_good_circle_SE5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_good_circle_SE5

end FormalResearch.Special
