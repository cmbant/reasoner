module

public import FormalResearch.Special.AiryCft2ComboAlg
public import FormalResearch.Special.AiryCftWeights

/-!
# The zeros of `N = P·Ai + Q·Ai'` (`Q ≠ 0`): real, simple, positive weights, interlaced with the zeros of `Ai`

Formalises (CFT/PR240 `GENERAL_THEOREMS.md` §1 preamble and `SOFT_EDGE_THEOREMS.md` Lemma 4.4 for constant `P, Q`; for the
Clark functions `ψ_α`, `P = cos α`, `Q = -sin α`) the zero theory used by the Clark-Airy summation, **without** the Prüfer angle or
de Branges theory: everything follows from the Mittag-Leffler expansion of `Ai'/Ai` (`AiryCftMittagLeffler`).

Let `m = Ai'/Ai`.  At a zero `z` of `N` one has `Ai(z) ≠ 0` and `m(z) = -P/Q ∈ ℝ`.

* `airyNC_zero_im`: **every zero of `N` in `ℂ` is real**.  `Im m(z) = -Im z · Σ_n |z - a_n|^{-2}` (the imaginary part of the
  Mittag-Leffler series), which vanishes only for `Im z = 0`.
* `airyNC_zero_weight_pos`: at a real zero `x`: `D(x) = P² - x Q² > 0` and `N'(x) = -Ai(x) D(x)/Q ≠ 0` (the zeros are
  simple, the weights `D/N'²` of the Clark summation are positive).  From `m' = x - m² = -Σ_n (x - a_n)^{-2} < 0`
  (`airyAi_sq_series_real`) and `m(x)² = P²/Q²`.
* `airy_m_strictAntiOn`: `m` is strictly decreasing on any interval free of zeros of `Ai`; hence
  consequently (`airyNIdx_injOn`) **at most one zero of `N` between two consecutive zeros of `Ai`** (and at most one above `a_1`).
* the index `airyNIdx t` (the number of zeros `a_j` above `t`, `t ∈ (a_{n+1}, a_n)`, `a_0 = +∞`) is injective on the real zeros of `N`
  (`airyNIdx_injOn`) and `t < a_n` for `n = airyNIdx t ≥ 1`, so `-t ≥ 2.5 n^{2/3}` for `n ≥ 2` (`airyNIdx_abs_ge`); hence
  `airyNC_zeros_finite`: finitely many zeros in every disc, and the node counting `#{|t| < r} = O(r^{3/2})`.
* `airyNC_weight_norm_le`: for a real zero `t ≤ -1`: `‖D(t)/N'(t)²‖ ≤ 8π² (3|P|+5|Q|)² Q^{-2} (1 + |t|)^{-1/2}` (from
  `M(t) = -D/(πN'(t))`, `M(t) = (M - iN)(t)` and `airyMC_sub_I_mul_sq_le`).
* `airyNC_summable_weighted`: if `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` with `ν < -1`, then `Σ_{N(z)=0} f(z) D(z)/N'(z)²` converges absolutely
  (summable over the subtype of zeros).

All proved (no numerics enter).  Not formalised: existence and the exact location of the nodes `z_n(α)` (`z_1 > a_1`,
`z_n ∈ (a_n, a_{n-1})`; the node asymptotics).  This module is the constant-coefficient case; for polynomial `P, Q` with `Q + iP` having
all roots in the open lower half-plane (Hermite-Biehler `N`, `SOFT_EDGE_THEOREMS.md` Lemma 4.6) the zeros are real and simple
(`airyPQ_zero_im`, `airyPQ_zero_weight_pos`, `AiryPolyZeros`, umbrella `AiryPoly`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Zeros of `N` are not zeros of `Ai`; zeros are real -/

lemma airyNC_ne_zero_of_airy_zero (P Q : ℝ) (hQ : Q ≠ 0) {z : ℂ} (h : airyAiC z = 0) : airyNC P Q z ≠ 0 := by
  obtain ⟨n, -, rfl⟩ := (airyAiC_eq_zero_iff z).mp h
  unfold airyNC
  rw [h, mul_zero, zero_add]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hQ) (airyZero_deriv_ne_zero n)

lemma airyNC_logDeriv_at_zero (P Q : ℝ) (hQ : Q ≠ 0) {z : ℂ} (h : airyNC P Q z = 0) :
    deriv airyAiC z / airyAiC z = -((P : ℂ) / (Q : ℂ)) := by
  have hA : airyAiC z ≠ 0 := fun h0 => airyNC_ne_zero_of_airy_zero P Q hQ h0 h
  have hQ' : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  unfold airyNC at h
  field_simp
  linear_combination h

/-- **Every zero of `N = P Ai + Q Ai'` (`Q ≠ 0`) is real.** -/
theorem airyNC_zero_im (P Q : ℝ) (hQ : Q ≠ 0) {z : ℂ} (h : airyNC P Q z = 0) : z.im = 0 := by
  by_contra him
  have hA : airyAiC z ≠ 0 := fun h0 => airyNC_ne_zero_of_airy_zero P Q hQ h0 h
  have hm := airyNC_logDeriv_at_zero P Q hQ h
  have hs := airyAiC_logDeriv_mittagLeffler hA
  have hs' := Complex.hasSum_im hs
  have e0 : (deriv airyAiC 0 / airyAiC 0).im = 0 := by
    have h1 : deriv airyAiC ((0 : ℝ) : ℂ) = (airyAi' 0 : ℂ) := deriv_airyAiC_ofReal 0
    have h2 : airyAiC ((0 : ℝ) : ℂ) = (airyAi 0 : ℂ) := airyAiC_ofReal 0
    simp only [Complex.ofReal_zero] at h1 h2
    rw [h1, h2, ← Complex.ofReal_div]; simp
  have e1 : (deriv airyAiC z / airyAiC z - deriv airyAiC 0 / airyAiC 0).im = 0 := by
    rw [Complex.sub_im, e0, hm]
    simp [Complex.div_im, Complex.neg_im]
  rw [e1] at hs'
  have hterm : ∀ n : ℕ, (1 / (z - (airyZero (n + 1) : ℂ)) + 1 / (airyZero (n + 1) : ℂ)).im =
      -(z.im / Complex.normSq (z - (airyZero (n + 1) : ℂ))) := by
    intro n
    rw [Complex.add_im, one_div, one_div, Complex.inv_im, ← Complex.ofReal_inv, Complex.ofReal_im]
    simp
    ring
  simp_rw [hterm] at hs'
  have hs2 : HasSum (fun n : ℕ => z.im ^ 2 / Complex.normSq (z - (airyZero (n + 1) : ℂ))) 0 := by
    have := (hs'.neg).mul_left z.im
    simp only [neg_neg, neg_zero, mul_zero] at this
    convert this using 1
    funext n
    ring
  have hpos : ∀ n : ℕ, 0 ≤ z.im ^ 2 / Complex.normSq (z - (airyZero (n + 1) : ℂ)) := fun n =>
    div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have h0 := le_hasSum hs2 0 (fun j _ => hpos j)
  have hn : 0 < Complex.normSq (z - (airyZero (0 + 1) : ℂ)) := by
    rw [Complex.normSq_pos]
    intro h0
    have : z.im = 0 := by
      have := congrArg Complex.im (sub_eq_zero.mp h0)
      simpa using this
    exact him this
  have : 0 < z.im ^ 2 / Complex.normSq (z - (airyZero (0 + 1) : ℂ)) := by
    have : 0 < z.im ^ 2 := by positivity
    positivity
  linarith

/-- info: 'FormalResearch.Special.airyNC_zero_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_zero_im

/-! ### Real zeros: positive weights, simplicity -/

lemma airyNC_ofReal (P Q : ℝ) (x : ℝ) :
    airyNC P Q (x : ℂ) = ((P * airyAi x + Q * airyAi' x : ℝ) : ℂ) := by
  unfold airyNC
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal]
  push_cast; ring

/-- At a real zero `x` of `N`: `D(x) = P² - x Q² > 0` and `N'(x) ≠ 0`. -/
theorem airyNC_zero_weight_pos (P Q : ℝ) (hQ : Q ≠ 0) {x : ℝ} (h : airyNC P Q (x : ℂ) = 0) :
    0 < P ^ 2 - x * Q ^ 2 ∧ airyNC' P Q (x : ℂ) ≠ 0 := by
  rw [airyNC_ofReal, Complex.ofReal_eq_zero] at h
  have hAx : airyAi x ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_add] at h
    have : airyAi' x = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hQ
      · exact h1
    exact airyAi_ne_zero_of_deriv_zero this h0
  have hQ2 : 0 < Q ^ 2 := by positivity
  have hm : airyAi' x = -(P / Q) * airyAi x := by
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
  have hdiv : airyAi' x / airyAi x = -(P / Q) := by
    rw [hm]; field_simp
  rw [hdiv] at hpos
  have hD : 0 < P ^ 2 - x * Q ^ 2 := by
    have : (-(P / Q)) ^ 2 = P ^ 2 / Q ^ 2 := by ring
    rw [this] at hpos
    have h1 : 0 < P ^ 2 / Q ^ 2 - x := hpos
    have h2 := mul_pos h1 hQ2
    have e : (P ^ 2 / Q ^ 2 - x) * Q ^ 2 = P ^ 2 - x * Q ^ 2 := by field_simp
    linarith
  refine ⟨hD, ?_⟩
  unfold airyNC'
  rw [deriv_airyAiC_ofReal, airyAiC_ofReal]
  have : (P : ℂ) * (airyAi' x : ℂ) + (Q : ℂ) * ((x : ℂ) * (airyAi x : ℂ)) =
      (((P * airyAi' x + Q * (x * airyAi x)) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Ne, Complex.ofReal_eq_zero]
  have e : P * airyAi' x + Q * (x * airyAi x) = -(airyAi x / Q) * (P ^ 2 - x * Q ^ 2) := by
    rw [hm]; field_simp; ring
  rw [e]
  have : -(airyAi x / Q) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hAx hQ)
  exact mul_ne_zero this hD.ne'

/-- info: 'FormalResearch.Special.airyNC_zero_weight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_zero_weight_pos

/-! ### Strict monotonicity of `Ai'/Ai` between the zeros of `Ai` -/

/-- `m = Ai'/Ai` is strictly decreasing on an interval free of zeros of `Ai`. -/
theorem airy_m_strictAntiOn {a b : ℝ} (h : ∀ x ∈ Icc a b, airyAi x ≠ 0) :
    StrictAntiOn (fun x => airyAi' x / airyAi x) (Icc a b) := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt (fun x => airyAi' x / airyAi x)
      ((x * airyAi x * airyAi x - airyAi' x * airyAi' x) / airyAi x ^ 2) x := by
    intro x hx
    exact (hasDerivAt_airyAi' x).div (hasDerivAt_airyAi x) (h x hx)
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
  rw [(hd x hx').deriv]
  have hs := airyAi_sq_series_real (h x hx')
  have hpos : 0 < (airyAi' x / airyAi x) ^ 2 - x := by
    have h0 := le_hasSum hs 0 (fun j _ => by positivity)
    have : 0 < ((x - airyZero (0 + 1)) ^ 2)⁻¹ := by
      have : x - airyZero (0 + 1) ≠ 0 := by
        intro h1
        have hx2 : x = airyZero 1 := by linarith
        have := h x hx'
        rw [hx2, airyAi_airyZero] at this
        exact this rfl
      positivity
    linarith
  have hA := h x hx'
  have e : (x * airyAi x * airyAi x - airyAi' x * airyAi' x) / airyAi x ^ 2 =
      -((airyAi' x / airyAi x) ^ 2 - x) := by
    field_simp
    ring
  rw [e]; linarith

/-! ### The index of a real zero in the gaps of `Ai` -/

lemma airyN_exists_idx (t : ℝ) : ∃ n : ℕ, airyZero (n + 1) < t := by
  obtain ⟨n, hn2, hn⟩ := airyZero_exists_abs_ge (-t + 1)
  exact ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; linarith⟩

/-- The index: least `n` with `a_{n+1} < t`; so `t ∈ (a_{n+1}, a_n)` (`a_0 = +∞`) if `t` is not a zero of `Ai`. -/
noncomputable def airyNIdx (t : ℝ) : ℕ := by
  classical exact Nat.find (airyN_exists_idx t)

lemma airyNIdx_spec (t : ℝ) : airyZero (airyNIdx t + 1) < t := by
  classical
  unfold airyNIdx
  exact Nat.find_spec (airyN_exists_idx t)

lemma airyNIdx_min {t : ℝ} {j : ℕ} (hj : j < airyNIdx t) : ¬ airyZero (j + 1) < t := by
  classical
  unfold airyNIdx at hj
  exact Nat.find_min (airyN_exists_idx t) hj

/-- For a real `t` which is not a zero of `Ai`: `a_j > t` for `1 ≤ j ≤ n`, `a_j < t` for `j ≥ n + 1`, `n = airyNIdx t`. -/
lemma airyNIdx_gap {t : ℝ} (ht : airyAi t ≠ 0) {j : ℕ} (hj : 1 ≤ j) :
    (j ≤ airyNIdx t → t < airyZero j) ∧ (airyNIdx t + 1 ≤ j → airyZero j < t) := by
  constructor
  · intro hjn
    have := airyNIdx_min (t := t) (j := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    rcases (not_lt.mp this).lt_or_eq with h | h
    · exact h
    · exfalso
      apply ht
      rw [h, airyAi_airyZero]
  · intro hjn
    have h1 := airyNIdx_spec t
    rcases hjn.lt_or_eq with h | h
    · have := airyZero_lt_of_lt (n := airyNIdx t + 1) (m := j) (by omega) h
      linarith
    · rw [← h]; exact h1

/-- At most one zero of `N` has a given index. -/
theorem airyNIdx_injOn (P Q : ℝ) (hQ : Q ≠ 0) :
    Set.InjOn airyNIdx {t : ℝ | airyNC P Q (t : ℂ) = 0} := by
  have key : ∀ t₁ t₂ : ℝ, airyNC P Q (t₁ : ℂ) = 0 → airyNC P Q (t₂ : ℂ) = 0 → t₁ < t₂ →
      airyNIdx t₁ = airyNIdx t₂ → False := by
    intro t₁ t₂ h₁ h₂ hlt hidx
    have hA : ∀ t : ℝ, airyNC P Q (t : ℂ) = 0 → airyAi t ≠ 0 := by
      intro t ht h0
      have := airyNC_ne_zero_of_airy_zero P Q hQ (z := (t : ℂ)) (by rw [airyAiC_ofReal, h0]; simp)
      exact this ht
    set n := airyNIdx t₂ with hn
    have hfree : ∀ x ∈ Icc t₁ t₂, airyAi x ≠ 0 := by
      intro x hx h0
      have hz : airyAiC (x : ℂ) = 0 := by rw [airyAiC_ofReal, h0]; simp
      obtain ⟨j, hj, hxj⟩ := (airyAiC_eq_zero_iff _).mp hz
      have hxj' : x = airyZero j := by exact_mod_cast hxj
      by_cases hjn : j ≤ n
      · have := (airyNIdx_gap (hA t₂ h₂) hj).1 hjn
        linarith [hx.2]
      · have := (airyNIdx_gap (hA t₁ h₁) hj).2 (by rw [hidx]; omega)
        linarith [hx.1]
    have hanti := airy_m_strictAntiOn hfree
    have e1 : airyAi' t₁ / airyAi t₁ = -(P / Q) := by
      have := airyNC_logDeriv_at_zero P Q hQ h₁
      rw [deriv_airyAiC_ofReal, airyAiC_ofReal, ← Complex.ofReal_div] at this
      have h' : airyAi' t₁ / airyAi t₁ = -(P / Q) := by exact_mod_cast this
      exact h'
    have e2 : airyAi' t₂ / airyAi t₂ = -(P / Q) := by
      have := airyNC_logDeriv_at_zero P Q hQ h₂
      rw [deriv_airyAiC_ofReal, airyAiC_ofReal, ← Complex.ofReal_div] at this
      have h' : airyAi' t₂ / airyAi t₂ = -(P / Q) := by exact_mod_cast this
      exact h'
    have := hanti ⟨le_refl t₁, hlt.le⟩ ⟨hlt.le, le_refl t₂⟩ hlt
    simp only at this
    rw [e1, e2] at this
    exact lt_irrefl _ this
  intro t₁ h₁ t₂ h₂ hidx
  rcases lt_trichotomy t₁ t₂ with h | h | h
  · exact (key t₁ t₂ h₁ h₂ h hidx).elim
  · exact h
  · exact (key t₂ t₁ h₂ h₁ h hidx.symm).elim

/-- `t < a_n` for `n = airyNIdx t ≥ 1` at a real zero of `N`; hence `-t ≥ 2.5 n^{2/3}` for `n ≥ 2`. -/
theorem airyNIdx_abs_ge (P Q : ℝ) (hQ : Q ≠ 0) {t : ℝ} (h : airyNC P Q (t : ℂ) = 0)
    (hn : 2 ≤ airyNIdx t) : 2.5 * (airyNIdx t : ℝ) ^ (2 / 3 : ℝ) ≤ -t := by
  have hA : airyAi t ≠ 0 := by
    intro h0
    have := airyNC_ne_zero_of_airy_zero P Q hQ (z := (t : ℂ)) (by rw [airyAiC_ofReal, h0]; simp)
    exact this h
  have := (airyNIdx_gap hA (j := airyNIdx t) (by omega)).1 le_rfl
  have hb := (airyZero_abs_bounds (n := airyNIdx t) hn).1
  linarith

/-! ### Finiteness in discs -/

theorem airyNC_zeros_finite (P Q : ℝ) (hQ : Q ≠ 0) (R : ℝ) :
    {z : ℂ | airyNC P Q z = 0 ∧ ‖z‖ ≤ R}.Finite := by
  set K : ℕ := ⌈(2 * R / 5) ^ (3 / 2 : ℝ)⌉₊ + 2 with hK
  have hfin : ({n : ℕ | n < K}).Finite := Set.finite_lt_nat K
  refine Set.Finite.of_injOn (f := fun z : ℂ => airyNIdx z.re) (t := {n : ℕ | n < K}) ?_ ?_ hfin
  · intro z hz
    obtain ⟨hz0, hzR⟩ := hz
    have him := airyNC_zero_im P Q hQ hz0
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hzr] at hz0
    show airyNIdx z.re < K
    by_contra hge
    have hge : K ≤ airyNIdx z.re := not_lt.mp hge
    have h2 : 2 ≤ airyNIdx z.re := by omega
    have hb := airyNIdx_abs_ge P Q hQ hz0 h2
    have hzn : -z.re ≤ R := by
      have := Complex.abs_re_le_norm z
      linarith [neg_le_abs z.re]
    have h3 : (5 / 2 : ℝ) * (airyNIdx z.re : ℝ) ^ (2 / 3 : ℝ) ≤ R := by norm_num at hb ⊢; linarith
    have hK' : (2 * R / 5) ^ (3 / 2 : ℝ) < (airyNIdx z.re : ℝ) := by
      have hc : (⌈(2 * R / 5) ^ (3 / 2 : ℝ)⌉₊ : ℝ) < K := by
        rw [hK]; push_cast; linarith
      have h4 : ((⌈(2 * R / 5) ^ (3 / 2 : ℝ)⌉₊ : ℕ) : ℝ) + 1 ≤ (airyNIdx z.re : ℝ) := by
        exact_mod_cast (by omega : ⌈(2 * R / 5) ^ (3 / 2 : ℝ)⌉₊ + 1 ≤ airyNIdx z.re)
      have h5 := Nat.le_ceil ((2 * R / 5) ^ (3 / 2 : ℝ))
      linarith
    have hn0 : (0 : ℝ) < (airyNIdx z.re : ℝ) := by exact_mod_cast (by omega : 0 < airyNIdx z.re)
    have hR0 : 0 ≤ 2 * R / 5 := by
      have : 0 ≤ ‖z‖ := norm_nonneg _
      linarith
    have : 2 * R / 5 < ((airyNIdx z.re : ℝ)) ^ (2 / 3 : ℝ) := by
      have := Real.rpow_lt_rpow (Real.rpow_nonneg hR0 _) hK' (by norm_num : (0 : ℝ) < 2 / 3)
      rwa [← Real.rpow_mul hR0, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at this
    linarith
  · intro z₁ hz₁ z₂ hz₂ h12
    obtain ⟨h1, -⟩ := hz₁
    obtain ⟨h2, -⟩ := hz₂
    have i1 := airyNC_zero_im P Q hQ h1
    have i2 := airyNC_zero_im P Q hQ h2
    have e1 : z₁ = (z₁.re : ℂ) := Complex.ext (by simp) (by simp [i1])
    have e2 : z₂ = (z₂.re : ℂ) := Complex.ext (by simp) (by simp [i2])
    rw [e1] at h1
    rw [e2] at h2
    have := airyNIdx_injOn P Q hQ h1 h2 h12
    rw [e1, e2, this]

/-- info: 'FormalResearch.Special.airyNC_zeros_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_zeros_finite

end FormalResearch.Special
