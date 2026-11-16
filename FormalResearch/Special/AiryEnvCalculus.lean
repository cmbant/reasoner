module

public import FormalResearch.Special.AiryEnvelope

/-!
# Calculus of the squared envelope `e(u) = exp(-(4/3) Re u^{3/2})` (E3, E4)

Notation: `airyEnv u = e(u) = exp(-(4/3) Re u^{3/2})` (principal branch), `a(u) = Re √u ≥ 0`.

The whole file rests on one algebraic fact.  Write `w = u^{1/2}`, `a = Re w ≥ 0`, `b = Im w`.  Then
`u = w²`, `u^{3/2} = w³`, `Re u = a² - b²`, `Im u = 2ab`, `‖u‖ = a² + b²`, so

`Re u^{3/2} = a³ - 3ab² = 3 (Re u) a - 2a³`    (`re_cpow_three_halves_eq`),

and no derivative or argument is ever taken.  Statements (AIRY_POISSON.md §1, LOCAL_AIRY_MODEL.md (c)):

* **(E3) shift inequality** `airyEnv_add_real_le`: for every `u ∈ ℂ` and every real `τ`
  (the survey needs `τ ≥ 0`; the proof does not),
  `e(u + τ) ≤ e(u) exp(-2 τ Re √u)`.  The proof is the identity
  `Re (u+τ)^{3/2} - Re u^{3/2} - (3/2) τ Re √u = (a'-a)²(a' + a/2) + (3/2) a (b'-b)²`
  (primes for `u + τ`), using only `a b = a' b'` (equal imaginary parts) and `a, a' ≥ 0`.
* **monotone in the imaginary part** `airyEnv_mono_im`: `u.re = u'.re`, `|u.im| ≤ |u'.im|` implies
  `e(u) ≤ e(u')`; in particular `e(x + i s)` is nondecreasing in `s ≥ 0` (`airyEnv_mono_of_nonneg`).
  Direction checked: at `x = -1`, `e(-1) = 1 ≤ e(-1+i)`.
* **(E4)** `airyPhi_norm_le`: for `Φ_τ(u) = Ai(k (u+τ))`, `k = 2^{2/3}` (`airyPhi`), `τ ≥ 0`:
  `‖Φ_τ(u)‖ ≤ 3 (1+τ)^{1/4} (1+‖u‖)^{-1/4} e(u) exp(-2 τ Re √u)`.

Numerical checks (mpmath, 30 digits, 20000 random points each, `|x|,|s|,|τ| ≤ 30..40`): the shift
inequality holds with minimal relative slack `1.6e-7`; monotonicity has no violation; the true supremum
of `‖Φ_τ(u)‖ / ((1+τ)^{1/4}(1+‖u‖)^{-1/4} e(u) e^{-2τ Re √u)}` is `0.29`, so the constant `3` (from (E1)) is
far from sharp.

Not formalised: the identification of `Φ_τ` with the distributional Poisson-type identities of
AIRY_POISSON (only the pointwise bound E4 is proved).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `a(u) = Re √u`, the real part of the principal square root. -/
noncomputable def airySqrtRe (u : ℂ) : ℝ := (u ^ (1 / 2 : ℂ)).re

lemma airySqrtRe_nonneg (u : ℂ) : 0 ≤ airySqrtRe u := cpow_half_re_nonneg u

lemma airySqrtRe_sq_sub (u : ℂ) :
    airySqrtRe u ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 = u.re := by
  have h := congrArg Complex.re (cpow_half_sq u)
  rw [re_sq] at h
  exact h

lemma airySqrtRe_mul_im (u : ℂ) : 2 * airySqrtRe u * (u ^ (1 / 2 : ℂ)).im = u.im := by
  have h := congrArg Complex.im (cpow_half_sq u)
  rw [im_sq] at h
  exact h

lemma airySqrtRe_sq_add (u : ℂ) :
    airySqrtRe u ^ 2 + (u ^ (1 / 2 : ℂ)).im ^ 2 = ‖u‖ := by
  unfold airySqrtRe
  rw [← sq_norm_eq, norm_cpow_half_sq]

/-- `Re u^{3/2} = a³ - 3ab²` in terms of the principal root `w = a + ib`. -/
lemma re_cpow_three_halves_eq_ab (u : ℂ) :
    (u ^ (3 / 2 : ℂ)).re = airySqrtRe u ^ 3 - 3 * airySqrtRe u * (u ^ (1 / 2 : ℂ)).im ^ 2 := by
  rw [← cpow_half_cube, re_cube]
  rfl

/-- `Re u^{3/2} = 3 (Re u) a - 2 a³` with `a = Re √u`. -/
lemma re_cpow_three_halves_eq (u : ℂ) :
    (u ^ (3 / 2 : ℂ)).re = 3 * u.re * airySqrtRe u - 2 * airySqrtRe u ^ 3 := by
  rw [re_cpow_three_halves_eq_ab, ← airySqrtRe_sq_sub u]
  ring

/-! ### (E3) -/

/-- **(E3) core inequality.** For every `u` and every real `τ`:
`Re (u+τ)^{3/2} ≥ Re u^{3/2} + (3/2) τ Re √u`. -/
lemma re_cpow_three_halves_add_ge (u : ℂ) (τ : ℝ) :
    (u ^ (3 / 2 : ℂ)).re + 3 / 2 * τ * airySqrtRe u ≤ ((u + τ) ^ (3 / 2 : ℂ)).re := by
  set a := airySqrtRe u with ha
  set b := (u ^ (1 / 2 : ℂ)).im with hb
  set a' := airySqrtRe (u + τ) with ha'
  set b' := ((u + τ) ^ (1 / 2 : ℂ)).im with hb'
  have h0 : 0 ≤ a := airySqrtRe_nonneg u
  have h0' : 0 ≤ a' := airySqrtRe_nonneg (u + τ)
  have e1 := airySqrtRe_sq_sub u
  have e2 := airySqrtRe_sq_sub (u + τ)
  have f1 := airySqrtRe_mul_im u
  have f2 := airySqrtRe_mul_im (u + τ)
  have hre : (u + (τ : ℂ)).re = u.re + τ := by simp
  have him : (u + (τ : ℂ)).im = u.im := by simp
  rw [him] at f2
  rw [hre] at e2
  have h : a' * b' = a * b := by linarith
  rw [re_cpow_three_halves_eq_ab, re_cpow_three_halves_eq_ab]
  have key : a' ^ 3 - 3 * a' * b' ^ 2 - (a ^ 3 - 3 * a * b ^ 2 + 3 / 2 * τ * a) =
      (a' - a) ^ 2 * (a' + a / 2) + 3 / 2 * a * (b' - b) ^ 2 := by
    have hτ : τ = a' ^ 2 - b' ^ 2 - (a ^ 2 - b ^ 2) := by linarith
    rw [hτ]
    linear_combination (-3 * b') * h
  have : 0 ≤ (a' - a) ^ 2 * (a' + a / 2) + 3 / 2 * a * (b' - b) ^ 2 := by positivity
  linarith

/-- **(E3)** `e(u + τ) ≤ e(u) exp(-2 τ Re √u)` for all `u ∈ ℂ` and real `τ`
(AIRY_POISSON.md (E3): stated there for `τ ≥ 0`). -/
theorem airyEnv_add_real_le (u : ℂ) (τ : ℝ) :
    airyEnv (u + τ) ≤ airyEnv u * Real.exp (-2 * τ * airySqrtRe u) := by
  unfold airyEnv
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := re_cpow_three_halves_add_ge u τ
  linarith

/-! ### Monotonicity in the imaginary part -/

/-- `e` is nondecreasing in `|Im u|` at fixed `Re u`. -/
theorem airyEnv_mono_im {u u' : ℂ} (hre : u.re = u'.re) (him : |u.im| ≤ |u'.im|) :
    airyEnv u ≤ airyEnv u' := by
  unfold airyEnv
  apply Real.exp_le_exp.mpr
  have hn : ‖u‖ ≤ ‖u'‖ := by
    have h1 : ‖u‖ ^ 2 ≤ ‖u'‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      have h2 := sq_le_sq.mpr him
      have h3 : u.re * u.re = u'.re * u'.re := by rw [hre]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have e1 := airySqrtRe_sq_sub u
  have e2 := airySqrtRe_sq_sub u'
  have f1 := airySqrtRe_sq_add u
  have f2 := airySqrtRe_sq_add u'
  have h0 := airySqrtRe_nonneg u
  have h0' := airySqrtRe_nonneg u'
  set a := airySqrtRe u
  set a' := airySqrtRe u'
  have haa : a ≤ a' := by
    have h1 : a ^ 2 ≤ a' ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ h0 h0' two_ne_zero).mp h1
  rw [re_cpow_three_halves_eq, re_cpow_three_halves_eq, hre]
  have hb2 := sq_nonneg ((u ^ (1 / 2 : ℂ)).im)
  have hx : u'.re ≤ a ^ 2 := by rw [← hre]; nlinarith
  have : 0 ≤ (a' - a) * (2 * (a ^ 2 + a * a' + a' ^ 2) - 3 * u'.re) :=
    mul_nonneg (by linarith) (by nlinarith [mul_nonneg h0 h0', mul_nonneg h0 (sub_nonneg.mpr haa)])
  nlinarith

/-- `e(x + i s)` is nondecreasing in `s ≥ 0`. -/
theorem airyEnv_mono_of_nonneg (x : ℝ) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') :
    airyEnv ((x : ℂ) + (s : ℂ) * I) ≤ airyEnv ((x : ℂ) + (s' : ℂ) * I) := by
  refine airyEnv_mono_im (by simp) ?_
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  simpa using hss

/-! ### (E4) -/

/-- The dilation constant `k = 2^{2/3}` (so that `k^{3/2} = 2`). -/
noncomputable def airyPhiK : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ)

lemma one_le_airyPhiK : 1 ≤ airyPhiK :=
  Real.one_le_rpow (by norm_num) (by norm_num)

lemma airyPhiK_pos : 0 < airyPhiK := lt_of_lt_of_le one_pos one_le_airyPhiK

lemma airyPhiK_rpow : airyPhiK ^ (3 / 2 : ℝ) = 2 := by
  unfold airyPhiK
  rw [← Real.rpow_mul (by norm_num)]
  norm_num

/-- `(k v)^{3/2} = k^{3/2} v^{3/2}` for real `k > 0` (principal branch). -/
lemma cpow_three_halves_ofReal_mul {k : ℝ} (hk : 0 < k) (v : ℂ) :
    ((k : ℂ) * v) ^ (3 / 2 : ℂ) = ((k ^ (3 / 2 : ℝ) : ℝ) : ℂ) * v ^ (3 / 2 : ℂ) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hk0 hv), Complex.log_ofReal_mul hk hv,
    Complex.ofReal_cpow hk.le, Complex.cpow_def_of_ne_zero hv, add_mul, Complex.exp_add]
  rw [Complex.cpow_def_of_ne_zero hk0, Complex.ofReal_log hk.le]
  push_cast
  rfl

/-- The Poisson-type family `Φ_τ(u) = Ai(k (u + τ))`, `k = 2^{2/3}`
(AIRY_POISSON.md Lemma 3: `∂_τ² Φ = 4 (u+τ) Φ`). -/
noncomputable def airyPhi (τ : ℝ) (u : ℂ) : ℂ := airyAiC ((airyPhiK : ℂ) * (u + τ))

/-- `Re (k v)^{3/2} = 2 Re v^{3/2}`. -/
lemma re_cpow_three_halves_dilate (v : ℂ) :
    (((airyPhiK : ℂ) * v) ^ (3 / 2 : ℂ)).re = 2 * (v ^ (3 / 2 : ℂ)).re := by
  rw [cpow_three_halves_ofReal_mul airyPhiK_pos, airyPhiK_rpow, Complex.re_ofReal_mul]

/-- **(E4)** For `τ ≥ 0` and all `u ∈ ℂ`:
`‖Φ_τ(u)‖ ≤ 3 (1+τ)^{1/4} (1+‖u‖)^{-1/4} e(u) exp(-2 τ Re √u)`
(AIRY_POISSON.md (E4), constant `C = 3` from (E1)). -/
theorem airyPhi_norm_le {τ : ℝ} (hτ : 0 ≤ τ) (u : ℂ) :
    ‖airyPhi τ u‖ ≤ 3 * (1 + τ) ^ (1 / 4 : ℝ) * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) * airyEnv u *
      Real.exp (-2 * τ * airySqrtRe u) := by
  set v : ℂ := u + τ with hv
  have h1 := airyAiC_envelope ((airyPhiK : ℂ) * v)
  have hnorm : ‖(airyPhiK : ℂ) * v‖ = airyPhiK * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos airyPhiK_pos]
  rw [re_cpow_three_halves_dilate, hnorm] at h1
  -- the exponential factor
  have hexp : Real.exp (-(2 / 3) * (2 * (v ^ (3 / 2 : ℂ)).re)) = airyEnv v := by
    unfold airyEnv; congr 1; ring
  rw [hexp] at h1
  -- the power factor
  have hpow : (1 + airyPhiK * ‖v‖) ^ (-(1 / 4) : ℝ) ≤ (1 + τ) ^ (1 / 4 : ℝ) * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) := by
    have hle : 1 + ‖v‖ ≤ 1 + airyPhiK * ‖v‖ := by
      nlinarith [one_le_airyPhiK, norm_nonneg v]
    have hu : 1 + ‖u‖ ≤ (1 + τ) * (1 + ‖v‖) := by
      have : ‖u‖ ≤ ‖v‖ + τ := by
        have : u = v - τ := by rw [hv]; ring
        calc ‖u‖ = ‖v - (τ : ℂ)‖ := by rw [← this]
          _ ≤ ‖v‖ + ‖(τ : ℂ)‖ := norm_sub_le _ _
          _ = ‖v‖ + τ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
      nlinarith [norm_nonneg v]
    have p1 : (1 + airyPhiK * ‖v‖) ^ (-(1 / 4) : ℝ) ≤ (1 + ‖v‖) ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
    have p2 : (1 + ‖v‖) ^ (-(1 / 4) : ℝ) ≤ (1 + τ) ^ (1 / 4 : ℝ) * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) := by
      have hpos : 0 < 1 + ‖u‖ := by positivity
      have hpos' : 0 < 1 + ‖v‖ := by positivity
      have hτ1 : 0 < 1 + τ := by linarith
      have q1 : (1 + ‖u‖) ^ (1 / 4 : ℝ) ≤ ((1 + τ) * (1 + ‖v‖)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hpos.le hu (by norm_num)
      rw [Real.mul_rpow hτ1.le hpos'.le] at q1
      have q2 : 0 < (1 + ‖u‖) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hpos _
      have q3 : 0 < (1 + ‖v‖) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hpos' _
      rw [Real.rpow_neg hpos'.le, Real.rpow_neg hpos.le]
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ q3 q2]
      nlinarith
    exact p1.trans p2
  have h2 := airyEnv_add_real_le u τ
  rw [← hv] at h2
  have h4 : 0 ≤ airyEnv v := (airyEnv_pos v).le
  have h3 : 0 ≤ (1 + τ) ^ (1 / 4 : ℝ) * (1 + ‖u‖) ^ (-(1 / 4) : ℝ) := by positivity
  unfold airyPhi
  rw [← hv]
  calc ‖airyAiC ((airyPhiK : ℂ) * v)‖
      ≤ 3 * (1 + airyPhiK * ‖v‖) ^ (-(1 / 4) : ℝ) * airyEnv v := h1
    _ ≤ 3 * ((1 + τ) ^ (1 / 4 : ℝ) * (1 + ‖u‖) ^ (-(1 / 4) : ℝ)) * (airyEnv u *
          Real.exp (-2 * τ * airySqrtRe u)) := by
        gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.Special.airyEnv_add_real_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyEnv_add_real_le

/-- info: 'FormalResearch.Special.airyEnv_mono_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyEnv_mono_im

/-- info: 'FormalResearch.Special.airyPhi_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPhi_norm_le

end FormalResearch.Special
