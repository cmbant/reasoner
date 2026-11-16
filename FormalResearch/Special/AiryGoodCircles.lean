module

public import FormalResearch.Special.AiryAsymNegComplex

/-!
# Good circles for `Ai` (E2)

Statement formalised (CFT/PR240, `AIRY_POISSON.md` (E2), `GENERAL_THEOREMS.md` Lemma 1.0 with `α = 0`):
for every integer `k ≥ 10` there is a radius `r ∈ [k, k+1]` such that on the whole circle `|u| = r`

`‖Ai(u)‖² ≥ (1/(25π)) (1 + r)^{-1/2} e(u)`,   `e(u) = exp(-(4/3) Re u^{3/2})`.

(`good_circle_exists`; the radii are explicit: `(2/3) r^{3/2} = π/4 + mπ`, `m ∈ ℕ`, `radius = airyGoodRadius`.)

Proof (no Olver theory): on `Re u ≥ -|u|/2` the sector asymptotics of `AiryAsymSector` (`s = 1/2`,
`‖Ai‖² ≥ e/(16π√|u|)`); on `Re u < -|u|/2` write `u = -q²`, `q = (-u)^{1/2}`, `|arg q| < π/6`, and use the
two-exponential asymptotics `AiryAsymNegComplex` with the phase `ξ = (2/3)q³` (`|ξ| = (2/3) r^{3/2} = π/4 + mπ`):
`|cos(ξ - π/4)| ≥ e^{|Im ξ|}/4` there, the remainder is `≤ (6/5) r^{-3/2} · e^{|Im ξ|} √(π/|q|)/π`, and
`e(u) = e^{2|Im ξ|}`.

Numerical check (mpmath, 20 digits; `k ∈ {10,…,59, 80, 120, 160, 200}`, 721 angles on the upper half circle):
`min_k min_{|u|=r_k} ‖Ai(u)‖²/((1+r)^{-1/2} e(u)) = 0.0798 ≈ 1/(4π)` (attained near the positive axis), so the proved
constant `1/(25π) = 0.0127` is conservative.

Not formalised: the `P·Ai + Q·Ai'` version (`GENERAL_THEOREMS.md` Lemma 1.0′), the residue-defect formula
(Theorem D) and its `|R_±| ≤ C/e` bound, the uniform-in-`α` version of Lemma 1.0; radii `k < 10`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### A lower bound for `|cos(ξ - π/4)|` at the good phases -/

lemma re_cos_eq (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  rw [Complex.cos_eq]
  simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re]

lemma cosh_ge_half_exp_abs (y : ℝ) : Real.exp |y| / 2 ≤ Real.cosh y := by
  rw [Real.cosh_eq]
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; have := Real.exp_pos (-y); linarith
  · rw [h]; have := Real.exp_pos y; linarith

/-- Large imaginary part: `|cos w| ≥ e^{|Im w|}/4` once `|Im w| ≥ 1`. -/
lemma norm_cos_ge_of_abs_im_ge {w : ℂ} (h : 1 ≤ |w.im|) :
    Real.exp |w.im| / 4 ≤ ‖Complex.cos w‖ := by
  have h2 : 2 * Complex.cos w = cexp (w * I) + cexp (-w * I) := Complex.two_cos w
  have nA : ‖cexp (w * I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]; simp
  have nB : ‖cexp (-w * I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]; simp
  have hb : ‖cexp (-w * I) - (-cexp (w * I))‖ = ‖2 * Complex.cos w‖ := by
    rw [h2]; congr 1; ring
  have hd := abs_norm_sub_norm_le (cexp (-w * I)) (-cexp (w * I))
  rw [hb, norm_neg, nA, nB, norm_mul, Complex.norm_two] at hd
  have e2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  rcases abs_cases w.im with ⟨hy, _⟩ | ⟨hy, _⟩
  · rw [hy] at h ⊢
    have h3 : Real.exp (-w.im) * Real.exp w.im = 1 := by rw [← Real.exp_add]; simp
    have h4 : Real.exp 2 ≤ Real.exp w.im * Real.exp w.im := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hp := Real.exp_pos w.im
    have hq := Real.exp_pos (-w.im)
    -- e^{-y} ≤ e^{y}/2
    have h5 : Real.exp (-w.im) ≤ Real.exp w.im / 2 := by nlinarith
    have : Real.exp w.im - Real.exp (-w.im) ≤ |Real.exp w.im - Real.exp (-w.im)| := le_abs_self _
    nlinarith [abs_sub_comm (Real.exp (-w.im)) (Real.exp w.im)]
  · rw [hy] at h ⊢
    have h3 : Real.exp (-w.im) * Real.exp w.im = 1 := by rw [← Real.exp_add]; simp
    have h4 : Real.exp 2 ≤ Real.exp (-w.im) * Real.exp (-w.im) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hp := Real.exp_pos w.im
    have hq := Real.exp_pos (-w.im)
    have h5 : Real.exp w.im ≤ Real.exp (-w.im) / 2 := by nlinarith
    have : Real.exp (-w.im) - Real.exp w.im ≤ |Real.exp (-w.im) - Real.exp w.im| := le_abs_self _
    nlinarith [abs_sub_comm (Real.exp w.im) (Real.exp (-w.im))]

/-- **The cosine at a good phase.** If `Re ξ ≥ 0`, `‖ξ‖ = π/4 + mπ` (`m ∈ ℕ`) and `‖ξ‖ ≥ 1`, then
`‖cos(ξ - π/4)‖ ≥ e^{|Im ξ|}/4`. -/
lemma norm_cos_good {ξ : ℂ} (hre : 0 ≤ ξ.re) (m : ℕ) (hm : ‖ξ‖ = π / 4 + m * π) (h1 : 1 ≤ ‖ξ‖) :
    Real.exp |ξ.im| / 4 ≤ ‖Complex.cos (ξ - (π / 4 : ℂ))‖ := by
  set w : ℂ := ξ - (π / 4 : ℂ) with hw
  have hwr : w.re = ξ.re - π / 4 := by simp [hw]
  have hwi : w.im = ξ.im := by simp [hw]
  by_cases hy : 1 ≤ |ξ.im|
  · have := norm_cos_ge_of_abs_im_ge (w := w) (by rw [hwi]; exact hy)
    rw [hwi] at this
    exact this
  replace hy := not_le.mp hy
  have hre' : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := re_cos_eq w
  have hcosh := cosh_ge_half_exp_abs ξ.im
  -- d = ‖ξ‖ - Re ξ
  set d := ‖ξ‖ - ξ.re with hd
  have hd0 : 0 ≤ d := by
    have := Complex.re_le_norm ξ; linarith
  have hsq : d * (‖ξ‖ + ξ.re) = ξ.im ^ 2 := by
    have := sq_norm_eq ξ
    rw [hd]; nlinarith
  have hy2 : ξ.im ^ 2 < 1 := by
    have : |ξ.im| ^ 2 < 1 := by nlinarith [abs_nonneg ξ.im]
    rwa [sq_abs] at this
  have hd1 : d ≤ 1 := by nlinarith
  have hx : w.re = m * π - d := by rw [hwr, hd]; linarith
  have hcos : |Real.cos w.re| = Real.cos d := by
    rw [hx, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, zero_mul, add_zero]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩)
  have hc12 : 1 / 2 ≤ Real.cos d := by
    have := Real.one_sub_sq_div_two_le_cos (x := d)
    nlinarith
  have hre2 : ‖Complex.cos w‖ ≥ |(Complex.cos w).re| := Complex.abs_re_le_norm _
  rw [hre', abs_mul, hcos, abs_of_pos (Real.cosh_pos _), hwi] at hre2
  have hep := Real.exp_pos |ξ.im|
  nlinarith

/-! ### The good radii -/

lemma rpow_three_halves_eq {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow]

lemma three_le_sqrt {x : ℝ} (hx : 10 ≤ x) : 3 ≤ √x :=
  Real.le_sqrt_of_sq_le (by nlinarith)

/-- `(x+1)^{3/2} ≥ x^{3/2} + (3/2) √x` (Bernoulli). -/
lemma rpow_three_halves_succ_ge {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) + 3 / 2 * √x ≤ (x + 1) ^ (3 / 2 : ℝ) := by
  have h1x : -1 ≤ 1 / x := by
    have : 0 < 1 / x := by positivity
    linarith
  have hb := one_add_mul_self_le_rpow_one_add h1x (p := 3 / 2) (by norm_num)
  have e1 : x + 1 = x * (1 + 1 / x) := by field_simp
  rw [e1, Real.mul_rpow hx.le (by positivity), rpow_three_halves_eq hx]
  have e2 : x * √x * (1 + 3 / 2 * (1 / x)) = x * √x + 3 / 2 * √x := by field_simp
  rw [← e2]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Every `[k, k+1]`, `k ≥ 10`, contains a radius `r` with `(2/3) r^{3/2} = π/4 + mπ`, `m ∈ ℕ`. -/
lemma good_radius_exists (k : ℕ) (hk : 10 ≤ k) :
    ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧ ∃ m : ℕ, 2 / 3 * r ^ (3 / 2 : ℝ) = π / 4 + m * π := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  set G : ℝ := 2 / 3 * (k : ℝ) ^ (3 / 2 : ℝ) with hG
  have hk32 := rpow_three_halves_eq hkpos
  have hs3 := three_le_sqrt hk'
  have hG20 : 20 ≤ G := by rw [hG, hk32]; nlinarith
  have hpi := Real.pi_lt_d2
  have hpipos := Real.pi_pos
  set a : ℝ := (G - π / 4) / π with ha
  have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg <;> linarith
  set m : ℕ := ⌈a⌉₊ with hm
  have hm1 : a ≤ m := Nat.le_ceil a
  have hm2 : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hmπ1 : G - π / 4 ≤ m * π := by
    have := mul_le_mul_of_nonneg_right hm1 hpipos.le
    rwa [ha, div_mul_cancel₀ _ hpipos.ne'] at this
  have hmπ2 : (m : ℝ) * π < G - π / 4 + π := by
    have := mul_lt_mul_of_pos_right hm2 hpipos
    rwa [add_mul, ha, div_mul_cancel₀ _ hpipos.ne', one_mul] at this
  set t : ℝ := π / 4 + m * π with ht
  have ht0 : 0 ≤ 3 / 2 * t := by positivity
  set r : ℝ := (3 / 2 * t) ^ (2 / 3 : ℝ) with hr
  have hr32 : r ^ (3 / 2 : ℝ) = 3 / 2 * t := by
    rw [hr, ← Real.rpow_mul ht0]; norm_num
  have hr0 : 0 ≤ r := Real.rpow_nonneg ht0 _
  refine ⟨r, ?_, ?_, m, ?_⟩
  · rw [← Real.rpow_le_rpow_iff hkpos.le hr0 (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ1
    nlinarith
  · have hsucc := rpow_three_halves_succ_ge hkpos
    have hs3' : π ≤ √(k : ℝ) :=
      le_trans hpi.le (Real.le_sqrt_of_sq_le (by norm_num; linarith))
    rw [← Real.rpow_le_rpow_iff hr0 (by positivity) (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ2
    nlinarith
  · rw [hr32]; ring

/-! ### The sector `Re u < -|u|/2`: `u = -q²` -/

lemma im_cube' (w : ℂ) : (w ^ 3).im = 3 * w.re ^ 2 * w.im - w.im ^ 3 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

lemma NegSector.re_sq_ge {q : ℂ} (h : NegSector q) : 3 * q.im ^ 2 ≤ q.re ^ 2 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e := sq_norm_eq q
  have h1 : (√3 / 2 * ‖q‖) ^ 2 ≤ q.re ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have : (√3 / 2 * ‖q‖) ^ 2 = 3 / 4 * ‖q‖ ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring
  nlinarith

lemma NegSector.im_cube_sign {q : ℂ} (h : NegSector q) :
    (q.im ≤ 0 → (q ^ 3).im ≤ 0) ∧ (0 ≤ q.im → 0 ≤ (q ^ 3).im) := by
  have h1 := h.re_sq_ge
  have e : (q ^ 3).im = q.im * (3 * q.re ^ 2 - q.im ^ 2) := by rw [im_cube']; ring
  have h2 : 0 ≤ 3 * q.re ^ 2 - q.im ^ 2 := by nlinarith [sq_nonneg q.im]
  rw [e]
  exact ⟨fun hb => mul_nonpos_of_nonpos_of_nonneg hb h2, fun hb => mul_nonneg hb h2⟩

/-- `e(-q²) = exp(2 |Im ξ|)` for `ξ = (2/3) q³`, `|arg q| ≤ π/6`. -/
lemma airyEnv_neg_sq {q : ℂ} (h : NegSector q) :
    airyEnv (-(q ^ 2)) = Real.exp (2 * |((2 / 3 : ℂ) * q ^ 3).im|) := by
  set w := (-(q ^ 2)) ^ (1 / 2 : ℂ) with hw
  have hw2 : w ^ 2 = (I * q) ^ 2 := by
    rw [hw, cpow_half_sq, mul_pow, Complex.I_sq]; ring
  have hre : 0 ≤ w.re := cpow_half_re_nonneg _
  have key : ((-(q ^ 2)) ^ (3 / 2 : ℂ)).re = -|(q ^ 3).im| := by
    rw [← cpow_half_cube, ← hw]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hw2 with h1 | h1
    · have him : q.im ≤ 0 := by
        rw [h1] at hre; simpa using hre
      rw [h1, mul_pow, show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]
      have := (h.im_cube_sign).1 him
      rw [abs_of_nonpos this]
      simp
    · have him : 0 ≤ q.im := by
        rw [h1] at hre; simpa using hre
      have e3 : (-(I * q)) ^ 3 = I * q ^ 3 := by linear_combination (-I * q ^ 3) * Complex.I_sq
      rw [h1, e3]
      have := (h.im_cube_sign).2 him
      rw [abs_of_nonneg this]
      simp
  unfold airyEnv
  rw [key]
  congr 1
  have : ((2 / 3 : ℂ) * q ^ 3).im = 2 / 3 * (q ^ 3).im := by
    simp [Complex.mul_im]
  rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
  ring

/-- **Lower bound near the negative axis at a good radius.** For `q` with `|arg q| ≤ π/6`, `‖q‖ ≥ 3` and
`(2/3)‖q‖³ = π/4 + mπ` (`m ∈ ℕ`): `‖Ai(-q²)‖² ≥ e(-q²)/(25 π ‖q‖)`. -/
theorem airyAiC_neg_sq_ge {q : ℂ} (hq : NegSector q) (m : ℕ) (hm : 2 / 3 * ‖q‖ ^ 3 = π / 4 + m * π)
    (h3 : 3 ≤ ‖q‖) : airyEnv (-(q ^ 2)) / (25 * π * ‖q‖) ≤ ‖airyAiC (-(q ^ 2))‖ ^ 2 := by
  have hq0 : 0 < ‖q‖ := by linarith
  set ξ : ℂ := (2 / 3 : ℂ) * q ^ 3 with hξ
  have hnξ : ‖ξ‖ = 2 / 3 * ‖q‖ ^ 3 := by
    rw [hξ, norm_mul, norm_pow]; norm_num
  have hξ1 : 1 ≤ ‖ξ‖ := by
    rw [hnξ]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 3]
  have hξre : 0 ≤ ξ.re := by
    have h1 := hq.re_sq_ge
    have h0 := hq.re_nonneg
    have : ξ.re = 2 / 3 * (q.re * (q.re ^ 2 - 3 * q.im ^ 2)) := by
      rw [hξ]; simp [Complex.mul_re, re_cube]; ring
    rw [this]
    have : 0 ≤ q.re * (q.re ^ 2 - 3 * q.im ^ 2) := mul_nonneg h0 (by linarith)
    positivity
  have hcos := norm_cos_good hξre m (by rw [hnξ]; exact hm) hξ1
  set Y := |ξ.im| with hY
  have hmain := airyAiC_neg_complex hq hq0
  set M : ℂ := (1 / (π : ℂ)) * ((π : ℂ) / q) ^ (1 / 2 : ℂ) * Complex.cos (ξ - (π / 4 : ℂ)) with hM
  have hτ : ‖((π : ℂ) / q) ^ (1 / 2 : ℂ)‖ = √(π / ‖q‖) := by
    rw [norm_cpow_half, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hMn : ‖M‖ = √(π / ‖q‖) / π * ‖Complex.cos (ξ - (π / 4 : ℂ))‖ := by
    rw [hM, norm_mul, norm_mul, hτ, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    ring
  set A : ℝ := √(π / ‖q‖) / π with hA
  have hApos : 0 < A := by positivity
  have hq27 : (27 : ℝ) ≤ ‖q‖ ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 3]
  have herr : 6 / 5 * Real.exp Y * A / ‖q‖ ^ 3 ≤ 1 / 20 * (A * Real.exp Y) := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.exp_pos Y
    nlinarith [mul_pos hApos this]
  have hlow : 1 / 5 * (A * Real.exp Y) ≤ ‖airyAiC (-(q ^ 2))‖ := by
    have h1 : ‖M‖ - ‖airyAiC (-(q ^ 2)) - M‖ ≤ ‖airyAiC (-(q ^ 2))‖ := by
      have := norm_sub_norm_le M (M - airyAiC (-(q ^ 2)))
      rw [norm_sub_rev M (airyAiC (-(q ^ 2)))] at this
      simpa using this
    have h2 : A * (Real.exp Y / 4) ≤ ‖M‖ := by
      rw [hMn]; exact mul_le_mul_of_nonneg_left hcos hApos.le
    have : ‖airyAiC (-(q ^ 2)) - M‖ ≤ 1 / 20 * (A * Real.exp Y) := hmain.trans herr
    nlinarith
  rw [airyEnv_neg_sq hq]
  have hEY : Real.exp (2 * Y) = Real.exp Y ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq : (1 / 5 * (A * Real.exp Y)) ^ 2 ≤ ‖airyAiC (-(q ^ 2))‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlow 2
  refine le_trans (le_of_eq ?_) hsq
  have hAsq : A ^ 2 = 1 / (π * ‖q‖) := by
    rw [hA, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hEY, mul_pow, mul_pow, hAsq]
  field_simp
  ring

/-! ### The good-circle theorem -/

lemma onePlus_rpow_le {r : ℝ} (hr : 0 < r) : (1 + r) ^ (-(1 / 2) : ℝ) ≤ 1 / √r := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
  apply inv_anti₀ (Real.sqrt_pos.mpr hr)
  exact Real.sqrt_le_sqrt (by linarith)

lemma NegSector_of_re_lt {u : ℂ} (hu : u.re < -(‖u‖ / 2)) : NegSector ((-u) ^ (1 / 2 : ℂ)) := by
  have e1 := airySqrtRe_sq_sub (-u)
  have e2 := airySqrtRe_sq_add (-u)
  rw [norm_neg] at e2
  have hn : ‖(-u) ^ (1 / 2 : ℂ)‖ ^ 2 = ‖u‖ := by rw [norm_cpow_half_sq, norm_neg]
  have h0 := airySqrtRe_nonneg (-u)
  unfold NegSector
  have : (√3 / 2 * ‖(-u) ^ (1 / 2 : ℂ)‖) ^ 2 ≤ ((-u) ^ (1 / 2 : ℂ)).re ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), hn]
    have : ((-u) ^ (1 / 2 : ℂ)).re = airySqrtRe (-u) := rfl
    rw [this]
    simp only [Complex.neg_re] at e1
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) h0 two_ne_zero).mp this

/-- **Good circles (E2).** For every integer `k ≥ 10` there is a radius `r ∈ [k, k+1]` such that for all `u`
with `|u| = r`: `(1/(25π)) (1+r)^{-1/2} e(u) ≤ ‖Ai(u)‖²`, `e(u) = exp(-(4/3) Re u^{3/2})`.
(`GENERAL_THEOREMS.md` Lemma 1.0 with `α = 0`; the radius satisfies `(2/3) r^{3/2} ∈ π/4 + πℕ`.) -/
theorem good_circle_exists (k : ℕ) (hk : 10 ≤ k) :
    ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧ ∀ u : ℂ, ‖u‖ = r →
      1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2 := by
  obtain ⟨r, hr1, hr2, m, hm⟩ := good_radius_exists k hk
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hr10 : 10 ≤ r := by linarith
  have hrpos : 0 < r := by linarith
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  have hs3 := three_le_sqrt hr10
  have hpi := Real.pi_pos
  have hr32 : r ^ (3 / 2 : ℝ) = r * √r := rpow_three_halves_eq hrpos
  have henv := airyEnv_pos u
  have hsqrt_pos : 0 < √r := by linarith
  have hw := onePlus_rpow_le hrpos
  -- common target: ≤ e(u)/(c π √r)
  by_cases hcase : -(‖u‖ / 2) ≤ u.re
  · -- sector |arg u| ≤ 2π/3
    have hz : 0 < ‖u‖ := by rw [hu]; exact hrpos
    have hη : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 / 2 := by
      rw [hu, hr32]
      have h7 : (7 / 10 : ℝ) ≤ √(1 / 2 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
      have hden : (7 / 80 : ℝ) * (r * √r) ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * (r * √r) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 (by norm_num : (0:ℝ) ≤ (1 / 2) ^ 3))
          (by positivity : (0:ℝ) ≤ r * √r)
        nlinarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hr10 hs3 (by norm_num) (by linarith)]
    have := airyAiC_sq_ge_sector (z := u) (s := 1 / 2) (by norm_num) hz (by nlinarith) hη
    rw [hu] at this
    refine le_trans ?_ this
    have h1 : 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) ≤ 1 / (16 * π * √r) := by
      calc 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) ≤ 1 / (25 * π) * (1 / √r) := by gcongr
        _ ≤ 1 / (16 * π * √r) := by
          rw [one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
          nlinarith
    calc 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ 1 / (16 * π * √r) * airyEnv u := by gcongr
      _ = airyEnv u / (16 * π * √r) := by ring
  · -- sector near the negative axis
    have hlt : u.re < -(‖u‖ / 2) := not_le.mp hcase
    set q : ℂ := (-u) ^ (1 / 2 : ℂ) with hqdef
    have hq : NegSector q := NegSector_of_re_lt hlt
    have hq2 : q ^ 2 = -u := cpow_half_sq _
    have hqn : ‖q‖ ^ 2 = r := by rw [hqdef, norm_cpow_half_sq, norm_neg, hu]
    have hq3 : ‖q‖ ^ 3 = r ^ (3 / 2 : ℝ) := by
      rw [hqdef, norm_cpow_half_pow_three, norm_neg, hu]
    have hqs : ‖q‖ = √r := by
      rw [← hqn, Real.sqrt_sq (norm_nonneg _)]
    have := airyAiC_neg_sq_ge hq m (by rw [hq3]; exact hm) (by rw [hqs]; exact hs3)
    have e : -(q ^ 2) = u := by rw [hq2, neg_neg]
    rw [e, hqs] at this
    refine le_trans ?_ this
    calc 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ 1 / (25 * π) * (1 / √r) * airyEnv u := by
          gcongr
      _ = airyEnv u / (25 * π * √r) := by field_simp

/-- Ai has no zero on a good circle (zero-free circles for the residue/defect formula). -/
theorem good_circle_airyAiC_ne_zero (k : ℕ) (hk : 10 ≤ k) :
    ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧ ∀ u : ℂ, ‖u‖ = r → airyAiC u ≠ 0 := by
  obtain ⟨r, h1, h2, h⟩ := good_circle_exists k hk
  refine ⟨r, h1, h2, fun u hu h0 => ?_⟩
  have := h u hu
  rw [h0, norm_zero] at this
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have : 0 < 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u := by
    have := airyEnv_pos u
    have : 0 < (1 + r) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  linarith

/-- info: 'FormalResearch.Special.good_circle_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.good_circle_exists

end FormalResearch.Special
