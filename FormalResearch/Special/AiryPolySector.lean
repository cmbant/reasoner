module

public import FormalResearch.Special.AiryCft2ComboBounds

/-!
# Lower bounds for `a·Ai + b·Ai'` (arbitrary complex `a`, `b`) at a point of a good circle

Sector inputs for the good circles of `N = P·Ai + Q·Ai'` with **polynomial** `P`, `Q` (`general_theorems.tex` Lemma 1.0′(a),(b)).
The coefficients enter only through the two numbers `a = P(u)`, `b = Q(u)`, whose relative size is controlled by the dominance
hypothesis (`AiryPolyAsym`); here they are arbitrary complex numbers.  With `w = √‖u‖`, `E = e(u)`:

* `airyAB_sector_ge` (sector `Re u ≥ -‖u‖/2`, `‖u‖ ≥ 10`): if `16‖b‖w ≤ ‖a‖` or `16‖a‖ ≤ ‖b‖w`, then
  `max(‖a‖, ‖b‖w)² E / (16 π w) ≤ ‖a Ai(u) + b Ai'(u)‖²`  (`Ai ≈ Λ`, `Ai' ≈ -u^{1/2} Λ`);
* `airyAB_neg_sq_ge` (`u = -q²`, `q` in the sector `|arg q| ≤ π/6`, `‖q‖ ≥ 5`, `ξ = (2/3) q³`): if
  (`‖cos(ξ - π/4)‖ ≥ e^{|Im ξ|}/4` and `16‖b‖‖q‖ ≤ ‖a‖`) or (`‖sin(ξ - π/4)‖ ≥ e^{|Im ξ|}/4` and `16‖a‖ ≤ ‖b‖‖q‖`), then
  `e(u) max(‖a‖, ‖b‖‖q‖)² / (64 π ‖q‖) ≤ ‖a Ai(u) + b Ai'(u)‖²`  (two-exponential asymptotics `AiryAsymNegComplex`,
  `AiryCft2DerivNeg`);
* `airyPQ_cos_good`: at a radius with `(2/3)‖q‖³ = π/4 + mπ` (cosine) — the sine analogue, `3π/4 + mπ`, is `airyC2_sin_good`.

The constants are not optimised (numerically the left sides are smaller than the right by a factor `≥ 15`, see `AiryPolyCircle`).
All proved.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### The cosine at a good phase -/

lemma airyPQ_re_cos (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  rw [Complex.cos_eq]
  simp [Complex.cos_ofReal_re, Complex.cosh_ofReal_re]

/-- **The cosine at a good phase.** If `Re ξ ≥ 0`, `‖ξ‖ ≥ 1` and `‖ξ‖ = π/4 + mπ` (`m ∈ ℕ`) then
`‖cos(ξ - π/4)‖ ≥ e^{|Im ξ|}/4`. -/
lemma airyPQ_cos_good {ξ : ℂ} (hre : 0 ≤ ξ.re) (h1 : 1 ≤ ‖ξ‖) (m : ℕ) (hm : ‖ξ‖ = π / 4 + m * π) :
    Real.exp |ξ.im| / 4 ≤ ‖Complex.cos (ξ - (π / 4 : ℂ))‖ := by
  set w : ℂ := ξ - (π / 4 : ℂ) with hw
  have hwr : w.re = ξ.re - π / 4 := by simp [hw]
  have hwi : w.im = ξ.im := by simp [hw]
  by_cases hy : 1 ≤ |ξ.im|
  · have := airyNorm_cos_ge_of_abs_im_ge (w := w) (by simpa [hwi] using hy)
    rwa [hwi] at this
  replace hy := not_le.mp hy
  have hre' : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := airyPQ_re_cos w
  have hcosh := airyCosh_ge_half_exp_abs ξ.im
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

/-! ### Real arithmetic -/

lemma airyPQ_arith (x y E s : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hE : 0 ≤ E) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 125) :
    (16 * y ≤ x → E * x / 8 ≤ E * (x / 4 - y) - E * s * (6 / 5 * x + 41 / 10 * y)) ∧
    (16 * x ≤ y → E * y / 8 ≤ E * (y / 4 - x) - E * s * (6 / 5 * x + 41 / 10 * y)) := by
  have hb : s * (6 / 5 * x + 41 / 10 * y) ≤ 1 / 125 * (6 / 5 * x + 41 / 10 * y) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  constructor
  · intro h
    have : x / 8 ≤ x / 4 - y - s * (6 / 5 * x + 41 / 10 * y) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hE]
  · intro h
    have : y / 8 ≤ y / 4 - x - s * (6 / 5 * x + 41 / 10 * y) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hE]

/-! ### Sector `Re u ≥ -‖u‖/2` -/

/-- **Lower bound in the sector `Re u ≥ -‖u‖/2`** for `a Ai + b Ai'`. -/
theorem airyAB_sector_ge (a b : ℂ) {u : ℂ} (hre : -(‖u‖ / 2) ≤ u.re) (h10 : 10 ≤ ‖u‖)
    (hdom : 16 * ‖b‖ * √‖u‖ ≤ ‖a‖ ∨ 16 * ‖a‖ ≤ ‖b‖ * √‖u‖) :
    max ‖a‖ (‖b‖ * √‖u‖) ^ 2 * airyEnv u / (16 * π * √‖u‖) ≤
      ‖a * airyAiC u + b * deriv airyAiC u‖ ^ 2 := by
  have hz : 0 < ‖u‖ := by linarith
  have hre' : (2 * (1 / 2 : ℝ) ^ 2 - 1) * ‖u‖ ≤ u.re := by nlinarith
  have hA := airyAiC_sector_asymptotic (z := u) (s := 1 / 2) (by norm_num) hz hre'
  have hD := deriv_airyAiC_sector_asymptotic (z := u) (s := 1 / 2) (by norm_num) (by norm_num) hz hre'
  set Λ := airyAiLead u with hΛ
  set Λ' := airyAiDerivLead u with hΛ'
  have hs3 := airyGC_three_le_sqrt h10
  have hX : 30 ≤ ‖u‖ ^ (3 / 2 : ℝ) := by rw [airyRpow_three_halves_eq hz]; nlinarith
  have h7 : (7 / 10 : ℝ) ≤ √(1 / 2 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
  have hden : (21 / 8 : ℝ) ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ) := by
    have h1 : (7 / 80 : ℝ) ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) := by nlinarith
    nlinarith
  have hdenpos : 0 < (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ) := by linarith
  have hη : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 / 20 := by
    rw [div_le_iff₀ hdenpos]; linarith
  have hη' : 17 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_iff₀ hdenpos]; linarith
  have hr0 : 0 < √‖u‖ := Real.sqrt_pos.mpr hz
  have hnΛ' : ‖Λ'‖ = √‖u‖ * ‖Λ‖ := by
    rw [hΛ', airyAiDerivLead, norm_neg, norm_mul, norm_cpow_half]
  have hΛn : 0 ≤ ‖Λ‖ := norm_nonneg _
  set w := √‖u‖ with hw
  set x := ‖a‖ with hx
  set y := ‖b‖ * w with hy
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := by positivity
  have hlead : a * Λ + b * Λ' = Λ * (a - b * u ^ (1 / 2 : ℂ)) := by
    rw [hΛ', airyAiDerivLead]; ring
  have hnlead : ‖Λ‖ * |x - y| ≤ ‖a * Λ + b * Λ'‖ := by
    rw [hlead, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hΛn
    have := abs_norm_sub_norm_le a (b * u ^ (1 / 2 : ℂ))
    rw [norm_mul, norm_cpow_half] at this
    exact this
  have herr : ‖a * airyAiC u + b * deriv airyAiC u - (a * Λ + b * Λ')‖ ≤ ‖Λ‖ * (x / 20 + y / 4) := by
    have e : a * airyAiC u + b * deriv airyAiC u - (a * Λ + b * Λ') =
        a * (airyAiC u - Λ) + b * (deriv airyAiC u - Λ') := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have b1 : x * ‖airyAiC u - Λ‖ ≤ x * (‖Λ‖ / 20) := by
      refine mul_le_mul_of_nonneg_left ?_ hx0
      refine hA.trans ?_
      have := mul_le_mul_of_nonneg_right hη hΛn
      linarith
    have b2 : ‖b‖ * ‖deriv airyAiC u - Λ'‖ ≤ ‖b‖ * (1 / 4 * (w * ‖Λ‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine hD.trans ?_
      rw [hnΛ']
      exact mul_le_mul_of_nonneg_right hη' (by positivity)
    have e1 : x * (‖Λ‖ / 20) + ‖b‖ * (1 / 4 * (w * ‖Λ‖)) = ‖Λ‖ * (x / 20 + y / 4) := by
      rw [hy]; ring
    linarith
  have hmax : ‖Λ‖ * (max x y / 2) ≤ ‖a * airyAiC u + b * deriv airyAiC u‖ := by
    have h1 := norm_sub_norm_le (a * Λ + b * Λ') (a * airyAiC u + b * deriv airyAiC u)
    have h2 : ‖a * Λ + b * Λ' - (a * airyAiC u + b * deriv airyAiC u)‖ ≤ ‖Λ‖ * (x / 20 + y / 4) := by
      rw [norm_sub_rev]; exact herr
    have hd' : 16 * y ≤ x ∨ 16 * x ≤ y := by
      rcases hdom with h | h
      · left; rw [hy]; linarith
      · right; rw [hx]; linarith
    rcases hd' with h | h
    · have hm : max x y = x := max_eq_left (by linarith)
      rw [hm]
      have hxy : |x - y| = x - y := abs_of_nonneg (by linarith)
      rw [hxy] at hnlead
      nlinarith [mul_le_mul_of_nonneg_left (show x / 2 ≤ (x - y) - (x / 20 + y / 4) by linarith) hΛn]
    · have hm : max x y = y := max_eq_right (by linarith)
      rw [hm]
      have hxy : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [hxy] at hnlead
      nlinarith [mul_le_mul_of_nonneg_left (show y / 2 ≤ (y - x) - (x / 20 + y / 4) by linarith) hΛn]
  have hsq : (‖Λ‖ * (max x y / 2)) ^ 2 ≤ ‖a * airyAiC u + b * deriv airyAiC u‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hmax 2
  refine le_trans (le_of_eq ?_) hsq
  have h2 := norm_airyAiLead_sq u
  rw [← hΛ] at h2
  rw [mul_pow, h2, div_pow]
  field_simp
  ring

/-! ### Sector `u = -q²` near the negative axis -/

/-- **Lower bound near the negative axis** for `a Ai + b Ai'` at `u = -q²`. -/
theorem airyAB_neg_sq_ge (a b : ℂ) {q : ℂ} (hq : NegSector q) (h5 : 5 ≤ ‖q‖)
    (hdom : (Real.exp |((2 / 3 : ℂ) * q ^ 3).im| / 4 ≤ ‖Complex.cos ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ∧
        16 * ‖b‖ * ‖q‖ ≤ ‖a‖) ∨
      (Real.exp |((2 / 3 : ℂ) * q ^ 3).im| / 4 ≤ ‖Complex.sin ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ∧
        16 * ‖a‖ ≤ ‖b‖ * ‖q‖)) :
    airyEnv (-(q ^ 2)) * (max ‖a‖ (‖b‖ * ‖q‖) ^ 2 / (64 * π * ‖q‖)) ≤
      ‖a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2))‖ ^ 2 := by
  have hq0 : 0 < ‖q‖ := by linarith
  set ξ : ℂ := (2 / 3 : ℂ) * q ^ 3 with hξ
  set Y := |ξ.im| with hY
  have hmA := airyAiC_neg_complex hq hq0
  have hmD := deriv_airyAiC_neg_complex hq hq0
  rw [← hξ, ← hY] at hmA hmD
  set τ : ℂ := ((π : ℂ) / q) ^ (1 / 2 : ℂ) with hτ
  have hτn : ‖τ‖ = √(π / ‖q‖) := by
    rw [hτ, norm_cpow_half, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  set A : ℝ := √(π / ‖q‖) / π with hA
  have hApos : 0 < A := by positivity
  have hπn : ‖(1 / (π : ℂ))‖ = 1 / π := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  set TA : ℂ := (1 / (π : ℂ)) * τ * Complex.cos (ξ - (π / 4 : ℂ)) with hTA
  set TD : ℂ := (1 / (π : ℂ)) * q * τ * Complex.sin (ξ - (π / 4 : ℂ)) with hTD
  have hcos : ‖Complex.cos (ξ - (π / 4 : ℂ))‖ ≤ Real.exp Y := by
    have := airyC2_cos_le_exp (ξ - (π / 4 : ℂ))
    have e : (ξ - (π / 4 : ℂ)).im = ξ.im := by simp
    rwa [e] at this
  have hsin : ‖Complex.sin (ξ - (π / 4 : ℂ))‖ ≤ Real.exp Y := by
    have h2 : Complex.sin (ξ - (π / 4 : ℂ)) = Complex.cos (ξ - (π / 4 : ℂ) - (π / 2 : ℂ)) :=
      (Complex.cos_sub_pi_div_two _).symm
    rw [h2]
    have := airyC2_cos_le_exp (ξ - (π / 4 : ℂ) - (π / 2 : ℂ))
    have e : (ξ - (π / 4 : ℂ) - (π / 2 : ℂ)).im = ξ.im := by simp
    rwa [e] at this
  have nTA : ‖TA‖ ≤ A * Real.exp Y := by
    rw [hTA, norm_mul, norm_mul, hπn, hτn]
    have : 1 / π * √(π / ‖q‖) = A := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hcos hApos.le
  have nTD : ‖TD‖ ≤ A * ‖q‖ * Real.exp Y := by
    rw [hTD, norm_mul, norm_mul, norm_mul, hπn, hτn]
    have : 1 / π * ‖q‖ * √(π / ‖q‖) = A * ‖q‖ := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsin (by positivity)
  set Ee : ℝ := A * Real.exp Y with hEe
  have hEe0 : 0 < Ee := by positivity
  set x := ‖a‖ with hx
  set y := ‖b‖ * ‖q‖ with hy
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := by positivity
  set s : ℝ := 1 / ‖q‖ ^ 3 with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 / 125 := by
    rw [hs]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) h5 3]
  have herr : ‖a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2)) - (a * TA + b * TD)‖ ≤
      Ee * s * (6 / 5 * x + 41 / 10 * y) := by
    have e : a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2)) - (a * TA + b * TD) =
        a * (airyAiC (-(q ^ 2)) - TA) + b * (deriv airyAiC (-(q ^ 2)) - TD) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have b1 : x * ‖airyAiC (-(q ^ 2)) - TA‖ ≤ x * (6 / 5 * Ee * s) := by
      refine mul_le_mul_of_nonneg_left ?_ hx0
      have : (6 / 5 * Real.exp Y * (√(π / ‖q‖) / π) / ‖q‖ ^ 3) = 6 / 5 * Ee * s := by
        rw [hEe, hs, hA]; ring
      rw [← this]; exact hmA
    have b2 : ‖b‖ * ‖deriv airyAiC (-(q ^ 2)) - TD‖ ≤ ‖b‖ * (41 / 10 * Ee * (s * ‖q‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have : (41 / 10 * Real.exp Y * (√(π / ‖q‖) / π) / ‖q‖ ^ 2) = 41 / 10 * Ee * (s * ‖q‖) := by
        rw [hEe, hs, hA]; field_simp
      rw [← this]; exact hmD
    have e1 : x * (6 / 5 * Ee * s) + ‖b‖ * (41 / 10 * Ee * (s * ‖q‖)) = Ee * s * (6 / 5 * x + 41 / 10 * y) := by
      rw [hy]; ring
    linarith
  have hari := airyPQ_arith x y Ee s hx0 hy0 hEe0.le hs0 hs1
  have hfin : Ee * (max x y / 8) ≤ ‖a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2))‖ := by
    have h1 := norm_sub_norm_le (a * TA + b * TD) (a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2)))
    have h2 : ‖a * TA + b * TD - (a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2)))‖ ≤
        Ee * s * (6 / 5 * x + 41 / 10 * y) := by
      rw [norm_sub_rev]; exact herr
    rcases hdom with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · have hd' : 16 * y ≤ x := by rw [hy]; linarith
      have hm : max x y = x := max_eq_left (by linarith)
      rw [hm]
      have hmain : Ee * (x / 4 - y) ≤ ‖a * TA + b * TD‖ := by
        have h3 := norm_sub_norm_le (a * TA) (-(b * TD))
        rw [sub_neg_eq_add, norm_neg, norm_mul a TA, norm_mul b TD] at h3
        have hTAn : ‖TA‖ = A * ‖Complex.cos (ξ - (π / 4 : ℂ))‖ := by
          rw [hTA, norm_mul, norm_mul, hπn, hτn]
          have : 1 / π * √(π / ‖q‖) = A := by rw [hA]; ring
          rw [this]
        have h4 : x * (Ee / 4) ≤ x * ‖TA‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hx0
          rw [hTAn, hEe]
          have := mul_le_mul_of_nonneg_left hc hApos.le
          linarith
        have h5' : ‖b‖ * ‖TD‖ ≤ ‖b‖ * (A * ‖q‖ * Real.exp Y) := mul_le_mul_of_nonneg_left nTD (norm_nonneg _)
        have e2 : ‖b‖ * (A * ‖q‖ * Real.exp Y) = y * Ee := by rw [hy, hEe]; ring
        linarith
      have := hari.1 hd'
      linarith
    · have hd' : 16 * x ≤ y := by rw [hy]; linarith
      have hm : max x y = y := max_eq_right (by linarith)
      rw [hm]
      have hmain : Ee * (y / 4 - x) ≤ ‖a * TA + b * TD‖ := by
        have h3 := norm_sub_norm_le (b * TD) (-(a * TA))
        rw [sub_neg_eq_add, add_comm, norm_neg, norm_mul b TD, norm_mul a TA] at h3
        have hTDn : ‖TD‖ = A * ‖q‖ * ‖Complex.sin (ξ - (π / 4 : ℂ))‖ := by
          rw [hTD, norm_mul, norm_mul, norm_mul, hπn, hτn]
          have : 1 / π * ‖q‖ * √(π / ‖q‖) = A * ‖q‖ := by rw [hA]; ring
          rw [this]
        have h4 : ‖b‖ * (A * ‖q‖ * (Real.exp Y / 4)) ≤ ‖b‖ * ‖TD‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hTDn]
          exact mul_le_mul_of_nonneg_left hc (by positivity)
        have h5' : x * ‖TA‖ ≤ x * (A * Real.exp Y) := mul_le_mul_of_nonneg_left nTA hx0
        have e2 : ‖b‖ * (A * ‖q‖ * (Real.exp Y / 4)) = y * Ee / 4 := by rw [hy, hEe]; ring
        have e3 : x * (A * Real.exp Y) = x * Ee := by rw [hEe]
        linarith
      have := hari.2 hd'
      linarith
  rw [airyEnv_neg_sq hq]
  have hEY : Real.exp (2 * |((2 / 3 : ℂ) * q ^ 3).im|) = Real.exp Y ^ 2 := by
    rw [← hY, ← Real.exp_nat_mul]; norm_num
  have hsq : (Ee * (max x y / 8)) ^ 2 ≤ ‖a * airyAiC (-(q ^ 2)) + b * deriv airyAiC (-(q ^ 2))‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfin 2
  have hAsq : A ^ 2 = 1 / (π * ‖q‖) := by
    rw [hA, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have e : (Ee * (max x y / 8)) ^ 2 = Real.exp Y ^ 2 * (max x y ^ 2 / (64 * π * ‖q‖)) := by
    have : (Ee * (max x y / 8)) ^ 2 = A ^ 2 * Real.exp Y ^ 2 * (max x y ^ 2 / 64) := by rw [hEe]; ring
    rw [this, hAsq]
    field_simp
  rw [hEY, ← e]
  exact hsq

/-- info: 'FormalResearch.Special.airyPQ_cos_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_cos_good

/-- info: 'FormalResearch.Special.airyAB_sector_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAB_sector_ge

/-- info: 'FormalResearch.Special.airyAB_neg_sq_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAB_neg_sq_ge

end FormalResearch.Special
