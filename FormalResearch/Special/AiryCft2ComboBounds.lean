module

public import FormalResearch.Special.AiryCft2DerivNeg
public import FormalResearch.Special.AiryCft2ComboAlg

/-!
# Good circles for `N = P·Ai + Q·Ai'` (`Q ≠ 0`): the lower bound and the ratio bound `‖M/N ∓ i‖ ≤ C/e`

Formalises (CFT/PR240) `GENERAL_THEOREMS.md` Lemma 1.0 (Clark functions `ψ_α = cos α Ai - sin α Ai'`, `sin α ≠ 0`)
and the constant-coefficient case `p = q = 0` of Lemma 1.0′ (`κ = 1/4`), for **real constants** `P, Q` with `Q ≠ 0`:

`airyNC_good_circle`: there are `C > 0` and `k₀` such that every `[k, k+1]`, `k ≥ k₀`, contains a radius `r` with, on
the whole circle `|u| = r`,

* `(Q²/(256π)) √r · e(u) ≤ ‖N(u)‖²`  (so `N ≠ 0` there; `e(u) = exp(-(4/3) Re u^{3/2})`);
* `‖M(u)/N(u) - i‖ e(u) ≤ C` for `Im u ≥ 0`, and `‖M(u)/N(u) + i‖ e(u) ≤ C` for `Im u ≤ 0`,

with `C = 40 √π (3|P| + 5|Q|)/|Q|` and `k₀ = ⌈64 (1 + P²/Q²)⌉`.  The radii are explicit:
`(2/3) r^{3/2} = 3π/4 + mπ`, `m ∈ ℕ` (the zeros of `sin(ξ - π/4)` are avoided).

Proof: on `Re u ≥ -|u|/2` the sector asymptotics of `AiryAsymSector` (`Ai ≈ Λ`, `Ai' ≈ -u^{1/2} Λ`, so `N ≈ Λ (P - Q u^{1/2})`,
dominated by the `Q` term once `|u|^{1/2} ≥ 8|P|/|Q|`); on `Re u < -|u|/2` write `u = -q²`, use the two-exponential
asymptotics of `Ai` (`airyAiC_neg_complex`) and `Ai'` (`deriv_airyAiC_neg_complex`), whose combination is
`(1/π) τ (P cos(ξ - π/4) + Q q sin(ξ - π/4))`, `τ = (π/q)^{1/2}`, `ξ = (2/3) q³`, and at the radii above
`|sin(ξ - π/4)| ≥ e^{|Im ξ|}/4`; the numerator `M - iN` is bounded by `airyMC_sub_I_mul_sq_le`.

Numerical check (mpmath, 25 digits; `(P,Q) ∈ {(1,-1), (0.3,-1), (-2,0.5), (1,1), (5,-1), (0,1)}`, radii with `m` up to
`400`, `r ≥ max(64, 64 P²/Q²)`, 121 angles on the upper half circle): `min ‖N‖²/((Q²/(256π))√r e) = 49`, and
`max ‖M/N - i‖ e = 2.56` (against the proved `C`).  The constants are not optimised.

Not formalised: polynomial coefficients `P, Q` (Lemma 1.0′ with `deg ≥ 1`, needed for the Hermite-Biehler extensions of
`SOFT_EDGE_THEOREMS.md` Lemma 4.4/4.6), uniformity in `α` over a compact set, and radii `k < k₀`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-! ### Elementary bounds -/

lemma airyC2_norm_real_mul (a : ℝ) (z : ℂ) : ‖(a : ℂ) * z‖ = |a| * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

lemma airyC2_re_sin (w : ℂ) : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
  rw [Complex.sin_eq]
  simp [Complex.sin_ofReal_re, Complex.cosh_ofReal_re]

lemma airyC2_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h2 : 2 * Complex.cos w = cexp (w * I) + cexp (-w * I) := Complex.two_cos w
  have nA : ‖cexp (w * I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have nB : ‖cexp (-w * I)‖ = Real.exp w.im := by rw [Complex.norm_exp]; simp
  have h3 : ‖2 * Complex.cos w‖ ≤ 2 * Real.exp |w.im| := by
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    rw [nA, nB]
    have a1 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs _)
    have a2 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self _)
    linarith
  rw [norm_mul, Complex.norm_two] at h3
  linarith

/-- **The sine at a good phase.** If `Re ξ ≥ 0` and `‖ξ‖ = 3π/4 + mπ` (`m ∈ ℕ`) then `‖sin(ξ - π/4)‖ ≥ e^{|Im ξ|}/4`. -/
lemma airyC2_sin_good {ξ : ℂ} (hre : 0 ≤ ξ.re) (m : ℕ) (hm : ‖ξ‖ = 3 * π / 4 + m * π) :
    Real.exp |ξ.im| / 4 ≤ ‖Complex.sin (ξ - (π / 4 : ℂ))‖ := by
  set w : ℂ := ξ - (π / 4 : ℂ) with hw
  have hwr : w.re = ξ.re - π / 4 := by simp [hw]
  have hwi : w.im = ξ.im := by simp [hw]
  have h1 : 1 ≤ ‖ξ‖ := by rw [hm]; nlinarith [Real.pi_gt_three, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hsin : Complex.sin w = Complex.cos (w - (π / 2 : ℂ)) := (Complex.cos_sub_pi_div_two w).symm
  by_cases hy : 1 ≤ |ξ.im|
  · have := airyNorm_cos_ge_of_abs_im_ge (w := w - (π / 2 : ℂ)) (by simpa [hwi] using hy)
    rw [hsin]
    have e : (w - (π / 2 : ℂ)).im = ξ.im := by simp [hw]
    rw [e] at this
    exact this
  replace hy := not_le.mp hy
  have hre' : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := airyC2_re_sin w
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
  have hx : w.re = (m * π - d) + π / 2 := by rw [hwr, hd]; linarith
  have hcos : |Real.sin w.re| = Real.cos d := by
    rw [hx, Real.sin_add_pi_div_two, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, zero_mul, add_zero]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩)
  have hc12 : 1 / 2 ≤ Real.cos d := by
    have := Real.one_sub_sq_div_two_le_cos (x := d)
    nlinarith
  have hre2 : ‖Complex.sin w‖ ≥ |(Complex.sin w).re| := Complex.abs_re_le_norm _
  rw [hre', abs_mul, hcos, abs_of_pos (Real.cosh_pos _), hwi] at hre2
  have hep := Real.exp_pos |ξ.im|
  nlinarith

/-- Every `[k, k+1]`, `k ≥ 10`, contains `r` with `(2/3) r^{3/2} = c + mπ`, `m ∈ ℕ` (`0 ≤ c ≤ π`). -/
lemma airyC2_radius_exists (k : ℕ) (hk : 10 ≤ k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ π) :
    ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧ ∃ m : ℕ, 2 / 3 * r ^ (3 / 2 : ℝ) = c + m * π := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  set G : ℝ := 2 / 3 * (k : ℝ) ^ (3 / 2 : ℝ) with hG
  have hk32 := airyRpow_three_halves_eq hkpos
  have hs3 := airyGC_three_le_sqrt hk'
  have hG20 : 20 ≤ G := by rw [hG, hk32]; nlinarith
  have hpi := Real.pi_lt_d2
  have hpipos := Real.pi_pos
  set a : ℝ := (G - c) / π with ha
  have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg <;> linarith
  set m : ℕ := ⌈a⌉₊ with hm
  have hm1 : a ≤ m := Nat.le_ceil a
  have hm2 : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hmπ1 : G - c ≤ m * π := by
    have := mul_le_mul_of_nonneg_right hm1 hpipos.le
    rwa [ha, div_mul_cancel₀ _ hpipos.ne'] at this
  have hmπ2 : (m : ℝ) * π < G - c + π := by
    have := mul_lt_mul_of_pos_right hm2 hpipos
    rwa [add_mul, ha, div_mul_cancel₀ _ hpipos.ne', one_mul] at this
  set t : ℝ := c + m * π with ht
  have ht0 : 0 ≤ 3 / 2 * t := by positivity
  set r : ℝ := (3 / 2 * t) ^ (2 / 3 : ℝ) with hr
  have hr32 : r ^ (3 / 2 : ℝ) = 3 / 2 * t := by
    rw [hr, ← Real.rpow_mul ht0]; norm_num
  have hr0 : 0 ≤ r := Real.rpow_nonneg ht0 _
  refine ⟨r, ?_, ?_, m, ?_⟩
  · rw [← Real.rpow_le_rpow_iff hkpos.le hr0 (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ1
    nlinarith
  · have hsucc := airyRpow_three_halves_succ_ge hkpos
    have hs3' : π ≤ √(k : ℝ) :=
      le_trans hpi.le (Real.le_sqrt_of_sq_le (by norm_num; linarith))
    rw [← Real.rpow_le_rpow_iff hr0 (by positivity) (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ2
    nlinarith
  · rw [hr32]; ring

lemma airyC2_arith {X p g : ℝ} (hX : 5 ≤ X) (hg : 0 ≤ g) (hp : 0 ≤ p) (h8 : 8 * p ≤ g * X) :
    g * X / 16 ≤ g * X / 4 - p - 6 / 5 * p / X ^ 3 - 41 / 10 * g / X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hX3 : 125 ≤ X ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hX 3]
  have hX3p : 0 < X ^ 3 := by positivity
  have t1 : 6 / 5 * p / X ^ 3 ≤ 6 / 5 * p / 125 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hX3
  have t2 : 41 / 10 * g / X ^ 2 ≤ 41 / 10 * g * X / 125 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hg hX0.le]
  nlinarith

/-! ### Sector `Re u ≥ -|u|/2`: `N ≈ Λ (P - Q u^{1/2})` -/

/-- **Lower bound in the sector `|arg u| ≤ 2π/3`** (`‖u‖ ≥ 10`, `|Q| √‖u‖ ≥ 8|P|`):
`(Q²/(16π)) √‖u‖ e(u) ≤ ‖N(u)‖²`. -/
theorem airyNC_sector_ge (P Q : ℝ) {u : ℂ} (hre : -(‖u‖ / 2) ≤ u.re) (h10 : 10 ≤ ‖u‖)
    (hP : 8 * |P| ≤ |Q| * √‖u‖) :
    Q ^ 2 * √‖u‖ * airyEnv u / (16 * π) ≤ ‖airyNC P Q u‖ ^ 2 := by
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
  have hη : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 := by
    rw [div_le_one hdenpos]; linarith
  have hη' : 17 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_iff₀ hdenpos]; linarith
  have hr0 : 0 < √‖u‖ := Real.sqrt_pos.mpr hz
  have hnΛ' : ‖Λ'‖ = √‖u‖ * ‖Λ‖ := by
    rw [hΛ', airyAiDerivLead, norm_neg, norm_mul, norm_cpow_half]
  have hΛn : 0 ≤ ‖Λ‖ := norm_nonneg _
  -- the leading part of N
  have hlead : (P : ℂ) * Λ + (Q : ℂ) * Λ' = Λ * ((P : ℂ) - (Q : ℂ) * u ^ (1 / 2 : ℂ)) := by
    rw [hΛ', airyAiDerivLead]; ring
  have hnlead : ‖Λ‖ * (|Q| * √‖u‖ - |P|) ≤ ‖(P : ℂ) * Λ + (Q : ℂ) * Λ'‖ := by
    rw [hlead, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ hΛn
    have := norm_sub_norm_le ((Q : ℂ) * u ^ (1 / 2 : ℂ)) ((P : ℂ))
    rw [norm_mul, norm_cpow_half, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at this
    rw [norm_sub_rev]
    exact this
  have herr : ‖airyNC P Q u - ((P : ℂ) * Λ + (Q : ℂ) * Λ')‖ ≤
      ‖Λ‖ * (|P| + |Q| * √‖u‖ / 4) := by
    have e : airyNC P Q u - ((P : ℂ) * Λ + (Q : ℂ) * Λ') =
        (P : ℂ) * (airyAiC u - Λ) + (Q : ℂ) * (deriv airyAiC u - Λ') := by
      unfold airyNC; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [airyC2_norm_real_mul, airyC2_norm_real_mul]
    have b1 : |P| * ‖airyAiC u - Λ‖ ≤ |P| * ‖Λ‖ := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine hA.trans ?_
      have := mul_le_mul_of_nonneg_right hη hΛn
      linarith
    have b2 : |Q| * ‖deriv airyAiC u - Λ'‖ ≤ |Q| * (1 / 4 * (√‖u‖ * ‖Λ‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine hD.trans ?_
      rw [hnΛ']
      exact mul_le_mul_of_nonneg_right hη' (by positivity)
    nlinarith
  have hN : ‖Λ‖ * (|Q| * √‖u‖ / 2) ≤ ‖airyNC P Q u‖ := by
    have h1 := norm_sub_norm_le ((P : ℂ) * Λ + (Q : ℂ) * Λ') (airyNC P Q u)
    have h2 : ‖(P : ℂ) * Λ + (Q : ℂ) * Λ' - airyNC P Q u‖ ≤ ‖Λ‖ * (|P| + |Q| * √‖u‖ / 4) := by
      rw [norm_sub_rev]; exact herr
    have hP0 := abs_nonneg P
    have hQ0 := abs_nonneg Q
    have : ‖Λ‖ * (|Q| * √‖u‖ - |P|) - ‖Λ‖ * (|P| + |Q| * √‖u‖ / 4) ≥ ‖Λ‖ * (|Q| * √‖u‖ / 2) := by
      have : |Q| * √‖u‖ - |P| - (|P| + |Q| * √‖u‖ / 4) ≥ |Q| * √‖u‖ / 2 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hΛn]
    linarith
  have hsq : (‖Λ‖ * (|Q| * √‖u‖ / 2)) ^ 2 ≤ ‖airyNC P Q u‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hN 2
  refine le_trans (le_of_eq ?_) hsq
  have h2 := norm_airyAiLead_sq u
  rw [← hΛ] at h2
  rw [mul_pow, h2, div_pow, mul_pow, sq_abs]
  field_simp
  ring

/-! ### Sector `Re u < -|u|/2`: `u = -q²` -/

/-- **Lower bound near the negative axis at a good radius** (`‖q‖ ≥ 5`, `|Q|‖q‖ ≥ 8|P|`,
`(2/3)‖q‖³ = 3π/4 + mπ`): `e(-q²) (Q² ‖q‖/(256π)) ≤ ‖N(-q²)‖²`. -/
theorem airyNC_neg_sq_ge (P Q : ℝ) {q : ℂ} (hq : NegSector q) (m : ℕ)
    (hm : 2 / 3 * ‖q‖ ^ 3 = 3 * π / 4 + m * π) (h5 : 5 ≤ ‖q‖) (hP : 8 * |P| ≤ |Q| * ‖q‖) :
    airyEnv (-(q ^ 2)) * (Q ^ 2 * ‖q‖ / (256 * π)) ≤ ‖airyNC P Q (-(q ^ 2))‖ ^ 2 := by
  have hq0 : 0 < ‖q‖ := by linarith
  set ξ : ℂ := (2 / 3 : ℂ) * q ^ 3 with hξ
  have hnξ : ‖ξ‖ = 2 / 3 * ‖q‖ ^ 3 := by
    rw [hξ, norm_mul, norm_pow]; norm_num
  have hξre : 0 ≤ ξ.re := by
    have h1 := hq.re_sq_ge
    have h0 := hq.re_nonneg
    have : ξ.re = 2 / 3 * (q.re * (q.re ^ 2 - 3 * q.im ^ 2)) := by
      rw [hξ]; simp [Complex.mul_re, re_cube]; ring
    rw [this]
    have : 0 ≤ q.re * (q.re ^ 2 - 3 * q.im ^ 2) := mul_nonneg h0 (by linarith)
    positivity
  have hsin := airyC2_sin_good hξre m (by rw [hnξ]; exact hm)
  have hcos : ‖Complex.cos (ξ - (π / 4 : ℂ))‖ ≤ Real.exp |ξ.im| := by
    have := airyC2_cos_le_exp (ξ - (π / 4 : ℂ))
    have e : (ξ - (π / 4 : ℂ)).im = ξ.im := by simp
    rwa [e] at this
  set Y := |ξ.im| with hY
  have hYe : |((2 / 3 : ℂ) * q ^ 3).im| = Y := rfl
  have hmA := airyAiC_neg_complex hq hq0
  have hmD := deriv_airyAiC_neg_complex hq hq0
  rw [hYe] at hmA hmD
  set τ : ℂ := ((π : ℂ) / q) ^ (1 / 2 : ℂ) with hτ
  have hτn : ‖τ‖ = √(π / ‖q‖) := by
    rw [hτ, norm_cpow_half, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  set A : ℝ := √(π / ‖q‖) / π with hA
  have hApos : 0 < A := by positivity
  have hπn : ‖(1 / (π : ℂ))‖ = 1 / π := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  set TA : ℂ := (1 / (π : ℂ)) * τ * Complex.cos (ξ - (π / 4 : ℂ)) with hTA
  set TD : ℂ := (1 / (π : ℂ)) * q * τ * Complex.sin (ξ - (π / 4 : ℂ)) with hTD
  have nTA : ‖TA‖ ≤ A * Real.exp Y := by
    rw [hTA, norm_mul, norm_mul, hπn, hτn]
    have : 1 / π * √(π / ‖q‖) = A := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hcos hApos.le
  have nTD : A * ‖q‖ * (Real.exp Y / 4) ≤ ‖TD‖ := by
    rw [hTD, norm_mul, norm_mul, norm_mul, hπn, hτn]
    have : 1 / π * ‖q‖ * √(π / ‖q‖) = A * ‖q‖ := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsin (by positivity)
  have hmain : A * Real.exp Y * (|Q| * ‖q‖ / 4 - |P|) ≤ ‖(P : ℂ) * TA + (Q : ℂ) * TD‖ := by
    have h1 := norm_sub_norm_le ((Q : ℂ) * TD) (-((P : ℂ) * TA))
    rw [sub_neg_eq_add, add_comm, norm_neg, airyC2_norm_real_mul, airyC2_norm_real_mul] at h1
    have h2 : |Q| * (A * ‖q‖ * (Real.exp Y / 4)) ≤ |Q| * ‖TD‖ :=
      mul_le_mul_of_nonneg_left nTD (abs_nonneg _)
    have h3 : |P| * ‖TA‖ ≤ |P| * (A * Real.exp Y) := mul_le_mul_of_nonneg_left nTA (abs_nonneg _)
    nlinarith
  have herr : ‖airyNC P Q (-(q ^ 2)) - ((P : ℂ) * TA + (Q : ℂ) * TD)‖ ≤
      A * Real.exp Y * (6 / 5 * |P| / ‖q‖ ^ 3 + 41 / 10 * |Q| / ‖q‖ ^ 2) := by
    have e : airyNC P Q (-(q ^ 2)) - ((P : ℂ) * TA + (Q : ℂ) * TD) =
        (P : ℂ) * (airyAiC (-(q ^ 2)) - TA) + (Q : ℂ) * (deriv airyAiC (-(q ^ 2)) - TD) := by
      unfold airyNC; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [airyC2_norm_real_mul, airyC2_norm_real_mul]
    have b1 : |P| * ‖airyAiC (-(q ^ 2)) - TA‖ ≤ |P| * (6 / 5 * Real.exp Y * A / ‖q‖ ^ 3) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have : (6 / 5 * Real.exp Y * (√(π / ‖q‖) / π) / ‖q‖ ^ 3) = 6 / 5 * Real.exp Y * A / ‖q‖ ^ 3 := rfl
      rw [← this]; exact hmA
    have b2 : |Q| * ‖deriv airyAiC (-(q ^ 2)) - TD‖ ≤ |Q| * (41 / 10 * Real.exp Y * A / ‖q‖ ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have : (41 / 10 * Real.exp Y * (√(π / ‖q‖) / π) / ‖q‖ ^ 2) = 41 / 10 * Real.exp Y * A / ‖q‖ ^ 2 := rfl
      rw [← this]; exact hmD
    have e1 : |P| * (6 / 5 * Real.exp Y * A / ‖q‖ ^ 3) + |Q| * (41 / 10 * Real.exp Y * A / ‖q‖ ^ 2) =
        A * Real.exp Y * (6 / 5 * |P| / ‖q‖ ^ 3 + 41 / 10 * |Q| / ‖q‖ ^ 2) := by ring
    linarith
  have ar := airyC2_arith h5 (abs_nonneg Q) (abs_nonneg P) hP
  have hfin : A * Real.exp Y * (|Q| * ‖q‖ / 16) ≤ ‖airyNC P Q (-(q ^ 2))‖ := by
    have h1 := norm_sub_norm_le ((P : ℂ) * TA + (Q : ℂ) * TD) (airyNC P Q (-(q ^ 2)))
    have h2 : ‖(P : ℂ) * TA + (Q : ℂ) * TD - airyNC P Q (-(q ^ 2))‖ ≤
        A * Real.exp Y * (6 / 5 * |P| / ‖q‖ ^ 3 + 41 / 10 * |Q| / ‖q‖ ^ 2) := by
      rw [norm_sub_rev]; exact herr
    have hpos : 0 ≤ A * Real.exp Y := by positivity
    have : A * Real.exp Y * (|Q| * ‖q‖ / 4 - |P|) -
        A * Real.exp Y * (6 / 5 * |P| / ‖q‖ ^ 3 + 41 / 10 * |Q| / ‖q‖ ^ 2) ≥
        A * Real.exp Y * (|Q| * ‖q‖ / 16) := by
      have : |Q| * ‖q‖ / 4 - |P| - (6 / 5 * |P| / ‖q‖ ^ 3 + 41 / 10 * |Q| / ‖q‖ ^ 2) ≥ |Q| * ‖q‖ / 16 := by
        linarith [ar]
      nlinarith [mul_le_mul_of_nonneg_left this hpos]
    linarith
  rw [airyEnv_neg_sq hq]
  have hEY : Real.exp (2 * |((2 / 3 : ℂ) * q ^ 3).im|) = Real.exp Y ^ 2 := by
    rw [hYe, ← Real.exp_nat_mul]; norm_num
  have hsq : (A * Real.exp Y * (|Q| * ‖q‖ / 16)) ^ 2 ≤ ‖airyNC P Q (-(q ^ 2))‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfin 2
  have hAsq : A ^ 2 = 1 / (π * ‖q‖) := by
    rw [hA, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have e : (A * Real.exp Y * (|Q| * ‖q‖ / 16)) ^ 2 = Real.exp Y ^ 2 * (Q ^ 2 * ‖q‖ / (256 * π)) := by
    have : (A * Real.exp Y * (|Q| * ‖q‖ / 16)) ^ 2 = A ^ 2 * Real.exp Y ^ 2 * (|Q| ^ 2 * ‖q‖ ^ 2 / 256) := by ring
    rw [this, hAsq, sq_abs]
    field_simp
  rw [hEY, ← e]
  exact hsq

/-! ### The good circles -/

lemma airyC2_abs_le_of_sq {P Q r : ℝ} (hr : 64 * (1 + P ^ 2 / Q ^ 2) ≤ r) (hQ : Q ≠ 0) :
    8 * |P| ≤ |Q| * √r := by
  have hQ2 : 0 < Q ^ 2 := by positivity
  have h1 : 64 * (Q ^ 2 + P ^ 2) ≤ Q ^ 2 * r := by
    have := mul_le_mul_of_nonneg_left hr hQ2.le
    have e : Q ^ 2 * (64 * (1 + P ^ 2 / Q ^ 2)) = 64 * (Q ^ 2 + P ^ 2) := by field_simp
    linarith
  have hr0 : 0 ≤ r := by nlinarith [sq_nonneg P]
  have h2 : (8 * |P|) ^ 2 ≤ (|Q| * √r) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hr0]
    nlinarith [sq_nonneg Q]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

lemma airyC2_ratio_le {a b e K r Q : ℝ} (hb : 0 < b) (he : 0 < e) (hsr : 0 < √r)
    (ha : a ^ 2 * e ≤ 4 * K ^ 2 * (3 / 2 * √r)) (hb2 : Q ^ 2 / (256 * π) * √r * e ≤ b ^ 2)
    (hK : 0 ≤ K) (hQ : 0 < |Q|) (ha0 : 0 ≤ a := by positivity) :
    a / b * e ≤ 40 * √π * K / |Q| := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  have hC : 0 ≤ 40 * √π * K / |Q| := by positivity
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
  have hpi := Real.pi_pos
  have hQ2 : 0 < Q ^ 2 := by
    have := sq_pos_of_pos hQ; rwa [sq_abs] at this
  have e1 : (a * e) ^ 2 = (a ^ 2 * e) * e := by ring
  have e2 : (40 * √π * K / |Q| * b) ^ 2 = (1600 * π * K ^ 2 / Q ^ 2) * b ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hpi.le, sq_abs]; ring
  rw [e1, e2]
  have h3 : (1600 * π * K ^ 2 / Q ^ 2) * (Q ^ 2 / (256 * π) * √r * e) ≤
      (1600 * π * K ^ 2 / Q ^ 2) * b ^ 2 := by gcongr
  have hQne : Q ≠ 0 := by intro h; simp [h] at hQ2
  have h4 : (1600 * π * K ^ 2 / Q ^ 2) * (Q ^ 2 / (256 * π) * √r * e) = 25 / 4 * K ^ 2 * √r * e := by
    field_simp; ring
  have h5 : (a ^ 2 * e) * e ≤ (4 * K ^ 2 * (3 / 2 * √r)) * e := mul_le_mul_of_nonneg_right ha he.le
  have h6 : 0 ≤ K ^ 2 * √r * e := by positivity
  nlinarith

/-- **Good circles for `N = P Ai + Q Ai'`, `Q ≠ 0`** (`GENERAL_THEOREMS.md` Lemmas 1.0, 1.0′, constant coefficients). -/
theorem airyNC_good_circle (P Q : ℝ) (hQ : Q ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧
      ∀ u : ℂ, ‖u‖ = r →
        Q ^ 2 / (256 * π) * √r * airyEnv u ≤ ‖airyNC P Q u‖ ^ 2 ∧
        (0 ≤ u.im → ‖airyMC P Q u / airyNC P Q u - I‖ * airyEnv u ≤ C) ∧
        (u.im ≤ 0 → ‖airyMC P Q u / airyNC P Q u + I‖ * airyEnv u ≤ C) := by
  have hQ0 : 0 < |Q| := abs_pos.mpr hQ
  have hK0 : 0 ≤ 3 * |P| + 5 * |Q| := by positivity
  refine ⟨40 * √π * (3 * |P| + 5 * |Q|) / |Q|, by positivity, ⌈64 * (1 + P ^ 2 / Q ^ 2)⌉₊, ?_⟩
  intro k hk
  have hk64 : 64 * (1 + P ^ 2 / Q ^ 2) ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hk10 : 10 ≤ k := by
    have : (64 : ℝ) ≤ k := by
      have : 0 ≤ P ^ 2 / Q ^ 2 := by positivity
      linarith
    exact_mod_cast (by linarith : (10 : ℝ) ≤ k)
  obtain ⟨r, hr1, hr2, m, hm⟩ := airyC2_radius_exists k hk10 (c := 3 * π / 4) (by positivity)
    (by linarith [Real.pi_pos])
  have hrk : 64 * (1 + P ^ 2 / Q ^ 2) ≤ r := hk64.trans hr1
  have hr64 : (64 : ℝ) ≤ r := by
    have : 0 ≤ P ^ 2 / Q ^ 2 := by positivity
    linarith
  have hrpos : 0 < r := by linarith
  have hsr : 8 ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hPQ := airyC2_abs_le_of_sq hrk hQ
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  -- the lower bound
  have hlow : ∀ v : ℂ, ‖v‖ = r →
      Q ^ 2 / (256 * π) * √r * airyEnv v ≤ ‖airyNC P Q v‖ ^ 2 := by
    intro v hv
    have henv := airyEnv_pos v
    by_cases hcase : -(‖v‖ / 2) ≤ v.re
    · have := airyNC_sector_ge P Q hcase (by rw [hv]; linarith) (by rw [hv]; exact hPQ)
      rw [hv] at this
      refine le_trans ?_ this
      have : Q ^ 2 / (256 * π) * √r * airyEnv v ≤ Q ^ 2 * √r * airyEnv v / (16 * π) := by
        have hh : 0 ≤ Q ^ 2 * √r * airyEnv v := by positivity
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hh Real.pi_pos.le]
      exact this
    · have hlt : v.re < -(‖v‖ / 2) := not_le.mp hcase
      set q : ℂ := (-v) ^ (1 / 2 : ℂ) with hqdef
      have hq : NegSector q := NegSector_of_re_lt hlt
      have hq2 : q ^ 2 = -v := cpow_half_sq _
      have hqn : ‖q‖ ^ 2 = r := by rw [hqdef, norm_cpow_half_sq, norm_neg, hv]
      have hq3 : ‖q‖ ^ 3 = r ^ (3 / 2 : ℝ) := by
        rw [hqdef, airyNorm_cpow_half_pow_three, norm_neg, hv]
      have hqs : ‖q‖ = √r := by rw [← hqn, Real.sqrt_sq (norm_nonneg _)]
      have := airyNC_neg_sq_ge P Q hq m (by rw [hq3]; exact hm) (by rw [hqs]; linarith)
        (by rw [hqs]; exact hPQ)
      have e : -(q ^ 2) = v := by rw [hq2, neg_neg]
      rw [e, hqs] at this
      refine le_trans (le_of_eq ?_) this
      ring
  have hL := hlow u hu
  -- the ratio bound in the closed upper half plane
  have hup : ∀ v : ℂ, ‖v‖ = r → 0 ≤ v.im →
      ‖airyMC P Q v / airyNC P Q v - I‖ * airyEnv v ≤ 40 * √π * (3 * |P| + 5 * |Q|) / |Q| := by
    intro v hv hvi
    have hLv := hlow v hv
    have hen := airyEnv_pos v
    have hsr0 : 0 < √r := Real.sqrt_pos.mpr hrpos
    have hN2 : 0 < ‖airyNC P Q v‖ ^ 2 := by
      refine lt_of_lt_of_le ?_ hLv
      positivity
    have hN : 0 < ‖airyNC P Q v‖ := by
      rcases (norm_nonneg (airyNC P Q v)).lt_or_eq with h | h
      · exact h
      · rw [← h] at hN2; simp at hN2
    have hne : airyNC P Q v ≠ 0 := norm_pos_iff.mp hN
    have hnum := airyMC_sub_I_mul_sq_le P Q hvi
    rw [hv] at hnum
    have e : airyMC P Q v / airyNC P Q v - I = (airyMC P Q v - I * airyNC P Q v) / airyNC P Q v := by
      field_simp
    rw [e, norm_div]
    have h1r : (1 + r) ^ (1 / 2 : ℝ) ≤ 3 / 2 * √r := by
      have : (1 + r) ^ (1 / 2 : ℝ) = √(1 + r) := (Real.sqrt_eq_rpow _).symm
      rw [this]
      have : √(1 + r) ≤ √(2 * r) := Real.sqrt_le_sqrt (by linarith)
      refine this.trans ?_
      rw [Real.sqrt_mul (by norm_num)]
      have : √2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    have hnum' : ‖airyMC P Q v - I * airyNC P Q v‖ ^ 2 * airyEnv v ≤
        4 * (3 * |P| + 5 * |Q|) ^ 2 * (3 / 2 * √r) :=
      hnum.trans (by gcongr)
    exact airyC2_ratio_le hN hen hsr0 hnum' hLv hK0 hQ0
  refine ⟨hL, fun hi => hup u hu hi, fun hi => ?_⟩
  have hci : 0 ≤ ((starRingEnd ℂ) u).im := by simpa using hi
  have hcu : ‖(starRingEnd ℂ) u‖ = r := by rw [Complex.norm_conj, hu]
  have h := hup ((starRingEnd ℂ) u) hcu hci
  have e : ‖airyMC P Q u / airyNC P Q u + I‖ =
      ‖airyMC P Q ((starRingEnd ℂ) u) / airyNC P Q ((starRingEnd ℂ) u) - I‖ := by
    have : airyMC P Q ((starRingEnd ℂ) u) / airyNC P Q ((starRingEnd ℂ) u) - I =
        (starRingEnd ℂ) (airyMC P Q u / airyNC P Q u + I) := by
      rw [map_add, map_div₀, conj_airyMC, conj_airyNC, Complex.conj_I]; ring
    rw [this, Complex.norm_conj]
  rw [e, ← airyEnv_conj u]
  exact h

/-- info: 'FormalResearch.Special.airyC2_sin_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyC2_sin_good

/-- info: 'FormalResearch.Special.airyNC_good_circle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_good_circle

end FormalResearch.Special
