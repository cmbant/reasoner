module

public import FormalResearch.ModularBootstrap.Bessel.Laplace
public import FormalResearch.ModularBootstrap.Bessel.VSeries
public import FormalResearch.ModularBootstrap.Constants

/-!
# Lemma B (c): asymptotics of `V` in the Airy-edge variable

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), part (c)
(real-`x` statements).  With `L(x) = 2πx/3` (`besselL`) and `as(z) = e^z/√(2πz)` (`besselAs`):

* `besselV_asymptotic`: for every `x₀ > 0`, all `c' ≥ 48 + 10/x₀` and `x ≥ x₀`,
  `|V(c'x²/3)/as(c'L(x)) - (1 - e^{-4πx})²| ≤ (96 + 55/x₀)/c'`,
  where `V = besselV (c'/12)` (the `O_{x₀}(c'^{-1})` of the paper, with explicit constants);
* `besselV_comparison`: `t^{-1/2} e^{c'L(x)}/V(t) ≍ x^{-1/2}` on `x ≥ ξ_*/2`, `t = c'x²/3`, namely
  `t^{-1/2} e^{c'L(x)}/V(t) = 2π x^{-1/2}/B(x)` with `B(x) = V(t)/as(c'L(x)) ∈ [1/2, 2]`
  (so `π x^{-1/2} ≤ … ≤ 4π x^{-1/2}`) for `c' ≥ c₀`;
* `log_besselK_asymptotic`: `log K_a(c'x²/3) = c'L(x) - ½ log(c'L(x)) + O(1)` with `|O(1)| ≤ 3`
  for `x ≥ ξ_*`, used by Lemma G;
* `besselK_le_exp_div_sqrt`: `K_a(c'x²/3) ≤ C_K e^{c'(2π/3)x}/√c'` for `x ≥ 0.05` (the field
  `hKa_ub` of `WeaklyFeasibleTest`), with explicit `C_K`.

The complex-neighbourhood version of (c) (holomorphic expansion with Cauchy derivative estimates) is
not formalised.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.Bessel

/-- `L(x) = 2πx/3`. -/
noncomputable def besselL (x : ℝ) : ℝ := 2 * π * x / 3

/-- Core ratio estimate: `I₀(z₀ s) e^m / as(z₀)` is within `d + (1-s) + 30/z₀` of `1`, where
`z₀ s = z₀ - m - d` with `m, d ≥ 0` and `1/2 ≤ s ≤ 1`, `z₀ ≥ 8`. -/
lemma ratio_lemma {z0 s m d : ℝ} (hz0 : 8 ≤ z0) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1) (hd : 0 ≤ d)
    (hz : z0 * s = z0 - m - d) :
    |besselI0 (z0 * s) * exp m / besselAs z0 - 1| ≤ d + (1 - s) + 30 / z0 := by
  have hz00 : 0 < z0 := by linarith
  have hs0 : 0 < s := by linarith
  have hzs : 4 ≤ z0 * s := by nlinarith
  -- asymptotic of I₀ at z0*s
  have hasym := besselI0_asymptotic hzs
  set ε := besselI0 (z0 * s) / besselAs (z0 * s) - 1 with hε
  have hAs : 0 < besselAs (z0 * s) := besselAs_pos (by positivity)
  have hI : besselI0 (z0 * s) = besselAs (z0 * s) * (1 + ε) := by
    rw [hε]; field_simp; ring
  have hεb : |ε| ≤ 20 / z0 := by
    refine hasym.trans ?_
    rw [div_le_div_iff₀ (by positivity) hz00]
    nlinarith
  -- ratio of `as`
  set w := 1 - s with hw
  have hw0 : 0 ≤ w := by linarith
  have hw1 : w ≤ 1 / 2 := by linarith
  set B := 1 / √s with hB
  have hsqs : 0 < √s := Real.sqrt_pos.mpr hs0
  have hBratio : besselAs (z0 * s) * exp m / besselAs z0 = exp (-d) * B := by
    unfold besselAs
    have h1 : √(2 * π * (z0 * s)) = √(2 * π * z0) * √s := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
    have h2 : exp (z0 * s) * exp m = exp (-d) * exp z0 := by
      rw [← exp_add, ← exp_add]; congr 1; linarith
    have hsq0 : 0 < √(2 * π * z0) := by positivity
    rw [h1, hB]
    field_simp
    rw [h2]; ring
  have hB1 : 1 ≤ B := by
    rw [hB, le_div_iff₀ hsqs]
    simpa using Real.sqrt_le_one.mpr hs1
  have hBw : B ≤ 1 + w := by
    rw [hB, div_le_iff₀ hsqs]
    have : 1 / (1 + w) ≤ √s := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hw0 (by nlinarith : 0 ≤ 1 - w - w ^ 2)]
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  -- assemble
  have hq : besselI0 (z0 * s) * exp m / besselAs z0 = exp (-d) * (B * (1 + ε)) := by
    rw [hI, ← mul_assoc, ← hBratio]; ring
  have hexp0 : 0 < exp (-d) := exp_pos _
  have hexp1 : exp (-d) ≤ 1 := by rw [exp_le_one_iff]; linarith
  have hexp2 : 1 - d ≤ exp (-d) := by
    have := Real.add_one_le_exp (-d); linarith
  have hBε : |B * ε| ≤ 30 / z0 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ B)]
    calc B * |ε| ≤ (3 / 2) * (20 / z0) := by
          apply mul_le_mul (by linarith) hεb (abs_nonneg _) (by norm_num)
      _ = 30 / z0 := by field_simp; norm_num
  have hB' : |B * (1 + ε) - 1| ≤ w + 30 / z0 := by
    have : B * (1 + ε) - 1 = (B - 1) + B * ε := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ B - 1)]
    linarith
  have hfin : exp (-d) * (B * (1 + ε)) - 1 =
      exp (-d) * (B * (1 + ε) - 1) + (exp (-d) - 1) := by ring
  rw [hq, hfin]
  refine (abs_add_le _ _).trans ?_
  have e1 : |exp (-d) * (B * (1 + ε) - 1)| ≤ w + 30 / z0 := by
    rw [abs_mul, abs_of_pos hexp0]
    calc exp (-d) * |B * (1 + ε) - 1| ≤ 1 * (w + 30 / z0) := by
          apply mul_le_mul hexp1 hB' (abs_nonneg _) (by norm_num)
      _ = w + 30 / z0 := one_mul _
  have e2 : |exp (-d) - 1| ≤ d := by
    rw [abs_le]; constructor <;> linarith
  linarith

lemma sqrt_one_sub_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    1 - u / 2 - u ^ 2 / 2 ≤ √(1 - u) ∧ √(1 - u) ≤ 1 - u / 2 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg hu0 hu0, mul_nonneg (mul_nonneg hu0 hu0) hu0,
      mul_nonneg (mul_nonneg hu0 hu0) (mul_nonneg hu0 hu0)]
  · rw [Real.sqrt_le_left (by linarith)]
    nlinarith [sq_nonneg u]

/-- The `j`-th shifted argument: `I₀(z₀ √(1 - 12 j/c'))`, `z₀ = c' L(x)`, relative to `as(z₀)`. -/
lemma ratio_j {c' x j : ℝ} (hc : 0 < c') (hj : 0 ≤ j) (hu : 12 * j / c' ≤ 1 / 2)
    (hz0 : 8 ≤ c' * besselL x) :
    |besselI0 (c' * besselL x * √(1 - 12 * j / c')) * exp (4 * π * j * x) /
        besselAs (c' * besselL x) - 1| ≤
      48 * π * j ^ 2 * x / c' + 12 * j / c' + 30 / (c' * besselL x) := by
  set u := 12 * j / c' with hu_def
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨hl, hr⟩ := sqrt_one_sub_bounds hu0 hu
  set z0 := c' * besselL x with hz0def
  have hz00 : 0 < z0 := by linarith
  set s := √(1 - u) with hs
  have hu2 : u ^ 2 / 2 ≤ u / 4 := by nlinarith
  have hs_lo : 1 / 2 ≤ s := by nlinarith
  have hs_hi : s ≤ 1 := by linarith
  have hd0 : 0 ≤ z0 * (1 - u / 2 - s) := mul_nonneg hz00.le (by linarith)
  have hd1 : z0 * (1 - u / 2 - s) ≤ 48 * π * j ^ 2 * x / c' := by
    have : z0 * (u ^ 2 / 2) = 48 * π * j ^ 2 * x / c' := by
      rw [hz0def, hu_def]; unfold besselL; field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left (by linarith) hz00.le
  have hm : z0 * u / 2 = 4 * π * j * x := by
    rw [hz0def, hu_def]; unfold besselL; field_simp; ring
  have key := ratio_lemma (z0 := z0) (s := s) (m := 4 * π * j * x) (d := z0 * (1 - u / 2 - s))
    hz0 hs_lo hs_hi hd0 (by nlinarith [hm])
  have hw : 1 - s ≤ u := by nlinarith
  have : (1 - s) ≤ 12 * j / c' := hw
  calc _ ≤ _ := key
    _ ≤ 48 * π * j ^ 2 * x / c' + 12 * j / c' + 30 / z0 := by linarith

/-- `K_{a-j}(c'x²/3) = I₀(c' L(x) √(1 - 12 j/c'))` for `a = c'/12`. -/
lemma besselK_shift {c' x j : ℝ} (hc : 0 < c') (hx : 0 ≤ x) :
    besselK (c' / 12 - j) (c' * x ^ 2 / 3) = besselI0 (c' * besselL x * √(1 - 12 * j / c')) := by
  unfold besselK
  congr 1
  have h1 : (c' / 12 - j) * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 * (1 - 12 * j / c') := by
    field_simp; ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  unfold besselL; ring

lemma mul_exp_neg_le_one {y : ℝ} (hy : 0 ≤ y) : y * exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have h2 : exp y * exp (-y) = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (-y)]

/-- Arithmetic of the second difference: error combination `η₀ - 2qη₁ + q²η₂`. -/
lemma error_combination {η0 η1 η2 q x c' z0 x₀ : ℝ} (hx₀ : 0 < x₀) (hc0 : 0 < c')
    (hz0' : 2 * x₀ * c' ≤ z0) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hqx : 4 * π * x * q ≤ 1) (hq2x : 8 * π * x * q ^ 2 ≤ 1)
    (hη0b : |η0| ≤ 30 / z0) (hη1b : |η1| ≤ 48 * π * x / c' + 12 / c' + 30 / z0)
    (hη2b : |η2| ≤ 192 * π * x / c' + 24 / c' + 30 / z0) :
    |η0 - 2 * q * η1 + q ^ 2 * η2| ≤ (96 + 60 / x₀) / c' := by
  have hz00 : 0 < z0 := by nlinarith [mul_pos hx₀ hc0]
  have t1 : 2 * q * |η1| ≤ 48 / c' + 60 / z0 := by
    calc 2 * q * |η1| ≤ 2 * q * (48 * π * x / c' + 12 / c' + 30 / z0) := by gcongr
      _ = (24 * (4 * π * x * q) + 24 * q) / c' + 60 * q / z0 := by field_simp; ring
      _ ≤ (24 * 1 + 24 * 1) / c' + 60 * 1 / z0 := by gcongr
      _ = 48 / c' + 60 / z0 := by ring
  have t2 : q ^ 2 * |η2| ≤ 48 / c' + 30 / z0 := by
    have hq2 : q ^ 2 ≤ 1 := by nlinarith
    calc q ^ 2 * |η2| ≤ q ^ 2 * (192 * π * x / c' + 24 / c' + 30 / z0) := by gcongr
      _ = (24 * (8 * π * x * q ^ 2) + 24 * q ^ 2) / c' + 30 * q ^ 2 / z0 := by field_simp; ring
      _ ≤ (24 * 1 + 24 * 1) / c' + 30 * 1 / z0 := by gcongr
      _ = 48 / c' + 30 / z0 := by ring
  have hsum : |η0 - 2 * q * η1 + q ^ 2 * η2| ≤ |η0| + 2 * q * |η1| + q ^ 2 * |η2| := by
    calc |η0 - 2 * q * η1 + q ^ 2 * η2| ≤ |η0 - 2 * q * η1| + |q ^ 2 * η2| := abs_add_le _ _
      _ ≤ |η0| + |2 * q * η1| + |q ^ 2 * η2| := by gcongr; exact abs_sub _ _
      _ = |η0| + 2 * q * |η1| + q ^ 2 * |η2| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hq0, abs_of_pos (by positivity : 0 < q ^ 2),
          abs_two]
  have hfinal : 96 / c' + 120 / z0 ≤ (96 + 60 / x₀) / c' := by
    have h120 : 120 / z0 ≤ 60 / x₀ / c' := by
      rw [div_div, div_le_div_iff₀ hz00 (by positivity)]; nlinarith
    rw [add_div]
    linarith
  calc |η0 - 2 * q * η1 + q ^ 2 * η2| ≤ |η0| + 2 * q * |η1| + q ^ 2 * |η2| := hsum
    _ ≤ 30 / z0 + (48 / c' + 60 / z0) + (48 / c' + 30 / z0) := by linarith
    _ = 96 / c' + 120 / z0 := by ring
    _ ≤ (96 + 60 / x₀) / c' := hfinal

/-- **Lemma B (c), real `x`** (`vlo:Bessel`): for every `x₀ > 0`, all `c' ≥ 48 + 4/x₀` and all real
`x ≥ x₀`, with `a = c'/12`,
`|V(c'x²/3)/as(c'L(x)) - (1 - e^{-4πx})²| ≤ (96 + 60/x₀)/c'`.
This is the paper's `V(c'x²/3) = as(c'L(x))[(1-e^{-4πx})² + O_{x₀}(c'^{-1})]`, uniformly in
`x ≥ x₀`, with explicit constants.  (The complex-neighbourhood version is not covered.) -/
theorem besselV_asymptotic {x₀ : ℝ} (hx₀ : 0 < x₀) {c' x : ℝ} (hc : 48 + 4 / x₀ ≤ c')
    (hx : x₀ ≤ x) :
    |besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs (c' * besselL x) -
        (1 - exp (-(4 * π * x))) ^ 2| ≤ (96 + 60 / x₀) / c' := by
  have hx0 : 0 ≤ x := hx₀.le.trans hx
  have h4x : 0 < 4 / x₀ := by positivity
  have hc0 : 0 < c' := by linarith
  have hc48 : 48 ≤ c' := by linarith
  have hz0 : 8 ≤ c' * besselL x := by
    unfold besselL
    have : 4 / x₀ ≤ c' := by linarith
    have h1 : 4 ≤ c' * x₀ := by
      rw [div_le_iff₀ hx₀] at this; linarith
    have hpi := Real.pi_gt_three
    nlinarith [mul_le_mul_of_nonneg_left hx hc0.le]
  have hz00 : 0 < c' * besselL x := by linarith
  have hA : 0 < besselAs (c' * besselL x) := besselAs_pos hz00
  -- the three terms
  have hK : ∀ j : ℝ, besselK (c' / 12 - j) (c' * x ^ 2 / 3) =
      besselI0 (c' * besselL x * √(1 - 12 * j / c')) := fun j => besselK_shift hc0 hx0
  have hV : besselV (c' / 12) (c' * x ^ 2 / 3) =
      besselI0 (c' * besselL x * √(1 - 12 * 0 / c')) -
        2 * besselI0 (c' * besselL x * √(1 - 12 * 1 / c')) +
        besselI0 (c' * besselL x * √(1 - 12 * 2 / c')) := by
    unfold besselV
    have h0 := hK 0; have h1 := hK 1; have h2 := hK 2
    simp only [sub_zero] at h0
    rw [h0, show c' / 12 - 1 = c' / 12 - (1 : ℝ) from rfl, h1,
      show c' / 12 - 2 = c' / 12 - (2 : ℝ) from rfl, h2]
  set z0 := c' * besselL x with hz0def
  -- ratios
  have hu1 : 12 * (1 : ℝ) / c' ≤ 1 / 2 := by rw [div_le_iff₀ hc0]; linarith
  have hu2 : 12 * (2 : ℝ) / c' ≤ 1 / 2 := by rw [div_le_iff₀ hc0]; linarith
  have hu0 : 12 * (0 : ℝ) / c' ≤ 1 / 2 := by simp
  have r0 := ratio_j (c' := c') (x := x) (j := 0) hc0 le_rfl hu0 hz0
  have r1 := ratio_j (c' := c') (x := x) (j := 1) hc0 zero_le_one hu1 hz0
  have r2 := ratio_j (c' := c') (x := x) (j := 2) hc0 (by norm_num) hu2 hz0
  rw [← hz0def] at r0 r1 r2
  -- notation
  set η0 := besselI0 (z0 * √(1 - 12 * 0 / c')) * exp (4 * π * 0 * x) / besselAs z0 - 1 with hη0
  set η1 := besselI0 (z0 * √(1 - 12 * 1 / c')) * exp (4 * π * 1 * x) / besselAs z0 - 1 with hη1
  set η2 := besselI0 (z0 * √(1 - 12 * 2 / c')) * exp (4 * π * 2 * x) / besselAs z0 - 1 with hη2
  have e1 : exp (4 * π * 1 * x) = exp (4 * π * x) := by ring_nf
  have e2 : exp (4 * π * 2 * x) = exp (4 * π * x) ^ 2 := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hE : exp (-(4 * π * x)) * exp (4 * π * x) = 1 := by rw [← exp_add]; simp
  set q := exp (-(4 * π * x)) with hq
  have hq0 : 0 < q := exp_pos _
  have hq1 : q ≤ 1 := by rw [hq, exp_le_one_iff]; have := pi_pos; nlinarith
  have hexp1 : exp (4 * π * x) = 1 / q := by field_simp; linarith
  -- identify each ratio
  have ρ0 : besselI0 (z0 * √(1 - 12 * 0 / c')) / besselAs z0 = 1 + η0 := by
    rw [hη0]; simp
  have ρ1 : besselI0 (z0 * √(1 - 12 * 1 / c')) / besselAs z0 = q * (1 + η1) := by
    rw [hη1, e1, hexp1]; field_simp; ring
  have ρ2 : besselI0 (z0 * √(1 - 12 * 2 / c')) / besselAs z0 = q ^ 2 * (1 + η2) := by
    rw [hη2, e2, hexp1]; field_simp; ring
  have hmain : besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs z0 - (1 - q) ^ 2 =
      η0 - 2 * q * η1 + q ^ 2 * η2 := by
    rw [hV]
    have : (besselI0 (z0 * √(1 - 12 * 0 / c')) - 2 * besselI0 (z0 * √(1 - 12 * 1 / c')) +
        besselI0 (z0 * √(1 - 12 * 2 / c'))) / besselAs z0 =
        (1 + η0) - 2 * (q * (1 + η1)) + q ^ 2 * (1 + η2) := by
      rw [← ρ0, ← ρ1, ← ρ2]; ring
    rw [this]; ring
  rw [hmain]
  -- bounds
  have hqx : 4 * π * x * q ≤ 1 := mul_exp_neg_le_one (by positivity)
  have hq2x : 8 * π * x * q ^ 2 ≤ 1 := by
    have := mul_exp_neg_le_one (y := 8 * π * x) (by positivity)
    have e : exp (-(8 * π * x)) = q ^ 2 := by
      rw [hq, ← exp_nat_mul]; congr 1; push_cast; ring
    rwa [e] at this
  have hz0' : 2 * x₀ * c' ≤ z0 := by
    rw [hz0def]; unfold besselL
    have hpi := Real.pi_gt_three
    have h1 : x₀ * c' ≤ x * c' := by gcongr
    nlinarith [mul_nonneg (mul_nonneg hc0.le hx0) (sub_nonneg.2 hpi.le)]
  have hη0b : |η0| ≤ 30 / z0 := by
    have := r0
    simp only [mul_zero, zero_div, zero_pow two_ne_zero, add_zero, zero_mul, zero_add] at this
    exact this
  have hη1b : |η1| ≤ 48 * π * x / c' + 12 / c' + 30 / z0 := by
    have := r1
    simp only [one_pow, mul_one] at this
    exact this
  have hη2b : |η2| ≤ 192 * π * x / c' + 24 / c' + 30 / z0 := by
    have := r2
    have e : 48 * π * (2 : ℝ) ^ 2 * x / c' = 192 * π * x / c' := by ring
    have e' : 12 * (2 : ℝ) / c' = 24 / c' := by ring
    rw [e, e'] at this
    exact this
  exact error_combination hx₀ hc0 hz0' hq0 hq1 hqx hq2x hη0b hη1b hη2b

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_asymptotic

end FormalResearch.ModularBootstrap.Bessel
