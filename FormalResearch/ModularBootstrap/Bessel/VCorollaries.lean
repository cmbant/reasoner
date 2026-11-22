module

public import FormalResearch.ModularBootstrap.Bessel.VAsymptotic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Corollaries of Lemma B (c): comparison, log asymptotics, and the `K_a` upper bound

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`) (c), the
consequences used by Lemma G (`vlo:Gap`) and by `WeaklyFeasibleTest.hKa_ub` in
`SlitStrip/EntropyAndDeficit.lean`:

* `besselV_comparison`: `t^{-1/2} e^{c'L(x)}/V(t) ≍ x^{-1/2}` on `x ≥ ξ_*/2`;
* `log_besselK_asymptotic`: `log K_a(c'x²/3) = c'L(x) - ½ log(c'L(x)) + O(1)` for `x ≥ ξ_*`;
* `besselI0_le_two_mul_exp_div_sqrt`, `besselK_le_exp_div_sqrt`: the `K_a` bound
  `K_a(c'x²/3) ≤ C_K e^{c'(2π/3)x}/√c'` of `hKa_ub` with explicit `C_K = 7`;
* `besselV_le_two_mul` (in `Bessel.VSeries`): `V ≤ 2 K_a`, the field `hV_le_two_Ka`.
-/

@[expose] public section

open Real

namespace FormalResearch.ModularBootstrap.Bessel

/-- `3/4 ≤ π ξ_* = arsinh 1`. -/
lemma three_quarters_le_pi_mul_xiStar : 3 / 4 ≤ π * xiStar := by
  have h1 : π * xiStar = Real.arsinh 1 := by
    unfold xiStar; field_simp
  rw [h1]
  by_contra hlt
  rw [not_le] at hlt
  have h2 : exp (Real.arsinh 1) = 1 + √2 := by
    rw [Real.exp_arsinh]; norm_num
  have h3 : exp (Real.arsinh 1) < exp (3 / 4) := exp_lt_exp.mpr hlt
  have h4 : exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
    have h5 : exp (1 / 4 : ℝ) * exp (-(1 / 4 : ℝ)) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos (1 / 4 : ℝ), exp_pos (-(1 / 4 : ℝ))]
  have h6 : exp (3 / 4 : ℝ) = exp (1 / 4 : ℝ) ^ 3 := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have h7 : exp (1 / 4 : ℝ) ^ 3 ≤ (4 / 3) ^ 3 := by gcongr
  have h8 : (1.4 : ℝ) ≤ √2 := by
    apply Real.le_sqrt_of_sq_le; norm_num
  rw [h2, h6] at h3
  nlinarith

lemma one_fifth_le_xiStar : 1 / 5 ≤ xiStar := by
  have h := three_quarters_le_pi_mul_xiStar
  have hπ := Real.pi_lt_d2
  have hξ := xiStar_pos
  nlinarith

/-- **Lemma B (c), comparison** (`vlo:Bessel`): for `c' ≥ 10⁴`, `x ≥ ξ_*/2` and `t = c'x²/3`,
`(5π/3) x^{-1/2} ≤ t^{-1/2} e^{c'L(x)}/V(t) ≤ 6π x^{-1/2}`, where `V = besselV (c'/12)`.
That is `t^{-1/2} e^{c'L(x)}/V(t) ≍ x^{-1/2}` uniformly on `x ≥ ξ_*/2`. -/
theorem besselV_comparison {c' x : ℝ} (hc : 10000 ≤ c') (hx : xiStar / 2 ≤ x) :
    5 * π / 3 / √x ≤
        1 / √(c' * x ^ 2 / 3) * exp (c' * besselL x) / besselV (c' / 12) (c' * x ^ 2 / 3) ∧
    1 / √(c' * x ^ 2 / 3) * exp (c' * besselL x) / besselV (c' / 12) (c' * x ^ 2 / 3) ≤
        6 * π / √x := by
  have hc0 : 0 < c' := by linarith
  have hx1 : (1 : ℝ) / 10 ≤ x := by linarith [one_fifth_le_xiStar]
  have hx0 : 0 < x := by linarith
  have hasym := besselV_asymptotic (x₀ := 1 / 10) (by norm_num) (c' := c') (x := x)
    (by norm_num; linarith) hx1
  set z0 := c' * besselL x with hz0
  have hz00 : 0 < z0 := by rw [hz0]; unfold besselL; positivity
  have hA := besselAs_pos hz00
  set q := exp (-(4 * π * x)) with hq
  have hq0 : 0 < q := exp_pos _
  have hq3 : q ≤ 1 / 3 := by
    have h1 : (3 : ℝ) / 2 ≤ 4 * π * x := by
      have := three_quarters_le_pi_mul_xiStar
      nlinarith [pi_pos]
    have h2 : (3 : ℝ) ≤ exp (3 / 2) := by
      have h3 : (3 : ℝ) / 2 ≤ exp (1 / 2 : ℝ) := by
        have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
      have h4 : exp (3 / 2 : ℝ) = exp (1 / 2 : ℝ) ^ 3 := by
        rw [← exp_nat_mul]; congr 1; push_cast; ring
      rw [h4]
      nlinarith [exp_pos (1 / 2 : ℝ), sq_nonneg (exp (1 / 2 : ℝ))]
    have h5 : exp (3 / 2) ≤ exp (4 * π * x) := exp_le_exp.mpr h1
    have h6 : q * exp (4 * π * x) = 1 := by rw [hq, ← exp_add]; simp
    nlinarith [exp_pos (4 * π * x)]
  set B := besselV (c' / 12) (c' * x ^ 2 / 3) / besselAs z0 with hB
  have herr : (96 + 60 / (1 / 10 : ℝ)) / c' ≤ 7 / 100 := by
    rw [div_le_iff₀ hc0]; norm_num; linarith
  have hBlo : 1 / 3 ≤ B := by
    have := (abs_le.mp hasym).1
    have h1 : 4 / 9 ≤ (1 - q) ^ 2 := by nlinarith
    linarith
  have hBhi : B ≤ 6 / 5 := by
    have := (abs_le.mp hasym).2
    have h1 : (1 - q) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hV : besselV (c' / 12) (c' * x ^ 2 / 3) = B * besselAs z0 := by
    rw [hB]; field_simp
  have hVpos : 0 < besselV (c' / 12) (c' * x ^ 2 / 3) := by
    rw [hV]; have : 0 < B := by linarith
    positivity
  -- the exact identity
  have hident : 1 / √(c' * x ^ 2 / 3) * exp z0 / besselV (c' / 12) (c' * x ^ 2 / 3) =
      2 * π / √x / B := by
    rw [hV]
    unfold besselAs
    have hB0 : 0 < B := by linarith
    have h1 : √(2 * π * z0) / √(c' * x ^ 2 / 3) = 2 * π / √x := by
      rw [← Real.sqrt_div (by positivity)]
      have : 2 * π * z0 / (c' * x ^ 2 / 3) = (2 * π / √x) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hx0.le, hz0]; unfold besselL; field_simp
      rw [this, Real.sqrt_sq (by positivity)]
    have hs : 0 < √(2 * π * z0) := by positivity
    have ht : 0 < √(c' * x ^ 2 / 3) := by positivity
    rw [← h1]
    field_simp
  rw [hz0] at hident
  rw [hident]
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hpi := pi_pos
  have hB0 : 0 < B := by linarith
  constructor
  · calc 5 * π / 3 / √x = (2 * π / √x) / (6 / 5) := by field_simp; ring
      _ ≤ (2 * π / √x) / B := div_le_div_of_nonneg_left (by positivity) hB0 hBhi
  · calc (2 * π / √x) / B ≤ (2 * π / √x) / (1 / 3) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hBlo
      _ = 6 * π / √x := by field_simp; ring

/-- **Log asymptotics** (`vlo:Bessel` (c), real `x`, used by Lemma G): for `c' ≥ 8` and `x ≥ ξ_*`,
`|log K_a(c'x²/3) - (c'L(x) - ½ log(c'L(x)))| ≤ 4`, where `K_a = besselK (c'/12)`. -/
theorem log_besselK_asymptotic {c' x : ℝ} (hc : 8 ≤ c') (hx : xiStar ≤ x) :
    |Real.log (besselK (c' / 12) (c' * x ^ 2 / 3)) -
        (c' * besselL x - 1 / 2 * Real.log (c' * besselL x))| ≤ 4 := by
  have hc0 : 0 < c' := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le xiStar_pos hx
  set z := c' * besselL x with hz
  have hz4 : 4 ≤ z := by
    have h := three_quarters_le_pi_mul_xiStar
    have h1 : π * xiStar ≤ π * x := by gcongr
    have e1 := mul_le_mul_of_nonneg_left h1 hc0.le
    have e2 := mul_le_mul_of_nonneg_left h hc0.le
    rw [hz]; unfold besselL
    nlinarith
  have hz0 : 0 < z := by linarith
  have hK : besselK (c' / 12) (c' * x ^ 2 / 3) = besselI0 z := by
    have := besselK_shift (c' := c') (x := x) (j := 0) hc0 hx0.le
    simpa using this
  rw [hK]
  have hA := besselAs_pos hz0
  have hl := besselI0_lower hz0
  have hu := besselI0_upper hz4
  have hI : 0 < besselI0 z := lt_of_lt_of_le zero_lt_one (one_le_besselI0 z)
  have hlog : Real.log (besselI0 z) =
      Real.log (besselI0 z / besselAs z) + (z - 1 / 2 * Real.log (2 * π * z)) := by
    rw [Real.log_div hI.ne' hA.ne']
    unfold besselAs
    rw [Real.log_div (exp_pos z).ne' (by positivity), Real.log_exp, Real.log_sqrt (by positivity)]
    ring
  have hlz : Real.log (2 * π * z) = Real.log (2 * π) + Real.log z := by
    rw [Real.log_mul (by positivity) hz0.ne']
  have hr1 : 3 / 4 ≤ besselI0 z / besselAs z := by
    rw [le_div_iff₀ hA]
    have : 1 / z ≤ 1 / 4 := by gcongr
    nlinarith
  have hr2 : besselI0 z / besselAs z ≤ 7 / 2 := by
    rw [div_le_iff₀ hA]
    have : 10 / z ≤ 10 / 4 := by gcongr
    nlinarith
  have hlg1 : -1 / 3 ≤ Real.log (besselI0 z / besselAs z) := by
    have := Real.one_sub_inv_le_log_of_pos (x := besselI0 z / besselAs z) (by positivity)
    have h2 : (besselI0 z / besselAs z)⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; simpa using hr1
    linarith
  have hlg2 : Real.log (besselI0 z / besselAs z) ≤ 5 / 2 := by
    have := Real.log_le_sub_one_of_pos (x := besselI0 z / besselAs z) (by positivity)
    linarith
  have hl2π1 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [pi_gt_three])
  have hl2π2 : Real.log (2 * π) ≤ 2 * π - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hpi := Real.pi_lt_d2
  rw [hlog, hlz, abs_le]
  constructor <;> nlinarith

/-- `I₀(z) ≤ 2 e^z/√z` for all `z > 0`. -/
theorem besselI0_le_two_mul_exp_div_sqrt {z : ℝ} (hz : 0 < z) :
    besselI0 z ≤ 2 * exp z / √z := by
  have hs : 0 < √z := Real.sqrt_pos.mpr hz
  rcases lt_or_ge z 4 with h | h
  · have h1 := besselI0_le_exp hz.le
    have h2 : √z ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h.le
    rw [le_div_iff₀ hs]
    nlinarith [exp_pos z]
  · have h1 := besselI0_upper h
    have hA : besselAs z = exp z / √(2 * π * z) := rfl
    have h2 : (1 + 10 / z) ≤ 7 / 2 := by
      have : 10 / z ≤ 10 / 4 := by gcongr
      linarith
    have h3 : 1 / √(2 * π * z) ≤ 1 / (2 * √z) := by
      have : 2 * √z ≤ √(2 * π * z) := by
        apply Real.le_sqrt_of_sq_le
        have := Real.sq_sqrt hz.le
        nlinarith [Real.pi_gt_three]
      gcongr
    calc besselI0 z ≤ (1 + 10 / z) * besselAs z := h1
      _ ≤ (7 / 2) * (exp z / √(2 * π * z)) := by
          rw [hA]; gcongr
      _ = 7 / 2 * exp z * (1 / √(2 * π * z)) := by ring
      _ ≤ 7 / 2 * exp z * (1 / (2 * √z)) := by gcongr
      _ ≤ 2 * exp z / √z := by
          rw [← sub_nonneg]
          have : 2 * exp z / √z - 7 / 2 * exp z * (1 / (2 * √z)) = (exp z / √z) * (1 / 4) := by
            field_simp; ring
          rw [this]; positivity

/-- **`hKa_ub`** (`WeaklyFeasibleTest`): for `c' > 0` and `x ≥ 0.05`,
`K_a(c'x²/3) ≤ 7 e^{c'(2π/3)x}/√c'` (so `C_K = 7` works; `2√(30/π) ≈ 6.18` is what the proof
gives), where `K_a = besselK (c'/12)`, i.e. `I₀(4π√(a t))` with `a = c'/12`. -/
theorem besselK_le_exp_div_sqrt {c' x : ℝ} (hc : 0 < c') (hx : (0.05 : ℝ) ≤ x) :
    besselK (c' / 12) (c' * x ^ 2 / 3) ≤ 7 * exp (c' * ((2 * π / 3) * x)) / √c' := by
  have hx0 : 0 ≤ x := by linarith
  have hK : besselK (c' / 12) (c' * x ^ 2 / 3) = besselI0 (c' * besselL x) := by
    have := besselK_shift (c' := c') (x := x) (j := 0) hc hx0
    simpa using this
  rw [hK]
  set z := c' * besselL x with hz
  have hzx : z = c' * ((2 * π / 3) * x) := by rw [hz]; unfold besselL; ring
  have hxp : 0 < x := by linarith
  have hz0 : 0 < z := by rw [hz]; unfold besselL; positivity
  refine (besselI0_le_two_mul_exp_div_sqrt hz0).trans ?_
  rw [hzx]
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hc
  have hz' : (π / 30) * c' ≤ c' * ((2 * π / 3) * x) := by
    have := pi_pos
    nlinarith
  have h1 : √(π / 30) * √c' ≤ √(c' * ((2 * π / 3) * x)) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : 0 < √(π / 30) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 2 * exp (c' * ((2 * π / 3) * x)) / √(c' * ((2 * π / 3) * x)) ≤
      2 * exp (c' * ((2 * π / 3) * x)) / (√(π / 30) * √c') := by
    gcongr
  refine h2.trans ?_
  have hsq7 : (2 / 7 : ℝ) ≤ √(π / 30) := by
    apply Real.le_sqrt_of_sq_le
    have := Real.pi_gt_three; nlinarith
  rw [div_le_div_iff₀ (by positivity) hsc]
  have : 2 * exp (c' * ((2 * π / 3) * x)) * √c' ≤ 7 * exp (c' * ((2 * π / 3) * x)) * (√(π / 30) * √c') := by
    have := exp_pos (c' * ((2 * π / 3) * x))
    nlinarith [mul_pos this hsc]
  exact this

/-- **Bessel fields of `WeaklyFeasibleTest`** (`SlitStrip/EntropyAndDeficit.lean`): with
`K_a := besselK (c'/12)` and `V := besselV (c'/12)`, for `c' > 0` and `x ≥ 0.05`,
`V(c'x²/3) ≤ 2 K_a(c'x²/3)` (`hV_le_two_Ka`) and
`K_a(c'x²/3) ≤ 7 e^{c'(2π/3)x}/√c'` (`hKa_ub` with `C_K = 7`). -/
theorem weaklyFeasible_bessel_fields {c' x : ℝ} (hc : 0 < c') (hx : (0.05 : ℝ) ≤ x) :
    besselV (c' / 12) (c' * x ^ 2 / 3) ≤ 2 * besselK (c' / 12) (c' * x ^ 2 / 3) ∧
    besselK (c' / 12) (c' * x ^ 2 / 3) ≤ 7 * exp (c' * ((2 * π / 3) * x)) / √c' :=
  ⟨besselV_le_two_mul (by positivity), besselK_le_exp_div_sqrt hc hx⟩

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselV_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselV_comparison

/-- info: 'FormalResearch.ModularBootstrap.Bessel.log_besselK_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms log_besselK_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Bessel.besselK_le_exp_div_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselK_le_exp_div_sqrt

/-- info: 'FormalResearch.ModularBootstrap.Bessel.weaklyFeasible_bessel_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weaklyFeasible_bessel_fields

end FormalResearch.ModularBootstrap.Bessel
