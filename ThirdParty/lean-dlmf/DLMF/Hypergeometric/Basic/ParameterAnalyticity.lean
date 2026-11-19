/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.GaussSeries
public import DLMFMathlib.Analysis.Complex.ParameterContinuity
public import DLMFMathlib.Analysis.SpecialFunctions.Gamma.Bounds
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The regularized Gauss function in its parameters (DLMF §15.2(ii))

Mathlib's regularized Gauss function `regularizedGaussHGFun a b c z = 𝐅(a,b;c;z)` is, for
`‖z‖ < 1`, an entire function of its parameters. Together with the identity principle this
extends identities proved under restrictive parameter hypotheses to all parameters.

## Main results

* `analyticOnNhd_regularizedGaussHypergeometricFun_comp`,
  `analyticOnNhd_regularizedGaussHypergeometricFun_a`,
  `analyticOnNhd_regularizedGaussHypergeometricFun_b`,
  `analyticOnNhd_regularizedGaussHypergeometricFun_c`: analyticity in the parameters, along any
  entire curve.
* `eq_of_eqOn_not_neg_nat`, `eq_of_eqOn_re_pos`: identity principles in the parameters.
* `regularizedHGFun_cons_cons`: common-parameter cancellation, including all Gamma poles.
* `regularizedGaussHypergeometricFun_eq_div_Gamma`: `𝐅 = ₂F₁/Γ(c)` off the poles.
* `deriv_regularizedGaussHypergeometricFun`, `iteratedDeriv_regularizedGaussHypergeometricFun`: DLMF
  15.5.1–15.5.2 for the regularized function, for all parameters.
* `regularized_at_neg_nat`, `tendsto_regularized_at_neg_nat`: the regularized function at a
  nonpositive integer denominator parameter, DLMF 15.2.3_5.
* `contiguous_c`, `contiguous_shift_b`: two of Gauss's contiguous relations on the disk
  (DLMF 15.5.16_5), and `regularizedGaussHypergeometricFun_contiguous_c`,
  `regularizedGaussHypergeometricFun_contiguous_shift_b`: their regularized forms, for all
  parameters.

## Implementation notes

The proof of analyticity dominates the tail of the series, on a neighbourhood of any point, by
the series with parameters `(‖a‖, ‖b‖, 1 - N)`, using `‖1/Γ(c+n)‖ ≤ 1/((n-N)! ‖Γ(c+N)‖)` for
`Re (c+N) ≥ 1`. The remaining regularized contiguous relations and the transformations are in
`DLMF.Hypergeometric.Continuation`.
-/

public section

open Complex Filter Set FormalMultilinearSeries
open scoped Topology

noncomputable section

namespace DLMF.Hypergeometric

/-- Helper lemma for contiguous relations: `a (a+1)_n = (a+n) (a)_n`. -/
theorem pochhammer_succ_left_mul (a : ℂ) (n : ℕ) : a * pochhammer (a + 1) n = (a + n) *
    pochhammer a n := by
  rw [← pochhammer_succ_left, pochhammer_succ, mul_comm]

/-- Helper lemma for `contiguous_shift_b`. -/
theorem pochhammer_sub_succ (b : ℂ) (n : ℕ) :
    pochhammer b (n + 1) - pochhammer (b + 1) (n + 1) = -(n + 1 : ℂ) * pochhammer (b + 1) n := by
  rw [pochhammer_succ_left, pochhammer_succ]
  ring

/-- Helper lemma for `contiguous_shift_b`. The identity is false at `c = 0` without this
regularity hypothesis: both left-hand hypergeometric series collapse to `1` in Lean's
totalization, while the right-hand side need not vanish. -/
theorem gaussHypergeometricCoeff_contiguous_shift_b {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    c * gaussHypergeometricCoeff a b c (n + 1) - c * gaussHypergeometricCoeff a (b + 1) c (n + 1) =
      -a * gaussHypergeometricCoeff (a + 1) (b + 1) (c + 1) n := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hcp1 := pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_add_nat hc 1) n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hdiff := pochhammer_sub_succ b n
  have hfac : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  simp only [gaussHypergeometricCoeff, pochhammer_succ_left a n, pochhammer_succ_left c n, hfac]
  field_simp [hc0, hcp1, hn, hf0]
  rw [hdiff]
  ring

/-- One of Gauss's contiguous relations, under the standing AAR convention that the
denominator parameter is not a nonpositive integer. Without that hypothesis the identity
fails at `c = 0`. -/
@[dlmf 15.5.E16_5]
theorem contiguous_shift_b {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    c * ₂F₁ a b c z - c * ₂F₁ a (b + 1) c z =
      -(a * z) * ₂F₁ (a + 1) (b + 1) (c + 1) z := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow hz'
  have hs2 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a (b + 1) c).hasSum_mul_pow hz'
  have hs3 :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + 1) (b + 1) (c + 1)).hasSum_mul_pow hz'
  have hL := (hs1.mul_left c).sub (hs2.mul_left c)
  have hR0 := hs3.mul_left (-a)
  let d : ℕ → ℂ := fun n =>
    match n with
    | 0 => 0
    | n + 1 => -a * gaussHypergeometricCoeff (a + 1) (b + 1) (c + 1) n
  have hd_succ : ∀ n, d (n + 1) = -a *
      gaussHypergeometricCoeff (a + 1) (b + 1) (c + 1) n := fun n => rfl
  have hds : HasSum (fun n => d (n + 1) * z ^ n)
      (-a * ₂F₁ (a + 1) (b + 1) (c + 1) z) := by
    have hfun : (fun n => d (n + 1) * z ^ n) =
        fun n => -a * (gaussHypergeometricCoeff (a + 1) (b + 1) (c + 1) n * z ^ n) := by
      funext n
      rw [hd_succ]
      ring
    rwa [hfun]
  have hR := HasSum.mul_pow_shift hds rfl
  have hfunL : (fun n : ℕ =>
      c * (gaussHypergeometricCoeff a b c n * z ^ n) - c *
          (gaussHypergeometricCoeff a (b + 1) c n * z ^ n)) =
      fun n => d n * z ^ n := by
    funext n
    cases n with
    | zero => simp [d, gaussHypergeometricCoeff, pochhammer_zero]
    | succ n =>
      simp only [d]
      have hcoeff := gaussHypergeometricCoeff_contiguous_shift_b (a := a) (b := b) (c := c) hc n
      linear_combination hcoeff * z ^ (n + 1)
  have hL' : HasSum (fun n => d n * z ^ n)
      (c * ₂F₁ a b c z - c * ₂F₁ a (b + 1) c z) := by
    rwa [← hfunL]
  have hval : z * (-a * ₂F₁ (a + 1) (b + 1) (c + 1) z) =
      -(a * z) * ₂F₁ (a + 1) (b + 1) (c + 1) z := by ring
  exact hL'.unique (hval ▸ hR)

/-- Helper lemma for `contiguous_c`. -/
theorem gaussHypergeometricCoeff_contiguous_c {a b c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    c * gaussHypergeometricCoeff a b c n - (c - a) * gaussHypergeometricCoeff a b (c + 1) n -
      a * gaussHypergeometricCoeff (a + 1) b (c + 1) n = 0 := by
  have hcp := pochhammer_ne_zero_of_not_neg_nat hc n
  have hcp1 : pochhammer (c + 1) n ≠ 0 := by
    simpa using pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_add_nat hc 1) n
  have hfact : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hA := pochhammer_succ_left_mul a n
  have hC := pochhammer_succ_left_mul c n
  have hnum :
      c * pochhammer a n * pochhammer (c + 1) n - (c - a) * pochhammer a n * pochhammer c n -
        a * pochhammer (a + 1) n * pochhammer c n = 0 := by
    rw [show c * pochhammer a n * pochhammer (c + 1) n = pochhammer a n *
        (c * pochhammer (c + 1) n) by ring, hC]
    rw [show a * pochhammer (a + 1) n * pochhammer c n = pochhammer c n *
        (a * pochhammer (a + 1) n) by ring, hA]
    ring
  have hden : pochhammer c n * pochhammer (c + 1) n * (n.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcp hcp1) hfact
  simp only [gaussHypergeometricCoeff]
  apply mul_left_cancel₀ hden
  rw [mul_zero]
  field_simp [hcp, hcp1, hfact]
  linear_combination pochhammer b n * hnum

/-- The Gauss contiguous relation among `F(c)`, `F(c+1)` and `F(a+1,c+1)`,
for `c` outside the nonpositive integers and argument in the open unit disk. -/
theorem contiguous_c {a b c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) :
    c * ₂F₁ a b c z - (c - a) * ₂F₁ a b (c + 1) z -
      a * ₂F₁ (a + 1) b (c + 1) z = 0 := by
  have hz' := mem_eball_one_of_norm_lt_one hz
  have hs0 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).hasSum_mul_pow hz'
  have hs1 := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b (c + 1)).hasSum_mul_pow hz'
  have hs2 :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + 1) b (c + 1)).hasSum_mul_pow hz'
  have hsum := (hs0.mul_left c).sub ((hs1.mul_left (c - a)).add (hs2.mul_left a))
  have hfun : (fun n : ℕ =>
      c * (gaussHypergeometricCoeff a b c n * z ^ n) -
        ((c - a) * (gaussHypergeometricCoeff a b (c + 1) n * z ^ n) +
          a * (gaussHypergeometricCoeff (a + 1) b (c + 1) n * z ^ n))) =
      fun _ => 0 := by
    funext n
    have hcoeff := gaussHypergeometricCoeff_contiguous_c (a := a) (b := b) (c := c) hc n
    linear_combination hcoeff * z ^ n
  have hsum' : HasSum (fun _ : ℕ => (0 : ℂ))
      (c * ₂F₁ a b c z - ((c - a) * ₂F₁ a b (c + 1) z + a * ₂F₁ (a + 1) b (c + 1) z)) := by
    rwa [hfun] at hsum
  have hval := hsum'.tsum_eq
  rw [tsum_zero] at hval
  rw [eq_comm] at hval
  convert hval using 1
  ring

/-- Two entire functions agreeing near a point agree everywhere. -/
theorem eq_of_analyticOnNhd_univ_of_eventuallyEq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ) {z₀ : ℂ}
    (hfg : f =ᶠ[𝓝 z₀] g) : f = g :=
  AnalyticOnNhd.eq_of_eventuallyEq hf hg hfg

/-- Two entire functions agreeing on a nonempty open set agree everywhere. -/
theorem eq_of_analyticOnNhd_univ_of_eqOn {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ) {U : Set ℂ} (hU : IsOpen U)
    (hne : U.Nonempty) (h : EqOn f g U) : f = g := by
  obtain ⟨z₀, hz₀⟩ := hne
  exact AnalyticOnNhd.eq_of_eventuallyEq hf hg (eventuallyEq_of_mem (hU.mem_nhds hz₀) h)

/-- Pochhammer symbols with nonnegative real argument are nonnegative. -/
theorem ascPochhammer_eval_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (ascPochhammer ℝ n).eval x := by
  exact pochhammer_eval_nonneg hx n

/-- Pochhammer symbols are monotone on the nonnegative reals. -/
theorem ascPochhammer_eval_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    (ascPochhammer ℝ n).eval x ≤ (ascPochhammer ℝ n).eval y := by
  exact pochhammer_eval_mono hx hxy n

/-- Evaluating the complex Pochhammer polynomial at a real number. -/
theorem ascPochhammer_eval_ofReal (x : ℝ) (n : ℕ) :
    (ascPochhammer ℂ n).eval (x : ℂ) = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  have h := ascPochhammer_map (algebraMap ℝ ℂ) n
  rw [← h, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply _ _

/-- `‖(a)_n‖ ≤ (r)_n` for `‖a‖ ≤ r`. -/
theorem norm_ascPochhammer_eval_le {a : ℂ} {r : ℝ} (hr : ‖a‖ ≤ r) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval a‖ ≤ ‖(ascPochhammer ℂ n).eval (r : ℂ)‖ := by
  rw [ascPochhammer_eval_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact (norm_pochhammer_le a n).trans
    ((pochhammer_eval_mono (norm_nonneg a) hr n).trans (le_abs_self _))

/-- The complement of the nonpositive integers is open in `ℂ`. -/
theorem isOpen_not_neg_nat : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} := by
  have hce : Topology.IsClosedEmbedding (fun m : ℕ => -((m : ℝ) : ℂ)) :=
    (Homeomorph.neg ℂ).isClosedEmbedding.comp
      (Complex.isometry_ofReal.isClosedEmbedding.comp Nat.isClosedEmbedding_coe_real)
  have hset : {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} = (Set.range fun m : ℕ => -((m : ℝ) : ℂ))ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists,
      Complex.ofReal_natCast]
    exact ⟨fun h m hm => h m hm.symm, fun h m hm => h m hm.symm⟩
  rw [hset]
  exact hce.isClosed_range.isOpen_compl

/-- Near `-n`, but away from it, no nonpositive integer is hit. -/
theorem eventually_nhdsWithin_ne_neg_nat (n : ℕ) :
    ∀ᶠ c in 𝓝[≠] (-(n : ℂ)), ∀ k : ℕ, c ≠ -(k : ℂ) := by
  have h1 : ∀ᶠ c in 𝓝[≠] (-(n : ℂ)), c ≠ -(n : ℂ) := self_mem_nhdsWithin
  have h2 : ∀ᶠ c in 𝓝[≠] (-(n : ℂ)), dist c (-(n : ℂ)) < 1 / 2 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (-(n : ℂ)) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h1, h2] with c hc hc' k hk
  rw [dist_eq_norm] at hc'
  rcases eq_or_ne k n with rfl | hkn
  · exact hc hk
  · have hdist : (1 : ℝ) ≤ ‖(-(k : ℂ)) - -(n : ℂ)‖ := by
      rw [show (-(k : ℂ)) - -(n : ℂ) = (((n : ℤ) - k : ℤ) : ℂ) by push_cast; ring,
        Complex.norm_intCast]
      have : (n : ℤ) - k ≠ 0 := by omega
      exact_mod_cast Int.one_le_abs this
    rw [hk] at hc'
    linarith

/-- `(x)_{m+k} = (x)_m (x+m)_k`. -/
theorem ascPochhammer_eval_add (x : ℂ) (m k : ℕ) :
    (ascPochhammer ℂ (m + k)).eval x =
      (ascPochhammer ℂ m).eval x * (ascPochhammer ℂ k).eval (x + m) := by
  rw [← ascPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp]
  simp

/-- `1/Γ(y) = (y)_{p+1}/Γ(y+p+1)` for every `y`. -/
theorem recip_Gamma_eq_pochhammer_mul (p : ℕ) (y : ℂ) :
    (Gamma y)⁻¹ = pochhammer y (p + 1) * (Gamma (y + (p + 1 : ℕ)))⁻¹ := by
  by_cases hy : ∀ m : ℕ, y ≠ -(m : ℂ)
  · have h := Gamma_add_nat_div_Gamma_eq (n := p + 1) y hy
    have h0 := Gamma_ne_zero hy
    have h1 : Gamma (y + (p + 1 : ℕ)) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hy _)
    rw [pochhammer, ← h]
    field_simp
  · simp only [not_forall, not_not] at hy
    obtain ⟨j, rfl⟩ := hy
    rw [Gamma_neg_nat_eq_zero, inv_zero]
    rcases Nat.lt_or_ge p j with hpj | hpj
    · have : -(j : ℂ) + ((p + 1 : ℕ) : ℂ) = -((j - p - 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this, Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
    · rw [pochhammer_neg_nat_eq_zero (by omega), zero_mul]

/-- Cancelling a common parameter in the totalized regularized generalized series introduces
`1 / Γ(c)`, including at every nonpositive integer parameter and outside convergence disks. -/
theorem regularizedHGFun_cons_cons (c : ℂ) (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun (c ::ₘ a) (c ::ₘ b) z =
      (Gamma c)⁻¹ * regularizedHGFun a b z := by
  rw [regularizedHGFun_eq_tsum', regularizedHGFun_eq_tsum', ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hΓ : (ascPochhammer ℂ n).eval c * (Gamma (c + n))⁻¹ = (Gamma c)⁻¹ := by
    cases n with
    | zero => simp
    | succ k =>
      simpa only [pochhammer, Nat.succ_eq_add_one] using
        (recip_Gamma_eq_pochhammer_mul k c).symm
  simp only [regularizedHGFunCoeff, Multiset.map_cons, Multiset.prod_cons,
    div_eq_mul_inv, mul_inv_rev]
  linear_combination ((a.map (fun x => (ascPochhammer ℂ n).eval x)).prod *
    ((n.factorial : ℂ) * (b.map (fun x => Gamma (x + n))).prod)⁻¹ * z ^ n) * hΓ

/-- The regularized Gauss series with the `Γ` factor isolated. -/
theorem regularizedGaussHypergeometricFun_eq_tsum (a b c z : ℂ) :
    regularizedGaussHGFun a b c z =
      ∑' n : ℕ, (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
        (Gamma (c + n))⁻¹ := by
  unfold regularizedGaussHGFun FormalMultilinearSeries.sum
  congr 1
  funext n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_regularizedGaussHGFunSeries,
    smul_eq_mul]
  ring

/-- Membership of the disk in the ball of convergence of the regularized series. -/
theorem mem_eball_radius_regularizedGaussHypergeometricFunSeries (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    z ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
  Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
    (mem_eball_one_of_norm_lt_one hz)

/-- For `‖z‖ < 1`, the terms `(a)ₙ (b)ₙ zⁿ / (n! Γ(c + n))` of the regularized Gauss series are
  summable. -/
theorem summable_regularizedGaussHypergeometricFun_term (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ =>
      (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
        (Gamma (c + n))⁻¹ := by
  have hpos : (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have h := ((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall hpos).hasSum_mul_pow
    (mem_eball_radius_regularizedGaussHypergeometricFunSeries a b c hz)
  refine h.summable.congr fun n => ?_
  have hc : regularizedHGFunCoeff {a, b} {c} n = (regularizedGaussHGFunSeries a b c).coeff n := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  rw [hc, coeff_regularizedGaussHGFunSeries]
  ring

/-- For real `α, β` and `n ≥ N`, the norm of the `n`-th coefficient of the regularized series with
  `c = 1 - N` is `|(α)ₙ| |(β)ₙ| / (n! (n - N)!)`. -/
theorem norm_regularizedGaussHypergeometricFunSeries_apply_ofReal (α β : ℝ) (N n : ℕ) (hn : N ≤ n) :
    ‖regularizedGaussHGFunSeries (α : ℂ) (β : ℂ) (1 - N) n‖ =
      ‖(ascPochhammer ℂ n).eval (α : ℂ)‖ * ‖(ascPochhammer ℂ n).eval (β : ℂ)‖ /
        (n.factorial * (n - N).factorial) := by
  have hΓ : Gamma ((1 : ℂ) - N + n) = ((n - N).factorial : ℂ) := by
    rw [show (1 : ℂ) - N + n = ((n - N : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hn]; ring]
    exact Complex.Gamma_nat_eq_factorial _
  rw [norm_apply_eq_norm_coef, coeff_regularizedGaussHGFunSeries, hΓ, norm_div, norm_mul, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast]

/-- The tail-domination step, shared by the three parameters: on `U` the `n`-th term is
bounded by the `n`-th term of the majorant series. -/
theorem norm_term_le_majorant {a b c : ℂ} {z : ℂ} {α β : ℝ}
    (ha : ‖a‖ ≤ α) (hb : ‖b‖ ≤ β) {N : ℕ} (hre : 1 ≤ (c + N).re) {m : ℝ} (hm : 0 < m)
    (hΓ : m ≤ ‖Gamma (c + N)‖) {n : ℕ} (hn : N ≤ n) :
    ‖(ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
        (Gamma (c + n))⁻¹‖ ≤
      m⁻¹ * (‖regularizedGaussHGFunSeries (α : ℂ) (β : ℂ) (1 - N) n‖ * ‖z‖ ^ n) := by
  rw [norm_regularizedGaussHypergeometricFunSeries_apply_ofReal α β N n hn, norm_mul,
      norm_div, norm_mul,
    norm_mul, norm_pow, Complex.norm_natCast]
  have hA := norm_ascPochhammer_eval_le ha n
  have hB := norm_ascPochhammer_eval_le hb n
  have hG := norm_recip_Gamma_add_nat_le hre hm hΓ hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hf' : (0 : ℝ) < (n - N).factorial := by positivity
  calc ‖(ascPochhammer ℂ n).eval a‖ * ‖(ascPochhammer ℂ n).eval b‖ * ‖z‖ ^ n / n.factorial *
        ‖(Gamma (c + n))⁻¹‖
      ≤ ‖(ascPochhammer ℂ n).eval (α : ℂ)‖ * ‖(ascPochhammer ℂ n).eval (β : ℂ)‖ * ‖z‖ ^ n /
          n.factorial * (((n - N).factorial : ℝ)⁻¹ * m⁻¹) := by gcongr
    _ = _ := by field_simp

/-- The regularized Gauss function is entire along any entire curve in the parameter space
(DLMF §15.2(ii)): for entire `A B C`, `w ↦ 𝐅(A w, B w; C w; z)` is entire when `‖z‖ < 1`. -/
theorem analyticOnNhd_regularizedGaussHypergeometricFun_comp {A B C : ℂ → ℂ}
    (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) univ := by
  simp_rw [regularizedGaussHypergeometricFun_eq_tsum]
  refine analyticOnNhd_tsum_of_eventually_dominated ?_ ?_ ?_
  · intro n
    have h1 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    have h2 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (B w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hB
    exact (((h1.mul h2).mul_const _).div_const _).mul
      (differentiable_one_div_Gamma.comp (hC.add_const _))
  · intro w
    exact summable_regularizedGaussHypergeometricFun_term _ _ _ hz
  · intro w₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (C w₀).re ≤ N := exists_nat_ge _
    have hre0 : 2 ≤ (C w₀ + N).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
    have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
      hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevB : ∀ᶠ w in 𝓝 w₀, ‖B w‖ < ‖B w₀‖ + 1 :=
      hB.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevC : ∀ᶠ w in 𝓝 w₀, (C w₀).re - 1 < (C w).re :=
      (Complex.continuous_re.comp hC.continuous).continuousAt.eventually
        (lt_mem_nhds (by show (C w₀).re - 1 < (C w₀).re; linarith))
    have hevV : ∀ᶠ w in 𝓝 w₀, C w ∈ V := hC.continuous.continuousAt (hVopen.mem_nhds hc₀V)
    obtain ⟨U, hU, hUopen, hw₀U⟩ := eventually_nhds_iff.mp (hevA.and (hevB.and (hevC.and hevV)))
    refine ⟨U, hUopen, hw₀U, N, ?_⟩
    set p := regularizedGaussHGFunSeries ((‖A w₀‖ + 1 : ℝ) : ℂ) ((‖B w₀‖ + 1 : ℝ) : ℂ) (1 - N)
      with hp
    have hz' : (‖z‖₊ : ENNReal) < p.radius := by
      refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one _ _ _)
      rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
      exact hz
    have hm : 0 < ‖Gamma (C w₀ + N)‖ / 2 := by
      have hpole : ∀ k : ℕ, C w₀ + N ≠ -k := fun k h => by
        have := congrArg Complex.re h
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
      positivity
    refine ⟨fun n => (‖Gamma (C w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n),
      (p.summable_norm_mul_pow hz').mul_left _, ?_⟩
    intro n hn w hw
    obtain ⟨hAw, hBw, hCw, hVw⟩ := hU w hw
    have hre : 1 ≤ (C w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using
      norm_term_le_majorant hAw.le hBw.le hre hm (hV _ hVw).le hn

/-- The regularized Gauss function is entire in the parameter `c` (DLMF §15.2(ii)). -/
theorem analyticOnNhd_regularizedGaussHypergeometricFun_c (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b c z) univ :=
  analyticOnNhd_regularizedGaussHypergeometricFun_comp (differentiable_const a)
      (differentiable_const b)
    differentiable_id hz

/-- The regularized Gauss function is entire in the parameter `a` (DLMF §15.2(ii)). -/
theorem analyticOnNhd_regularizedGaussHypergeometricFun_a (b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun a => regularizedGaussHGFun a b c z) univ :=
  analyticOnNhd_regularizedGaussHypergeometricFun_comp differentiable_id (differentiable_const b)
    (differentiable_const c) hz

/-- The regularized Gauss function is entire in the parameter `b` (DLMF §15.2(ii)). -/
theorem analyticOnNhd_regularizedGaussHypergeometricFun_b (a c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun b => regularizedGaussHGFun a b c z) univ :=
  analyticOnNhd_regularizedGaussHypergeometricFun_comp (differentiable_const a) differentiable_id
    (differentiable_const c) hz

/-- Pointwise form of `analyticOnNhd_regularizedGaussHypergeometricFun_comp`, usable by `fun_prop`.
-/
@[fun_prop]
theorem analyticAt_regularizedGaussHypergeometricFun_comp {A B C : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) (w : ℂ) :
    AnalyticAt ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) w :=
  analyticOnNhd_regularizedGaussHypergeometricFun_comp hA hB hC hz w (mem_univ w)

/-- Two entire functions agreeing off the nonpositive integers agree everywhere. -/
theorem eq_of_eqOn_not_neg_nat {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ c : ℂ, (∀ k : ℕ, c ≠ -(k : ℂ)) → f c = g c) : f = g :=
  eq_of_analyticOnNhd_univ_of_eqOn hf hg isOpen_not_neg_nat ⟨1, fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩ h

/-- Two entire functions agreeing on the open right half-plane agree everywhere. -/
theorem eq_of_eqOn_re_pos {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ c : ℂ, 0 < c.re → f c = g c) : f = g :=
  eq_of_analyticOnNhd_univ_of_eqOn hf hg (isOpen_lt continuous_const Complex.continuous_re)
    ⟨1, by simp⟩ h

/-- The coefficient recurrence behind 15.5.1, valid for all parameters. -/
theorem regularizedHGFunCoeff_pair_succ (a b c : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * regularizedHGFunCoeff {a, b} {c} (n + 1) =
      a * b * regularizedHGFunCoeff {a + 1, b + 1} {c + 1} n := by
  have hc1 : regularizedHGFunCoeff {a, b} {c} (n + 1) =
      (regularizedGaussHGFunSeries a b c).coeff (n + 1) := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  have hc2 : regularizedHGFunCoeff {a + 1, b + 1} {c + 1} n =
      (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff n := by
    rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]
  rw [hc1, hc2, coeff_regularizedGaussHGFunSeries, coeff_regularizedGaussHGFunSeries,
    show (ascPochhammer ℂ (n + 1)).eval a = a * (ascPochhammer ℂ n).eval (a + 1) from
      pochhammer_succ_left a n,
    show (ascPochhammer ℂ (n + 1)).eval b = b * (ascPochhammer ℂ n).eval (b + 1) from
      pochhammer_succ_left b n,
    show c + ((n + 1 : ℕ) : ℂ) = c + 1 + n by push_cast; ring, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
  field_simp

/-- 15.5.1 for the regularized function: `𝐅'(a,b;c;z) = a b 𝐅(a+1,b+1;c+1;z)`, with no
hypothesis on the parameters. -/
theorem deriv_regularizedGaussHypergeometricFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (regularizedGaussHGFun a b c) z =
      a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  have hpos : ∀ a b c : ℂ, (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    fun a b c => lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  have hp : HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (ofScalars ℂ (regularizedHGFunCoeff {a, b} {c})) 0
      (regularizedGaussHGFunSeries a b c).radius :=
    (regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall (hpos a b c)
  have hq : HasFPowerSeriesOnBall (regularizedGaussHGFun (a + 1) (b + 1) (c + 1))
      (ofScalars ℂ (regularizedHGFunCoeff {a + 1, b + 1} {c + 1})) 0
      (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).radius :=
    (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).hasFPowerSeriesOnBall (hpos _ _ _)
  have hd := hp.deriv_ofScalars.hasSum_mul_pow
    (mem_eball_radius_regularizedGaussHypergeometricFunSeries a b c hz)
  have hs := (hq.hasSum_mul_pow
    (mem_eball_radius_regularizedGaussHypergeometricFunSeries (a + 1) (b + 1) (c + 1)
        hz)).mul_left (a * b)
  refine hd.unique ?_
  convert hs using 1
  funext n
  rw [← mul_assoc, regularizedHGFunCoeff_pair_succ]

/-- `𝐅(a,b;c;·)` is differentiable on the unit disk. -/
theorem differentiableAt_regularizedGaussHypergeometricFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (regularizedGaussHGFun a b c) z := by
  have hpos : (0 : ENNReal) < (regularizedGaussHGFunSeries a b c).radius :=
    lt_of_lt_of_le (by norm_num) (radius_regularizedGaussHGFunSeries_ge_one a b c)
  exact (((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall hpos).analyticAt_of_mem
    (mem_eball_radius_regularizedGaussHypergeometricFunSeries a b c hz)).differentiableAt

/-- 15.5.2 for the regularized function, with no hypothesis on the parameters:
`𝐅⁽ⁿ⁾(a,b;c;z) = (a)ₙ (b)ₙ 𝐅(a+n,b+n;c+n;z)`. -/
theorem iteratedDeriv_regularizedGaussHypergeometricFun (a b c : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    iteratedDeriv n (regularizedGaussHGFun a b c) z =
      pochhammer a n * pochhammer b n * regularizedGaussHGFun (a + n) (b + n) (c + n) z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, pochhammer_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (regularizedGaussHGFun a b c) =ᶠ[𝓝 z]
        fun w => pochhammer a n * pochhammer b n *
            regularizedGaussHGFun (a + n) (b + n) (c + n) w := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
      exact ih hw
    rw [heq.deriv_eq, deriv_const_mul _
        (differentiableAt_regularizedGaussHypergeometricFun _ _ _ hz),
      deriv_regularizedGaussHypergeometricFun _ _ _ hz, pochhammer_succ, pochhammer_succ,
      show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
      show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring,
      show c + ((n + 1 : ℕ) : ℂ) = c + n + 1 by push_cast; ring]
    ring

/-- `𝐅(a,b;c;z)` is entire in `c` after any translation of `c`. -/
theorem analyticOnNhd_regularizedGaussHypergeometricFun_c_add (a b t : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun c => regularizedGaussHGFun a b (c + t) z) univ :=
  (analyticOnNhd_regularizedGaussHypergeometricFun_c a b hz).comp
    (analyticOnNhd_id.add analyticOnNhd_const) (mapsTo_univ _ _)

/-- The Gauss function and its regularization agree off the poles. -/
theorem regularizedGaussHypergeometricFun_eq_div_Gamma {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (z : ℂ) :
    regularizedGaussHGFun a b c z = ₂F₁ a b c z / Gamma c :=
  (ordinaryHypergeometric_div_Gamma_eq hc).symm

/-- If `c` is not a nonpositive integer, then neither is `c + 1`. -/
theorem not_neg_nat_add_one {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by
  simpa using not_neg_nat_add_nat hc 1

/-- If `c` is not a nonpositive integer, then `c ≠ 0`. -/
theorem ne_zero_of_not_neg_nat {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) : c ≠ 0 := by
  simpa using hc 0

/-- `Γ(c + 1) = c Γ(c)` for `c` not a nonpositive integer. -/
theorem Gamma_succ_of_not_neg_nat {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    Gamma (c + 1) = c * Gamma c :=
  Gamma_add_one c (ne_zero_of_not_neg_nat hc)

/-- Two entire functions agreeing on `{c | c - 1 ∉ -ℕ}` agree everywhere. -/
theorem eq_of_eqOn_not_neg_nat_sub_one {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hg : AnalyticOnNhd ℂ g univ) (h : ∀ c : ℂ, (∀ k : ℕ, c - 1 ≠ -(k : ℂ)) → f c = g c) :
    f = g :=
  eq_of_analyticOnNhd_univ_of_eqOn hf hg
    (isOpen_not_neg_nat.preimage (continuous_id.sub continuous_const)) ⟨2, fun k h => by
      have := congrArg Complex.re h
      simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩ h

/-- Two entire functions that agree off the nonpositive integers agree everywhere. -/
theorem eqFun_of_eqOn_not_neg_nat (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (h : ∀ c : ℂ, (∀ k : ℕ, c ≠ -(k : ℂ)) → f c = g c) (c : ℂ) : f c = g c :=
  congrFun (eq_of_eqOn_not_neg_nat hf hg h) c

/-- The regularized Gauss function as a differentiable function of an entire curve in the
parameters, usable by `fun_prop`. -/
@[fun_prop]
theorem differentiable_regularizedGaussHypergeometricFun_comp {A B C : ℂ → ℂ}
    (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hC : Differentiable ℂ C) {z : ℂ} (hz : ‖z‖ < 1) :
    Differentiable ℂ (fun w => regularizedGaussHGFun (A w) (B w) (C w) z) :=
  fun w => ((analyticOnNhd_regularizedGaussHypergeometricFun_comp hA hB hC hz) w
      (mem_univ w)).differentiableAt

/-- 15.5.11 for the regularized function: `𝐅(a,b;c) = (c-a) 𝐅(a,b;c+1) + a 𝐅(a+1,b;c+1)`. -/
theorem regularizedGaussHypergeometricFun_contiguous_c (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (c - a) * regularizedGaussHGFun a b (c + 1) z +
        a * regularizedGaussHGFun (a + 1) b (c + 1) z :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => regularizedGaussHGFun a b c z)
    (fun c => (c - a) * regularizedGaussHGFun a b (c + 1) z +
      a * regularizedGaussHGFun (a + 1) b (c + 1) z)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have h := contiguous_c (a := a) (b := b) hc hz
      simp only [regularizedGaussHypergeometricFun_eq_div_Gamma hc,
        regularizedGaussHypergeometricFun_eq_div_Gamma hc1, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc]
      linear_combination h) c

/-- 15.5.16 (`contiguous_shift_b`) for the regularized function, valid for all parameters. -/
theorem regularizedGaussHypergeometricFun_contiguous_shift_b (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z - regularizedGaussHGFun a (b + 1) c z =
      -(a * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z :=
  eqFun_of_eqOn_not_neg_nat
    (fun c => regularizedGaussHGFun a b c z - regularizedGaussHGFun a (b + 1) c z)
    (fun c => -(a * z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z)
    (by intro c _; fun_prop (disch := assumption))
    (by intro c _; fun_prop (disch := assumption))
    (fun c hc => by
      have hc1 := not_neg_nat_add_one hc
      have hΓ0 : Gamma c ≠ 0 := Gamma_ne_zero hc
      have hΓ1 := Gamma_succ_of_not_neg_nat hc
      have h := contiguous_shift_b (a := a) (b := b) hc hz
      simp only [regularizedGaussHypergeometricFun_eq_div_Gamma hc,
        regularizedGaussHypergeometricFun_eq_div_Gamma hc1, hΓ1]
      field_simp [hΓ0, ne_zero_of_not_neg_nat hc]
      linear_combination h) c

/-- Identity under the stated parameter and domain assumptions: `regularizedGaussHGFun a b (-n) z
= pochhammer a (n + 1) * pochhammer b (n + 1) / ((n + 1).factorial : ℂ) * z ^ (n + 1) * ₂F₁ (a + n +
1) (b + n + 1) (n + 2) z`. -/
@[dlmf 15.2.E3_5]
theorem regularized_at_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b (-n) z =
      pochhammer a (n + 1) * pochhammer b (n + 1) / ((n + 1).factorial : ℂ) * z ^ (n + 1) *
        ₂F₁ (a + n + 1) (b + n + 1) (n + 2) z := by
  rw [regularizedGaussHypergeometricFun_eq_tsum]
  have hs := summable_regularizedGaussHypergeometricFun_term a b (-n) hz
  rw [← hs.sum_add_tsum_nat_add (n + 1)]
  have hzero : ∀ k ∈ Finset.range (n + 1),
      (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b * z ^ k / k.factorial *
        (Gamma (-(n : ℂ) + k))⁻¹ = 0 := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (-(n : ℂ) + k) = -((n - k : ℕ) : ℂ) := by push_cast [Nat.cast_sub hk']; ring
    rw [this, Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add]
  have hF := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + n + 1) (b + n + 1)
    (n + 2)).hasSum_mul_pow (mem_eball_one_of_norm_lt_one hz)
  rw [← hF.tsum_eq, ← tsum_mul_left]
  congr 1
  funext j
  have hpole : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat, Complex.neg_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hΓ : Gamma ((n : ℂ) + 2 + j) =
      (ascPochhammer ℂ j).eval ((n : ℂ) + 2) * Gamma ((n : ℂ) + 2) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := j) ((n : ℂ) + 2) hpole]
    field_simp [Gamma_ne_zero hpole]
  have hΓ1 : Gamma ((n : ℂ) + 2 + j) = ((n + 1 + j).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 + j = ((n + 1 + j : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ2 : Gamma ((n : ℂ) + 2) = ((n + 1).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ3 : Gamma (-(n : ℂ) + ((n + 1 + j : ℕ) : ℂ)) = (j.factorial : ℂ) := by
    rw [show -(n : ℂ) + ((n + 1 + j : ℕ) : ℂ) = (j : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hp : (ascPochhammer ℂ j).eval ((n : ℂ) + 2) ≠ 0 := pochhammer_ne_zero_of_not_neg_nat hpole j
  have hf1 : ((n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((n + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hΓ1, hΓ2] at hΓ
  simp only [gaussHypergeometricCoeff, pochhammer]
  rw [add_comm j (n + 1), ascPochhammer_eval_add a, ascPochhammer_eval_add b, hΓ3,
    show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
    show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring, pow_add]
  field_simp
  linear_combination (-((ascPochhammer ℂ (n + 1)).eval a * (ascPochhammer ℂ j).eval (a + n + 1) *
    (ascPochhammer ℂ (n + 1)).eval b * (ascPochhammer ℂ j).eval (b + n + 1) *
    z ^ (n + 1) * z ^ j)) * hΓ

/-- The map `(fun c : ℂ => ₂F₁ a b c z / Gamma c)` tends to `(𝓝 (regularizedGaussHGFun a b (-n)
z))` along `(𝓝[≠] (-(n : ℂ)))`. -/
@[dlmf 15.2.E3_5]
theorem tendsto_regularized_at_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun c : ℂ => ₂F₁ a b c z / Gamma c) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedGaussHGFun a b (-n) z)) := by
  have hcont : ContinuousAt (fun c => regularizedGaussHGFun a b c z) (-(n : ℂ)) :=
    ((analyticOnNhd_regularizedGaussHypergeometricFun_c a b hz) _ (Set.mem_univ _)).continuousAt
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsWithin_ne_neg_nat n] with c hc
  exact regularizedGaussHypergeometricFun_eq_div_Gamma hc z

end DLMF.Hypergeometric
