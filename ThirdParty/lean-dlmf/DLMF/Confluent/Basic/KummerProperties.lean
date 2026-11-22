/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Confluent.Basic.Tricomi
public import DLMF.Hypergeometric.Basic.GaussSeries
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Kummer's function: series, equation and transformation

The basic properties of Kummer's function `M(a,c,z) = ₁F₁(a;c;z)` (DLMF §13.2): its relation to
Mathlib's regularized series, the power series with infinite radius, Kummer's differential
equation, uniqueness of entire solutions, Kummer's transformation, and the value of Tricomi's
`U` at zero first parameter.

## Main results

* `kummerM_eq_mul_regularizedHGFun`: `M(a,c,z) = Γ(c) 𝐌(a,c,z)` (DLMF 13.2.4).
* `hasFPowerSeriesOnBall_kummerM`, `analyticOnNhd_kummerM`: Kummer's series has infinite radius
  of convergence, so `M(a,c,·)` is entire.
* `kummerM_ode`: Kummer's equation `z w'' + (c - z) w' - a w = 0` (DLMF 13.2.1).
* `confluent_ode_unique`: entire solutions of Kummer's equation are determined by their value at
  zero when `c` is not a nonpositive integer.
* `kummerM_kummer_transform`: Kummer's transformation `M(a,c,z) = e^z M(c-a,c,-z)`
  (DLMF 13.2.39).
* `kummerM_self`: `M(a,a,z) = e^z` (DLMF 13.6.1).
* `kummerM_eq_sum_neg_nat`: the terminating series at `a = -n`.
* `kummerU_zero`: `U(0,b,z) = 1`, including integer second parameters.
* `hasDerivAt_gaussianPrimitive`: `z M(1/2, 3/2, -z²)` is a primitive of `e^{-z²}`.

## Implementation notes

Kummer's transformation is proved here from the uniqueness of entire solutions of Kummer's
equation. The coefficient proof through the Chu–Vandermonde sum, the confluence limit from
Gauss's function and Euler's integral are in `DLMF.Confluent.KummerProperties`; the Wronskians
and the behaviour of `U` at integer `b` are in `DLMF.Confluent.BasicProperties`.
-/

public section

open Complex Filter
open scoped Real Nat Topology ENNReal
open DLMF.Hypergeometric

noncomputable section

namespace DLMF.Confluent

/-! ### The series -/

/-- `₁F₁(a;a;z) = e^z` when `a` is not a nonpositive integer. -/
@[dlmf 13.6.E1]
theorem kummerM_self {a z : ℂ} (ha : ∀ k : ℕ, a ≠ -k) :
    kummerM a a z = exp z := by
  unfold kummerM
  have hcoeff : ∀ n : ℕ, pochhammer a n / (pochhammer a n * n !) * z ^ n = z ^ n / n ! := by
    intro n
    have hne := pochhammer_ne_zero_of_not_neg_nat ha n
    field [hne]
  simp_rw [hcoeff]
  simpa [exp_eq_exp_ℂ] using (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)) z).symm

/-- A terminating `₁F₁(-n;c;z)` is a polynomial of degree at most `n`. -/
theorem kummerM_eq_sum_neg_nat (n : ℕ) (c z : ℂ) :
    kummerM (-(n : ℂ)) c z =
      ∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℂ)) k /
          (pochhammer c k * k.factorial) * z ^ k := by
  unfold kummerM
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [pochhammer_neg_nat_eq_zero hkn]

/-- The coefficients of the regularized `₁F₁` are `(a)_n / (n! Γ(c+n))`. -/
theorem regularizedHGFunCoeff_singleton (a c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {c} n = pochhammer a n / (n ! * Gamma (c + n)) := by
  simp [regularizedHGFunCoeff, pochhammer]

/-- The regularized generalized hypergeometric function is the sum of its coefficient series. -/
theorem regularizedHGFun_eq_tsum (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  unfold regularizedHGFun regularizedHGFunSeries
  rw [FormalMultilinearSeries.sum]
  simp_rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- The coefficient comparison with Mathlib's regularized confluent series. -/
theorem kummerMCoeff_eq_mul_regularizedHGFunCoeff {a c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    kummerMCoeff a c n = Gamma c * regularizedHGFunCoeff {a} {c} n := by
  have hp : pochhammer c n = Gamma (c + n) / Gamma c :=
    (Gamma_add_nat_div_Gamma_eq (n := n) c hc).symm
  have hc0 : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hc n)
  rw [kummerMCoeff, hp, regularizedHGFunCoeff_singleton]
  field [hc0, hcn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Recover Kummer's `M` from Mathlib's regularized `₁F₁`. -/
@[dlmf 13.2.E4]
theorem kummerM_eq_mul_regularizedHGFun {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    kummerM a c z = Gamma c * regularizedHGFun {a} {c} z := by
  unfold kummerM
  simp_rw [show ∀ n : ℕ, pochhammer a n / (pochhammer c n * n !) =
    Gamma c * regularizedHGFunCoeff {a} {c} n from
      kummerMCoeff_eq_mul_regularizedHGFunCoeff hc]
  rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- Kummer's series has infinite radius, by Mathlib's convergence theorem for the
regularized hypergeometric series. -/
theorem hasFPowerSeriesOnBall_kummerM {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    HasFPowerSeriesOnBall (kummerM a c)
      (FormalMultilinearSeries.ofScalars ℂ (kummerMCoeff a c)) 0 ⊤ := by
  have hr : (regularizedHGFunSeries {a} {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hs : HasFPowerSeriesOnBall (regularizedHGFun {a} {c})
      (regularizedHGFunSeries {a} {c}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {c}).sum
      (regularizedHGFunSeries {a} {c}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {a} {c}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have ht := hs.const_smul (c := Gamma c)
  have hp : Gamma c • regularizedHGFunSeries {a} {c} =
      FormalMultilinearSeries.ofScalars ℂ (kummerMCoeff a c) := by
    rw [regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalars_smul]
    congr 1
    funext n
    exact (kummerMCoeff_eq_mul_regularizedHGFunCoeff hc n).symm
  have hf : Gamma c • regularizedHGFun {a} {c} = kummerM a c := by
    funext z
    exact (kummerM_eq_mul_regularizedHGFun hc).symm
  rwa [hp, hf] at ht

/-- For `b` not a nonpositive integer, `M(a,b,·)` is entire. -/
theorem analyticOnNhd_kummerM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    AnalyticOnNhd ℂ (kummerM a b) Set.univ := fun z _ =>
  (hasFPowerSeriesOnBall_kummerM (a := a) hb).analyticAt_of_mem (by simp)

/-! ### Kummer's equation -/

/-- The coefficient recurrence for the confluent hypergeometric equation. -/
theorem kummerMCoeff_recurrence {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * kummerMCoeff a c (n + 1) =
      (a + n) * kummerMCoeff a c n := by
  have hcp := pochhammer_ne_zero_of_not_neg_nat hc n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [kummerMCoeff, pochhammer_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hcp, hcn, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- The confluent hypergeometric equation
`z y'' + (c-z) y' - a y = 0` (AAR §4.1). -/
@[dlmf 13.2.E1]
theorem kummerM_ode {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    z * iteratedDeriv 2 (kummerM a c) z + (c - z) * deriv (kummerM a c) z -
      a * kummerM a c z = 0 := by
  have h := (hasFPowerSeriesOnBall_kummerM (a := a) hc).ode_of_recurrence
    (A := 0) (B := 1) (C := a) (D := c) (fun n => ?_)
    (z := z) (by simp)
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [kummerMCoeff_recurrence hc]
    ring

/-- Differentiating the confluent equation repeatedly gives the shifted equations. -/
theorem confluent_ode_iteratedDeriv {a c : ℂ} {f : ℂ → ℂ}
    (hf : ∀ w, AnalyticAt ℂ f w)
    (hode : ∀ w, w * deriv (deriv f) w + (c - w) * deriv f w - a * f w = 0)
    (n : ℕ) (w : ℂ) :
    w * iteratedDeriv (n + 2) f w + (c + n - w) * iteratedDeriv (n + 1) f w -
      (a + n) * iteratedDeriv n f w = 0 := by
  have ha (k : ℕ) (z : ℂ) : AnalyticAt ℂ (iteratedDeriv k f) z := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf z
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hd (k : ℕ) (z : ℂ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f z) z := by
    simpa only [iteratedDeriv_succ] using (ha k z).differentiableAt.hasDerivAt
  induction n generalizing w with
  | zero =>
    simpa only [Nat.cast_zero, add_zero, iteratedDeriv_succ, iteratedDeriv_zero] using hode w
  | succ n ih =>
    have he : (id * iteratedDeriv (n + 2) f +
        ((fun _ => c + n) - id) * iteratedDeriv (n + 1) f -
        (fun z => (a + n) * iteratedDeriv n f z)) = (fun _ => 0) := funext ih
    have ht := (((hasDerivAt_id w).mul (hd (n + 2) w)).add
      (((hasDerivAt_const w (c + n)).sub (hasDerivAt_id w)).mul (hd (n + 1) w))).sub
      ((hd n w).const_mul (a + n))
    have he' := ht.deriv
    rw [he, deriv_const] at he'
    simp only [id_eq, one_mul, zero_sub, Pi.sub_apply] at he'
    push_cast
    linear_combination -he'

/-- Entire solutions of the confluent equation are determined by their value at zero
when the denominator parameter is not a nonpositive integer. -/
theorem confluent_ode_unique {a c : ℂ} {f g : ℂ → ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hf : ∀ w, AnalyticAt ℂ f w) (hg : ∀ w, AnalyticAt ℂ g w)
    (hfeq : ∀ w, w * deriv (deriv f) w + (c - w) * deriv f w - a * f w = 0)
    (hgeq : ∀ w, w * deriv (deriv g) w + (c - w) * deriv g w - a * g w = 0)
    (hzero : f 0 = g 0) : f = g := by
  have he (n : ℕ) : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      have hfn := confluent_ode_iteratedDeriv hf hfeq n 0
      have hgn := confluent_ode_iteratedDeriv hg hgeq n 0
      have hcn : c + (n : ℂ) ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
      have hm : (c + n) * (iteratedDeriv (n + 1) f 0 - iteratedDeriv (n + 1) g 0) = 0 := by
        rw [ih] at hfn
        linear_combination hfn - hgn
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hcn)
  apply AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hf w) (fun w _ => hg w) (z₀ := 0)
  have hp := (hf 0).hasFPowerSeriesAt
  have hq := (hg 0).hasFPowerSeriesAt
  simp_rw [he] at hp
  filter_upwards [hp.eventually_hasSum_sub, hq.eventually_hasSum_sub] with w hw₁ hw₂
  exact hw₁.unique hw₂

/-- Kummer's transformation `M(a,c,z) = e^z M(c-a,c,-z)` (AAR (4.1.11), p. 191).
AAR excludes nonpositive integer denominator parameters in §2.1, p. 62; that standing
restriction must be explicit for our totalized series. There is also a typographical error
in the supplied AAR printing: the right-hand denominator in (4.1.11) is printed as `a`
instead of `c`. The formula below uses the intended denominator `c`. -/
@[dlmf 13.2.E39]
theorem kummerM_kummer_transform {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    kummerM a c z = exp z * kummerM (c - a) c (-z) := by
  have hM (α w : ℂ) : AnalyticAt ℂ (kummerM α c) w :=
    (hasFPowerSeriesOnBall_kummerM (a := α) hc).analyticAt_of_mem (by simp)
  have hode (α w : ℂ) : w * deriv (deriv (kummerM α c)) w + (c - w) * deriv (kummerM α c) w -
      α * kummerM α c w = 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using kummerM_ode (a := α) (z := w) hc
  set h := kummerM (c - a) c with hh
  have hd1 (w : ℂ) : HasDerivAt h (deriv h w) w := (hM (c - a) w).differentiableAt.hasDerivAt
  have hd2 (w : ℂ) : HasDerivAt (deriv h) (deriv (deriv h) w) w :=
    (hM (c - a) w).deriv.differentiableAt.hasDerivAt
  have hcomp {F : ℂ → ℂ} {F' : ℂ → ℂ} (hF : ∀ w, HasDerivAt F (F' w) w) (w : ℂ) :
      HasDerivAt (fun w => exp w * F (-w)) (exp w * F (-w) - exp w * F' (-w)) w := by
    have ht := (Complex.hasDerivAt_exp w).mul ((hF (-w)).comp w (hasDerivAt_neg w))
    exact ht.congr_deriv (by simp only [Function.comp_apply]; ring)
  let g : ℂ → ℂ := fun w => exp w * h (-w)
  have hg (w : ℂ) : AnalyticAt ℂ g w :=
    analyticAt_cexp.mul ((hM (c - a) (-w)).comp (analyticAt_id.neg))
  have hgd : deriv g = fun w => exp w * h (-w) - exp w * deriv h (-w) :=
    funext fun w => (hcomp hd1 w).deriv
  have hgd2 (w : ℂ) : deriv (deriv g) w =
      exp w * h (-w) - exp w * deriv h (-w) -
        (exp w * deriv h (-w) - exp w * deriv (deriv h) (-w)) := by
    rw [hgd]
    exact ((hcomp hd1 w).sub (hcomp hd2 w)).deriv
  have hgeq (w : ℂ) : w * deriv (deriv g) w + (c - w) * deriv g w - a * g w = 0 := by
    rw [hgd2, hgd]
    have h1 := hode (c - a) (-w)
    rw [← hh] at h1
    simp only [g]
    linear_combination (-exp w) * h1
  have he := confluent_ode_unique hc (hM a) hg (hode a) hgeq (by simp [g, hh])
  exact congrFun he z

/-! ### Tricomi's function at zero first parameter -/

/-- The connection formula at zero first parameter is identically one away from integers. -/
theorem kummerUConnection_zero (b z : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    kummerUConnection 0 b z = 1 := by
  have hp : ∀ k : ℕ, 1 - b ≠ -(k : ℂ) := by
    intro k hk
    apply hb ((k : ℤ) + 1)
    push_cast
    linear_combination -hk
  simp only [kummerUConnection, kummerM_of_zero_param, Gamma_zero, div_zero,
    zero_mul, add_zero, mul_one]
  rw [show (0 : ℂ) - b + 1 = 1 - b by ring, div_self (Gamma_ne_zero hp)]

/-- The connection formula at zero first parameter converges to one at every second parameter. -/
theorem tendsto_kummerUConnection_zero (b z : ℂ) :
    Tendsto (fun c => kummerUConnection 0 c z) (𝓝[integerComplement] b) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  symm
  apply kummerUConnection_zero c z
  intro k hk
  exact hc ⟨k, hk.symm⟩

/-- Tricomi's value at zero first parameter, including integer second parameters. -/
theorem kummerU_zero (b z : ℂ) : kummerU 0 b z = 1 := by
  classical
  unfold kummerU
  split_ifs with hb
  · exact kummerUConnection_zero b z hb
  · have hd : Dense integerComplement :=
      (Set.countable_range (fun k : ℤ => (k : ℂ))).dense_compl ℂ
    have : NeBot (𝓝[integerComplement] b) :=
      mem_closure_iff_nhdsWithin_neBot.mp (hd b)
    exact (tendsto_kummerUConnection_zero b z).limUnder_eq

/-! ### The Gaussian primitive -/

/-- The coefficient identity for the Gaussian antiderivative. -/
theorem kummerMCoeff_half (n : ℕ) :
    (2 * n + 1 : ℂ) * kummerMCoeff (1 / 2) (3 / 2) n = 1 / n.factorial := by
  have hp : pochhammer (1 / 2 : ℂ) n ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat (fun k hk => by
      have he := congrArg Complex.re hk
      simp at he
      have := Nat.cast_nonneg (α := ℝ) k
      linarith) n
  have hn : (2 * n + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  rw [kummerMCoeff, pochhammer_three_halves_eq]
  field [hp, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- A first-order relation between the confluent series and the exponential. -/
theorem kummerM_half_add_two_mul_deriv (w : ℂ) :
    kummerM (1 / 2) (3 / 2) w +
      2 * w * deriv (kummerM (1 / 2) (3 / 2)) w = exp w := by
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
    intro k hk
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hf := hasFPowerSeriesOnBall_kummerM (a := (1 / 2 : ℂ)) hc
  have hs := (hf.hasSum_mul_pow (z := w) (by simp)).add
    ((hf.hasSum_z_mul_deriv (z := w) (by simp)).mul_left 2)
  have heq : (fun n : ℕ => kummerMCoeff (1 / 2) (3 / 2) n * w ^ n +
      2 * ((n : ℂ) * kummerMCoeff (1 / 2) (3 / 2) n * w ^ n)) =
      (fun n : ℕ => w ^ n / n.factorial) := by
    funext n
    calc
      _ = ((2 * n + 1 : ℂ) * kummerMCoeff (1 / 2) (3 / 2) n) * w ^ n := by ring
      _ = _ := by rw [kummerMCoeff_half]; ring
  rw [heq] at hs
  simpa [mul_assoc] using hs.unique (by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w)

/-- Differentiating the confluent representation gives the Gaussian. -/
theorem hasDerivAt_gaussianPrimitive (z : ℂ) :
    HasDerivAt (fun z : ℂ => z * kummerM (1 / 2) (3 / 2) (-(z ^ 2)))
      (exp (-(z ^ 2))) z := by
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
    intro k hk
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hf := hasFPowerSeriesOnBall_kummerM (a := (1 / 2 : ℂ)) hc
  have hm := (hf.analyticAt_of_mem (y := -(z ^ 2)) (by simp)).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_id z).mul (hm.comp z (((hasDerivAt_id z).pow 2).neg))
  convert! hd using 1
  have h := kummerM_half_add_two_mul_deriv (-(z ^ 2))
  simp only [id_eq, Function.comp_apply, Pi.neg_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
  linear_combination -h

end DLMF.Confluent
