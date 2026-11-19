/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.Pochhammer
public import DLMF.Hypergeometric.Basic.GaussCoefficients
public import DLMF.Hypergeometric.Basic.PrincipalBranch
public import DLMF.Hypergeometric.Basic.AppellF4
public import DLMF.Hypergeometric.Basic.GaussEquation
public import DLMF.Hypergeometric.Basic.ParameterAnalyticity
public import DLMF.Hypergeometric.Basic.CutPlane
public import DLMF.Hypergeometric.Basic.GaussSeries

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Elementary special values of the hypergeometric series (AAR §2.1)

Mathlib defines `ordinaryHypergeometric` (`₂F₁`) and proves that its radius of convergence is
`1` (or `⊤` when the series terminates); AAR Theorem 2.1.1 for `p = 2`, `q = 1` is that
statement. The definitions of this area are in `DLMF.Hypergeometric.Basic`, and the series
facts of §15.2(i) (the terminating identity 15.2.4, absolute convergence on the unit circle,
the binomial case 15.4.6) are in `DLMF.Hypergeometric.Basic.GaussSeries`.

## Main results

* `regularizedGaussHypergeometric_zero`: the constant term of Mathlib’s regularized series,
  including the zeros of reciprocal Gamma at exceptional lower parameters.

* `log_one_add_eq_ordinaryHypergeometric`: `log(1+x) = x ₂F₁(1,1;2;-x)`, DLMF 15.4.1.
* `arctan_eq_ordinaryHypergeometric`: `arctan x = x ₂F₁(1/2,1;3/2;-x²)`, DLMF 15.4.3.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §2.1.
-/

public section

open Complex Filter Nat
open scoped Topology Real

noncomputable section

namespace DLMF.Hypergeometric

/-- The regularized Gauss value at zero is reciprocal Gamma for every lower parameter,
including the nonpositive integers where the reciprocal Gamma factor vanishes. -/
theorem regularizedGaussHypergeometric_zero (a b c : ℂ) :
    regularizedGaussHypergeometric a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHypergeometric_eq_regularizedGaussHypergeometricFun _ _ _ (by simp)]
  have h := Complex.regularizedHGFun_zero (a := {a, b}) (b := {c})
  simpa [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFun,
    regularizedHGFunCoeff] using h

/-- The coefficients of `₂F₁(1, 1; 2; z)` are `1/(n + 1)`. -/
theorem gaussHypergeometricCoeff_one_one_two (n : ℕ) : gaussHypergeometricCoeff 1 1 2 n = 1 /
    (n + 1 : ℂ) := by
  have hfact : ((n + 1)! : ℂ) = (n ! : ℂ) * (n + 1) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm]
  rw [gaussHypergeometricCoeff, pochhammer_nat_one, pochhammer_nat_two, hfact]
  field [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

/-- The series `₂F₁(1, 1; 2; z)` has radius of convergence `1`. -/
theorem radius_ordinaryHypergeometric_one_one_two :
    (ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2).radius = 1 :=
  ordinaryHypergeometricSeries_radius_eq_one ℂ (1 : ℂ) 1 2 fun kn => by
    have hk : (0 : ℝ) ≤ kn := Nat.cast_nonneg kn
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have : (kn : ℝ) = -1 := by simpa using congrArg Complex.re h
      linarith [hk]
    · intro h
      have : (kn : ℝ) = -1 := by simpa using congrArg Complex.re h
      linarith [hk]
    · intro h
      have : (kn : ℝ) = -2 := by simpa using congrArg Complex.re h
      linarith [hk]

/-- Helper lemma for `log_one_add_eq_ordinaryHypergeometric`: the series of `₂F₁(1,1;2;-x)`. -/
theorem hasSum_ordinaryHypergeometric_one_one_two {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-x) ^ n / (n + 1 : ℂ)) (₂F₁ (1 : ℂ) 1 2 (-x)) := by
  have hmem : -x ∈ Metric.eball (0 : ℂ)
      (ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2).radius := by
    rw [radius_ordinaryHypergeometric_one_one_two]
    exact mem_eball_one_of_norm_lt_one (by simpa)
  have hs := (ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2).hasSum hmem
  have heq : (fun n : ℕ => ordinaryHypergeometricSeries ℂ (1 : ℂ) 1 2 n fun _ => -x) =
      fun n : ℕ => (-x) ^ n / (n + 1 : ℂ) := by
    refine funext fun (n : ℕ) => ?_
    rw [ordinaryHypergeometricSeries_apply_eq]
    change ordinaryHypergeometricCoefficient 1 1 2 n • (-x) ^ n = _
    rw [ordinaryHypergeometricCoefficient_eq, gaussHypergeometricCoeff_one_one_two, smul_eq_mul]
    ring
  rwa [heq] at hs

/-- AAR (2.1.3): `log(1+x) = x · ₂F₁(1,1;2;-x)` for `|x| < 1`. -/
@[dlmf 15.4.E1]
theorem log_one_add_eq_ordinaryHypergeometric {x : ℂ} (hx : ‖x‖ < 1) :
    log (1 + x) = x * ₂F₁ (1 : ℂ) 1 2 (-x) := by
  have hx' : ‖-x‖ < 1 := by simpa
  have hF := (hasSum_ordinaryHypergeometric_one_one_two hx).mul_left x
  have hlog : HasSum (fun n : ℕ => x * ((-x) ^ n / (n + 1 : ℂ))) (log (1 + x)) := by
    have h := (hasSum_taylorSeries_neg_log' hx').neg
    have heq : (fun n : ℕ => -((-x) ^ (n + 1) / (n + 1 : ℂ))) =
        fun n : ℕ => x * ((-x) ^ n / (n + 1 : ℂ)) := by
      refine funext fun (n : ℕ) => ?_
      rw [pow_succ]
      ring
    have hlog' : - -log (1 - -x) = log (1 + x) := by simp [sub_neg_eq_add]
    rw [hlog'] at h
    rwa [heq] at h
  exact hlog.unique hF

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`. -/
theorem gaussHypergeometricCoeff_half_one_three_halves (n : ℕ) :
    gaussHypergeometricCoeff (1 / 2) 1 (3 / 2) n = 1 / (2 * n + 1 : ℂ) := by
  have hne : (2 * n + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    intro h
    have : (2 * n + 1 : ℝ) = 0 := by simpa using congrArg Complex.re h
    linarith
  have hp : pochhammer (1 / 2 : ℂ) n ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat (fun k hk => by
      have : ((1 : ℝ) / 2) = -k := by simpa using congrArg Complex.re hk
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith) n
  rw [gaussHypergeometricCoeff, pochhammer_nat_one, pochhammer_three_halves_eq]
  field [Nat.cast_ne_zero.mpr n.factorial_ne_zero, hne, hp]

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`. -/
theorem radius_ordinaryHypergeometric_half_one_three_halves :
    (ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2)).radius = 1 :=
  ordinaryHypergeometricSeries_radius_eq_one ℂ (1 / 2 : ℂ) 1 (3 / 2) fun kn => by
    have hk : (0 : ℝ) ≤ kn := Nat.cast_nonneg kn
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hk]
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hk]
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith [hk]

/-- Helper lemma for `arctan_eq_ordinaryHypergeometric`: the series of
`₂F₁(1/2,1;3/2;-x²)`. -/
theorem hasSum_ordinaryHypergeometric_half_one_three_halves {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => (-(x ^ 2)) ^ n / (2 * n + 1 : ℂ))
      (₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (-(x ^ 2))) := by
  have hx2 : ‖-(x ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hmem : -(x ^ 2) ∈ Metric.eball (0 : ℂ)
      (ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2)).radius := by
    rw [radius_ordinaryHypergeometric_half_one_three_halves]
    exact mem_eball_one_of_norm_lt_one hx2
  have hs := (ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2)).hasSum hmem
  have heq :
      (fun n : ℕ => ordinaryHypergeometricSeries ℂ (1 / 2 : ℂ) 1 (3 / 2) n fun _ => -(x ^ 2)) =
        fun n : ℕ => (-(x ^ 2)) ^ n / (2 * n + 1 : ℂ) := by
    refine funext fun (n : ℕ) => ?_
    rw [ordinaryHypergeometricSeries_apply_eq]
    change ordinaryHypergeometricCoefficient (1 / 2) 1 (3 / 2) n • (-(x ^ 2)) ^ n = _
    rw [ordinaryHypergeometricCoefficient_eq,
        gaussHypergeometricCoeff_half_one_three_halves, smul_eq_mul]
    ring
  rwa [heq] at hs

/-- AAR (2.1.4): `arctan x = x · ₂F₁(1/2,1;3/2;-x²)` for `|x| < 1`. -/
@[dlmf 15.4.E3]
theorem arctan_eq_ordinaryHypergeometric {x : ℂ} (hx : ‖x‖ < 1) :
    arctan x = x * ₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (-(x ^ 2)) := by
  have hF := (hasSum_ordinaryHypergeometric_half_one_three_halves hx).mul_left x
  have hart : HasSum (fun n : ℕ => x * ((-(x ^ 2)) ^ n / (2 * n + 1 : ℂ))) (arctan x) := by
    have h := hasSum_arctan hx
    have heq : (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / ↑(2 * n + 1)) =
        fun n : ℕ => x * ((-(x ^ 2)) ^ n / (2 * n + 1 : ℂ)) := by
      refine funext fun (n : ℕ) => ?_
      have hn : (-(x ^ 2)) ^ n = (-1) ^ n * x ^ (2 * n) := by
        rw [neg_pow (x ^ 2), pow_mul]
      rw [hn, pow_succ]
      push_cast
      ring
    rwa [heq] at h
  exact hart.unique hF

end DLMF.Hypergeometric
