/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctJC
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Smooth Hadamard division and even square-root lifting (`ℝ → ℝ`)

Provides:
* `hadamardRem k f x`: Taylor integral remainder dividing out `x^k` when `f^{(j)}(0) = 0` (`j < k`),
  with exact identity `f x = x ^ k * hadamardRem k f x`, explicit iterated derivatives,
  and uniform bounds on compact intervals `Icc (-R) R`.
* `evenLift N g z`: for an even `C^{2N + M}` function `g` on `ℝ` (`M + 1 ≤ N`), constructs a `C^M`
  function on `Ioo (-1) (R ^ 2)` (`1 ≤ R`) satisfying `evenLift N g (x ^ 2) = g x` for all `x`, with
  explicit `JC M` bound `evenLiftBound M N R B` depending only on `M, N, R, B`.

Used to instantiate `CfuTheta` (`fct:comp-cfu`) from `fct_comp_D_part1`, `nfun`/`ntil`, and `theta_hat`
without Whitney extensions or cutoff approximations on the chart range.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff BigOperators

namespace FormalResearch.SignUncertainty

/-! ### 1. Smooth Hadamard division `f(x) = x^k * hadamardRem k f x` -/

/-- Taylor integral remainder dividing out `x^k`:
`hadamardRem k f x = ∫₀¹ ((1 - t)^(k - 1) / (k - 1)!) * f^{(k)}(t * x) dt` for `k ≥ 1`, and `f x` for `k = 0`. -/
noncomputable def hadamardRem (k : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if k = 0 then f x else
    ∫ t in (0 : ℝ)..1, ((1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ)) * iteratedDeriv k f (t * x)

lemma hadamardRem_zero (f : ℝ → ℝ) (x : ℝ) : hadamardRem 0 f x = f x := by
  simp [hadamardRem]

lemma hadamardRem_succ (k : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    hadamardRem (k + 1) f x =
      ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / (Nat.factorial k : ℝ)) * iteratedDeriv (k + 1) f (t * x) := by
  simp [hadamardRem]

lemma hadamardRem_identity {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f)
    (hz : ∀ j < k, iteratedDeriv j f 0 = 0) (x : ℝ) :
    f x = x ^ k * hadamardRem k f x := by
  induction k with
  | zero => simp [hadamardRem]
  | succ k ih =>
    have hfk : ContDiff ℝ k f := hf.of_le (by exact_mod_cast Nat.le_succ k)
    have hzk : ∀ j < k, iteratedDeriv j f 0 = 0 := fun j hj => hz j (Nat.lt_succ_of_lt hj)
    have hprev := ih hfk hzk
    rw [hprev]
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [pow_zero, one_mul, pow_one, hadamardRem_zero, hadamardRem_succ]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, zero_add,
        iteratedDeriv_one]
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => f (s * x)) (x * deriv f (t * x)) t := fun t _ => by
        have h1 : HasDerivAt f (deriv f (t * x)) (t * x) :=
          ((hf.differentiable (by norm_num)) (t * x)).hasDerivAt
        exact (h1.comp t ((hasDerivAt_id t).mul_const x)).congr_deriv (by ring)
      have hc : Continuous fun t : ℝ => x * deriv f (t * x) :=
        continuous_const.mul ((hf.continuous_deriv (by norm_num)).comp (continuous_id.mul continuous_const))
      have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
      have h0 : f 0 = 0 := by simpa [iteratedDeriv_zero] using hz 0 zero_lt_one
      simp only [one_mul, zero_mul, h0, sub_zero] at hint
      rw [intervalIntegral.integral_const_mul] at hint
      exact hint.symm
    · rw [hadamardRem_succ]
      have hrem_eq : hadamardRem k f x =
          ∫ t in (0 : ℝ)..1, ((1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ)) * iteratedDeriv k f (t * x) := by
        simp [hadamardRem, hk0]
      rw [hrem_eq]
      let u : ℝ → ℝ := fun t => -((1 - t) ^ k / (Nat.factorial k : ℝ))
      let v : ℝ → ℝ := fun t => iteratedDeriv k f (t * x)
      have hu_d : ∀ t ∈ uIcc (0 : ℝ) 1,
          HasDerivAt u ((1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ)) t := fun t _ => by
        have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub 1
        have hpow := h1.pow k
        have hd := (hpow.div_const (Nat.factorial k : ℝ)).neg
        refine hd.congr_deriv ?_
        have hkfact : (Nat.factorial k : ℝ) = (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
          cases k with
          | zero => contradiction
          | succ m => simp [Nat.factorial_succ, mul_comm]
        rw [hkfact]
        have hkpos : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
        have hfp : (Nat.factorial (k - 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        field_simp [hkpos, hfp]
      have hfk_cd : ContDiff ℝ 1 (iteratedDeriv k f) := by
        have hf' : ContDiff ℝ ((1 + k : ℕ) : WithTop ℕ∞) f :=
          hf.of_le (by exact_mod_cast le_of_eq (add_comm 1 k))
        have h1 := hf'.iterate_deriv' 1 k
        have heq : deriv^[k] f = iteratedDeriv k f := by ext y; rw [iteratedDeriv_eq_iterate]
        rwa [heq] at h1
      have hv_d : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt v (x * iteratedDeriv (k + 1) f (t * x)) t := fun t _ => by
        have h1 : HasDerivAt (iteratedDeriv k f) (deriv (iteratedDeriv k f) (t * x)) (t * x) :=
          ((hfk_cd.differentiable (by norm_num)) (t * x)).hasDerivAt
        have hcomp := h1.comp t ((hasDerivAt_id t).mul_const x)
        refine hcomp.congr_deriv ?_
        rw [← iteratedDeriv_succ]
        ring
      have hu_int : IntervalIntegrable (fun t => (1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ)) volume 0 1 :=
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      have hv_int : IntervalIntegrable (fun t => x * iteratedDeriv (k + 1) f (t * x)) volume 0 1 := by
        refine Continuous.intervalIntegrable ?_ _ _
        exact continuous_const.mul ((hf.continuous_iteratedDeriv (k + 1) le_rfl).comp
          (continuous_id.mul continuous_const))
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_d hv_d hu_int hv_int
      have hswap : (∫ t in (0 : ℝ)..1, ((1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ)) * iteratedDeriv k f (t * x)) =
          -(∫ t in (0 : ℝ)..1, u t * (x * iteratedDeriv (k + 1) f (t * x))) := by
        have hu1 : u 1 = 0 := by simp [u, hk0]
        have hv0 : v 0 = 0 := by simp [v, hz k (Nat.lt_succ_self k)]
        dsimp only [v] at hibp hv0
        rw [hu1, hv0] at hibp
        linarith [hibp]
      rw [hswap]
      have hfac : (∫ t in (0 : ℝ)..1, u t * (x * iteratedDeriv (k + 1) f (t * x))) =
          -x * ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / (Nat.factorial k : ℝ)) * iteratedDeriv (k + 1) f (t * x) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [u]; ring
      rw [hfac]
      ring

private lemma contDiff_param_weighted {w g : ℝ → ℝ} (hw : Continuous w) {n : ℕ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * x)) ∧
      ∀ r ≤ n, ∀ x : ℝ, iteratedDeriv r (fun y : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * y)) x =
        ∫ t in (0 : ℝ)..1, (w t * t ^ r) * iteratedDeriv r g (t * x) := by
  induction n generalizing w g with
  | zero =>
    refine ⟨?_, fun r hr x => ?_⟩
    · rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero]
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => w t * g (t * x)) ?_ 0 1
      exact (hw.comp continuous_snd).mul (hg.continuous.comp (continuous_snd.mul continuous_fst))
    · obtain rfl : r = 0 := Nat.eq_zero_of_le_zero hr
      simp
  | succ n ih =>
    have hg_n1 : ContDiff ℝ ((n : WithTop ℕ∞) + 1) g := by
      simpa [Nat.cast_add, Nat.cast_one] using hg
    have hg' : ContDiff ℝ n (deriv g) := (contDiff_succ_iff_deriv.mp hg_n1).2.2
    have ih2 := ih (hw.mul continuous_id) hg'
    have hderiv_eq : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * y))
          (∫ t in (0 : ℝ)..1, (w t * t) * deriv g (t * x)) x := by
      intro x
      let F : ℝ → ℝ → ℝ := fun y t => w t * g (t * y)
      let F' : ℝ → ℝ → ℝ := fun y t => (w t * t) * deriv g (t * y)
      have hF_cont : ∀ y, Continuous (F y) := fun y =>
        hw.mul (hg.continuous.comp (continuous_id.mul continuous_const))
      have hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) :=
        ((hw.comp continuous_snd).mul continuous_snd).mul
          ((hg.continuous_deriv (by norm_num)).comp (continuous_snd.mul continuous_fst))
      obtain ⟨B, hB⟩ := (isCompact_closedBall x 1 |>.prod isCompact_Icc).exists_bound_of_continuousOn
        hF'_cont.continuousOn
      have hI := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
        (x₀ := x) (bound := fun _ => B) (Metric.ball_mem_nhds x one_pos)
        (Filter.Eventually.of_forall fun y =>
          (hF_cont y).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
        ((hF_cont x).intervalIntegrable 0 1)
        ((hw.mul continuous_id |>.mul ((hg.continuous_deriv (by norm_num)).comp
          (continuous_id.mul continuous_const))).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
        (ae_of_all _ fun t ht y hy => by
          rw [Set.uIoc_of_le zero_le_one] at ht
          exact hB (y, t) ⟨Metric.ball_subset_closedBall hy, ht.1.le, ht.2⟩)
        (intervalIntegrable_const (μ := volume) (a := (0 : ℝ)) (b := 1) (c := B))
        (ae_of_all _ fun t _ y _ => by
          have hd : HasDerivAt g (deriv g (t * y)) (t * y) :=
            ((hg.differentiable (by norm_num)) (t * y)).hasDerivAt
          exact ((hd.comp y ((hasDerivAt_const y t).mul (hasDerivAt_id y))).const_mul (w t)).congr_deriv
            (by dsimp only [F']; ring))
      exact hI.2
    have hderiv_fun : deriv (fun y : ℝ => ∫ t in (0 : ℝ)..1, w t * g (t * y)) =
        fun x : ℝ => ∫ t in (0 : ℝ)..1, (w t * t) * deriv g (t * x) :=
      funext fun x => (hderiv_eq x).deriv
    refine ⟨?_, fun r hr x => ?_⟩
    · rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => ⟨_, hderiv_eq x⟩, by simp, ?_⟩
      rw [hderiv_fun]
      exact ih2.1
    · cases r with
      | zero => simp
      | succ r =>
        rw [iteratedDeriv_succ', hderiv_fun]
        have heq_f : (fun x : ℝ => ∫ t in (0 : ℝ)..1, (w t * t) * deriv g (t * x)) =
            fun y : ℝ => ∫ t in (0 : ℝ)..1, ((w * id : ℝ → ℝ) t) * deriv g (t * y) := by
          ext y; simp [Pi.mul_apply]
        rw [heq_f, ih2.2 r (Nat.le_of_succ_le_succ hr) x]
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [iteratedDeriv_succ']
        simp only [Pi.mul_apply, id_eq]
        ring

lemma hadamardRem_contDiff_and_iteratedDeriv {k n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (k + n) f) :
    ContDiff ℝ n (hadamardRem k f) ∧
      ∀ r ≤ n, ∀ x : ℝ, iteratedDeriv r (hadamardRem k f) x =
        if k = 0 then iteratedDeriv r f x else
          ∫ t in (0 : ℝ)..1, ((1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) * t ^ r) *
            iteratedDeriv (k + r) f (t * x) := by
  cases k with
  | zero =>
    have hfn : ContDiff ℝ n f := by simpa using hf
    have heq : hadamardRem 0 f = f := funext fun x => hadamardRem_zero f x
    rw [heq]
    exact ⟨hfn, fun r _ x => rfl⟩
  | succ k =>
    have hf' : ContDiff ℝ ((n + (k + 1) : ℕ) : WithTop ℕ∞) f := by
      rw [add_comm n (k + 1)]; exact hf
    have hfk : ContDiff ℝ n (iteratedDeriv (k + 1) f) := by
      have h1 := hf'.iterate_deriv' n (k + 1)
      have heq : deriv^[k + 1] f = iteratedDeriv (k + 1) f := by ext y; rw [iteratedDeriv_eq_iterate]
      rwa [heq] at h1
    have hw : Continuous fun t : ℝ => (1 - t) ^ k / (Nat.factorial k : ℝ) := by fun_prop
    have hp := contDiff_param_weighted hw hfk
    have heq : hadamardRem (k + 1) f =
        fun x => ∫ t in (0 : ℝ)..1, ((1 - t) ^ k / (Nat.factorial k : ℝ)) * iteratedDeriv (k + 1) f (t * x) :=
      funext fun x => hadamardRem_succ k f x
    rw [heq]
    refine ⟨hp.1, fun r hr x => ?_⟩
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    rw [hp.2 r hr x]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hit : iteratedDeriv r (iteratedDeriv (k + 1) f) (t * x) = iteratedDeriv (k + 1 + r) f (t * x) := by
      rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
        show r + (k + 1) = k + 1 + r by omega]
    rw [hit]

lemma abs_iteratedDeriv_hadamardRem_le {k r : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (k + r) f)
    {R B : ℝ} (_hB : 0 ≤ B)
    (hbd : ∀ y : ℝ, |y| ≤ R → |iteratedDeriv (k + r) f y| ≤ B) {x : ℝ} (hx : |x| ≤ R) :
    |iteratedDeriv r (hadamardRem k f) x| ≤ B := by
  have hp := (hadamardRem_contDiff_and_iteratedDeriv hf).2 r le_rfl x
  rw [hp]
  split_ifs with hk
  · subst hk; simpa using hbd x hx
  · rw [← Real.norm_eq_abs]
    have hni := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := B)
      (f := fun t => ((1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) * t ^ r) *
        iteratedDeriv (k + r) f (t * x))
      fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        have ht0 : 0 ≤ t := ht.1.le
        have h01 : 0 ≤ 1 - t := by linarith [ht.2]
        have hwt_nn : 0 ≤ (1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) * t ^ r := by positivity
        have h1 : (1 - t) ^ (k - 1) ≤ 1 := pow_le_one₀ h01 (by linarith)
        have h2 : t ^ r ≤ 1 := pow_le_one₀ ht0 ht.2
        have h3 : (1 : ℝ) ≤ (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
        have hw_le : (1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) * t ^ r ≤ 1 := by
          have hd : (1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]; exact h1.trans h3
          calc (1 - t) ^ (k - 1) / (Nat.factorial (k - 1) : ℝ) * t ^ r
              ≤ 1 * 1 := mul_le_mul hd h2 (pow_nonneg ht0 _) zero_le_one
            _ = 1 := one_mul 1
        have htx : |t * x| ≤ R := by
          rw [abs_mul, abs_of_nonneg ht0]
          exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwt_nn]
        exact (mul_le_mul hw_le (hbd (t * x) htx) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    simpa only [sub_zero, abs_one, mul_one] using hni

/-! ### 2. Smooth even square-root lifting `evenLift` -/

lemma iteratedDeriv_even_odd_zero {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) {k : ℕ} (hk : Odd k) :
    iteratedDeriv k g 0 = 0 := by
  have hcomp : (fun x : ℝ => g (-x)) = g := funext heven
  have hid : iteratedDeriv k (fun x : ℝ => g (-x)) 0 = (-1 : ℝ) ^ k * iteratedDeriv k g (-0) := by
    simpa using iteratedDeriv_comp_neg k g 0
  rw [hcomp, neg_zero, hk.neg_one_pow] at hid
  linarith

lemma iteratedDeriv_even_poly_zero (c : ℕ → ℝ) (N m : ℕ) (hm : m < N) :
    iteratedDeriv (2 * m) (fun x : ℝ => ∑ j ∈ Finset.range N, c j * x ^ (2 * j)) 0 =
      (Nat.factorial (2 * m) : ℝ) * c m := by
  have hsum : iteratedDeriv (2 * m) (fun x : ℝ => ∑ j ∈ Finset.range N, c j * x ^ (2 * j)) 0 =
      ∑ j ∈ Finset.range N, iteratedDeriv (2 * m) (fun x : ℝ => c j * x ^ (2 * j)) 0 := by
    have hfun : (fun x : ℝ => ∑ j ∈ Finset.range N, c j * x ^ (2 * j)) =
        ∑ j ∈ Finset.range N, fun x => c j * x ^ (2 * j) := by ext x; simp
    rw [hfun]
    exact iteratedDeriv_sum (𝕜 := ℝ) (I := Finset.range N) (n := 2 * m) (x := (0 : ℝ))
      fun j _ => (contDiff_const.mul (contDiff_id.pow (2 * j))).contDiffAt
  rw [hsum]
  have hterm : ∀ j : ℕ, iteratedDeriv (2 * m) (fun x : ℝ => c j * x ^ (2 * j)) 0 =
      if j = m then (Nat.factorial (2 * m) : ℝ) * c m else 0 := by
    intro j
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    rcases lt_trichotomy (2 * j) (2 * m) with hlt | heq | hgt
    · have hif : j ≠ m := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
      simp [hif]
    · have hif : j = m := by omega
      subst hif
      simp [Nat.descFactorial_self, mul_comm]
    · have hif : j ≠ m := by omega
      have hpos : 2 * j - 2 * m ≠ 0 := by omega
      simp [hif, zero_pow hpos]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range.mpr hm]

/-- Taylor polynomial in `z = x²` of degree `< N` for an even smooth function `g`. -/
noncomputable def evenTaylorPoly (N : ℕ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * z ^ j

/-- The residual `g(x) - evenTaylorPoly N g (x²)` vanishes to order `< 2 * N` at `x = 0`. -/
lemma evenTaylor_rem_zero {N : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ (2 * N) g) (heven : ∀ x, g (-x) = g x)
    {r : ℕ} (hr : r < 2 * N) :
    iteratedDeriv r (fun x : ℝ => g x - evenTaylorPoly N g (x ^ 2)) 0 = 0 := by
  have hP : ContDiff ℝ r (fun x : ℝ => evenTaylorPoly N g (x ^ 2)) :=
    ContDiff.sum fun j _ => contDiff_const.mul (((contDiff_id.pow 2)).pow j)
  have hg_r : ContDiff ℝ r g := hg.of_le (by exact_mod_cast hr.le)
  have hsub : iteratedDeriv r (fun x : ℝ => g x - evenTaylorPoly N g (x ^ 2)) 0 =
      iteratedDeriv r g 0 - iteratedDeriv r (fun x : ℝ => evenTaylorPoly N g (x ^ 2)) 0 := by
    exact iteratedDeriv_sub hg_r.contDiffAt hP.contDiffAt
  rw [hsub]
  rcases Nat.even_or_odd r with ⟨m, hm⟩ | hodd
  · obtain rfl : r = 2 * m := by omega
    have hmN : m < N := by omega
    have hpoly : (fun x : ℝ => evenTaylorPoly N g (x ^ 2)) =
        fun x : ℝ => ∑ j ∈ Finset.range N,
          (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * x ^ (2 * j) := by
      ext x
      simp only [evenTaylorPoly]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_mul, mul_comm 2 j]
    rw [hpoly, iteratedDeriv_even_poly_zero _ N m hmN]
    have hfp : (Nat.factorial (2 * m) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp [hfp]
    ring
  · have hP_even : ∀ x : ℝ, evenTaylorPoly N g ((-x) ^ 2) = evenTaylorPoly N g (x ^ 2) := fun x => by
      rw [neg_sq]
    rw [iteratedDeriv_even_odd_zero heven hodd, iteratedDeriv_even_odd_zero hP_even hodd, sub_self]

/-- Smooth lifting of an even `C^{2N}` function on `ℝ` to `z = x²`:
`evenLift N g z = P(z) + 1_{z > 0} z^N R(√z)`. -/
noncomputable def evenLift (N : ℕ) (g : ℝ → ℝ) (z : ℝ) : ℝ :=
  evenTaylorPoly N g z +
    if 0 < z then
      z ^ N * hadamardRem (2 * N) (fun x : ℝ => g x - evenTaylorPoly N g (x ^ 2)) (Real.sqrt z)
    else 0

lemma evenLift_sq {N : ℕ} (hN : 1 ≤ N) {g : ℝ → ℝ} (hg : ContDiff ℝ (2 * N) g)
    (heven : ∀ x, g (-x) = g x) (x : ℝ) : evenLift N g (x ^ 2) = g x := by
  have hP_cd : ContDiff ℝ (2 * N) (fun y : ℝ => evenTaylorPoly N g (y ^ 2)) :=
    ContDiff.sum fun j _ => contDiff_const.mul (((contDiff_id.pow 2)).pow j)
  unfold evenLift
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, lt_self_iff_false, ↓reduceIte,
      add_zero, evenTaylorPoly]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj; simp [hj]
    · intro h0; exact absurd (Finset.mem_range.mpr (by omega)) h0
  · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp only [hx2, ↓reduceIte, Real.sqrt_sq_eq_abs]
    have hrem : |x| ^ (2 * N) *
        hadamardRem (2 * N) (fun y : ℝ => g y - evenTaylorPoly N g (y ^ 2)) |x| =
        g |x| - evenTaylorPoly N g (|x| ^ 2) :=
      (hadamardRem_identity (k := 2 * N) (hg.sub hP_cd)
        (fun r hr => evenTaylor_rem_zero hg heven hr) |x|).symm
    have hpow : (x ^ 2) ^ N = |x| ^ (2 * N) := by
      rw [← sq_abs x, ← pow_mul, mul_comm 2 N]
    rw [hpow, hrem, sq_abs]
    have hg_abs : g |x| = g x := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, heven]
    rw [hg_abs]
    ring

/-! ### 3. `ContDiff` and `JC` bounds for `evenLift` -/

structure SqrtTerm where
  c : ℝ
  k : ℕ
  a : ℕ -- `a = 0` gives `1`, `a = 1` gives `√z`
  j : ℕ

private noncomputable def evalTerm (h : ℝ → ℝ) (t : SqrtTerm) (z : ℝ) : ℝ :=
  if 0 < z then t.c * z ^ t.k * (if t.a = 0 then 1 else Real.sqrt z) * iteratedDeriv t.j h (Real.sqrt z) else 0

noncomputable def derivTermList (t : SqrtTerm) : List SqrtTerm :=
  if t.a = 0 then
    [⟨t.c * t.k, t.k - 1, 0, t.j⟩, ⟨t.c / 2, t.k - 1, 1, t.j + 1⟩]
  else
    [⟨t.c * (t.k + 1 / 2), t.k - 1, 1, t.j⟩, ⟨t.c / 2, t.k, 0, t.j + 1⟩]

/-- List-of-terms normal form for `√z` derivatives (`SqrtTerm`). -/
noncomputable def stepTerms : ℕ → List SqrtTerm → List SqrtTerm
  | 0, L => L
  | m + 1, L => stepTerms m (L.flatMap derivTermList)

private noncomputable def evalList (h : ℝ → ℝ) (L : List SqrtTerm) (z : ℝ) : ℝ :=
  (L.map (fun t => evalTerm h t z)).sum

private lemma evalList_append (h : ℝ → ℝ) (A B : List SqrtTerm) (z : ℝ) :
    evalList h (A ++ B) z = evalList h A z + evalList h B z := by
  simp [evalList]

private lemma list_abs_sum_le (L : List ℝ) : |L.sum| ≤ (L.map abs).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le _ _).trans (by gcongr)

private lemma evalTerm_nonpos {h : ℝ → ℝ} (t : SqrtTerm) {z : ℝ} (hz : z ≤ 0) :
    evalTerm h t z = 0 := by
  simp [evalTerm, not_lt.mpr hz]

private lemma evalList_nonpos {h : ℝ → ℝ} (L : List SqrtTerm) {z : ℝ} (hz : z ≤ 0) :
    evalList h L z = 0 := by
  unfold evalList
  have h0 : L.map (fun t => evalTerm h t z) = L.map (fun _ => (0 : ℝ)) :=
    List.map_congr_left fun t _ => evalTerm_nonpos t hz
  rw [h0]
  simp

private lemma evalTerm_continuous {h : ℝ → ℝ} (t : SqrtTerm) (htk : 1 ≤ t.k)
    {n : ℕ} (hh : ContDiff ℝ n h) (htj : t.j ≤ n) :
    Continuous (evalTerm h t) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases lt_trichotomy z 0 with hneg | rfl | hpos
  · exact (continuousAt_const (y := (0 : ℝ))).congr
      (by filter_upwards [Iio_mem_nhds hneg] with w hw; exact (evalTerm_nonpos t hw.le).symm)
  · have hc_h : Continuous (iteratedDeriv t.j h) := hh.continuous_iteratedDeriv t.j (by exact_mod_cast htj)
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc_h.continuousOn (s := Icc (0 : ℝ) 1))
    let M : ℝ := |t.c| * (max B 0)
    have hM0 : 0 ≤ M := by positivity
    have hbd : ∀ w : ℝ, |w| ≤ 1 → |evalTerm h t w| ≤ M * |w| := fun w hw => by
      by_cases hwpos : 0 < w
      · have hw1 : w ≤ 1 := (le_abs_self w).trans hw
        have hsq1 : Real.sqrt w ≤ 1 := (Real.sqrt_le_left zero_le_one).mpr (by simpa using hw1)
        have hmem : Real.sqrt w ∈ Icc (0 : ℝ) 1 := ⟨Real.sqrt_nonneg _, hsq1⟩
        have hh_le : |iteratedDeriv t.j h (Real.sqrt w)| ≤ max B 0 :=
          (Real.norm_eq_abs _ ▸ hB _ hmem).trans (le_max_left _ _)
        have h1a : |(if t.a = 0 then (1 : ℝ) else Real.sqrt w)| ≤ 1 := by
          split_ifs <;> simp [abs_of_nonneg (Real.sqrt_nonneg _), hsq1]
        have hwk : w ^ t.k = w * w ^ (t.k - 1) := by
          cases k : t.k with
          | zero => omega
          | succ m => simp [pow_succ']
        have hwk1 : w ^ (t.k - 1) ≤ 1 := pow_le_one₀ hwpos.le hw1
        simp only [evalTerm, hwpos, ↓reduceIte, abs_mul]
        rw [hwk, abs_mul, abs_of_nonneg (pow_nonneg hwpos.le _)]
        calc |t.c| * (|w| * w ^ (t.k - 1)) * |if t.a = 0 then 1 else Real.sqrt w| * |iteratedDeriv t.j h (Real.sqrt w)|
            ≤ |t.c| * (|w| * 1) * 1 * max B 0 := by gcongr
          _ = M * |w| := by simp only [M]; ring
      · rw [evalTerm_nonpos t (not_lt.mp hwpos), abs_zero]; positivity
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min 1 (ε / (M + 1)), lt_min one_pos (div_pos hε (by linarith)), fun {w} hw => ?_⟩
    have h0 : evalTerm h t 0 = 0 := evalTerm_nonpos t le_rfl
    rw [Real.dist_eq, h0, sub_zero]
    rw [Real.dist_eq, sub_zero] at hw
    have hw1 : |w| ≤ 1 := (hw.le).trans (min_le_left _ _)
    have hw2 : |w| < ε / (M + 1) := hw.trans_le (min_le_right _ _)
    calc |evalTerm h t w| ≤ M * |w| := hbd w hw1
      _ ≤ (M + 1) * |w| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hw2 (by linarith)
      _ = ε := mul_div_cancel₀ ε (by linarith)
  · have hc_h : Continuous (iteratedDeriv t.j h) := hh.continuous_iteratedDeriv t.j (by exact_mod_cast htj)
    have hc_prod : Continuous fun w : ℝ =>
        t.c * w ^ t.k * (if t.a = 0 then 1 else Real.sqrt w) * iteratedDeriv t.j h (Real.sqrt w) := by
      refine (((continuous_const.mul (continuous_pow t.k)).mul ?_).mul (hc_h.comp Real.continuous_sqrt))
      split_ifs
      · exact continuous_const
      · exact Real.continuous_sqrt
    refine hc_prod.continuousAt.congr ?_
    filter_upwards [Ioi_mem_nhds hpos] with w hw
    simp [evalTerm, Set.mem_Ioi.mp hw]

private lemma evalTerm_hasDerivAt_pos {h : ℝ → ℝ} (t : SqrtTerm) (htk : 1 ≤ t.k)
    {n : ℕ} (hh : ContDiff ℝ n h) (htj : t.j + 1 ≤ n) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (evalTerm h t) (evalList h (derivTermList t) z) z := by
  have hsq_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hsq_d : HasDerivAt (fun w : ℝ => Real.sqrt w) ((2 * Real.sqrt z)⁻¹) z := by
    simpa [div_eq_mul_inv, mul_comm] using Real.hasDerivAt_sqrt hz.ne'
  have hh_j : ContDiff ℝ 1 (iteratedDeriv t.j h) := by
    have hh' : ContDiff ℝ ((1 + t.j : ℕ) : WithTop ℕ∞) h :=
      hh.of_le (by exact_mod_cast (by omega : 1 + t.j ≤ n))
    have h1 := hh'.iterate_deriv' 1 t.j
    have heq : deriv^[t.j] h = iteratedDeriv t.j h := by ext y; rw [iteratedDeriv_eq_iterate]
    rwa [heq] at h1
  have hh_d : HasDerivAt (fun w => iteratedDeriv t.j h (Real.sqrt w))
      (iteratedDeriv (t.j + 1) h (Real.sqrt z) * (2 * Real.sqrt z)⁻¹) z := by
    have h1 : HasDerivAt (iteratedDeriv t.j h) (deriv (iteratedDeriv t.j h) (Real.sqrt z)) (Real.sqrt z) :=
      ((hh_j.differentiable (by norm_num)) (Real.sqrt z)).hasDerivAt
    have h2 := h1.comp z hsq_d
    rwa [← iteratedDeriv_succ] at h2
  have hpow_d : HasDerivAt (fun w : ℝ => t.c * w ^ t.k) (t.c * ((t.k : ℝ) * z ^ (t.k - 1))) z := by
    simpa using ((hasDerivAt_pow t.k z).const_mul t.c)
  have hev : (fun w : ℝ => t.c * w ^ t.k * (if t.a = 0 then 1 else Real.sqrt w) * iteratedDeriv t.j h (Real.sqrt w)) =ᶠ[𝓝 z]
      evalTerm h t := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    simp [evalTerm, Set.mem_Ioi.mp hw]
  have hzk : z ^ t.k = z * z ^ (t.k - 1) := by
    cases k : t.k with
    | zero => omega
    | succ m => simp [pow_succ']
  have hsq2 : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
  have hsq_inv : z * (2 * Real.sqrt z)⁻¹ = (1 / 2 : ℝ) * Real.sqrt z := by
    field_simp [hsq_pos.ne']; linarith [hsq2]
  rcases eq_or_ne t.a 0 with ha | ha
  · have hd_ev : HasDerivAt (fun w => t.c * w ^ t.k * 1 * iteratedDeriv t.j h (Real.sqrt w))
        ((t.c * ((t.k : ℝ) * z ^ (t.k - 1))) * iteratedDeriv t.j h (Real.sqrt z) +
          t.c * z ^ t.k * (iteratedDeriv (t.j + 1) h (Real.sqrt z) * (2 * Real.sqrt z)⁻¹)) z := by
      simpa only [mul_one] using hpow_d.fun_mul hh_d
    refine (hd_ev.congr_of_eventuallyEq (by
      filter_upwards [hev] with w hw; simpa [ha] using hw.symm)).congr_deriv ?_
    simp only [evalList, derivTermList, ha, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, evalTerm, hz, one_ne_zero, mul_one]
    rw [hzk]
    calc (t.c * ((t.k : ℝ) * z ^ (t.k - 1))) * iteratedDeriv t.j h (Real.sqrt z) +
          t.c * (z * z ^ (t.k - 1)) * (iteratedDeriv (t.j + 1) h (Real.sqrt z) * (2 * Real.sqrt z)⁻¹)
        = (t.c * (t.k : ℝ)) * z ^ (t.k - 1) * iteratedDeriv t.j h (Real.sqrt z) +
            (t.c / 2) * z ^ (t.k - 1) * (z * (2 * Real.sqrt z)⁻¹ * 2) * iteratedDeriv (t.j + 1) h (Real.sqrt z) := by ring
      _ = _ := by rw [hsq_inv]; ring
  · have hfa : HasDerivAt (fun w : ℝ => t.c * w ^ t.k * Real.sqrt w)
        (t.c * ((t.k : ℝ) * z ^ (t.k - 1)) * Real.sqrt z + t.c * z ^ t.k * (2 * Real.sqrt z)⁻¹) z :=
      hpow_d.fun_mul hsq_d
    have hd_ev := hfa.fun_mul hh_d
    refine (hd_ev.congr_of_eventuallyEq (by
      filter_upwards [hev] with w hw; simpa [ha] using hw.symm)).congr_deriv ?_
    simp only [evalList, derivTermList, ha, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, evalTerm, hz, one_ne_zero, mul_one]
    rw [hzk]
    calc (t.c * ((t.k : ℝ) * z ^ (t.k - 1)) * Real.sqrt z + t.c * (z * z ^ (t.k - 1)) * (2 * Real.sqrt z)⁻¹) *
            iteratedDeriv t.j h (Real.sqrt z) +
          t.c * (z * z ^ (t.k - 1)) * Real.sqrt z * (iteratedDeriv (t.j + 1) h (Real.sqrt z) * (2 * Real.sqrt z)⁻¹)
        = (t.c * (t.k : ℝ) * z ^ (t.k - 1) * Real.sqrt z +
            t.c * z ^ (t.k - 1) * (z * (2 * Real.sqrt z)⁻¹)) * iteratedDeriv t.j h (Real.sqrt z) +
            (t.c * z ^ (t.k - 1) * Real.sqrt z * (z * (2 * Real.sqrt z)⁻¹)) * iteratedDeriv (t.j + 1) h (Real.sqrt z) := by ring
      _ = (t.c * (t.k : ℝ) * z ^ (t.k - 1) * Real.sqrt z +
            t.c * z ^ (t.k - 1) * ((1 / 2 : ℝ) * Real.sqrt z)) * iteratedDeriv t.j h (Real.sqrt z) +
            (t.c * z ^ (t.k - 1) * Real.sqrt z * ((1 / 2 : ℝ) * Real.sqrt z)) * iteratedDeriv (t.j + 1) h (Real.sqrt z) := by
          rw [hsq_inv]
      _ = t.c * ((t.k : ℝ) + 1 / 2) * z ^ (t.k - 1) * Real.sqrt z * iteratedDeriv t.j h (Real.sqrt z) +
            t.c / 2 * (z * z ^ (t.k - 1)) * iteratedDeriv (t.j + 1) h (Real.sqrt z) := by
          ring_nf; rw [Real.sq_sqrt hz.le]; ring

private lemma evalTerm_hasDerivAt_all {h : ℝ → ℝ} (t : SqrtTerm) (htk : 2 ≤ t.k)
    {n : ℕ} (hh : ContDiff ℝ n h) (htj : t.j + 1 ≤ n) (z : ℝ) :
    HasDerivAt (evalTerm h t) (evalList h (derivTermList t) z) z := by
  rcases lt_trichotomy z 0 with hneg | rfl | hpos
  · rw [evalList_nonpos _ hneg.le]
    exact (hasDerivAt_const z 0).congr_of_eventuallyEq
      (by filter_upwards [Iio_mem_nhds hneg] with w hw; exact evalTerm_nonpos t (le_of_lt (Set.mem_Iio.mp hw)))
  · rw [evalList_nonpos _ le_rfl]
    have hc_h : Continuous (iteratedDeriv t.j h) := hh.continuous_iteratedDeriv t.j (by exact_mod_cast (by omega : t.j ≤ n))
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc_h.continuousOn (s := Icc (0 : ℝ) 1))
    let M : ℝ := |t.c| * (max B 0)
    have hM0 : 0 ≤ M := by positivity
    have hbd : ∀ w : ℝ, |w| ≤ 1 → |evalTerm h t w| ≤ M * |w| ^ 2 := fun w hw => by
      by_cases hwpos : 0 < w
      · have hw1 : w ≤ 1 := (le_abs_self w).trans hw
        have hsq1 : Real.sqrt w ≤ 1 := (Real.sqrt_le_left zero_le_one).mpr (by simpa using hw1)
        have hmem : Real.sqrt w ∈ Icc (0 : ℝ) 1 := ⟨Real.sqrt_nonneg _, hsq1⟩
        have hh_le : |iteratedDeriv t.j h (Real.sqrt w)| ≤ max B 0 :=
          (Real.norm_eq_abs _ ▸ hB _ hmem).trans (le_max_left _ _)
        have h1a : |(if t.a = 0 then (1 : ℝ) else Real.sqrt w)| ≤ 1 := by
          split_ifs <;> simp [abs_of_nonneg (Real.sqrt_nonneg _), hsq1]
        have hwk : w ^ t.k = w ^ 2 * w ^ (t.k - 2) := by
          rw [← pow_add, Nat.add_sub_cancel' htk]
        have hwk2 : w ^ (t.k - 2) ≤ 1 := pow_le_one₀ hwpos.le hw1
        simp only [evalTerm, hwpos, ↓reduceIte, abs_mul]
        rw [hwk, abs_mul, abs_pow, abs_of_nonneg (pow_nonneg hwpos.le _)]
        calc |t.c| * (|w| ^ 2 * w ^ (t.k - 2)) * |if t.a = 0 then 1 else Real.sqrt w| * |iteratedDeriv t.j h (Real.sqrt w)|
            ≤ |t.c| * (|w| ^ 2 * 1) * 1 * max B 0 := by gcongr
          _ = M * |w| ^ 2 := by simp only [M]; ring
      · rw [evalTerm_nonpos t (not_lt.mp hwpos), abs_zero]; positivity
    rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhds]
    intro ε hε
    let δ : ℝ := min 1 (ε / (M + 1))
    have hδ : 0 < δ := lt_min one_pos (div_pos hε (by linarith))
    refine Filter.Eventually.mono (nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ)) ?_
    intro w hw
    rw [Real.dist_eq, sub_zero] at hw
    by_cases hw0 : w = 0
    · subst hw0; simp [hε]
    · have hw1 : |w| ≤ 1 := hw.le.trans (min_le_left _ _)
      have hw2 : |w| < ε / (M + 1) := hw.trans_le (min_le_right _ _)
      have h0 : evalTerm h t 0 = 0 := evalTerm_nonpos t le_rfl
      rw [Real.dist_eq, zero_add, h0, sub_zero, sub_zero, smul_eq_mul, abs_mul, abs_inv]
      calc |w|⁻¹ * |evalTerm h t w| ≤ |w|⁻¹ * (M * |w| ^ 2) := mul_le_mul_of_nonneg_left (hbd w hw1) (by positivity)
        _ = M * |w| := by field_simp [abs_ne_zero.mpr hw0]
        _ ≤ (M + 1) * |w| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hw2 (by linarith)
        _ = ε := mul_div_cancel₀ ε (by linarith)
  · exact evalTerm_hasDerivAt_pos t (by omega) hh htj hpos

private lemma evalList_hasDerivAt_all {h : ℝ → ℝ} (L : List SqrtTerm) {n : ℕ} (hh : ContDiff ℝ n h)
    (hk : ∀ t ∈ L, 2 ≤ t.k) (hj : ∀ t ∈ L, t.j + 1 ≤ n) (z : ℝ) :
    HasDerivAt (evalList h L) (evalList h (L.flatMap derivTermList) z) z := by
  induction L with
  | nil =>
    have hev : evalList h [] = fun _ => (0 : ℝ) := funext fun u => by simp [evalList]
    rw [hev]
    simpa [evalList] using hasDerivAt_const z (0 : ℝ)
  | cons t L ih =>
    have hev : evalList h (t :: L) = fun u => evalTerm h t u + evalList h L u := rfl
    rw [hev, List.flatMap_cons, evalList_append]
    exact (evalTerm_hasDerivAt_all t (hk t (by simp)) hh (hj t (by simp)) z).add
      (ih (fun s hs => hk s (by simp [hs])) (fun s hs => hj s (by simp [hs])))

private lemma sqrtPos_contDiff {h : ℝ → ℝ} {n m : ℕ} (hh : ContDiff ℝ n h) (L : List SqrtTerm)
    (hk : ∀ t ∈ L, m + 1 ≤ t.k) (hj : ∀ t ∈ L, t.j + m ≤ n) :
    ContDiff ℝ m (evalList h L) ∧
      ∀ r ≤ m, ∀ z : ℝ, iteratedDeriv r (evalList h L) z = evalList h (stepTerms r L) z := by
  induction m generalizing L with
  | zero =>
    refine ⟨?_, fun r hr z => ?_⟩
    · rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero]
      induction L with
      | nil =>
        have hev : evalList h [] = fun _ => (0 : ℝ) := funext fun u => by simp [evalList]
        rw [hev]; exact continuous_const
      | cons t L ih =>
        have hev : evalList h (t :: L) = fun u => evalTerm h t u + evalList h L u := rfl
        rw [hev]
        exact (evalTerm_continuous t (hk t (by simp)) hh (hj t (by simp))).add
          (ih (fun s hs => hk s (by simp [hs])) (fun s hs => hj s (by simp [hs])))
    · obtain rfl : r = 0 := Nat.eq_zero_of_le_zero hr
      simp [stepTerms]
  | succ m ih =>
    have hderiv : ∀ z : ℝ, HasDerivAt (evalList h L) (evalList h (L.flatMap derivTermList) z) z := fun z =>
      evalList_hasDerivAt_all L hh (fun t ht => by have := hk t ht; omega) (fun t ht => by have := hj t ht; omega) z
    have hdf : deriv (evalList h L) = evalList h (L.flatMap derivTermList) :=
      funext fun z => (hderiv z).deriv
    have hk' : ∀ s ∈ L.flatMap derivTermList, m + 1 ≤ s.k := by
      intro s hs
      rw [List.mem_flatMap] at hs
      obtain ⟨u, hu, hus⟩ := hs
      have hsk := hk u hu
      dsimp only [derivTermList] at hus
      split_ifs at hus <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hus <;>
        rcases hus with rfl | rfl <;> dsimp only at * <;> omega
    have hj' : ∀ s ∈ L.flatMap derivTermList, s.j + m ≤ n := by
      intro s hs
      rw [List.mem_flatMap] at hs
      obtain ⟨u, hu, hus⟩ := hs
      have hsj := hj u hu
      dsimp only [derivTermList] at hus
      split_ifs at hus <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hus <;>
        rcases hus with rfl | rfl <;> dsimp only at * <;> omega
    have ihL := ih (L.flatMap derivTermList) hk' hj'
    refine ⟨?_, fun r hr z => ?_⟩
    · rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun z => ⟨_, hderiv z⟩, by simp, ?_⟩
      rw [hdf]
      exact ihL.1
    · cases r with
      | zero => simp [stepTerms]
      | succ r =>
        rw [iteratedDeriv_succ', hdf, ihL.2 r (Nat.le_of_succ_le_succ hr) z]
        rfl

private lemma evalList_abs_le {h : ℝ → ℝ} (L : List SqrtTerm) {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hh : ∀ t ∈ L, ∀ y : ℝ, |y| ≤ R → |iteratedDeriv t.j h y| ≤ B)
    {z : ℝ} (hz : |z| ≤ R ^ 2) :
    |evalList h L z| ≤ (L.map (fun t => |t.c| * R ^ (2 * t.k + 1) * B)).sum := by
  unfold evalList
  refine (list_abs_sum_le _).trans ?_
  simp only [List.map_map, Function.comp_def]
  refine List.sum_le_sum fun t ht => ?_
  by_cases hzpos : 0 < z
  · have hzR : z ≤ R ^ 2 := (le_abs_self z).trans hz
    have hsq_le : Real.sqrt z ≤ R := (Real.sqrt_le_left (by linarith)).mpr hzR
    have hsq_abs : |Real.sqrt z| ≤ R := by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsq_le
    have h1a : (if t.a = 0 then 1 else Real.sqrt z) ≤ R := by
      split_ifs <;> linarith [Real.sqrt_nonneg z]
    have h1a_nn : 0 ≤ (if t.a = 0 then (1 : ℝ) else Real.sqrt z) := by split_ifs <;> positivity
    have hzk : z ^ t.k ≤ R ^ (2 * t.k) := by
      calc z ^ t.k ≤ (R ^ 2) ^ t.k := pow_le_pow_left₀ hzpos.le hzR _
        _ = R ^ (2 * t.k) := by rw [← pow_mul]
    simp only [evalTerm, hzpos, ↓reduceIte, abs_mul]
    rw [abs_of_nonneg (pow_nonneg hzpos.le _), abs_of_nonneg h1a_nn]
    calc |t.c| * z ^ t.k * (if t.a = 0 then 1 else Real.sqrt z) * |iteratedDeriv t.j h (Real.sqrt z)|
        ≤ |t.c| * R ^ (2 * t.k) * R * B := by
          gcongr
          exact hh t ht (Real.sqrt z) hsq_abs
      _ = |t.c| * R ^ (2 * t.k + 1) * B := by rw [pow_succ]; ring
  · simp [evalTerm_nonpos t (not_lt.mp hzpos)]
    positivity

private lemma stepTerms_invariant (M m : ℕ) (hm : m ≤ M) (L : List SqrtTerm)
    (hL : ∀ t ∈ L, M + 1 ≤ t.k) (jmax : ℕ) (hj : ∀ t ∈ L, t.j ≤ jmax) :
    ∀ t ∈ stepTerms m L, (M - m) + 1 ≤ t.k ∧ t.j ≤ jmax + m := by
  induction m generalizing M L jmax with
  | zero =>
    intro t ht
    exact ⟨by simpa using hL t ht, by simpa using hj t ht⟩
  | succ m ih =>
    intro t ht
    rw [stepTerms] at ht
    have hm1 : m ≤ M - 1 := by omega
    have hk' : ∀ s ∈ L.flatMap derivTermList, (M - 1) + 1 ≤ s.k := by
      intro s hs
      rw [List.mem_flatMap] at hs
      obtain ⟨u, hu, hus⟩ := hs
      have := hL u hu
      dsimp only [derivTermList] at hus
      split_ifs at hus <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hus <;>
        rcases hus with rfl | rfl <;> dsimp only at * <;> omega
    have hj' : ∀ s ∈ L.flatMap derivTermList, s.j ≤ jmax + 1 := by
      intro s hs
      rw [List.mem_flatMap] at hs
      obtain ⟨u, hu, hus⟩ := hs
      have := hj u hu
      dsimp only [derivTermList] at hus
      split_ifs at hus <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hus <;>
        rcases hus with rfl | rfl <;> dsimp only at * <;> omega
    have hstep := ih (M - 1) hm1 (L.flatMap derivTermList) hk' (jmax + 1) hj' t ht
    omega

private lemma evenTaylor_monomial_deriv_bound (N m k : ℕ) {R B x : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hx : |x| ≤ R ^ m) {g : ℝ → ℝ} (h0 : ∀ j < N, |iteratedDeriv (2 * j) g 0| ≤ B) :
    |iteratedDeriv k (fun w : ℝ => ∑ j ∈ Finset.range N,
        (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (m * j)) x| ≤
      (N : ℝ) * ((Nat.factorial (m * N) : ℝ) * R ^ (m ^ 2 * N)) * B := by
  have hsum : iteratedDeriv k (fun w : ℝ => ∑ j ∈ Finset.range N,
        (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (m * j)) x =
      ∑ j ∈ Finset.range N, iteratedDeriv k (fun w : ℝ =>
        (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (m * j)) x := by
    have hfun : (fun w : ℝ => ∑ j ∈ Finset.range N,
          (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (m * j)) =
        ∑ j ∈ Finset.range N, fun w =>
          (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (m * j) := by ext w; simp
    rw [hfun]
    exact iteratedDeriv_sum (𝕜 := ℝ) (I := Finset.range N) (n := k) (x := x)
      fun j _ => (contDiff_const.mul (contDiff_id.pow (m * j))).contDiffAt
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ Finset.range N,
      |iteratedDeriv k (fun w : ℝ => (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (m * j)) x| ≤
        (Nat.factorial (m * N) : ℝ) * R ^ (m ^ 2 * N) * B := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow, ← mul_assoc, abs_mul, abs_mul]
    have hc_le : |iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)| ≤ B := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Nat.factorial (2 * j) : ℝ))]
      exact (div_le_self hB (by exact_mod_cast Nat.factorial_pos _)).trans'
        (div_le_div_of_nonneg_right (h0 j hjN) (by positivity))
    have hd_le : |((m * j).descFactorial k : ℝ)| ≤ (Nat.factorial (m * N) : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
      rcases lt_or_ge (m * j) k with hlt | hge
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]; simp
      · have hle : (m * j).descFactorial k ≤ (m * j).factorial := by
          calc (m * j).descFactorial k = 1 * (m * j).descFactorial k := (one_mul _).symm
            _ ≤ (m * j - k).factorial * (m * j).descFactorial k :=
                Nat.mul_le_mul_right _ (Nat.factorial_pos _)
            _ = (m * j).factorial := Nat.factorial_mul_descFactorial hge
        exact_mod_cast hle.trans (Nat.factorial_le (Nat.mul_le_mul_left m hjN.le))
    have hx_le : |x ^ (m * j - k)| ≤ R ^ (m ^ 2 * N) := by
      rw [abs_pow]
      calc |x| ^ (m * j - k) ≤ (R ^ m) ^ (m * j - k) := pow_le_pow_left₀ (abs_nonneg _) hx _
        _ = R ^ (m * (m * j - k)) := by rw [← pow_mul]
        _ ≤ R ^ (m ^ 2 * N) := pow_le_pow_right₀ hR (by
          rw [sq, mul_assoc]
          exact Nat.mul_le_mul_left m ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left m hjN.le)))
    calc |iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)| * |((m * j).descFactorial k : ℝ)| * |x ^ (m * j - k)|
        ≤ B * (Nat.factorial (m * N) : ℝ) * R ^ (m ^ 2 * N) := by gcongr
      _ = (Nat.factorial (m * N) : ℝ) * R ^ (m ^ 2 * N) * B := by ring
  calc ∑ j ∈ Finset.range N, _ ≤ ∑ _ ∈ Finset.range N, (Nat.factorial (m * N) : ℝ) * R ^ (m ^ 2 * N) * B :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) * ((Nat.factorial (m * N) : ℝ) * R ^ (m ^ 2 * N)) * B := by simp [mul_assoc]

/-- Explicit uniform `C^M` bound for `evenLift N g` on `Ioo (-1) (R ^ 2)` in terms of `M, N, R, B`. -/
noncomputable def evenLiftBound (M N : ℕ) (R B : ℝ) : ℝ :=
  let Bf := B + (N : ℝ) * ((Nat.factorial (2 * N) : ℝ) * R ^ (2 ^ 2 * N)) * B
  let Bp := (N : ℝ) * ((Nat.factorial N : ℝ) * (R ^ 2) ^ (1 ^ 2 * N)) * B
  Bp + ∑ r ∈ Finset.range (M + 1),
    ((stepTerms r [⟨1, N, 0, 0⟩]).map (fun t => |t.c| * R ^ (2 * t.k + 1) * Bf)).sum

lemma evenLiftBound_nonneg (M N : ℕ) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) :
    0 ≤ evenLiftBound M N R B := by
  unfold evenLiftBound
  refine add_nonneg (by positivity) (Finset.sum_nonneg fun r _ => List.sum_nonneg fun x hx => ?_)
  rw [List.mem_map] at hx; obtain ⟨t, _, rfl⟩ := hx; positivity

/-- `evenLift N g` is `C^M` on `Ioo (-1) (R^2)` with uniform jet bound `evenLiftBound M N R B`. -/
lemma evenLift_jc {M N : ℕ} (hMN : M + 1 ≤ N) {R B : ℝ} (hR : 1 ≤ R) (hB : 0 ≤ B)
    {g : ℝ → ℝ} (hg : ContDiff ℝ (2 * N + M) g)
    (hbd : ∀ k ≤ 2 * N + M, ∀ y : ℝ, |y| ≤ R → |iteratedDeriv k g y| ≤ B) :
    JC M (Ioo (-1 : ℝ) (R ^ 2)) (evenLift N g) (evenLiftBound M N R B) := by
  let P : ℝ → ℝ := evenTaylorPoly N g
  let f : ℝ → ℝ := fun x => g x - P (x ^ 2)
  let h : ℝ → ℝ := hadamardRem (2 * N) f
  have hP_cd : ContDiff ℝ (⊤ : ℕ∞) P := ContDiff.sum fun j _ => contDiff_const.mul (contDiff_id.pow j)
  have hPx2_cd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => P (x ^ 2)) :=
    ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_id.pow 2).pow j)
  have hf_cd : ContDiff ℝ (2 * N + M) f := hg.sub (hPx2_cd.of_le (WithTop.coe_le_coe.mpr le_top))
  have hh_cd : ContDiff ℝ M h := (hadamardRem_contDiff_and_iteratedDeriv hf_cd).1
  have hE_eq : evenLift N g = fun z => P z + evalList h [⟨1, N, 0, 0⟩] z := by
    ext z; simp [evenLift, evalList, evalTerm, P, h, f, iteratedDeriv_zero]
  have hL_cd := sqrtPos_contDiff hh_cd [⟨1, N, 0, 0⟩]
    (fun t ht => by simp at ht; rw [ht]; exact hMN) (fun t ht => by simp at ht; rw [ht]; simp)
  have hE_cd : ContDiff ℝ M (evenLift N g) := hE_eq ▸ (hP_cd.of_le (WithTop.coe_le_coe.mpr le_top)).add hL_cd.1
  refine ⟨hE_cd.contDiffOn, fun r hr z hz => ?_⟩
  rw [iteratedFDerivWithin_of_isOpen r isOpen_Ioo hz, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
  have hz_abs : |z| ≤ R ^ 2 := abs_le.mpr ⟨by linarith [hz.1], hz.2.le⟩
  have h0_bd : ∀ j < N, |iteratedDeriv (2 * j) g 0| ≤ B := fun j hj =>
    hbd (2 * j) (by omega) 0 (by rw [abs_zero]; linarith)
  have hP_eq : P = fun w : ℝ => ∑ j ∈ Finset.range N,
      (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (1 * j) := by
    ext w; simp [P, evenTaylorPoly]
  have hPx2_eq : (fun w : ℝ => P (w ^ 2)) = fun w : ℝ => ∑ j ∈ Finset.range N,
      (iteratedDeriv (2 * j) g 0 / (Nat.factorial (2 * j) : ℝ)) * w ^ (2 * j) := by
    ext w; simp only [P, evenTaylorPoly]; refine Finset.sum_congr rfl fun j _ => ?_; rw [← pow_mul, mul_comm 2 j]
  have hP_bd : ∀ i ≤ M, |iteratedDeriv i P z| ≤ (N : ℝ) * ((Nat.factorial N : ℝ) * (R ^ 2) ^ (1 ^ 2 * N)) * B :=
    fun i _ => by
      rw [hP_eq]
      simpa only [one_mul] using evenTaylor_monomial_deriv_bound N 1 i h1 hB (by simpa using hz_abs) h0_bd
  let Bf := B + (N : ℝ) * ((Nat.factorial (2 * N) : ℝ) * R ^ (2 ^ 2 * N)) * B
  have hBf0 : 0 ≤ Bf := by positivity
  have hf_bd : ∀ k ≤ 2 * N + M, ∀ y : ℝ, |y| ≤ R → |iteratedDeriv k f y| ≤ Bf := fun k hk y hy => by
    have hsub : iteratedDeriv k f y = iteratedDeriv k g y - iteratedDeriv k (fun w : ℝ => P (w ^ 2)) y :=
      iteratedDeriv_sub (hg.of_le (by exact_mod_cast hk)).contDiffAt ((hPx2_cd.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    rw [hsub, hPx2_eq]
    exact (abs_sub _ _).trans (add_le_add (hbd k hk y hy)
      (evenTaylor_monomial_deriv_bound N 2 k hR hB (hy.trans (by nlinarith)) h0_bd))
  have hh_bd : ∀ j ≤ M, ∀ y : ℝ, |y| ≤ R → |iteratedDeriv j h y| ≤ Bf := fun j hj y hy =>
    abs_iteratedDeriv_hadamardRem_le (hf_cd.of_le (by exact_mod_cast (show 2 * N + j ≤ 2 * N + M by omega)))
      hBf0 (fun y' hy' => hf_bd (2 * N + j) (by omega) y' hy') hy
  have hEr : iteratedDeriv r (evenLift N g) z = iteratedDeriv r P z + iteratedDeriv r (evalList h [⟨1, N, 0, 0⟩]) z := by
    rw [hE_eq]
    exact iteratedDeriv_add ((hP_cd.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
      ((hL_cd.1.of_le (by exact_mod_cast hr)).contDiffAt)
  rw [hEr, hL_cd.2 r hr z]
  have hstep := stepTerms_invariant M r hr [⟨1, N, 0, 0⟩]
    (fun t ht => by simp at ht; rw [ht]; exact hMN) 0 (fun t ht => by simp at ht; rw [ht])
  have hL_bd : |evalList h (stepTerms r [⟨1, N, 0, 0⟩]) z| ≤
      ((stepTerms r [⟨1, N, 0, 0⟩]).map (fun t => |t.c| * R ^ (2 * t.k + 1) * Bf)).sum :=
    evalList_abs_le _ hR hBf0 (fun t ht y hy => hh_bd t.j (by have := (hstep t ht).2; omega) y hy) hz_abs
  have hL_sum : ((stepTerms r [⟨1, N, 0, 0⟩]).map (fun t => |t.c| * R ^ (2 * t.k + 1) * Bf)).sum ≤
      ∑ i ∈ Finset.range (M + 1),
        ((stepTerms i [⟨1, N, 0, 0⟩]).map (fun t => |t.c| * R ^ (2 * t.k + 1) * Bf)).sum := by
    refine Finset.single_le_sum (f := fun i =>
        ((stepTerms i [⟨1, N, 0, 0⟩]).map (fun t => |t.c| * R ^ (2 * t.k + 1) * Bf)).sum)
      (fun i _ => List.sum_nonneg fun x hx => by
        rw [List.mem_map] at hx; obtain ⟨t, _, rfl⟩ := hx; positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  refine (abs_add_le _ _).trans ?_
  unfold evenLiftBound
  exact add_le_add (hP_bd r hr) (hL_bd.trans hL_sum)

/-- info: 'FormalResearch.SignUncertainty.evenLift_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evenLift_jc

end FormalResearch.SignUncertainty
