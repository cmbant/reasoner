module

public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw
public import FormalResearch.ModularBootstrap.Upper.Holes.AII
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Analytic Region-II Saddle-Ratio Bound (Lemma K8)

Formalizes Lemma K8 (`cmb:K8`, `cmb:eK8simple`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`
(lines 304--354):

* `vZeroK8`: $v_0(x) = \pi^{-1} \operatorname{arccosh}(\sinh(\pi x))$ for $x > \xi_*$.
* `edgeDerivK8`: $F'(v_0) = \sqrt{1 - 2\operatorname{sech}^2(\pi x)}$.
* `tanhTipK8`: $T(x) = |T_{\xi_*}(x)| = \tanh(\frac{\pi}{2}(x - \xi_*)) \tanh(\frac{\pi}{2}(x + \xi_*))$.
* `vRhoInfty`: $v\rho_\infty(x; n_1) = \frac{1}{2} \bigl(\frac{\sqrt{v_0^2 + 1/4}}{x F'(v_0)}\bigr)^{1/2} \coth(\pi x/2)\, T(x)^{2 n_1}$.
* `arsinh_one_gt_five_sixths`, `pi_div_twelve_lt_xiStar`: $\operatorname{arsinh} 1 > 5/6 > \pi^2 / 12$,
  so $\xi_* > \pi / 12$.
* `vRhoInfty_le`: for every $n_1 \ge 3/4$ and $x > \xi_*$,
  $v\rho_\infty(x; n_1) \le v\rho_\infty(x; 3/4) \le \frac12 (11/8)^{1/4} < 542/1000 < 55/100$.
* `regionII_margin_gt`: combined with `muFour_gt` ($\mu_4 > 7/10$),
  $\mu_4 - v\rho_\infty(x; n_1) > 158/1000 > 13/100$.
-/

@[expose] public section

open Real
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-- Saddle point $v_0(x) = \pi^{-1} \operatorname{arccosh}(\sinh(\pi x))$ (`comb_estimates.tex`, `cmb:K8`). -/
noncomputable def vZeroK8 (x : ℝ) : ℝ :=
  arccoshR (Real.sinh (π * x)) / π

/-- Edge phase derivative $F'(v_0) = \sqrt{1 - 2\operatorname{sech}^2(\pi x)}$ (`comb_estimates.tex`, `cmb:K8`). -/
noncomputable def edgeDerivK8 (x : ℝ) : ℝ :=
  √(1 - 2 / Real.cosh (π * x) ^ 2)

/-- Real Blaschke modulus at the tip $T(x) = \tanh(\frac{\pi}{2}(x - \xi_*))\tanh(\frac{\pi}{2}(x + \xi_*))$. -/
noncomputable def tanhTipK8 (x : ℝ) : ℝ :=
  Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2)

/-- Phase-free Region-II amplitude-to-level ratio $v\rho_\infty(x; n_1)$ (`comb_estimates.tex`, `cmb:K8`). -/
noncomputable def vRhoInfty (x n₁ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ) *
    (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x ^ (2 * n₁)

/-- $\operatorname{arsinh} 1 > 5/6$ and $\pi^2 / 12 < 5/6$, hence $\pi / 12 < \xi_*$. -/
theorem arsinh_one_gt_five_sixths :
    (5 / 6 : ℝ) < Real.arsinh 1 ∧ π ^ 2 / 12 < 5 / 6 := by
  have h_exp_ub : Real.exp (5 / 6 : ℝ) < (231 / 100 : ℝ) := by
    have he := Real.exp_one_lt_d9
    have he5 : Real.exp 5 < (27183 / 10000 : ℝ) ^ 5 := by
      have h := pow_lt_pow_left₀ (by linarith : Real.exp 1 < 27183 / 10000) (Real.exp_pos 1).le
        (by norm_num : 5 ≠ 0)
      rwa [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] at h
    have hpow6 : Real.exp (5 / 6 : ℝ) ^ 6 = Real.exp 5 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hrat : (27183 / 10000 : ℝ) ^ 5 < (231 / 100 : ℝ) ^ 6 := by norm_num
    have h6 : Real.exp (5 / 6 : ℝ) ^ 6 < (231 / 100 : ℝ) ^ 6 := by linarith
    by_contra hge
    push Not at hge
    have h6' := pow_le_pow_left₀ (by norm_num) hge 6
    linarith
  have h_sinh : Real.sinh (5 / 6 : ℝ) < 1 := by
    rw [Real.sinh_eq]
    have h_neg : (100 / 231 : ℝ) < Real.exp (-(5 / 6 : ℝ)) := by
      rw [Real.exp_neg, inv_eq_one_div, lt_div_iff₀ (Real.exp_pos _)]
      linarith
    linarith
  have h_arsinh : (5 / 6 : ℝ) < Real.arsinh 1 := by
    rw [← Real.sinh_lt_sinh, Real.sinh_arsinh]
    exact h_sinh
  have h_pi : π ^ 2 / 12 < 5 / 6 := by
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    nlinarith
  exact ⟨h_arsinh, h_pi⟩

theorem pi_div_twelve_lt_xiStar : π / 12 < xiStar := by
  unfold xiStar
  have hpi := Real.pi_pos
  have h := arsinh_one_gt_five_sixths
  rw [div_lt_div_iff₀ (by norm_num) hpi]
  nlinarith

private lemma tanhTipK8_eq_cosh {x : ℝ} (hx : xiStar < x) :
    tanhTipK8 x = (Real.cosh (π * x) - √2) / (Real.cosh (π * x) + √2) ∧
      0 < tanhTipK8 x ∧ tanhTipK8 x < Real.tanh (π * x / 2) ∧ Real.tanh (π * x / 2) < 1 := by
  have hpi := Real.pi_pos
  have ha := xiStar_pos
  have hcosh_a : Real.cosh (π * xiStar) = √2 := by
    have h := Real.cosh_sq_sub_sinh_sq (π * xiStar)
    rw [sinh_pi_mul_xiStar] at h
    have hpos : 0 < Real.cosh (π * xiStar) := Real.cosh_pos _
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h1 : 0 < Real.tanh (π * (x - xiStar) / 2) :=
    tanh_pos_of_pos (by nlinarith)
  have h2 : 0 < Real.tanh (π * (x + xiStar) / 2) :=
    tanh_pos_of_pos (by nlinarith)
  have htanh_lt_one : ∀ u : ℝ, Real.tanh u < 1 := by
    intro u
    rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos u), Real.sinh_eq, Real.cosh_eq]
    linarith [Real.exp_pos (-u)]
  have h_mono : Real.tanh (π * (x - xiStar) / 2) < Real.tanh (π * x / 2) := by
    have hs : Real.sinh (π * xiStar / 2) > 0 := Real.sinh_pos_iff.mpr (by positivity)
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_lt_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)]
    have hid : Real.sinh (π * (x - xiStar) / 2) * Real.cosh (π * x / 2) -
        Real.sinh (π * x / 2) * Real.cosh (π * (x - xiStar) / 2) =
        -Real.sinh (π * xiStar / 2) := by
      have hsub := Real.sinh_sub (π * (x - xiStar) / 2) (π * x / 2)
      rw [show π * (x - xiStar) / 2 - π * x / 2 = -(π * xiStar / 2) by ring, Real.sinh_neg] at hsub
      linarith
    linarith
  have h_prod_lt : tanhTipK8 x < Real.tanh (π * x / 2) := by
    unfold tanhTipK8
    calc Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2)
        < Real.tanh (π * (x - xiStar) / 2) * 1 := mul_lt_mul_of_pos_left (htanh_lt_one _) h1
      _ = Real.tanh (π * (x - xiStar) / 2) := mul_one _
      _ < Real.tanh (π * x / 2) := h_mono
  have h_eq : tanhTipK8 x = (Real.cosh (π * x) - √2) / (Real.cosh (π * x) + √2) := by
    unfold tanhTipK8
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, div_mul_div_comm]
    have hnum : 2 * Real.sinh (π * (x - xiStar) / 2) * Real.sinh (π * (x + xiStar) / 2) =
        Real.cosh (π * x) - Real.cosh (π * xiStar) := by
      have ha1 := Real.cosh_add (π * (x - xiStar) / 2) (π * (x + xiStar) / 2)
      have hs1 := Real.cosh_sub (π * (x - xiStar) / 2) (π * (x + xiStar) / 2)
      rw [show π * (x - xiStar) / 2 + π * (x + xiStar) / 2 = π * x by ring] at ha1
      rw [show π * (x - xiStar) / 2 - π * (x + xiStar) / 2 = -(π * xiStar) by ring,
        Real.cosh_neg] at hs1
      linarith
    have hden : 2 * Real.cosh (π * (x - xiStar) / 2) * Real.cosh (π * (x + xiStar) / 2) =
        Real.cosh (π * x) + Real.cosh (π * xiStar) := by
      have ha1 := Real.cosh_add (π * (x - xiStar) / 2) (π * (x + xiStar) / 2)
      have hs1 := Real.cosh_sub (π * (x - xiStar) / 2) (π * (x + xiStar) / 2)
      rw [show π * (x - xiStar) / 2 + π * (x + xiStar) / 2 = π * x by ring] at ha1
      rw [show π * (x - xiStar) / 2 - π * (x + xiStar) / 2 = -(π * xiStar) by ring,
        Real.cosh_neg] at hs1
      linarith
    have hch1 : Real.cosh (π * (x - xiStar) / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have hch2 : Real.cosh (π * (x + xiStar) / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have hcd : Real.cosh (π * x) + √2 ≠ 0 := by positivity
    rw [← hcosh_a, ← hnum, ← hden]
    field_simp [hch1, hch2]
  exact ⟨h_eq, mul_pos h1 h2, h_prod_lt, htanh_lt_one _⟩

/-- **Lemma K8** (`cmb:K8`, `cmb:eK8simple`, `comb_estimates.tex` lines 304--354):
For every $n_1 \ge \frac34$ and every $x > \xi_*$,
$v\rho_\infty(x; n_1) \le v\rho_\infty(x; \tfrac34) \le \frac12 (11/8)^{1/4} < 542/1000 < 55/100$. -/
theorem vRhoInfty_le {n₁ x : ℝ} (hn₁ : 3 / 4 ≤ n₁) (hx : xiStar < x) :
    vRhoInfty x n₁ ≤ vRhoInfty x (3 / 4) ∧
      vRhoInfty x (3 / 4) ≤ (1 / 2 : ℝ) * (11 / 8 : ℝ) ^ (1 / 4 : ℝ) ∧
      (1 / 2 : ℝ) * (11 / 8 : ℝ) ^ (1 / 4 : ℝ) < 542 / 1000 ∧
      (542 / 1000 : ℝ) < 55 / 100 := by
  have hpi := Real.pi_pos
  have hx_pos : 0 < x := xiStar_pos.trans hx
  obtain ⟨hT_eq, hT_pos, hT_lt_tanh, htanh_lt_one⟩ := tanhTipK8_eq_cosh hx
  have hT_lt_one : tanhTipK8 x < 1 := hT_lt_tanh.trans htanh_lt_one
  have hC_gt : √2 < Real.cosh (π * x) := by
    have h1 : Real.sinh (π * xiStar) < Real.sinh (π * x) :=
      Real.sinh_lt_sinh.mpr (by nlinarith)
    rw [sinh_pi_mul_xiStar] at h1
    have h2 := Real.cosh_sq_sub_sinh_sq (π * x)
    nlinarith [Real.cosh_pos (π * x), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  -- Step 1: monotonicity in n₁
  have h_n1_mono : vRhoInfty x n₁ ≤ vRhoInfty x (3 / 4) := by
    unfold vRhoInfty
    have hpow : tanhTipK8 x ^ (2 * n₁) ≤ tanhTipK8 x ^ (2 * (3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hT_pos hT_lt_one.le (by linarith)
    have hcoth_nn : 0 ≤ Real.cosh (π * x / 2) / Real.sinh (π * x / 2) := by
      have hs := Real.sinh_pos_iff.mpr (by positivity : 0 < π * x / 2)
      exact div_nonneg (Real.cosh_pos _).le hs.le
    have hpref_nn : 0 ≤ (1 / 2 : ℝ) * (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ) *
        (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) :=
      mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg
        (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hx_pos.le (Real.sqrt_nonneg _))) _)) hcoth_nn
    exact mul_le_mul_of_nonneg_left hpow hpref_nn
  -- Step 2: v₀ < x
  have hv0_lt_x : vZeroK8 x < x := by
    unfold vZeroK8
    have hsh_gt : 1 < Real.sinh (π * x) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
    have hv0_pos : 0 < arccoshR (Real.sinh (π * x)) := arccoshR_pos hsh_gt
    have hcosh : Real.cosh (arccoshR (Real.sinh (π * x))) = Real.sinh (π * x) :=
      cosh_arccoshR hsh_gt.le
    have hlt_cosh : Real.cosh (arccoshR (Real.sinh (π * x))) < Real.cosh (π * x) := by
      rw [hcosh, Real.sinh_eq, Real.cosh_eq]
      linarith [Real.exp_pos (-(π * x))]
    have harg : arccoshR (Real.sinh (π * x)) < π * x := by
      by_contra hge
      push Not at hge
      have hle : Real.cosh (π * x) ≤ Real.cosh (arccoshR (Real.sinh (π * x))) :=
        Real.cosh_le_cosh.mpr (by rw [abs_of_pos (by positivity), abs_of_pos hv0_pos]; exact hge)
      linarith
    exact (div_lt_iff₀ hpi).mpr (by linarith)
  have hv0_nn : 0 ≤ vZeroK8 x := by
    unfold vZeroK8
    have hsh_ge : 1 ≤ Real.sinh (π * x) := by
      rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
    exact div_nonneg (arccoshR_nonneg hsh_ge) hpi.le
  -- Step 3: F'(v₀) ≥ √T
  have hF_ge : √(tanhTipK8 x) ≤ edgeDerivK8 x := by
    unfold edgeDerivK8
    have hC_pos : 0 < Real.cosh (π * x) := Real.cosh_pos _
    have hid : 1 - 2 / Real.cosh (π * x) ^ 2 =
        tanhTipK8 x * ((Real.cosh (π * x) + √2) / Real.cosh (π * x)) ^ 2 := by
      rw [hT_eq]
      have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [hC_pos.ne', (show Real.cosh (π * x) + √2 ≠ 0 by positivity)]
      nlinarith [hsq2]
    rw [hid, Real.sqrt_mul hT_pos.le,
      Real.sqrt_sq (div_nonneg (by positivity) hC_pos.le)]
    have hratio : 1 ≤ (Real.cosh (π * x) + √2) / Real.cosh (π * x) := by
      rw [one_le_div hC_pos]; linarith [Real.sqrt_nonneg 2]
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hratio
  have hF_pos : 0 < edgeDerivK8 x := lt_of_lt_of_le (Real.sqrt_pos.mpr hT_pos) hF_ge
  -- Step 4: coth(π x / 2) * T < 1
  have hcoth_T_lt : (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x < 1 := by
    have hs : 0 < Real.sinh (π * x / 2) := Real.sinh_pos_iff.mpr (by positivity)
    calc (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x
        < (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * Real.tanh (π * x / 2) :=
          mul_lt_mul_of_pos_left hT_lt_tanh (div_pos (Real.cosh_pos _) hs)
      _ = 1 := by rw [Real.tanh_eq_sinh_div_cosh]; field_simp [hs.ne', (Real.cosh_pos _).ne']
  -- Step 5: upper bound in terms of ((1 + 1/(4 x^2)) * T)^(1/4)
  have h_step5 : vRhoInfty x (3 / 4) ≤ (1 / 2 : ℝ) * ((1 + 1 / (4 * x ^ 2)) * tanhTipK8 x) ^ (1 / 4 : ℝ) := by
    unfold vRhoInfty
    have hsqrt_le : √(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x) ≤
        √(1 + 1 / (4 * x ^ 2)) / √(tanhTipK8 x) := by
      have hv_sq : vZeroK8 x ^ 2 + 1 / 4 ≤ x ^ 2 + 1 / 4 := by nlinarith
      have h1 : √(vZeroK8 x ^ 2 + 1 / 4) ≤ x * √(1 + 1 / (4 * x ^ 2)) := by
        calc √(vZeroK8 x ^ 2 + 1 / 4) ≤ √(x ^ 2 + 1 / 4) := Real.sqrt_le_sqrt hv_sq
          _ = √(x ^ 2 * (1 + 1 / (4 * x ^ 2))) := by
              congr 1; field_simp [hx_pos.ne']
          _ = x * √(1 + 1 / (4 * x ^ 2)) := by
              rw [Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx_pos.le]
      calc √(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)
          ≤ (x * √(1 + 1 / (4 * x ^ 2))) / (x * edgeDerivK8 x) := by gcongr
        _ = √(1 + 1 / (4 * x ^ 2)) / edgeDerivK8 x := by field_simp [hx_pos.ne']
        _ ≤ √(1 + 1 / (4 * x ^ 2)) / √(tanhTipK8 x) := by gcongr
    have h_rpow_le : (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ) ≤
        (1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) * tanhTipK8 x ^ (-(1 / 4 : ℝ)) := by
      have h_pow12 := Real.rpow_le_rpow (by positivity) hsqrt_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      refine h_pow12.trans_eq ?_
      rw [Real.div_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), ← Real.rpow_mul hT_pos.le,
        show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num, div_eq_mul_inv,
        ← Real.rpow_neg hT_pos.le]
    have hcoth_pos : 0 < Real.cosh (π * x / 2) / Real.sinh (π * x / 2) :=
      div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.mpr (by positivity))
    calc (1 / 2 : ℝ) * (√(vZeroK8 x ^ 2 + 1 / 4) / (x * edgeDerivK8 x)) ^ (1 / 2 : ℝ) *
          (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x ^ (2 * (3 / 4 : ℝ))
        ≤ (1 / 2 : ℝ) * ((1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) * tanhTipK8 x ^ (-(1 / 4 : ℝ))) *
            (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x ^ (3 / 2 : ℝ) := by
          rw [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num]
          gcongr
      _ = (1 / 2 : ℝ) * ((Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x) *
            ((1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) * tanhTipK8 x ^ (1 / 4 : ℝ)) := by
          have h_split : tanhTipK8 x ^ (-(1 / 4 : ℝ)) * tanhTipK8 x ^ (3 / 2 : ℝ) =
              tanhTipK8 x * tanhTipK8 x ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_add hT_pos, ← Real.rpow_one_add' hT_pos.le (by norm_num)]
            congr 1; norm_num
          calc (1 / 2 : ℝ) * ((1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) * tanhTipK8 x ^ (-(1 / 4 : ℝ))) *
                (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x ^ (3 / 2 : ℝ)
              = (1 / 2 : ℝ) * (Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) *
                  (1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) *
                  (tanhTipK8 x ^ (-(1 / 4 : ℝ)) * tanhTipK8 x ^ (3 / 2 : ℝ)) := by ring
            _ = (1 / 2 : ℝ) * ((Real.cosh (π * x / 2) / Real.sinh (π * x / 2)) * tanhTipK8 x) *
                  ((1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) * tanhTipK8 x ^ (1 / 4 : ℝ)) := by
                rw [h_split]; ring
      _ ≤ (1 / 2 : ℝ) * 1 * ((1 + 1 / (4 * x ^ 2)) ^ (1 / 4 : ℝ) * tanhTipK8 x ^ (1 / 4 : ℝ)) := by
          gcongr
      _ = (1 / 2 : ℝ) * ((1 + 1 / (4 * x ^ 2)) * tanhTipK8 x) ^ (1 / 4 : ℝ) := by
          rw [mul_one, ← Real.mul_rpow (by positivity) hT_pos.le]
  -- Step 6: T ≤ min(1, 3/2 * x^2) and (1 + 1/(4s)) * min(1, 3/2 * s) ≤ 11/8
  have hT_le_lin : tanhTipK8 x ≤ (π / 2) * (x - xiStar) := by
    have htanh_le_id : ∀ z : ℝ, 0 ≤ z → Real.tanh z ≤ z := by
      intro z hz
      rw [Real.tanh_eq_sinh_div_cosh]
      have hs : Real.sinh z ≤ z * Real.cosh z := by
        let g : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
        have hm := monotoneOn_of_deriv_nonneg (f := g) (convex_Icc 0 z)
          ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
          (((differentiable_id.mul Real.differentiable_cosh).sub Real.differentiable_sinh).differentiableOn.mono interior_subset)
          (fun t ht => by
            rw [interior_Icc] at ht
            have hd : HasDerivAt g (t * Real.sinh t) t := by
              have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
              exact h.congr_deriv (by simp)
            change 0 ≤ deriv g t
            rw [hd.deriv]
            exact mul_nonneg ht.1.le (Real.sinh_nonneg_iff.mpr ht.1.le))
        have h0 := hm (Set.left_mem_Icc.mpr hz) (Set.right_mem_Icc.mpr hz) hz
        dsimp [g] at h0
        simp only [zero_mul, Real.sinh_zero, sub_self] at h0
        linarith
      exact (div_le_iff₀ (Real.cosh_pos z)).mpr hs
    unfold tanhTipK8
    have h1 := htanh_le_id (π * (x - xiStar) / 2) (by nlinarith)
    have h2 : Real.tanh (π * (x + xiStar) / 2) < 1 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos _), Real.sinh_eq, Real.cosh_eq]
      linarith [Real.exp_pos (-(π * (x + xiStar) / 2))]
    have h1_pos : 0 < Real.tanh (π * (x - xiStar) / 2) :=
      tanh_pos_of_pos (by nlinarith)
    calc Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2)
        ≤ Real.tanh (π * (x - xiStar) / 2) * 1 := mul_le_mul_of_nonneg_left h2.le h1_pos.le
      _ ≤ (π * (x - xiStar) / 2) := by linarith
      _ = (π / 2) * (x - xiStar) := by ring
  have h_quad_le : (π / 2) * (x - xiStar) ≤ (3 / 2) * x ^ 2 := by
    have h_a : π / 12 < xiStar := pi_div_twelve_lt_xiStar
    have hid : (3 / 2 : ℝ) * x ^ 2 - (π / 2) * (x - xiStar) =
        (3 / 2) * (x - π / 6) ^ 2 + (π / 2) * (xiStar - π / 12) := by ring
    nlinarith [sq_nonneg (x - π / 6)]
  have hT_le_min : tanhTipK8 x ≤ min 1 ((3 / 2) * x ^ 2) :=
    le_min hT_lt_one.le (hT_le_lin.trans h_quad_le)
  have h_prod_11_8 : (1 + 1 / (4 * x ^ 2)) * tanhTipK8 x ≤ 11 / 8 := by
    calc (1 + 1 / (4 * x ^ 2)) * tanhTipK8 x
        ≤ (1 + 1 / (4 * x ^ 2)) * min 1 ((3 / 2) * x ^ 2) := by gcongr
      _ ≤ 11 / 8 := by
          rcases le_or_gt (x ^ 2) (2 / 3) with hs | hs
          · calc (1 + 1 / (4 * x ^ 2)) * min 1 ((3 / 2) * x ^ 2)
                ≤ (1 + 1 / (4 * x ^ 2)) * ((3 / 2) * x ^ 2) :=
                  mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
              _ = (3 / 2) * x ^ 2 + 3 / 8 := by field_simp [hx_pos.ne']; ring
              _ ≤ 11 / 8 := by linarith
          · calc (1 + 1 / (4 * x ^ 2)) * min 1 ((3 / 2) * x ^ 2)
                ≤ (1 + 1 / (4 * x ^ 2)) * 1 :=
                  mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
              _ = 1 + 1 / (4 * x ^ 2) := mul_one _
              _ ≤ 1 + 1 / (4 * (2 / 3)) := by gcongr
              _ = 11 / 8 := by norm_num
  have h_11_8_rpow : (1 / 2 : ℝ) * ((1 + 1 / (4 * x ^ 2)) * tanhTipK8 x) ^ (1 / 4 : ℝ) ≤
      (1 / 2 : ℝ) * (11 / 8 : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by positivity) h_prod_11_8 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    gcongr
  have h_num1 : (1 / 2 : ℝ) * (11 / 8 : ℝ) ^ (1 / 4 : ℝ) < 542 / 1000 := by
    have hpow4 : ((11 / 8 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 11 / 8 := by
      rw [← Real.rpow_natCast ((11 / 8 : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hlt4 : (11 / 8 : ℝ) < (1084 / 1000 : ℝ) ^ 4 := by norm_num
    have hrpow_lt : (11 / 8 : ℝ) ^ (1 / 4 : ℝ) < 1084 / 1000 := by
      by_contra hge
      push Not at hge
      have h4 := pow_le_pow_left₀ (by norm_num) hge 4
      linarith
    linarith
  have h_num2 : (542 / 1000 : ℝ) < 55 / 100 := by norm_num
  exact ⟨h_n1_mono, h_step5.trans h_11_8_rpow, h_num1, h_num2⟩

/-- Combined Region-II margin: $\mu_4 - v\rho_\infty(x; n_1) > 158/1000 > 13/100$
(`comb_estimates.tex`, line 315). -/
theorem regionII_margin_gt {n₁ x : ℝ} (hn₁ : 3 / 4 ≤ n₁) (hx : xiStar < x) :
    (13 / 100 : ℝ) < 158 / 1000 ∧ (158 / 1000 : ℝ) < muFour - vRhoInfty x n₁ := by
  have h1 := muFour_gt
  obtain ⟨h2a, h2b, h2c, _⟩ := vRhoInfty_le hn₁ hx
  refine ⟨by norm_num, ?_⟩
  linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.arsinh_one_gt_five_sixths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.arsinh_one_gt_five_sixths

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.vRhoInfty_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.vRhoInfty_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.regionII_margin_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.regionII_margin_gt

end FormalResearch.ModularBootstrap.Upper.Holes
