module

public import FormalResearch.ModularBootstrap.Bessel.Defs
public import FormalResearch.ModularBootstrap.Crossing.Setup
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Crossing Sum Rule at Fixed Weight `(H_w)`

Formalizes Section `fw:s11` of `/home/user/scratch/mb/pr240/CFT/modular_bootstrap/paper/crossing_sum_rule.tex`:
* Integral representation and uniform upper/lower bounds for modified Bessel functions `I_n(z)`.
* Cartesian Cardy density `ϱ(x) = ρ_C(‖x‖² / 2)` on `ℝ^{2w}` with exponential growth
  sandwich `c W₀(x) ≤ ϱ(x) ≤ C W₀(x)` at infinity.
* Mehler kernel `K_r(x, y)` and regularisation `A_r f`, with Gaussian kernel bounds, mass
  limit `A_r f → f`, compact-support negative-part convergence `∫ A_r f_- dν → ∫ f_- dν`, and
  exponential-polynomial weight bound `A_r W ≤ C' W`.
* Lemma FW-A (`fw:abel`), isolating Hermite/Laguerre `L²` completeness in `MehlerOddMomentInput`.
* Lemma FW-X (`fw:crossing`) (one-sided sum rule, counting bound `fw:counting`, equality) and
  Theorem FW-C (`fw:FWC`) certification.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace ENNReal

namespace FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: Modified Bessel function `I_n` and Cardy density comparison -/

/-- The power series of `Bessel.besselI n z`: `∑_{k ≥ 0} (z / 2)^{2k + n} / (k! (k + n)!)`. -/
lemma besselI_eq_tsum (n : ℕ) (z : ℝ) :
    Bessel.besselI n z =
      ∑' k : ℕ, (z / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * ((k + n).factorial : ℝ)) := by
  unfold Bessel.besselI Bessel.besselS Bessel.besselTerm
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have h : (z / 2) ^ (2 * k + n) = (z / 2) ^ n * (z ^ 2 / 4) ^ k := by
    rw [pow_add, pow_mul, mul_comm]
    congr 2
    ring
  rw [h]
  ring

lemma summable_besselITerm (n : ℕ) (z : ℝ) :
    Summable fun k : ℕ => (z / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * ((k + n).factorial : ℝ)) := by
  have hexp : Summable fun k : ℕ => |z / 2| ^ n * ((|z / 2| ^ 2) ^ k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial _).mul_left _
  refine hexp.of_norm_bounded fun k => ?_
  have hk1 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hk2 : (1 : ℝ) ≤ ((k + n).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hk1 (lt_of_lt_of_le zero_lt_one hk2))]
  rw [show 2 * k + n = n + 2 * k by omega, pow_add, pow_mul, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (abs_nonneg _) _)
  refine div_le_div_of_nonneg_left (pow_nonneg (sq_nonneg _) _) hk1 ?_
  nlinarith

/-- Link between the bootstrap kernel `kernelK w α t` (`w ≥ 1`) and `Bessel.besselI (w - 1)`. -/
lemma kernelK_eq_besselI {w : ℕ} (hw : 1 ≤ w) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    kernelK w α t =
      Real.sqrt (t / α) ^ (w - 1) * Bessel.besselI (w - 1) (4 * π * Real.sqrt (α * t)) := by
  unfold kernelK kernelKTerm
  rw [besselI_eq_tsum]
  have hw_eq : (2 * π * t) ^ (w - 1) =
      Real.sqrt (t / α) ^ (w - 1) * (4 * π * Real.sqrt (α * t) / 2) ^ (w - 1) := by
    rw [← mul_pow]
    congr 1
    have h1 : Real.sqrt (t / α) * (4 * π * Real.sqrt (α * t) / 2) =
        2 * π * (Real.sqrt (t / α) * Real.sqrt (α * t)) := by ring
    rw [h1, ← Real.sqrt_mul (div_pos ht hα).le]
    have hsimp : t / α * (α * t) = t ^ 2 := by field_simp
    rw [hsimp, Real.sqrt_sq ht.le]
  rw [hw_eq, mul_assoc, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  have hsq : (4 * π * Real.sqrt (α * t) / 2) ^ (2 * k) = (4 * π ^ 2 * α * t) ^ k := by
    rw [show 4 * π * Real.sqrt (α * t) / 2 = 2 * π * Real.sqrt (α * t) by ring, pow_mul,
      mul_pow, mul_pow, Real.sq_sqrt (mul_pos hα ht).le]
    ring_nf
  have hkw : k + w - 1 = k + (w - 1) := by omega
  rw [add_comm (2 * k) (w - 1), pow_add, ← hsq, hkw]
  ring

private lemma integral_cexp_int_mul_I_negPi_pi (k : ℤ) :
    ∫ θ in (-π)..π, Complex.exp ((k : ℂ) * Complex.I * θ) =
      if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero]
    simp [sub_neg_eq_add, two_mul]
  · have hkne : (k : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero
    let F : ℝ → ℂ := fun θ => Complex.exp ((k : ℂ) * Complex.I * θ) / ((k : ℂ) * Complex.I)
    have hderiv : ∀ θ ∈ uIcc (-π) π,
        HasDerivAt F (Complex.exp ((k : ℂ) * Complex.I * θ)) θ := fun θ _ => by
      have hd1 : HasDerivAt (fun x : ℝ => (k : ℂ) * Complex.I * (x : ℂ)) ((k : ℂ) * Complex.I) θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul ((k : ℂ) * Complex.I)
      have hd2 := hd1.cexp.div_const ((k : ℂ) * Complex.I)
      convert hd2 using 1
      rw [mul_div_cancel_right₀ _ hkne]
    have hint : IntervalIntegrable (fun θ => Complex.exp ((k : ℂ) * Complex.I * θ)) volume (-π) π :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hper : Complex.exp ((k : ℂ) * Complex.I * (π : ℂ)) =
        Complex.exp ((k : ℂ) * Complex.I * ((-π : ℝ) : ℂ)) := by
      have hdiff : (k : ℂ) * Complex.I * (π : ℂ) =
          (k : ℂ) * Complex.I * ((-π : ℝ) : ℂ) + k * (2 * π * Complex.I) := by
        push_cast; ring
      rw [hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp [F, hper]

private lemma integral_cos_pow_mul_cos_negPi_pi (m n : ℕ) :
    ∫ θ in (-π)..π, Real.cos θ ^ m * Real.cos (n * θ) =
      if n ≤ m ∧ (m - n) % 2 = 0 then
        2 * π * ((m.choose ((m - n) / 2) : ℝ) / (2 : ℝ) ^ m)
      else 0 := by
  let F : ℝ → ℂ := fun θ => (Real.cos θ : ℂ) ^ m * Complex.exp ((n : ℂ) * Complex.I * θ)
  have hre : ∀ θ : ℝ, Real.cos θ ^ m * Real.cos (n * θ) = Complex.reCLM (F θ) := fun θ => by
    change Real.cos θ ^ m * Real.cos (n * θ) = (F θ).re
    dsimp [F]
    rw [← Complex.ofReal_pow]
    have hexp_re : (Complex.exp ((n : ℂ) * Complex.I * (θ : ℂ))).re = Real.cos (n * θ) := by
      rw [show (n : ℂ) * Complex.I * (θ : ℂ) = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I_re]
    rw [Complex.re_ofReal_mul, hexp_re]
  simp_rw [hre]
  have hF_int : IntervalIntegrable F volume (-π) π :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [Complex.reCLM.intervalIntegral_comp_comm hF_int]
  have hF_exp : ∀ θ : ℝ, F θ = ((2 : ℂ) ^ m)⁻¹ *
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℂ) * Complex.exp (((2 * (j : ℤ) - (m : ℤ) + (n : ℤ) : ℤ) : ℂ) * Complex.I * θ) := by
    intro θ
    have hcos : (Real.cos θ : ℂ) =
        (Complex.exp (Complex.I * θ) + Complex.exp (-Complex.I * θ)) * (2 : ℂ)⁻¹ := by
      rw [Complex.ofReal_cos, Complex.cos, div_eq_mul_inv]
      ring_nf
    have hpow : (Real.cos θ : ℂ) ^ m = ((2 : ℂ) ^ m)⁻¹ *
        ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
          Complex.exp (((2 * (j : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I * θ) := by
      rw [hcos, mul_pow, inv_pow, mul_comm _ ((2 : ℂ) ^ m)⁻¹, add_pow]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hj_le : j ≤ m := by omega
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      calc Complex.exp (↑j * (Complex.I * ↑θ)) * Complex.exp (↑(m - j) * (-Complex.I * ↑θ)) * (m.choose j : ℂ)
          = (m.choose j : ℂ) * (Complex.exp (↑j * (Complex.I * ↑θ)) * Complex.exp (↑(m - j) * (-Complex.I * ↑θ))) := by
            ring
        _ = (m.choose j : ℂ) * Complex.exp (((2 * (j : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I * ↑θ) := by
            congr 1
            rw [← Complex.exp_add]
            congr 1
            have hcast : ((m - j : ℕ) : ℂ) = (m : ℂ) - (j : ℂ) := Nat.cast_sub hj_le
            rw [hcast]; push_cast; ring
    calc F θ = (Real.cos θ : ℂ) ^ m * Complex.exp ((n : ℂ) * Complex.I * θ) := rfl
      _ = ((2 : ℂ) ^ m)⁻¹ * (∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
          Complex.exp (((2 * (j : ℤ) - (m : ℤ) : ℤ) : ℂ) * Complex.I * θ)) *
            Complex.exp ((n : ℂ) * Complex.I * θ) := by rw [hpow]
      _ = ((2 : ℂ) ^ m)⁻¹ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
          Complex.exp (((2 * (j : ℤ) - (m : ℤ) + (n : ℤ) : ℤ) : ℂ) * Complex.I * θ) := by
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, ← Complex.exp_add]
        congr 2; push_cast; ring
  have hint_eq : ∫ θ in (-π)..π, F θ = ((2 : ℂ) ^ m)⁻¹ *
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
        (if 2 * (j : ℤ) - (m : ℤ) + (n : ℤ) = 0 then (2 * π : ℂ) else 0) := by
    simp_rw [hF_exp]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_cexp_int_mul_I_negPi_pi]
    · intro j _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hint_eq, Complex.reCLM_apply]
  by_cases hkn : n ≤ m ∧ (m - n) % 2 = 0
  · simp only [hkn, and_self, ↓reduceIte]
    have hk_eq : m = 2 * ((m - n) / 2) + n := by omega
    have hk_mem : (m - n) / 2 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have huniq : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
        (if 2 * (j : ℤ) - (m : ℤ) + (n : ℤ) = 0 then (2 * π : ℂ) else 0) =
        (m.choose ((m - n) / 2) : ℂ) * (2 * π : ℂ) := by
      rw [Finset.sum_eq_single ((m - n) / 2)]
      · have h0 : (2 * (((m - n) / 2 : ℕ) : ℤ) - (m : ℤ) + (n : ℤ)) = 0 := by omega
        simp only [h0, ↓reduceIte]
      · intro j _ hjk
        have hne : 2 * (j : ℤ) - (m : ℤ) + (n : ℤ) ≠ 0 := by omega
        simp only [hne, ↓reduceIte, mul_zero]
      · intro hmem; exact absurd hk_mem hmem
    rw [huniq]
    have hreal : ((2 : ℂ) ^ m)⁻¹ * ((m.choose ((m - n) / 2) : ℂ) * (2 * π : ℂ)) =
        ((2 * π * ((m.choose ((m - n) / 2) : ℝ) / (2 : ℝ) ^ m) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hreal, Complex.ofReal_re]
  · simp only [hkn, ↓reduceIte]
    have hzero : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) *
        (if 2 * (j : ℤ) - (m : ℤ) + (n : ℤ) = 0 then (2 * π : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : 2 * (j : ℤ) - (m : ℤ) + (n : ℤ) ≠ 0 := by intro heq; apply hkn; omega
      simp only [hne, ↓reduceIte, mul_zero]
    rw [hzero, mul_zero, Complex.zero_re]

/-- Integral representation `I_n(z) = (1 / π) ∫₀^π exp(z cos θ) cos(n θ) dθ` (`n ∈ ℕ`, `z ∈ ℝ`). -/
theorem besselI_eq_integral (n : ℕ) (z : ℝ) :
    Bessel.besselI n z = (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
  have hpi_le : -π ≤ π := by linarith [Real.pi_pos]
  have heven : ∫ θ in (-π)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) =
      2 * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (Continuous.intervalIntegrable (by fun_prop) (-π) 0)
      (Continuous.intervalIntegrable (by fun_prop) 0 π)]
    have hrefl : ∫ θ in (-π)..0, Real.exp (z * Real.cos θ) * Real.cos (n * θ) =
        ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
      have hsub := intervalIntegral.integral_comp_neg (a := -π) (b := 0)
        (fun θ => Real.exp (z * Real.cos θ) * Real.cos (n * θ))
      simp only [neg_zero, neg_neg] at hsub
      convert hsub using 1
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp [Real.cos_neg, mul_neg]
    rw [hrefl, two_mul]
  have hseries : ∀ θ : ℝ, Real.exp (z * Real.cos θ) * Real.cos (n * θ) =
      ∑' m : ℕ, (z ^ m / (m.factorial : ℝ)) * (Real.cos θ ^ m * Real.cos (n * θ)) := by
    intro θ
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [mul_pow, smul_eq_mul]; ring
  have htsum_int : ∫ θ in (-π)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) =
      ∑' m : ℕ, (z ^ m / (m.factorial : ℝ)) * ∫ θ in (-π)..π, Real.cos θ ^ m * Real.cos (n * θ) := by
    simp_rw [hseries, intervalIntegral.integral_of_le hpi_le]
    have hbound : Summable fun m : ℕ =>
        ∫ θ in Ioc (-π) π, ‖(z ^ m / (m.factorial : ℝ)) * (Real.cos θ ^ m * Real.cos (n * θ))‖ := by
      have hexp : Summable fun m : ℕ => (2 * π) * (|z| ^ m / (m.factorial : ℝ)) :=
        (Real.summable_pow_div_factorial |z|).mul_left _
      refine hexp.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) fun m => ?_
      have hle : ∀ θ ∈ Ioc (-π) π,
          ‖(z ^ m / (m.factorial : ℝ)) * (Real.cos θ ^ m * Real.cos (n * θ))‖ ≤
            |z| ^ m / (m.factorial : ℝ) := by
        intro θ _
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow,
          abs_of_pos (by positivity : (0 : ℝ) < (m.factorial : ℝ)), abs_pow]
        have hc1 : |Real.cos θ| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ)
        have hc2 : |Real.cos (n * θ)| ≤ 1 := Real.abs_cos_le_one _
        calc |z| ^ m / (m.factorial : ℝ) * (|Real.cos θ| ^ m * |Real.cos (n * θ)|)
            ≤ |z| ^ m / (m.factorial : ℝ) * (1 * 1) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul hc1 hc2 (abs_nonneg _) zero_le_one)
                (by positivity)
          _ = |z| ^ m / (m.factorial : ℝ) := by ring
      calc ∫ θ in Ioc (-π) π, ‖(z ^ m / (m.factorial : ℝ)) * (Real.cos θ ^ m * Real.cos (n * θ))‖
          ≤ ∫ _ in Ioc (-π) π, |z| ^ m / (m.factorial : ℝ) := by
            refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Ioc hle
            exact (by fun_prop : Continuous fun θ =>
              ‖(z ^ m / (m.factorial : ℝ)) * (Real.cos θ ^ m * Real.cos (n * θ))‖).integrableOn_Ioc
        _ = (2 * π) * (|z| ^ m / (m.factorial : ℝ)) := by
            rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hpi_le]
            ring
    rw [← integral_tsum_of_summable_integral_norm
      (fun m => Continuous.integrableOn_Ioc (by fun_prop)) hbound]
    refine tsum_congr fun m => ?_
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hpi_le]
  rw [htsum_int] at heven
  let term : ℕ → ℝ := fun m => (z ^ m / (m.factorial : ℝ)) *
    (if n ≤ m ∧ (m - n) % 2 = 0 then 2 * π * ((m.choose ((m - n) / 2) : ℝ) / (2 : ℝ) ^ m) else 0)
  have hf_sub : ∀ k : ℕ, term (2 * k + n) =
      (2 * π) * ((z / 2) ^ (2 * k + n) / ((k.factorial : ℝ) * ((k + n).factorial : ℝ))) := by
    intro k
    have hk_ex : n ≤ 2 * k + n ∧ (2 * k + n - n) % 2 = 0 := by omega
    dsimp [term]
    simp only [hk_ex, and_self, ↓reduceIte, show (2 * k + n - n) / 2 = k by omega]
    have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ 2 * k + n)
    rw [show 2 * k + n - k = k + n by omega] at hfac
    have hfacR : ((2 * k + n).choose k : ℝ) * (k.factorial : ℝ) * ((k + n).factorial : ℝ) =
        ((2 * k + n).factorial : ℝ) := by exact_mod_cast hfac
    have hc_ne : ((2 * k + n).choose k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : k ≤ 2 * k + n)).ne'
    have hm_ne : ((2 * k + n).factorial : ℝ) ≠ 0 := by positivity
    have hk_ne : (k.factorial : ℝ) ≠ 0 := by positivity
    have hkn_ne : ((k + n).factorial : ℝ) ≠ 0 := by positivity
    rw [div_pow]
    calc (z ^ (2 * k + n) / ((2 * k + n).factorial : ℝ)) *
          (2 * π * (((2 * k + n).choose k : ℝ) / (2 : ℝ) ^ (2 * k + n)))
        = 2 * π * ((z ^ (2 * k + n) / (2 : ℝ) ^ (2 * k + n)) *
            (((2 * k + n).choose k : ℝ) / ((2 * k + n).factorial : ℝ))) := by ring
      _ = 2 * π * ((z ^ (2 * k + n) / (2 : ℝ) ^ (2 * k + n)) /
            ((k.factorial : ℝ) * ((k + n).factorial : ℝ))) := by
          congr 2
          rw [← hfacR]
          field_simp
  have hhas : HasSum term (2 * π * Bessel.besselI n z) := by
    have hsub_has : HasSum (fun k => term (2 * k + n)) (2 * π * Bessel.besselI n z) := by
      simp_rw [hf_sub]
      rw [besselI_eq_tsum]
      exact (summable_besselITerm n z).hasSum.mul_left (2 * π)
    refine (Function.Injective.hasSum_iff (f := term) (g := fun k : ℕ => 2 * k + n)
      (fun a b h => by dsimp only at h; omega) ?_).mp hsub_has
    intro m hm
    dsimp [term]
    have hnex : ¬ (n ≤ m ∧ (m - n) % 2 = 0) := by
      intro h
      apply hm
      exact ⟨(m - n) / 2, by dsimp only; omega⟩
    simp only [hnex, ↓reduceIte, mul_zero]
  have hterms : ∑' m : ℕ, term m = 2 * π * Bessel.besselI n z := hhas.tsum_eq
  have hsum_eq : ∑' m : ℕ, (z ^ m / (m.factorial : ℝ)) *
      ∫ θ in (-π)..π, Real.cos θ ^ m * Real.cos (n * θ) = ∑' m : ℕ, term m := by
    refine tsum_congr fun m => ?_
    rw [integral_cos_pow_mul_cos_negPi_pi]
  rw [hsum_eq, hterms] at heven
  have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
  linarith [show (1 / π) * (2 * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ)) =
      (1 / π) * (2 * π * Bessel.besselI n z) from congrArg (fun x => (1 / π) * x) heven.symm,
    show (1 / π) * (2 * π * Bessel.besselI n z) = 2 * Bessel.besselI n z by field_simp,
    show (1 / π) * (2 * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ)) =
      2 * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ)) by ring]

private lemma one_sub_cos_eq (θ : ℝ) : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
  have h1 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
  rw [h1, Real.cos_two_mul]
  have h2 := Real.cos_sq_add_sin_sq (θ / 2)
  linarith

/-- Uniform order domination `I_n(z) ≤ I_0(z)` for all `n ∈ ℕ` and `z ∈ ℝ`. -/
lemma besselI_le_zero (n : ℕ) (z : ℝ) : Bessel.besselI n z ≤ Bessel.besselI 0 z := by
  rw [besselI_eq_integral n z, besselI_eq_integral 0 z]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono_on Real.pi_pos.le
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun θ _ => ?_
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)

/-- Uniform Gaussian-saddle upper bound `I_0(z) ≤ √(π / 8) * exp z / √z` for all `z > 0`. -/
theorem besselI_zero_le_exp_div_sqrt {z : ℝ} (hz : 0 < z) :
    Bessel.besselI 0 z ≤ Real.sqrt (π / 8) * Real.exp z / Real.sqrt z := by
  rw [besselI_eq_integral 0 z]
  have hpt : ∀ θ ∈ Ioc (0 : ℝ) π,
      Real.exp (z * Real.cos θ) * Real.cos ((0 : ℕ) * θ) ≤
        Real.exp z * Real.exp (-(2 * z / π ^ 2) * θ ^ 2) := by
    intro θ ⟨hθ0, hθpi⟩
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    have hsin : 2 / π * (θ / 2) ≤ Real.sin (θ / 2) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hsin_sq : (θ / π) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := by
      have h1 : θ / π ≤ Real.sin (θ / 2) := by
        calc θ / π = 2 / π * (θ / 2) := by ring
          _ ≤ Real.sin (θ / 2) := hsin
      exact pow_le_pow_left₀ (by positivity) h1 2
    have hcos_le : Real.cos θ ≤ 1 - 2 / π ^ 2 * θ ^ 2 := by
      have hsub := one_sub_cos_eq θ
      have h2 : 2 * (θ / π) ^ 2 ≤ 1 - Real.cos θ := by
        linarith [mul_le_mul_of_nonneg_left hsin_sq (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [show 2 * (θ / π) ^ 2 = 2 / π ^ 2 * θ ^ 2 by ring]
    calc Real.exp (z * Real.cos θ)
        ≤ Real.exp (z * (1 - 2 / π ^ 2 * θ ^ 2)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcos_le hz.le)
      _ = Real.exp z * Real.exp (-(2 * z / π ^ 2) * θ ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
  have hint_ioc : IntegrableOn (fun θ => Real.exp z * Real.exp (-(2 * z / π ^ 2) * θ ^ 2))
      (Ioc 0 π) :=
    Continuous.integrableOn_Ioc (by fun_prop)
  have hint_ioi : IntegrableOn (fun θ => Real.exp (-(2 * z / π ^ 2) * θ ^ 2)) (Ioi 0) :=
    (integrableOn_Ioi_exp_neg_mul_sq_iff).mpr (by positivity)
  have h1 : ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos ((0 : ℕ) * θ) ≤
      Real.exp z * ∫ θ in Ioi (0 : ℝ), Real.exp (-(2 * z / π ^ 2) * θ ^ 2) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    calc ∫ θ in Ioc 0 π, Real.exp (z * Real.cos θ) * Real.cos ((0 : ℕ) * θ)
        ≤ ∫ θ in Ioc 0 π, Real.exp z * Real.exp (-(2 * z / π ^ 2) * θ ^ 2) :=
          setIntegral_mono_on (Continuous.integrableOn_Ioc (by fun_prop)) hint_ioc
            measurableSet_Ioc hpt
      _ = Real.exp z * ∫ θ in Ioc 0 π, Real.exp (-(2 * z / π ^ 2) * θ ^ 2) :=
          integral_const_mul _ _
      _ ≤ Real.exp z * ∫ θ in Ioi 0, Real.exp (-(2 * z / π ^ 2) * θ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact setIntegral_mono_set hint_ioi (Eventually.of_forall fun _ => (Real.exp_pos _).le)
            Ioc_subset_Ioi_self.eventuallyLE
  rw [integral_gaussian_Ioi] at h1
  have hcalc : (1 / π) * (Real.exp z * (Real.sqrt (π / (2 * z / π ^ 2)) / 2)) =
      Real.sqrt (π / 8) * Real.exp z / Real.sqrt z := by
    have hpi : 0 < π := Real.pi_pos
    have hsq : π / (2 * z / π ^ 2) = π ^ 2 * (π / 2 / z) := by field_simp
    rw [hsq, Real.sqrt_mul (sq_nonneg π), Real.sqrt_sq hpi.le]
    have h8 : Real.sqrt (π / 8) = Real.sqrt (π / 2) / 2 := by
      rw [show π / 8 = (π / 2) / 2 ^ 2 by ring, Real.sqrt_div (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [h8, Real.sqrt_div (by positivity)]
    field_simp
  calc (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos ((0 : ℕ) * θ)
      ≤ (1 / π) * (Real.exp z * (Real.sqrt (π / (2 * z / π ^ 2)) / 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.sqrt (π / 8) * Real.exp z / Real.sqrt z := hcalc

/-- Asymptotic lower bound `besselI n z ≥ c * exp z / √z` for sufficiently large `z`. -/
theorem besselI_ge_exp_div_sqrt (n : ℕ) :
    ∃ c z₀ : ℝ, 0 < c ∧ 1 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z → c * Real.exp z / Real.sqrt z ≤ Bessel.besselI n z := by
  let θ₀ : ℝ := π / (3 * ((n : ℝ) + 1))
  have hθ₀_pos : 0 < θ₀ := by positivity
  have hθ₀_le : θ₀ ≤ π / 3 := by
    dsimp [θ₀]
    refine div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hθ₀_lt_pi : θ₀ < π := lt_of_le_of_lt hθ₀_le (by linarith [Real.pi_pos])
  have hcos_lt : Real.cos θ₀ < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ₀_pos.le, hθ₀_lt_pi.le⟩ hθ₀_pos
  let δ : ℝ := 1 - Real.cos θ₀
  have hδ_pos : 0 < δ := sub_pos.mpr hcos_lt
  let cmain : ℝ := Real.exp (-1 / 2) / 2
  have hcmain_pos : 0 < cmain := by positivity
  let z₀ : ℝ := max 1 (max (1 / θ₀ ^ 2) ((4 * π / (δ * Real.exp (-1 / 2))) ^ 2))
  refine ⟨cmain / (2 * π), z₀, by positivity, le_max_left _ _, fun z hz => ?_⟩
  have hz_ge1 : 1 ≤ z := (le_max_left _ _).trans hz
  have hz_pos : 0 < z := by linarith
  have hz_θ₀ : 1 / θ₀ ^ 2 ≤ z := ((le_max_left _ _).trans (le_max_right _ _)).trans hz
  have hz_tail : (4 * π / (δ * Real.exp (-1 / 2))) ^ 2 ≤ z :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hz
  let a : ℝ := 1 / Real.sqrt z
  have ha_pos : 0 < a := by positivity
  have ha_le_θ₀ : a ≤ θ₀ := by
    dsimp [a]
    rw [← Real.sqrt_one, ← Real.sqrt_div zero_le_one, Real.sqrt_le_iff]
    refine ⟨hθ₀_pos.le, ?_⟩
    rw [div_le_iff₀ hz_pos]
    calc (1 : ℝ) = (1 / θ₀ ^ 2) * θ₀ ^ 2 := by field_simp
      _ ≤ z * θ₀ ^ 2 := mul_le_mul_of_nonneg_right hz_θ₀ (sq_nonneg _)
      _ = θ₀ ^ 2 * z := by ring
  have ha_le_pi : a ≤ π := ha_le_θ₀.trans hθ₀_lt_pi.le
  rw [besselI_eq_integral n z]
  have hint1 : IntervalIntegrable (fun θ => Real.exp (z * Real.cos θ) * Real.cos (n * θ)) volume 0 a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint2 : IntervalIntegrable (fun θ => Real.exp (z * Real.cos θ) * Real.cos (n * θ)) volume a θ₀ :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hint3 : IntervalIntegrable (fun θ => Real.exp (z * Real.cos θ) * Real.cos (n * θ)) volume θ₀ π :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hsplit : ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) =
      (∫ θ in (0 : ℝ)..a, Real.exp (z * Real.cos θ) * Real.cos (n * θ)) +
      (∫ θ in a..θ₀, Real.exp (z * Real.cos θ) * Real.cos (n * θ)) +
      (∫ θ in θ₀..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ)) := by
    have h12 := (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    have h123 := (intervalIntegral.integral_add_adjacent_intervals (hint1.trans hint2) hint3).symm
    rw [h123, h12]
  have hcos_n_pos : ∀ θ ∈ Icc 0 θ₀, (1 / 2 : ℝ) ≤ Real.cos (n * θ) := by
    intro θ ⟨h0, h1⟩
    have hn1 : 0 ≤ (n : ℝ) * θ := by positivity
    have hn2 : (n : ℝ) * θ ≤ π / 3 := by
      calc (n : ℝ) * θ ≤ (n : ℝ) * θ₀ := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = (n : ℝ) * (π / (3 * ((n : ℝ) + 1))) := rfl
        _ ≤ ((n : ℝ) + 1) * (π / (3 * ((n : ℝ) + 1))) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = π / 3 := by
          have hn_ne : (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp
    rw [← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos.antitoneOn ⟨hn1, hn2.trans (by linarith [Real.pi_pos])⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩ hn2
  have hmain_lb : cmain * Real.exp z / Real.sqrt z ≤
      ∫ θ in (0 : ℝ)..a, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
    have hconst_int : ∫ _ in (0 : ℝ)..a, cmain * Real.exp z = cmain * Real.exp z / Real.sqrt z := by
      simp [a, sub_zero, div_eq_mul_inv, mul_comm, mul_assoc]
    rw [← hconst_int]
    refine intervalIntegral.integral_mono_on ha_pos.le (Continuous.intervalIntegrable (by fun_prop) _ _)
      hint1 fun θ ⟨h0, hθa⟩ => ?_
    have hθ_θ₀ : θ ≤ θ₀ := hθa.trans ha_le_θ₀
    have hsin : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le (by linarith)
    have hcos_lb : 1 - θ ^ 2 / 2 ≤ Real.cos θ := by
      have h1 : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := one_sub_cos_eq θ
      have hs_nn : 0 ≤ Real.sin (θ / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ_θ₀.trans hθ₀_lt_pi.le])
      have h2 : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := pow_le_pow_left₀ hs_nn hsin 2
      linarith
    have hz_θ_sq : z * θ ^ 2 / 2 ≤ 1 / 2 := by
      have hsq : θ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ h0 hθa 2
      have ha_sq : a ^ 2 = 1 / z := by dsimp [a]; rw [div_pow, one_pow, Real.sq_sqrt hz_pos.le]
      rw [ha_sq] at hsq
      have hz_mul : z * θ ^ 2 ≤ 1 := by
        calc z * θ ^ 2 ≤ z * (1 / z) := mul_le_mul_of_nonneg_left hsq hz_pos.le
          _ = 1 := mul_one_div_cancel hz_pos.ne'
      linarith
    have hexp_lb : Real.exp (-1 / 2) * Real.exp z ≤ Real.exp (z * Real.cos θ) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hcn := hcos_n_pos θ ⟨h0, hθ_θ₀⟩
    calc cmain * Real.exp z = (1 / 2) * (Real.exp (-1 / 2) * Real.exp z) := by
          dsimp [cmain]; ring
      _ ≤ Real.cos (n * θ) * Real.exp (z * Real.cos θ) :=
          mul_le_mul hcn hexp_lb (by positivity) (by linarith)
      _ = Real.exp (z * Real.cos θ) * Real.cos (n * θ) := mul_comm _ _
  have hmid_nn : 0 ≤ ∫ θ in a..θ₀, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
    refine intervalIntegral.integral_nonneg ha_le_θ₀ fun θ ⟨h1, h2⟩ => ?_
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hcos_n_pos θ ⟨ha_pos.le.trans h1, h2⟩])
  have htail_lb : -(cmain * Real.exp z / (2 * Real.sqrt z)) ≤
      ∫ θ in θ₀..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
    have hpt : ∀ θ ∈ Icc θ₀ π, -Real.exp (z * Real.cos θ₀) ≤
        Real.exp (z * Real.cos θ) * Real.cos (n * θ) := fun θ ⟨h1, h2⟩ => by
      have hcos_θ : Real.cos θ ≤ Real.cos θ₀ :=
        Real.strictAntiOn_cos.antitoneOn ⟨hθ₀_pos.le, hθ₀_lt_pi.le⟩ ⟨hθ₀_pos.le.trans h1, h2⟩ h1
      have hexp_le : Real.exp (z * Real.cos θ) ≤ Real.exp (z * Real.cos θ₀) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcos_θ hz_pos.le)
      have hneg1 : -1 ≤ Real.cos (n * θ) := Real.neg_one_le_cos _
      calc -Real.exp (z * Real.cos θ₀) ≤ -Real.exp (z * Real.cos θ) := neg_le_neg hexp_le
        _ = Real.exp (z * Real.cos θ) * (-1) := by ring
        _ ≤ Real.exp (z * Real.cos θ) * Real.cos (n * θ) :=
            mul_le_mul_of_nonneg_left hneg1 (Real.exp_pos _).le
    have hint_neg : ∫ _ in θ₀..π, -Real.exp (z * Real.cos θ₀) ≤
        ∫ θ in θ₀..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) :=
      intervalIntegral.integral_mono_on hθ₀_lt_pi.le
        (Continuous.intervalIntegrable (by fun_prop) _ _) hint3 hpt
    have hconst_val : ∫ _ in θ₀..π, -Real.exp (z * Real.cos θ₀) =
        -(π - θ₀) * Real.exp (z * Real.cos θ₀) := by
      simp [sub_eq_add_neg]; ring
    rw [hconst_val] at hint_neg
    have htail_bound : (π - θ₀) * Real.exp (z * Real.cos θ₀) ≤
        cmain * Real.exp z / (2 * Real.sqrt z) := by
      have hexp_δ : δ * z ≤ Real.exp (δ * z) := by
        linarith [Real.add_one_le_exp (δ * z)]
      have hexp_neg_δ : Real.exp (-(δ * z)) ≤ 1 / (δ * z) := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by positivity) hexp_δ
      have hz_rt : 4 * π / (δ * Real.exp (-1 / 2)) ≤ Real.sqrt z := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * π / (δ * Real.exp (-1 / 2)))]
        exact Real.sqrt_le_sqrt hz_tail
      have hratio : π / (δ * z) ≤ cmain / (2 * Real.sqrt z) := by
        have h1 : 4 * π ≤ δ * Real.exp (-1 / 2) * Real.sqrt z := by
          have := mul_le_mul_of_nonneg_left hz_rt (by positivity : 0 ≤ δ * Real.exp (-1 / 2))
          rwa [mul_div_cancel₀ _ (by positivity)] at this
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hsq_z : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz_pos.le
        dsimp [cmain]
        calc π * (2 * Real.sqrt z) = (4 * π) * (Real.sqrt z / 2) := by ring
          _ ≤ (δ * Real.exp (-1 / 2) * Real.sqrt z) * (Real.sqrt z / 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = Real.exp (-1 / 2) / 2 * (δ * (Real.sqrt z * Real.sqrt z)) := by ring
          _ = Real.exp (-1 / 2) / 2 * (δ * z) := by rw [hsq_z]
      calc (π - θ₀) * Real.exp (z * Real.cos θ₀)
          ≤ π * Real.exp (z * Real.cos θ₀) := by
            refine mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = π * Real.exp (-(δ * z)) * Real.exp z := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp [δ]; ring
        _ ≤ π * (1 / (δ * z)) * Real.exp z := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_neg_δ
              Real.pi_pos.le) (Real.exp_pos _).le
        _ = (π / (δ * z)) * Real.exp z := by ring
        _ ≤ (cmain / (2 * Real.sqrt z)) * Real.exp z :=
            mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
        _ = cmain * Real.exp z / (2 * Real.sqrt z) := by ring
    linarith
  have hsum_lb : cmain * Real.exp z / (2 * Real.sqrt z) ≤
      ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) := by
    rw [hsplit]
    calc cmain * Real.exp z / (2 * Real.sqrt z)
        = cmain * Real.exp z / Real.sqrt z + 0 + (-(cmain * Real.exp z / (2 * Real.sqrt z))) := by
          ring
      _ ≤ _ := add_le_add (add_le_add hmain_lb hmid_nn) htail_lb
  calc cmain / (2 * π) * Real.exp z / Real.sqrt z
      = (1 / π) * (cmain * Real.exp z / (2 * Real.sqrt z)) := by ring
    _ ≤ (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos (n * θ) :=
        mul_le_mul_of_nonneg_left hsum_lb (by positivity)

/-- Smooth radial part of `kernelK w α t` with `t^{w - 1}` factored out:
`kernelKReduced w α t = (2π)^{w - 1} ∑_{k ≥ 0} kernelKTerm w α t k`. -/
noncomputable def kernelKReduced (w : ℕ) (α t : ℝ) : ℝ :=
  (2 * π) ^ (w - 1) * ∑' k : ℕ, kernelKTerm w α t k

lemma kernelK_eq_pow_mul_reduced (w : ℕ) (α t : ℝ) :
    kernelK w α t = t ^ (w - 1) * kernelKReduced w α t := by
  unfold kernelK kernelKReduced
  rw [mul_pow]
  ring

lemma continuous_kernelKReduced (w : ℕ) (α : ℝ) : Continuous (kernelKReduced w α) := by
  unfold kernelKReduced
  refine continuous_const.mul ?_
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  let R : ℝ := |t₀| + 1
  let M : ℕ → ℝ := fun k => (4 * π ^ 2 * |α| * R) ^ k / (k.factorial : ℝ)
  have hM : Summable M := Real.summable_pow_div_factorial _
  have hcont_unif : ContinuousOn (fun t => ∑' k : ℕ, kernelKTerm w α t k) (Icc (-R) R) := by
    refine continuousOn_tsum (fun k => (by unfold kernelKTerm; fun_prop :
        Continuous (fun t => kernelKTerm w α t k)).continuousOn) hM ?_
    intro k t ht
    unfold kernelKTerm
    have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hfac2_pos : (0 : ℝ) < ((k + w - 1).factorial : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (mul_pos hfac_pos hfac2_pos)]
    have hfac : (1 : ℝ) ≤ ((k + w - 1).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    have h1 : |4 * π ^ 2 * α * t| ≤ 4 * π ^ 2 * |α| * R := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < (4 : ℝ)),
        abs_of_pos (sq_pos_of_pos Real.pi_pos)]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by positivity)
    calc |4 * π ^ 2 * α * t| ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ))
        ≤ (4 * π ^ 2 * |α| * R) ^ k / ((k.factorial : ℝ) * ((k + w - 1).factorial : ℝ)) := by
          gcongr
      _ ≤ (4 * π ^ 2 * |α| * R) ^ k / (k.factorial : ℝ) := by
          refine div_le_div_of_nonneg_left (pow_nonneg (by positivity) k) hfac_pos ?_
          nlinarith
  have hmem : t₀ ∈ Ioo (-R) R :=
    ⟨by dsimp [R]; linarith [neg_abs_le t₀], by dsimp [R]; linarith [le_abs_self t₀]⟩
  exact hcont_unif.continuousAt (mem_of_superset (Ioo_mem_nhds hmem.1 hmem.2) Ioo_subset_Icc_self)

/-- Reduced Cardy density `V(t) / t^{w - 1}` extended smoothly to `t ∈ ℝ`. -/
noncomputable def FixedWeightProblem.cardyVReduced (prob : FixedWeightProblem)
    (a t : ℝ) : ℝ :=
  ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * kernelKReduced prob.w (a - prob.shiftSum s) t

lemma FixedWeightProblem.cardyV_eq_pow_mul_reduced (prob : FixedWeightProblem) (a t : ℝ) :
    prob.cardyV a t = t ^ (prob.w - 1) * prob.cardyVReduced a t := by
  unfold FixedWeightProblem.cardyV FixedWeightProblem.cardyVReduced
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [kernelK_eq_pow_mul_reduced]
  ring

lemma continuous_cardyVReduced (prob : FixedWeightProblem) (a : ℝ) :
    Continuous (prob.cardyVReduced a) := by
  unfold FixedWeightProblem.cardyVReduced
  refine continuous_finsetSum _ fun s _ =>
    continuous_const.mul (continuous_kernelKReduced prob.w _)

/-- Cartesian Cardy density `ϱ(t)` (as a function of `t = ‖x‖² / 2`) satisfying
`∫ x : ℝ^{2w}, h(‖x‖²/2) * ϱ(‖x‖²/2) dx = 2π ∫₀^∞ h(t) V(t) dt`. -/
noncomputable def FixedWeightProblem.rhoDensity (prob : FixedWeightProblem)
    (a t : ℝ) : ℝ :=
  ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π * prob.cardyVReduced a t)

lemma continuous_rhoDensity (prob : FixedWeightProblem) (a : ℝ) :
    Continuous (prob.rhoDensity a) := by
  unfold FixedWeightProblem.rhoDensity
  exact continuous_const.mul (continuous_const.mul (continuous_cardyVReduced prob a))

lemma FixedWeightProblem.rhoDensity_nonneg (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ prob.rhoDensity a t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · have htend : Tendsto (prob.rhoDensity a) (𝓝[>] 0) (𝓝 (prob.rhoDensity a 0)) :=
      (continuous_rhoDensity prob a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hup : (0 : ℝ) < u := hu
    have hV : 0 ≤ prob.cardyV a u := prob.cardyV_nonneg ha hup.le
    rw [prob.cardyV_eq_pow_mul_reduced] at hV
    have hred : 0 ≤ prob.cardyVReduced a u :=
      nonneg_of_mul_nonneg_right hV (pow_pos hup _)
    unfold FixedWeightProblem.rhoDensity
    positivity
  · have hV : 0 ≤ prob.cardyV a t := prob.cardyV_nonneg ha ht
    rw [prob.cardyV_eq_pow_mul_reduced] at hV
    have hred : 0 ≤ prob.cardyVReduced a t :=
      nonneg_of_mul_nonneg_right hV (pow_pos ht_pos _)
    unfold FixedWeightProblem.rhoDensity
    positivity

lemma FixedWeightProblem.integral_rhoDensity (prob : FixedWeightProblem) (a : ℝ)
    (h : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin (2 * prob.w)),
        h (‖x‖ ^ 2 / 2) * prob.rhoDensity a (‖x‖ ^ 2 / 2) =
      ∫ t in Ioi 0, h t * prob.cardyDensity a t := by
  have h1 := integral_radialLiftReal prob.hw (fun t => h t * prob.rhoDensity a t)
  rw [h1]
  have hfac_ne : ((prob.w - 1).factorial : ℝ) ≠ 0 := by positivity
  have hpi_ne : (2 * π) ^ prob.w ≠ 0 := by positivity
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht_pos : 0 < t := Set.mem_Ioi.mp ht
  unfold FixedWeightProblem.rhoDensity FixedWeightProblem.cardyDensity
  rw [prob.cardyV_eq_pow_mul_reduced]
  field_simp

/-- Polynomial-exponential weight function in the `t = ‖x‖² / 2` variable:
`cardyWeight b d t = (1 + 2t)^b exp(d √(2t))`, so `cardyWeight b d (‖x‖² / 2) = (1 + ‖x‖²)^b exp(d ‖x‖)`. -/
noncomputable def cardyWeight (b d t : ℝ) : ℝ :=
  (1 + 2 * t) ^ b * Real.exp (d * Real.sqrt (2 * t))

lemma cardyWeight_pos (b d : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 < cardyWeight b d t := by
  unfold cardyWeight
  have h1 : 0 < 1 + 2 * t := by linarith
  exact mul_pos (Real.rpow_pos_of_pos h1 b) (Real.exp_pos _)

private lemma rpow_bessel_prefactor {w : ℕ} (hw : 1 ≤ w) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Real.sqrt (t / α) ^ (w - 1) / Real.sqrt (4 * π * Real.sqrt (α * t)) =
      (α ^ (-((w - 1 : ℝ) / 2 + 1 / 4)) / Real.sqrt (4 * π)) *
        t ^ ((w - 1 : ℝ) + (-((w - 1 : ℝ) / 2 + 1 / 4))) := by
  have hat_pos : 0 < α * t := mul_pos hα ht
  have hw_cast : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by
    rw [Nat.cast_sub hw, Nat.cast_one]
  have hnum : Real.sqrt (t / α) ^ (w - 1) =
      t ^ (((w : ℝ) - 1) / 2) / α ^ (((w : ℝ) - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ (w - 1), ← Real.rpow_mul (div_pos ht hα).le,
      hw_cast, one_div_mul_eq_div, Real.div_rpow ht.le hα.le]
  have hden : Real.sqrt (4 * π * Real.sqrt (α * t)) =
      Real.sqrt (4 * π) * (α ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ)) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π),
      Real.sqrt_eq_rpow (Real.sqrt (α * t)), Real.sqrt_eq_rpow (α * t),
      ← Real.rpow_mul hat_pos.le, Real.mul_rpow hα.le ht.le]
    norm_num
  rw [hnum, hden, div_div, div_eq_mul_inv]
  simp only [mul_inv, ← Real.rpow_neg hα.le, ← Real.rpow_neg ht.le]
  have hα_mul : α ^ (-(((w : ℝ) - 1) / 2)) * α ^ (-(1 / 4 : ℝ)) =
      α ^ (-((w - 1 : ℝ) / 2 + 1 / 4)) := by
    rw [← Real.rpow_add hα]; congr 1; ring
  have ht_mul : t ^ (((w : ℝ) - 1) / 2) * t ^ (-(1 / 4 : ℝ)) =
      t ^ ((w - 1 : ℝ) + (-((w - 1 : ℝ) / 2 + 1 / 4))) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  calc t ^ (((w : ℝ) - 1) / 2) *
        (α ^ (-(((w : ℝ) - 1) / 2)) * ((Real.sqrt (4 * π))⁻¹ * (α ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ)))))
      = (Real.sqrt (4 * π))⁻¹ * (α ^ (-(((w : ℝ) - 1) / 2)) * α ^ (-(1 / 4 : ℝ))) *
          (t ^ (((w : ℝ) - 1) / 2) * t ^ (-(1 / 4 : ℝ))) := by ring
    _ = (Real.sqrt (4 * π))⁻¹ * α ^ (-((w - 1 : ℝ) / 2 + 1 / 4)) *
          t ^ ((w - 1 : ℝ) + (-((w - 1 : ℝ) / 2 + 1 / 4))) := by rw [hα_mul, ht_mul]
    _ = (α ^ (-((w - 1 : ℝ) / 2 + 1 / 4)) / Real.sqrt (4 * π)) *
          t ^ ((w - 1 : ℝ) + (-((w - 1 : ℝ) / 2 + 1 / 4))) := by ring

/-- Upper bound `rhoDensity prob a t ≤ C * (1 + 2t)^{-(w-1)/2 - 1/4} * exp(4π √(a t))` for `t ≥ 0`. -/
theorem FixedWeightProblem.rhoDensity_le_cardyWeight (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      prob.rhoDensity a t ≤
        C * cardyWeight (-((prob.w - 1 : ℝ) / 2 + 1 / 4)) (2 * Real.sqrt 2 * π * Real.sqrt a) t := by
  let b : ℝ := -((prob.w - 1 : ℝ) / 2 + 1 / 4)
  let d : ℝ := 2 * Real.sqrt 2 * π * Real.sqrt a
  have hw1 : (1 : ℝ) ≤ (prob.w : ℝ) := by exact_mod_cast prob.hw
  have hb_neg : b ≤ 0 := by dsimp [b]; linarith
  have hd_eq : ∀ t : ℝ, 0 ≤ t → d * Real.sqrt (2 * t) = 4 * π * Real.sqrt (a * t) := fun t _ => by
    dsimp [d]
    rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul ha_pos.le]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
    calc (2 * Real.sqrt 2 * π * Real.sqrt a) * (Real.sqrt 2 * Real.sqrt t)
        = 2 * (Real.sqrt 2 * Real.sqrt 2) * π * (Real.sqrt a * Real.sqrt t) := by ring
      _ = 4 * π * (Real.sqrt a * Real.sqrt t) := by rw [hsq2]; ring
  have hcomp : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨M₀, hM₀⟩ := hcomp.exists_bound_of_continuousOn
    (continuous_rhoDensity prob a).continuousOn
  let M₀' : ℝ := max M₀ 1
  have hw01 : ∀ t ∈ Icc (0 : ℝ) 1,
      (3 : ℝ) ^ b ≤ cardyWeight b d t := fun t ⟨ht0, ht1⟩ => by
    unfold cardyWeight
    have h12t : 1 + 2 * t ≤ 3 := by linarith
    have h1_pos : 0 < 1 + 2 * t := by linarith
    have hrp : (3 : ℝ) ^ b ≤ (1 + 2 * t) ^ b :=
      Real.rpow_le_rpow_of_nonpos h1_pos h12t hb_neg
    have hexp : 1 ≤ Real.exp (d * Real.sqrt (2 * t)) :=
      Real.one_le_exp (by positivity : 0 ≤ d * Real.sqrt (2 * t))
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) b]
  let c₀ : ℝ := ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π) * (2 : ℝ) ^ prob.m
  have hc₀_pos : 0 < c₀ := by positivity
  let C_hi : ℝ := c₀ * a ^ b * (Real.sqrt (π / 8) / Real.sqrt (4 * π)) * (3 : ℝ) ^ (-b)
  have hC_hi_pos : 0 < C_hi := by positivity
  let C : ℝ := max (M₀' / (3 : ℝ) ^ b) C_hi
  refine ⟨C, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun t ht => ?_⟩
  rcases le_or_gt t 1 with ht1 | ht1
  · have hrho_le : prob.rhoDensity a t ≤ M₀' :=
      (le_abs_self _).trans ((hM₀ t ⟨ht, ht1⟩).trans (le_max_left _ _))
    have h3b_pos : 0 < (3 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) b
    calc prob.rhoDensity a t ≤ M₀' := hrho_le
      _ = (M₀' / (3 : ℝ) ^ b) * (3 : ℝ) ^ b := by field_simp
      _ ≤ C * (3 : ℝ) ^ b := mul_le_mul_of_nonneg_right (le_max_left _ _) h3b_pos.le
      _ ≤ C * cardyWeight b d t := mul_le_mul_of_nonneg_left (hw01 t ⟨ht, ht1⟩)
          (le_trans (by positivity) (le_max_left _ _))
  · have ht_pos : 0 < t := by linarith
    have hV_le := prob.cardyV_le_two_pow_kernelK ha ht
    rw [prob.cardyV_eq_pow_mul_reduced, kernelK_eq_besselI prob.hw ha_pos ht_pos] at hV_le
    have ht_pow_pos : 0 < t ^ (prob.w - 1) := pow_pos ht_pos _
    have hred_le : prob.cardyVReduced a t ≤
        (2 : ℝ) ^ prob.m * (Real.sqrt (t / a) ^ (prob.w - 1) *
          Bessel.besselI (prob.w - 1) (4 * π * Real.sqrt (a * t))) / t ^ (prob.w - 1) := by
      rw [le_div_iff₀ ht_pow_pos, mul_comm (prob.cardyVReduced a t)]
      exact hV_le
    have hbes := (besselI_le_zero (prob.w - 1) (4 * π * Real.sqrt (a * t))).trans
      (besselI_zero_le_exp_div_sqrt (by positivity : 0 < 4 * π * Real.sqrt (a * t)))
    have hpref := rpow_bessel_prefactor prob.hw ha_pos ht_pos
    have hpow_div : t ^ ((prob.w - 1 : ℝ) + b) / t ^ (prob.w - 1) = t ^ b := by
      rw [← Real.rpow_natCast t (prob.w - 1), Nat.cast_sub prob.hw, Nat.cast_one,
        Real.rpow_add ht_pos, mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos ht_pos _).ne']
    have h12t_le : 1 + 2 * t ≤ 3 * t := by linarith
    have h3t_pow : t ^ b ≤ (3 : ℝ) ^ (-b) * (1 + 2 * t) ^ b := by
      have hrp : (3 * t) ^ b ≤ (1 + 2 * t) ^ b :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h12t_le hb_neg
      rw [Real.mul_rpow (by norm_num) ht_pos.le] at hrp
      calc t ^ b = (3 : ℝ) ^ (-b) * ((3 : ℝ) ^ b * t ^ b) := by
            rw [← mul_assoc, ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ (3 : ℝ) ^ (-b) * (1 + 2 * t) ^ b :=
            mul_le_mul_of_nonneg_left hrp (Real.rpow_pos_of_pos (by norm_num) _).le
    have hrho_eq : prob.rhoDensity a t =
        ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π) * prob.cardyVReduced a t := by
      unfold FixedWeightProblem.rhoDensity; ring
    have hstep : prob.rhoDensity a t ≤
        C_hi * ((1 + 2 * t) ^ b * Real.exp (4 * π * Real.sqrt (a * t))) := by
      calc prob.rhoDensity a t
          ≤ ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π) *
              ((2 : ℝ) ^ prob.m * (Real.sqrt (t / a) ^ (prob.w - 1) *
                Bessel.besselI (prob.w - 1) (4 * π * Real.sqrt (a * t))) / t ^ (prob.w - 1)) := by
            rw [hrho_eq]
            exact mul_le_mul_of_nonneg_left hred_le (by positivity)
        _ ≤ ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π) *
              ((2 : ℝ) ^ prob.m * (Real.sqrt (t / a) ^ (prob.w - 1) *
                (Real.sqrt (π / 8) * Real.exp (4 * π * Real.sqrt (a * t)) /
                  Real.sqrt (4 * π * Real.sqrt (a * t)))) / t ^ (prob.w - 1)) := by
            refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbes
                (pow_nonneg (Real.sqrt_nonneg _) _)) (by positivity)) ht_pow_pos.le) (by positivity)
        _ = c₀ * Real.sqrt (π / 8) *
              ((Real.sqrt (t / a) ^ (prob.w - 1) / Real.sqrt (4 * π * Real.sqrt (a * t))) /
                t ^ (prob.w - 1)) * Real.exp (4 * π * Real.sqrt (a * t)) := by
            dsimp [c₀]; ring
        _ = c₀ * Real.sqrt (π / 8) * (a ^ b / Real.sqrt (4 * π)) *
              t ^ b * Real.exp (4 * π * Real.sqrt (a * t)) := by
            rw [hpref, show -((prob.w - 1 : ℝ) / 2 + 1 / 4) = b from rfl]
            rw [show a ^ b / Real.sqrt (4 * π) * t ^ (↑prob.w - 1 + b) / t ^ (prob.w - 1) =
              a ^ b / Real.sqrt (4 * π) * (t ^ (↑prob.w - 1 + b) / t ^ (prob.w - 1)) by ring, hpow_div]
            ring
        _ ≤ c₀ * Real.sqrt (π / 8) * (a ^ b / Real.sqrt (4 * π)) *
              ((3 : ℝ) ^ (-b) * (1 + 2 * t) ^ b) * Real.exp (4 * π * Real.sqrt (a * t)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3t_pow (by positivity))
              (Real.exp_pos _).le
        _ = C_hi * ((1 + 2 * t) ^ b * Real.exp (4 * π * Real.sqrt (a * t))) := by
            dsimp [C_hi]; ring
    calc prob.rhoDensity a t
        ≤ C_hi * ((1 + 2 * t) ^ b * Real.exp (4 * π * Real.sqrt (a * t))) := hstep
      _ = C_hi * cardyWeight b d t := by unfold cardyWeight; rw [hd_eq t ht]
      _ ≤ C * cardyWeight b d t :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (cardyWeight_pos b d ht).le

/-- Asymptotic lower bound `c * cardyWeight(-((w-1)/2 + 1/4), 2√2 π √a, t) ≤ rhoDensity prob a t`
for all sufficiently large `t ≥ T₀` (`a ≥ ∑ μ_l`, `a > 0`). -/
theorem FixedWeightProblem.rhoDensity_ge_cardyWeight_large (prob : FixedWeightProblem)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      c * cardyWeight (-((prob.w - 1 : ℝ) / 2 + 1 / 4)) (2 * Real.sqrt 2 * π * Real.sqrt a) t ≤
        prob.rhoDensity a t := by
  let b : ℝ := -((prob.w - 1 : ℝ) / 2 + 1 / 4)
  let d : ℝ := 2 * Real.sqrt 2 * π * Real.sqrt a
  have hw1 : (1 : ℝ) ≤ (prob.w : ℝ) := by exact_mod_cast prob.hw
  have hb_neg : b ≤ 0 := by dsimp [b]; linarith
  have hd_eq : ∀ t : ℝ, 0 ≤ t → d * Real.sqrt (2 * t) = 4 * π * Real.sqrt (a * t) := fun t _ => by
    dsimp [d]
    rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul ha_pos.le]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
    calc (2 * Real.sqrt 2 * π * Real.sqrt a) * (Real.sqrt 2 * Real.sqrt t)
        = 2 * (Real.sqrt 2 * Real.sqrt 2) * π * (Real.sqrt a * Real.sqrt t) := by ring
      _ = 4 * π * (Real.sqrt a * Real.sqrt t) := by rw [hsq2]; ring
  obtain ⟨c_b, z₀, hc_b_pos, hz₀_ge1, hbes_lb⟩ := besselI_ge_exp_div_sqrt (prob.w - 1)
  let T_bes : ℝ := max 1 (z₀ ^ 2 / (16 * π ^ 2 * a))
  have hT_bes_ge1 : 1 ≤ T_bes := le_max_left _ _
  have hK_a_lb : ∀ t : ℝ, T_bes ≤ t →
      (c_b * a ^ b / Real.sqrt (4 * π)) * t ^ ((prob.w - 1 : ℝ) + b) *
        Real.exp (4 * π * Real.sqrt (a * t)) ≤ kernelK prob.w a t := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le (by linarith) ht
    have hz_ge : z₀ ≤ 4 * π * Real.sqrt (a * t) := by
      have hz_sq : z₀ ^ 2 ≤ 16 * π ^ 2 * (a * t) := by
        have h1 : z₀ ^ 2 / (16 * π ^ 2 * a) ≤ t := (le_max_right _ _).trans ht
        rw [div_le_iff₀ (by positivity)] at h1
        linarith
      rw [← Real.sqrt_sq (by linarith : 0 ≤ z₀)]
      calc Real.sqrt (z₀ ^ 2) ≤ Real.sqrt (16 * π ^ 2 * (a * t)) := Real.sqrt_le_sqrt hz_sq
        _ = Real.sqrt ((4 * π) ^ 2 * (a * t)) := by congr 1; ring
        _ = 4 * π * Real.sqrt (a * t) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hbes := hbes_lb (4 * π * Real.sqrt (a * t)) hz_ge
    rw [kernelK_eq_besselI prob.hw ha_pos ht_pos]
    have hpref := rpow_bessel_prefactor prob.hw ha_pos ht_pos
    calc (c_b * a ^ b / Real.sqrt (4 * π)) * t ^ ((prob.w - 1 : ℝ) + b) *
          Real.exp (4 * π * Real.sqrt (a * t))
        = c_b * ((a ^ b / Real.sqrt (4 * π)) * t ^ ((prob.w - 1 : ℝ) + b)) *
            Real.exp (4 * π * Real.sqrt (a * t)) := by ring
      _ = Real.sqrt (t / a) ^ (prob.w - 1) *
            (c_b * Real.exp (4 * π * Real.sqrt (a * t)) / Real.sqrt (4 * π * Real.sqrt (a * t))) := by
          rw [← hpref]; ring
      _ ≤ Real.sqrt (t / a) ^ (prob.w - 1) * Bessel.besselI (prob.w - 1) (4 * π * Real.sqrt (a * t)) :=
          mul_le_mul_of_nonneg_left hbes (pow_nonneg (Real.sqrt_nonneg _) _)
  have hV_half_Ka : ∃ T_V : ℝ, 1 ≤ T_V ∧ ∀ t : ℝ, T_V ≤ t →
      (1 / 2 : ℝ) * kernelK prob.w a t ≤ prob.cardyV a t := by
    by_cases hm : prob.m = 0
    · refine ⟨1, le_rfl, fun t ht => ?_⟩
      have : IsEmpty (Fin prob.m) := by rw [hm]; infer_instance
      have hcard : prob.cardyV a t = kernelK prob.w a t := by
        unfold FixedWeightProblem.cardyV
        have hfin : (Finset.univ : Finset (Finset (Fin prob.m))) = {∅} := by
          ext s; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
          exact Finset.eq_empty_of_isEmpty s
        rw [hfin, Finset.sum_singleton]
        simp [FixedWeightProblem.shiftSum]
      rw [hcard]
      have hnn : 0 ≤ kernelK prob.w a t := kernelK_nonneg ha_pos.le (by linarith)
      linarith
    · have hm_pos : 0 < prob.m := Nat.pos_of_ne_zero hm
      have hne_fin : (Finset.univ : Finset (Fin prob.m)).Nonempty :=
        ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
      let μ_min : ℝ := Finset.univ.inf' hne_fin prob.μ
      have hμ_min_pos : 0 < μ_min := by
        obtain ⟨l, _, hl⟩ := Finset.exists_mem_eq_inf' hne_fin prob.μ
        show 0 < μ_min
        dsimp [μ_min]
        rw [hl]
        exact prob.hμ l
      have hμ_min_le : ∀ l : Fin prob.m, μ_min ≤ prob.μ l := fun l =>
        Finset.inf'_le prob.μ (Finset.mem_univ l)
      have hμ_min_le_tot : μ_min ≤ prob.totalShift := by
        calc μ_min ≤ prob.μ ⟨0, hm_pos⟩ := hμ_min_le ⟨0, hm_pos⟩
          _ ≤ ∑ l : Fin prob.m, prob.μ l :=
              Finset.single_le_sum (fun l _ => (prob.hμ l).le) (Finset.mem_univ _)
          _ = prob.totalShift := rfl
      let α₁ : ℝ := max (a - μ_min) (a / 2)
      have hα₁_pos : 0 < α₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hα₁_lt : α₁ < a := max_lt (by linarith) (by linarith)
      have hK_mono : ∀ s : Finset (Fin prob.m), s ≠ ∅ → ∀ t : ℝ, 0 ≤ t →
          kernelK prob.w (a - prob.shiftSum s) t ≤ kernelK prob.w α₁ t := by
        intro s hs t ht
        obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hshift_ge : μ_min ≤ prob.shiftSum s := by
          calc μ_min ≤ prob.μ l := hμ_min_le l
            _ ≤ ∑ j ∈ s, prob.μ j := Finset.single_le_sum (fun j _ => (prob.hμ j).le) hl
            _ = prob.shiftSum s := rfl
        have hdiff_nn : 0 ≤ a - prob.shiftSum s :=
          sub_nonneg.mpr ((prob.shiftSum_le_totalShift s).trans ha)
        have hdiff_le : a - prob.shiftSum s ≤ α₁ :=
          (by linarith : a - prob.shiftSum s ≤ a - μ_min).trans (le_max_left _ _)
        exact kernelK_mono_alpha hdiff_nn hdiff_le ht
      let c_a : ℝ := c_b * a ^ b / Real.sqrt (4 * π)
      have hc_a_pos : 0 < c_a := by positivity
      let C₁ : ℝ := α₁ ^ b * Real.sqrt (π / 8) / Real.sqrt (4 * π)
      have hC₁_pos : 0 < C₁ := by positivity
      have hK_α₁_ub : ∀ t : ℝ, 1 ≤ t →
          kernelK prob.w α₁ t ≤
            C₁ * t ^ ((prob.w - 1 : ℝ) + b) * Real.exp (4 * π * Real.sqrt (α₁ * t)) := by
        intro t ht
        have ht_pos : 0 < t := by linarith
        rw [kernelK_eq_besselI prob.hw hα₁_pos ht_pos]
        have hbes := (besselI_le_zero (prob.w - 1) (4 * π * Real.sqrt (α₁ * t))).trans
          (besselI_zero_le_exp_div_sqrt (by positivity : 0 < 4 * π * Real.sqrt (α₁ * t)))
        have hpref := rpow_bessel_prefactor prob.hw hα₁_pos ht_pos
        calc Real.sqrt (t / α₁) ^ (prob.w - 1) * Bessel.besselI (prob.w - 1) (4 * π * Real.sqrt (α₁ * t))
            ≤ Real.sqrt (t / α₁) ^ (prob.w - 1) *
                (Real.sqrt (π / 8) * Real.exp (4 * π * Real.sqrt (α₁ * t)) /
                  Real.sqrt (4 * π * Real.sqrt (α₁ * t))) :=
              mul_le_mul_of_nonneg_left hbes (pow_nonneg (Real.sqrt_nonneg _) _)
          _ = (Real.sqrt (t / α₁) ^ (prob.w - 1) / Real.sqrt (4 * π * Real.sqrt (α₁ * t))) *
                Real.sqrt (π / 8) * Real.exp (4 * π * Real.sqrt (α₁ * t)) := by ring
          _ = C₁ * t ^ ((prob.w - 1 : ℝ) + b) * Real.exp (4 * π * Real.sqrt (α₁ * t)) := by
              rw [hpref]; dsimp [C₁, b]; ring
      let gap : ℝ := 4 * π * (Real.sqrt a - Real.sqrt α₁)
      have hgap_pos : 0 < gap :=
        mul_pos (by positivity) (sub_pos.mpr (Real.sqrt_lt_sqrt hα₁_pos.le hα₁_lt))
      let K_rat : ℝ := max 1 ((2 : ℝ) ^ prob.m * C₁ / (c_a / 2))
      have hK_rat_pos : 0 < K_rat := by positivity
      let T_exp : ℝ := (Real.log K_rat / gap) ^ 2
      refine ⟨max T_bes (max 1 T_exp), le_trans (le_max_left _ _) (le_max_right _ _), fun t ht => ?_⟩
      have ht_bes : T_bes ≤ t := (le_max_left _ _).trans ht
      have ht_ge1 : 1 ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
      have ht_exp : T_exp ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
      have ht_pos : 0 < t := by linarith
      have hsqrt_t : Real.log K_rat / gap ≤ Real.sqrt t := by
        rcases le_or_gt (Real.log K_rat / gap) 0 with hneg | hpos
        · exact hneg.trans (Real.sqrt_nonneg t)
        · rw [← Real.sqrt_sq hpos.le]
          exact Real.sqrt_le_sqrt ht_exp
      have hexp_gap : K_rat * Real.exp (4 * π * Real.sqrt (α₁ * t)) ≤
          Real.exp (4 * π * Real.sqrt (a * t)) := by
        have hlog : Real.log K_rat ≤ gap * Real.sqrt t := by
          have := mul_le_mul_of_nonneg_left hsqrt_t hgap_pos.le
          rwa [mul_div_cancel₀ _ hgap_pos.ne'] at this
        have hK_le : K_rat ≤ Real.exp (gap * Real.sqrt t) := by
          rw [← Real.exp_log hK_rat_pos]
          exact Real.exp_le_exp.mpr hlog
        calc K_rat * Real.exp (4 * π * Real.sqrt (α₁ * t))
            ≤ Real.exp (gap * Real.sqrt t) * Real.exp (4 * π * Real.sqrt (α₁ * t)) :=
              mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le
          _ = Real.exp (gap * Real.sqrt t + 4 * π * Real.sqrt (α₁ * t)) := (Real.exp_add _ _).symm
          _ = Real.exp (4 * π * Real.sqrt (a * t)) := by
              congr 1
              rw [Real.sqrt_mul hα₁_pos.le, Real.sqrt_mul ha_pos.le]
              dsimp [gap]; ring
      have hsub_le : (2 : ℝ) ^ prob.m * kernelK prob.w α₁ t ≤ (1 / 2 : ℝ) * kernelK prob.w a t := by
        have hpow_nn : 0 ≤ t ^ ((prob.w - 1 : ℝ) + b) := Real.rpow_nonneg ht_pos.le _
        have hKa_lb := hK_a_lb t ht_bes
        have hKα₁ := hK_α₁_ub t ht_ge1
        have hmul_c : (2 : ℝ) ^ prob.m * C₁ ≤ (c_a / 2) * K_rat := by
          have := mul_le_mul_of_nonneg_left
            (le_max_right (1 : ℝ) ((2 : ℝ) ^ prob.m * C₁ / (c_a / 2)))
            (by linarith : 0 ≤ c_a / 2)
          rwa [mul_div_cancel₀ _ (by positivity)] at this
        calc (2 : ℝ) ^ prob.m * kernelK prob.w α₁ t
            ≤ (2 : ℝ) ^ prob.m *
                (C₁ * t ^ ((prob.w - 1 : ℝ) + b) * Real.exp (4 * π * Real.sqrt (α₁ * t))) :=
              mul_le_mul_of_nonneg_left hKα₁ (by positivity)
          _ = ((2 : ℝ) ^ prob.m * C₁) * t ^ ((prob.w - 1 : ℝ) + b) *
                Real.exp (4 * π * Real.sqrt (α₁ * t)) := by ring
          _ ≤ ((c_a / 2) * K_rat) * t ^ ((prob.w - 1 : ℝ) + b) *
                Real.exp (4 * π * Real.sqrt (α₁ * t)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmul_c hpow_nn)
                (Real.exp_pos _).le
          _ = (c_a / 2) * t ^ ((prob.w - 1 : ℝ) + b) *
                (K_rat * Real.exp (4 * π * Real.sqrt (α₁ * t))) := by ring
          _ ≤ (c_a / 2) * t ^ ((prob.w - 1 : ℝ) + b) * Real.exp (4 * π * Real.sqrt (a * t)) :=
              mul_le_mul_of_nonneg_left hexp_gap (mul_nonneg (by positivity) hpow_nn)
          _ = (1 / 2 : ℝ) *
                (c_a * t ^ ((prob.w - 1 : ℝ) + b) * Real.exp (4 * π * Real.sqrt (a * t))) := by ring
          _ ≤ (1 / 2 : ℝ) * kernelK prob.w a t :=
              mul_le_mul_of_nonneg_left hKa_lb (by norm_num)
      have hcardy_lb : kernelK prob.w a t - (2 : ℝ) ^ prob.m * kernelK prob.w α₁ t ≤
          prob.cardyV a t := by
        unfold FixedWeightProblem.cardyV
        have hsplit : ∑ s : Finset (Fin prob.m), (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t =
            kernelK prob.w a t + ∑ s ∈ Finset.univ.erase ∅,
              (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ∅)]
          simp [FixedWeightProblem.shiftSum]
        rw [hsplit]
        have hsum_bound : ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin prob.m)),
            (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t ≥
            -(2 : ℝ) ^ prob.m * kernelK prob.w α₁ t := by
          have hterm_ge : ∀ s ∈ Finset.univ.erase (∅ : Finset (Fin prob.m)),
              -kernelK prob.w α₁ t ≤ (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t := by
            intro s hs
            have hs_ne : s ≠ ∅ := (Finset.mem_erase.mp hs).1
            have hdiff_nn : 0 ≤ a - prob.shiftSum s :=
              sub_nonneg.mpr ((prob.shiftSum_le_totalShift s).trans ha)
            have hk_nn : 0 ≤ kernelK prob.w (a - prob.shiftSum s) t := kernelK_nonneg hdiff_nn ht_pos.le
            have hk_le : kernelK prob.w (a - prob.shiftSum s) t ≤ kernelK prob.w α₁ t :=
              hK_mono s hs_ne t ht_pos.le
            have hneg_one : -kernelK prob.w (a - prob.shiftSum s) t ≤
                (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t := by
              rcases neg_one_pow_eq_or ℝ s.card with h1 | h1 <;> rw [h1] <;> linarith
            linarith
          have hcard_le : ((Finset.univ.erase (∅ : Finset (Fin prob.m))).card : ℝ) ≤ (2 : ℝ) ^ prob.m := by
            have h1 : (Finset.univ.erase (∅ : Finset (Fin prob.m))).card ≤
                (Finset.univ : Finset (Finset (Fin prob.m))).card :=
              Finset.card_le_card (Finset.erase_subset _ _)
            have h2 : (Finset.univ : Finset (Finset (Fin prob.m))).card = 2 ^ prob.m := by
              simp [Fintype.card_finset]
            exact_mod_cast h1.trans_eq h2
          calc -(2 : ℝ) ^ prob.m * kernelK prob.w α₁ t
              ≤ -((Finset.univ.erase (∅ : Finset (Fin prob.m))).card : ℝ) * kernelK prob.w α₁ t := by
                refine mul_le_mul_of_nonneg_right (neg_le_neg hcard_le)
                  (kernelK_nonneg hα₁_pos.le ht_pos.le)
            _ = ∑ _s ∈ Finset.univ.erase (∅ : Finset (Fin prob.m)), (-kernelK prob.w α₁ t) := by
                simp [Finset.sum_const, nsmul_eq_mul]; ring
            _ ≤ ∑ s ∈ Finset.univ.erase (∅ : Finset (Fin prob.m)),
                  (-1 : ℝ) ^ s.card * kernelK prob.w (a - prob.shiftSum s) t :=
                Finset.sum_le_sum hterm_ge
        linarith
      linarith
  obtain ⟨T_V, hT_V_ge1, hV_half⟩ := hV_half_Ka
  let c₀ : ℝ := ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π)
  have hc₀_pos : 0 < c₀ := by positivity
  let c_lo : ℝ := c₀ * (1 / 2 : ℝ) * (c_b * a ^ b / Real.sqrt (4 * π))
  refine ⟨c_lo, max T_bes T_V, by positivity, le_trans hT_bes_ge1 (le_max_left _ _), fun t ht => ?_⟩
  have ht_bes : T_bes ≤ t := (le_max_left _ _).trans ht
  have ht_V : T_V ≤ t := (le_max_right _ _).trans ht
  have ht_pos : 0 < t := by linarith
  have hV_lb := hK_a_lb t ht_bes
  have hV_comp := hV_half t ht_V
  have hrho_eq : prob.rhoDensity a t = c₀ * (prob.cardyV a t / t ^ (prob.w - 1)) := by
    unfold FixedWeightProblem.rhoDensity
    rw [prob.cardyV_eq_pow_mul_reduced]
    have hpow_ne : t ^ (prob.w - 1) ≠ 0 := pow_ne_zero _ ht_pos.ne'
    dsimp [c₀]
    field_simp
  have h12t_ge : t ≤ 1 + 2 * t := by linarith
  have hpow_cardy : (1 + 2 * t) ^ b ≤ t ^ b :=
    Real.rpow_le_rpow_of_nonpos ht_pos h12t_ge hb_neg
  have hpow_div : t ^ ((prob.w - 1 : ℝ) + b) / t ^ (prob.w - 1) = t ^ b := by
    rw [← Real.rpow_natCast t (prob.w - 1), Nat.cast_sub prob.hw, Nat.cast_one,
      Real.rpow_add ht_pos, mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos ht_pos _).ne']
  rw [hrho_eq]
  unfold cardyWeight
  rw [hd_eq t ht_pos.le]
  calc c_lo * ((1 + 2 * t) ^ b * Real.exp (4 * π * Real.sqrt (a * t)))
      ≤ c_lo * (t ^ b * Real.exp (4 * π * Real.sqrt (a * t))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow_cardy (Real.exp_pos _).le)
          (by positivity)
    _ = c₀ * ((1 / 2 : ℝ) * ((c_b * a ^ b / Real.sqrt (4 * π)) *
          t ^ ((prob.w - 1 : ℝ) + b) * Real.exp (4 * π * Real.sqrt (a * t)) / t ^ (prob.w - 1))) := by
        rw [show (c_b * a ^ b / Real.sqrt (4 * π)) * t ^ ((prob.w - 1 : ℝ) + b) *
            Real.exp (4 * π * Real.sqrt (a * t)) / t ^ (prob.w - 1) =
            (c_b * a ^ b / Real.sqrt (4 * π)) * (t ^ ((prob.w - 1 : ℝ) + b) / t ^ (prob.w - 1)) *
            Real.exp (4 * π * Real.sqrt (a * t)) by ring, hpow_div]
        dsimp [c_lo]; ring
    _ ≤ c₀ * ((1 / 2 : ℝ) * (kernelK prob.w a t / t ^ (prob.w - 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hV_lb (pow_nonneg ht_pos.le _)) (by norm_num)) hc₀_pos.le
    _ = c₀ * (((1 / 2 : ℝ) * kernelK prob.w a t) / t ^ (prob.w - 1)) := by ring
    _ ≤ c₀ * (prob.cardyV a t / t ^ (prob.w - 1)) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hV_comp (pow_nonneg ht_pos.le _))
          hc₀_pos.le

private lemma pow_le_const_mul_exp_mul {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → u ^ k ≤ C * Real.exp (c * u) := by
  refine ⟨(k.factorial : ℝ) / c ^ k, by positivity, fun u hu => ?_⟩
  have hterm : (c * u) ^ k / (k.factorial : ℝ) ≤ Real.exp (c * u) := by
    have hnn : ∀ m : ℕ, 0 ≤ (c * u) ^ m / (m.factorial : ℝ) := fun m => by positivity
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    have hle := (Real.summable_pow_div_factorial (c * u)).le_tsum k (fun m _ => hnn m)
    simpa [div_eq_mul_inv, mul_comm, smul_eq_mul] using hle
  have hk_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  rw [mul_pow] at hterm
  have h2 : c ^ k * u ^ k ≤ (k.factorial : ℝ) * Real.exp (c * u) := by
    rwa [div_le_iff₀ hk_pos, mul_comm (Real.exp (c * u))] at hterm
  rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc k)]
  nlinarith

/-! ### Section 2: Mehler kernel `K_r`, regularisation `A_r`, and Lemma FW-A (`fw:abel`) -/

/-- Cartesian Euclidean space `ℝ^{2w}` used for Hankel/Mehler regularisation (`t = ‖x‖² / 2`). -/
abbrev RadialSpace (w : ℕ) : Type := EuclideanSpace ℝ (Fin (2 * w))

/-- Cartesian Mehler kernel in the Mathlib normalization `t = ‖x‖² / 2`:
`K_r(x, y) = ((1 - r) / 2)^{-w} exp(-π * ((1 + r)(‖x‖² + ‖y‖²) - 4 √r ⟨x, y⟩) / (1 - r))`. -/
noncomputable def mehlerKernel (w : ℕ) (r : ℝ) (x y : RadialSpace w) : ℝ :=
  ((1 - r) / 2) ^ (-(w : ℝ)) *
    Real.exp (-π * ((1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y) / (1 - r))

/-- Mehler regularisation `(A_r f)(x) = ∫ y, K_r(x, y) f(y) dy`. -/
noncomputable def mehlerMean (w : ℕ) (r : ℝ) (f : RadialSpace w → ℝ) (x : RadialSpace w) : ℝ :=
  ∫ y : RadialSpace w, mehlerKernel w r x y * f y

lemma mehlerKernel_nonneg (w : ℕ) {r : ℝ} (hr1 : r < 1) (x y : RadialSpace w) :
    0 ≤ mehlerKernel w r x y := by
  unfold mehlerKernel
  have h1r : 0 < (1 - r) / 2 := by linarith
  exact mul_nonneg (Real.rpow_nonneg h1r.le _) (Real.exp_pos _).le

lemma mehlerKernel_symm (w : ℕ) (r : ℝ) (x y : RadialSpace w) :
    mehlerKernel w r x y = mehlerKernel w r y x := by
  unfold mehlerKernel
  rw [real_inner_comm]
  ring_nf

lemma continuous_mehlerKernel (w : ℕ) (r : ℝ) :
    Continuous (fun p : RadialSpace w × RadialSpace w => mehlerKernel w r p.1 p.2) := by
  unfold mehlerKernel
  fun_prop

lemma mehlerKernel_quad_identity {w : ℕ} {r : ℝ} (hr : 0 ≤ r) (x y : RadialSpace w) :
    (1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y =
      (1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2 := by
  have hinner : 2 * @inner ℝ _ _ x y = ‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2 := by
    linarith [norm_sub_sq_real x y]
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  calc (1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y
      = (1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 2 * Real.sqrt r * (2 * @inner ℝ _ _ x y) := by ring
    _ = (1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 2 * Real.sqrt r * (‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2) := by
        rw [hinner]
    _ = (1 - 2 * Real.sqrt r + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2 := by ring
    _ = (1 - 2 * Real.sqrt r + Real.sqrt r ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) +
          2 * Real.sqrt r * ‖x - y‖ ^ 2 := by rw [hsq]
    _ = (1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2 := by ring

lemma mehlerKernel_shift_identity {w : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r < 1) (x y : RadialSpace w) :
    (1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ x y =
      (1 + r) * ‖y - ((2 * Real.sqrt r / (1 + r)) • x)‖ ^ 2 + ((1 - r) ^ 2 / (1 + r)) * ‖x‖ ^ 2 := by
  have h1r : (1 + r) ≠ 0 := by linarith
  rw [norm_sub_sq_real, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt r / (1 + r)),
    inner_smul_right, real_inner_comm]
  have halg : (1 + r) * (‖y‖ ^ 2 - 2 * (2 * Real.sqrt r / (1 + r) * @inner ℝ _ _ y x) +
      (2 * Real.sqrt r / (1 + r) * ‖x‖) ^ 2) + (1 - r) ^ 2 / (1 + r) * ‖x‖ ^ 2 =
      (1 + r) * (‖x‖ ^ 2 + ‖y‖ ^ 2) - 4 * Real.sqrt r * @inner ℝ _ _ y x := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hr0]
    field_simp
    ring
  exact halg.symm

lemma mehlerKernel_le_diff_gaussian (w : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x y : RadialSpace w) :
    mehlerKernel w r x y ≤
      ((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-2 * π * Real.sqrt r / (1 - r) * ‖x - y‖ ^ 2) := by
  unfold mehlerKernel
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by linarith) _)
  rw [mehlerKernel_quad_identity hr0 x y]
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have hnn : 0 ≤ (1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
  have hnum : 2 * Real.sqrt r * ‖x - y‖ ^ 2 ≤
      (1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2 := by linarith
  have hdiv : -π * ((1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2) / (1 - r) ≤
      -π * (2 * Real.sqrt r * ‖x - y‖ ^ 2) / (1 - r) := by
    refine div_le_div_of_nonneg_right ?_ h1r_pos.le
    nlinarith [Real.pi_pos]
  exact hdiv.trans_eq (by ring)

lemma mehlerKernel_le_half_gaussian (w : ℕ) {r : ℝ} (hr12 : 1 / 2 ≤ r) (hr1 : r < 1)
    (x y : RadialSpace w) :
    mehlerKernel w r x y ≤
      ((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖x - y‖ ^ 2) := by
  refine (mehlerKernel_le_diff_gaussian w (by linarith) hr1 x y).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by linarith) _)
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have hsq_r : (1 : ℝ) ≤ 2 * Real.sqrt r := by
    have h4r : (1 : ℝ) ≤ 4 * r := by linarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (4 * r) := Real.sqrt_le_sqrt h4r
      _ = Real.sqrt (2 ^ 2 * r) := by norm_num
      _ = 2 * Real.sqrt r := by rw [Real.sqrt_mul (sq_nonneg 2), Real.sqrt_sq zero_le_two]
  have hdiv : -2 * π * Real.sqrt r / (1 - r) ≤ -π / (1 - r) := by
    refine div_le_div_of_nonneg_right ?_ h1r_pos.le
    nlinarith [Real.pi_pos]
  exact mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)

/-- Exact `2w`-dimensional Gaussian integral `∫ y, exp(-π c ‖y‖²) dy = c^{-w}`. -/
lemma integral_exp_neg_pi_mul_norm_sq (w : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : RadialSpace w => Real.exp (-π * c * ‖y‖ ^ 2)) ∧
      ∫ y : RadialSpace w, Real.exp (-π * c * ‖y‖ ^ 2) = c ^ (-(w : ℝ)) := by
  have hb : 0 < ((π * c : ℝ) : ℂ).re := by simp [Real.pi_pos, hc]
  have hlift : (fun y : RadialSpace w => Complex.exp (-((π * c : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2)) =
      fun y => (Real.exp (-π * c * ‖y‖ ^ 2) : ℂ) := by
    ext y; rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hintC : Integrable (fun y : RadialSpace w =>
      Complex.exp (-((π * c : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : RadialSpace w)
  have hintR : Integrable (fun y : RadialSpace w => Real.exp (-π * c * ‖y‖ ^ 2)) := by
    have heq : (fun y : RadialSpace w => Real.exp (-π * c * ‖y‖ ^ 2)) =
        fun y => Complex.reCLM (Complex.exp (-((π * c : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2)) := by
      ext y
      have h1 : Complex.exp (-((π * c : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2) =
          (Real.exp (-π * c * ‖y‖ ^ 2) : ℂ) := by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      rw [h1, Complex.reCLM_apply, Complex.ofReal_re]
    rw [heq]
    exact Complex.reCLM.integrable_comp hintC
  refine ⟨hintR, ?_⟩
  have hfou := fourier_gaussian_innerProductSpace (V := RadialSpace w) hb 0
  have hlhs : 𝓕 (fun y : RadialSpace w => Complex.exp (-((π * c : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2)) 0 =
      ∫ y : RadialSpace w, (Real.exp (-π * c * ‖y‖ ^ 2) : ℂ) := by
    rw [Real.fourier_eq, ← hlift]
    simp
  rw [hlhs] at hfou
  have hdim : (Module.finrank ℝ (RadialSpace w) / 2 : ℂ) = (w : ℂ) := by
    rw [finrank_euclideanSpace_fin]; push_cast; ring
  have hpi : ((π : ℝ) : ℂ) / ((π * c : ℝ) : ℂ) = ((c⁻¹ : ℝ) : ℂ) := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    push_cast; field_simp
  rw [hdim, hpi, show (w : ℂ) = ((w : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ c⁻¹), Real.inv_rpow hc.le,
    ← Real.rpow_neg hc.le] at hfou
  simp only [norm_zero, Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_div, Complex.exp_zero, mul_one] at hfou
  have hio : (∫ y : RadialSpace w, (Real.exp (-π * c * ‖y‖ ^ 2) : ℂ)) =
      ((∫ y : RadialSpace w, Real.exp (-π * c * ‖y‖ ^ 2) : ℝ) : ℂ) := integral_ofReal
  rw [hio] at hfou
  exact Complex.ofReal_inj.mp hfou

/-- Exact mass of the Mehler kernel: `∫ y, K_r(x, y) dy = (2 / (1 + r))^w * exp(-π ((1-r)/(1+r)) ‖x‖²)`. -/
theorem integral_mehlerKernel (w : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : RadialSpace w) :
    Integrable (fun y => mehlerKernel w r x y) ∧
      ∫ y : RadialSpace w, mehlerKernel w r x y =
        (2 / (1 + r)) ^ (w : ℝ) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1pr_pos : 0 < 1 + r := by linarith
  have hc_pos : 0 < (1 + r) / (1 - r) := div_pos h1pr_pos h1r_pos
  let x₀ : RadialSpace w := (2 * Real.sqrt r / (1 + r)) • x
  let C₀ : ℝ := ((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)
  have heq : ∀ y : RadialSpace w, mehlerKernel w r x y =
      C₀ * Real.exp (-π * ((1 + r) / (1 - r)) * ‖y - x₀‖ ^ 2) := fun y => by
    unfold mehlerKernel
    rw [mehlerKernel_shift_identity hr0 hr1 x y]
    dsimp [C₀, x₀]
    have hexp_eq : -π * ((1 + r) * ‖y - (2 * Real.sqrt r / (1 + r)) • x‖ ^ 2 +
          (1 - r) ^ 2 / (1 + r) * ‖x‖ ^ 2) / (1 - r) =
        (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) +
          (-π * ((1 + r) / (1 - r)) * ‖y - (2 * Real.sqrt r / (1 + r)) • x‖ ^ 2) := by
      field_simp; ring
    rw [hexp_eq, Real.exp_add]; ring
  have hg := integral_exp_neg_pi_mul_norm_sq w hc_pos
  have hint_shift : Integrable (fun y : RadialSpace w =>
      Real.exp (-π * ((1 + r) / (1 - r)) * ‖y - x₀‖ ^ 2)) :=
    hg.1.comp_sub_right x₀
  have hint : Integrable (fun y => mehlerKernel w r x y) := by
    simp_rw [heq]
    exact hint_shift.const_mul C₀
  refine ⟨hint, ?_⟩
  simp_rw [heq]
  rw [integral_const_mul]
  change C₀ * ∫ y : RadialSpace w,
      (fun u : RadialSpace w => Real.exp (-π * ((1 + r) / (1 - r)) * ‖u‖ ^ 2)) (y - x₀) = _
  rw [integral_sub_right_eq_self (fun u : RadialSpace w => Real.exp (-π * ((1 + r) / (1 - r)) * ‖u‖ ^ 2)) x₀,
    hg.2]
  have hpow : ((1 - r) / 2) ^ (-(w : ℝ)) * ((1 + r) / (1 - r)) ^ (-(w : ℝ)) =
      (2 / (1 + r)) ^ (w : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have hsimp : (1 - r) / 2 * ((1 + r) / (1 - r)) = (2 / (1 + r))⁻¹ := by field_simp
    rw [hsimp, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  dsimp [C₀]
  calc (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)) *
        ((1 + r) / (1 - r)) ^ (-(w : ℝ))
      = (((1 - r) / 2) ^ (-(w : ℝ)) * ((1 + r) / (1 - r)) ^ (-(w : ℝ))) *
          Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by ring
    _ = (2 / (1 + r)) ^ (w : ℝ) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) := by rw [hpow]

lemma integral_mehlerKernel_le (w : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : RadialSpace w) :
    ∫ y : RadialSpace w, mehlerKernel w r x y ≤ (2 : ℝ) ^ w := by
  rw [(integral_mehlerKernel w hr0 hr1 x).2]
  have h2_le : 2 / (1 + r) ≤ 2 := div_le_self (by norm_num) (by linarith)
  have hpow_le : (2 / (1 + r)) ^ (w : ℝ) ≤ (2 : ℝ) ^ (w : ℝ) :=
    Real.rpow_le_rpow (by positivity) h2_le (Nat.cast_nonneg w)
  have hexp_le : Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have h1r : 0 ≤ (1 - r) / (1 + r) := div_nonneg (sub_nonneg.mpr hr1.le) (by linarith)
      rw [show -π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2 = -(π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) by ring]
      exact neg_nonpos.mpr (by positivity))
  have hrp : (2 : ℝ) ^ (w : ℝ) = (2 : ℝ) ^ w := Real.rpow_natCast 2 w
  calc (2 / (1 + r)) ^ (w : ℝ) * Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)
      ≤ (2 / (1 + r)) ^ (w : ℝ) * 1 := mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ ≤ (2 : ℝ) ^ w := by rw [mul_one, ← hrp]; exact hpow_le

/-- Euclidean weight `W(x) = (1 + ‖x‖²)^b exp(d ‖x‖)` (`b, d ∈ ℝ`). -/
noncomputable def euclideanWeight (b d : ℝ) {w : ℕ} (x : RadialSpace w) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ b * Real.exp (d * ‖x‖)

lemma euclideanWeight_eq_cardyWeight (b d : ℝ) {w : ℕ} (x : RadialSpace w) :
    euclideanWeight b d x = cardyWeight b d (‖x‖ ^ 2 / 2) := by
  unfold euclideanWeight cardyWeight
  have h2 : 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 := by ring
  rw [h2, Real.sqrt_sq (norm_nonneg x)]

lemma euclideanWeight_pos (b d : ℝ) {w : ℕ} (x : RadialSpace w) :
    0 < euclideanWeight b d x := by
  unfold euclideanWeight
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) b) (Real.exp_pos _)

/-- Peetre + triangle ratio bound for `euclideanWeight b d`:
`W(y) ≤ 2^{|b|} W(x) (1 + ‖y - x‖²)^{|b|} exp(|d| ‖y - x‖)`. -/
lemma euclideanWeight_ratio_le (b d : ℝ) {w : ℕ} (x y : RadialSpace w) :
    euclideanWeight b d y ≤
      (2 : ℝ) ^ |b| * euclideanWeight b d x *
        ((1 + ‖y - x‖ ^ 2) ^ |b| * Real.exp (|d| * ‖y - x‖)) := by
  have hpeetre : ∀ u v : RadialSpace w,
      1 + ‖u + v‖ ^ 2 ≤ 2 * (1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2) := fun u v => by
    have hnorm : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
    nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg ‖u‖, sq_nonneg ‖v‖]
  have hpow : (1 + ‖y‖ ^ 2) ^ b ≤
      (2 : ℝ) ^ |b| * (1 + ‖x‖ ^ 2) ^ b * (1 + ‖y - x‖ ^ 2) ^ |b| := by
    rcases le_or_gt 0 b with hb | hb
    · rw [abs_of_nonneg hb]
      have h1 : 1 + ‖y‖ ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) * (1 + ‖y - x‖ ^ 2) := by
        simpa [add_sub_cancel] using hpeetre x (y - x)
      have hrp := Real.rpow_le_rpow (by positivity) h1 hb
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)] at hrp
      exact hrp
    · rw [abs_of_neg hb]
      have h1 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) * (1 + ‖y - x‖ ^ 2) := by
        simpa [sub_add_cancel, norm_sub_rev] using hpeetre y (x - y)
      have hrp : (2 * (1 + ‖y‖ ^ 2) * (1 + ‖y - x‖ ^ 2)) ^ b ≤ (1 + ‖x‖ ^ 2) ^ b :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 hb.le
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)] at hrp
      have h2_pos : 0 < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
      have hv_pos : 0 < (1 + ‖y - x‖ ^ 2) ^ (-b) := Real.rpow_pos_of_pos (by positivity) _
      have h2_inv : (2 : ℝ) ^ (-b) * (2 : ℝ) ^ b = 1 := by
        rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
      have hv_inv : (1 + ‖y - x‖ ^ 2) ^ (-b) * (1 + ‖y - x‖ ^ 2) ^ b = 1 := by
        rw [← Real.rpow_add (by positivity), neg_add_cancel, Real.rpow_zero]
      have hmul := mul_le_mul_of_nonneg_left hrp (mul_pos h2_pos hv_pos).le
      calc (1 + ‖y‖ ^ 2) ^ b
          = ((2 : ℝ) ^ (-b) * (1 + ‖y - x‖ ^ 2) ^ (-b)) *
              ((2 : ℝ) ^ b * (1 + ‖y‖ ^ 2) ^ b * (1 + ‖y - x‖ ^ 2) ^ b) := by
            calc (1 + ‖y‖ ^ 2) ^ b = 1 * 1 * (1 + ‖y‖ ^ 2) ^ b := by ring
              _ = ((2 : ℝ) ^ (-b) * (2 : ℝ) ^ b) * ((1 + ‖y - x‖ ^ 2) ^ (-b) *
                    (1 + ‖y - x‖ ^ 2) ^ b) * (1 + ‖y‖ ^ 2) ^ b := by rw [h2_inv, hv_inv]
              _ = _ := by ring
        _ ≤ ((2 : ℝ) ^ (-b) * (1 + ‖y - x‖ ^ 2) ^ (-b)) * (1 + ‖x‖ ^ 2) ^ b := hmul
        _ = (2 : ℝ) ^ (-b) * (1 + ‖x‖ ^ 2) ^ b * (1 + ‖y - x‖ ^ 2) ^ (-b) := by ring
  have hexp : Real.exp (d * ‖y‖) ≤ Real.exp (d * ‖x‖) * Real.exp (|d| * ‖y - x‖) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have htri : d * ‖y‖ - d * ‖x‖ ≤ |d| * ‖y - x‖ :=
      calc d * ‖y‖ - d * ‖x‖ = d * (‖y‖ - ‖x‖) := by ring
        _ ≤ |d * (‖y‖ - ‖x‖)| := le_abs_self _
        _ = |d| * |‖y‖ - ‖x‖| := abs_mul _ _
        _ ≤ |d| * ‖y - x‖ := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le y x) (abs_nonneg d)
    linarith
  unfold euclideanWeight
  calc (1 + ‖y‖ ^ 2) ^ b * Real.exp (d * ‖y‖)
      ≤ ((2 : ℝ) ^ |b| * (1 + ‖x‖ ^ 2) ^ b * (1 + ‖y - x‖ ^ 2) ^ |b|) *
          (Real.exp (d * ‖x‖) * Real.exp (|d| * ‖y - x‖)) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = (2 : ℝ) ^ |b| * ((1 + ‖x‖ ^ 2) ^ b * Real.exp (d * ‖x‖)) *
          ((1 + ‖y - x‖ ^ 2) ^ |b| * Real.exp (|d| * ‖y - x‖)) := by ring

private lemma rpow_sq_mul_exp_le_exp (b d u : ℝ) (hu : 0 ≤ u) :
    (1 + u ^ 2) ^ |b| * Real.exp (|d| * u) ≤
      Real.exp ((2 * (Nat.ceil |b| : ℝ) + |d|) * u) := by
  let k : ℕ := Nat.ceil |b|
  have hk : |b| ≤ (k : ℝ) := Nat.le_ceil |b|
  have h1 : (1 + u ^ 2) ^ |b| ≤ (1 + u ^ 2) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg u]) hk
  have h2 : (1 + u ^ 2) ^ (k : ℝ) = (1 + u ^ 2) ^ k := Real.rpow_natCast _ k
  have h3 : (1 + u ^ 2) ^ k ≤ (Real.exp u) ^ (2 * k) := by
    have h1u : 1 + u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
    have hexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    calc (1 + u ^ 2) ^ k ≤ ((1 + u) ^ 2) ^ k := pow_le_pow_left₀ (by positivity) h1u k
      _ = (1 + u) ^ (2 * k) := by rw [← pow_mul]
      _ ≤ (Real.exp u) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hexp (2 * k)
  have h4 : (Real.exp u) ^ (2 * k) = Real.exp (2 * (k : ℝ) * u) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 + u ^ 2) ^ |b| * Real.exp (|d| * u)
      ≤ Real.exp (2 * (k : ℝ) * u) * Real.exp (|d| * u) :=
        mul_le_mul_of_nonneg_right (h1.trans (h2 ▸ h3.trans h4.le)) (Real.exp_pos _).le
    _ = Real.exp ((2 * (k : ℝ) + |d|) * u) := by rw [← Real.exp_add]; congr 1; ring

private lemma integrable_exp_linear_sub_gaussian (w : ℕ) (D₁ : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : RadialSpace w => Real.exp (D₁ * ‖u‖ - π * c * ‖u‖ ^ 2)) := by
  have hcomp : ∀ u : RadialSpace w,
      Real.exp (D₁ * ‖u‖ - π * c * ‖u‖ ^ 2) ≤
        Real.exp (D₁ ^ 2 / (2 * π * c)) * Real.exp (-π * (c / 2) * ‖u‖ ^ 2) := fun u => by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsq : 0 ≤ (π * c / 2) * (‖u‖ - D₁ / (π * c)) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    have hid : D₁ * ‖u‖ - π * c * ‖u‖ ^ 2 + (π * c / 2) * (‖u‖ - D₁ / (π * c)) ^ 2 =
        D₁ ^ 2 / (2 * π * c) + -π * (c / 2) * ‖u‖ ^ 2 := by
      have hpc : π * c ≠ 0 := (mul_pos Real.pi_pos hc).ne'
      field_simp; ring
    linarith
  have hg := (integral_exp_neg_pi_mul_norm_sq w (half_pos hc)).1.const_mul (Real.exp (D₁ ^ 2 / (2 * π * c)))
  refine hg.mono' (by fun_prop : Continuous fun u : RadialSpace w =>
      Real.exp (D₁ * ‖u‖ - π * c * ‖u‖ ^ 2)).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hcomp u

/-- Pointwise convergence `A_r h x → h x` as `r → 1⁻` for any continuous function `h` bounded
by a multiple of `euclideanWeight b d`. -/
theorem tendsto_mehlerMean_of_continuous_weight {w : ℕ} {h : RadialSpace w → ℝ}
    (hcont : Continuous h) {C b d : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, |h y| ≤ C * euclideanWeight b d y) (x : RadialSpace w) :
    Tendsto (fun r => mehlerMean w r h x) (𝓝[<] 1) (𝓝 (h x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (ε / (4 * (2 : ℝ) ^ w)) (by positivity)
  have hx_tend : Tendsto (fun r => h x * ((∫ y : RadialSpace w, mehlerKernel w r x y) - 1))
      (𝓝[<] 1) (𝓝 0) := by
    have hm_tend : Tendsto (fun r => (2 / (1 + r)) ^ (w : ℝ) *
        Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)) (𝓝[<] 1) (𝓝 1) := by
      have hdiv_cont : ContinuousAt (fun r : ℝ => 2 / (1 + r)) 1 :=
        continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
      have hexp_cont : ContinuousAt (fun r : ℝ => Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)) 1 :=
        Real.continuous_exp.continuousAt.comp
          (((continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).div
            (continuousAt_const.add continuousAt_id) (by norm_num))).mul continuousAt_const))
      have hbase : Tendsto (fun r : ℝ => (2 / (1 + r)) ^ (w : ℝ) *
          Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2)) (𝓝 1)
          (𝓝 ((2 / (1 + (1 : ℝ))) ^ (w : ℝ) * Real.exp (-π * ((1 - (1 : ℝ)) / (1 + (1 : ℝ))) * ‖x‖ ^ 2))) :=
        ((hdiv_cont.rpow continuousAt_const (Or.inl (by norm_num))).mul hexp_cont).tendsto
      have h1_val : (2 / (1 + (1 : ℝ))) ^ (w : ℝ) *
          Real.exp (-π * ((1 - (1 : ℝ)) / (1 + (1 : ℝ))) * ‖x‖ ^ 2) = 1 := by norm_num
      rw [h1_val] at hbase
      exact hbase.mono_left nhdsWithin_le_nhds
    have hint_eq : ∀ᶠ r in 𝓝[<] 1, (2 / (1 + r)) ^ (w : ℝ) *
        Real.exp (-π * ((1 - r) / (1 + r)) * ‖x‖ ^ 2) = ∫ y, mehlerKernel w r x y := by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r ⟨hr0, hr1⟩
      exact (integral_mehlerKernel w hr0.le hr1 x).2.symm
    have hm_tend' := hm_tend.congr' hint_eq
    have hsub := hm_tend'.sub_const (1 : ℝ)
    simp only [sub_self] at hsub
    simpa [mul_zero] using hsub.const_mul (h x)
  let D₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  have hint_tail : Integrable (fun u : RadialSpace w =>
      Real.exp (D₁ * ‖u‖ - π * (1 / 2 : ℝ) * ‖u‖ ^ 2)) :=
    integrable_exp_linear_sub_gaussian w D₁ (by norm_num)
  let I_tail : ℝ := ∫ u : RadialSpace w, Real.exp (D₁ * ‖u‖ - π * (1 / 2 : ℝ) * ‖u‖ ^ 2)
  have hI_tail_nn : 0 ≤ I_tail := integral_nonneg fun _ => (Real.exp_pos _).le
  have htail_const : 0 < (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) + 1 :=
    add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num) _).le)
      (euclideanWeight_pos b d x).le) (abs_nonneg _)) zero_lt_one
  let c_tail : ℝ := (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * (2 : ℝ) ^ w * I_tail + 1
  have hc_tail_pos : 0 < c_tail := by
    have h2 : 0 ≤ (2 : ℝ) ^ |b| := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hW : 0 ≤ euclideanWeight b d x := (euclideanWeight_pos b d x).le
    dsimp [c_tail]
    positivity
  obtain ⟨K_poly, hK_poly_pos, hK_poly⟩ :=
    pow_le_const_mul_exp_mul (by positivity : 0 < π * δ ^ 2 / 4) w
  have hr_tail : ∀ᶠ r in 𝓝[<] 1,
      c_tail * (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) < ε / 4 := by
    have hpow_lim : Tendsto (fun r : ℝ =>
        c_tail * (2 : ℝ) ^ w * K_poly * Real.exp (-(π * δ ^ 2 / 4) * (1 - r)⁻¹)) (𝓝[<] 1) (𝓝 0) := by
      have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝 0) := by
        have h : ContinuousAt (fun r : ℝ => 1 - r) 1 := continuousAt_const.sub continuousAt_id
        have h1 := h.tendsto
        rw [sub_self] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) (𝓝[<] 1) atTop :=
        tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsub
          (by filter_upwards [self_mem_nhdsWithin] with r hr; exact sub_pos.mpr hr))
      have hneg : Tendsto (fun r : ℝ => -(π * δ ^ 2 / 4) * (1 - r)⁻¹) (𝓝[<] 1) atBot := by
        convert (tendsto_neg_atTop_atBot.comp (hinv.const_mul_atTop (by positivity : 0 < π * δ ^ 2 / 4)))
          using 1
        ext r; dsimp [Function.comp_def]; ring
      simpa [mul_zero] using (Real.tendsto_exp_atBot.comp hneg).const_mul (c_tail * (2 : ℝ) ^ w * K_poly)
    filter_upwards [hpow_lim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4)),
        Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr_lt ⟨hr12, hr1⟩
    have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
    have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
    have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
    have hu_le := hK_poly (1 - r)⁻¹ (by positivity)
    have hrp : ((1 - r) / 2) ^ (-(w : ℝ)) = (2 : ℝ) ^ w * ((1 - r)⁻¹) ^ w := by
      rw [Real.rpow_neg h1r2_nn, Real.rpow_natCast, div_pow, inv_div, div_eq_mul_inv, inv_pow, mul_comm]
    have hexp_eq : Real.exp (-(π * δ ^ 2 / 4) * (1 - r)⁻¹) =
        Real.exp (π * δ ^ 2 / 4 * (1 - r)⁻¹) * Real.exp (-π * δ ^ 2 / (2 * (1 - r))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hbound : c_tail * (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) ≤
        c_tail * (2 : ℝ) ^ w * K_poly * Real.exp (-(π * δ ^ 2 / 4) * (1 - r)⁻¹) := by
      rw [hrp]
      calc c_tail * ((2 : ℝ) ^ w * ((1 - r)⁻¹) ^ w * Real.exp (-π * δ ^ 2 / (2 * (1 - r))))
          ≤ c_tail * ((2 : ℝ) ^ w * (K_poly * Real.exp (π * δ ^ 2 / 4 * (1 - r)⁻¹)) *
              Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hu_le (by positivity)) (Real.exp_pos _).le) hc_tail_pos.le
        _ = c_tail * (2 : ℝ) ^ w * K_poly *
              (Real.exp (π * δ ^ 2 / 4 * (1 - r)⁻¹) * Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) := by ring
        _ = c_tail * (2 : ℝ) ^ w * K_poly * Real.exp (-(π * δ ^ 2 / 4) * (1 - r)⁻¹) := by
            rw [hexp_eq]
    exact hbound.trans_lt hr_lt
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1),
      hx_tend.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 4)),
      hr_tail] with r ⟨hr12, hr1⟩ hrx hrtail
  have hr0 : 0 ≤ r := by linarith
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
  have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
  have h2b_nn : 0 ≤ (2 : ℝ) ^ |b| := (Real.rpow_pos_of_pos (by norm_num) _).le
  have h1r_le : 1 - r ≤ 1 := by linarith
  have hk_int := (integral_mehlerKernel w hr0 hr1 x).1
  have hW_dom : ∀ y : RadialSpace w, |h y| ≤ C * (2 : ℝ) ^ |b| * euclideanWeight b d x *
      Real.exp (D₁ * ‖y - x‖) := fun y => by
    have h1 := hb y
    have h2 := euclideanWeight_ratio_le b d x y
    have h3 := rpow_sq_mul_exp_le_exp b d ‖y - x‖ (norm_nonneg _)
    calc |h y| ≤ C * euclideanWeight b d y := h1
      _ ≤ C * ((2 : ℝ) ^ |b| * euclideanWeight b d x *
            ((1 + ‖y - x‖ ^ 2) ^ |b| * Real.exp (|d| * ‖y - x‖))) :=
          mul_le_mul_of_nonneg_left h2 hC
      _ ≤ C * ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h3 (mul_nonneg h2b_nn (euclideanWeight_pos b d x).le)) hC
      _ = C * (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖) := by ring
  have hk_h_int : Integrable (fun y => mehlerKernel w r x y * h y) := by
    have hmaj : Integrable (fun y => (C * (2 : ℝ) ^ |b| * euclideanWeight b d x) *
        ((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2)) := by
      have hg := (integrable_exp_linear_sub_gaussian w D₁ (one_div_pos.mpr h1r_pos)).comp_sub_right x
      have heq : (fun y : RadialSpace w =>
          (C * (2 : ℝ) ^ |b| * euclideanWeight b d x) * ((1 - r) / 2) ^ (-(w : ℝ)) *
            Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2)) =
          fun y => ((C * (2 : ℝ) ^ |b| * euclideanWeight b d x) * ((1 - r) / 2) ^ (-(w : ℝ))) *
            Real.exp (D₁ * ‖y - x‖ - π * (1 / (1 - r)) * ‖y - x‖ ^ 2) := by
        ext y; congr 2; ring
      rw [heq]
      exact hg.const_mul _
    refine hmaj.mono' ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
        |>.mul hcont).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
    have hker := mehlerKernel_le_half_gaussian w hr12.le hr1 x y
    rw [norm_sub_rev x y] at hker
    calc mehlerKernel w r x y * |h y|
        ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
            (C * (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) :=
          mul_le_mul hker (hW_dom y) (abs_nonneg _) (by positivity)
      _ = (C * (2 : ℝ) ^ |b| * euclideanWeight b d x) * ((1 - r) / 2) ^ (-(w : ℝ)) *
            Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2) := by
          rw [show (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
              (C * (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) =
              (C * (2 : ℝ) ^ |b| * euclideanWeight b d x) * ((1 - r) / 2) ^ (-(w : ℝ)) *
                (Real.exp (D₁ * ‖y - x‖) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) by ring]
          rw [← Real.exp_add]; congr 2; ring
  have hdiff_eq : mehlerMean w r h x - h x =
      (∫ y, mehlerKernel w r x y * (h y - h x)) +
        h x * ((∫ y, mehlerKernel w r x y) - 1) := by
    unfold mehlerMean
    have hmul : (fun y => mehlerKernel w r x y * (h y - h x)) =
        fun y => mehlerKernel w r x y * h y - mehlerKernel w r x y * h x := funext fun _ => mul_sub _ _ _
    rw [hmul, integral_sub hk_h_int (hk_int.mul_const _), integral_mul_const]
    ring
  have hdom_sub : Integrable (fun y => mehlerKernel w r x y * |h y - h x|) := by
    have hsub_int : Integrable (fun y => mehlerKernel w r x y * (h y - h x)) := by
      convert hk_h_int.sub (hk_int.mul_const (h x)) using 1
      ext y; simp [mul_sub]
    refine hsub_int.abs.congr (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
  have hin_le : ∫ y in Metric.ball x δ, mehlerKernel w r x y * |h y - h x| ≤ ε / 4 := by
    have hpt_in : ∀ y ∈ Metric.ball x δ,
        mehlerKernel w r x y * |h y - h x| ≤ (ε / (4 * (2 : ℝ) ^ w)) * mehlerKernel w r x y := by
      intro y hy
      rw [mul_comm (ε / _)]
      exact mul_le_mul_of_nonneg_left (hδ hy).le (mehlerKernel_nonneg w hr1 x y)
    have hint_in : IntegrableOn (fun y => (ε / (4 * (2 : ℝ) ^ w)) * mehlerKernel w r x y)
        (Metric.ball x δ) := (hk_int.const_mul _).integrableOn
    calc ∫ y in Metric.ball x δ, mehlerKernel w r x y * |h y - h x|
        ≤ ∫ y in Metric.ball x δ, (ε / (4 * (2 : ℝ) ^ w)) * mehlerKernel w r x y :=
          setIntegral_mono_on hdom_sub.integrableOn hint_in measurableSet_ball hpt_in
      _ ≤ ∫ y, (ε / (4 * (2 : ℝ) ^ w)) * mehlerKernel w r x y :=
          setIntegral_le_integral (hk_int.const_mul _)
            (Eventually.of_forall fun y => mul_nonneg (by positivity) (mehlerKernel_nonneg w hr1 x y))
      _ = (ε / (4 * (2 : ℝ) ^ w)) * ∫ y, mehlerKernel w r x y := integral_const_mul _ _
      _ ≤ (ε / (4 * (2 : ℝ) ^ w)) * (2 : ℝ) ^ w :=
          mul_le_mul_of_nonneg_left (integral_mehlerKernel_le w hr0 hr1 x) (by positivity)
      _ = ε / 4 := by field_simp
  have hout_le : ∫ y in (Metric.ball x δ)ᶜ, mehlerKernel w r x y * |h y - h x| ≤ ε / 4 := by
    have hW_nn : 0 ≤ euclideanWeight b d x := (euclideanWeight_pos b d x).le
    have hcoeff_part_nn : 0 ≤ C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x| :=
      add_nonneg (mul_nonneg (mul_nonneg hC h2b_nn) hW_nn) (abs_nonneg _)
    let coeff : ℝ := (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) *
      (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * δ ^ 2 / (2 * (1 - r))))
    have hcoeff_nn : 0 ≤ coeff :=
      mul_nonneg hcoeff_part_nn (mul_nonneg hrp_nn (Real.exp_pos _).le)
    have hD₁_nn : 0 ≤ D₁ := by dsimp [D₁]; positivity
    have hpt_out : ∀ y ∈ (Metric.ball x δ)ᶜ,
        mehlerKernel w r x y * |h y - h x| ≤
          coeff * Real.exp (D₁ * ‖y - x‖ - π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2) := by
      intro y hy
      have hδ_le : δ ≤ ‖y - x‖ := by
        simpa [Metric.mem_ball, dist_eq_norm, not_lt] using hy
      have hker := mehlerKernel_le_half_gaussian w hr12.le hr1 x y
      rw [norm_sub_rev x y] at hker
      have hexp_split : Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2) ≤
          Real.exp (-π * δ ^ 2 / (2 * (1 - r))) * Real.exp (-π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hsq1 : δ ^ 2 ≤ ‖y - x‖ ^ 2 := pow_le_pow_left₀ hδ_pos.le hδ_le 2
        have h1 : π * δ ^ 2 / (2 * (1 - r)) ≤ π / (2 * (1 - r)) * ‖y - x‖ ^ 2 := by
          have : π * δ ^ 2 ≤ π * ‖y - x‖ ^ 2 := mul_le_mul_of_nonneg_left hsq1 Real.pi_pos.le
          calc π * δ ^ 2 / (2 * (1 - r)) ≤ π * ‖y - x‖ ^ 2 / (2 * (1 - r)) :=
                div_le_div_of_nonneg_right this (by positivity)
            _ = π / (2 * (1 - r)) * ‖y - x‖ ^ 2 := by ring
        have h2 : π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2 ≤ π / (2 * (1 - r)) * ‖y - x‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [Real.pi_pos]
        have hsum := add_le_add h1 h2
        have halg : π / (2 * (1 - r)) * ‖y - x‖ ^ 2 + π / (2 * (1 - r)) * ‖y - x‖ ^ 2 =
            π / (1 - r) * ‖y - x‖ ^ 2 := by field_simp; ring
        have hsub := hsum.trans_eq halg
        calc -π / (1 - r) * ‖y - x‖ ^ 2 = -(π / (1 - r) * ‖y - x‖ ^ 2) := by ring
          _ ≤ -(π * δ ^ 2 / (2 * (1 - r)) + π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2) := neg_le_neg hsub
          _ = -π * δ ^ 2 / (2 * (1 - r)) + -π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by ring
      have hsub_le : |h y - h x| ≤
          (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * Real.exp (D₁ * ‖y - x‖) := by
        have h1e : 1 ≤ Real.exp (D₁ * ‖y - x‖) := Real.one_le_exp (mul_nonneg hD₁_nn (norm_nonneg _))
        calc |h y - h x| ≤ |h y| + |h x| := abs_sub _ _
          _ ≤ C * (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖) +
                |h x| * Real.exp (D₁ * ‖y - x‖) := by
              refine add_le_add (hW_dom y) ?_
              exact le_mul_of_one_le_right (abs_nonneg _) h1e
          _ = _ := by ring
      calc mehlerKernel w r x y * |h y - h x|
          ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * (Real.exp (-π * δ ^ 2 / (2 * (1 - r))) *
              Real.exp (-π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2))) *
              ((C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * Real.exp (D₁ * ‖y - x‖)) :=
            mul_le_mul (hker.trans (mul_le_mul_of_nonneg_left hexp_split hrp_nn))
              hsub_le (abs_nonneg _) (mul_nonneg hrp_nn (by positivity))
        _ = coeff * (Real.exp (D₁ * ‖y - x‖) * Real.exp (-π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2)) := by
            dsimp [coeff]; ring
        _ = coeff * Real.exp (D₁ * ‖y - x‖ - π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2) := by
            rw [← Real.exp_add]; congr 2; ring
    have hint_out : Integrable (fun y : RadialSpace w =>
        coeff * Real.exp (D₁ * ‖y - x‖ - π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2)) :=
      (hint_tail.comp_sub_right x).const_mul coeff
    calc ∫ y in (Metric.ball x δ)ᶜ, mehlerKernel w r x y * |h y - h x|
        ≤ ∫ y in (Metric.ball x δ)ᶜ,
            coeff * Real.exp (D₁ * ‖y - x‖ - π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2) :=
          setIntegral_mono_on hdom_sub.integrableOn hint_out.integrableOn
            measurableSet_ball.compl hpt_out
      _ ≤ ∫ y, coeff * Real.exp (D₁ * ‖y - x‖ - π * (1 / 2 : ℝ) * ‖y - x‖ ^ 2) :=
          setIntegral_le_integral hint_out
            (Eventually.of_forall fun _ => mul_nonneg hcoeff_nn (Real.exp_pos _).le)
      _ = coeff * I_tail := by
          rw [integral_const_mul]
          congr 1
          exact integral_sub_right_eq_self
            (fun u : RadialSpace w => Real.exp (D₁ * ‖u‖ - π * (1 / 2 : ℝ) * ‖u‖ ^ 2)) x
      _ ≤ c_tail * (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) := by
          dsimp [coeff, c_tail]
          have hI : (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * I_tail ≤
              (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * (2 : ℝ) ^ w * I_tail + 1 := by
            have h1w : (1 : ℝ) ≤ (2 : ℝ) ^ w := one_le_pow₀ (by norm_num)
            have hmul : (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * I_tail ≤
                ((C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * (2 : ℝ) ^ w) * I_tail := by
              refine mul_le_mul_of_nonneg_right ?_ hI_tail_nn
              exact le_mul_of_one_le_right hcoeff_part_nn h1w
            linarith
          calc (C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) *
                (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) * I_tail
              = ((C * (2 : ℝ) ^ |b| * euclideanWeight b d x + |h x|) * I_tail) *
                  (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * δ ^ 2 / (2 * (1 - r)))) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hI (mul_nonneg hrp_nn (Real.exp_pos _).le)
      _ ≤ ε / 4 := hrtail.le
  have hsplit_int : ∫ y, mehlerKernel w r x y * |h y - h x| =
      (∫ y in Metric.ball x δ, mehlerKernel w r x y * |h y - h x|) +
        (∫ y in (Metric.ball x δ)ᶜ, mehlerKernel w r x y * |h y - h x|) :=
    (integral_add_compl measurableSet_ball hdom_sub).symm
  have hnorm_int : |∫ y, mehlerKernel w r x y * (h y - h x)| ≤
      ∫ y, mehlerKernel w r x y * |h y - h x| := by
    calc |∫ y, mehlerKernel w r x y * (h y - h x)|
        = ‖∫ y, mehlerKernel w r x y * (h y - h x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖mehlerKernel w r x y * (h y - h x)‖ := norm_integral_le_integral_norm _
      _ = ∫ y, mehlerKernel w r x y * |h y - h x| := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
  have hrx_abs : |h x * ((∫ y, mehlerKernel w r x y) - 1)| < ε / 4 := by
    simpa [Real.dist_eq, sub_zero] using hrx
  rw [Real.dist_eq, hdiff_eq]
  calc |(∫ y, mehlerKernel w r x y * (h y - h x)) + h x * ((∫ y, mehlerKernel w r x y) - 1)|
      ≤ |∫ y, mehlerKernel w r x y * (h y - h x)| + |h x * ((∫ y, mehlerKernel w r x y) - 1)| :=
        abs_add_le _ _
    _ ≤ (∫ y, mehlerKernel w r x y * |h y - h x|) + |h x * ((∫ y, mehlerKernel w r x y) - 1)| :=
        add_le_add hnorm_int le_rfl
    _ < (ε / 4 + ε / 4) + ε / 4 := by
        rw [hsplit_int]
        exact add_lt_add_of_le_of_lt (add_le_add hin_le hout_le) hrx_abs
    _ < ε := by linarith

/-- Uniform Mehler stability of `euclideanWeight b d` for `r ∈ [1 / 2, 1)`:
`A_r W(x) ≤ C' W(x)`. -/
theorem mehlerMean_euclideanWeight_le (w : ℕ) (b d : ℝ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ {r : ℝ}, r ∈ Ico (1 / 2 : ℝ) 1 → ∀ x : RadialSpace w,
      mehlerMean w r (euclideanWeight b d) x ≤ C' * euclideanWeight b d x := by
  let D₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  have hD₁_nn : 0 ≤ D₁ := by dsimp [D₁]; positivity
  have hint_g := integrable_exp_linear_sub_gaussian w D₁ one_pos
  let I_g : ℝ := ∫ v : RadialSpace w, Real.exp (D₁ * ‖v‖ - π * 1 * ‖v‖ ^ 2)
  have hI_g_nn : 0 ≤ I_g := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨(2 : ℝ) ^ |b| * (2 : ℝ) ^ w * I_g + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
      (by positivity)) hI_g_nn) zero_lt_one, fun {r} ⟨hr12, hr1⟩ x => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
  have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
  have h2b_nn : 0 ≤ (2 : ℝ) ^ |b| := (Real.rpow_pos_of_pos (by norm_num) _).le
  have h1r_le : 1 - r ≤ 1 := by linarith
  let s : ℝ := Real.sqrt (1 - r)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h1r_pos
  have hs_le1 : s ≤ 1 := Real.sqrt_le_one.mpr h1r_le
  let bound : RadialSpace w → ℝ := fun y =>
    (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
      Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2)
  have hpt : ∀ y : RadialSpace w, mehlerKernel w r x y * euclideanWeight b d y ≤ bound y := fun y => by
    have hk := mehlerKernel_le_half_gaussian w hr12 hr1 x y
    rw [norm_sub_rev x y] at hk
    have hw := euclideanWeight_ratio_le b d x y
    have hexp := rpow_sq_mul_exp_le_exp b d ‖y - x‖ (norm_nonneg _)
    have hw' : euclideanWeight b d y ≤ (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖) :=
      hw.trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg h2b_nn (euclideanWeight_pos b d x).le))
    calc mehlerKernel w r x y * euclideanWeight b d y
        ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
            ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) :=
          mul_le_mul hk hw' (euclideanWeight_pos b d y).le (by positivity)
      _ = bound y := by
          dsimp [bound]
          rw [show (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
              ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) =
              (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
                (Real.exp (D₁ * ‖y - x‖) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) by ring]
          rw [← Real.exp_add]; congr 2; ring
  have hbound_int : Integrable bound := by
    have h1 := (integrable_exp_linear_sub_gaussian w D₁ (one_div_pos.mpr h1r_pos)).comp_sub_right x
    have heq : bound = fun y => ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
        Real.exp (D₁ * ‖y - x‖ - π * (1 / (1 - r)) * ‖y - x‖ ^ 2) := by
      ext y; dsimp [bound]; congr 2; ring
    rw [heq]; exact h1.const_mul _
  have hscale : ∫ u : RadialSpace w, Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2) ≤
      (1 - r) ^ (w : ℝ) * I_g := by
    have hcomp := Measure.integral_comp_smul (volume : Measure (RadialSpace w))
      (fun u : RadialSpace w => Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2)) s
    rw [finrank_euclideanSpace_fin] at hcomp
    have hs_pow : s ^ (2 * w) = (1 - r) ^ (w : ℝ) := by
      dsimp [s]
      rw [pow_mul, Real.sq_sqrt h1r_pos.le, Real.rpow_natCast]
    rw [hs_pow, abs_of_pos (inv_pos.mpr (Real.rpow_pos_of_pos h1r_pos w)), smul_eq_mul] at hcomp
    have hpt_v : ∀ v : RadialSpace w,
        Real.exp (D₁ * ‖s • v‖ - π / (1 - r) * ‖s • v‖ ^ 2) ≤
          Real.exp (D₁ * ‖v‖ - π * 1 * ‖v‖ ^ 2) := fun v => by
      refine Real.exp_le_exp.mpr ?_
      rw [norm_smul, Real.norm_of_nonneg hs_pos.le]
      have h1 : D₁ * (s * ‖v‖) ≤ D₁ * ‖v‖ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg v) hs_le1) hD₁_nn
      have h2 : π / (1 - r) * (s * ‖v‖) ^ 2 = π * 1 * ‖v‖ ^ 2 := by
        have hsq : s ^ 2 = 1 - r := Real.sq_sqrt h1r_pos.le
        rw [mul_pow, hsq]; field_simp
      linarith
    have hint_lhs : Integrable (fun v : RadialSpace w =>
        Real.exp (D₁ * ‖s • v‖ - π / (1 - r) * ‖s • v‖ ^ 2)) := by
      refine hint_g.mono' (by fun_prop : Continuous fun v : RadialSpace w =>
          Real.exp (D₁ * ‖s • v‖ - π / (1 - r) * ‖s • v‖ ^ 2)).aestronglyMeasurable ?_
      filter_upwards with v
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hpt_v v
    have hint_le : ∫ v : RadialSpace w, Real.exp (D₁ * ‖s • v‖ - π / (1 - r) * ‖s • v‖ ^ 2) ≤ I_g :=
      integral_mono hint_lhs hint_g hpt_v
    have heq_int : ∫ u : RadialSpace w, Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2) =
        (1 - r) ^ (w : ℝ) * ∫ v : RadialSpace w, Real.exp (D₁ * ‖s • v‖ - π / (1 - r) * ‖s • v‖ ^ 2) := by
      have h := congrArg (fun z => (1 - r) ^ (w : ℝ) * z) hcomp.symm
      rwa [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1r_pos w).ne', one_mul] at h
    rw [heq_int]
    exact mul_le_mul_of_nonneg_left hint_le (Real.rpow_pos_of_pos h1r_pos w).le
  have hint_lhs : ∫ y, mehlerKernel w r x y * euclideanWeight b d y ≤ ∫ y, bound y :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun y => mul_nonneg (mehlerKernel_nonneg w hr1 x y)
        (euclideanWeight_pos b d y).le) hbound_int (Eventually.of_forall hpt)
  have hbound_eval : ∫ y, bound y =
      ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
        ∫ u : RadialSpace w, Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2) := by
    change ∫ y, ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
      (fun u : RadialSpace w => Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2)) (y - x) = _
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun u : RadialSpace w => Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2)) x]
  have hrp_cancel : ((1 - r) / 2) ^ (-(w : ℝ)) * (1 - r) ^ (w : ℝ) = (2 : ℝ) ^ w := by
    rw [Real.rpow_neg h1r2_nn, Real.rpow_natCast, Real.rpow_natCast, div_pow, inv_div]
    field_simp
  calc mehlerMean w r (euclideanWeight b d) x
      ≤ ∫ y, bound y := hint_lhs
    _ = ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
          ∫ u : RadialSpace w, Real.exp (D₁ * ‖u‖ - π / (1 - r) * ‖u‖ ^ 2) := hbound_eval
    _ ≤ ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
          ((1 - r) ^ (w : ℝ) * I_g) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (mul_nonneg h2b_nn (euclideanWeight_pos b d x).le) hrp_nn)
    _ = ((2 : ℝ) ^ |b| * (((1 - r) / 2) ^ (-(w : ℝ)) * (1 - r) ^ (w : ℝ)) * I_g) *
          euclideanWeight b d x := by ring
    _ = ((2 : ℝ) ^ |b| * (2 : ℝ) ^ w * I_g) * euclideanWeight b d x := by rw [hrp_cancel]
    _ ≤ ((2 : ℝ) ^ |b| * (2 : ℝ) ^ w * I_g + 1) * euclideanWeight b d x :=
        mul_le_mul_of_nonneg_right (by linarith) (euclideanWeight_pos b d x).le

/-- Uniform Gaussian domination of `A_r f` for a continuous nonnegative function `f` supported in a
closed ball `‖y‖ ≤ R` and `r ∈ [1 / 2, 1)`:
`0 ≤ A_r f(x) ≤ C * exp(-π / 8 * ‖x‖²)`. -/
lemma mehlerMean_compactSupport_gaussian_ub {w : ℕ} {f : RadialSpace w → ℝ}
    (hf_cont : Continuous f) {R B : ℝ} (_hR : 0 ≤ R) (hB : 0 ≤ B)
    (hf_nn : ∀ y, 0 ≤ f y) (hf_le : ∀ y, f y ≤ B) (hf_supp : ∀ y, R < ‖y‖ → f y = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, r ∈ Ico (1 / 2 : ℝ) 1 → ∀ x : RadialSpace w,
      0 ≤ mehlerMean w r f x ∧ mehlerMean w r f x ≤ C * Real.exp (-π / 8 * ‖x‖ ^ 2) := by
  let R₀ : ℝ := max 1 (2 * R)
  have hR₀_ge1 : 1 ≤ R₀ := le_max_left _ _
  obtain ⟨K_poly, hK_poly_pos, hK_poly⟩ :=
    pow_le_const_mul_exp_mul (by positivity : 0 < π / 8) w
  let volR : ℝ := (volume : Measure (RadialSpace w)).real (Metric.closedBall (0 : RadialSpace w) R)
  have hvol_nn : 0 ≤ volR := ENNReal.toReal_nonneg
  let C_in : ℝ := B * (2 : ℝ) ^ w * Real.exp (π / 8 * R₀ ^ 2) + 1
  let C_out : ℝ := B * (2 : ℝ) ^ w * K_poly * volR + 1
  let C : ℝ := max C_in C_out
  refine ⟨C, lt_of_lt_of_le (by positivity : 0 < C_in) (le_max_left _ _), fun {r} ⟨hr12, hr1⟩ x => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  have hk_int := (integral_mehlerKernel w hr0 hr1 x).1
  have hf_int : Integrable (fun y => mehlerKernel w r x y * f y) := by
    refine (hk_int.const_mul B).mono'
      ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
        |>.mul hf_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg w hr1 x y) (hf_nn y))]
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left (hf_le y) (mehlerKernel_nonneg w hr1 x y)
  refine ⟨integral_nonneg fun y => mul_nonneg (mehlerKernel_nonneg w hr1 x y) (hf_nn y), ?_⟩
  rcases le_or_gt ‖x‖ R₀ with hx_in | hx_out
  · have hin : mehlerMean w r f x ≤ B * (2 : ℝ) ^ w := by
      have hle : ∀ y, mehlerKernel w r x y * f y ≤ B * mehlerKernel w r x y := fun y => by
        rw [mul_comm B]
        exact mul_le_mul_of_nonneg_left (hf_le y) (mehlerKernel_nonneg w hr1 x y)
      calc mehlerMean w r f x ≤ ∫ y, B * mehlerKernel w r x y :=
            integral_mono hf_int (hk_int.const_mul B) hle
        _ = B * ∫ y, mehlerKernel w r x y := integral_const_mul _ _
        _ ≤ B * (2 : ℝ) ^ w := mul_le_mul_of_nonneg_left (integral_mehlerKernel_le w hr0 hr1 x) hB
    have hexp_ge : Real.exp (-π / 8 * R₀ ^ 2) ≤ Real.exp (-π / 8 * ‖x‖ ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have hsq : ‖x‖ ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx_in 2
      nlinarith [Real.pi_pos]
    calc mehlerMean w r f x ≤ B * (2 : ℝ) ^ w := hin
      _ = (B * (2 : ℝ) ^ w * Real.exp (π / 8 * R₀ ^ 2)) * Real.exp (-π / 8 * R₀ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add, show π / 8 * R₀ ^ 2 + -π / 8 * R₀ ^ 2 = 0 by ring,
            Real.exp_zero, mul_one]
      _ ≤ C_in * Real.exp (-π / 8 * ‖x‖ ^ 2) :=
          mul_le_mul (by linarith [le_refl C_in]) hexp_ge (Real.exp_pos _).le (by positivity)
      _ ≤ C * Real.exp (-π / 8 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have hx_ge1 : 1 ≤ ‖x‖ := le_of_lt (lt_of_le_of_lt hR₀_ge1 hx_out)
    have hx_gt_2R : 2 * R < ‖x‖ := lt_of_le_of_lt (le_max_right _ _) hx_out
    have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
    have h1r_le : 1 - r ≤ 1 := by linarith
    let coef_out : ℝ := B * (2 : ℝ) ^ w * K_poly * Real.exp (-π / 8 * ‖x‖ ^ 2)
    have hpt_out : ∀ y : RadialSpace w,
        mehlerKernel w r x y * f y ≤
          Set.indicator (Metric.closedBall (0 : RadialSpace w) R) (fun _ => coef_out) y := by
      intro y
      by_cases hy : y ∈ Metric.closedBall (0 : RadialSpace w) R
      · rw [Set.indicator_of_mem hy]
        have hy_le : ‖y‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
        have hxy_ge : ‖x‖ / 2 ≤ ‖x - y‖ := by
          have htri := norm_sub_norm_le x y
          linarith
        have hxy_sq : ‖x‖ ^ 2 / 4 ≤ ‖x - y‖ ^ 2 := by
          have := pow_le_pow_left₀ (by positivity : 0 ≤ ‖x‖ / 2) hxy_ge 2
          linarith [this]
        have hker := mehlerKernel_le_half_gaussian w hr12 hr1 x y
        have hexp_le : Real.exp (-π / (1 - r) * ‖x - y‖ ^ 2) ≤
            Real.exp (-π * ‖x‖ ^ 2 / (8 * (1 - r))) * Real.exp (-π / 8 * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have h1 : π * ‖x‖ ^ 2 / (8 * (1 - r)) ≤ π / (2 * (1 - r)) * ‖x - y‖ ^ 2 := by
            have hmul := mul_le_mul_of_nonneg_left hxy_sq (by positivity : 0 ≤ π / (2 * (1 - r)))
            calc π * ‖x‖ ^ 2 / (8 * (1 - r)) = π / (2 * (1 - r)) * (‖x‖ ^ 2 / 4) := by
                  field_simp; ring
              _ ≤ π / (2 * (1 - r)) * ‖x - y‖ ^ 2 := hmul
          have h2 : π / 8 * ‖x‖ ^ 2 ≤ π / (2 * (1 - r)) * ‖x - y‖ ^ 2 := by
            have hinv : 1 / 2 ≤ 1 / (2 * (1 - r)) := by
              rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
            calc π / 8 * ‖x‖ ^ 2 = (π * (1 / 2)) * (‖x‖ ^ 2 / 4) := by ring
              _ ≤ (π * (1 / (2 * (1 - r)))) * ‖x - y‖ ^ 2 :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hinv Real.pi_pos.le) hxy_sq
                    (by positivity) (by positivity)
              _ = π / (2 * (1 - r)) * ‖x - y‖ ^ 2 := by field_simp
          have hsum := add_le_add h1 h2
          have halg : π / (2 * (1 - r)) * ‖x - y‖ ^ 2 + π / (2 * (1 - r)) * ‖x - y‖ ^ 2 =
              π / (1 - r) * ‖x - y‖ ^ 2 := by field_simp; ring
          have hsub : π * ‖x‖ ^ 2 / (8 * (1 - r)) + π / 8 * ‖x‖ ^ 2 ≤ π / (1 - r) * ‖x - y‖ ^ 2 :=
            hsum.trans_eq halg
          calc -π / (1 - r) * ‖x - y‖ ^ 2 = -(π / (1 - r) * ‖x - y‖ ^ 2) := by ring
            _ ≤ -(π * ‖x‖ ^ 2 / (8 * (1 - r)) + π / 8 * ‖x‖ ^ 2) := neg_le_neg hsub
            _ = -π * ‖x‖ ^ 2 / (8 * (1 - r)) + -π / 8 * ‖x‖ ^ 2 := by ring
        have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
        have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
        have hpoly : ((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * ‖x‖ ^ 2 / (8 * (1 - r))) ≤
            (2 : ℝ) ^ w * K_poly := by
          have hrp : ((1 - r) / 2) ^ (-(w : ℝ)) = (2 : ℝ) ^ w * ((1 - r)⁻¹) ^ w := by
            rw [Real.rpow_neg h1r2_nn, Real.rpow_natCast, div_pow, inv_div, div_eq_mul_inv,
              inv_pow, mul_comm]
          have hx_sq1 : 1 ≤ ‖x‖ ^ 2 := one_le_pow₀ hx_ge1
          have hexp_inv : Real.exp (-π * ‖x‖ ^ 2 / (8 * (1 - r))) ≤
              Real.exp (-(π / 8) * (1 - r)⁻¹) := by
            refine Real.exp_le_exp.mpr ?_
            have hmul : (π / 8) * (1 - r)⁻¹ ≤ π * ‖x‖ ^ 2 / (8 * (1 - r)) := by
              have := mul_le_mul_of_nonneg_left hx_sq1 (by positivity : 0 ≤ (π / 8) * (1 - r)⁻¹)
              calc (π / 8) * (1 - r)⁻¹ = (π / 8) * (1 - r)⁻¹ * 1 := by ring
                _ ≤ (π / 8) * (1 - r)⁻¹ * ‖x‖ ^ 2 := this
                _ = π * ‖x‖ ^ 2 / (8 * (1 - r)) := by field_simp
            linarith [show -(π / 8) * (1 - r)⁻¹ = -((π / 8) * (1 - r)⁻¹) by ring,
              show -π * ‖x‖ ^ 2 / (8 * (1 - r)) = -(π * ‖x‖ ^ 2 / (8 * (1 - r))) by ring]
          have hu_le := hK_poly (1 - r)⁻¹ (by positivity)
          have hcancel : Real.exp ((π / 8) * (1 - r)⁻¹) * Real.exp (-(π / 8) * (1 - r)⁻¹) = 1 := by
            rw [← Real.exp_add]; simp
          rw [hrp]
          calc (2 : ℝ) ^ w * ((1 - r)⁻¹) ^ w * Real.exp (-π * ‖x‖ ^ 2 / (8 * (1 - r)))
              ≤ (2 : ℝ) ^ w * (K_poly * Real.exp ((π / 8) * (1 - r)⁻¹)) *
                  Real.exp (-(π / 8) * (1 - r)⁻¹) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hu_le (by positivity)) hexp_inv
                  (Real.exp_pos _).le (by positivity)
            _ = (2 : ℝ) ^ w * K_poly *
                  (Real.exp ((π / 8) * (1 - r)⁻¹) * Real.exp (-(π / 8) * (1 - r)⁻¹)) := by ring
            _ = (2 : ℝ) ^ w * K_poly := by rw [hcancel, mul_one]
        calc mehlerKernel w r x y * f y
            ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * (Real.exp (-π * ‖x‖ ^ 2 / (8 * (1 - r))) *
                Real.exp (-π / 8 * ‖x‖ ^ 2))) * B :=
              mul_le_mul (hker.trans (mul_le_mul_of_nonneg_left hexp_le hrp_nn))
                (hf_le y) (hf_nn y) (by positivity)
          _ = B * (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π * ‖x‖ ^ 2 / (8 * (1 - r)))) *
                Real.exp (-π / 8 * ‖x‖ ^ 2) := by ring
          _ ≤ B * ((2 : ℝ) ^ w * K_poly) * Real.exp (-π / 8 * ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hB) (Real.exp_pos _).le
          _ = coef_out := by dsimp [coef_out]; ring
      · rw [Set.indicator_of_notMem hy]
        have hy_gt : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
        rw [hf_supp y hy_gt, mul_zero]
    have hind_int : Integrable (Set.indicator (Metric.closedBall (0 : RadialSpace w) R)
        (fun _ => coef_out)) :=
      (integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const (C := coef_out) (hs := measure_closedBall_lt_top.ne))
    calc mehlerMean w r f x
        ≤ ∫ y, Set.indicator (Metric.closedBall (0 : RadialSpace w) R) (fun _ => coef_out) y :=
          integral_mono hf_int hind_int hpt_out
      _ = volR * coef_out := by
          rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul]
      _ = (B * (2 : ℝ) ^ w * K_poly * volR) * Real.exp (-π / 8 * ‖x‖ ^ 2) := by
          dsimp [coef_out]; ring
      _ ≤ C_out * Real.exp (-π / 8 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith [le_refl C_out]) (Real.exp_pos _).le
      _ ≤ C * Real.exp (-π / 8 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Unproved analytic input from Lemma FW-A (`crossing_sum_rule.tex`, lines 14–24 & 33–55):
completeness of the radial Laguerre orthonormal basis in `L²(ℝ^{2w})` and Cauchy-bound series
interchange imply that thermal crossing `∫ Ξ_β dν = ∫ Ξ_β dρ` for all `β > 0` passes to
`∫ A_r f dν = ∫ A_r f dρ` (`0 < r < 1`) for every bounded continuous `L²` Fourier-odd radial test
`f(x) = g(‖x‖² / 2)`. -/
def MehlerOddMomentInput (w : ℕ) : Prop :=
  ∀ (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ],
    (∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν) →
    (∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ) →
    (∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ) →
    ∀ {g : ℝ → ℝ},
      ContinuousOn g (Ici 0) →
      Integrable (radialLift w g) →
      𝓕 (radialLift w g) = -(radialLift w g) →
      ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 1 →
        ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν =
          ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ

/-- Non-vacuity witness for `MehlerOddMomentInput`: equality of Mehler means holds on the diagonal
measure pair `ν = ρ = volume` (Gaussian measure or Lebesgue measure). -/
theorem mehlerOddMomentInput_nonvacuous (w : ℕ) :
    ∃ (ν ρ : Measure (RadialSpace w)) (_ : SigmaFinite ν) (_ : SigmaFinite ρ),
      (∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν) ∧
      (∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ) ∧
      (∀ {β : ℝ}, 0 < β →
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
          ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ) ∧
      ∀ {g : ℝ → ℝ},
        ContinuousOn g (Ici 0) →
        Integrable (radialLift w g) →
        𝓕 (radialLift w g) = -(radialLift w g) →
        ∀ {r : ℝ}, r ∈ Ioo (0 : ℝ) 1 →
          ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν =
            ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ := by
  refine ⟨volume, volume, inferInstance, inferInstance, ?_, ?_, fun {_} _ => rfl,
    fun {_} _ _ _ {_} _ => rfl⟩
  · intro ε hε
    simpa [mul_comm π (ε / π), mul_div_cancel₀ _ Real.pi_pos.ne'] using
      (integral_exp_neg_pi_mul_norm_sq w (div_pos hε Real.pi_pos)).1
  · intro ε hε
    simpa [mul_comm π (ε / π), mul_div_cancel₀ _ Real.pi_pos.ne'] using
      (integral_exp_neg_pi_mul_norm_sq w (div_pos hε Real.pi_pos)).1

/-- Any Fourier-odd `L¹` radial function `radialLift w g` is bounded and continuous everywhere
on `ℝ^{2w}`, with `‖radialLift w g x‖ ≤ ∫ y, ‖radialLift w g y‖`. -/
lemma radialLift_bounded_continuous_of_fourier_odd {w : ℕ} {g : ℝ → ℝ}
    (hint : Integrable (radialLift w g)) (hodd : 𝓕 (radialLift w g) = -(radialLift w g)) :
    Continuous (radialLiftReal w g) ∧
      ∀ x : RadialSpace w, |radialLiftReal w g x| ≤ ∫ y : RadialSpace w, ‖radialLift w g y‖ := by
  have hf_eq : ∀ x : RadialSpace w, radialLift w g x = -(𝓕 (radialLift w g) x) := fun x => by
    rw [hodd]; simp
  have hcontC : Continuous (radialLift w g) := by
    have heq : radialLift w g = fun x => -(𝓕 (radialLift w g) x) := funext hf_eq
    rw [heq]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hint).neg
  have hcontR : Continuous (radialLiftReal w g) := by
    have heq : radialLiftReal w g = fun x => (radialLift w g x).re := funext fun x => by
      rw [radialLift_eq_ofReal, Complex.ofReal_re]
    rw [heq]
    exact Complex.continuous_re.comp hcontC
  refine ⟨hcontR, fun x => ?_⟩
  have hnorm : |radialLiftReal w g x| = ‖radialLift w g x‖ := by
    rw [radialLift_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hf_eq x, norm_neg]
  exact Real.norm_fourier_le_integral_norm _ x

/-- Continuity of `A_r f` for continuous bounded `f` when `0 ≤ r < 1`. -/
lemma continuous_mehlerMean_of_bounded {w : ℕ} {f : RadialSpace w → ℝ}
    (hf_cont : Continuous f) {B : ℝ} (hf_bd : ∀ x, |f x| ≤ B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun x => mehlerMean w r f x) := by
  have hB_nn : 0 ≤ B := (abs_nonneg _).trans (hf_bd 0)
  have hk_int : ∀ x, Integrable (fun y => mehlerKernel w r x y * f y) := fun x =>
    ((integral_mehlerKernel w hr0 hr1 x).1.const_mul B).mono'
      ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
        |>.mul hf_cont).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm B]
        exact mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y))
  have h1sqr_pos : 0 < (1 - Real.sqrt r) ^ 2 / (1 - r) := by
    have hsr_lt : Real.sqrt r < 1 := by
      calc Real.sqrt r < Real.sqrt 1 := Real.sqrt_lt_sqrt hr0 hr1
        _ = 1 := Real.sqrt_one
    exact div_pos (sq_pos_of_pos (sub_pos.mpr hsr_lt)) (sub_pos.mpr hr1)
  let C_bd : ℝ := B * ((1 - r) / 2) ^ (-(w : ℝ))
  let g_dom : RadialSpace w → ℝ := fun y =>
    C_bd * Real.exp (-π * ((1 - Real.sqrt r) ^ 2 / (1 - r)) * ‖y‖ ^ 2)
  have hg_dom_int : Integrable g_dom :=
    (integral_exp_neg_pi_mul_norm_sq w h1sqr_pos).1.const_mul C_bd
  refine continuous_of_dominated (bound := g_dom) (fun x => (hk_int x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun y => ?_) hg_dom_int ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
    have hk_bd : mehlerKernel w r x y ≤
        ((1 - r) / 2) ^ (-(w : ℝ)) *
          Real.exp (-π * ((1 - Real.sqrt r) ^ 2 / (1 - r)) * ‖y‖ ^ 2) := by
      unfold mehlerKernel
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by linarith) _)
      rw [mehlerKernel_quad_identity hr0 x y]
      have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
      have hge : (1 - Real.sqrt r) ^ 2 * ‖y‖ ^ 2 ≤
          (1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2 := by
        have h1 : 0 ≤ (1 - Real.sqrt r) ^ 2 * ‖x‖ ^ 2 := by positivity
        have h2 : 0 ≤ 2 * Real.sqrt r * ‖x - y‖ ^ 2 := by positivity
        linarith
      have hdiv := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hge Real.pi_pos.le) h1r_pos.le
      calc -π * ((1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2) / (1 - r)
          = -(π * ((1 - Real.sqrt r) ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 2 * Real.sqrt r * ‖x - y‖ ^ 2) / (1 - r)) := by ring
        _ ≤ -(π * ((1 - Real.sqrt r) ^ 2 * ‖y‖ ^ 2) / (1 - r)) := neg_le_neg hdiv
        _ = -π * ((1 - Real.sqrt r) ^ 2 / (1 - r)) * ‖y‖ ^ 2 := by ring
    calc mehlerKernel w r x y * |f y| ≤ mehlerKernel w r x y * B :=
          mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y)
      _ ≤ (((1 - r) / 2) ^ (-(w : ℝ)) *
            Real.exp (-π * ((1 - Real.sqrt r) ^ 2 / (1 - r)) * ‖y‖ ^ 2)) * B :=
          mul_le_mul_of_nonneg_right hk_bd hB_nn
      _ = g_dom y := by dsimp [g_dom, C_bd]; ring
  · exact Eventually.of_forall fun y =>
      ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_id continuous_const)).mul
        continuous_const

/-- Gaussian integrability of `A_r f` against any Gaussian-integrating measure (`0 ≤ r < 1`)
for bounded `f`. -/
lemma integrable_mehlerMean_of_bounded {w : ℕ} {ν : Measure (RadialSpace w)}
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    {f : RadialSpace w → ℝ} (hf_cont : Continuous f) {B : ℝ} (hf_bd : ∀ x, |f x| ≤ B)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun x => mehlerMean w r f x) ν := by
  have hk_int : ∀ x, Integrable (fun y => mehlerKernel w r x y * f y) := fun x =>
    ((integral_mehlerKernel w hr0 hr1 x).1.const_mul B).mono'
      ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
        |>.mul hf_cont).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm B]
        exact mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y))
  have hB_nn : 0 ≤ B := (abs_nonneg _).trans (hf_bd 0)
  have hpt : ∀ x, ‖mehlerMean w r f x‖ ≤
      (B * (2 / (1 + r)) ^ (w : ℝ)) * Real.exp (-(π * ((1 - r) / (1 + r))) * ‖x‖ ^ 2) := fun x => by
    calc ‖mehlerMean w r f x‖ ≤ ∫ y, ‖mehlerKernel w r x y * f y‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ y, mehlerKernel w r x y * |f y| := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
      _ ≤ ∫ y, B * mehlerKernel w r x y :=
          integral_mono ((hk_int x).abs.congr (Eventually.of_forall fun y => by
            dsimp only
            rw [abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]))
            ((integral_mehlerKernel w hr0 hr1 x).1.const_mul B)
            (fun y => by rw [mul_comm B]; exact mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y))
      _ = B * ∫ y, mehlerKernel w r x y := integral_const_mul _ _
      _ = (B * (2 / (1 + r)) ^ (w : ℝ)) * Real.exp (-(π * ((1 - r) / (1 + r))) * ‖x‖ ^ 2) := by
          rw [(integral_mehlerKernel w hr0 hr1 x).2]
          ring_nf
  have hmeas : AEStronglyMeasurable (fun x => mehlerMean w r f x) ν :=
    (continuous_mehlerMean_of_bounded hf_cont hf_bd hr0 hr1).aestronglyMeasurable
  have hε : 0 < π * ((1 - r) / (1 + r)) := mul_pos Real.pi_pos (div_pos (sub_pos.mpr hr1) (by linarith))
  exact ((hν_gauss hε).const_mul (B * (2 / (1 + r)) ^ (w : ℝ))).mono' hmeas (Eventually.of_forall hpt)

/-- Lemma FW-A (1): restatement via `MehlerOddMomentInput` for radial `TestClass` elements. -/
theorem lemma_fwA_part1 {w : ℕ} (hMehler : MehlerOddMomentInput w)
    (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ]
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    (hρ_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ)
    (h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun x => mehlerMean w r (radialLiftReal w g) x) ν ∧
      Integrable (fun x => mehlerMean w r (radialLiftReal w g) x) ρ ∧
      ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ν =
        ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ := by
  obtain ⟨hf_cont, hf_bd⟩ := radialLift_bounded_continuous_of_fourier_odd hg_int hg_odd
  exact ⟨integrable_mehlerMean_of_bounded hν_gauss hf_cont hf_bd hr.1.le hr.2,
    integrable_mehlerMean_of_bounded hρ_gauss hf_cont hf_bd hr.1.le hr.2,
    hMehler ν ρ hν_gauss hρ_gauss h_thermal hg_cont hg_int hg_odd hr⟩

/-- Lemma FW-A (2) (`crossing_sum_rule.tex`, `fw:abel`): one-sided Fatou crossing bound
`∫ |f| dν < ∞` and `∫ f dν ≤ ∫ f dρ` when `f_-` is compactly supported and
`∫ A_r f dρ → ∫ f dρ`. -/
theorem lemma_fwA_part2 {w : ℕ} (hMehler : MehlerOddMomentInput w)
    (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ]
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    (hρ_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ)
    (h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g))
    (_hf_rho : Integrable (radialLiftReal w g) ρ)
    {R : ℝ} (hR : 0 ≤ R) (hneg_supp : ∀ y : RadialSpace w, R < ‖y‖ → max (-radialLiftReal w g y) 0 = 0)
    (htend_rho : Tendsto (fun r => ∫ x : RadialSpace w, mehlerMean w r (radialLiftReal w g) x ∂ρ)
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace w, radialLiftReal w g x ∂ρ))) :
    Integrable (radialLiftReal w g) ν ∧
      ∫ x : RadialSpace w, radialLiftReal w g x ∂ν ≤
        ∫ x : RadialSpace w, radialLiftReal w g x ∂ρ := by
  let f : RadialSpace w → ℝ := radialLiftReal w g
  obtain ⟨hf_cont, hf_bd⟩ := radialLift_bounded_continuous_of_fourier_odd hg_int hg_odd
  let B : ℝ := ∫ y : RadialSpace w, ‖radialLift w g y‖
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  let fPlus : RadialSpace w → ℝ := fun x => max (f x) 0
  let fMinus : RadialSpace w → ℝ := fun x => max (-f x) 0
  have hf_split : ∀ x, f x = fPlus x - fMinus x := fun x => by
    dsimp [fPlus, fMinus]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hfPlus_eq : ∀ x, fPlus x = f x + fMinus x := fun x => by linarith [hf_split x]
  have hfPlus_nn : ∀ x, 0 ≤ fPlus x := fun x => le_max_right _ _
  have hfMinus_nn : ∀ x, 0 ≤ fMinus x := fun x => le_max_right _ _
  have hfMinus_cont : Continuous fMinus := (hf_cont.neg).max continuous_const
  have hfPlus_cont : Continuous fPlus := hf_cont.max continuous_const
  have hfMinus_bd : ∀ x, fMinus x ≤ B := fun x => by
    dsimp [fMinus]; exact max_le ((neg_le_abs _).trans (hf_bd x)) hB_nn
  have hfMinus_abs_bd : ∀ x, |fMinus x| ≤ B := fun x => by
    rw [abs_of_nonneg (hfMinus_nn x)]; exact hfMinus_bd x
  have hfMinus_int_nu : Integrable fMinus ν := by
    have hpt : ∀ x : RadialSpace w, ‖fMinus x‖ ≤ (B * Real.exp (R ^ 2)) * Real.exp (-1 * ‖x‖ ^ 2) := by
      intro x
      rw [Real.norm_of_nonneg (hfMinus_nn x)]
      rcases le_or_gt ‖x‖ R with hx | hx
      · have h1 : 1 ≤ Real.exp (R ^ 2) * Real.exp (-1 * ‖x‖ ^ 2) := by
          rw [← Real.exp_add]
          have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
          exact Real.one_le_exp (by linarith)
        calc fMinus x ≤ B := hfMinus_bd x
          _ ≤ B * (Real.exp (R ^ 2) * Real.exp (-1 * ‖x‖ ^ 2)) := le_mul_of_one_le_right hB_nn h1
          _ = (B * Real.exp (R ^ 2)) * Real.exp (-1 * ‖x‖ ^ 2) := by ring
      · dsimp [fMinus]; rw [hneg_supp x hx]; positivity
    exact ((hν_gauss one_pos).const_mul (B * Real.exp (R ^ 2))).mono' hfMinus_cont.aestronglyMeasurable
      (Eventually.of_forall hpt)
  obtain ⟨C_neg, hC_neg_pos, hneg_ub⟩ :=
    mehlerMean_compactSupport_gaussian_ub hfMinus_cont hR hB_nn hfMinus_nn hfMinus_bd hneg_supp
  have htend_neg_nu : Tendsto (fun r => ∫ x : RadialSpace w, mehlerMean w r fMinus x ∂ν)
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace w, fMinus x ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (F := fun r x => mehlerMean w r fMinus x)
      (f := fMinus) (bound := fun x => C_neg * Real.exp (-π / 8 * ‖x‖ ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨hr12, hr1⟩
      exact (integrable_mehlerMean_of_bounded hν_gauss hfMinus_cont hfMinus_abs_bd
        (by linarith) hr1).aestronglyMeasurable
    · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      filter_upwards with x
      have hsub := hneg_ub hr x
      rw [Real.norm_of_nonneg hsub.1]
      exact hsub.2
    · convert (hν_gauss (by positivity : 0 < π / 8)).const_mul C_neg using 1
      ext x; ring
    · filter_upwards with x
      refine tendsto_mehlerMean_of_continuous_weight hfMinus_cont (b := 0) (d := 0) hB_nn
        (fun y => ?_) x
      calc |fMinus y| ≤ B := hfMinus_abs_bd y
        _ = B * euclideanWeight 0 0 y := by unfold euclideanWeight; simp
  let rSeq : ℕ → ℝ := fun n => 1 - 1 / (2 * ((n : ℝ) + 1))
  have hrSeq_mem : ∀ n : ℕ, rSeq n ∈ Ico (1 / 2 : ℝ) 1 := fun n => by
    dsimp [rSeq]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    refine ⟨?_, ?_⟩
    · have : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 :=
        div_le_div_of_nonneg_left zero_le_one zero_lt_two (by linarith)
      linarith
    · have : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
      linarith
  have hrSeq_tend : Tendsto rSeq atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => (hrSeq_mem n).2⟩
    have hinv : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop two_pos)
    have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    simpa [rSeq] using hsub
  have hAr_add : ∀ n : ℕ, ∀ x : RadialSpace w,
      mehlerMean w (rSeq n) fPlus x =
        mehlerMean w (rSeq n) f x + mehlerMean w (rSeq n) fMinus x := fun n x => by
    have hr0 : 0 ≤ rSeq n := by linarith [(hrSeq_mem n).1]
    have hr1 : rSeq n < 1 := (hrSeq_mem n).2
    have hkf : Integrable (fun y => mehlerKernel w (rSeq n) x y * f y) :=
      ((integral_mehlerKernel w hr0 hr1 x).1.const_mul B).mono'
        ((continuous_mehlerKernel w (rSeq n)).comp (Continuous.prodMk continuous_const continuous_id)
          |>.mul hf_cont).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm B]
          exact mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y))
    have hkm : Integrable (fun y => mehlerKernel w (rSeq n) x y * fMinus y) :=
      ((integral_mehlerKernel w hr0 hr1 x).1.const_mul B).mono'
        ((continuous_mehlerKernel w (rSeq n)).comp (Continuous.prodMk continuous_const continuous_id)
          |>.mul hfMinus_cont).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm B]
          exact mul_le_mul_of_nonneg_left (hfMinus_abs_bd y) (mehlerKernel_nonneg w hr1 x y))
    unfold mehlerMean
    simp_rw [hfPlus_eq, mul_add]
    exact integral_add hkf hkm
  have hAr_fPlus_nn : ∀ n : ℕ, ∀ x : RadialSpace w, 0 ≤ mehlerMean w (rSeq n) fPlus x := fun n x =>
    integral_nonneg fun y => mul_nonneg (mehlerKernel_nonneg w (hrSeq_mem n).2 x y) (hfPlus_nn y)
  have hAr_fPlus_eq_int : ∀ n : ℕ,
      ∫ x : RadialSpace w, mehlerMean w (rSeq n) fPlus x ∂ν =
        ∫ x : RadialSpace w, mehlerMean w (rSeq n) f x ∂ρ +
          ∫ x : RadialSpace w, mehlerMean w (rSeq n) fMinus x ∂ν := fun n => by
    have hmem : rSeq n ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [(hrSeq_mem n).1], (hrSeq_mem n).2⟩
    obtain ⟨hf_nu, _, h_cross⟩ :=
      lemma_fwA_part1 hMehler ν ρ hν_gauss hρ_gauss h_thermal hg_cont hg_int hg_odd hmem
    have hm_nu := integrable_mehlerMean_of_bounded hν_gauss hfMinus_cont hfMinus_abs_bd
      hmem.1.le hmem.2
    simp_rw [hAr_add n]
    rw [integral_add hf_nu hm_nu, h_cross]
  have hf_pt_plus : ∀ x : RadialSpace w,
      Tendsto (fun n => ENNReal.ofReal (mehlerMean w (rSeq n) fPlus x)) atTop
        (𝓝 (ENNReal.ofReal (fPlus x))) := fun x => by
    have h_lim : Tendsto (fun n => mehlerMean w (rSeq n) fPlus x) atTop (𝓝 (fPlus x)) := by
      refine (tendsto_mehlerMean_of_continuous_weight hfPlus_cont (b := 0) (d := 0) hB_nn
        (fun y => ?_) x).comp hrSeq_tend
      calc |fPlus y| ≤ B := by
            rw [abs_of_nonneg (hfPlus_nn y)]
            exact max_le ((le_abs_self _).trans (hf_bd y)) hB_nn
        _ = B * euclideanWeight 0 0 y := by unfold euclideanWeight; simp
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h_lim
  have hfPlus_abs_bd : ∀ x, |fPlus x| ≤ B := fun x => by
    rw [abs_of_nonneg (hfPlus_nn x)]
    exact max_le ((le_abs_self _).trans (hf_bd x)) hB_nn
  have hfatou : ∫⁻ x : RadialSpace w, ENNReal.ofReal (fPlus x) ∂ν ≤
      liminf (fun n => ∫⁻ x : RadialSpace w, ENNReal.ofReal (mehlerMean w (rSeq n) fPlus x) ∂ν)
        atTop := by
    have hliminf : ∀ x, ENNReal.ofReal (fPlus x) =
        liminf (fun n => ENNReal.ofReal (mehlerMean w (rSeq n) fPlus x)) atTop :=
      fun x => (hf_pt_plus x).liminf_eq.symm
    rw [lintegral_congr hliminf]
    refine lintegral_liminf_le fun n => ?_
    exact ENNReal.continuous_ofReal.measurable.comp
      (continuous_mehlerMean_of_bounded hfPlus_cont hfPlus_abs_bd
        (by linarith [(hrSeq_mem n).1]) (hrSeq_mem n).2).measurable
  have hlint_eq : ∀ n : ℕ,
      ∫⁻ x : RadialSpace w, ENNReal.ofReal (mehlerMean w (rSeq n) fPlus x) ∂ν =
        ENNReal.ofReal (∫ x : RadialSpace w, mehlerMean w (rSeq n) f x ∂ρ +
          ∫ x : RadialSpace w, mehlerMean w (rSeq n) fMinus x ∂ν) := fun n => by
    have hmem : rSeq n ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [(hrSeq_mem n).1], (hrSeq_mem n).2⟩
    have h_int := integrable_mehlerMean_of_bounded hν_gauss hfPlus_cont hfPlus_abs_bd
      hmem.1.le hmem.2
    rw [← ofReal_integral_eq_lintegral_ofReal h_int (Eventually.of_forall (hAr_fPlus_nn n)),
      hAr_fPlus_eq_int n]
  have hrhs_tend : Tendsto (fun n =>
      ENNReal.ofReal (∫ x : RadialSpace w, mehlerMean w (rSeq n) f x ∂ρ +
        ∫ x : RadialSpace w, mehlerMean w (rSeq n) fMinus x ∂ν)) atTop
      (𝓝 (ENNReal.ofReal (∫ x : RadialSpace w, f x ∂ρ + ∫ x : RadialSpace w, fMinus x ∂ν))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((htend_rho.comp hrSeq_tend).add (htend_neg_nu.comp hrSeq_tend))
  have hlint_le : ∫⁻ x : RadialSpace w, ENNReal.ofReal (fPlus x) ∂ν ≤
      ENNReal.ofReal (∫ x : RadialSpace w, f x ∂ρ + ∫ x : RadialSpace w, fMinus x ∂ν) := by
    refine hfatou.trans ?_
    simp_rw [hlint_eq]
    exact hrhs_tend.liminf_eq.le
  have hfPlus_int_nu : Integrable fPlus ν := by
    refine ⟨hfPlus_cont.aestronglyMeasurable, ?_⟩
    have heq : (fun x : RadialSpace w => (‖fPlus x‖ₑ : ℝ≥0∞)) =
        fun x => ENNReal.ofReal (fPlus x) := by
      ext x
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hfPlus_nn x)]
    rw [hasFiniteIntegral_iff_enorm, heq]
    exact lt_of_le_of_lt hlint_le ENNReal.ofReal_lt_top
  have hf_int_nu : Integrable f ν := by
    have heq : f = fun x => fPlus x - fMinus x := funext hf_split
    rw [heq]
    exact hfPlus_int_nu.sub hfMinus_int_nu
  refine ⟨hf_int_nu, ?_⟩
  have hofReal_fPlus : ∫⁻ x : RadialSpace w, ENNReal.ofReal (fPlus x) ∂ν =
      ENNReal.ofReal (∫ x : RadialSpace w, fPlus x ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hfPlus_int_nu (Eventually.of_forall hfPlus_nn)).symm
  rw [hofReal_fPlus] at hlint_le
  have hlim_nn : 0 ≤ ∫ x : RadialSpace w, f x ∂ρ + ∫ x : RadialSpace w, fMinus x ∂ν := by
    refine ge_of_tendsto ((htend_rho.comp hrSeq_tend).add (htend_neg_nu.comp hrSeq_tend))
      (Eventually.of_forall fun n => ?_)
    dsimp only [Function.comp_def]
    rw [← hAr_fPlus_eq_int n]
    exact integral_nonneg (hAr_fPlus_nn n)
  have hreal_le : ∫ x : RadialSpace w, fPlus x ∂ν ≤
      ∫ x : RadialSpace w, f x ∂ρ + ∫ x : RadialSpace w, fMinus x ∂ν :=
    (ENNReal.ofReal_le_ofReal_iff hlim_nn).mp hlint_le
  have hf_int_eq : ∫ x : RadialSpace w, f x ∂ν =
      ∫ x : RadialSpace w, fPlus x ∂ν - ∫ x : RadialSpace w, fMinus x ∂ν := by
    have heq : f = fun x => fPlus x - fMinus x := funext hf_split
    rw [heq]
    exact integral_sub hfPlus_int_nu hfMinus_int_nu
  linarith

/-- Lemma FW-A (3) (`crossing_sum_rule.tex`, `fw:abel`): exact equality `∫ f dν = ∫ f dρ`
when `|f(x)| ≤ C W(x)` for a weight `W(x) = (1 + ‖x‖²)^b exp(d ‖x‖)` integrable against both
`ν` and `ρ`. -/
theorem lemma_fwA_part3 {w : ℕ} (hMehler : MehlerOddMomentInput w)
    (ν ρ : Measure (RadialSpace w)) [SigmaFinite ν] [SigmaFinite ρ]
    (hν_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ν)
    (hρ_gauss : ∀ {ε : ℝ}, 0 < ε → Integrable (fun x : RadialSpace w => Real.exp (-ε * ‖x‖ ^ 2)) ρ)
    (h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w (thermalDiff w β) x ∂ρ)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Ici 0)) (hg_int : Integrable (radialLift w g))
    (hg_odd : 𝓕 (radialLift w g) = -(radialLift w g))
    {C b d : ℝ} (hC : 0 ≤ C) (hb : ∀ x : RadialSpace w, |radialLiftReal w g x| ≤ C * euclideanWeight b d x)
    (hWν : Integrable (euclideanWeight b d) ν) (hWρ : Integrable (euclideanWeight b d) ρ) :
    Integrable (radialLiftReal w g) ν ∧
      Integrable (radialLiftReal w g) ρ ∧
      ∫ x : RadialSpace w, radialLiftReal w g x ∂ν =
        ∫ x : RadialSpace w, radialLiftReal w g x ∂ρ := by
  let f : RadialSpace w → ℝ := radialLiftReal w g
  obtain ⟨hf_cont, hf_bd⟩ := radialLift_bounded_continuous_of_fourier_odd hg_int hg_odd
  have hf_int_ν : Integrable f ν :=
    (hWν.const_mul C).mono' hf_cont.aestronglyMeasurable (Eventually.of_forall fun x => hb x)
  have hf_int_ρ : Integrable f ρ :=
    (hWρ.const_mul C).mono' hf_cont.aestronglyMeasurable (Eventually.of_forall fun x => hb x)
  refine ⟨hf_int_ν, hf_int_ρ, ?_⟩
  obtain ⟨C', _, hW_stab⟩ := mehlerMean_euclideanWeight_le w b d
  let B : ℝ := ∫ y : RadialSpace w, ‖radialLift w g y‖
  let D₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  have hAr_bd : ∀ {r : ℝ}, r ∈ Ico (1 / 2 : ℝ) 1 → ∀ x : RadialSpace w,
      ‖mehlerMean w r f x‖ ≤ (C * C') * euclideanWeight b d x := fun {r} hr x => by
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have hr1 : r < 1 := hr.2
    have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
    have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
    have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
    have h2b_nn : 0 ≤ (2 : ℝ) ^ |b| := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hkf_int : Integrable (fun y => mehlerKernel w r x y * f y) :=
      ((integral_mehlerKernel w hr0 hr1 x).1.const_mul B).mono'
        ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
          |>.mul hf_cont).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y), mul_comm B]
          exact mul_le_mul_of_nonneg_left (hf_bd y) (mehlerKernel_nonneg w hr1 x y))
    let g_dom : RadialSpace w → ℝ := fun y =>
      (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
        Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2)
    have hg_dom_int : Integrable g_dom := by
      have h1 := (integrable_exp_linear_sub_gaussian w D₁ (one_div_pos.mpr h1r_pos)).comp_sub_right x
      have heq : g_dom = fun y => ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
          Real.exp (D₁ * ‖y - x‖ - π * (1 / (1 - r)) * ‖y - x‖ ^ 2) := by
        ext y; dsimp [g_dom]; congr 2; ring
      rw [heq]; exact h1.const_mul _
    have hkW_int : Integrable (fun y => mehlerKernel w r x y * euclideanWeight b d y) := by
      have hW_cont : Continuous (euclideanWeight b d : RadialSpace w → ℝ) := by
        unfold euclideanWeight
        refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
          ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
            continuousAt_const (Or.inl (by positivity))) (by fun_prop)
      refine hg_dom_int.mono'
        ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
          |>.mul hW_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg w hr1 x y)
        (euclideanWeight_pos b d y).le)]
      have hk := mehlerKernel_le_half_gaussian w hr.1 hr1 x y
      rw [norm_sub_rev x y] at hk
      have hw := euclideanWeight_ratio_le b d x y
      have hexp := rpow_sq_mul_exp_le_exp b d ‖y - x‖ (norm_nonneg _)
      have hw' : euclideanWeight b d y ≤ (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖) :=
        hw.trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg h2b_nn (euclideanWeight_pos b d x).le))
      calc mehlerKernel w r x y * euclideanWeight b d y
          ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
              ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) :=
            mul_le_mul hk hw' (euclideanWeight_pos b d y).le (mul_nonneg hrp_nn (Real.exp_pos _).le)
        _ = g_dom y := by
            dsimp [g_dom]
            rw [show (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
                ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) =
                (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
                  (Real.exp (D₁ * ‖y - x‖) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) by ring]
            rw [← Real.exp_add]; congr 2; ring
    calc ‖mehlerMean w r f x‖ ≤ ∫ y, ‖mehlerKernel w r x y * f y‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ y, mehlerKernel w r x y * |f y| := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]
      _ ≤ ∫ y, C * (mehlerKernel w r x y * euclideanWeight b d y) := by
          refine integral_mono (hkf_int.abs.congr (Eventually.of_forall fun y => by
            dsimp only
            rw [abs_mul, abs_of_nonneg (mehlerKernel_nonneg w hr1 x y)]))
            (hkW_int.const_mul C) fun y => ?_
          rw [← mul_assoc, mul_comm C (mehlerKernel w r x y), mul_assoc]
          exact mul_le_mul_of_nonneg_left (hb y) (mehlerKernel_nonneg w hr1 x y)
      _ = C * mehlerMean w r (euclideanWeight b d) x := integral_const_mul _ _
      _ ≤ C * (C' * euclideanWeight b d x) := mul_le_mul_of_nonneg_left (hW_stab hr x) hC
      _ = (C * C') * euclideanWeight b d x := by ring
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have htend_ν : Tendsto (fun r => ∫ x : RadialSpace w, mehlerMean w r f x ∂ν)
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace w, f x ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (F := fun r x => mehlerMean w r f x)
      (f := f) (bound := fun x => (C * C') * euclideanWeight b d x) ?_ ?_ (hWν.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨hr12, hr1⟩
      exact (integrable_mehlerMean_of_bounded hν_gauss hf_cont hf_bd (by linarith) hr1).aestronglyMeasurable
    · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      exact Eventually.of_forall (hAr_bd hr)
    · filter_upwards with x
      exact tendsto_mehlerMean_of_continuous_weight hf_cont hC hb x
  have htend_ρ : Tendsto (fun r => ∫ x : RadialSpace w, mehlerMean w r f x ∂ρ)
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace w, f x ∂ρ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (F := fun r x => mehlerMean w r f x)
      (f := f) (bound := fun x => (C * C') * euclideanWeight b d x) ?_ ?_ (hWρ.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨hr12, hr1⟩
      exact (integrable_mehlerMean_of_bounded hρ_gauss hf_cont hf_bd (by linarith) hr1).aestronglyMeasurable
    · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      exact Eventually.of_forall (hAr_bd hr)
    · filter_upwards with x
      exact tendsto_mehlerMean_of_continuous_weight hf_cont hC hb x
  have heq_f : ∀ᶠ r in 𝓝[<] 1,
      (∫ x : RadialSpace w, mehlerMean w r f x ∂ν) =
        ∫ x : RadialSpace w, mehlerMean w r f x ∂ρ := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact (lemma_fwA_part1 hMehler ν ρ hν_gauss hρ_gauss h_thermal hg_cont hg_int hg_odd hr).2.2
  exact tendsto_nhds_unique (htend_ν.congr' heq_f) htend_ρ

/-! ### Section 3: Crossing sum rule (`Lemma FW-X`) and certification (`Theorem FW-C`) -/

private lemma norm_euclidean_single_zero (w : ℕ) (hw : 1 ≤ w) :
    ‖(EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ) : RadialSpace w)‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (2 * w))).norm_eq_one ⟨0, by omega⟩

/-- Canonical embedding of `t ≥ 0` into `RadialSpace w` along the `0`-th coordinate with
`‖embedRadial w hw t‖² / 2 = t`. -/
noncomputable def embedRadial (w : ℕ) (hw : 1 ≤ w) (t : ℝ) : RadialSpace w :=
  Real.sqrt (2 * t) • EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ)

lemma continuous_embedRadial (w : ℕ) (hw : 1 ≤ w) : Continuous (embedRadial w hw) := by
  unfold embedRadial
  exact (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).smul continuous_const

lemma measurable_embedRadial (w : ℕ) (hw : 1 ≤ w) : Measurable (embedRadial w hw) :=
  (continuous_embedRadial w hw).measurable

lemma norm_embedRadial_sq {w : ℕ} (hw : 1 ≤ w) {t : ℝ} (ht : 0 ≤ t) :
    ‖embedRadial w hw t‖ ^ 2 = 2 * t := by
  unfold embedRadial
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_euclidean_single_zero w hw,
    mul_one, Real.sq_sqrt (by linarith)]

lemma radialLiftReal_embedRadial {w : ℕ} (hw : 1 ≤ w) (h : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    radialLiftReal w h (embedRadial w hw t) = h t := by
  unfold radialLiftReal
  rw [norm_embedRadial_sq hw ht]
  congr 1; ring

lemma continuous_radialLiftReal_of_continuousOn {w : ℕ} {h : ℝ → ℝ}
    (hh : ContinuousOn h (Ici 0)) : Continuous (radialLiftReal w h) := by
  unfold radialLiftReal
  have hmaps : ∀ x : RadialSpace w, ‖x‖ ^ 2 / 2 ∈ Ici (0 : ℝ) := fun x =>
    Set.mem_Ici.mpr (by positivity)
  have hcont_t : Continuous (fun x : RadialSpace w => ‖x‖ ^ 2 / 2) :=
    (continuous_norm.pow 2).div_const 2
  exact hh.comp_continuous hcont_t hmaps

private lemma admissibleMeasure_Ici_sub_lt_top (prob : FixedWeightProblem) (a : ℝ)
    (meas : AdmissibleCrossingMeasure prob a) {S : Set ℝ} {R : ℝ}
    (hS : S ⊆ Icc 0 R) : meas.ν S < ⊤ := by
  let B : ℝ := Real.exp (-2 * π * 1 * R)
  have hB_pos : 0 < B := Real.exp_pos _
  have hfin := meas.finite_laplace one_pos
  have hlin_lt : (∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν) < ⊤ := by
    have h1 : (∫⁻ t in Ici 0, ‖Real.exp (-2 * π * 1 * t)‖ₑ ∂meas.ν) < ⊤ := hfin.2
    have hcongr : (∫⁻ t in Ici 0, ‖Real.exp (-2 * π * 1 * t)‖ₑ ∂meas.ν) =
        ∫⁻ t in Ici 0, ENNReal.ofReal (Real.exp (-2 * π * 1 * t)) ∂meas.ν :=
      lintegral_congr_ae (ae_of_all _ fun t => Real.enorm_of_nonneg (Real.exp_pos _).le)
    rwa [hcongr] at h1
  have hsub_ge : S ⊆ {t ∈ Ici 0 | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))} := by
    intro t ht
    have ht_icc := hS ht
    refine ⟨ht_icc.1, ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)⟩
    nlinarith [Real.pi_pos, ht_icc.2]
  have hae : AEMeasurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * π * 1 * t)))
      (meas.ν.restrict (Ici 0)) :=
    (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-2 * π * 1 * t))).aemeasurable
  have hmarkov := mul_meas_ge_le_lintegral₀ hae (ENNReal.ofReal B)
  have hmeas_ge : meas.ν S ≤ (meas.ν.restrict (Ici 0))
      {t : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))} := by
    have h1 : meas.ν S ≤ meas.ν ({t ∈ Ici 0 | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))}) :=
      measure_mono hsub_ge
    have hmeas_set : MeasurableSet {t : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))} :=
      measurableSet_le measurable_const (ENNReal.continuous_ofReal.comp (by fun_prop)).measurable
    rwa [Measure.restrict_apply hmeas_set, Set.inter_comm]
  have hmul_lt : ENNReal.ofReal B * meas.ν S < ⊤ :=
    (by gcongr : ENNReal.ofReal B * meas.ν S ≤ ENNReal.ofReal B * (meas.ν.restrict (Ici 0))
      {t : ℝ | ENNReal.ofReal B ≤ ENNReal.ofReal (Real.exp (-2 * π * 1 * t))}).trans_lt
      (hmarkov.trans_lt hlin_lt)
  rcases ENNReal.mul_lt_top_iff.mp hmul_lt with ⟨_, hlt⟩ | h0 | h0
  · exact hlt
  · exfalso
    have hle0 : B ≤ 0 := ENNReal.ofReal_eq_zero.mp h0
    linarith [hB_pos]
  · simp [h0]

/-- Pushforward of `meas.ν.restrict (Ici 0)` onto `ℝ^{2w}` along `embedRadial`. -/
noncomputable def nuLift (prob : FixedWeightProblem) (a : ℝ)
    (meas : AdmissibleCrossingMeasure prob a) : Measure (RadialSpace prob.w) :=
  Measure.map (embedRadial prob.w prob.hw) (meas.ν.restrict (Ici 0))

lemma nuLift_sigmaFinite (prob : FixedWeightProblem) (a : ℝ)
    (meas : AdmissibleCrossingMeasure prob a) : SigmaFinite (nuLift prob a meas) := by
  refine ⟨⟨{
    set := fun n => Metric.ball (0 : RadialSpace prob.w) (n : ℝ)
    set_mem := fun _ => Set.mem_univ _
    finite := fun n => by
      unfold nuLift
      rw [Measure.map_apply (measurable_embedRadial prob.w prob.hw) measurableSet_ball]
      rw [Measure.restrict_apply (measurableSet_ball.preimage (measurable_embedRadial prob.w prob.hw))]
      refine admissibleMeasure_Ici_sub_lt_top prob a meas (R := (n : ℝ) ^ 2 / 2) ?_
      intro t ⟨ht_ball, ht_nn⟩
      refine ⟨ht_nn, ?_⟩
      have hlt : ‖embedRadial prob.w prob.hw t‖ < (n : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using ht_ball
      have hsq : 2 * t ≤ (n : ℝ) ^ 2 := by
        rw [← norm_embedRadial_sq prob.hw ht_nn]
        exact pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
      linarith
    spanning := Metric.iUnion_ball_nat 0
  }⟩⟩

lemma nuLift_gauss (prob : FixedWeightProblem) (a : ℝ)
    (meas : AdmissibleCrossingMeasure prob a) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2)) (nuLift prob a meas) := by
  unfold nuLift
  rw [integrable_map_measure (by fun_prop : Continuous fun x : RadialSpace prob.w =>
      Real.exp (-ε * ‖x‖ ^ 2)).aestronglyMeasurable
    (measurable_embedRadial prob.w prob.hw).aemeasurable]
  have hlap := meas.finite_laplace (div_pos hε Real.pi_pos)
  refine hlap.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  dsimp only [Function.comp_def]
  rw [norm_embedRadial_sq prob.hw (Set.mem_Ici.mp ht)]
  congr 1; field_simp

lemma integrable_nuLift_iff (prob : FixedWeightProblem) (a : ℝ)
    (meas : AdmissibleCrossingMeasure prob a) {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0)) :
    Integrable (radialLiftReal prob.w h) (nuLift prob a meas) ↔
      IntegrableOn h (Ici 0) meas.ν := by
  unfold nuLift IntegrableOn
  rw [integrable_map_measure (continuous_radialLiftReal_of_continuousOn hh).aestronglyMeasurable
    (measurable_embedRadial prob.w prob.hw).aemeasurable]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact radialLiftReal_embedRadial prob.hw h (Set.mem_Ici.mp ht)

lemma integral_nuLift (prob : FixedWeightProblem) (a : ℝ)
    (meas : AdmissibleCrossingMeasure prob a) {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0)) :
    ∫ x : RadialSpace prob.w, radialLiftReal prob.w h x ∂(nuLift prob a meas) =
      ∫ t in Ici 0, h t ∂meas.ν := by
  unfold nuLift
  rw [integral_map (measurable_embedRadial prob.w prob.hw).aemeasurable
    (continuous_radialLiftReal_of_continuousOn hh).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact radialLiftReal_embedRadial prob.hw h (Set.mem_Ici.mp ht)

/-- Reference Cardy measure `ϱ(‖x‖²/2) dx` on `ℝ^{2w}`. -/
noncomputable def rhoLift (prob : FixedWeightProblem) (a : ℝ) : Measure (RadialSpace prob.w) :=
  volume.withDensity (fun x : RadialSpace prob.w => ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2)))

private lemma exp_linear_sub_gaussian_bound (D₁ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, 0 ≤ u → Real.exp (D₁ * u - π * c * u ^ 2) ≤ K := by
  refine ⟨Real.exp (D₁ ^ 2 / (4 * π * c)), Real.exp_pos _, fun u _ => Real.exp_le_exp.mpr ?_⟩
  have hsq : 0 ≤ (2 * π * c * u - D₁) ^ 2 := sq_nonneg _
  have hpc : 0 < 4 * π * c := by positivity
  rw [le_div_iff₀ hpc]
  nlinarith [Real.pi_pos]

lemma rhoLift_gauss (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2)) (rhoLift prob a) := by
  unfold rhoLift
  have hmeas : Measurable (fun x : RadialSpace prob.w =>
      ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
    (ENNReal.continuous_ofReal.comp ((continuous_rhoDensity prob a).comp
      ((continuous_norm.pow 2).div_const 2))).measurable
  rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  obtain ⟨C, hC_pos, hrho_le⟩ := prob.rhoDensity_le_cardyWeight ha ha_pos
  let b : ℝ := -((prob.w - 1 : ℝ) / 2 + 1 / 4)
  let d : ℝ := 2 * Real.sqrt 2 * π * Real.sqrt a
  let C₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  obtain ⟨K₁, hK₁_pos, hK₁⟩ := exp_linear_sub_gaussian_bound C₁ (div_pos (div_pos hε two_pos) Real.pi_pos)
  have hint_g := (integral_exp_neg_pi_mul_norm_sq prob.w (div_pos (div_pos hε two_pos) Real.pi_pos)).1
  have heq_dens : (fun x : RadialSpace prob.w =>
      (ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))).toReal • Real.exp (-ε * ‖x‖ ^ 2)) =
      fun x => prob.rhoDensity a (‖x‖ ^ 2 / 2) * Real.exp (-ε * ‖x‖ ^ 2) := by
    ext x
    rw [ENNReal.toReal_ofReal (prob.rhoDensity_nonneg ha (by positivity)), smul_eq_mul]
  rw [heq_dens]
  have hcont_f : Continuous (fun x : RadialSpace prob.w =>
      prob.rhoDensity a (‖x‖ ^ 2 / 2) * Real.exp (-ε * ‖x‖ ^ 2)) :=
    ((continuous_rhoDensity prob a).comp ((continuous_norm.pow 2).div_const 2)).mul
      (by fun_prop : Continuous fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2))
  refine (hint_g.const_mul (C * K₁)).mono' hcont_f.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hrho_nn : 0 ≤ prob.rhoDensity a (‖x‖ ^ 2 / 2) := prob.rhoDensity_nonneg ha (by positivity)
  rw [Real.norm_of_nonneg (mul_nonneg hrho_nn (Real.exp_pos _).le)]
  have h1 : prob.rhoDensity a (‖x‖ ^ 2 / 2) ≤ C * euclideanWeight b d x := by
    have hraw := hrho_le (‖x‖ ^ 2 / 2) (by positivity)
    rwa [← euclideanWeight_eq_cardyWeight b d x] at hraw
  have h2 := rpow_sq_mul_exp_le_exp b d ‖x‖ (norm_nonneg x)
  have hb_nonpos : b ≤ 0 := by
    have hw1 : (1 : ℝ) ≤ (prob.w : ℝ) := by exact_mod_cast prob.hw
    dsimp [b]; linarith
  have hw_le : euclideanWeight b d x ≤ Real.exp (C₁ * ‖x‖) := by
    have h1pow : (1 + ‖x‖ ^ 2) ^ b ≤ (1 + ‖x‖ ^ 2) ^ |b| :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖x‖]) (hb_nonpos.trans (abs_nonneg b))
    have hde : Real.exp (d * ‖x‖) ≤ Real.exp (|d| * ‖x‖) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self d) (norm_nonneg x))
    calc euclideanWeight b d x = (1 + ‖x‖ ^ 2) ^ b * Real.exp (d * ‖x‖) := rfl
      _ ≤ (1 + ‖x‖ ^ 2) ^ |b| * Real.exp (|d| * ‖x‖) :=
          mul_le_mul h1pow hde (Real.exp_pos _).le (Real.rpow_pos_of_pos (by positivity) _).le
      _ ≤ Real.exp (C₁ * ‖x‖) := h2
  have hK₁_le := hK₁ ‖x‖ (norm_nonneg x)
  have hexp_split : Real.exp (C₁ * ‖x‖) * Real.exp (-ε * ‖x‖ ^ 2) ≤
      K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) := by
    calc Real.exp (C₁ * ‖x‖) * Real.exp (-ε * ‖x‖ ^ 2)
        = Real.exp (C₁ * ‖x‖ + -ε * ‖x‖ ^ 2) := (Real.exp_add _ _).symm
      _ = Real.exp ((C₁ * ‖x‖ - π * (ε / 2 / π) * ‖x‖ ^ 2) +
            (-π * (ε / 2 / π) * ‖x‖ ^ 2)) := by
          congr 1; field_simp; ring
      _ = Real.exp (C₁ * ‖x‖ - π * (ε / 2 / π) * ‖x‖ ^ 2) *
            Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) := Real.exp_add _ _
      _ ≤ K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hK₁_le (Real.exp_pos _).le
  calc prob.rhoDensity a (‖x‖ ^ 2 / 2) * Real.exp (-ε * ‖x‖ ^ 2)
      ≤ (C * Real.exp (C₁ * ‖x‖)) * Real.exp (-ε * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (h1.trans (mul_le_mul_of_nonneg_left hw_le hC_pos.le))
          (Real.exp_pos _).le
    _ = C * (Real.exp (C₁ * ‖x‖) * Real.exp (-ε * ‖x‖ ^ 2)) := by ring
    _ ≤ C * (K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp_split hC_pos.le
    _ = C * K₁ * Real.exp (-π * (ε / 2 / π) * ‖x‖ ^ 2) := by ring

lemma integrable_rhoLift_of_cardy {prob : FixedWeightProblem} {a : ℝ}
    (ha : prob.totalShift ≤ a) {h : ℝ → ℝ} (hh : ContinuousOn h (Ici 0))
    (hint : IntegrableOn (fun t => |h t| * prob.cardyV a t) (Ioi 0)) :
    Integrable (radialLiftReal prob.w h) (rhoLift prob a) := by
  unfold rhoLift
  have hmeas : Measurable (fun x : RadialSpace prob.w =>
      ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
    (ENNReal.continuous_ofReal.comp ((continuous_rhoDensity prob a).comp
      ((continuous_norm.pow 2).div_const 2))).measurable
  rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun x : RadialSpace prob.w =>
      (ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))).toReal • radialLiftReal prob.w h x) =
      fun x => prob.rhoDensity a (‖x‖ ^ 2 / 2) * h (‖x‖ ^ 2 / 2) := by
    ext x
    rw [ENNReal.toReal_ofReal (prob.rhoDensity_nonneg ha (by positivity)), smul_eq_mul]
    rfl
  rw [heq]
  have hint_rad : Integrable (radialLift prob.w (fun t => prob.rhoDensity a t * h t)) := by
    rw [integrable_radialLift_iff prob.hw]
    let c₀ : ℝ := ((prob.w - 1).factorial : ℝ) / (2 * π) ^ prob.w * (2 * π)
    have h1 : IntegrableOn (fun t => c₀ * (|h t| * prob.cardyV a t)) (Ioi 0) :=
      hint.const_mul c₀
    have hcont_t : ContinuousOn (fun t => t ^ (prob.w - 1) * (prob.rhoDensity a t * h t)) (Ioi 0) :=
      ((continuous_id.pow _).continuousOn.mul
        ((continuous_rhoDensity prob a).continuousOn.mul hh)).mono Ioi_subset_Ici_self
    refine h1.mono' (hcont_t.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := Set.mem_Ioi.mp ht
    have hV_nn : 0 ≤ prob.cardyV a t := prob.cardyV_nonneg ha ht_pos.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos ht_pos _),
      abs_of_nonneg (prob.rhoDensity_nonneg ha ht_pos.le)]
    have heq_t : t ^ (prob.w - 1) * prob.rhoDensity a t = c₀ * prob.cardyV a t := by
      unfold FixedWeightProblem.rhoDensity
      rw [prob.cardyV_eq_pow_mul_reduced]
      dsimp [c₀]; ring
    rw [← mul_assoc, heq_t]
    exact le_of_eq (by ring)
  exact (integrable_radialLift_iff_real prob.w _).mp hint_rad |>.congr
    (Eventually.of_forall fun x => rfl)

lemma integral_rhoLift (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (h : ℝ → ℝ) :
    ∫ x : RadialSpace prob.w, radialLiftReal prob.w h x ∂(rhoLift prob a) =
      ∫ t in Ioi 0, h t * prob.cardyDensity a t := by
  unfold rhoLift
  have hmeas : Measurable (fun x : RadialSpace prob.w =>
      ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
    (ENNReal.continuous_ofReal.comp ((continuous_rhoDensity prob a).comp
      ((continuous_norm.pow 2).div_const 2))).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun x : RadialSpace prob.w =>
      (ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))).toReal • radialLiftReal prob.w h x) =
      fun x => h (‖x‖ ^ 2 / 2) * prob.rhoDensity a (‖x‖ ^ 2 / 2) := by
    ext x
    rw [ENNReal.toReal_ofReal (prob.rhoDensity_nonneg ha (by positivity)), smul_eq_mul, mul_comm]
    rfl
  rw [heq]
  exact prob.integral_rhoDensity a h

lemma integral_rhoLift_eq_neg_gVac (prob : FixedWeightProblem) {a : ℝ} (ha : prob.totalShift ≤ a)
    (g : ℝ → ℝ) :
    ∫ x : RadialSpace prob.w, radialLiftReal prob.w g x ∂(rhoLift prob a) = -prob.gVac a g := by
  rw [integral_rhoLift prob ha g]
  unfold FixedWeightProblem.gVac FixedWeightProblem.cardyDensity
  have heq : (fun t => g t * (2 * π * prob.cardyV a t)) = fun t => (2 * π) * (g t * prob.cardyV a t) := by
    ext t; ring
  rw [heq, integral_const_mul]
  ring

private lemma mehlerKernel_mul_euclideanWeight_integrable {w : ℕ} (b d : ℝ)
    {r : ℝ} (hr12 : 1 / 2 ≤ r) (hr1 : r < 1) (x : RadialSpace w) :
    Integrable (fun y : RadialSpace w => mehlerKernel w r x y * euclideanWeight b d y) := by
  have h1r_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h1r2_nn : 0 ≤ (1 - r) / 2 := by linarith
  have hrp_nn : 0 ≤ ((1 - r) / 2) ^ (-(w : ℝ)) := Real.rpow_nonneg h1r2_nn _
  have h2b_nn : 0 ≤ (2 : ℝ) ^ |b| := (Real.rpow_pos_of_pos (by norm_num) _).le
  let D₁ : ℝ := 2 * (Nat.ceil |b| : ℝ) + |d|
  let g_dom : RadialSpace w → ℝ := fun y =>
    (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
      Real.exp (D₁ * ‖y - x‖ - π / (1 - r) * ‖y - x‖ ^ 2)
  have hg_dom_int : Integrable g_dom := by
    have h1 := (integrable_exp_linear_sub_gaussian w D₁ (one_div_pos.mpr h1r_pos)).comp_sub_right x
    have heq : g_dom = fun y => ((2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ))) *
        Real.exp (D₁ * ‖y - x‖ - π * (1 / (1 - r)) * ‖y - x‖ ^ 2) := by
      ext y; dsimp [g_dom]; congr 2; ring
    rw [heq]; exact h1.const_mul _
  have hW_cont : Continuous (euclideanWeight b d : RadialSpace w → ℝ) := by
    unfold euclideanWeight
    refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
        continuousAt_const (Or.inl (by positivity))) (by fun_prop)
  refine hg_dom_int.mono'
    ((continuous_mehlerKernel w r).comp (Continuous.prodMk continuous_const continuous_id)
      |>.mul hW_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg w hr1 x y)
    (euclideanWeight_pos b d y).le)]
  have hk := mehlerKernel_le_half_gaussian w hr12 hr1 x y
  rw [norm_sub_rev x y] at hk
  have hw := euclideanWeight_ratio_le b d x y
  have hexp := rpow_sq_mul_exp_le_exp b d ‖y - x‖ (norm_nonneg _)
  have hw' : euclideanWeight b d y ≤ (2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖) :=
    hw.trans (mul_le_mul_of_nonneg_left hexp (mul_nonneg h2b_nn (euclideanWeight_pos b d x).le))
  calc mehlerKernel w r x y * euclideanWeight b d y
      ≤ (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
          ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) :=
        mul_le_mul hk hw' (euclideanWeight_pos b d y).le (mul_nonneg hrp_nn (Real.exp_pos _).le)
    _ = g_dom y := by
        dsimp [g_dom]
        rw [show (((1 - r) / 2) ^ (-(w : ℝ)) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) *
            ((2 : ℝ) ^ |b| * euclideanWeight b d x * Real.exp (D₁ * ‖y - x‖)) =
            (2 : ℝ) ^ |b| * euclideanWeight b d x * ((1 - r) / 2) ^ (-(w : ℝ)) *
              (Real.exp (D₁ * ‖y - x‖) * Real.exp (-π / (1 - r) * ‖y - x‖ ^ 2)) by ring]
        rw [← Real.exp_add]; congr 2; ring

private lemma tendsto_mehlerMean_rhoLift (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) {g : ℝ → ℝ} (hg : TestClass prob a g) :
    Tendsto (fun r => ∫ x : RadialSpace prob.w, mehlerMean prob.w r (radialLiftReal prob.w g) x
        ∂(rhoLift prob a))
      (𝓝[<] 1) (𝓝 (∫ x : RadialSpace prob.w, radialLiftReal prob.w g x ∂(rhoLift prob a))) := by
  let f : RadialSpace prob.w → ℝ := radialLiftReal prob.w g
  let rhoTil : RadialSpace prob.w → ℝ := fun x => prob.rhoDensity a (‖x‖ ^ 2 / 2)
  have hrho_cont : Continuous rhoTil :=
    (continuous_rhoDensity prob a).comp ((continuous_norm.pow 2).div_const 2)
  have hrho_nn : ∀ x, 0 ≤ rhoTil x := fun x => prob.rhoDensity_nonneg ha (by positivity)
  obtain ⟨hf_cont, hf_bd⟩ := radialLift_bounded_continuous_of_fourier_odd hg.int_lift hg.fourier_odd
  let B : ℝ := ∫ y : RadialSpace prob.w, ‖radialLift prob.w g y‖
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  let b : ℝ := -((prob.w - 1 : ℝ) / 2 + 1 / 4)
  let d : ℝ := 2 * Real.sqrt 2 * π * Real.sqrt a
  obtain ⟨C_hi, hC_hi_pos, hrho_hi⟩ := prob.rhoDensity_le_cardyWeight ha ha_pos
  obtain ⟨c_lo, T₀, hc_lo_pos, _, hrho_lo⟩ := prob.rhoDensity_ge_cardyWeight_large ha ha_pos
  obtain ⟨C', _, hW_stab⟩ := mehlerMean_euclideanWeight_le prob.w b d
  have hrho_dom : ∀ x : RadialSpace prob.w, |rhoTil x| ≤ C_hi * euclideanWeight b d x := fun x => by
    rw [abs_of_nonneg (hrho_nn x)]
    exact (hrho_hi (‖x‖ ^ 2 / 2) (by positivity)).trans_eq (by rw [euclideanWeight_eq_cardyWeight])
  have hf_rho_int : Integrable (fun y : RadialSpace prob.w => |f y| * rhoTil y) volume := by
    have h1 := integrable_rhoLift_of_cardy ha hg.cont.abs (by simpa only [abs_abs] using hg.int_cardy)
    change Integrable (fun x : RadialSpace prob.w => |g (‖x‖ ^ 2 / 2)|) (rhoLift prob a) at h1
    unfold rhoLift at h1
    have hmeas : Measurable (fun x : RadialSpace prob.w =>
        ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.comp hrho_cont).measurable
    rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (Eventually.of_forall fun x => ?_)
    dsimp only [rhoTil]
    rw [ENNReal.toReal_ofReal (hrho_nn x), smul_eq_mul, mul_comm]
    rfl
  have hf_W_int : Integrable (fun y : RadialSpace prob.w => |f y| * euclideanWeight b d y) volume := by
    let R₀ : ℝ := Real.sqrt (2 * T₀)
    let M_in : ℝ := B * (1 + R₀ ^ 2) ^ |b| * Real.exp (|d| * R₀)
    let g_maj : RadialSpace prob.w → ℝ := fun y =>
      (1 / c_lo) * (|f y| * rhoTil y) +
        Set.indicator (Metric.closedBall (0 : RadialSpace prob.w) R₀) (fun _ => M_in) y
    have hmaj_int : Integrable g_maj volume :=
      (hf_rho_int.const_mul _).add ((integrable_indicator_iff measurableSet_closedBall).mpr
        (integrableOn_const (C := M_in) (hs := measure_closedBall_lt_top.ne)))
    have hW_cont : Continuous (euclideanWeight b d : RadialSpace prob.w → ℝ) := by
      unfold euclideanWeight
      refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
        ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
          continuousAt_const (Or.inl (by positivity))) (by fun_prop)
    refine hmaj_int.mono' (hf_cont.abs.mul hW_cont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (euclideanWeight_pos b d y).le)]
    rcases le_or_gt ‖y‖ R₀ with hy_in | hy_out
    · have hmem : y ∈ Metric.closedBall (0 : RadialSpace prob.w) R₀ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hy_in
      have h1pow : (1 + ‖y‖ ^ 2) ^ b ≤ (1 + R₀ ^ 2) ^ |b| := by
        have hb_nn : b ≤ 0 := by
          have hw1 : (1 : ℝ) ≤ (prob.w : ℝ) := by exact_mod_cast prob.hw
          dsimp [b]; linarith
        calc (1 + ‖y‖ ^ 2) ^ b ≤ (1 + ‖y‖ ^ 2) ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg ‖y‖]) hb_nn
          _ = 1 := Real.rpow_zero _
          _ ≤ (1 + R₀ ^ 2) ^ |b| := Real.one_le_rpow (by linarith [sq_nonneg R₀]) (abs_nonneg b)
      have hexp_le : Real.exp (d * ‖y‖) ≤ Real.exp (|d| * R₀) :=
        Real.exp_le_exp.mpr (calc d * ‖y‖ ≤ |d| * ‖y‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self d) (norm_nonneg y)
          _ ≤ |d| * R₀ := mul_le_mul_of_nonneg_left hy_in (abs_nonneg d))
      have hW_le : euclideanWeight b d y ≤ (1 + R₀ ^ 2) ^ |b| * Real.exp (|d| * R₀) :=
        mul_le_mul h1pow hexp_le (Real.exp_pos _).le (by positivity)
      have h1 : |f y| * euclideanWeight b d y ≤ M_in := by
        calc |f y| * euclideanWeight b d y ≤ B * ((1 + R₀ ^ 2) ^ |b| * Real.exp (|d| * R₀)) :=
              mul_le_mul (hf_bd y) hW_le (euclideanWeight_pos b d y).le hB_nn
          _ = M_in := by dsimp [M_in]; ring
      have hnonneg : 0 ≤ (1 / c_lo) * (|f y| * rhoTil y) :=
        mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) (hrho_nn y))
      dsimp [g_maj]
      rw [Set.indicator_of_mem hmem]
      linarith
    · have hnot : y ∉ Metric.closedBall (0 : RadialSpace prob.w) R₀ := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy_out
      have ht_ge : T₀ ≤ ‖y‖ ^ 2 / 2 := by
        have hsq : R₀ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy_out.le 2
        rw [Real.sq_sqrt (by positivity)] at hsq
        linarith
      have hcardy_le := hrho_lo (‖y‖ ^ 2 / 2) ht_ge
      rw [← euclideanWeight_eq_cardyWeight] at hcardy_le
      have hW_le : euclideanWeight b d y ≤ (1 / c_lo) * rhoTil y := by
        rw [one_div_mul_eq_div, le_div_iff₀ hc_lo_pos, mul_comm]
        exact hcardy_le
      dsimp [g_maj]
      rw [Set.indicator_of_notMem hnot, add_zero]
      calc |f y| * euclideanWeight b d y ≤ |f y| * ((1 / c_lo) * rhoTil y) :=
            mul_le_mul_of_nonneg_left hW_le (abs_nonneg _)
        _ = (1 / c_lo) * (|f y| * rhoTil y) := by ring
  have hint_eval : (fun r => ∫ x : RadialSpace prob.w,
        mehlerMean prob.w r f x ∂(rhoLift prob a)) =ᶠ[𝓝[<] 1]
      (fun r => ∫ y : RadialSpace prob.w, f y * mehlerMean prob.w r rhoTil y ∂volume) := by
    filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
    have hr1 : r < 1 := hr.2
    have hrew : ∫ x : RadialSpace prob.w, mehlerMean prob.w r f x ∂(rhoLift prob a) =
        ∫ x : RadialSpace prob.w, mehlerMean prob.w r f x * rhoTil x ∂volume := by
      unfold rhoLift
      have hmeas : Measurable (fun x : RadialSpace prob.w =>
          ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
        (ENNReal.continuous_ofReal.comp hrho_cont).measurable
      rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only [rhoTil]
      rw [ENNReal.toReal_ofReal (hrho_nn x), smul_eq_mul, mul_comm]
    rw [hrew]
    have hprod_int : Integrable (Function.uncurry fun x y : RadialSpace prob.w =>
        (mehlerKernel prob.w r x y * f y) * rhoTil x) (volume.prod volume) := by
      have haesm : AEStronglyMeasurable (Function.uncurry fun x y : RadialSpace prob.w =>
          (mehlerKernel prob.w r x y * f y) * rhoTil x) (volume.prod volume) :=
        (((continuous_mehlerKernel prob.w r).mul (hf_cont.comp continuous_snd)).mul
          (hrho_cont.comp continuous_fst)).aestronglyMeasurable
      rw [integrable_prod_iff' haesm]
      refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
      · have hW := mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr1 y
        have hcont_x : Continuous (fun x : RadialSpace prob.w =>
            mehlerKernel prob.w r x y * f y * rhoTil x) :=
          (((continuous_mehlerKernel prob.w r).comp (continuous_id.prodMk continuous_const)).mul
            continuous_const).mul hrho_cont
        refine (hW.const_mul (|f y| * C_hi)).mono' hcont_x.aestronglyMeasurable
          (Eventually.of_forall fun x => ?_)
        dsimp only [Function.uncurry]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg prob.w hr1 x y),
          mehlerKernel_symm prob.w r x y]
        calc mehlerKernel prob.w r y x * |f y| * |rhoTil x|
            ≤ mehlerKernel prob.w r y x * |f y| * (C_hi * euclideanWeight b d x) :=
              mul_le_mul_of_nonneg_left (hrho_dom x)
                (mul_nonneg (mehlerKernel_nonneg prob.w hr1 y x) (abs_nonneg _))
          _ = |f y| * C_hi * (mehlerKernel prob.w r y x * euclideanWeight b d x) := by ring
      · have heq_y : (fun y : RadialSpace prob.w =>
            ∫ x : RadialSpace prob.w, ‖(Function.uncurry fun x y : RadialSpace prob.w =>
              mehlerKernel prob.w r x y * f y * rhoTil x) (x, y)‖) =
            fun y => |f y| * mehlerMean prob.w r rhoTil y := by
          ext y
          have hker_rho : ∀ x, ‖mehlerKernel prob.w r x y * f y * rhoTil x‖ =
              |f y| * (mehlerKernel prob.w r y x * rhoTil x) := fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mehlerKernel_nonneg prob.w hr1 x y),
              abs_of_nonneg (hrho_nn x), mehlerKernel_symm prob.w r x y]
            ring
          simp_rw [Function.uncurry_apply_pair, hker_rho, integral_const_mul]
          rfl
        rw [heq_y]
        have haesm_Ar : AEStronglyMeasurable (mehlerMean prob.w r rhoTil) volume :=
          (((continuous_mehlerKernel prob.w r).mul (hrho_cont.comp continuous_snd)).aestronglyMeasurable).integral_prod_right'
        refine (hf_W_int.const_mul (C_hi * C')).mono' (hf_cont.abs.aestronglyMeasurable.mul haesm_Ar)
          (Eventually.of_forall fun y => ?_)
        · have hAr_nn : 0 ≤ mehlerMean prob.w r rhoTil y :=
            integral_nonneg fun x => mul_nonneg (mehlerKernel_nonneg prob.w hr1 y x) (hrho_nn x)
          rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hAr_nn)]
          have hAr_ub : mehlerMean prob.w r rhoTil y ≤ C_hi * C' * euclideanWeight b d y := by
            have h1 : mehlerMean prob.w r rhoTil y ≤ C_hi * mehlerMean prob.w r (euclideanWeight b d) y := by
              unfold mehlerMean
              rw [← integral_const_mul]
              refine integral_mono
                ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr1 y).const_mul C_hi |>.mono'
                  (((continuous_mehlerKernel prob.w r).comp
                    (Continuous.prodMk continuous_const continuous_id)).mul hrho_cont).aestronglyMeasurable
                  (Eventually.of_forall fun x => by
                    rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg prob.w hr1 y x) (hrho_nn x)),
                      ← mul_assoc, mul_comm C_hi (mehlerKernel prob.w r y x), mul_assoc]
                    exact mul_le_mul_of_nonneg_left
                      (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                      (mehlerKernel_nonneg prob.w hr1 y x)))
                ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr1 y).const_mul C_hi)
                (fun x => by
                  rw [← mul_assoc, mul_comm C_hi (mehlerKernel prob.w r y x), mul_assoc]
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                    (mehlerKernel_nonneg prob.w hr1 y x))
            exact h1.trans (by nlinarith [hW_stab hr y])
          calc |f y| * mehlerMean prob.w r rhoTil y
              ≤ |f y| * (C_hi * C' * euclideanWeight b d y) :=
                mul_le_mul_of_nonneg_left hAr_ub (abs_nonneg _)
            _ = C_hi * C' * (|f y| * euclideanWeight b d y) := by ring
    have hswap := integral_integral_swap hprod_int
    calc ∫ x : RadialSpace prob.w, mehlerMean prob.w r f x * rhoTil x
        = ∫ x : RadialSpace prob.w, ∫ y : RadialSpace prob.w,
            mehlerKernel prob.w r x y * f y * rhoTil x := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          unfold mehlerMean
          exact (integral_mul_const (rhoTil x) _).symm
      _ = ∫ y : RadialSpace prob.w, ∫ x : RadialSpace prob.w,
            mehlerKernel prob.w r x y * f y * rhoTil x := hswap
      _ = ∫ y : RadialSpace prob.w, f y * mehlerMean prob.w r rhoTil y := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          have heq_x : (fun x => mehlerKernel prob.w r x y * f y * rhoTil x) =
              fun x => f y * (mehlerKernel prob.w r y x * rhoTil x) := by
            ext x; rw [mehlerKernel_symm prob.w r x y]; ring
          dsimp only
          rw [heq_x, integral_const_mul]
          rfl
  have hdom_tend : Tendsto (fun r => ∫ y : RadialSpace prob.w, f y * mehlerMean prob.w r rhoTil y ∂volume)
      (𝓝[<] 1) (𝓝 (∫ y : RadialSpace prob.w, f y * rhoTil y ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (F := fun r y => f y * mehlerMean prob.w r rhoTil y)
      (f := fun y => f y * rhoTil y)
      (bound := fun y => (C_hi * C') * (|f y| * euclideanWeight b d y)) ?_ ?_ (hf_W_int.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r ⟨_, hr1⟩
      exact hf_cont.aestronglyMeasurable.mul
        (((continuous_mehlerKernel prob.w r).mul (hrho_cont.comp continuous_snd)).aestronglyMeasurable).integral_prod_right'
    · filter_upwards [Ico_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with r hr
      filter_upwards with y
      have hAr_nn : 0 ≤ mehlerMean prob.w r rhoTil y :=
        integral_nonneg fun x => mul_nonneg (mehlerKernel_nonneg prob.w hr.2 y x) (hrho_nn x)
      have hAr_ub : mehlerMean prob.w r rhoTil y ≤ C_hi * C' * euclideanWeight b d y := by
        have h1 : mehlerMean prob.w r rhoTil y ≤ C_hi * mehlerMean prob.w r (euclideanWeight b d) y := by
          unfold mehlerMean
          rw [← integral_const_mul]
          refine integral_mono
            ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr.2 y).const_mul C_hi |>.mono'
              (((continuous_mehlerKernel prob.w r).comp
                (Continuous.prodMk continuous_const continuous_id)).mul hrho_cont).aestronglyMeasurable
              (Eventually.of_forall fun x => by
                rw [Real.norm_of_nonneg (mul_nonneg (mehlerKernel_nonneg prob.w hr.2 y x) (hrho_nn x)),
                  ← mul_assoc, mul_comm C_hi (mehlerKernel prob.w r y x), mul_assoc]
                exact mul_le_mul_of_nonneg_left
                  (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                  (mehlerKernel_nonneg prob.w hr.2 y x)))
            ((mehlerKernel_mul_euclideanWeight_integrable b d hr.1 hr.2 y).const_mul C_hi)
            (fun x => by
              rw [← mul_assoc, mul_comm C_hi (mehlerKernel prob.w r y x), mul_assoc]
              exact mul_le_mul_of_nonneg_left
                (by simpa [abs_of_nonneg (hrho_nn x)] using hrho_dom x)
                (mehlerKernel_nonneg prob.w hr.2 y x))
        exact h1.trans (by nlinarith [hW_stab hr y])
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hAr_nn]
      calc |f y| * mehlerMean prob.w r rhoTil y
          ≤ |f y| * (C_hi * C' * euclideanWeight b d y) :=
            mul_le_mul_of_nonneg_left hAr_ub (abs_nonneg _)
        _ = (C_hi * C') * (|f y| * euclideanWeight b d y) := by ring
    · filter_upwards with y
      exact tendsto_const_nhds.mul (tendsto_mehlerMean_of_continuous_weight hrho_cont hC_hi_pos.le hrho_dom y)
  have hrho_target : ∫ y : RadialSpace prob.w, f y * rhoTil y ∂volume =
      ∫ x : RadialSpace prob.w, radialLiftReal prob.w g x ∂(rhoLift prob a) := by
    unfold rhoLift
    have hmeas : Measurable (fun x : RadialSpace prob.w =>
        ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.comp hrho_cont).measurable
    rw [integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [rhoTil]
    rw [ENNReal.toReal_ofReal (hrho_nn x), smul_eq_mul, mul_comm]
  rw [hrho_target] at hdom_tend
  exact hdom_tend.congr' hint_eval.symm

/-- Counting bound (`fw:counting` in `crossing_sum_rule.tex`): for any admissible crossing
measure `ν`, `ν([0, R]) ≤ C * (1 + √R)^w * exp(4π √(a R))` for all `R ≥ 0`. -/
theorem crossing_counting_bound (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) (meas : AdmissibleCrossingMeasure prob a) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      (meas.ν (Icc 0 R)).toReal ≤
        C * (1 + Real.sqrt R) ^ prob.w * Real.exp (4 * π * Real.sqrt (a * R)) := by
  let I₁ : ℝ := ∫ t in Ici 0, Real.exp (-2 * π * 1 * t) ∂meas.ν
  have hI₁_nn : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Ici fun _ _ => (Real.exp_pos _).le
  let c₀ : ℝ := max 1 (1 / Real.sqrt a)
  have hc₀_ge1 : 1 ≤ c₀ := le_max_left _ _
  have hc₀_sqrt : 1 / Real.sqrt a ≤ c₀ := le_max_right _ _
  let C : ℝ := c₀ ^ prob.w * (I₁ + 1) * Real.exp (2 * π * a)
  refine ⟨C, by positivity, fun R hR => ?_⟩
  let β : ℝ := Real.sqrt (a / (R + a))
  have hRa_pos : 0 < R + a := by linarith
  have hβ_pos : 0 < β := Real.sqrt_pos.mpr (div_pos ha_pos hRa_pos)
  have hβ_le1 : β ≤ 1 := Real.sqrt_le_one.mpr (div_le_one_of_le₀ (by linarith) hRa_pos.le)
  have hlap_β := meas.finite_laplace hβ_pos
  have hlap_inv := meas.finite_laplace (inv_pos.mpr hβ_pos)
  have hlap_1 := meas.finite_laplace one_pos
  have hcross := meas.crossing hβ_pos
  have hthermal_eq : ∫ t in Ici 0, thermalDiff prob.w β t ∂meas.ν =
      (∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν) -
        β ^ (-(prob.w : ℝ)) * ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂meas.ν := by
    have heq : (fun t => thermalDiff prob.w β t) = fun t =>
        Real.exp (-2 * π * β * t) - β ^ (-(prob.w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t) := by
      ext t; unfold thermalDiff; rw [div_eq_mul_inv]; ring_nf
    rw [heq, integral_sub hlap_β (hlap_inv.const_mul _), integral_const_mul]
  have hcardy_eq : ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t ≤
      β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) := by
    have h1 := prob.cardyV_laplace a hβ_pos
    have hV_nonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ prob.cardyV a t := fun t ht =>
      prob.cardyV_nonneg ha (Set.mem_Ioi.mp ht).le
    have hmono : ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t ≤
        ∫ t in Ioi 0, Real.exp (-2 * π * β * t) * prob.cardyDensity a t := by
      have hint_L : IntegrableOn (fun t => thermalDiff prob.w β t * prob.cardyDensity a t) (Ioi 0) := by
        refine (((thermalDiff_mem_TestClass prob ha hβ_pos).int_cardy).norm.const_mul (2 * π)).mono'
          (((by unfold thermalDiff; fun_prop : Continuous (thermalDiff prob.w β)).mul
            (by unfold FixedWeightProblem.cardyDensity; exact continuous_const.mul (continuous_cardyV prob a))).continuousOn.mono
              Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        unfold FixedWeightProblem.cardyDensity
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
          abs_of_nonneg (hV_nonneg t ht),
          Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hV_nonneg t ht))]
        ring_nf; rfl
      have hint_R : IntegrableOn (fun t => Real.exp (-2 * π * β * t) * prob.cardyDensity a t) (Ioi 0) := by
        have heq_r : (fun t => Real.exp (-2 * π * β * t) * prob.cardyDensity a t) =
            fun t => (2 * π) * (prob.cardyV a t * Real.exp (-2 * π * β * t)) := by
          ext t; unfold FixedWeightProblem.cardyDensity; ring
        rw [heq_r]
        exact h1.1.const_mul (2 * π)
      refine setIntegral_mono_on hint_L hint_R measurableSet_Ioi fun t ht => ?_
      have hcard_nn : 0 ≤ prob.cardyDensity a t := by
        unfold FixedWeightProblem.cardyDensity
        exact mul_nonneg (by positivity) (hV_nonneg t ht)
      refine mul_le_mul_of_nonneg_right ?_ hcard_nn
      unfold thermalDiff
      linarith [mul_nonneg (Real.rpow_nonneg hβ_pos.le (-(prob.w : ℝ)))
        (Real.exp_pos (-2 * π * t / β)).le]
    have hcard_lap : ∫ t in Ioi 0, Real.exp (-2 * π * β * t) * prob.cardyDensity a t =
        β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) := by
      have heq_l : (fun t => Real.exp (-2 * π * β * t) * prob.cardyDensity a t) =
          fun t => (2 * π) * (prob.cardyV a t * Real.exp (-2 * π * β * t)) := by
        ext t; unfold FixedWeightProblem.cardyDensity; ring
      rw [heq_l, integral_const_mul, h1.2]
    have hQ_le : prob.nullPoly (Real.exp (-2 * π / β)) ≤ 1 :=
      prob.nullPoly_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hβ_pos.le))
    calc ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t
        ≤ β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) :=
          hmono.trans_eq hcard_lap
      _ ≤ β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * 1 :=
          mul_le_mul_of_nonneg_left hQ_le (mul_nonneg (Real.rpow_nonneg hβ_pos.le _) (Real.exp_pos _).le)
      _ = β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) := mul_one _
  have hinv_le : ∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂meas.ν ≤ I₁ := by
    refine setIntegral_mono_on hlap_inv hlap_1 measurableSet_Ici fun t ht => ?_
    refine Real.exp_le_exp.mpr ?_
    have h1β : 1 ≤ β⁻¹ := one_le_inv₀ hβ_pos |>.mpr hβ_le1
    have ht_nn : 0 ≤ t := Set.mem_Ici.mp ht
    linarith [mul_le_mul_of_nonneg_left h1β (mul_nonneg (by positivity : 0 ≤ 2 * π) ht_nn)]
  have hIβ_le : ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν ≤
      β ^ (-(prob.w : ℝ)) * (I₁ + 1) * Real.exp (2 * π * a / β) := by
    have h1exp : 1 ≤ Real.exp (2 * π * a / β) := Real.one_le_exp (by positivity)
    calc ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν
        = β ^ (-(prob.w : ℝ)) * (∫ t in Ici 0, Real.exp (-2 * π * β⁻¹ * t) ∂meas.ν) +
            ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t := by linarith [hthermal_eq, hcross]
      _ ≤ β ^ (-(prob.w : ℝ)) * I₁ + β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) :=
          add_le_add (mul_le_mul_of_nonneg_left hinv_le (Real.rpow_nonneg hβ_pos.le _)) hcardy_eq
      _ ≤ β ^ (-(prob.w : ℝ)) * (I₁ * Real.exp (2 * π * a / β)) +
            β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) := by
          gcongr; exact le_mul_of_one_le_right hI₁_nn h1exp
      _ = β ^ (-(prob.w : ℝ)) * (I₁ + 1) * Real.exp (2 * π * a / β) := by ring
  have hmeas_lt_top : meas.ν (Icc 0 R) < ⊤ :=
    admissibleMeasure_Ici_sub_lt_top prob a meas Subset.rfl
  have hmass_lb : (meas.ν (Icc 0 R)).toReal * Real.exp (-2 * π * β * R) ≤
      ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
    have hmono1 : ∫ t in Icc 0 R, Real.exp (-2 * π * β * R) ∂meas.ν ≤
        ∫ t in Icc 0 R, Real.exp (-2 * π * β * t) ∂meas.ν :=
      setIntegral_mono_on (integrableOn_const (hs := hmeas_lt_top.ne))
        (hlap_β.mono_set Icc_subset_Ici_self) measurableSet_Icc fun t ht => by
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ 2 * π * β)
        linarith
    have hmono2 : ∫ t in Icc 0 R, Real.exp (-2 * π * β * t) ∂meas.ν ≤
        ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν :=
      setIntegral_mono_set hlap_β (Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (Eventually.of_forall fun _ h => Icc_subset_Ici_self h)
    simpa [setIntegral_const, smul_eq_mul, Measure.real] using hmono1.trans hmono2
  have hexp_bound : Real.exp (2 * π * β * R + 2 * π * a / β) ≤
      Real.exp (2 * π * a) * Real.exp (4 * π * Real.sqrt (a * R)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : β * R ≤ Real.sqrt (a * R) := by
      rcases eq_or_lt_of_le hR with rfl | hR_pos
      · simp
      · have hsub : β ≤ Real.sqrt (a / R) :=
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_left ha_pos.le hR_pos (by linarith))
        calc β * R ≤ Real.sqrt (a / R) * R := mul_le_mul_of_nonneg_right hsub hR
          _ = Real.sqrt (a / R) * Real.sqrt (R ^ 2) := by rw [Real.sqrt_sq hR]
          _ = Real.sqrt ((a / R) * R ^ 2) := by rw [← Real.sqrt_mul (by positivity)]
          _ = Real.sqrt (a * R) := by congr 1; field_simp
    have h2 : a / β ≤ Real.sqrt (a * R) + a := by
      have haβ : a / β = Real.sqrt (a * (R + a)) := by
        rw [div_eq_iff hβ_pos.ne']
        dsimp [β]
        rw [← Real.sqrt_mul (mul_nonneg ha_pos.le hRa_pos.le),
          show a * (R + a) * (a / (R + a)) = a ^ 2 by field_simp, Real.sqrt_sq ha_pos.le]
      have hsqrt_add : Real.sqrt (R + a) ≤ Real.sqrt R + Real.sqrt a := by
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg R) (Real.sqrt_nonneg a))]
        refine Real.sqrt_le_sqrt ?_
        rw [add_sq, Real.sq_sqrt hR, Real.sq_sqrt ha_pos.le]
        nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg a]
      calc a / β = Real.sqrt (a * (R + a)) := haβ
        _ = Real.sqrt a * Real.sqrt (R + a) := Real.sqrt_mul ha_pos.le _
        _ ≤ Real.sqrt a * (Real.sqrt R + Real.sqrt a) := mul_le_mul_of_nonneg_left hsqrt_add (Real.sqrt_nonneg a)
        _ = Real.sqrt a * Real.sqrt R + Real.sqrt a * Real.sqrt a := by ring
        _ = Real.sqrt (a * R) + a := by
            rw [← Real.sqrt_mul ha_pos.le R, Real.mul_self_sqrt ha_pos.le]
    have hadd := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0 ≤ 2 * π)
    linarith [show 2 * π * (β * R + a / β) = 2 * π * β * R + 2 * π * a / β by ring,
      show 2 * π * (Real.sqrt (a * R) + (Real.sqrt (a * R) + a)) =
        2 * π * a + 4 * π * Real.sqrt (a * R) by ring]
  have hβ_pow : β ^ (-(prob.w : ℝ)) ≤ c₀ ^ prob.w * (1 + Real.sqrt R) ^ prob.w := by
    have hinv_le1 : β⁻¹ ≤ c₀ * (1 + Real.sqrt R) := by
      have h1 : β⁻¹ = Real.sqrt ((R + a) / a) := by
        dsimp [β]
        rw [Real.sqrt_div ha_pos.le, inv_div, Real.sqrt_div hRa_pos.le]
      have hsqrt_add : Real.sqrt (R + a) ≤ Real.sqrt R + Real.sqrt a := by
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg R) (Real.sqrt_nonneg a))]
        refine Real.sqrt_le_sqrt ?_
        rw [add_sq, Real.sq_sqrt hR, Real.sq_sqrt ha_pos.le]
        nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg a]
      calc β⁻¹ = Real.sqrt (R + a) / Real.sqrt a := by
            rw [h1, Real.sqrt_div hRa_pos.le]
        _ ≤ (Real.sqrt R + Real.sqrt a) / Real.sqrt a :=
            div_le_div_of_nonneg_right hsqrt_add (Real.sqrt_nonneg a)
        _ = (1 / Real.sqrt a) * Real.sqrt R + 1 := by field_simp
        _ ≤ c₀ * Real.sqrt R + c₀ * 1 := by
            nlinarith [Real.sqrt_nonneg R]
        _ = c₀ * (1 + Real.sqrt R) := by ring
    rw [Real.rpow_neg hβ_pos.le, Real.rpow_natCast]
    calc (β ^ prob.w)⁻¹ = (β⁻¹) ^ prob.w := (inv_pow β prob.w).symm
      _ ≤ (c₀ * (1 + Real.sqrt R)) ^ prob.w := pow_le_pow_left₀ (by positivity) hinv_le1 _
      _ = c₀ ^ prob.w * (1 + Real.sqrt R) ^ prob.w := mul_pow _ _ _
  have hmul_exp : (meas.ν (Icc 0 R)).toReal ≤
      Real.exp (2 * π * β * R) * ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
    rw [← le_div_iff₀ (Real.exp_pos (-2 * π * β * R))] at hmass_lb
    calc (meas.ν (Icc 0 R)).toReal
        ≤ (∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν) / Real.exp (-2 * π * β * R) := hmass_lb
      _ = Real.exp (2 * π * β * R) * ∫ t in Ici 0, Real.exp (-2 * π * β * t) ∂meas.ν := by
          rw [div_eq_mul_inv, ← Real.exp_neg, show -(-2 * π * β * R) = 2 * π * β * R by ring,
            mul_comm]
  calc (meas.ν (Icc 0 R)).toReal
      ≤ Real.exp (2 * π * β * R) * (β ^ (-(prob.w : ℝ)) * (I₁ + 1) * Real.exp (2 * π * a / β)) :=
        hmul_exp.trans (mul_le_mul_of_nonneg_left hIβ_le (Real.exp_pos _).le)
    _ = β ^ (-(prob.w : ℝ)) * (I₁ + 1) * Real.exp (2 * π * β * R + 2 * π * a / β) := by
        rw [Real.exp_add]; ring
    _ ≤ (c₀ ^ prob.w * (1 + Real.sqrt R) ^ prob.w) * (I₁ + 1) *
          (Real.exp (2 * π * a) * Real.exp (4 * π * Real.sqrt (a * R))) := by
        gcongr
    _ = C * (1 + Real.sqrt R) ^ prob.w * Real.exp (4 * π * Real.sqrt (a * R)) := by
        dsimp [C]; ring

/-- Crossing sum rule (`Lemma FW-X`, part (1): one-sided crossing inequality `fw:crossing`).
Conditional on `MehlerOddMomentInput prob.w`. -/
theorem lemma_fwX_one_sided (prob : FixedWeightProblem)
    (hMehler : MehlerOddMomentInput prob.w)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a)
    (meas : AdmissibleCrossingMeasure prob a)
    {g : ℝ → ℝ} (hg : TestClass prob a g) {T : ℝ} (hT_nn : ∀ t, T ≤ t → 0 ≤ g t) :
    IntegrableOn g (Ici 0) meas.ν ∧
      prob.gVac a g + ∫ t in Ici 0, g t ∂meas.ν ≤ 0 := by
  have : SigmaFinite (nuLift prob a meas) := nuLift_sigmaFinite prob a meas
  have : SigmaFinite (rhoLift prob a) :=
    SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hν_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2)) (nuLift prob a meas) :=
    fun hε => nuLift_gauss prob a meas hε
  have hρ_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2)) (rhoLift prob a) :=
    fun hε => rhoLift_gauss prob ha ha_pos hε
  have h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace prob.w, radialLiftReal prob.w (thermalDiff prob.w β) x ∂(nuLift prob a meas) =
        ∫ x : RadialSpace prob.w, radialLiftReal prob.w (thermalDiff prob.w β) x ∂(rhoLift prob a) := by
    intro β hβ
    rw [integral_nuLift prob a meas (by unfold thermalDiff; fun_prop :
        Continuous (thermalDiff prob.w β)).continuousOn,
      integral_rhoLift prob ha, meas.crossing hβ]
  have hf_rho := integrable_rhoLift_of_cardy ha hg.cont hg.int_cardy
  have htend_rho := tendsto_mehlerMean_rhoLift prob ha ha_pos hg
  let R : ℝ := Real.sqrt (2 * max T 0)
  have hR_nn : 0 ≤ R := Real.sqrt_nonneg _
  have hneg_supp : ∀ y : RadialSpace prob.w, R < ‖y‖ → max (-radialLiftReal prob.w g y) 0 = 0 := by
    intro y hy
    have hsq : R ^ 2 < ‖y‖ ^ 2 := pow_lt_pow_left₀ hy hR_nn two_ne_zero
    rw [Real.sq_sqrt (by positivity)] at hsq
    have ht_ge : T ≤ ‖y‖ ^ 2 / 2 := le_trans (le_max_left T 0) (by linarith)
    have hgy_nn : 0 ≤ g (‖y‖ ^ 2 / 2) := hT_nn _ ht_ge
    change max (-g (‖y‖ ^ 2 / 2)) 0 = 0
    exact max_eq_right (by linarith)
  obtain ⟨hint_nu, hle⟩ := lemma_fwA_part2 hMehler (nuLift prob a meas) (rhoLift prob a)
    hν_gauss hρ_gauss h_thermal hg.cont hg.int_lift hg.fourier_odd hf_rho hR_nn hneg_supp htend_rho
  rw [integrable_nuLift_iff prob a meas hg.cont] at hint_nu
  rw [integral_nuLift prob a meas hg.cont, integral_rhoLift_eq_neg_gVac prob ha g] at hle
  exact ⟨hint_nu, by linarith⟩

/-- Crossing sum rule (`Lemma FW-X`, part (2): exact equality `fw:crossing` under decay `q > (w+1)/2`).
Conditional on `MehlerOddMomentInput prob.w`. -/
theorem lemma_fwX_equality (prob : FixedWeightProblem)
    (hMehler : MehlerOddMomentInput prob.w)
    {a : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a)
    (meas : AdmissibleCrossingMeasure prob a)
    {g : ℝ → ℝ} (hg : TestClass prob a g) {q C_g : ℝ}
    (hq : (prob.w + 1 : ℝ) / 2 < q) (hC_g : 0 ≤ C_g)
    (hdecay : ∀ t, 0 ≤ t → |g t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))) :
    IntegrableOn g (Ici 0) meas.ν ∧
      prob.gVac a g + ∫ t in Ici 0, g t ∂meas.ν = 0 := by
  have : SigmaFinite (nuLift prob a meas) := nuLift_sigmaFinite prob a meas
  have : SigmaFinite (rhoLift prob a) :=
    SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hν_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2)) (nuLift prob a meas) :=
    fun hε => nuLift_gauss prob a meas hε
  have hρ_gauss : ∀ {ε : ℝ}, 0 < ε →
      Integrable (fun x : RadialSpace prob.w => Real.exp (-ε * ‖x‖ ^ 2)) (rhoLift prob a) :=
    fun hε => rhoLift_gauss prob ha ha_pos hε
  have h_thermal : ∀ {β : ℝ}, 0 < β →
      ∫ x : RadialSpace prob.w, radialLiftReal prob.w (thermalDiff prob.w β) x ∂(nuLift prob a meas) =
        ∫ x : RadialSpace prob.w, radialLiftReal prob.w (thermalDiff prob.w β) x ∂(rhoLift prob a) := by
    intro β hβ
    rw [integral_nuLift prob a meas (by unfold thermalDiff; fun_prop :
        Continuous (thermalDiff prob.w β)).continuousOn,
      integral_rhoLift prob ha, meas.crossing hβ]
  let b : ℝ := -q
  let d : ℝ := -(2 * Real.sqrt 2 * π * Real.sqrt a)
  have hw1 : (1 : ℝ) ≤ (prob.w : ℝ) := by exact_mod_cast prob.hw
  have hq_gt1 : 1 < q := by linarith
  have hW_cont : Continuous (euclideanWeight b d : RadialSpace prob.w → ℝ) := by
    unfold euclideanWeight
    refine Continuous.mul (continuous_iff_continuousAt.mpr fun y =>
      ContinuousAt.rpow (continuousAt_const.add ((continuous_norm.pow 2).continuousAt))
        continuousAt_const (Or.inl (by positivity))) (by fun_prop)
  have hW_dom : ∀ x : RadialSpace prob.w,
      |radialLiftReal prob.w g x| ≤ (C_g * (2 : ℝ) ^ q) * euclideanWeight b d x := fun x => by
    let t : ℝ := ‖x‖ ^ 2 / 2
    have ht_nn : 0 ≤ t := by positivity
    have hdec := hdecay t ht_nn
    have hpow_le : (1 + t) ^ (-q) ≤ (2 : ℝ) ^ q * (1 + ‖x‖ ^ 2) ^ (-q) := by
      have h1 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + t) := by dsimp [t]; linarith
      have h2 : (2 * (1 + t)) ^ (-q) ≤ (1 + ‖x‖ ^ 2) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      rw [Real.mul_rpow two_pos.le (by positivity)] at h2
      calc (1 + t) ^ (-q) = (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * (1 + t) ^ (-q)) := by
            rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
        _ ≤ (2 : ℝ) ^ q * (1 + ‖x‖ ^ 2) ^ (-q) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos two_pos _).le
    have hexp_eq : -4 * π * Real.sqrt (a * t) = d * ‖x‖ := by
      dsimp [t, d]
      rw [show a * (‖x‖ ^ 2 / 2) = (a / 2) * ‖x‖ ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg x),
        Real.sqrt_div ha_pos.le]
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
      calc -4 * π * (Real.sqrt a / Real.sqrt 2 * ‖x‖)
          = -(2 * (Real.sqrt 2 * Real.sqrt 2) * π * (Real.sqrt a / Real.sqrt 2) * ‖x‖) := by
            rw [hsq2]; ring
        _ = -(2 * Real.sqrt 2 * π * Real.sqrt a) * ‖x‖ := by
            have hsq_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
            field_simp
    calc |radialLiftReal prob.w g x| = |g t| := rfl
      _ ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t)) := hdec
      _ ≤ C_g * ((2 : ℝ) ^ q * (1 + ‖x‖ ^ 2) ^ (-q)) * Real.exp (d * ‖x‖) := by
          rw [hexp_eq]
          gcongr
      _ = (C_g * (2 : ℝ) ^ q) * euclideanWeight b d x := by
          unfold euclideanWeight; dsimp [b]; ring
  have hW_nu : Integrable (euclideanWeight b d) (nuLift prob a meas) := by
    obtain ⟨C_N, hC_N_pos, hcount⟩ := crossing_counting_bound prob ha ha_pos meas
    let M_s : ℝ := (2 : ℝ) ^ prob.w * (2 : ℝ) ^ q * C_N * Real.exp (4 * π * Real.sqrt a)
    have hM_s_nn : 0 ≤ M_s :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_pos_of_pos two_pos q).le)
        hC_N_pos.le) (Real.exp_pos _).le
    let f_t : ℝ → ℝ := fun t => (1 + 2 * t) ^ (-q) * Real.exp (-4 * π * Real.sqrt (a * t))
    have hf_t_eq : ∀ t : ℝ, 0 ≤ t →
        euclideanWeight b d (embedRadial prob.w prob.hw t) = f_t t := fun t ht => by
      unfold euclideanWeight f_t
      rw [norm_embedRadial_sq prob.hw ht]
      dsimp [b, d]
      rw [show -4 * π * Real.sqrt (a * t) = -(2 * Real.sqrt 2 * π * Real.sqrt a) * Real.sqrt (2 * t) by
        rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul ha_pos.le]
        have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
        calc -4 * π * (Real.sqrt a * Real.sqrt t)
            = -(2 * (Real.sqrt 2 * Real.sqrt 2) * π * Real.sqrt a * Real.sqrt t) := by rw [hsq2]; ring
          _ = -(2 * Real.sqrt 2 * π * Real.sqrt a) * (Real.sqrt 2 * Real.sqrt t) := by ring]
      congr 2
      unfold embedRadial
      rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_euclidean_single_zero prob.w prob.hw,
        mul_one]
    have hshell : ∀ n : ℕ,
        ∫⁻ t in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν ≤
          ENNReal.ofReal (M_s * ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q)) := fun n => by
      have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hpow_le : ∀ t ∈ Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2),
          (1 + 2 * t) ^ (-q) ≤ (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ (-2 * q) := fun t ht => by
        have ht_nn : 0 ≤ t := le_trans (sq_nonneg _) ht.1
        have ht1 : ((n : ℝ) + 1) ^ 2 ≤ 2 * (1 + 2 * t) := by nlinarith [ht.1]
        have h1 : (2 * (1 + 2 * t)) ^ (-q) ≤ (((n : ℝ) + 1) ^ 2) ^ (-q) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) ht1 (by linarith)
        rw [Real.mul_rpow two_pos.le (by linarith : 0 ≤ 1 + 2 * t),
          ← Real.rpow_natCast ((n : ℝ) + 1) 2, ← Real.rpow_mul hn1_pos.le] at h1
        calc (1 + 2 * t) ^ (-q) = (2 : ℝ) ^ q * ((2 : ℝ) ^ (-q) * (1 + 2 * t) ^ (-q)) := by
              rw [← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
          _ ≤ (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ ((2 : ℝ) * (-q)) :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos two_pos _).le
          _ = (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ (-2 * q) := by congr 2; ring
      have hexp_le : ∀ t ∈ Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2),
          Real.exp (-4 * π * Real.sqrt (a * t)) ≤ Real.exp (-4 * π * Real.sqrt a * (n : ℝ)) := fun t ht => by
        refine Real.exp_le_exp.mpr ?_
        have hsqrt : (n : ℝ) ≤ Real.sqrt t := by
          rw [← Real.sqrt_sq hn_nn]; exact Real.sqrt_le_sqrt ht.1
        rw [Real.sqrt_mul ha_pos.le]
        have hmul_s : Real.sqrt a * (n : ℝ) ≤ Real.sqrt a * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg a)
        nlinarith [Real.pi_pos, hmul_s]
      let ub : ℝ := (2 : ℝ) ^ q * ((n : ℝ) + 1) ^ (-2 * q) * Real.exp (-4 * π * Real.sqrt a * (n : ℝ))
      have hub : ∀ t ∈ Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), f_t t ≤ ub := fun t ht =>
        mul_le_mul (hpow_le t ht) (hexp_le t ht) (Real.exp_pos _).le (by positivity)
      have hcount_n : meas.ν (Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2)) ≤
          ENNReal.ofReal (C_N * (2 : ℝ) ^ prob.w * ((n : ℝ) + 1) ^ (prob.w : ℝ) *
            Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1))) := by
        have h1 : meas.ν (Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2)) ≤
            meas.ν (Icc 0 (((n : ℝ) + 1) ^ 2)) := measure_mono fun t ht =>
          ⟨le_trans (sq_nonneg _) ht.1, ht.2.le⟩
        have hc := hcount (((n : ℝ) + 1) ^ 2) (sq_nonneg _)
        rw [Real.sqrt_sq hn1_pos.le] at hc
        have hc' : (meas.ν (Icc 0 (((n : ℝ) + 1) ^ 2))).toReal ≤
            C_N * (2 : ℝ) ^ prob.w * ((n : ℝ) + 1) ^ (prob.w : ℝ) *
              Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)) := by
          have h1n : (1 + ((n : ℝ) + 1)) ^ prob.w ≤ (2 * ((n : ℝ) + 1)) ^ prob.w :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have hexp_s : Real.sqrt (a * ((n : ℝ) + 1) ^ 2) = Real.sqrt a * ((n : ℝ) + 1) := by
            rw [Real.sqrt_mul ha_pos.le, Real.sqrt_sq hn1_pos.le]
          rw [hexp_s] at hc
          calc (meas.ν (Icc 0 (((n : ℝ) + 1) ^ 2))).toReal
              ≤ C_N * (1 + ((n : ℝ) + 1)) ^ prob.w * Real.exp (4 * π * (Real.sqrt a * ((n : ℝ) + 1))) := hc
            _ ≤ C_N * (2 * ((n : ℝ) + 1)) ^ prob.w * Real.exp (4 * π * (Real.sqrt a * ((n : ℝ) + 1))) := by gcongr
            _ = C_N * (2 : ℝ) ^ prob.w * ((n : ℝ) + 1) ^ (prob.w : ℝ) *
                  Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)) := by
                rw [mul_pow, Real.rpow_natCast]; ring
        have hlt_top := admissibleMeasure_Ici_sub_lt_top prob a meas (Subset.rfl :
          Icc 0 (((n : ℝ) + 1) ^ 2) ⊆ Icc 0 (((n : ℝ) + 1) ^ 2))
        exact h1.trans (ENNReal.le_ofReal_iff_toReal_le hlt_top.ne (by positivity) |>.mpr hc')
      calc ∫⁻ t in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν
          ≤ ∫⁻ _ in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal ub ∂meas.ν :=
            setLIntegral_mono' measurableSet_Ico fun t ht => ENNReal.ofReal_le_ofReal (hub t ht)
        _ = ENNReal.ofReal ub * meas.ν (Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2)) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal ub * ENNReal.ofReal (C_N * (2 : ℝ) ^ prob.w * ((n : ℝ) + 1) ^ (prob.w : ℝ) *
              Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1))) := by gcongr
        _ = ENNReal.ofReal (ub * (C_N * (2 : ℝ) ^ prob.w * ((n : ℝ) + 1) ^ (prob.w : ℝ) *
              Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (M_s * ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q)) := by
            congr 1
            have hexp_mul : Real.exp (-4 * π * Real.sqrt a * (n : ℝ)) *
                Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)) = Real.exp (4 * π * Real.sqrt a) := by
              rw [← Real.exp_add]; congr 1; ring
            have hpow_mul : ((n : ℝ) + 1) ^ (-2 * q) * ((n : ℝ) + 1) ^ (prob.w : ℝ) =
                ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q) := by
              rw [← Real.rpow_add hn1_pos]; congr 1; ring
            calc ub * (C_N * (2 : ℝ) ^ prob.w * ((n : ℝ) + 1) ^ (prob.w : ℝ) *
                    Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1)))
                = ((2 : ℝ) ^ prob.w * (2 : ℝ) ^ q * C_N) *
                    (Real.exp (-4 * π * Real.sqrt a * (n : ℝ)) *
                      Real.exp (4 * π * Real.sqrt a * ((n : ℝ) + 1))) *
                    (((n : ℝ) + 1) ^ (-2 * q) * ((n : ℝ) + 1) ^ (prob.w : ℝ)) := by
                  dsimp [ub]; ring
              _ = M_s * ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q) := by
                  rw [hexp_mul, hpow_mul]
    have hcov : Ici (0 : ℝ) ⊆ ⋃ n : ℕ, Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2) := fun t ht => by
      let n : ℕ := Nat.floor (Real.sqrt t)
      have hn_le : (n : ℝ) ≤ Real.sqrt t := Nat.floor_le (Real.sqrt_nonneg t)
      have hlt_n1 : Real.sqrt t < (n : ℝ) + 1 := Nat.lt_floor_add_one _
      refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
      · have := pow_le_pow_left₀ (Nat.cast_nonneg n) hn_le 2
        rwa [Real.sq_sqrt (Set.mem_Ici.mp ht)] at this
      · have := pow_lt_pow_left₀ hlt_n1 (Real.sqrt_nonneg t) two_ne_zero
        rwa [Real.sq_sqrt (Set.mem_Ici.mp ht)] at this
    have hsum_fin : Summable (fun n : ℕ => M_s * ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q)) := by
      have hpow_sum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q)) := by
        have heq_s : (fun n : ℕ => ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q)) =
            fun n => (((n + 1 : ℕ) : ℝ) ^ ((prob.w : ℝ) - 2 * q)) := by
          ext n; push_cast; rfl
        rw [heq_s]
        refine (summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) ^ ((prob.w : ℝ) - 2 * q))).mpr ?_
        exact Real.summable_nat_rpow.mpr (by linarith)
      exact hpow_sum.mul_left M_s
    unfold nuLift
    rw [integrable_map_measure hW_cont.aestronglyMeasurable (measurable_embedRadial prob.w prob.hw).aemeasurable]
    refine ⟨hW_cont.comp (continuous_embedRadial prob.w prob.hw) |>.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hcongr_e : (∫⁻ t in Ici 0, ‖(euclideanWeight b d ∘ embedRadial prob.w prob.hw) t‖ₑ ∂meas.ν) =
        ∫⁻ t in Ici 0, ENNReal.ofReal (f_t t) ∂meas.ν := by
      refine setLIntegral_congr_fun measurableSet_Ici (fun t ht => ?_)
      dsimp only [Function.comp_def]
      rw [Real.enorm_of_nonneg (euclideanWeight_pos _ _ _).le, hf_t_eq t (Set.mem_Ici.mp ht)]
    rw [hcongr_e]
    calc ∫⁻ t in Ici 0, ENNReal.ofReal (f_t t) ∂meas.ν
        ≤ ∫⁻ t in ⋃ n : ℕ, Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν :=
          lintegral_mono_set hcov
      _ ≤ ∑' n : ℕ, ∫⁻ t in Ico ((n : ℝ) ^ 2) (((n : ℝ) + 1) ^ 2), ENNReal.ofReal (f_t t) ∂meas.ν :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (M_s * ((n : ℝ) + 1) ^ ((prob.w : ℝ) - 2 * q)) :=
          ENNReal.tsum_le_tsum hshell
      _ < ⊤ := hsum_fin.tsum_ofReal_lt_top
  have hW_rho : Integrable (euclideanWeight b d) (rhoLift prob a) := by
    unfold rhoLift
    have hmeas : Measurable (fun x : RadialSpace prob.w =>
        ENNReal.ofReal (prob.rhoDensity a (‖x‖ ^ 2 / 2))) :=
      (ENNReal.continuous_ofReal.comp ((continuous_rhoDensity prob a).comp
        ((continuous_norm.pow 2).div_const 2))).measurable
    rw [integrable_withDensity_iff_integrable_smul' hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    obtain ⟨C_hi, hC_hi_pos, hrho_hi⟩ := prob.rhoDensity_le_cardyWeight ha ha_pos
    let b₀ : ℝ := -((prob.w - 1 : ℝ) / 2 + 1 / 4)
    let r_exp : ℝ := -q + (prob.w - 1 : ℝ) / 2 - 1 / 4
    have hr_lt : r_exp < -1 := by dsimp [r_exp]; linarith
    have hcont_12t : ∀ r : ℝ, ContinuousOn (fun t : ℝ => (1 + 2 * t) ^ r) (Ici 0) := fun r => by
      intro t ht
      have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
      exact ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).rpow
        continuousAt_const (Or.inl (by change 1 + 2 * t ≠ 0; linarith))).continuousWithinAt
    have hcont_cw : ContinuousOn (cardyWeight b d) (Ici 0) :=
      (hcont_12t b).mul (Real.continuous_exp.comp (continuous_const.mul
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)))).continuousOn
    have hint_t : IntegrableOn (fun t : ℝ => (1 + 2 * t) ^ r_exp) (Ioi (0 : ℝ)) := by
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
      refine IntegrableOn.union ?_ ?_
      · exact ((hcont_12t r_exp).mono (fun t ht => ht.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      · have h1 : IntegrableOn (fun t : ℝ => t ^ r_exp) (Ioi (1 : ℝ)) :=
          integrableOn_Ioi_rpow_of_lt hr_lt one_pos
        refine h1.mono' ((hcont_12t r_exp).mono (fun t ht =>
            le_trans zero_le_one (le_of_lt (Set.mem_Ioi.mp ht)))
            |>.aestronglyMeasurable measurableSet_Ioi) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 < t := Set.mem_Ioi.mp ht
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (hr_lt.le.trans (by norm_num))
    have hrad_int : Integrable (radialLift prob.w (fun t =>
        prob.rhoDensity a t * cardyWeight b d t)) := by
      rw [integrable_radialLift_iff prob.hw]
      refine (hint_t.const_mul C_hi).mono' ?_ ?_
      · refine (((continuous_id.pow (prob.w - 1)).continuousOn.mul
            ((continuous_rhoDensity prob a).continuousOn.mul hcont_cw)).mono Ioi_subset_Ici_self
          |>.aestronglyMeasurable measurableSet_Ioi)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht_pos : 0 < t := Set.mem_Ioi.mp ht
        have h1 := hrho_hi t ht_pos.le
        have hexp_cancel : Real.exp (2 * Real.sqrt 2 * π * Real.sqrt a * Real.sqrt (2 * t)) *
            Real.exp (d * Real.sqrt (2 * t)) = 1 := by
          rw [← Real.exp_add, show 2 * Real.sqrt 2 * π * Real.sqrt a * Real.sqrt (2 * t) +
            d * Real.sqrt (2 * t) = 0 by dsimp [d]; ring, Real.exp_zero]
        have ht_le_pow : t ^ (prob.w - 1) ≤ (1 + 2 * t) ^ ((prob.w : ℝ) - 1) := by
          rw [← Real.rpow_natCast t (prob.w - 1), Nat.cast_sub prob.hw, Nat.cast_one]
          exact Real.rpow_le_rpow ht_pos.le (by linarith) (by linarith)
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht_pos.le _)
          (mul_nonneg (prob.rhoDensity_nonneg ha ht_pos.le) (cardyWeight_pos b d ht_pos.le).le))]
        calc t ^ (prob.w - 1) * (prob.rhoDensity a t * cardyWeight b d t)
            ≤ (1 + 2 * t) ^ ((prob.w : ℝ) - 1) *
                (C_hi * cardyWeight b₀ (2 * Real.sqrt 2 * π * Real.sqrt a) t * cardyWeight b d t) :=
              mul_le_mul ht_le_pow (mul_le_mul_of_nonneg_right h1 (cardyWeight_pos b d ht_pos.le).le)
                (mul_nonneg (prob.rhoDensity_nonneg ha ht_pos.le) (cardyWeight_pos b d ht_pos.le).le)
                (by positivity)
          _ = C_hi * ((1 + 2 * t) ^ ((prob.w : ℝ) - 1) * ((1 + 2 * t) ^ b₀ * (1 + 2 * t) ^ b) *
                (Real.exp (2 * Real.sqrt 2 * π * Real.sqrt a * Real.sqrt (2 * t)) *
                  Real.exp (d * Real.sqrt (2 * t)))) := by
              unfold cardyWeight; ring
          _ = C_hi * (1 + 2 * t) ^ r_exp := by
              rw [hexp_cancel, mul_one, ← Real.rpow_add (by linarith : 0 < 1 + 2 * t),
                ← Real.rpow_add (by linarith : 0 < 1 + 2 * t)]
              congr 2; dsimp [r_exp, b₀, b]; ring
    refine ((integrable_radialLift_iff_real prob.w _).mp hrad_int).congr
      (Eventually.of_forall fun x => ?_)
    dsimp only [radialLiftReal]
    rw [ENNReal.toReal_ofReal (prob.rhoDensity_nonneg ha (by positivity)), smul_eq_mul,
      ← euclideanWeight_eq_cardyWeight b d x]
  obtain ⟨hint_nu, _, heq⟩ := lemma_fwA_part3 hMehler (nuLift prob a meas) (rhoLift prob a)
    hν_gauss hρ_gauss h_thermal hg.cont hg.int_lift hg.fourier_odd (C := C_g * (2 : ℝ) ^ q)
    (b := b) (d := d) (by positivity) hW_dom hW_nu hW_rho
  rw [integrable_nuLift_iff prob a meas hg.cont] at hint_nu
  rw [integral_nuLift prob a meas hg.cont, integral_rhoLift_eq_neg_gVac prob ha g] at heq
  exact ⟨hint_nu, by linarith⟩

noncomputable def spectrumMeasure (prob : FixedWeightProblem) (a : ℝ)
    (spec : AdmissibleSpectrum prob a) : Measure ℝ :=
  Measure.sum fun n : spec.ι => ENNReal.ofReal (spec.d n) • Measure.dirac (spec.t n)

lemma spectrumMeasure_Iio_eq_zero (prob : FixedWeightProblem) {a : ℝ}
    (spec : AdmissibleSpectrum prob a) (ht_nn : ∀ n : spec.ι, 0 ≤ spec.t n) :
    spectrumMeasure prob a spec (Iio 0) = 0 := by
  unfold spectrumMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  have h0 : ∀ n : spec.ι, (ENNReal.ofReal (spec.d n) • Measure.dirac (spec.t n)) (Iio 0) = 0 := by
    intro n
    have hnot : spec.t n ∉ Iio (0 : ℝ) := not_lt.mpr (ht_nn n)
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply (spec.t n) (Iio 0),
      Set.indicator_of_notMem hnot 1, mul_zero]
  simp [h0]

/-- Convert an `AdmissibleSpectrum` whose primary parameters satisfy `0 ≤ spec.t n`
into an `AdmissibleCrossingMeasure`. -/
noncomputable def AdmissibleSpectrum.toAdmissibleCrossingMeasure (prob : FixedWeightProblem) {a : ℝ}
    (_ha : prob.totalShift ≤ a) (spec : AdmissibleSpectrum prob a)
    (ht_nn : ∀ n : spec.ι, 0 ≤ spec.t n) : AdmissibleCrossingMeasure prob a :=
  letI := spec.countable_ι
  have hrestrict : (spectrumMeasure prob a spec).restrict (Ici 0) = spectrumMeasure prob a spec := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, show {a : ℝ | a ∉ Ici 0} = Iio 0 by ext t; simp]
    exact spectrumMeasure_Iio_eq_zero prob spec ht_nn
  have hd_ne_top : ∀ n : spec.ι, ENNReal.ofReal (spec.d n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  { ν := spectrumMeasure prob a spec
    supp_nonneg := spectrumMeasure_Iio_eq_zero prob spec ht_nn
    finite_laplace := fun {β} hβ => by
      dsimp [IntegrableOn]
      rw [hrestrict]
      unfold spectrumMeasure
      refine integrable_sum_dirac hd_ne_top ?_
      have heq_f : (fun n : spec.ι => (ENNReal.ofReal (spec.d n)).toReal * ‖Real.exp (-2 * π * β * spec.t n)‖) =
          fun n => spec.d n * Real.exp (-2 * π * β * spec.t n) := by
        ext n
        rw [ENNReal.toReal_ofReal (spec.hd_pos n).le, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [heq_f]
      exact spec.summable_thermal hβ
    crossing := fun {β} hβ => by
      rw [hrestrict]
      unfold spectrumMeasure
      rw [integral_sum_dirac hd_ne_top]
      have hs1 := spec.summable_thermal hβ
      have hs2 := (spec.summable_thermal (inv_pos.mpr hβ)).mul_left (β ^ (-(prob.w : ℝ)))
      have hsum_eq : (∑' n : spec.ι, (ENNReal.ofReal (spec.d n)).toReal • thermalDiff prob.w β (spec.t n)) =
          (∑' n : spec.ι, spec.d n * Real.exp (-2 * π * β * spec.t n)) -
            β ^ (-(prob.w : ℝ)) * ∑' n : spec.ι, spec.d n * Real.exp (-2 * π * (spec.t n) / β) := by
        have heq_t : (fun n : spec.ι => (ENNReal.ofReal (spec.d n)).toReal • thermalDiff prob.w β (spec.t n)) =
            fun n => spec.d n * Real.exp (-2 * π * β * spec.t n) -
              β ^ (-(prob.w : ℝ)) * (spec.d n * Real.exp (-2 * π * (spec.t n) / β)) := by
          ext n
          rw [ENNReal.toReal_ofReal (spec.hd_pos n).le, smul_eq_mul]
          unfold thermalDiff; ring
        have hs2' : Summable (fun n : spec.ι =>
            β ^ (-(prob.w : ℝ)) * (spec.d n * Real.exp (-2 * π * (spec.t n) / β))) := by
          have heq2 : (fun n : spec.ι => β ^ (-(prob.w : ℝ)) * (spec.d n * Real.exp (-2 * π * (spec.t n) / β))) =
              fun n => β ^ (-(prob.w : ℝ)) * (spec.d n * Real.exp (-2 * π * β⁻¹ * spec.t n)) := by
            ext n; congr 2; congr 1; ring
          rw [heq2]
          exact hs2
        rw [heq_t, Summable.tsum_sub hs1 hs2', tsum_mul_left]
      have hcross_spec := spec.crossing hβ
      have hvac_eq : ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t =
          -prob.gVac a (thermalDiff prob.w β) := by
        unfold FixedWeightProblem.gVac FixedWeightProblem.cardyDensity
        have heq_c : (fun t => thermalDiff prob.w β t * (2 * π * prob.cardyV a t)) =
            fun t => (2 * π) * (thermalDiff prob.w β t * prob.cardyV a t) := by ext t; ring
        rw [heq_c, integral_const_mul]; ring
      rw [hsum_eq, hvac_eq, prob.gVac_thermalDiff a hβ]
      linarith }

/-- Crossing certification (`Theorem FW-C`, `fw:FWC` in `crossing_sum_rule.tex`):
if `g ∈ TestClass prob a` is feasible at gap `T > 0` (`gVac > 0` and `g ≥ 0` on `[T, ∞)`),
then every admissible crossing-symmetric spectrum has a non-vacuum primary with `t_n < T`
(so `Δ_n < a + T`). Conditional on `MehlerOddMomentInput prob.w`. -/
theorem theorem_fwC (prob : FixedWeightProblem)
    (hMehler : MehlerOddMomentInput prob.w)
    {a T : ℝ} (ha : prob.totalShift ≤ a) (ha_pos : 0 < a) (hT : 0 < T)
    {g : ℝ → ℝ} (hg : prob.IsFeasible a T g) (spec : AdmissibleSpectrum prob a) :
    ∃ n : spec.ι, spec.t n < T := by
  by_contra hnone
  push Not at hnone
  have ht_nn : ∀ n : spec.ι, 0 ≤ spec.t n := fun n => hT.le.trans (hnone n)
  let meas := spec.toAdmissibleCrossingMeasure prob ha ht_nn
  obtain ⟨_, hle⟩ := lemma_fwX_one_sided prob hMehler ha ha_pos meas hg.1 hg.2.2
  have : Countable spec.ι := spec.countable_ι
  have hrestrict : meas.ν.restrict (Ici 0) = meas.ν := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, show {a : ℝ | a ∉ Ici 0} = Iio 0 by ext t; simp]
    exact meas.supp_nonneg
  have hnonneg_int : 0 ≤ ∫ t in Ici 0, g t ∂meas.ν := by
    rw [hrestrict]
    dsimp [meas, AdmissibleSpectrum.toAdmissibleCrossingMeasure, spectrumMeasure]
    rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
    refine tsum_nonneg fun n => ?_
    rw [ENNReal.toReal_ofReal (spec.hd_pos n).le, smul_eq_mul]
    exact mul_nonneg (spec.hd_pos n).le (hg.2.2 _ (hnone n))
  linarith [hg.2.1]

/-- Spectral gap bound via `T_V`: for any admissible crossing-symmetric spectrum at `a = cTilde / 12`
(`12 * totalShift ≤ cTilde`, `0 < cTilde`), if `∀ n, T_gap ≤ spec.t n` then `T_gap ≤ T_V cTilde`.
Conditional on `MehlerOddMomentInput prob.w`. -/
theorem theorem_fwC_le_T_V (prob : FixedWeightProblem)
    (hMehler : MehlerOddMomentInput prob.w)
    {cTilde T_gap : ℝ} (hc : 12 * prob.totalShift ≤ cTilde) (hc_pos : 0 < cTilde)
    (spec : AdmissibleSpectrum prob (cTilde / 12)) (hgap : ∀ n : spec.ι, T_gap ≤ spec.t n) :
    T_gap ≤ prob.T_V cTilde := by
  unfold FixedWeightProblem.T_V
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha_pos : 0 < cTilde / 12 := by linarith
  refine le_csInf (prob.feasible_nonempty hc) ?_
  rintro T ⟨hT, g, hg⟩
  obtain ⟨n, hn⟩ := theorem_fwC prob hMehler ha ha_pos hT hg spec
  exact (hgap n).trans hn.le

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part1

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part2

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwA_part3

/-- info: 'FormalResearch.ModularBootstrap.Crossing.crossing_counting_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.crossing_counting_bound

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwX_one_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwX_one_sided

/-- info: 'FormalResearch.ModularBootstrap.Crossing.lemma_fwX_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.lemma_fwX_equality

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_fwC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_fwC

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_fwC_le_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_fwC_le_T_V

end FormalResearch.ModularBootstrap.Crossing




