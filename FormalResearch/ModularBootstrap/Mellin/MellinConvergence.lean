module

public import FormalResearch.ModularBootstrap.ComplexBessel.LemmaS2
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Convergence and Holomorphy of the Mellin Transform `Mg` and `m_g` (Lemma S1, first part)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S1 (`vlo:S1`), first part.

For `2 ≤ a` (`a = c'/12` with `24 ≤ c'`) and every `g ∈ TestClass virasoroProblem a`:
* `besselVCoeff_ge_positive`: `besselVCoeff a k > 0` for every `k ≥ 2`, giving polynomial
  domination `t^r ≤ (besselVCoeff a n)⁻¹ V(t)` on `[1, ∞)` for `r ≤ n` (`n ≥ 2`);
* `integrableOn_mellinTransformG`: `t ↦ (g t : ℂ) * (t : ℂ) ^ (z - 1)` is integrable on `(0, ∞)`
  for every `z : ℂ` with `0 < z.re` (splitting at `t = 1` using `lemmaB_b_sup` on `(0, 1]` and
  `V`-domination on `(1, ∞)`);
* `mellinTransformG_head_bound`: `∫ t in Ioc 0 1, ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤ (8 / π) * M[g] / z.re`;
* `differentiableOn_mellinTransformG`, `analyticOnNhd_mellinTransformG`:
  `mellinTransformG g` is holomorphic on `{z : ℂ | 0 < z.re}`;
* `differentiableOn_mellinMG`, `analyticOnNhd_mellinMG`:
  `mellinMG g` is holomorphic on `{z : ℂ | 0 < z.re}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Mellin

open Crossing Bessel Integration ComplexBessel

/-! ### Section 1: Positivity of all `V`-coefficients `v_k` (`k ≥ 2`) and large-`t` domination -/

private lemma pow_add_one_sub_ge_one {x : ℝ} (hx : 1 ≤ x) :
    ∀ k : ℕ, 1 ≤ k → 1 ≤ (x + 1) ^ k - x ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hpow_ge : 1 ≤ x ^ m := one_le_pow₀ hx
    have hpow_le : x ^ m ≤ (x + 1) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have hx_nn : 0 ≤ x := by linarith
    calc (1 : ℝ) ≤ (x + 1) ^ m - x ^ m := ih
      _ ≤ x * ((x + 1) ^ m - x ^ m) + (x + 1) ^ m := by nlinarith
      _ = (x + 1) ^ (m + 1) - x ^ (m + 1) := by ring

private lemma second_difference_pow_ge_two {b : ℝ} (hb : 0 ≤ b) :
    ∀ k : ℕ, 2 ≤ k → 2 ≤ (b + 2) ^ k - 2 * (b + 1) ^ k + b ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => linarith
  | succ m hm ih =>
    have hm1 : 1 ≤ m := by omega
    have h1 : 1 ≤ (b + 2) ^ m - (b + 1) ^ m := by
      have h := pow_add_one_sub_ge_one (x := b + 1) (by linarith) m hm1
      simpa [show b + 1 + 1 = b + 2 by ring] using h
    have h2 : (b + 2) ^ (m + 1) - 2 * (b + 1) ^ (m + 1) + b ^ (m + 1) =
        b * ((b + 2) ^ m - 2 * (b + 1) ^ m + b ^ m) + 2 * ((b + 2) ^ m - (b + 1) ^ m) := by
      ring
    rw [h2]
    nlinarith

/-- For `2 ≤ a` and `2 ≤ k`, `besselVCoeff a k ≥ 2 * (4π²)^k / (k!)² > 0`. -/
theorem besselVCoeff_pos {a : ℝ} (ha : 2 ≤ a) {k : ℕ} (hk : 2 ≤ k) :
    0 < besselVCoeff a k := by
  unfold besselVCoeff
  have h2 : 2 ≤ a ^ k - 2 * (a - 1) ^ k + (a - 2) ^ k := by
    have h := second_difference_pow_ge_two (b := a - 2) (by linarith) k hk
    simpa [show a - 2 + 2 = a by ring, show a - 2 + 1 = a - 1 by ring] using h
  have hc_pos : 0 < (4 * Real.pi ^ 2) ^ k / ((k ! : ℝ) ^ 2) := by positivity
  nlinarith

/-- For `2 ≤ a`, `0 ≤ t`, and `2 ≤ k`, `besselVCoeff a k * t ^ k ≤ virasoroProblem.cardyV a t`. -/
theorem besselVCoeff_mul_pow_le_cardyV {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) (k : ℕ) :
    besselVCoeff a k * t ^ k ≤ virasoroProblem.cardyV a t := by
  rw [virasoro_cardyV_eq_besselV ha ht]
  exact le_hasSum (besselV_hasSum ha ht) k fun j _ =>
    mul_nonneg (besselVCoeff_nonneg ha j) (pow_nonneg ht j)

/-- On `[1, ∞)`, any real power `t ^ r` is dominated by `(besselVCoeff a n)⁻¹ * cardyV a t`
for any `n ≥ 2` with `r ≤ n`. -/
theorem rpow_le_inv_besselVCoeff_mul_cardyV {a t r : ℝ} (ha : 2 ≤ a) (ht : 1 ≤ t)
    {n : ℕ} (hn : 2 ≤ n) (hrn : r ≤ (n : ℝ)) :
    t ^ r ≤ (besselVCoeff a n)⁻¹ * virasoroProblem.cardyV a t := by
  have ht0 : 0 ≤ t := by linarith
  have hv_pos : 0 < besselVCoeff a n := besselVCoeff_pos ha hn
  have h1 : t ^ r ≤ t ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hrn
  rw [Real.rpow_natCast] at h1
  have h2 : besselVCoeff a n * t ^ n ≤ virasoroProblem.cardyV a t :=
    besselVCoeff_mul_pow_le_cardyV ha ht0 n
  rw [← le_mul_inv_iff₀' hv_pos] at h2
  calc t ^ r ≤ t ^ n := h1
    _ ≤ (besselVCoeff a n)⁻¹ * virasoroProblem.cardyV a t := by
        simpa [mul_comm] using h2

/-! ### Section 2: Convergence of `Mg(z)` on `0 < Re z` -/

private lemma mellin_integrand_aestronglyMeasurable {a : ℝ} {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1))
      (volume.restrict (Ioi 0)) := by
  have hcont_g : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
  have hcont_pow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Ioi 0) := by
    intro t ht
    have hne : (t : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using mem_Ioi.mp ht))
    exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const hne).continuousWithinAt
  exact (hcont_g.mul hcont_pow).aestronglyMeasurable measurableSet_Ioi

private lemma norm_mellin_integrand_eq {g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ = |g t| * t ^ (z.re - 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re]

private lemma integrableOn_rpow_sub_one_Ioc {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1)) (Ioc 0 1) := by
  rw [← integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r - 1))

/-- Uniform domination on `Ioc 0 1` for `r₁ ≤ z.re`: `|g t| * t ^ (z.re - 1) ≤ (8/π) M[g] t ^ (r₁ - 1)`. -/
private lemma integrableOn_mellin_head {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {r₁ : ℝ} (hr₁ : 0 < r₁)
    {z : ℂ} (hz : r₁ ≤ z.re) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc 0 1) := by
  have hdom : IntegrableOn (fun t : ℝ => (8 / Real.pi * virasoroProblem.cardyNorm a g) * t ^ (r₁ - 1))
      (Ioc 0 1) :=
    (integrableOn_rpow_sub_one_Ioc hr₁).const_mul _
  refine hdom.mono' ((mellin_integrand_aestronglyMeasurable hg z).mono_set Ioc_subset_Ioi_self) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rw [norm_mellin_integrand_eq ht0 z]
  have hg_bd : |g t| ≤ 8 / Real.pi * virasoroProblem.cardyNorm a g :=
    lemmaB_b_sup ha hg ht0.le
  have hpow_le : t ^ (z.re - 1) ≤ t ^ (r₁ - 1) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
  have hM_nn : 0 ≤ virasoroProblem.cardyNorm a g :=
    virasoroProblem.cardyNorm_nonneg (by rw [virasoroProblem_totalShift]; exact ha) g
  exact mul_le_mul hg_bd hpow_le (Real.rpow_nonneg ht0.le _) (by positivity)

/-- Domination on `Ioi 1` by `|g t| * V(t)` for `z.re ≤ r₂`. -/
private lemma integrableOn_mellin_tail {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {r₂ : ℝ} {z : ℂ} (hz : z.re ≤ r₂) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 1) := by
  let n : ℕ := max 2 ⌈r₂⌉₊
  have hn2 : 2 ≤ n := le_max_left _ _
  have hrn : z.re - 1 ≤ (n : ℝ) := by
    have h1 : r₂ ≤ ⌈r₂⌉₊ := Nat.le_ceil r₂
    have h2 : (⌈r₂⌉₊ : ℝ) ≤ n := by exact_mod_cast le_max_right 2 ⌈r₂⌉₊
    linarith
  have hv_pos : 0 < besselVCoeff a n := besselVCoeff_pos ha hn2
  have hdom : IntegrableOn (fun t : ℝ => (besselVCoeff a n)⁻¹ * (|g t| * virasoroProblem.cardyV a t))
      (Ioi 1) :=
    (hg.int_cardy.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
  refine hdom.mono' ((mellin_integrand_aestronglyMeasurable hg z).mono_set (Ioi_subset_Ioi zero_le_one)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
  have ht0 : 0 < t := by linarith
  rw [norm_mellin_integrand_eq ht0 z]
  have hpow := rpow_le_inv_besselVCoeff_mul_cardyV ha ht1 hn2 hrn
  calc |g t| * t ^ (z.re - 1)
      ≤ |g t| * ((besselVCoeff a n)⁻¹ * virasoroProblem.cardyV a t) := by
        gcongr
    _ = (besselVCoeff a n)⁻¹ * (|g t| * virasoroProblem.cardyV a t) := by ring

/-- **Convergence of `Mg(z)` on `Re z > 0`** (`vlo:S1`):
for `2 ≤ a`, `g ∈ TestClass virasoroProblem a`, and `0 < z.re`,
the Mellin integrand `g(t) t^{z-1}` is integrable on `(0, ∞)`. -/
theorem integrableOn_mellinTransformG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (integrableOn_mellin_head ha hg hz le_rfl).union (integrableOn_mellin_tail ha hg le_rfl)

/-- Norm integrability of `g(t) t^{z-1}` on `(0, ∞)` for `0 < z.re`. -/
theorem integrableOn_abs_mellinTransformG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => |g t| * t ^ (r - 1)) (Ioi 0) := by
  have hint : IntegrableOn (fun t : ℝ => ‖(g t : ℂ) * (t : ℂ) ^ ((r : ℂ) - 1)‖) (Ioi 0) :=
    (integrableOn_mellinTransformG ha hg (z := (r : ℂ)) (by simpa using hr)).norm
  refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact norm_mellin_integrand_eq (mem_Ioi.mp ht) (r : ℂ)

/-- Paper's head bound (`vlo:S1` proof): `∫₀¹ |g(t)| t^{Re z - 1} dt ≤ (8/π) M[g] / Re z`. -/
theorem mellinTransformG_head_bound {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioc (0 : ℝ) 1, |g t| * t ^ (z.re - 1) ≤
      (8 / Real.pi * virasoroProblem.cardyNorm a g) / z.re := by
  have hhead : IntegrableOn (fun t : ℝ => |g t| * t ^ (z.re - 1)) (Ioc 0 1) := by
    have h : IntegrableOn (fun t : ℝ => ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖) (Ioc 0 1) :=
      (integrableOn_mellin_head ha hg hz le_rfl).norm
    exact h.congr_fun (fun t ht => norm_mellin_integrand_eq ht.1 z) measurableSet_Ioc
  have hrpow_int : IntegrableOn (fun t : ℝ => t ^ (z.re - 1)) (Ioc 0 1) :=
    integrableOn_rpow_sub_one_Ioc hz
  have hrpow_val : ∫ t in Ioc (0 : ℝ) 1, t ^ (z.re - 1) = 1 / z.re := by
    rw [← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith : -1 < z.re - 1))]
    simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hz.ne', sub_zero, one_div]
  calc ∫ t in Ioc (0 : ℝ) 1, |g t| * t ^ (z.re - 1)
      ≤ ∫ t in Ioc (0 : ℝ) 1, (8 / Real.pi * virasoroProblem.cardyNorm a g) * t ^ (z.re - 1) := by
        refine setIntegral_mono_on hhead (hrpow_int.const_mul _) measurableSet_Ioc fun t ht => ?_
        have hg_bd := lemmaB_b_sup ha hg ht.1.le
        exact mul_le_mul_of_nonneg_right hg_bd (Real.rpow_nonneg ht.1.le _)
    _ = (8 / Real.pi * virasoroProblem.cardyNorm a g) * ∫ t in Ioc (0 : ℝ) 1, t ^ (z.re - 1) :=
        integral_const_mul _ _
    _ = (8 / Real.pi * virasoroProblem.cardyNorm a g) / z.re := by
        rw [hrpow_val]; ring

/-! ### Section 3: Holomorphy of `Mg(z)` and `m_g(z)` on `0 < Re z` -/

private lemma neg_log_mul_rpow_le_inv {t ε : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
    (-Real.log t) * t ^ ε ≤ ε⁻¹ := by
  have hu0 : 0 < t ^ ε := Real.rpow_pos_of_pos ht0 ε
  have hu1 : t ^ ε ≤ 1 := Real.rpow_le_one ht0.le ht1 hε.le
  have hlog : -Real.log (t ^ ε) ≤ (t ^ ε)⁻¹ := by
    rw [← Real.log_inv]
    exact (Real.log_le_sub_one_of_pos (inv_pos.mpr hu0)).trans (by linarith)
  have hmul : (-Real.log (t ^ ε)) * t ^ ε ≤ 1 := by
    calc (-Real.log (t ^ ε)) * t ^ ε ≤ (t ^ ε)⁻¹ * t ^ ε := by gcongr
      _ = 1 := inv_mul_cancel₀ hu0.ne'
  have hlog_pow : Real.log (t ^ ε) = ε * Real.log t := Real.log_rpow ht0 ε
  rw [hlog_pow] at hmul
  calc (-Real.log t) * t ^ ε = ε⁻¹ * (-(ε * Real.log t) * t ^ ε) := by
        field_simp [hε.ne']
    _ ≤ ε⁻¹ * 1 := by gcongr
    _ = ε⁻¹ := mul_one _

private lemma log_le_self_of_one_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ t := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
  linarith

/-- Derivative formula for `mellinTransformG g` on `0 < z.re`. -/
theorem hasDerivAt_mellinTransformG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (mellinTransformG g)
      (∫ t in Ioi (0 : ℝ), (g t : ℂ) * ((t : ℂ) ^ (z₀ - 1) * Complex.log (t : ℂ))) z₀ := by
  let δ : ℝ := z₀.re / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let F : ℂ → ℝ → ℂ := fun z t => (g t : ℂ) * (t : ℂ) ^ (z - 1)
  let F' : ℂ → ℝ → ℂ := fun z t => (g t : ℂ) * ((t : ℂ) ^ (z - 1) * Complex.log (t : ℂ))
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) :=
    mellin_integrand_aestronglyMeasurable hg
  have hF_int : Integrable (F z₀) (volume.restrict (Ioi 0)) :=
    integrableOn_mellinTransformG ha hg hz₀
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioi 0)) := by
    have hcont_g : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn (hg.cont.mono Ioi_subset_Ici_self)
    have hcont_pow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z₀ - 1)) (Ioi 0) := by
      intro t ht
      have hne : (t : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using mem_Ioi.mp ht))
      exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const hne).continuousWithinAt
    have hcont_log : ContinuousOn (fun t : ℝ => Complex.log (t : ℂ)) (Ioi 0) := by
      have heq : EqOn (fun t : ℝ => Complex.log (t : ℂ)) (fun t : ℝ => (Real.log t : ℂ)) (Ioi 0) :=
        fun t ht => (Complex.ofReal_log (mem_Ioi.mp ht).le).symm
      exact (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun t ht => (mem_Ioi.mp ht).ne')).congr heq
    exact (hcont_g.mul (hcont_pow.mul hcont_log)).aestronglyMeasurable measurableSet_Ioi
  let n : ℕ := max 2 ⌈z₀.re + δ⌉₊
  have hn2 : 2 ≤ n := le_max_left _ _
  have hv_pos : 0 < besselVCoeff a n := besselVCoeff_pos ha hn2
  let M : ℝ := virasoroProblem.cardyNorm a g
  have hM_nn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg (by rw [virasoroProblem_totalShift]; exact ha) g
  let C_head : ℝ := (8 / Real.pi * M) * δ⁻¹
  let bound : ℝ → ℝ := fun t =>
    if t ≤ 1 then C_head * t ^ (δ - 1)
    else (besselVCoeff a n)⁻¹ * (|g t| * virasoroProblem.cardyV a t)
  have hbound_int : IntegrableOn bound (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    refine IntegrableOn.union ?_ ?_
    · have hhead : IntegrableOn (fun t : ℝ => C_head * t ^ (δ - 1)) (Ioc 0 1) :=
        (integrableOn_rpow_sub_one_Ioc hδ).const_mul _
      exact hhead.congr_fun (fun t ht => by simp [bound, ht.2]) measurableSet_Ioc
    · have htail : IntegrableOn (fun t : ℝ => (besselVCoeff a n)⁻¹ * (|g t| * virasoroProblem.cardyV a t))
          (Ioi 1) := (hg.int_cardy.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
      exact htail.congr_fun (fun t ht => by
        have hnot : ¬ t ≤ 1 := not_le.mpr (mem_Ioi.mp ht)
        simp [bound, hnot]) measurableSet_Ioi
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball z₀ δ,
      ‖F' z t‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht z hz => ?_
    have ht0 : 0 < t := mem_Ioi.mp ht
    have hz_ball : ‖z - z₀‖ < δ := dist_eq_norm z z₀ ▸ Metric.mem_ball.mp hz
    have hre_diff : |z.re - z₀.re| < δ := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      simpa using h1.trans_lt hz_ball
    have hz_lo : 2 * δ ≤ z.re := by dsimp [δ] at *; linarith [(abs_lt.mp hre_diff).1]
    have hz_hi : z.re ≤ z₀.re + δ := by linarith [(abs_lt.mp hre_diff).2]
    have hlog_norm : ‖Complex.log (t : ℂ)‖ = |Real.log t| := by
      rw [← Complex.ofReal_log ht0.le, Complex.norm_real, Real.norm_eq_abs]
    have hnorm : ‖F' z t‖ = |g t| * t ^ (z.re - 1) * |Real.log t| := by
      dsimp [F']
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re, hlog_norm]
      ring
    rw [hnorm]
    by_cases ht1 : t ≤ 1
    · simp only [bound, ht1, ↓reduceIte]
      have hg_bd : |g t| ≤ 8 / Real.pi * M := lemmaB_b_sup ha hg ht0.le
      have hlog_abs : |Real.log t| = -Real.log t := abs_of_nonpos (Real.log_nonpos ht0.le ht1)
      have hpow_le : t ^ (z.re - 1) ≤ t ^ (2 * δ - 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
      have hsplit_pow : t ^ (2 * δ - 1) = t ^ δ * t ^ (δ - 1) := by
        rw [← Real.rpow_add ht0]; congr 1; ring
      have hlog_bd : (-Real.log t) * t ^ δ ≤ δ⁻¹ := neg_log_mul_rpow_le_inv ht0 ht1 hδ
      have hneg_log : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht0.le ht1)
      have hpow_nn : 0 ≤ t ^ (δ - 1) := Real.rpow_nonneg ht0.le _
      rw [hlog_abs]
      calc |g t| * t ^ (z.re - 1) * (-Real.log t)
          ≤ (8 / Real.pi * M) * t ^ (2 * δ - 1) * (-Real.log t) := by
            gcongr
        _ = (8 / Real.pi * M) * ((-Real.log t) * t ^ δ) * t ^ (δ - 1) := by
            rw [hsplit_pow]; ring
        _ ≤ (8 / Real.pi * M) * δ⁻¹ * t ^ (δ - 1) := by
            gcongr
        _ = C_head * t ^ (δ - 1) := rfl
    · simp only [bound, ht1, ↓reduceIte]
      have ht1' : 1 < t := lt_of_not_ge ht1
      have hlog_abs : |Real.log t| = Real.log t := abs_of_nonneg (Real.log_nonneg ht1'.le)
      have hlog_le : Real.log t ≤ t := log_le_self_of_one_le ht1'.le
      have hmul_pow : t ^ (z.re - 1) * t = t ^ z.re := by
        calc t ^ (z.re - 1) * t = t ^ (z.re - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = t ^ (z.re - 1 + 1) := (Real.rpow_add ht0 (z.re - 1) 1).symm
          _ = t ^ z.re := by ring_nf
      have hrn : z.re ≤ (n : ℝ) := by
        have h1 : z₀.re + δ ≤ ⌈z₀.re + δ⌉₊ := Nat.le_ceil _
        have h2 : (⌈z₀.re + δ⌉₊ : ℝ) ≤ n := by exact_mod_cast le_max_right 2 ⌈z₀.re + δ⌉₊
        linarith
      have hpow_le := rpow_le_inv_besselVCoeff_mul_cardyV ha ht1'.le hn2 hrn
      calc |g t| * t ^ (z.re - 1) * |Real.log t|
          = |g t| * t ^ (z.re - 1) * Real.log t := by rw [hlog_abs]
        _ ≤ |g t| * t ^ (z.re - 1) * t := by gcongr
        _ = |g t| * t ^ z.re := by rw [mul_assoc, hmul_pow]
        _ ≤ |g t| * ((besselVCoeff a n)⁻¹ * virasoroProblem.cardyV a t) := by gcongr
        _ = (besselVCoeff a n)⁻¹ * (|g t| * virasoroProblem.cardyV a t) := by ring
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball z₀ δ,
      HasDerivAt (fun w => F w t) (F' z t) z := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t ht z _ => ?_
    have ht0 : 0 < t := mem_Ioi.mp ht
    have htc_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hlin : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
    have hcpow := (hlin.const_cpow (Or.inl htc_ne)).const_mul (g t : ℂ)
    refine hcpow.congr_deriv ?_
    dsimp [F']
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (Metric.ball_mem_nhds z₀ hδ)
    (Eventually.of_forall hF_meas) hF_int hF'_meas h_bound hbound_int h_diff).2

/-- **Holomorphy of `Mg(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem differentiableOn_mellinTransformG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    DifferentiableOn ℂ (mellinTransformG g) {z : ℂ | 0 < z.re} :=
  fun _ hz => (hasDerivAt_mellinTransformG ha hg hz).differentiableAt.differentiableWithinAt

/-- **Analyticity of `Mg(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem analyticOnNhd_mellinTransformG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    AnalyticOnNhd ℂ (mellinTransformG g) {z : ℂ | 0 < z.re} :=
  (differentiableOn_mellinTransformG ha hg).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-- **Holomorphy of `m_g(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem differentiableOn_mellinMG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    DifferentiableOn ℂ (mellinMG g) {z : ℂ | 0 < z.re} := by
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hpow : Differentiable ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ z) :=
    fun z => (hasDerivAt_id z).const_cpow (Or.inl h2pi_ne) |>.differentiableAt
  have hinvG : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  have heq : mellinMG g = fun z =>
      ((2 * (Real.pi : ℂ)) ^ z * mellinTransformG g z) * (Complex.Gamma z)⁻¹ := by
    ext z; simp [mellinMG, div_eq_mul_inv]
  rw [heq]
  exact ((hpow.differentiableOn).mul (differentiableOn_mellinTransformG ha hg)).mul hinvG.differentiableOn

/-- **Analyticity of `m_g(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem analyticOnNhd_mellinMG {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    AnalyticOnNhd ℂ (mellinMG g) {z : ℂ | 0 < z.re} :=
  (differentiableOn_mellinMG ha hg).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Mellin.integrableOn_mellinTransformG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.integrableOn_mellinTransformG

/-- info: 'FormalResearch.ModularBootstrap.Mellin.differentiableOn_mellinTransformG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.differentiableOn_mellinTransformG

/-- info: 'FormalResearch.ModularBootstrap.Mellin.differentiableOn_mellinMG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.differentiableOn_mellinMG

end FormalResearch.ModularBootstrap.Mellin
