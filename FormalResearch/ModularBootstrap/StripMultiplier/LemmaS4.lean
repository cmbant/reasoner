module

public import FormalResearch.ModularBootstrap.Mellin.HankelMellin
public import FormalResearch.ModularBootstrap.ChartGeometry.HalfStripAsymptotics
public import FormalResearch.ModularBootstrap.ChartGeometry.QuadrantMonotonicity
public import FormalResearch.CohnElkies.MellinKernel
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Bounded Antisymmetric Multiplier (Lemma S4, `vlo:S4`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S4 (`vlo:S4`,
lines 409–414).

Defines the strip multiplier
`tildeWV c' g ζ = exp(-c' Υ(ζ)) m_g(1/2 + c' ω(ζ))`
for spinless Virasoro (`w = 1`) and proves **Lemma S4** (`lemma_S4`):
* `tildeWV c' g` is holomorphic on `stripOpen = {0 < Re ζ < 1}` and continuous on
  `stripClosed = {0 ≤ Re ζ ≤ 1}`;
* antisymmetry `tildeWV c' g (1 - ζ) = -tildeWV c' g ζ` on `stripClosed`;
* uniform strip bound `sup_{stripClosed} |tildeWV c' g| ≤ C M[g]` for all sufficiently large `c'`,
  proved via `PhragmenLindelof.vertical_strip` from Lemma S2 (`lemma_S2`) on the left edge,
  edge contact (`re_chartUpsilon_left_edge`), reflection symmetry, and polynomial-in-height
  `log⁺` growth on the strip.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.StripMultiplier

open Crossing Integration ComplexBessel Mellin Chart ChartGeometry

/-! ### Section 1: Strip multiplier definition, regularity, and antisymmetry -/

/-- Bounded antisymmetric strip multiplier
`W̃_V(ζ) = e^{-c' Υ(ζ)} m_g(1/2 + c' ω(ζ))` (`lower_o1_two_edge.tex`, Lemma S4, `vlo:S4`). -/
noncomputable def tildeWV (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (-(c' : ℂ) * chartUpsilon ζ) *
    mellinMGEntire g (1 / 2 + (c' : ℂ) * chartOmega ζ)

lemma tildeWV_differentiableOn {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    DifferentiableOn ℂ (tildeWV c' g) stripOpen := by
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hmg : Differentiable ℂ (mellinMGEntire g) := differentiable_mellinMGEntire ha hg
  have hup : DifferentiableOn ℂ chartUpsilon stripOpen :=
    lemma_S3_strip.2.2.1.differentiableOn
  have hom : DifferentiableOn ℂ chartOmega stripOpen :=
    lemma_S3_strip.1.differentiableOn
  refine (((hup.const_mul (-(c' : ℂ))).cexp)).mul ?_
  have hlin : DifferentiableOn ℂ (fun ζ => 1 / 2 + (c' : ℂ) * chartOmega ζ) stripOpen :=
    (differentiableOn_const _).add (hom.const_mul (c' : ℂ))
  exact hmg.comp_differentiableOn hlin

lemma tildeWV_continuousOn {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    ContinuousOn (tildeWV c' g) stripClosed := by
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hmg : Continuous (mellinMGEntire g) := (differentiable_mellinMGEntire ha hg).continuous
  have hup : ContinuousOn chartUpsilon stripClosed := lemma_S3_strip.2.2.2.1
  have hom : ContinuousOn chartOmega stripClosed := lemma_S3_strip.2.1
  refine ((hup.const_mul (-(c' : ℂ))).cexp).mul ?_
  have hlin : ContinuousOn (fun ζ => 1 / 2 + (c' : ℂ) * chartOmega ζ) stripClosed :=
    continuousOn_const.add (hom.const_mul (c' : ℂ))
  exact hmg.comp_continuousOn hlin

lemma tildeWV_reflect {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {ζ : ℂ} (hζ : ζ ∈ stripClosed) :
    tildeWV c' g (1 - ζ) = -tildeWV c' g ζ := by
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  unfold tildeWV
  rw [chartUpsilon_reflect hζ.1 hζ.2, chartOmega_reflect ζ]
  have harg : 1 / 2 + (c' : ℂ) * (-chartOmega ζ) =
      1 - (1 / 2 + (c' : ℂ) * chartOmega ζ) := by ring
  rw [harg, mellinMGEntire_one_sub ha hg]
  ring

/-! ### Section 2: Left-edge bound via Lemma S2 and edge contact -/

lemma edgeMu_ge_muStar (τ : ℝ) : muStar ≤ edgeMu τ := by
  unfold muStar edgeMu edgeX0
  have h1 : 1 ≤ √(Real.cosh (Real.pi * τ)) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (Real.one_le_cosh _)
  have h2 : Real.arsinh 1 ≤ Real.arsinh (√(Real.cosh (Real.pi * τ))) :=
    Real.arsinh_le_arsinh.mpr h1
  have hxi : xiStar = Real.arsinh 1 / Real.pi := rfl
  rw [hxi]
  have hpi := Real.pi_pos
  have h1' : Real.arsinh 1 / 3 ≤ Real.arsinh (√(Real.cosh (Real.pi * τ))) / 3 := by gcongr
  calc Real.pi * (Real.arsinh 1 / Real.pi) / 3 = Real.arsinh 1 / 3 := by field_simp
    _ ≤ Real.arsinh (√(Real.cosh (Real.pi * τ))) / 3 := h1'
    _ = Real.pi / 3 * (Real.arsinh (√(Real.cosh (Real.pi * τ))) / Real.pi) := by field_simp

lemma tildeWV_left_edge_norm_eq {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ) (τ : ℝ) :
    ‖tildeWV c' g ((τ : ℂ) * Complex.I)‖ =
      Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) *
        ‖mellinMG g (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)))‖ := by
  have hmul : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
  have hμ_pos : 0 < edgeMu τ := lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
  have hω_re : 0 < (chartOmega (Complex.I * (τ : ℂ))).re := by
    rw [chartOmega_left_edge τ]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact hμ_pos
  have hz_re : 0 < (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
    linarith [mul_pos hc' hω_re]
  unfold tildeWV
  rw [hmul, norm_mul, Complex.norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    re_chartUpsilon_left_edge τ, mellinMGEntire_of_re_pos g hz_re]
  ring_nf

/-! ### Section 3: Growth bound in the open strip for Phragmén–Lindelöf -/

private lemma pow_add_one_sub_ge_one' {x : ℝ} (hx : 1 ≤ x) :
    ∀ k : ℕ, 1 ≤ k → 1 ≤ (x + 1) ^ k - x ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m _ ih =>
    have hpow_ge : 1 ≤ x ^ m := one_le_pow₀ hx
    have hpow_le : x ^ m ≤ (x + 1) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have hx_nn : 0 ≤ x := by linarith
    calc (1 : ℝ) ≤ (x + 1) ^ m - x ^ m := ih
      _ ≤ x * ((x + 1) ^ m - x ^ m) + (x + 1) ^ m := by nlinarith
      _ = (x + 1) ^ (m + 1) - x ^ (m + 1) := by ring

private lemma second_difference_pow_ge_two' {b : ℝ} (hb : 0 ≤ b) :
    ∀ k : ℕ, 2 ≤ k → 2 ≤ (b + 2) ^ k - 2 * (b + 1) ^ k + b ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => linarith
  | succ m hm ih =>
    have hm1 : 1 ≤ m := by omega
    have h1 : 1 ≤ (b + 2) ^ m - (b + 1) ^ m := by
      have h := pow_add_one_sub_ge_one' (x := b + 1) (by linarith) m hm1
      simpa [show b + 1 + 1 = b + 2 by ring] using h
    have h2 : (b + 2) ^ (m + 1) - 2 * (b + 1) ^ (m + 1) + b ^ (m + 1) =
        b * ((b + 2) ^ m - 2 * (b + 1) ^ m + b ^ m) + 2 * ((b + 2) ^ m - (b + 1) ^ m) := by
      ring
    rw [h2]
    nlinarith

private lemma besselVCoeff_ge_two_div_sq_fac {a : ℝ} (ha : 2 ≤ a) {n : ℕ} (hn : 2 ≤ n) :
    2 / ((n ! : ℝ) ^ 2) ≤ Bessel.besselVCoeff a n := by
  unfold Bessel.besselVCoeff
  have h1 : (2 : ℝ) ≤ a ^ n - 2 * (a - 1) ^ n + (a - 2) ^ n := by
    have h := second_difference_pow_ge_two' (b := a - 2) (by linarith) n hn
    simpa [show a - 2 + 2 = a by ring, show a - 2 + 1 = a - 1 by ring] using h
  have hpi : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpow : (1 : ℝ) ≤ (4 * Real.pi ^ 2) ^ n := one_le_pow₀ hpi
  have hfac : (0 : ℝ) < (n ! : ℝ) ^ 2 := by positivity
  calc 2 / ((n ! : ℝ) ^ 2)
      = 1 / ((n ! : ℝ) ^ 2) * 2 := by ring
    _ ≤ (4 * Real.pi ^ 2) ^ n / ((n ! : ℝ) ^ 2) * 2 := by gcongr
    _ ≤ (4 * Real.pi ^ 2) ^ n / ((n ! : ℝ) ^ 2) * (a ^ n - 2 * (a - 1) ^ n + (a - 2) ^ n) := by
        gcongr

private lemma factorial_le_pow_self' (n : ℕ) : (n ! : ℝ) ≤ (n : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    calc ((m + 1 : ℕ) : ℝ) * (m ! : ℝ)
        ≤ ((m + 1 : ℕ) : ℝ) * (m : ℝ) ^ m := by gcongr
      _ ≤ ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ^ m := by
          gcongr; exact le_of_lt (Nat.cast_lt.mpr (Nat.lt_succ_self m))
      _ = ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by rw [pow_succ']

private lemma norm_mellinMG_le_of_half_le_re {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖mellinMG g z‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      Real.exp (20 * (1 + ‖z‖) ^ 2) := by
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  have hM_nn : 0 ≤ virasoroProblem.cardyNorm (c' / 12) g :=
    virasoroProblem.cardyNorm_nonneg hshift g
  have hz_pos : 0 < z.re := by linarith
  have hz_norm_ge : 1 / 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have hz_norm_pos : 0 < ‖z‖ := by linarith
  -- Factor 1: (2π)^z
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have h2pi_norm : ‖(2 * (Real.pi : ℂ)) ^ z‖ ≤ Real.exp (Real.log (2 * Real.pi) * ‖z‖) := by
    rw [show (2 * (Real.pi : ℂ)) ^ z = ((2 * Real.pi : ℝ) : ℂ) ^ z by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos h2pi_pos, Real.rpow_def_of_pos h2pi_pos]
    refine Real.exp_le_exp.mpr ?_
    have hlog_nn : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    exact mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hlog_nn
  -- Factor 2: (Gamma z)⁻¹
  have hgam_eq := FormalResearch.CohnElkies.exp_stirling_add_binetRem_eq_gamma hz_pos
  have hbin_bd : ‖FormalResearch.Asymptotics.binetRem z‖ ≤ 4 := by
    rw [FormalResearch.CohnElkies.binetRem_eq_binetB hz_pos]
    calc ‖FormalResearch.Special.ComplexStirling.binetB z‖
        ≤ 2 / ‖z‖ := FormalResearch.Special.ComplexStirling.norm_binetB_le_div hz_pos
      _ ≤ 2 / (1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz_norm_ge
      _ = 4 := by norm_num
  have hlogz_bd : ‖Complex.log z‖ ≤ 5 + ‖z‖ := by
    have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    rw [Complex.log_re, Complex.log_im] at h1
    have harg : |z.arg| ≤ Real.pi := Complex.abs_arg_le_pi z
    have hlog_abs : |Real.log ‖z‖| ≤ 1 + ‖z‖ := by
      rcases le_or_gt 1 ‖z‖ with hge1 | hlt1
      · rw [abs_of_nonneg (Real.log_nonneg hge1)]
        have := Real.log_le_sub_one_of_pos hz_norm_pos
        linarith
      · rw [abs_of_nonpos (Real.log_nonpos hz_norm_pos.le hlt1.le)]
        have hinv : Real.log ‖z‖⁻¹ ≤ Real.log 2 :=
          Real.log_le_log (inv_pos.mpr hz_norm_pos) (by rw [inv_le_comm₀ hz_norm_pos two_pos]; linarith)
        rw [Real.log_inv] at hinv
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        linarith
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    linarith
  have hgam_inv_norm : ‖(Complex.Gamma z)⁻¹‖ ≤
      Real.exp (‖(z - 1 / 2) * Complex.log z‖ + ‖z‖ + |Real.log (2 * Real.pi) / 2| + 4) := by
    rw [← hgam_eq, ← Complex.exp_neg, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    rw [Complex.neg_re]
    have hre_le := Complex.abs_re_le_norm
      ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetRem z)
    have htri : ‖(z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) +
          FormalResearch.Asymptotics.binetRem z‖ ≤
        ‖(z - 1 / 2) * Complex.log z‖ + ‖z‖ + |Real.log (2 * Real.pi) / 2| + 4 := by
      have ht1 := norm_add_le
        ((z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ))
        (FormalResearch.Asymptotics.binetRem z)
      have ht2 := norm_add_le
        ((z - 1 / 2) * Complex.log z - z)
        ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)
      have ht3 := norm_sub_le ((z - 1 / 2) * Complex.log z) z
      rw [Complex.norm_real, Real.norm_eq_abs] at ht2
      linarith
    linarith [(abs_le.mp hre_le).1]
  have hgam_exp_bd : ‖(Complex.Gamma z)⁻¹‖ ≤ Real.exp (9 * (1 + ‖z‖) ^ 2) := by
    refine hgam_inv_norm.trans (Real.exp_le_exp.mpr ?_)
    have hz12 : ‖z - 1 / 2‖ ≤ ‖z‖ + 1 / 2 :=
      (norm_sub_le z (1 / 2 : ℂ)).trans (by norm_num)
    have hmul : ‖(z - 1 / 2) * Complex.log z‖ ≤ (‖z‖ + 1 / 2) * (5 + ‖z‖) := by
      rw [norm_mul]
      exact mul_le_mul hz12 hlogz_bd (norm_nonneg _) (by positivity)
    have hlog2pi_le : |Real.log (2 * Real.pi) / 2| ≤ 2 := by
      have hpos : 0 ≤ Real.log (2 * Real.pi) / 2 := by
        have : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        exact div_nonneg (Real.log_nonneg this) (by norm_num)
      rw [abs_of_nonneg hpos]
      have h1 : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos h2pi_pos
      have h2 : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
      have hlog4 : Real.log (2 * Real.pi) ≤ 3 := by
        have hlt : 2 * Real.pi < Real.exp 3 := by
          have hexp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
            have := Real.sum_le_exp_of_nonneg zero_le_one 5
            simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
              Nat.factorial] at this
            norm_num at this
            linarith
          have hexp3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; simp
          rw [hexp3]
          have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr
          linarith
        exact (Real.log_lt_iff_lt_exp h2pi_pos).mpr hlt |>.le
      linarith
    nlinarith [norm_nonneg z]
  -- Factor 3: mellinTransformG g z
  have hint_all := integrableOn_mellinTransformG ha hg hz_pos
  have hint_head : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc 0 1) :=
    hint_all.mono_set Ioc_subset_Ioi_self
  have hint_tail : IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 1) :=
    hint_all.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsplit : mellinTransformG g z =
      (∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)) +
        (∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)) := by
    unfold mellinTransformG
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_head hint_tail]
  have hhead_bd : ‖∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
      (16 / Real.pi) * virasoroProblem.cardyNorm (c' / 12) g := by
    have h1 : ‖∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioc (0 : ℝ) 1, ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ t in Ioc (0 : ℝ) 1, ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ =
        ∫ t in Ioc (0 : ℝ) 1, |g t| * t ^ (z.re - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re]
    have h3 := mellinTransformG_head_bound ha hg hz_pos
    have h4 : (8 / Real.pi * virasoroProblem.cardyNorm (c' / 12) g) / z.re ≤
        (16 / Real.pi) * virasoroProblem.cardyNorm (c' / 12) g := by
      rw [div_le_iff₀ hz_pos]
      have hnn : 0 ≤ 8 / Real.pi * virasoroProblem.cardyNorm (c' / 12) g := by positivity
      calc 8 / Real.pi * virasoroProblem.cardyNorm (c' / 12) g
          = 16 / Real.pi * virasoroProblem.cardyNorm (c' / 12) g * (1 / 2) := by ring
        _ ≤ 16 / Real.pi * virasoroProblem.cardyNorm (c' / 12) g * z.re := by gcongr
    linarith
  let n : ℕ := max 2 ⌈z.re⌉₊
  have hn2 : 2 ≤ n := le_max_left _ _
  have hrn : z.re - 1 ≤ (n : ℝ) := by
    have h1 : z.re ≤ ⌈z.re⌉₊ := Nat.le_ceil z.re
    have h2 : (⌈z.re⌉₊ : ℝ) ≤ n := by exact_mod_cast le_max_right 2 ⌈z.re⌉₊
    linarith
  have hv_pos : 0 < Bessel.besselVCoeff (c' / 12) n := besselVCoeff_pos ha hn2
  have htail_bd : ‖∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
      (Bessel.besselVCoeff (c' / 12) n)⁻¹ * virasoroProblem.cardyNorm (c' / 12) g := by
    have h1 : ‖∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioi (1 : ℝ), ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    have hdom : IntegrableOn (fun t : ℝ => (Bessel.besselVCoeff (c' / 12) n)⁻¹ *
        (|g t| * virasoroProblem.cardyV (c' / 12) t)) (Ioi 1) :=
      (hg.int_cardy.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
    have h2 : ∫ t in Ioi (1 : ℝ), ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Ioi (1 : ℝ), (Bessel.besselVCoeff (c' / 12) n)⁻¹ *
          (|g t| * virasoroProblem.cardyV (c' / 12) t) := by
      refine setIntegral_mono_on hint_tail.norm hdom measurableSet_Ioi fun t ht => ?_
      have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
      have hrp := rpow_le_inv_besselVCoeff_mul_cardyV ha ht1 hn2 hrn
      calc |g t| * t ^ (z.re - 1)
          ≤ |g t| * ((Bessel.besselVCoeff (c' / 12) n)⁻¹ * virasoroProblem.cardyV (c' / 12) t) := by
            gcongr
        _ = (Bessel.besselVCoeff (c' / 12) n)⁻¹ * (|g t| * virasoroProblem.cardyV (c' / 12) t) := by
            ring
    have h3 : ∫ t in Ioi (1 : ℝ), (Bessel.besselVCoeff (c' / 12) n)⁻¹ *
          (|g t| * virasoroProblem.cardyV (c' / 12) t) ≤
        (Bessel.besselVCoeff (c' / 12) n)⁻¹ * virasoroProblem.cardyNorm (c' / 12) g := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hv_pos.le)
      refine setIntegral_mono_set hg.int_cardy ?_ (Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le)
    linarith
  have hv_inv_bd : (Bessel.besselVCoeff (c' / 12) n)⁻¹ ≤ Real.exp (2 * (‖z‖ + 2) ^ 2) := by
    have hv_lb := besselVCoeff_ge_two_div_sq_fac ha hn2
    have h1 : (Bessel.besselVCoeff (c' / 12) n)⁻¹ ≤ (n ! : ℝ) ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀ hv_pos]
      have hfac_pos : (0 : ℝ) < (n ! : ℝ) ^ 2 := by positivity
      calc (1 : ℝ) = ((n ! : ℝ) ^ 2 / 2) * (2 / (n ! : ℝ) ^ 2) := by field_simp [hfac_pos.ne']
        _ ≤ ((n ! : ℝ) ^ 2 / 2) * Bessel.besselVCoeff (c' / 12) n :=
            mul_le_mul_of_nonneg_left hv_lb (by positivity)
    have hn_le : (n : ℝ) ≤ ‖z‖ + 2 := by
      dsimp [n]
      rw [Nat.cast_max]
      refine max_le (by push_cast; linarith [norm_nonneg z]) ?_
      have hceil : (⌈z.re⌉₊ : ℝ) < z.re + 1 := Nat.ceil_lt_add_one hz_pos.le
      linarith [Complex.re_le_norm z]
    have hfac_le : (n ! : ℝ) ^ 2 ≤ Real.exp (2 * (n : ℝ) ^ 2) := by
      have hf := factorial_le_pow_self' n
      have hsq : (n ! : ℝ) ^ 2 ≤ ((n : ℝ) ^ n) ^ 2 := by gcongr
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hpow_eq : ((n : ℝ) ^ n) ^ 2 = Real.exp (2 * (n : ℝ) * Real.log n) := by
        rw [← Real.rpow_natCast (n : ℝ) n, ← Real.rpow_natCast ((n : ℝ) ^ (n : ℝ)) 2,
          ← Real.rpow_mul (by positivity), Real.rpow_def_of_pos hn_pos]
        congr 1; ring
      have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) := by
        have := Real.log_le_sub_one_of_pos hn_pos
        linarith
      have hexp_le : Real.exp (2 * (n : ℝ) * Real.log n) ≤ Real.exp (2 * (n : ℝ) ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hn_pos]
      linarith [hsq, hpow_eq, hexp_le]
    have hfac_sq_le : (n ! : ℝ) ^ 2 / 2 ≤ Real.exp (2 * (‖z‖ + 2) ^ 2) := by
      have h2 : 2 * (n : ℝ) ^ 2 ≤ 2 * (‖z‖ + 2) ^ 2 := by gcongr
      have hdiv : (n ! : ℝ) ^ 2 / 2 ≤ (n ! : ℝ) ^ 2 := by linarith [sq_nonneg (n ! : ℝ)]
      exact hdiv.trans (hfac_le.trans (Real.exp_le_exp.mpr h2))
    exact h1.trans hfac_sq_le
  have hMG_bd : ‖mellinTransformG g z‖ ≤
      virasoroProblem.cardyNorm (c' / 12) g * Real.exp (2 * (‖z‖ + 2) ^ 2 + 2) := by
    have htri : ‖mellinTransformG g z‖ ≤
        (16 / Real.pi + Real.exp (2 * (‖z‖ + 2) ^ 2)) * virasoroProblem.cardyNorm (c' / 12) g := by
      rw [hsplit]
      calc ‖(∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)) +
              (∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1))‖
          ≤ ‖∫ t in Ioc (0 : ℝ) 1, (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ +
              ‖∫ t in Ioi (1 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)‖ := norm_add_le _ _
        _ ≤ (16 / Real.pi) * virasoroProblem.cardyNorm (c' / 12) g +
              (Bessel.besselVCoeff (c' / 12) n)⁻¹ * virasoroProblem.cardyNorm (c' / 12) g := by
            gcongr
        _ ≤ (16 / Real.pi) * virasoroProblem.cardyNorm (c' / 12) g +
              Real.exp (2 * (‖z‖ + 2) ^ 2) * virasoroProblem.cardyNorm (c' / 12) g := by
            gcongr
        _ = (16 / Real.pi + Real.exp (2 * (‖z‖ + 2) ^ 2)) *
              virasoroProblem.cardyNorm (c' / 12) g := by ring
    have h16 : 16 / Real.pi ≤ 6 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith [Real.pi_gt_three]
    have h1e : 1 ≤ Real.exp (2 * (‖z‖ + 2) ^ 2) :=
      Real.one_le_exp (by positivity)
    have hexp2 : (7 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.sum_le_exp_of_nonneg zero_le_one 5
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
          Nat.factorial] at this
        norm_num at this
        linarith
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; simp
      rw [h2]; nlinarith
    calc ‖mellinTransformG g z‖
        ≤ (16 / Real.pi + Real.exp (2 * (‖z‖ + 2) ^ 2)) *
              virasoroProblem.cardyNorm (c' / 12) g := htri
      _ ≤ (6 + Real.exp (2 * (‖z‖ + 2) ^ 2)) * virasoroProblem.cardyNorm (c' / 12) g :=
          mul_le_mul_of_nonneg_right (add_le_add_left h16 _) hM_nn
      _ ≤ (7 * Real.exp (2 * (‖z‖ + 2) ^ 2)) * virasoroProblem.cardyNorm (c' / 12) g :=
          mul_le_mul_of_nonneg_right (by linarith) hM_nn
      _ ≤ (Real.exp 2 * Real.exp (2 * (‖z‖ + 2) ^ 2)) *
            virasoroProblem.cardyNorm (c' / 12) g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp2 (Real.exp_pos _).le) hM_nn
      _ = virasoroProblem.cardyNorm (c' / 12) g * Real.exp (2 * (‖z‖ + 2) ^ 2 + 2) := by
          rw [← Real.exp_add]; ring_nf
  -- Combine all three factors
  unfold mellinMG
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  have hlog2pi_le3 : Real.log (2 * Real.pi) ≤ 3 := by
    have hlt : 2 * Real.pi < Real.exp 3 := by
      have hexp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.sum_le_exp_of_nonneg zero_le_one 5
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
          Nat.factorial] at this
        norm_num at this
        linarith
      have hexp3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; simp
      rw [hexp3]
      have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr
      linarith [Real.pi_lt_four]
    exact (Real.log_lt_iff_lt_exp h2pi_pos).mpr hlt |>.le
  calc ‖(2 * (Real.pi : ℂ)) ^ z‖ * ‖mellinTransformG g z‖ * ‖(Complex.Gamma z)⁻¹‖
      ≤ Real.exp (Real.log (2 * Real.pi) * ‖z‖) *
          (virasoroProblem.cardyNorm (c' / 12) g * Real.exp (2 * (‖z‖ + 2) ^ 2 + 2)) *
          Real.exp (9 * (1 + ‖z‖) ^ 2) := by gcongr
    _ = virasoroProblem.cardyNorm (c' / 12) g *
          (Real.exp (Real.log (2 * Real.pi) * ‖z‖) *
            Real.exp (2 * (‖z‖ + 2) ^ 2 + 2) *
            Real.exp (9 * (1 + ‖z‖) ^ 2)) := by ring
    _ = virasoroProblem.cardyNorm (c' / 12) g *
          Real.exp (Real.log (2 * Real.pi) * ‖z‖ + (2 * (‖z‖ + 2) ^ 2 + 2) +
            9 * (1 + ‖z‖) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ virasoroProblem.cardyNorm (c' / 12) g * Real.exp (20 * (1 + ‖z‖) ^ 2) := by
        gcongr
        have hnz : 0 ≤ ‖z‖ := norm_nonneg z
        have h1 : Real.log (2 * Real.pi) * ‖z‖ ≤ 3 * ‖z‖ :=
          mul_le_mul_of_nonneg_right hlog2pi_le3 hnz
        nlinarith

private lemma tildeWV_strip_growth {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    ∃ B : ℝ, tildeWV c' g =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo 0 1)]
      fun ζ => Real.exp (B * Real.exp (1 * |ζ.im|)) := by
  obtain ⟨C_om, hC_om, hOm_bd⟩ := chartOmega_strip_bound
  obtain ⟨C_up, hC_up, hUp_bd⟩ := chartUpsilon_strip_bound
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hc'_pos : 0 < c' := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  have hM_nn : 0 ≤ virasoroProblem.cardyNorm (c' / 12) g :=
    virasoroProblem.cardyNorm_nonneg hshift g
  let K : ℝ := c' * C_up + 20 * (2 + c' * C_om) ^ 2
  have hK_nn : 0 ≤ K := by positivity
  let B : ℝ := K * 24 * Real.exp 1
  refine ⟨B, Asymptotics.IsBigO.of_bound (virasoroProblem.cardyNorm (c' / 12) g) ?_⟩
  filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with ζ hζ_re
  have hζ_mem : ζ ∈ stripOpen := hζ_re
  have hζ_cl : ζ ∈ stripClosed := ⟨hζ_mem.1.le, hζ_mem.2.le⟩
  have h_half_bd : ∀ {w : ℂ}, w ∈ stripClosed → w.re ≤ 1 / 2 →
      ‖tildeWV c' g w‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
        Real.exp (K * (1 + |w.im|) ^ 4) := by
    intro w hw hw_half
    have hω_re : 0 ≤ (chartOmega w).re := lemma_J7Q.2 w hw.1 hw_half
    set z : ℂ := 1 / 2 + (c' : ℂ) * chartOmega w
    have hz_re : 1 / 2 ≤ z.re := by
      simp only [z, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
      linarith [mul_nonneg hc'_pos.le hω_re]
    have hz_pos : 0 < z.re := by linarith
    have hω_bd := hOm_bd w hw
    have hup_bd := hUp_bd w hw
    have hsq_le : 1 + w.im ^ 2 ≤ (1 + |w.im|) ^ 2 := by
      nlinarith [abs_nonneg w.im, sq_abs w.im]
    have h1z_le : 1 + ‖z‖ ≤ (2 + c' * C_om) * (1 + |w.im|) ^ 2 := by
      have hz_norm : ‖z‖ ≤ 1 / 2 + c' * ‖chartOmega w‖ := by
        calc ‖1 / 2 + (c' : ℂ) * chartOmega w‖
            ≤ ‖(1 / 2 : ℂ)‖ + ‖(c' : ℂ) * chartOmega w‖ := norm_add_le _ _
          _ = 1 / 2 + c' * ‖chartOmega w‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le]; norm_num
      have h12 : (1 : ℝ) ≤ (1 + |w.im|) ^ 2 := by
        have : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
        nlinarith
      calc 1 + ‖z‖ ≤ 1 + (1 / 2 + c' * ‖chartOmega w‖) := by linarith
        _ ≤ 3 / 2 + c' * (C_om * (1 + w.im ^ 2)) := by
            have := mul_le_mul_of_nonneg_left hω_bd hc'_pos.le
            linarith
        _ ≤ 2 * (1 + |w.im|) ^ 2 + c' * C_om * (1 + |w.im|) ^ 2 := by
            have h1 := mul_le_mul_of_nonneg_left hsq_le (mul_nonneg hc'_pos.le hC_om.le)
            linarith
        _ = (2 + c' * C_om) * (1 + |w.im|) ^ 2 := by ring
    have h1w_ge1 : (1 : ℝ) ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
    have hsq_le4 : 1 + w.im ^ 2 ≤ (1 + |w.im|) ^ 4 := by
      calc 1 + w.im ^ 2 ≤ (1 + |w.im|) ^ 2 := hsq_le
        _ ≤ (1 + |w.im|) ^ 2 * (1 + |w.im|) ^ 2 := by nlinarith
        _ = (1 + |w.im|) ^ 4 := by ring
    have hexp_up : ‖Complex.exp (-(c' : ℂ) * chartUpsilon w)‖ ≤
        Real.exp (c' * C_up * (1 + |w.im|) ^ 4) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have h1 : (-(c' : ℂ) * chartUpsilon w).re ≤ ‖-(c' : ℂ) * chartUpsilon w‖ :=
        Complex.re_le_norm _
      have h2 : ‖-(c' : ℂ) * chartUpsilon w‖ = c' * ‖chartUpsilon w‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le]
      calc (-(c' : ℂ) * chartUpsilon w).re ≤ c' * ‖chartUpsilon w‖ := h1.trans_eq h2
        _ ≤ c' * (C_up * (1 + w.im ^ 2)) := by gcongr
        _ ≤ c' * (C_up * (1 + |w.im|) ^ 4) := by gcongr
        _ = c' * C_up * (1 + |w.im|) ^ 4 := by ring
    have hmg_bd := norm_mellinMG_le_of_half_le_re hc' hg hz_re
    have hexp_mg : ‖mellinMGEntire g z‖ ≤
        virasoroProblem.cardyNorm (c' / 12) g *
          Real.exp (20 * (2 + c' * C_om) ^ 2 * (1 + |w.im|) ^ 4) := by
      rw [mellinMGEntire_of_re_pos g hz_pos]
      refine hmg_bd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM_nn)
      have hsq1z : (1 + ‖z‖) ^ 2 ≤ ((2 + c' * C_om) * (1 + |w.im|) ^ 2) ^ 2 := by
        gcongr
      calc 20 * (1 + ‖z‖) ^ 2
          ≤ 20 * ((2 + c' * C_om) * (1 + |w.im|) ^ 2) ^ 2 := by gcongr
        _ = 20 * (2 + c' * C_om) ^ 2 * (1 + |w.im|) ^ 4 := by ring
    unfold tildeWV
    rw [norm_mul]
    calc ‖Complex.exp (-(c' : ℂ) * chartUpsilon w)‖ * ‖mellinMGEntire g z‖
        ≤ Real.exp (c' * C_up * (1 + |w.im|) ^ 4) *
            (virasoroProblem.cardyNorm (c' / 12) g *
              Real.exp (20 * (2 + c' * C_om) ^ 2 * (1 + |w.im|) ^ 4)) := by gcongr
      _ = virasoroProblem.cardyNorm (c' / 12) g * Real.exp (K * (1 + |w.im|) ^ 4) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; dsimp [K]; ring
  have hζ_bd : ‖tildeWV c' g ζ‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      Real.exp (K * (1 + |ζ.im|) ^ 4) := by
    rcases le_or_gt ζ.re (1 / 2) with hle | hgt
    · exact h_half_bd hζ_cl hle
    · have h1ζ_cl : 1 - ζ ∈ stripClosed := ⟨by simp; linarith [hζ_cl.2], by simp; linarith [hζ_cl.1]⟩
      have h1ζ_half : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
      have href := tildeWV_reflect hc' hg hζ_cl
      have hnorm_eq : ‖tildeWV c' g ζ‖ = ‖tildeWV c' g (1 - ζ)‖ := by rw [href, norm_neg]
      rw [hnorm_eq]
      simpa [Complex.sub_im, abs_neg] using h_half_bd h1ζ_cl h1ζ_half
  have hpow4_le : (1 + |ζ.im|) ^ 4 ≤ 24 * Real.exp 1 * Real.exp (1 * |ζ.im|) := by
    have hfac := Real.pow_div_factorial_le_exp (1 + |ζ.im|) (by positivity) 4
    have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h4, div_le_iff₀ (by norm_num)] at hfac
    rw [Real.exp_add] at hfac
    rw [one_mul]
    linarith
  have h_final : ‖tildeWV c' g ζ‖ ≤ virasoroProblem.cardyNorm (c' / 12) g *
      Real.exp (B * Real.exp (1 * |ζ.im|)) := by
    refine hζ_bd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM_nn)
    calc K * (1 + |ζ.im|) ^ 4
        ≤ K * (24 * Real.exp 1 * Real.exp (1 * |ζ.im|)) := by gcongr
      _ = B * Real.exp (1 * |ζ.im|) := by dsimp [B]; ring
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact h_final

/-! ### Section 4: Lemma S4 (`vlo:S4`) -/

/-- **Lemma S4 (bounded antisymmetric multiplier)** (`lower_o1_two_edge.tex`, §J2, `vlo:S4`,
lines 409–414):
there exist `C > 0` and `c₀ ≥ 10000` such that for all `c' ≥ c₀` and every
`g ∈ TestClass virasoroProblem (c' / 12)`, `tildeWV c' g` is holomorphic on `stripOpen`,
continuous on `stripClosed`, antisymmetric (`tildeWV c' g (1 - ζ) = -tildeWV c' g ζ`),
and uniformly bounded on `stripClosed` by `C * M[g]`. -/
theorem lemma_S4 :
    ∃ C c₀ : ℝ, 0 < C ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        DifferentiableOn ℂ (tildeWV c' g) stripOpen ∧
        ContinuousOn (tildeWV c' g) stripClosed ∧
        (∀ ζ ∈ stripClosed, tildeWV c' g (1 - ζ) = -tildeWV c' g ζ) ∧
        (∀ ζ ∈ stripClosed, ‖tildeWV c' g ζ‖ ≤ C * virasoroProblem.cardyNorm (c' / 12) g) := by
  let μ₀ : ℝ := (Real.pi * xiStar / 6 + muStar) / 2
  have hμ₀ : Real.pi * xiStar / 6 < μ₀ := by
    dsimp [μ₀]; unfold muStar
    have : 0 < Real.pi * xiStar := mul_pos Real.pi_pos xiStar_pos
    linarith
  have hμ₀_le_muStar : μ₀ ≤ muStar := by
    dsimp [μ₀]; unfold muStar
    have : 0 < Real.pi * xiStar := mul_pos Real.pi_pos xiStar_pos
    linarith
  obtain ⟨C, c₀, hC_pos, hc₀_10000, hS2⟩ := lemma_S2 hμ₀
  refine ⟨C, c₀, hC_pos, hc₀_10000, fun {c'} hc' {g} hg => ?_⟩
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have hdiff := tildeWV_differentiableOn hc'_24 hg
  have hcont := tildeWV_continuousOn hc'_24 hg
  have href : ∀ ζ ∈ stripClosed, tildeWV c' g (1 - ζ) = -tildeWV c' g ζ :=
    fun ζ hζ => tildeWV_reflect hc'_24 hg hζ
  refine ⟨hdiff, hcont, href, fun ζ hζ => ?_⟩
  have hleft : ∀ w : ℂ, w.re = 0 →
      ‖tildeWV c' g w‖ ≤ C * virasoroProblem.cardyNorm (c' / 12) g := by
    intro w hw_re
    have hw_eq : w = (w.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hw_re]
    rw [hw_eq, tildeWV_left_edge_norm_eq hc'_pos g w.im]
    have hω_re : μ₀ ≤ (chartOmega (Complex.I * (w.im : ℂ))).re := by
      rw [chartOmega_left_edge w.im]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
      exact hμ₀_le_muStar.trans (edgeMu_ge_muStar w.im)
    have hS2_bd := (hS2 hc' hω_re hg).2
    have hexp_pos : 0 ≤ Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ)))) :=
      (Real.exp_pos _).le
    calc Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ)))) *
            ‖mellinMG g (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (w.im : ℂ)))‖
        ≤ Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ)))) *
            (C * Real.exp (c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ)))) *
              virasoroProblem.cardyNorm (c' / 12) g) := by gcongr
      _ = C * (Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ)))) *
              Real.exp (c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ))))) *
            virasoroProblem.cardyNorm (c' / 12) g := by ring
      _ = C * virasoroProblem.cardyNorm (c' / 12) g := by
          rw [← Real.exp_add,
            show -c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ))) +
              c' * crudeExponentB (chartOmega (Complex.I * (w.im : ℂ))) = 0 by ring,
            Real.exp_zero, mul_one]
  have hright : ∀ w : ℂ, w.re = 1 →
      ‖tildeWV c' g w‖ ≤ C * virasoroProblem.cardyNorm (c' / 12) g := by
    intro w hw_re
    have hw_cl : w ∈ stripClosed := ⟨by linarith, by linarith⟩
    have h1w_re : (1 - w).re = 0 := by simp [hw_re]
    rw [show ‖tildeWV c' g w‖ = ‖tildeWV c' g (1 - w)‖ by rw [href w hw_cl, norm_neg]]
    exact hleft (1 - w) h1w_re
  have hcl_sub : closure (Complex.re ⁻¹' Ioo (0 : ℝ) 1) ⊆ stripClosed :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  have hfd : DiffContOnCl ℂ (tildeWV c' g) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) :=
    ⟨hdiff, hcont.mono hcl_sub⟩
  obtain ⟨B, hB⟩ := tildeWV_strip_growth hc'_24 hg
  have hc_lt : (1 : ℝ) < Real.pi / (1 - 0) := by
    rw [sub_zero, div_one]; linarith [Real.pi_gt_three]
  exact PhragmenLindelof.vertical_strip hfd ⟨1, hc_lt, B, hB⟩ hleft hright hζ.1 hζ.2

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.tildeWV_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripMultiplier.tildeWV_reflect

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.lemma_S4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.StripMultiplier.lemma_S4

end FormalResearch.ModularBootstrap.StripMultiplier
