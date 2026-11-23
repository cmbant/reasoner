module

public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS4WGrowth
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS2W
public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinW
public import FormalResearch.ModularBootstrap.ChartGeometry.HalfStripAsymptotics
public import FormalResearch.ModularBootstrap.ChartGeometry.QuadrantMonotonicity
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Bounded Antisymmetric Multiplier at Weight `w` (Lemma S4, `vlo:S4`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S4 (`vlo:S4`).

For `prob : FixedWeightProblem` (weight `w = prob.w ≥ 1`, any null-state product `Q`) the strip
multiplier is
`tildeWW w c' g ζ = exp(-c' Υ(ζ)) m_g(w/2 + c' ω(ζ))`
(`m_g = mellinMGEntireW w g`, the entire extension of `MellinW`).  `lemma_S4_W` proves:

* `tildeWW prob.w c' g` is holomorphic on `stripOpen = {0 < Re ζ < 1}` and continuous on
  `stripClosed = {0 ≤ Re ζ ≤ 1}`;
* antisymmetry `tildeWW (1 - ζ) = -tildeWW ζ` on `stripClosed`;
* `sup_{stripClosed} |tildeWW| ≤ C M[g]` for all `c' ≥ c₀`, `g ∈ TestClass prob (c'/12)`.

What the weight does to the proof (`vlo:S4`):

* **Reflection.**  Lemma S1 at weight `w` is `m_g(w - z) = -m_g(z)` (`mellinMGEntireW_sub`).  With
  `z = w/2 + c' ω(ζ)` one has `w - z = w/2 - c' ω(ζ) = w/2 + c' ω(1 - ζ)` because
  `ω(1 - ζ) = -ω(ζ)` (`chartOmega_reflect`), so the strip reflection is still `ζ ↦ 1 - ζ`
  (`tildeWW_reflect`); `Υ(1 - ζ) = Υ(ζ)` is weight free.
* **Left half-strip.**  `Re ω ≥ 0` (`lemma_J7Q`) gives `Re z ≥ w/2 ≥ 1/2`, so the growth bound
  `norm_mellinMGW_le_exp` (`Re z ≥ 1/2`, `LemmaS4WGrowth`) applies.
* **Edges.**  On `ζ = iτ` the real part of `ω` is `μ(τ) ≥ μ* > μ₀ > π ξ*/6` and `Re Υ = B(ω)`, so
  `lemma_S2_W` (`kernelBound_W`) gives `|m_g(w/2 + c'ω)| ≤ C e^{c' B(ω)} M[g]`, which cancels
  `|e^{-c'Υ}| = e^{-c' B(ω)}`.
* **Phragmén–Lindelöf.**  `|tildeWW| ≤ M[g] exp(K (1 + |Im ζ|)^4)` in the left half-strip (and by
  reflection in the right), far below `exp(A e^{ϑ|Im ζ|})`, `ϑ < π`.

Differences from the paper text (constants only): the tail estimate takes the Taylor term of order
`m + ⌈Re z⌉` of the `m`-fold difference `V` directly (the text uses order `⌈Re z⌉` of `K_a^{(w)}` and
the comparison W2), and the growth is `exp(O((1+|z|)²))` rather than
`exp(O((1+|z|) log(2+|z|)))`, which is still `exp(O((1+|Im ζ|)^4))` on the strip and suffices.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing WeightAxioms ComplexBessel Chart ChartGeometry

/-! ### Section 1: Strip multiplier definition, regularity, and antisymmetry -/

/-- Bounded antisymmetric strip multiplier at weight `w`,
`W̃_V(ζ) = e^{-c' Υ(ζ)} m_g(w/2 + c' ω(ζ))` (`lower_o1_two_edge.tex`, Lemma S4, `vlo:S4`). -/
noncomputable def tildeWW (w : ℕ) (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (-(c' : ℂ) * chartUpsilon ζ) *
    mellinMGEntireW w g ((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ)

/-- The size conditions on `c'` used throughout: `S ≤ c'/12`, `0 < c'/12`, `0 < c'`. -/
lemma shift_le_of_max_le (prob : FixedWeightProblem) {c' : ℝ}
    (hc : max 1 (24 * prob.totalShift) ≤ c') :
    prob.totalShift ≤ c' / 12 ∧ 0 < c' / 12 ∧ 0 < c' := by
  have h1 : (1 : ℝ) ≤ c' := (le_max_left _ _).trans hc
  have h2 : 24 * prob.totalShift ≤ c' := (le_max_right _ _).trans hc
  have hS := prob.totalShift_nonneg
  refine ⟨by linarith, by linarith, by linarith⟩

lemma tildeWW_differentiableOn (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) :
    DifferentiableOn ℂ (tildeWW prob.w c' g) stripOpen := by
  obtain ⟨hS, ha0, -⟩ := shift_le_of_max_le prob hc'
  have hmg : Differentiable ℂ (mellinMGEntireW prob.w g) :=
    differentiable_mellinMGEntireW prob.hw hg.cont hg.int_cardy (polyDom_cardyV prob hS ha0)
      hg.int_lift hg.fourier_odd
  have hup : DifferentiableOn ℂ chartUpsilon stripOpen :=
    lemma_S3_strip.2.2.1.differentiableOn
  have hom : DifferentiableOn ℂ chartOmega stripOpen :=
    lemma_S3_strip.1.differentiableOn
  refine (((hup.const_mul (-(c' : ℂ))).cexp)).mul ?_
  have hlin : DifferentiableOn ℂ (fun ζ => (prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ)
      stripOpen :=
    (differentiableOn_const _).add (hom.const_mul (c' : ℂ))
  exact hmg.comp_differentiableOn hlin

lemma tildeWW_continuousOn (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) :
    ContinuousOn (tildeWW prob.w c' g) stripClosed := by
  obtain ⟨hS, ha0, -⟩ := shift_le_of_max_le prob hc'
  have hmg : Continuous (mellinMGEntireW prob.w g) :=
    (differentiable_mellinMGEntireW prob.hw hg.cont hg.int_cardy (polyDom_cardyV prob hS ha0)
      hg.int_lift hg.fourier_odd).continuous
  have hup : ContinuousOn chartUpsilon stripClosed := lemma_S3_strip.2.2.2.1
  have hom : ContinuousOn chartOmega stripClosed := lemma_S3_strip.2.1
  refine ((hup.const_mul (-(c' : ℂ))).cexp).mul ?_
  have hlin : ContinuousOn (fun ζ => (prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ) stripClosed :=
    continuousOn_const.add (hom.const_mul (c' : ℂ))
  exact hmg.comp_continuousOn hlin

/-- Antisymmetry of the weight-`w` multiplier: the strip reflection is `ζ ↦ 1 - ζ` (the reflection
`z ↦ w - z` of Lemma S1 becomes `ω ↦ -ω`). -/
lemma tildeWW_reflect (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {ζ : ℂ} (hζ : ζ ∈ stripClosed) :
    tildeWW prob.w c' g (1 - ζ) = -tildeWW prob.w c' g ζ := by
  obtain ⟨hS, ha0, -⟩ := shift_le_of_max_le prob hc'
  unfold tildeWW
  rw [chartUpsilon_reflect hζ.1 hζ.2, chartOmega_reflect ζ]
  have harg : (prob.w : ℂ) / 2 + (c' : ℂ) * (-chartOmega ζ) =
      (prob.w : ℂ) - ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ) := by ring
  rw [harg, mellinMGEntireW_sub prob.hw hg.cont hg.int_cardy (polyDom_cardyV prob hS ha0)
    hg.int_lift hg.fourier_odd]
  ring

/-! ### Section 2: Left-edge identity -/

lemma edgeMu_ge_muStar_W (τ : ℝ) : muStar ≤ edgeMu τ := by
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

lemma tildeWW_left_edge_norm_eq (w : ℕ) {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ) (τ : ℝ) :
    ‖tildeWW w c' g ((τ : ℂ) * Complex.I)‖ =
      Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (τ : ℂ)))) *
        ‖mellinMGW g ((w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)))‖ := by
  have hmul : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
  have hμ_pos : 0 < edgeMu τ := lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar_W τ)
  have hω_re : 0 < (chartOmega (Complex.I * (τ : ℂ))).re := by
    rw [chartOmega_left_edge τ]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact hμ_pos
  have hz_re : 0 < ((w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
      Complex.re_ofReal_mul]
    have : (0 : ℝ) ≤ (w : ℝ) / 2 := by positivity
    nlinarith [mul_pos hc' hω_re]
  unfold tildeWW
  rw [hmul, norm_mul, Complex.norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    re_chartUpsilon_left_edge τ, mellinMGEntireW_of_re_pos w g hz_re]
  ring_nf

/-! ### Section 3: Growth bound in the open strip for Phragmén–Lindelöf -/

lemma tildeWW_strip_growth (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) :
    ∃ B : ℝ, tildeWW prob.w c' g =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo 0 1)]
      fun ζ => Real.exp (B * Real.exp (1 * |ζ.im|)) := by
  obtain ⟨hS, ha0, hc'_pos⟩ := shift_le_of_max_le prob hc'
  obtain ⟨C_om, hC_om, hOm_bd⟩ := chartOmega_strip_bound
  obtain ⟨C_up, hC_up, hUp_bd⟩ := chartUpsilon_strip_bound
  obtain ⟨K_mg, hK_mg, hMG⟩ := norm_mellinMGW_le_exp prob hS ha0
  have hM_nn : 0 ≤ prob.cardyNorm (c' / 12) g := prob.cardyNorm_nonneg hS g
  have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
  let D : ℝ := (prob.w : ℝ) / 2 + 1 + c' * C_om
  have hD_nn : 0 ≤ D := by positivity
  let K : ℝ := c' * C_up + K_mg * D ^ 2
  have hK_nn : 0 ≤ K := by positivity
  let B : ℝ := K * 24 * Real.exp 1
  refine ⟨B, Asymptotics.IsBigO.of_bound (prob.cardyNorm (c' / 12) g) ?_⟩
  filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with ζ hζ_re
  have hζ_mem : ζ ∈ stripOpen := hζ_re
  have hζ_cl : ζ ∈ stripClosed := ⟨hζ_mem.1.le, hζ_mem.2.le⟩
  have h_half_bd : ∀ {v : ℂ}, v ∈ stripClosed → v.re ≤ 1 / 2 →
      ‖tildeWW prob.w c' g v‖ ≤ prob.cardyNorm (c' / 12) g *
        Real.exp (K * (1 + |v.im|) ^ 4) := by
    intro v hv hv_half
    have hω_re : 0 ≤ (chartOmega v).re := lemma_J7Q.2 v hv.1 hv_half
    set z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega v with hz_def
    have hz_re : 1 / 2 ≤ z.re := by
      simp only [z, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
        Complex.re_ofReal_mul]
      nlinarith [mul_nonneg hc'_pos.le hω_re]
    have hz_pos : 0 < z.re := by linarith
    have hω_bd := hOm_bd v hv
    have hup_bd := hUp_bd v hv
    have hsq_le : 1 + v.im ^ 2 ≤ (1 + |v.im|) ^ 2 := by
      nlinarith [abs_nonneg v.im, sq_abs v.im]
    have h1z_le : 1 + ‖z‖ ≤ D * (1 + |v.im|) ^ 2 := by
      have hz_norm : ‖z‖ ≤ (prob.w : ℝ) / 2 + c' * ‖chartOmega v‖ := by
        calc ‖(prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega v‖
            ≤ ‖((prob.w : ℂ) / 2)‖ + ‖(c' : ℂ) * chartOmega v‖ := norm_add_le _ _
          _ = (prob.w : ℝ) / 2 + c' * ‖chartOmega v‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le, norm_div,
                Complex.norm_natCast]
              norm_num
      have h12 : (1 : ℝ) ≤ (1 + |v.im|) ^ 2 := by
        have : 1 ≤ 1 + |v.im| := by linarith [abs_nonneg v.im]
        nlinarith
      have hw2 : (0 : ℝ) ≤ (prob.w : ℝ) / 2 := by positivity
      calc 1 + ‖z‖ ≤ 1 + ((prob.w : ℝ) / 2 + c' * ‖chartOmega v‖) := by linarith
        _ ≤ ((prob.w : ℝ) / 2 + 1) + c' * (C_om * (1 + v.im ^ 2)) := by
            have := mul_le_mul_of_nonneg_left hω_bd hc'_pos.le
            linarith
        _ ≤ ((prob.w : ℝ) / 2 + 1) * (1 + |v.im|) ^ 2 + c' * C_om * (1 + |v.im|) ^ 2 := by
            have h1 := mul_le_mul_of_nonneg_left hsq_le (mul_nonneg hc'_pos.le hC_om.le)
            have h2 : ((prob.w : ℝ) / 2 + 1) * 1 ≤ ((prob.w : ℝ) / 2 + 1) * (1 + |v.im|) ^ 2 :=
              mul_le_mul_of_nonneg_left h12 (by linarith)
            nlinarith
        _ = D * (1 + |v.im|) ^ 2 := by simp only [D]; ring
    have h1w_ge1 : (1 : ℝ) ≤ 1 + |v.im| := by linarith [abs_nonneg v.im]
    have hsq_le4 : 1 + v.im ^ 2 ≤ (1 + |v.im|) ^ 4 := by
      calc 1 + v.im ^ 2 ≤ (1 + |v.im|) ^ 2 := hsq_le
        _ ≤ (1 + |v.im|) ^ 2 * (1 + |v.im|) ^ 2 := by nlinarith
        _ = (1 + |v.im|) ^ 4 := by ring
    have hexp_up : ‖Complex.exp (-(c' : ℂ) * chartUpsilon v)‖ ≤
        Real.exp (c' * C_up * (1 + |v.im|) ^ 4) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have h1 : (-(c' : ℂ) * chartUpsilon v).re ≤ ‖-(c' : ℂ) * chartUpsilon v‖ :=
        Complex.re_le_norm _
      have h2 : ‖-(c' : ℂ) * chartUpsilon v‖ = c' * ‖chartUpsilon v‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc'_pos.le]
      calc (-(c' : ℂ) * chartUpsilon v).re ≤ c' * ‖chartUpsilon v‖ := h1.trans_eq h2
        _ ≤ c' * (C_up * (1 + v.im ^ 2)) := by gcongr
        _ ≤ c' * (C_up * (1 + |v.im|) ^ 4) := by gcongr
        _ = c' * C_up * (1 + |v.im|) ^ 4 := by ring
    have hmg_bd := hMG hg hz_re
    have hexp_mg : ‖mellinMGEntireW prob.w g z‖ ≤
        prob.cardyNorm (c' / 12) g * Real.exp (K_mg * D ^ 2 * (1 + |v.im|) ^ 4) := by
      rw [mellinMGEntireW_of_re_pos prob.w g hz_pos]
      refine hmg_bd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM_nn)
      have hsq1z : (1 + ‖z‖) ^ 2 ≤ (D * (1 + |v.im|) ^ 2) ^ 2 := by gcongr
      calc K_mg * (1 + ‖z‖) ^ 2
          ≤ K_mg * (D * (1 + |v.im|) ^ 2) ^ 2 := by gcongr
        _ = K_mg * D ^ 2 * (1 + |v.im|) ^ 4 := by ring
    unfold tildeWW
    rw [norm_mul]
    calc ‖Complex.exp (-(c' : ℂ) * chartUpsilon v)‖ * ‖mellinMGEntireW prob.w g z‖
        ≤ Real.exp (c' * C_up * (1 + |v.im|) ^ 4) *
            (prob.cardyNorm (c' / 12) g *
              Real.exp (K_mg * D ^ 2 * (1 + |v.im|) ^ 4)) := by gcongr
      _ = prob.cardyNorm (c' / 12) g * Real.exp (K * (1 + |v.im|) ^ 4) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; simp only [K]; ring
  have hζ_bd : ‖tildeWW prob.w c' g ζ‖ ≤ prob.cardyNorm (c' / 12) g *
      Real.exp (K * (1 + |ζ.im|) ^ 4) := by
    rcases le_or_gt ζ.re (1 / 2) with hle | hgt
    · exact h_half_bd hζ_cl hle
    · have h1ζ_cl : 1 - ζ ∈ stripClosed :=
        ⟨by simp; linarith [hζ_cl.2], by simp; linarith [hζ_cl.1]⟩
      have h1ζ_half : (1 - ζ).re ≤ 1 / 2 := by simp; linarith
      have href := tildeWW_reflect prob hc' hg hζ_cl
      have hnorm_eq : ‖tildeWW prob.w c' g ζ‖ = ‖tildeWW prob.w c' g (1 - ζ)‖ := by
        rw [href, norm_neg]
      rw [hnorm_eq]
      simpa [Complex.sub_im, abs_neg] using h_half_bd h1ζ_cl h1ζ_half
  have hpow4_le : (1 + |ζ.im|) ^ 4 ≤ 24 * Real.exp 1 * Real.exp (1 * |ζ.im|) := by
    have hfac := Real.pow_div_factorial_le_exp (1 + |ζ.im|) (by positivity) 4
    have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h4, div_le_iff₀ (by norm_num)] at hfac
    rw [Real.exp_add] at hfac
    rw [one_mul]
    linarith
  have h_final : ‖tildeWW prob.w c' g ζ‖ ≤ prob.cardyNorm (c' / 12) g *
      Real.exp (B * Real.exp (1 * |ζ.im|)) := by
    refine hζ_bd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM_nn)
    calc K * (1 + |ζ.im|) ^ 4
        ≤ K * (24 * Real.exp 1 * Real.exp (1 * |ζ.im|)) := by gcongr
      _ = B * Real.exp (1 * |ζ.im|) := by simp only [B]; ring
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact h_final

/-! ### Section 4: Lemma S4 at weight `w` (`vlo:S4`) -/

/-- **Lemma S4 at weight `w` (bounded antisymmetric multiplier)** (`lower_o1_two_edge.tex`, §J2,
`vlo:S4`): for a fixed-weight problem `prob` (weight `w = prob.w ≥ 1`, any `Q`) there exist `C > 0`
and `c₀ ≥ max 1 (24 S)` such that for all `c' ≥ c₀` and every `g ∈ TestClass prob (c' / 12)`, the
function `W̃_V(ζ) = e^{-c'Υ(ζ)} m_g(w/2 + c' ω(ζ))` is holomorphic on `stripOpen`, continuous on
`stripClosed`, antisymmetric (`W̃_V(1 - ζ) = -W̃_V(ζ)`), and bounded by `C M[g]` on `stripClosed`.
The Virasoro Lemma S4 is the `w = 1` instance (`LemmaS4WBridge`). -/
theorem lemma_S4_W (prob : FixedWeightProblem) :
    ∃ C c₀ : ℝ, 0 < C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass prob (c' / 12) g →
        DifferentiableOn ℂ (tildeWW prob.w c' g) stripOpen ∧
        ContinuousOn (tildeWW prob.w c' g) stripClosed ∧
        (∀ ζ ∈ stripClosed, tildeWW prob.w c' g (1 - ζ) = -tildeWW prob.w c' g ζ) ∧
        (∀ ζ ∈ stripClosed, ‖tildeWW prob.w c' g ζ‖ ≤ C * prob.cardyNorm (c' / 12) g) := by
  let μ₀ : ℝ := (Real.pi * xiStar / 6 + muStar) / 2
  have hμ₀ : Real.pi * xiStar / 6 < μ₀ := by
    dsimp [μ₀]; unfold muStar
    have : 0 < Real.pi * xiStar := mul_pos Real.pi_pos xiStar_pos
    linarith
  have hμ₀_le_muStar : μ₀ ≤ muStar := by
    dsimp [μ₀]; unfold muStar
    have : 0 < Real.pi * xiStar := mul_pos Real.pi_pos xiStar_pos
    linarith
  obtain ⟨C, c₀, hC_pos, hc₀, hS2⟩ := lemma_S2_W prob hμ₀
  refine ⟨C, c₀, hC_pos, hc₀, fun {c'} hc' {g} hg => ?_⟩
  have hc'max : max 1 (24 * prob.totalShift) ≤ c' := hc₀.trans hc'
  obtain ⟨hS, ha0, hc'_pos⟩ := shift_le_of_max_le prob hc'max
  have hdiff := tildeWW_differentiableOn prob hc'max hg
  have hcont := tildeWW_continuousOn prob hc'max hg
  have href : ∀ ζ ∈ stripClosed, tildeWW prob.w c' g (1 - ζ) = -tildeWW prob.w c' g ζ :=
    fun ζ hζ => tildeWW_reflect prob hc'max hg hζ
  refine ⟨hdiff, hcont, href, fun ζ hζ => ?_⟩
  have hleft : ∀ v : ℂ, v.re = 0 →
      ‖tildeWW prob.w c' g v‖ ≤ C * prob.cardyNorm (c' / 12) g := by
    intro v hv_re
    have hv_eq : v = (v.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hv_re]
    rw [hv_eq, tildeWW_left_edge_norm_eq prob.w hc'_pos g v.im]
    have hω_re : μ₀ ≤ (chartOmega (Complex.I * (v.im : ℂ))).re := by
      rw [chartOmega_left_edge v.im]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
      exact hμ₀_le_muStar.trans (edgeMu_ge_muStar_W v.im)
    have hS2_bd := (hS2 hc' hω_re hg).2
    have hexp_pos : 0 ≤ Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ)))) :=
      (Real.exp_pos _).le
    calc Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ)))) *
            ‖mellinMGW g ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (v.im : ℂ)))‖
        ≤ Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ)))) *
            (C * Real.exp (c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ)))) *
              prob.cardyNorm (c' / 12) g) := by gcongr
      _ = C * (Real.exp (-c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ)))) *
              Real.exp (c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ))))) *
            prob.cardyNorm (c' / 12) g := by ring
      _ = C * prob.cardyNorm (c' / 12) g := by
          rw [← Real.exp_add,
            show -c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ))) +
              c' * crudeExponentB (chartOmega (Complex.I * (v.im : ℂ))) = 0 by ring,
            Real.exp_zero, mul_one]
  have hright : ∀ v : ℂ, v.re = 1 →
      ‖tildeWW prob.w c' g v‖ ≤ C * prob.cardyNorm (c' / 12) g := by
    intro v hv_re
    have hv_cl : v ∈ stripClosed := ⟨by linarith, by linarith⟩
    have h1v_re : (1 - v).re = 0 := by simp [hv_re]
    rw [show ‖tildeWW prob.w c' g v‖ = ‖tildeWW prob.w c' g (1 - v)‖ by
      rw [href v hv_cl, norm_neg]]
    exact hleft (1 - v) h1v_re
  have hcl_sub : closure (Complex.re ⁻¹' Ioo (0 : ℝ) 1) ⊆ stripClosed :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_re)
  have hfd : DiffContOnCl ℂ (tildeWW prob.w c' g) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) :=
    ⟨hdiff, hcont.mono hcl_sub⟩
  obtain ⟨B, hB⟩ := tildeWW_strip_growth prob hc'max hg
  have hc_lt : (1 : ℝ) < Real.pi / (1 - 0) := by
    rw [sub_zero, div_one]; linarith [Real.pi_gt_three]
  exact PhragmenLindelof.vertical_strip hfd ⟨1, hc_lt, B, hB⟩ hleft hright hζ.1 hζ.2

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.tildeWW_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.tildeWW_reflect

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S4_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.lemma_S4_W

end FormalResearch.ModularBootstrap.FixedWeightBand
