module

public import FormalResearch.ModularBootstrap.Contour.TruncationError
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS4W
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaS2W
public import FormalResearch.ModularBootstrap.FixedWeightBand.StirlingW
public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinWBridge
public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP

/-!
# Truncated Mellin density at weight `w`: definitions, interface and decomposition (Lemma D', `vlo:Dp`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, step (Z), Lemma D' (`vlo:Dp`) and Lemma Z
(`vlo:Z`), at every fixed weight problem `prob : FixedWeightProblem` (weight `w = prob.w ≥ 1`, null
shifts `Q`).  The Virasoro versions are `Contour/TruncationError.lean` (Lemma D'),
`Contour/WindowEnvelope.lean` (Lemma Z), `Contour/InnerTipBounds.lean`.

## Decomposition into modules (what each consumes and produces)

* `TruncationWDefs` (this file).
  Consumes: the weight-free Virasoro contour data `dpConfig`, `dpT0` (`lemma_Zp`), the chart
  `virasoroBChart`/`virasoroDeltaChartC`, `StirlingW`, `MellinW`, `LemmaS2W`, `LemmaS4W`, `PropositionP`
  (`UniformPropositionPData`, `W_C_prob_norm_le`, `chartAC`).
  Produces: `dpThr`, `mellinDensityIntegrandW`, `truncatedMellinPW` (the density `P` of eq. `vlo:eP` with
  `z = w/2 + c' ω`), the entire-extension wrapper `testClass_differentiable_mellinMGEntireW`, the complex
  weight bound `cardyVC_inner_bound` (`V_C = cardyVC prob (c'/12)`, the `W3` asymptote only on
  `|b - ξ_*| ≤ r_1`, i.e. on `closedBall 0 (chartAC r_1 c' ^ 2)`), the Stirling^(w) prefactor bound
  `norm_stirlingPrefW_le` and the pointwise density factorisation
  `mellinDensityIntegrandW_eq`, `norm_mellinDensityIntegrandW_le_*` for contour pieces.
* `TruncationWAnalytic`: holomorphy of `truncatedMellinPW` on the inner disc, conjugation symmetry, reality
  on the real diameter (Virasoro `truncatedMellinP_analyticOnNhd`, `truncatedMellinP_conj`).
  Consumes the `Defs` interface and the weight-free chart lemmas `virasoroBChart_inner_*`.
* `TruncationWMidline`: real-axis Mellin inversion at `Re z = w/2` and the tail bound along the midline
  `ζ = 1/2 + iτ` (Virasoro `midline*`, `mellin_midline_tail_exists`).  Consumes `lemma_S4_W`, the Stirling^(w)
  bounds, `chartOmega_strip_bound` for `|ω|^{(w-1)/2}`, and `dpConfig.hmid_tail`; produces
  `truncatedMellinPW_real_integral_eq` and `mellin_midline_tail_exists_W`.
* `TruncationWReal`: exponential truncation error on the real chart diameter
  (Virasoro `truncatedMellinP_real_err`).
* `TruncationWContour`: deformation to the saddle contour and the inner bound
  `‖P‖ ≤ C_P c'^{1/3} airyEnv` (Virasoro `truncatedMellinP_eq_contourIntegral`, `truncatedMellinP_inner_bound`).
  Consumes `lemma_S2_W`, `lemma_S4_W`, `cardyVC_inner_bound`, `lemma_S6`.
* `TruncationWHalfPlane`, `TruncationWDp`: the half-plane two-constants argument and Lemma D' proper
  (Virasoro section 6, `lemma_Dp`), against `psiTilde prob` and the general type-(II) envelope
  `psiTilde_typeII_envelope_general`.
* `TruncationWZ*`: the window lemma Z (Virasoro `WindowEnvelope`).

Statement shape: constants are existential and independent of `c'`; the inner disc is
`closedBall 0 (c₀_D c'^{2/3})` with `c₀_D ≤ min (innerChartRadius/4) (2 chartBV(r_1)²)`, so that both the
weight-free inner-chart facts (`innerChartRadius`) and the `W3` disc `|b - ξ_*| ≤ r_1` apply.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval FourierTransform

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special
open FormalResearch.ModularBootstrap.Chart
open FormalResearch.ModularBootstrap.ChartGeometry
open FormalResearch.ModularBootstrap.ComplexBessel
open FormalResearch.ModularBootstrap.StripMultiplier
open FormalResearch.ModularBootstrap.Mellin
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Contour
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### 1. Threshold, density integrand and truncated density -/

/-- Common lower threshold for `c'` in this development (`10000 ≤ c'` and `24 S ≤ c'`). -/
noncomputable def dpThr (prob : FixedWeightProblem) : ℝ := max 10000 (24 * prob.totalShift)

lemma dpThr_ge_10000 (prob : FixedWeightProblem) : 10000 ≤ dpThr prob := le_max_left _ _

lemma dpThr_pos (prob : FixedWeightProblem) : 0 < dpThr prob :=
  lt_of_lt_of_le (by norm_num) (dpThr_ge_10000 prob)

lemma max_one_le_of_dpThr_le (prob : FixedWeightProblem) {c' : ℝ} (hc' : dpThr prob ≤ c') :
    max 1 (24 * prob.totalShift) ≤ c' :=
  max_le (by linarith [dpThr_ge_10000 prob]) ((le_max_right _ _).trans hc')

/-- Mellin integrand `ω ↦ Γ(w/2 + c' ω) (2π t)^{-(w/2 + c' ω)} m_g(w/2 + c' ω)`. -/
noncomputable def mellinDensityIntegrandW (w : ℕ) (c' : ℝ) (g : ℝ → ℝ) (t ω : ℂ) : ℂ :=
  let z : ℂ := (w : ℂ) / 2 + (c' : ℂ) * ω
  Complex.Gamma z * (2 * (Real.pi : ℂ) * t) ^ (-z) * mellinMGEntireW w g z

/-- Truncated Mellin density `P(ũ)` (`lower_o1_two_edge.tex`, Lemma D' `vlo:Dp`, eq. `vlo:eP`) at weight `w`:
`P(ũ) = (-Δ'(ũ) / M[g]) V(Δ(ũ)) (c' / (2πi)) ∫_{ω(1/2 + iT₀)}^{ω(1/2 - iT₀)} Γ(z)(2π t)^{-z} m_g(z) dω`,
`z = w/2 + c' ω`. -/
noncomputable def truncatedMellinPW (prob : FixedWeightProblem) (c' T₀ : ℝ) (g : ℝ → ℝ)
    (u : ℂ) : ℂ :=
  let M : ℂ := (prob.cardyNorm (c' / 12) g : ℂ);
  let t : ℂ := virasoroDeltaChartC c' u;
  let ω₀ : ℂ := chartOmega ((1 / 2 : ℂ) + Complex.I * (T₀ : ℂ));
  let ω₁ : ℂ := chartOmega ((1 / 2 : ℂ) - Complex.I * (T₀ : ℂ));
  -(deriv (virasoroDeltaChartC c') u / M) * cardyVC prob (c' / 12) t *
    ((c' : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) *
    ∫ s in (0 : ℝ)..(1 : ℝ),
      mellinDensityIntegrandW prob.w c' g t ((1 - (s : ℂ)) * ω₀ + (s : ℂ) * ω₁) * (ω₁ - ω₀)

/-- The weight-one density is the Virasoro one (`cardyVC virasoroProblem (c'/12) = V_C c'`). -/
lemma mellinDensityIntegrandW_one (c' : ℝ) (g : ℝ → ℝ) (t ω : ℂ) :
    mellinDensityIntegrandW 1 c' g t ω = mellinDensityIntegrand c' g t ω := by
  unfold mellinDensityIntegrandW mellinDensityIntegrand
  simp only [Nat.cast_one]
  rw [mellinMGEntireW_one_eq]

/-! ### 2. Entire Mellin density for a test function -/

lemma testClass_differentiable_mellinMGEntireW (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) :
    Differentiable ℂ (mellinMGEntireW prob.w g) := by
  obtain ⟨hS, ha0, -⟩ := shift_le_of_max_le prob hc'
  exact differentiable_mellinMGEntireW prob.hw hg.cont hg.int_cardy (polyDom_cardyV prob hS ha0)
    hg.int_lift hg.fourier_odd

/-! ### 3. Complex weight bound on the chart disc (`W3` on `|b - ξ_*| ≤ r_1`) -/

/-- Complex weight bound `‖V(Δ(ũ))‖ ≤ C_V c'^{-1/2} e^{c' Re L(b)}` on `|ũ| ≤ A_{c'}(r_1)²`
(the `ε (2c'/3) b` rescaling of `W_C_prob_norm_le`). -/
theorem cardyVC_inner_bound {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_V C_V : ℝ, D.c₀ ≤ c_V ∧ 39 ≤ c_V ∧ 0 < C_V ∧
      ∀ {c' : ℝ}, c_V ≤ c' → ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) →
        ‖cardyVC prob (c' / 12) (virasoroDeltaChartC c' u)‖ ≤
          C_V * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL (virasoroBChart c' u)).re) := by
  let P₀ := D.pAt (le_rfl : D.c₀ ≤ D.c₀)
  obtain ⟨c_Q_disc, C_Q_disc, hcQ_pos, hCQ_le, hCQ_disc⟩ :=
    disc_Q_bounds D.hr1_pos.le D.hr1_le (Q_star := D.Q_star)
      (by rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]; exact P₀.p2_Q_holo)
      (fun {b} hb => by
        rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]
        exact P₀.p2_Q_ne_zero (by rwa [D.uniform_r_1 (le_rfl : D.c₀ ≤ D.c₀)]))
  have hCQ_pos : 0 < C_Q_disc := hcQ_pos.trans_le hCQ_le
  let C_W_fac : ℝ := (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
    Real.sqrt (2 * π ^ 2 * xiStar / 3)
  let C_W_hi : ℝ := C_W_fac * (C_Q_disc + D.η_V_max)
  have hxi := xiStar_pos
  have hCW_hi_pos : 0 < C_W_hi := by
    have hCQ_sum : 0 < C_Q_disc + D.η_V_max := add_pos_of_pos_of_nonneg hCQ_pos D.hηV_max_nn
    dsimp [C_W_hi, C_W_fac]
    positivity
  refine ⟨max D.c₀ 39, C_W_hi * (3 / 2) * (2 / xiStar), le_max_left _ _, le_max_right _ _,
    by positivity, fun {c'} hc' {u} hu => ?_⟩
  have hc'_c₀ : D.c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hc'_pos : 0 < c' := by linarith [le_max_right D.c₀ 39]
  set P := D.pAt hc'_c₀
  set b := virasoroBChart c' u with hb_def
  have hb_disc : b ∈ closedBall (xiStar : ℂ) P.r_1 := by
    rw [D.uniform_r_1 hc'_c₀, mem_closedBall, dist_eq_norm]
    exact virasoroBChart_sub_xiStar_le_r1 D.hr1_pos hc'_pos hu
  have hW_raw := W_C_prob_norm_le P (C_Q := C_Q_disc) (fun b' hb' => by
    rw [D.uniform_Q_star hc'_c₀]
    exact (hCQ_disc b' (by rwa [← D.uniform_r_1 hc'_c₀])).2) hb_disc
  dsimp only at hW_raw
  have hW_ub : ‖W_C_prob prob c' b‖ ≤ C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
    have hη_le : P.η_V ≤ D.η_V_max := D.uniform_ηV_le hc'_c₀
    have hCWf_nn : 0 ≤ C_W_fac := by dsimp [C_W_fac]; positivity
    calc ‖W_C_prob prob c' b‖
        ≤ C_W_fac * (C_Q_disc + P.η_V) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := hW_raw
      _ ≤ C_W_fac * (C_Q_disc + D.η_V_max) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
          gcongr
      _ = C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := rfl
  have hu_vir : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) :=
    chart_mem_virasoroClosedBall D.hr1_pos hc'_pos hu
  have hbd := virasoro_deltaChart_b_min hc'_pos hu_vir
  have hb_re : xiStar / 2 ≤ b.re := by
    have h1 := (Complex.abs_re_le_norm _).trans
      (hbd.trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [Complex.sub_re, Complex.ofReal_re, abs_le] at h1
    linarith [h1.1]
  have hb_norm : xiStar / 2 ≤ ‖b‖ := hb_re.trans (Complex.re_le_norm _)
  have hΔ : virasoroDeltaChartC c' u = (c' : ℂ) * b ^ 2 / 3 := virasoroDeltaChartC_eq_bChart_sq u
  have hε : 0 < tipEps c' := tipEps_pos hc'_pos
  have hW_eq : W_C_prob prob c' b = (((tipEps c' * (2 * c' / 3) : ℝ) : ℂ) * b) *
      cardyVC prob (c' / 12) (virasoroDeltaChartC c' u) := by
    unfold W_C_prob
    rw [hΔ]; push_cast; ring
  have hcoef : ‖(((tipEps c' * (2 * c' / 3) : ℝ) : ℂ) * b)‖ =
      (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    congr 1
    unfold tipEps
    calc c' ^ (-(2 / 3 : ℝ)) * (2 * c' / 3)
        = (2 / 3 : ℝ) * (c' * c' ^ (-(2 / 3 : ℝ))) := by ring
      _ = (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_one_add' hc'_pos.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]
          norm_num
  have hc13 : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  have hden_pos : 0 < (2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖ := by
    have : 0 < ‖b‖ := lt_of_lt_of_le (by positivity) hb_norm
    positivity
  rw [hW_eq, norm_mul, hcoef] at hW_ub
  have hV_le : ‖cardyVC prob (c' / 12) (virasoroDeltaChartC c' u)‖ ≤
      (C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) /
        ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖) := by
    rw [le_div_iff₀ hden_pos]
    linarith [hW_ub]
  refine hV_le.trans ?_
  have hpow : c' ^ (-(1 / 6 : ℝ)) / c' ^ (1 / 3 : ℝ) = c' ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_sub hc'_pos]; norm_num
  have hb_pos : 0 < ‖b‖ := lt_of_lt_of_le (by positivity) hb_norm
  calc (C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) /
        ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * ‖b‖)
      ≤ (C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) /
        ((2 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) * (xiStar / 2)) := by
        gcongr
    _ = C_W_hi * (3 / 2) * (2 / xiStar) * c' ^ (-(1 / 2 : ℝ)) * Real.exp (c' * (tipL b).re) := by
        rw [← hpow]
        field_simp
    _ = _ := by rw [hb_def]

/-! ### 4. Stirling^(w) prefactor and the pointwise factorisation of the density -/

/-- `|Im b| < Re b` gives `|arg b| < π/4`. -/
lemma abs_arg_lt_pi_div_four_of_abs_im_lt_re {b : ℂ} (h : |b.im| < b.re) : |b.arg| < Real.pi / 4 := by
  have hre : 0 < b.re := lt_of_le_of_lt (abs_nonneg _) h
  have harg_lt : |b.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have htan : |Real.tan b.arg| < 1 := by
    rw [Complex.tan_arg, abs_div, abs_of_pos hre, div_lt_one hre]
    exact h
  have h1 := abs_lt.mp harg_lt
  have h2 := abs_lt.mp htan
  have hmono := Real.strictMonoOn_tan
  have hpi4 : Real.tan (Real.pi / 4) = 1 := Real.tan_pi_div_four
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have hle : b.arg ≤ -(Real.pi / 4) := hcon
    have hm : Real.tan b.arg ≤ Real.tan (-(Real.pi / 4)) :=
      hmono.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hle
    rw [Real.tan_neg, hpi4] at hm
    linarith [h2.1]
  · by_contra hcon
    push Not at hcon
    have hm : Real.tan (Real.pi / 4) ≤ Real.tan b.arg :=
      hmono.monotoneOn ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ⟨by linarith, by linarith⟩ hcon
    rw [hpi4] at hm
    linarith [h2.2]

/-- Norm of the Stirling^(w) prefactor `(3ω/(2π b²))^{(w-1)/2}`: `= (3‖ω‖/(2π‖b‖²))^{(w-1)/2}`. -/
lemma norm_stirlingPrefW_eq (w : ℕ) (ω b : ℂ) :
    ‖stirlingPrefW w ω b‖ = (3 * ‖ω‖ / (2 * Real.pi * ‖b‖ ^ 2)) ^ (((w : ℝ) - 1) / 2) := by
  unfold stirlingPrefW
  have hexp : (((w : ℂ) - 1) / 2) = ((((w : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.norm_cpow_real]
  congr 1
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, h2pi]

/-- Upper bound for the Stirling^(w) prefactor when `‖ω‖ ≤ B` and `β ≤ ‖b‖`. -/
lemma norm_stirlingPrefW_le {w : ℕ} (hw : 1 ≤ w) {ω b : ℂ} {B β : ℝ} (hβ : 0 < β)
    (hω : ‖ω‖ ≤ B) (hb : β ≤ ‖b‖) :
    ‖stirlingPrefW w ω b‖ ≤ (3 * B / (2 * Real.pi * β ^ 2)) ^ (((w : ℝ) - 1) / 2) := by
  rw [norm_stirlingPrefW_eq]
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hexp : 0 ≤ ((w : ℝ) - 1) / 2 := by linarith
  have hπ := Real.pi_pos
  have hnn : 0 ≤ 3 * ‖ω‖ / (2 * Real.pi * ‖b‖ ^ 2) := by positivity
  refine Real.rpow_le_rpow hnn ?_ hexp
  have hβb : β ^ 2 ≤ ‖b‖ ^ 2 := pow_le_pow_left₀ hβ.le hb 2
  have hbpos : 0 < β ^ 2 := by positivity
  calc 3 * ‖ω‖ / (2 * Real.pi * ‖b‖ ^ 2) ≤ 3 * ‖ω‖ / (2 * Real.pi * β ^ 2) := by
        gcongr
    _ ≤ 3 * B / (2 * Real.pi * β ^ 2) := by gcongr

/-- On the inner chart disc, the chart value `b(ũ)` has `3 ξ_*/4 ≤ Re b`, `|Im b| ≤ ξ_*/4`,
hence `|arg b| < π/4`. -/
lemma inner_chart_arg_lt {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (innerChartRadius * c' ^ (2 / 3 : ℝ))) :
    3 * xiStar / 4 ≤ (virasoroBChart c' u).re ∧
      |(virasoroBChart c' u).im| ≤ xiStar / 4 ∧ |(virasoroBChart c' u).arg| < Real.pi / 4 := by
  have hbd := virasoroBChart_inner_bounds hc' hu
  have hxi4 : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ xiStar / 4 :=
    hbd.2.1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))))
  have hre := (Complex.abs_re_le_norm _).trans hxi4
  have him := (Complex.abs_im_le_norm _).trans hxi4
  rw [Complex.sub_re, Complex.ofReal_re, abs_le] at hre
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  have hxi := xiStar_pos
  have h1 : 3 * xiStar / 4 ≤ (virasoroBChart c' u).re := by linarith [hre.1]
  refine ⟨h1, him, abs_arg_lt_pi_div_four_of_abs_im_lt_re ?_⟩
  linarith

/-- Pointwise factorisation of the Mellin integrand at weight `w` (`vlo:stirling`, `vlo:S4`):
for `ω = ω(ζ)` with `Re ω ≥ 0`, `ω ≠ 0`, `Re b > 0`, `|arg b| < π/4`, `t = c' b²/3`,
`Γ(z)(2π t)^{-z} m_g(z) e^{...} = pref · t^{-1/2} · S · e^{c' Φ_V(ζ; b) - c' L(b)} · W̃_V(ζ)`. -/
lemma mellinDensityIntegrandW_strip_eq {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ)
    {ζ b : ℂ} (hω_re : 0 ≤ (chartOmega ζ).re) (hω_ne : chartOmega ζ ≠ 0) (hb_re : 0 < b.re)
    (hb : |b.arg| < Real.pi / 4) :
    mellinDensityIntegrandW w c' g ((c' : ℂ) * b ^ 2 / 3) (chartOmega ζ) =
      stirlingPrefW w (chartOmega ζ) b * ((c' : ℂ) * b ^ 2 / 3) ^ (-(1 / 2 : ℂ)) *
        stirlingSW w c' (chartOmega ζ) *
        Complex.exp ((c' : ℂ) * chartPhiV ζ b - (c' : ℂ) * tipL b) * tildeWW w c' g ζ := by
  have h_st := gamma_mul_two_pi_t_cpow_neg_W hw hc' hω_re hω_ne hb_re hb
  unfold mellinDensityIntegrandW
  dsimp only
  calc Complex.Gamma ((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ) *
        (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^ (-((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ)) *
        mellinMGEntireW w g ((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ)
      = (Complex.Gamma ((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ) *
        (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^
          (-((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ))) *
        mellinMGEntireW w g ((w : ℂ) / 2 + (c' : ℂ) * chartOmega ζ) := rfl
    _ = _ := by
        rw [h_st]
        unfold tildeWW chartPhiV
        have hex : Complex.exp ((c' : ℂ) * stirlingJ (chartOmega ζ) b) =
            Complex.exp ((c' : ℂ) * (chartUpsilon ζ + stirlingJ (chartOmega ζ) b + tipL b) -
              (c' : ℂ) * tipL b) * Complex.exp (-(c' : ℂ) * chartUpsilon ζ) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [hex]; ring

/-- Pointwise factorisation of the Mellin integrand off the strip (crude exponent):
`Γ(z)(2π t)^{-z} m_g(z) = pref · t^{-1/2} · S · e^{c' J(ω; b)} · m_g(w/2 + c' ω)` for `Re z > 0`. -/
lemma mellinDensityIntegrandW_crude_eq {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') (g : ℝ → ℝ)
    {ω b : ℂ} (hω_re : 0 ≤ ω.re) (hω_ne : ω ≠ 0) (hb_re : 0 < b.re)
    (hb : |b.arg| < Real.pi / 4) :
    mellinDensityIntegrandW w c' g ((c' : ℂ) * b ^ 2 / 3) ω =
      stirlingPrefW w ω b * ((c' : ℂ) * b ^ 2 / 3) ^ (-(1 / 2 : ℂ)) * stirlingSW w c' ω *
        Complex.exp ((c' : ℂ) * stirlingJ ω b) *
        mellinMGW g ((w : ℂ) / 2 + (c' : ℂ) * ω) := by
  have h_st := gamma_mul_two_pi_t_cpow_neg_W hw hc' hω_re hω_ne hb_re hb
  have hz_re : 0 < ((w : ℂ) / 2 + (c' : ℂ) * ω).re := by
    have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.re_ofReal_mul]
    have := mul_nonneg hc'.le hω_re
    linarith
  unfold mellinDensityIntegrandW
  dsimp only
  rw [mellinMGEntireW_of_re_pos w g hz_re]
  calc Complex.Gamma ((w : ℂ) / 2 + (c' : ℂ) * ω) *
        (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^ (-((w : ℂ) / 2 + (c' : ℂ) * ω)) *
        mellinMGW g ((w : ℂ) / 2 + (c' : ℂ) * ω)
      = (Complex.Gamma ((w : ℂ) / 2 + (c' : ℂ) * ω) *
        (2 * (Real.pi : ℂ) * ((c' : ℂ) * b ^ 2 / 3)) ^ (-((w : ℂ) / 2 + (c' : ℂ) * ω))) *
        mellinMGW g ((w : ℂ) / 2 + (c' : ℂ) * ω) := rfl
    _ = _ := by rw [h_st]; ring

/-! ### 5. Real part of the Mellin argument -/

lemma re_wHalf_add_mul (w : ℕ) (c' : ℝ) (ω : ℂ) :
    (((w : ℂ) / 2 + (c' : ℂ) * ω)).re = (w : ℝ) / 2 + c' * ω.re := by
  simp [Complex.add_re]

lemma re_wHalf_add_mul_pos {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 ≤ c') {ω : ℂ} (hω : 0 ≤ ω.re) :
    0 < (((w : ℂ) / 2 + (c' : ℂ) * ω)).re := by
  rw [re_wHalf_add_mul]
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have := mul_nonneg hc' hω
  linarith

lemma re_wHalf_add_mul_of_re_zero (w : ℕ) (c' : ℝ) {ω : ℂ} (hω : ω.re = 0) :
    (((w : ℂ) / 2 + (c' : ℂ) * ω)).re = (w : ℝ) / 2 := by
  rw [re_wHalf_add_mul, hω, mul_zero, add_zero]

lemma re_wHalf_add_mul_of_re_zero_pos {w : ℕ} (hw : 1 ≤ w) (c' : ℝ) {ω : ℂ} (hω : ω.re = 0) :
    0 < (((w : ℂ) / 2 + (c' : ℂ) * ω)).re := by
  rw [re_wHalf_add_mul_of_re_zero w c' hω]
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  linarith

/-! ### 6. Stirling threshold -/

/-- Threshold on `c' ‖ω‖` for which `‖S^{(w)}‖, ‖(S^{(w)})⁻¹‖ ≤ 2`
(`max (w, 2 (w²+2)) ≤ 2 (w²+2) + w`). -/
def stirThr (w : ℕ) : ℝ := 2 * ((w : ℝ) ^ 2 + 2) + w

lemma stirThr_pos (w : ℕ) : 0 < stirThr w := by
  unfold stirThr; positivity

lemma norm_stirlingSW_le_two_of_stirThr_le {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h : stirThr w ≤ c' * ‖ω‖) :
    ‖stirlingSW w c' ω‖ ≤ 2 ∧ ‖(stirlingSW w c' ω)⁻¹‖ ≤ 2 := by
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have h1 : 2 * ((w : ℝ) ^ 2 + 2) ≤ c' * ‖ω‖ := by unfold stirThr at h; linarith
  have h2 : (w : ℝ) ≤ c' * ‖ω‖ := by unfold stirThr at h; nlinarith [sq_nonneg (w : ℝ)]
  have := norm_stirlingSW_abs_bounds hw hc' hω_re h2 h1
  exact ⟨this.1, this.2.1⟩

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.cardyVC_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cardyVC_inner_bound

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.mellinDensityIntegrandW_strip_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinDensityIntegrandW_strip_eq

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.mellinDensityIntegrandW_crude_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinDensityIntegrandW_crude_eq

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_stirlingSW_le_two_of_stirThr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stirlingSW_le_two_of_stirThr_le

end FormalResearch.ModularBootstrap.FixedWeightBand
