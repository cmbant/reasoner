module

public import FormalResearch.ModularBootstrap.Chart.Upsilon
public import FormalResearch.ModularBootstrap.Blowup.TipMap
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Saddle Exponent `Φ_V`, Derivative Formula (Lemma S5), and Crude Exponent `E_c` (E2–E3)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2 & §J5:
* Lemma S5 (`vlo:S5`, lines 448–453, first claim):
  `Φ_V(ζ; b) := Υ(ζ) + J(ω(ζ); b) + L(b)` extended continuously at `ω = 0`, and
  `∂_ζ Φ_V = 2 log(b(ζ)/b) · ω'(ζ)`.
* Result E2–E3 (`vlo:E2`, lines 567–576):
  `E_c(ω; b) = B(ω) + Re J(ω; b) + Re L(b) = D(3μ/π, |b|) + 2 θ ν - (2π/3)(|b| - Re b)`
  (`ω = μ + i ν`, `θ = arg b`), strict convexity in `μ` with unique minimum at `μ_b = π |b| / 3`,
  affine in `ν` with slope `2 θ` on `μ = μ_b`, and left-edge identity
  `Re Φ_V(iτ; b) = E_c(ω(iτ); b)`.

Note: The second claim of Lemma S5 (evaluation at `ζ_+(b)` via Lemma T2) is out of scope for WP4a.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Chart

/-! ### Section 1: Saddle exponent `Φ_V`, continuity at `ω = 0`, and Lemma S5 (first claim) -/

/-- Saddle exponent `Φ_V(ζ; b) := Υ(ζ) + J(ω(ζ); b) + L(b)` (`lower_o1_two_edge.tex`, Lemma S5).
Because `Complex.log 0 = 0`, `stirlingJ 0 b = 0`, so this expression already realizes the
continuous extension at `ζ = 1/2` (`ω(1/2) = 0`). -/
noncomputable def chartPhiV (ζ b : ℂ) : ℂ :=
  chartUpsilon ζ + ComplexBessel.stirlingJ (chartOmega ζ) b + tipL b

private lemma tendsto_mul_log_zero :
    Tendsto (fun w : ℂ => w * Complex.log w) (𝓝 (0 : ℂ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let g : ℝ → ℝ := fun r => |r * Real.log r| + r * Real.pi
  have hg_cont : Continuous g := Real.continuous_mul_log.abs.add (continuous_id.mul continuous_const)
  have hg_tend : Tendsto (fun w : ℂ => g ‖w‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have h0 : g 0 = 0 := by simp [g]
    rw [← h0]
    exact hg_cont.tendsto 0 |>.comp (by simpa using continuous_norm.tendsto (0 : ℂ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg_tend
    (fun _ => norm_nonneg _) (fun w => ?_)
  rcases eq_or_ne w 0 with rfl | hw
  · simp [g]
  · have hlog_le : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
      rw [Complex.log_re, Complex.log_im] at h1
      linarith [Complex.abs_arg_le_pi w]
    have hnorm_pos : 0 ≤ ‖w‖ := norm_nonneg w
    calc ‖w * Complex.log w‖ = ‖w‖ * ‖Complex.log w‖ := norm_mul w _
      _ ≤ ‖w‖ * (|Real.log ‖w‖| + Real.pi) := mul_le_mul_of_nonneg_left hlog_le hnorm_pos
      _ = ‖w‖ * |Real.log ‖w‖| + ‖w‖ * Real.pi := by ring
      _ = |‖w‖ * Real.log ‖w‖| + ‖w‖ * Real.pi := by rw [abs_mul, abs_of_nonneg hnorm_pos]

private lemma tendsto_stirlingJ_zero (b : ℂ) :
    Tendsto (fun ω : ℂ => ComplexBessel.stirlingJ ω b) (𝓝 (0 : ℂ)) (𝓝 0) := by
  let c : ℂ := 3 / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero three_ne_zero
      (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos 1).ne'))
  have hsub : (fun ω : ℂ => ComplexBessel.stirlingJ ω b) =
      (fun ω : ℂ => c⁻¹ * ((c * ω) * Complex.log (c * ω)) - ω * (2 * Complex.log b)) := by
    ext ω
    unfold ComplexBessel.stirlingJ
    have hmul : 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) = c * ω := by
      dsimp [c]; ring
    rw [hmul]
    calc ω * (Complex.log (c * ω) - 2 * Complex.log b)
        = (c⁻¹ * c) * ω * Complex.log (c * ω) - ω * (2 * Complex.log b) := by
          rw [inv_mul_cancel₀ hc_ne, one_mul]; ring
      _ = c⁻¹ * ((c * ω) * Complex.log (c * ω)) - ω * (2 * Complex.log b) := by ring
  rw [hsub]
  have h1 : Tendsto (fun ω : ℂ => c * ω) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto (fun ω : ℂ => c * ω) (𝓝 0) (𝓝 (c * 0)))
  have hterm1 : Tendsto (fun ω : ℂ => c⁻¹ * ((c * ω) * Complex.log (c * ω))) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_mul_log_zero.comp h1)
  have hterm2 : Tendsto (fun ω : ℂ => ω * (2 * Complex.log b)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun ω : ℂ => ω) (𝓝 0) (𝓝 0)).mul tendsto_const_nhds
  simpa using hterm1.sub hterm2

lemma continuousWithinAt_chartPhiV_half (b : ℂ) :
    ContinuousWithinAt (fun ζ => chartPhiV ζ b) stripClosed (1 / 2 : ℂ) := by
  have hhalf_mem : (1 / 2 : ℂ) ∈ stripClosed := by
    simp only [stripClosed, Set.mem_ofPred_eq, Complex.div_ofNat_re, Complex.one_re]
    norm_num
  have hu : ContinuousWithinAt chartUpsilon stripClosed (1 / 2 : ℂ) :=
    continuousOn_chartUpsilon (1 / 2 : ℂ) hhalf_mem
  have hj : ContinuousWithinAt (fun ζ => ComplexBessel.stirlingJ (chartOmega ζ) b) stripClosed (1 / 2 : ℂ) := by
    have h_om : ContinuousWithinAt chartOmega stripClosed (1 / 2 : ℂ) :=
      continuousOn_chartOmega (1 / 2 : ℂ) hhalf_mem
    have h_tend : Tendsto chartOmega (𝓝[stripClosed] (1 / 2 : ℂ)) (𝓝 0) := by
      rw [← chartOmega_half]; exact h_om
    have hj0 : ContinuousWithinAt (fun ζ => ComplexBessel.stirlingJ (chartOmega ζ) b) stripClosed (1 / 2 : ℂ) := by
      change Tendsto (fun ζ => ComplexBessel.stirlingJ (chartOmega ζ) b) (𝓝[stripClosed] (1 / 2 : ℂ))
        (𝓝 (ComplexBessel.stirlingJ (chartOmega (1 / 2 : ℂ)) b))
      rw [chartOmega_half]
      have h0 : ComplexBessel.stirlingJ 0 b = 0 := by unfold ComplexBessel.stirlingJ; simp
      rw [h0]
      exact (tendsto_stirlingJ_zero b).comp h_tend
    exact hj0
  unfold chartPhiV
  exact (hu.add hj).add continuousWithinAt_const

private lemma hasDerivWithinAt_chartUpsilon_leftHalf {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) :
    HasDerivWithinAt chartUpsilon (chartIntegrand ζ) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} ζ := by
  have hζ : ζ ∈ stripClosed := ⟨h0, by linarith⟩
  obtain ⟨r, hr_pos, hf_ball⟩ := (analyticAt_chartIntegrand hζ.1 hζ.2).exists_ball_analyticOnNhd
  have hdiff_ball : DifferentiableOn ℂ chartIntegrand (ball ζ r) := hf_ball.differentiableOn
  have hcons_ball : Complex.IsConservativeOn chartIntegrand (ball ζ r) := hdiff_ball.isConservativeOn
  have hd_wedge := hcons_ball.hasDerivAt_wedgeIntegral hdiff_ball.continuousOn (mem_ball_self hr_pos)
  have hd_add : HasDerivAt (fun w => chartUpsilon ζ + Complex.wedgeIntegral ζ w chartIntegrand)
      (chartIntegrand ζ) ζ := hd_wedge.const_add _
  have hsub : {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} ⊆ stripClosed := fun w hw => ⟨hw.1, by linarith [hw.2]⟩
  have hev : ∀ᶠ w in 𝓝[{w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2}] ζ,
      chartUpsilon w = chartUpsilon ζ + Complex.wedgeIntegral ζ w chartIntegrand := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds ζ hr_pos] with w hw hw_left
    have hadd := wedgeIntegral_chartIntegrand_add hζ (hsub hw_left)
    unfold chartUpsilon
    linear_combination hadd
  exact hd_add.hasDerivWithinAt.congr_of_eventuallyEq hev (by unfold chartUpsilon; simp [Complex.wedgeIntegral])

private lemma b_mul_q_mem_slitPlane {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    chartB ζ * chartQ ζ ∈ Complex.slitPlane := by
  have hb := re_chartB_pos h0 h1 hne
  have hq := (re_chartQ_Ioo h0 h1 hne).1
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hb_ne : chartB ζ ≠ 0 := by intro h0'; rw [h0', Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have hreal : chartB ζ * chartQ ζ = (((chartB ζ * chartQ ζ).re : ℝ) : ℂ) := Complex.ext rfl h.2
  have hq_eq : chartQ ζ = (((chartB ζ * chartQ ζ).re : ℝ) : ℂ) * (chartB ζ)⁻¹ := by
    rw [← hreal]; field_simp [hb_ne]
  have hinv_re : 0 < ((chartB ζ)⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hb (Complex.normSq_pos.mpr hb_ne)
  have hq_le : (chartQ ζ).re ≤ 0 := by
    rw [hq_eq, Complex.re_ofReal_mul]
    exact mul_nonpos_of_nonpos_of_nonneg h.1 hinv_re.le
  linarith

private lemma log_b_mul_q {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2) (hne : ζ ≠ 1 / 2) :
    Complex.log (chartB ζ * chartQ ζ) = Complex.log (chartB ζ) + Complex.log (chartQ ζ) := by
  have hb := re_chartB_pos h0 h1 hne
  have hq := (re_chartQ_Ioo h0 h1 hne).1
  have hb_ne : chartB ζ ≠ 0 := by intro h0'; rw [h0', Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have hq_ne : chartQ ζ ≠ 0 := by intro h0'; rw [h0', Complex.zero_re] at hq; exact lt_irrefl 0 hq
  have hb_arg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hq_arg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hq)
  have harg : (chartB ζ).arg + (chartQ ζ).arg ∈ Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [(abs_lt.mp hb_arg).1, (abs_lt.mp hq_arg).1],
      by linarith [(abs_lt.mp hb_arg).2, (abs_lt.mp hq_arg).2]⟩
  exact Complex.log_mul hb_ne hq_ne harg

private lemma hasDerivAt_stirlingJ_chartOmega {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2)
    (hne : ζ ≠ 1 / 2) (b : ℂ) :
    HasDerivAt (fun ω : ℂ => ComplexBessel.stirlingJ ω b)
      (Complex.log (chartB ζ) + Complex.log (chartQ ζ) - 2 * Complex.log b) (chartOmega ζ) := by
  set ω := chartOmega ζ
  have hω_eq : ω = (2 * (Real.pi : ℂ) / 3) * chartB ζ * chartQ ζ := by
    dsimp [ω]; unfold chartOmega; simp only [h1, ↓reduceIte]; rfl
  let c : ℂ := 3 / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))
  have hcω_eq : c * ω = (((Real.exp 1)⁻¹ : ℝ) : ℂ) * (chartB ζ * chartQ ζ) := by
    dsimp [c]; rw [hω_eq]; push_cast; field_simp [Real.pi_pos.ne', (Real.exp_pos 1).ne']
  have hbq_slit := b_mul_q_mem_slitPlane h0 h1 hne
  have hcω_slit : c * ω ∈ Complex.slitPlane := by
    rw [hcω_eq, Complex.mem_slitPlane_iff]
    rcases Complex.mem_slitPlane_iff.mp hbq_slit with hre | him
    · left; rw [Complex.re_ofReal_mul]; exact mul_pos (inv_pos.mpr (Real.exp_pos 1)) hre
    · right; rw [Complex.im_ofReal_mul]; exact mul_ne_zero (inv_pos.mpr (Real.exp_pos 1)).ne' him
  have hc_lin : HasDerivAt (fun z : ℂ => 3 * z / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) c ω := by
    have hmul : (fun z : ℂ => 3 * z / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) = (fun z => c * z) := by
      ext z; dsimp [c]; ring
    rw [hmul]
    simpa using (hasDerivAt_id ω).const_mul c
  have h3ω_slit : 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) ∈ Complex.slitPlane := by
    rwa [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) = c * ω by dsimp [c]; ring]
  have hlog_d : HasDerivAt (fun z : ℂ => Complex.log (3 * z / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))))
      (ω⁻¹) ω := by
    refine ((Complex.hasDerivAt_log h3ω_slit).comp ω hc_lin).congr_deriv ?_
    have hc_ne : c ≠ 0 := by
      dsimp [c]; exact div_ne_zero three_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
          (Complex.ofReal_ne_zero.mpr (Real.exp_pos 1).ne'))
    have hω_ne : ω ≠ 0 := by
      intro h0'; rw [h0', mul_zero] at hcω_slit; exact Complex.zero_notMem_slitPlane hcω_slit
    rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) = c * ω by dsimp [c]; ring]
    field_simp [hc_ne, hω_ne]
  have hj_d : HasDerivAt (fun z : ℂ => ComplexBessel.stirlingJ z b)
      (1 * (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) - 2 * Complex.log b) +
        ω * (ω⁻¹ - 0)) ω := by
    unfold ComplexBessel.stirlingJ
    exact (hasDerivAt_id ω).mul (hlog_d.sub (hasDerivAt_const ω _))
  refine hj_d.congr_deriv ?_
  have hω_ne : ω ≠ 0 := by
    intro h0'; rw [h0', mul_zero] at hcω_slit; exact Complex.zero_notMem_slitPlane hcω_slit
  have hlog_val : Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) =
      Complex.log (chartB ζ) + Complex.log (chartQ ζ) - 1 := by
    rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) = c * ω by dsimp [c]; ring, hcω_eq]
    have hbq_ne : chartB ζ * chartQ ζ ≠ 0 := Complex.slitPlane_ne_zero hbq_slit
    have hexp_inv_pos : (0 : ℝ) < (Real.exp 1)⁻¹ := inv_pos.mpr (Real.exp_pos 1)
    have harg_inv : (((Real.exp 1)⁻¹ : ℝ) : ℂ).arg + (chartB ζ * chartQ ζ).arg ∈ Ioc (-Real.pi) Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hexp_inv_pos.le, zero_add]
      exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    rw [Complex.log_mul (Complex.ofReal_ne_zero.mpr hexp_inv_pos.ne') hbq_ne harg_inv,
      ← Complex.ofReal_log hexp_inv_pos.le, Real.log_inv, Real.log_exp, Complex.ofReal_neg,
      Complex.ofReal_one, log_b_mul_q h0 h1 hne]
    ring
  rw [hlog_val, sub_zero, mul_inv_cancel₀ hω_ne]
  ring

/-- **Lemma S5 (first claim, `vlo:S5`, `lower_o1_two_edge.tex`, lines 448–453)**:
derivative of `Φ_V(ζ; b) = Υ(ζ) + J(ω(ζ); b) + L(b)` on the left half-strip `{0 ≤ Re ζ ≤ 1/2} \ {1/2}`
(without `Re b > 0` branch assumption, stated as `2 (log b(ζ) - log b) ω'(ζ)`). -/
lemma hasDerivWithinAt_chartPhiV_sub {ζ b : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1 / 2)
    (hne : ζ ≠ 1 / 2) :
    HasDerivWithinAt (fun z => chartPhiV z b)
      (2 * (Complex.log (chartB ζ) - Complex.log b) * deriv chartOmega ζ)
      {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} ζ := by
  have hζ_strip : ζ ∈ stripClosed := ⟨h0, by linarith⟩
  have hu := hasDerivWithinAt_chartUpsilon_leftHalf h0 h1
  have hom : HasDerivAt chartOmega (deriv chartOmega ζ) ζ :=
    (analyticAt_chartOmega h0 (by linarith)).differentiableAt.hasDerivAt
  have hj := (hasDerivAt_stirlingJ_chartOmega h0 h1 hne b).comp ζ hom
  have hsum := hu.add hj.hasDerivWithinAt |>.add (hasDerivWithinAt_const ζ _ (tipL b))
  refine hsum.congr_deriv ?_
  unfold chartIntegrand
  rw [chartLogBQ_eq_sub h0 h1 hne, add_zero]
  ring

/-- **Lemma S5 (first claim, `vlo:S5`, `lower_o1_two_edge.tex`, lines 448–453)**:
for `Re b > 0`, `Φ_V(ζ; b)` is continuous at `ζ = 1/2` (`ω = 0`) and satisfies
`∂_ζ Φ_V = 2 log(b(ζ)/b) · ω'(ζ)` on `{0 ≤ Re ζ ≤ 1/2} \ {1/2}` (and as an unconstrained
complex derivative `HasDerivAt` on the open left half-strip `{0 < Re ζ < 1/2}`). -/
theorem lemma_S5_deriv {b : ℂ} (hb : 0 < b.re) :
    ContinuousWithinAt (fun ζ => chartPhiV ζ b) stripClosed (1 / 2 : ℂ) ∧
    (∀ ζ : ℂ, 0 < ζ.re → ζ.re < 1 / 2 →
      HasDerivAt (fun z => chartPhiV z b)
        (2 * Complex.log (chartB ζ / b) * deriv chartOmega ζ) ζ) ∧
    (∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 / 2 → ζ ≠ 1 / 2 →
      HasDerivWithinAt (fun z => chartPhiV z b)
        (2 * Complex.log (chartB ζ / b) * deriv chartOmega ζ)
        {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} ζ) := by
  refine ⟨continuousWithinAt_chartPhiV_half b, fun ζ h0 h1 => ?_, fun ζ h0 h1 hne => ?_⟩
  · have hne : ζ ≠ 1 / 2 := fun h => by rw [h] at h1; simp at h1
    have hu := hasDerivAt_chartUpsilon h0 (by linarith)
    have hom : HasDerivAt chartOmega (deriv chartOmega ζ) ζ :=
      (analyticAt_chartOmega h0.le (by linarith)).differentiableAt.hasDerivAt
    have hj := (hasDerivAt_stirlingJ_chartOmega h0.le h1.le hne b).comp ζ hom
    have hsum := hu.add hj |>.add (hasDerivAt_const ζ (tipL b))
    refine hsum.congr_deriv ?_
    unfold chartIntegrand
    rw [chartLogBQ_eq_sub h0.le h1.le hne, add_zero,
      log_div_of_re_pos (re_chartB_pos h0.le h1.le hne) hb]
    ring
  · have hd := hasDerivWithinAt_chartPhiV_sub h0 h1 hne (b := b)
    rw [log_div_of_re_pos (re_chartB_pos h0 h1 hne) hb]
    exact hd

/-! ### Section 2: Crude exponent `E_c` and results E2–E3 (`vlo:E2`) -/

/-- Crude Mellin integrand exponent `E_c(ω; b) := B(ω) + Re J(ω; b) + Re L(b)`
(`lower_o1_two_edge.tex`, §J5, Result E2–E3, line 570). -/
noncomputable def crudeExponentEc (ω b : ℂ) : ℝ :=
  ComplexBessel.crudeExponentB ω + (ComplexBessel.stirlingJ ω b).re + (tipL b).re

lemma crudeExponentEc_eq {ω b : ℂ} (hω_re : 0 < ω.re) (hb : b ≠ 0) :
    crudeExponentEc ω b =
      ComplexBessel.crudeDivergenceD (3 * ω.re / Real.pi) ‖b‖ +
        2 * b.arg * ω.im - (2 * Real.pi / 3) * (‖b‖ - b.re) := by
  unfold crudeExponentEc ComplexBessel.crudeExponentB ComplexBessel.stirlingJ tipL
    ComplexBessel.crudeDivergenceD
  have hnorm_b : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hω_norm : 0 < ‖ω‖ := lt_of_lt_of_le hω_re (Complex.re_le_norm ω)
  have hr_pos : 0 < 3 / (2 * Real.pi * Real.exp 1) := by positivity
  have harg_eq : (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).arg = ω.arg := by
    rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) =
        ((3 / (2 * Real.pi * Real.exp 1) : ℝ) : ℂ) * ω by push_cast; ring]
    exact Complex.arg_real_mul ω hr_pos
  have hnorm_eq : ‖3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))‖ =
      3 * ‖ω‖ / (2 * Real.pi * Real.exp 1) := by
    simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (Real.exp_pos 1).le]
  have hlog1_re : (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)))).re =
      Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) := by
    rw [Complex.log_re, hnorm_eq]
  have hlog1_im : (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)))).im = ω.arg := by
    rw [Complex.log_im, harg_eq]
  have hJ_re : (ω * (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) -
      2 * Complex.log b)).re =
      ω.re * (Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log ‖b‖) -
        ω.im * (ω.arg - 2 * b.arg) := by
    rw [Complex.mul_re, Complex.sub_re, Complex.sub_im, hlog1_re, hlog1_im,
      show (2 * Complex.log b).re = 2 * Real.log ‖b‖ by simp [Complex.log_re],
      show (2 * Complex.log b).im = 2 * b.arg by simp [Complex.log_im]]
  have hL_re : (((2 * Real.pi / 3 : ℝ) : ℂ) * b).re = (2 * Real.pi / 3) * b.re := by
    rw [Complex.re_ofReal_mul]
  have hlog_sum : Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) +
      Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log ‖b‖ =
      2 * Real.log ((3 * ω.re / Real.pi) / ‖b‖) - 1 := by
    have hprod : (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) * (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) =
        (3 * ω.re / Real.pi) ^ 2 / Real.exp 1 := by
      field_simp [Real.pi_pos.ne', hω_norm.ne', (Real.exp_pos 1).ne']
      ring
    rw [← Real.log_mul (by positivity) (by positivity), hprod,
      Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_pow, Real.log_div (by positivity) hnorm_b.ne']
    push_cast; ring
  have hlog_neg : Real.log (‖b‖ / (3 * ω.re / Real.pi)) =
      -Real.log ((3 * ω.re / Real.pi) / ‖b‖) := by
    rw [← Real.log_inv, inv_div]
  rw [hJ_re, hL_re, hlog_neg]
  calc ω.re * Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) - ω.re + ω.im * ω.arg +
        (ω.re * (Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log ‖b‖) -
          ω.im * (ω.arg - 2 * b.arg)) + (2 * Real.pi / 3) * b.re
      = ω.re * (Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) +
          Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log ‖b‖ - 1) +
          2 * b.arg * ω.im + (2 * Real.pi / 3) * b.re := by ring
    _ = ω.re * (2 * Real.log ((3 * ω.re / Real.pi) / ‖b‖) - 2) +
          2 * b.arg * ω.im + (2 * Real.pi / 3) * b.re := by rw [hlog_sum]; ring
    _ = (2 * Real.pi / 3) * (‖b‖ - 3 * ω.re / Real.pi -
          (3 * ω.re / Real.pi) * -Real.log ((3 * ω.re / Real.pi) / ‖b‖)) +
          2 * b.arg * ω.im - (2 * Real.pi / 3) * (‖b‖ - b.re) := by
        field_simp [Real.pi_pos.ne']; ring

lemma strictConvexOn_crudeExponentEc (b : ℂ) (hb : b ≠ 0) (ν : ℝ) :
    StrictConvexOn ℝ (Ioi (0 : ℝ)) (fun μ => crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b) := by
  have h_eq : ∀ μ : ℝ, 0 < μ →
      crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b =
        (2 * Real.pi / 3) * ((3 * μ / Real.pi) * Real.log (3 * μ / Real.pi)) -
          2 * (1 + Real.log ‖b‖) * μ +
          ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re)) := by
    intro μ hμ
    have hre : ((μ : ℂ) + (ν : ℂ) * Complex.I).re = μ := by simp
    have him : ((μ : ℂ) + (ν : ℂ) * Complex.I).im = ν := by simp
    rw [crudeExponentEc_eq (by rw [hre]; exact hμ) hb, hre, him]
    unfold ComplexBessel.crudeDivergenceD
    have hnorm_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hy_pos : 0 < 3 * μ / Real.pi := by positivity
    rw [Real.log_div hnorm_pos.ne' hy_pos.ne']
    field_simp [Real.pi_pos.ne']
    ring
  refine ⟨convex_Ioi 0, fun x hx y hy hxy a c ha hc hac => ?_⟩
  simp only [smul_eq_mul]
  have hmid : 0 < a * x + c * y := by nlinarith [mem_Ioi.mp hx, mem_Ioi.mp hy]
  rw [h_eq _ hmid, h_eq _ hx, h_eq _ hy]
  let g : ℝ → ℝ := fun t => t * Real.log t
  have hg_sc : StrictConvexOn ℝ (Ici 0) g := Real.strictConvexOn_mul_log
  have hyx : 3 * x / Real.pi ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (by have := mem_Ioi.mp hx; positivity)
  have hyy : 3 * y / Real.pi ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (by have := mem_Ioi.mp hy; positivity)
  have hyne : 3 * x / Real.pi ≠ 3 * y / Real.pi := by
    intro h; apply hxy; field_simp [Real.pi_pos.ne'] at h; exact h
  have hg_lt : g (a * (3 * x / Real.pi) + c * (3 * y / Real.pi)) <
      a * g (3 * x / Real.pi) + c * g (3 * y / Real.pi) :=
    hg_sc.2 hyx hyy hyne ha hc hac
  have hg_scaled : (2 * Real.pi / 3) * g (a * (3 * x / Real.pi) + c * (3 * y / Real.pi)) <
      a * ((2 * Real.pi / 3) * g (3 * x / Real.pi)) + c * ((2 * Real.pi / 3) * g (3 * y / Real.pi)) := by
    have hmul := mul_lt_mul_of_pos_left hg_lt (by positivity : 0 < 2 * Real.pi / 3)
    linarith
  have hlin : 3 * (a * x + c * y) / Real.pi = a * (3 * x / Real.pi) + c * (3 * y / Real.pi) := by
    ring
  change (2 * Real.pi / 3) * g (3 * (a * x + c * y) / Real.pi) - 2 * (1 + Real.log ‖b‖) * (a * x + c * y) +
      ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re)) <
    a * ((2 * Real.pi / 3) * g (3 * x / Real.pi) - 2 * (1 + Real.log ‖b‖) * x +
        ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re))) +
      c * ((2 * Real.pi / 3) * g (3 * y / Real.pi) - 2 * (1 + Real.log ‖b‖) * y +
        ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re)))
  rw [hlin]
  have h_aff : -2 * (1 + Real.log ‖b‖) * (a * x + c * y) +
      ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re)) =
      a * (-2 * (1 + Real.log ‖b‖) * x +
          ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re))) +
        c * (-2 * (1 + Real.log ‖b‖) * y +
          ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re))) := by
    calc -2 * (1 + Real.log ‖b‖) * (a * x + c * y) +
          ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re))
        = -2 * (1 + Real.log ‖b‖) * (a * x + c * y) +
          (a + c) * ((2 * Real.pi / 3) * ‖b‖ + 2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re)) := by
            rw [hac, one_mul]
      _ = _ := by ring
  linarith [hg_scaled]

lemma crudeExponentEc_min_at {b : ℂ} (hb : b ≠ 0) (ν μ : ℝ) (hμ : 0 < μ) :
    crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I) b ≤
      crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b ∧
    (μ ≠ Real.pi * ‖b‖ / 3 →
      crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I) b <
        crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b) := by
  have hnorm_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hμb_pos : 0 < Real.pi * ‖b‖ / 3 := by positivity
  have hre1 : ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I).re = Real.pi * ‖b‖ / 3 := by simp
  have him1 : ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I).im = ν := by simp
  have hre2 : ((μ : ℂ) + (ν : ℂ) * Complex.I).re = μ := by simp
  have him2 : ((μ : ℂ) + (ν : ℂ) * Complex.I).im = ν := by simp
  rw [crudeExponentEc_eq (by rw [hre1]; exact hμb_pos) hb,
    crudeExponentEc_eq (by rw [hre2]; exact hμ) hb, hre1, him1, hre2, him2]
  have hD0 : ComplexBessel.crudeDivergenceD (3 * (Real.pi * ‖b‖ / 3) / Real.pi) ‖b‖ = 0 := by
    rw [show 3 * (Real.pi * ‖b‖ / 3) / Real.pi = ‖b‖ by field_simp [Real.pi_pos.ne']]
    unfold ComplexBessel.crudeDivergenceD
    rw [div_self hnorm_pos.ne', Real.log_one]
    ring
  rw [hD0]
  have hD_nn : 0 ≤ ComplexBessel.crudeDivergenceD (3 * μ / Real.pi) ‖b‖ :=
    ComplexBessel.crudeDivergenceD_nonneg (by positivity) hnorm_pos
  refine ⟨by linarith, fun hne => ?_⟩
  have hy_ne : 3 * μ / Real.pi ≠ ‖b‖ := by
    intro h; apply hne; field_simp [Real.pi_pos.ne'] at h ⊢; linarith
  have hratio_ne : (3 * μ / Real.pi) / ‖b‖ ≠ 1 := by
    intro h; apply hy_ne; rw [div_eq_one_iff_eq hnorm_pos.ne'] at h; exact h
  have hy_pos : 0 < 3 * μ / Real.pi := by positivity
  have hstrict := Real.self_sub_one_lt_mul_log (div_pos hy_pos hnorm_pos).le hratio_ne
  have hlog_lt : Real.log (‖b‖ / (3 * μ / Real.pi)) = -Real.log ((3 * μ / Real.pi) / ‖b‖) := by
    rw [← Real.log_inv, inv_div]
  have hD_pos : 0 < ComplexBessel.crudeDivergenceD (3 * μ / Real.pi) ‖b‖ := by
    unfold ComplexBessel.crudeDivergenceD
    rw [hlog_lt]
    have hmul := mul_lt_mul_of_pos_left hstrict hnorm_pos
    have hmul_eq : ‖b‖ * ((3 * μ / Real.pi) / ‖b‖ - 1) = 3 * μ / Real.pi - ‖b‖ := by
      field_simp [hnorm_pos.ne']
    have hmul_rhs : ‖b‖ * ((3 * μ / Real.pi) / ‖b‖ * Real.log ((3 * μ / Real.pi) / ‖b‖)) =
        (3 * μ / Real.pi) * Real.log ((3 * μ / Real.pi) / ‖b‖) := by
      field_simp [hnorm_pos.ne']
    rw [hmul_eq, hmul_rhs] at hmul
    have hpos_inner : 0 < ‖b‖ - 3 * μ / Real.pi - (3 * μ / Real.pi) * -Real.log ((3 * μ / Real.pi) / ‖b‖) := by
      linarith
    positivity
  linarith

lemma crudeExponentEc_on_min_line {b : ℂ} (hb : b ≠ 0) (ν : ℝ) :
    crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I) b =
      2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re) := by
  have hnorm_pos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hre : ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I).re = Real.pi * ‖b‖ / 3 := by simp
  have him : ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I).im = ν := by simp
  rw [crudeExponentEc_eq (by rw [hre]; positivity) hb, hre, him,
    show 3 * (Real.pi * ‖b‖ / 3) / Real.pi = ‖b‖ by field_simp [Real.pi_pos.ne']]
  unfold ComplexBessel.crudeDivergenceD
  rw [div_self hnorm_pos.ne', Real.log_one]
  ring

lemma re_chartPhiV_edge_eq_Ec (τ : ℝ) (b : ℂ) :
    (chartPhiV (Complex.I * (τ : ℂ)) b).re =
      crudeExponentEc (chartOmega (Complex.I * (τ : ℂ))) b := by
  unfold chartPhiV crudeExponentEc
  rw [Complex.add_re, Complex.add_re, re_chartUpsilon_left_edge τ]

/-- **Results E2–E3 (`vlo:E2`, `lower_o1_two_edge.tex`, lines 567–576)**:
algebraic decomposition `E_c(ω; b) = D(3μ/π, |b|) + 2 θ ν - (2π/3)(|b| - Re b)`, strict convexity
in `μ > 0` with unique minimum at `μ_b = π |b| / 3`, affine dependence on `ν` with slope `2 θ` on
`μ = μ_b`, and left-edge contact `Re Φ_V(iτ; b) = E_c(ω(iτ); b)`. -/
theorem lemma_E2_E3 :
    (∀ {ω b : ℂ}, 0 < ω.re → b ≠ 0 →
      crudeExponentEc ω b =
        ComplexBessel.crudeDivergenceD (3 * ω.re / Real.pi) ‖b‖ +
          2 * b.arg * ω.im - (2 * Real.pi / 3) * (‖b‖ - b.re)) ∧
    (∀ {b : ℂ}, b ≠ 0 → ∀ ν : ℝ,
      StrictConvexOn ℝ (Ioi (0 : ℝ))
        (fun μ => crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b)) ∧
    (∀ {b : ℂ}, b ≠ 0 → ∀ ν μ : ℝ, 0 < μ →
      crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I) b ≤
        crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b ∧
      (μ ≠ Real.pi * ‖b‖ / 3 →
        crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I) b <
          crudeExponentEc ((μ : ℂ) + (ν : ℂ) * Complex.I) b)) ∧
    (∀ {b : ℂ}, b ≠ 0 → ∀ ν : ℝ,
      crudeExponentEc ((Real.pi * ‖b‖ / 3 : ℂ) + (ν : ℂ) * Complex.I) b =
        2 * b.arg * ν - (2 * Real.pi / 3) * (‖b‖ - b.re)) ∧
    (∀ τ : ℝ, ∀ b : ℂ,
      (chartPhiV (Complex.I * (τ : ℂ)) b).re =
        crudeExponentEc (chartOmega (Complex.I * (τ : ℂ))) b) :=
  ⟨fun hω hb => crudeExponentEc_eq hω hb,
   fun {_b} hb ν => strictConvexOn_crudeExponentEc _ hb ν,
   fun {_b} hb ν μ hμ => crudeExponentEc_min_at hb ν μ hμ,
   fun {_b} hb ν => crudeExponentEc_on_min_line hb ν,
   re_chartPhiV_edge_eq_Ec⟩

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_S5_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_S5_deriv

/-- info: 'FormalResearch.ModularBootstrap.Chart.lemma_E2_E3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_E2_E3

end FormalResearch.ModularBootstrap.Chart
