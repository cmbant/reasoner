module

public import FormalResearch.ModularBootstrap.FixedWeightBand.MellinGrowthW
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Convergence and Holomorphy of the Mellin Transform at Weight `w` (`vlo:S1`, first part)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S1 (`vlo:S1`), first part:
"`Mg(z)` converges absolutely and locally uniformly on `Re z > 0`; since `1/Γ` is entire, `m_g` is
holomorphic on `Re z > 0`".

The convergence argument uses only three facts about a test function `g` and the kernel `V`:
`g` is continuous on `[0, ∞)` (so bounded on `[0, 1]`), `|g| V` is integrable on `(0, ∞)`, and `V`
dominates every power on `[1, ∞)` (`PolyDom`, proved for `prob.cardyV a` in `MellinGrowthW`).  The
statements are therefore made for an abstract `V` (`mellinTransformW_*`), with the specialisations
to `g ∈ TestClass prob a` (`TestClass.integrableOn_mellin`, `TestClass.differentiableOn_mellinMG`).

* `mellinTransformW g z = ∫₀^∞ g(t) t^{z-1} dt` and `mellinMGW g z = (2π)^z Mg(z)/Γ(z)` (weight free,
  equal to `ComplexBessel.mellinTransformG`/`mellinMG`, see `MellinWBridge`);
* `integrableOn_mellinW`: absolute convergence on `Re z > 0` (head `|g| ≤ B`, tail `t^r ≤ C V`);
* `hasDerivAt_mellinTransformW`, `differentiableOn_mellinTransformW`, `analyticOnNhd_mellinTransformW`,
  `differentiableOn_mellinMGW`, `analyticOnNhd_mellinMGW`: holomorphy on `{Re z > 0}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing

/-! ### Definitions -/

/-- Mellin transform `Mg(z) = ∫₀^∞ g(t) t^{z - 1} dt` (`lower_o1_two_edge.tex`, §J2). -/
noncomputable def mellinTransformW (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1)

/-- Symmetric Mellin density `m_g(z) = (2π)^z Mg(z) / Γ(z)` (`lower_o1_two_edge.tex`, §J2). -/
noncomputable def mellinMGW (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ z * mellinTransformW g z / Complex.Gamma z

/-! ### Section 1: Absolute convergence on `Re z > 0` -/

section Abstract

variable {g V : ℝ → ℝ}

lemma mellin_integrand_aestronglyMeasurable (hcont : ContinuousOn g (Ici 0)) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1))
      (volume.restrict (Ioi 0)) := by
  have hcont_g : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (hcont.mono Ioi_subset_Ici_self)
  have hcont_pow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Ioi 0) := by
    intro t ht
    have hne : (t : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using mem_Ioi.mp ht))
    exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const hne).continuousWithinAt
  exact (hcont_g.mul hcont_pow).aestronglyMeasurable measurableSet_Ioi

lemma norm_mellin_integrand_eq {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖(g t : ℂ) * (t : ℂ) ^ (z - 1)‖ = |g t| * t ^ (z.re - 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re]

lemma integrableOn_rpow_sub_one_Ioc {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1)) (Ioc 0 1) := by
  rw [← integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r - 1))

/-- `g` continuous on `[0, ∞)` is bounded on `(0, 1]`. -/
lemma exists_bound_Ioc (hcont : ContinuousOn g (Ici 0)) :
    ∃ B : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, |g t| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.mono (fun t ht => ht.1 : Icc (0 : ℝ) 1 ⊆ Ici 0))
  exact ⟨B, fun t ht => by simpa using hB t ⟨ht.1.le, ht.2⟩⟩

/-- Domination on `Ioc 0 1` for `r₁ ≤ z.re`. -/
lemma integrableOn_mellin_head (hcont : ContinuousOn g (Ici 0)) {r₁ : ℝ} (hr₁ : 0 < r₁)
    {z : ℂ} (hz : r₁ ≤ z.re) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc 0 1) := by
  obtain ⟨B, hB⟩ := exists_bound_Ioc hcont
  have hdom : IntegrableOn (fun t : ℝ => B * t ^ (r₁ - 1)) (Ioc 0 1) :=
    (integrableOn_rpow_sub_one_Ioc hr₁).const_mul _
  refine hdom.mono' ((mellin_integrand_aestronglyMeasurable hcont z).mono_set Ioc_subset_Ioi_self) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  rw [norm_mellin_integrand_eq ht0 z]
  have hpow_le : t ^ (z.re - 1) ≤ t ^ (r₁ - 1) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
  exact mul_le_mul (hB t ht) hpow_le (Real.rpow_nonneg ht0.le _)
    ((abs_nonneg _).trans (hB t ht))

/-- Domination on `Ioi 1` by `C |g| V` for `z.re ≤ r₂`. -/
lemma integrableOn_mellin_tail (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) {r₂ : ℝ} {z : ℂ}
    (hz : z.re ≤ r₂) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 1) := by
  obtain ⟨C, hC⟩ := hdom r₂
  have hbd : IntegrableOn (fun t : ℝ => C * (|g t| * V t)) (Ioi 1) :=
    (hint.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
  refine hbd.mono' ((mellin_integrand_aestronglyMeasurable hcont z).mono_set
    (Ioi_subset_Ioi zero_le_one)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
  have ht0 : 0 < t := by linarith
  rw [norm_mellin_integrand_eq ht0 z]
  have hpow : t ^ (z.re - 1) ≤ C * V t :=
    (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)).trans (hC t ht1)
  calc |g t| * t ^ (z.re - 1) ≤ |g t| * (C * V t) := by gcongr
    _ = C * (|g t| * V t) := by ring

/-- **Convergence of `Mg(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem integrableOn_mellinW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) {z : ℂ}
    (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact (integrableOn_mellin_head hcont hz le_rfl).union
    (integrableOn_mellin_tail hcont hint hdom le_rfl)

/-- Norm integrability of `g(t) t^{r-1}` on `(0, ∞)` for real `r > 0`. -/
theorem integrableOn_abs_mellinW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => |g t| * t ^ (r - 1)) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => ‖(g t : ℂ) * (t : ℂ) ^ ((r : ℂ) - 1)‖) (Ioi 0) :=
    (integrableOn_mellinW hcont hint hdom (z := (r : ℂ)) (by simpa using hr)).norm
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact norm_mellin_integrand_eq (mem_Ioi.mp ht) (r : ℂ)

/-! ### Section 2: Holomorphy on `Re z > 0` -/

lemma neg_log_mul_rpow_le_inv {t ε : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
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

lemma log_le_self_of_one_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ t := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
  linarith

/-- Derivative formula for `mellinTransformW g` on `0 < z.re`. -/
theorem hasDerivAt_mellinTransformW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) :
    HasDerivAt (mellinTransformW g)
      (∫ t in Ioi (0 : ℝ), (g t : ℂ) * ((t : ℂ) ^ (z₀ - 1) * Complex.log (t : ℂ))) z₀ := by
  let δ : ℝ := z₀.re / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let F : ℂ → ℝ → ℂ := fun z t => (g t : ℂ) * (t : ℂ) ^ (z - 1)
  let F' : ℂ → ℝ → ℂ := fun z t => (g t : ℂ) * ((t : ℂ) ^ (z - 1) * Complex.log (t : ℂ))
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) :=
    mellin_integrand_aestronglyMeasurable hcont
  have hF_int : Integrable (F z₀) (volume.restrict (Ioi 0)) :=
    integrableOn_mellinW hcont hint hdom hz₀
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ioi 0)) := by
    have hcont_g : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn (hcont.mono Ioi_subset_Ici_self)
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
  obtain ⟨C, hC⟩ := hdom (z₀.re + δ)
  obtain ⟨B, hB⟩ := exists_bound_Ioc hcont
  let C_head : ℝ := B * δ⁻¹
  let bound : ℝ → ℝ := fun t =>
    if t ≤ 1 then C_head * t ^ (δ - 1) else C * (|g t| * V t)
  have hbound_int : IntegrableOn bound (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    refine IntegrableOn.union ?_ ?_
    · have hhead : IntegrableOn (fun t : ℝ => C_head * t ^ (δ - 1)) (Ioc 0 1) :=
        (integrableOn_rpow_sub_one_Ioc hδ).const_mul _
      exact hhead.congr_fun (fun t ht => by simp [bound, ht.2]) measurableSet_Ioc
    · have htail : IntegrableOn (fun t : ℝ => C * (|g t| * V t)) (Ioi 1) :=
        (hint.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
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
      have hg_bd : |g t| ≤ B := hB t ⟨ht0, ht1⟩
      have hB_nn : 0 ≤ B := (abs_nonneg _).trans hg_bd
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
          ≤ B * t ^ (2 * δ - 1) * (-Real.log t) := by
            gcongr
        _ = B * ((-Real.log t) * t ^ δ) * t ^ (δ - 1) := by
            rw [hsplit_pow]; ring
        _ ≤ B * δ⁻¹ * t ^ (δ - 1) := by
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
      have hpow_le : t ^ z.re ≤ C * V t :=
        (Real.rpow_le_rpow_of_exponent_le ht1'.le hz_hi).trans (hC t ht1'.le)
      calc |g t| * t ^ (z.re - 1) * |Real.log t|
          = |g t| * t ^ (z.re - 1) * Real.log t := by rw [hlog_abs]
        _ ≤ |g t| * t ^ (z.re - 1) * t := by gcongr
        _ = |g t| * t ^ z.re := by rw [mul_assoc, hmul_pow]
        _ ≤ |g t| * (C * V t) := by gcongr
        _ = C * (|g t| * V t) := by ring
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
theorem differentiableOn_mellinTransformW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) :
    DifferentiableOn ℂ (mellinTransformW g) {z : ℂ | 0 < z.re} :=
  fun _ hz => (hasDerivAt_mellinTransformW hcont hint hdom hz).differentiableAt.differentiableWithinAt

/-- **Analyticity of `Mg(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem analyticOnNhd_mellinTransformW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) :
    AnalyticOnNhd ℂ (mellinTransformW g) {z : ℂ | 0 < z.re} :=
  (differentiableOn_mellinTransformW hcont hint hdom).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- **Holomorphy of `m_g(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem differentiableOn_mellinMGW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) :
    DifferentiableOn ℂ (mellinMGW g) {z : ℂ | 0 < z.re} := by
  have hpow : Differentiable ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ z) := by
    have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
    exact fun z => (hasDerivAt_id z).const_cpow (Or.inl h2pi_ne) |>.differentiableAt
  have hinvG : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  have heq : mellinMGW g = fun z =>
      ((2 * (Real.pi : ℂ)) ^ z * mellinTransformW g z) * (Complex.Gamma z)⁻¹ := by
    ext z; simp [mellinMGW, div_eq_mul_inv]
  rw [heq]
  exact ((hpow.differentiableOn).mul (differentiableOn_mellinTransformW hcont hint hdom)).mul
    hinvG.differentiableOn

/-- **Analyticity of `m_g(z)` on `Re z > 0`** (`vlo:S1`). -/
theorem analyticOnNhd_mellinMGW (hcont : ContinuousOn g (Ici 0))
    (hint : IntegrableOn (fun t => |g t| * V t) (Ioi 0)) (hdom : PolyDom V) :
    AnalyticOnNhd ℂ (mellinMGW g) {z : ℂ | 0 < z.re} :=
  (differentiableOn_mellinMGW hcont hint hdom).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

end Abstract

/-! ### Section 3: Specialisation to `TestClass prob a` -/

/-- **`vlo:S1`, convergence** for `g ∈ TestClass prob a` (`S ≤ a`, `0 < a`):
`g(t) t^{z-1}` is integrable on `(0, ∞)` for `0 < Re z`. -/
theorem TestClass.integrableOn_mellin {prob : FixedWeightProblem} {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) {g : ℝ → ℝ} (hg : TestClass prob a g)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (g t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) :=
  integrableOn_mellinW hg.cont hg.int_cardy (polyDom_cardyV prob ha ha0) hz

/-- **`vlo:S1`, holomorphy of `Mg`** for `g ∈ TestClass prob a` on `Re z > 0`. -/
theorem TestClass.differentiableOn_mellinTransform {prob : FixedWeightProblem} {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) {g : ℝ → ℝ} (hg : TestClass prob a g) :
    DifferentiableOn ℂ (mellinTransformW g) {z : ℂ | 0 < z.re} :=
  differentiableOn_mellinTransformW hg.cont hg.int_cardy (polyDom_cardyV prob ha ha0)

/-- **`vlo:S1`, holomorphy of `m_g`** for `g ∈ TestClass prob a` on `Re z > 0`. -/
theorem TestClass.differentiableOn_mellinMG {prob : FixedWeightProblem} {a : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) {g : ℝ → ℝ} (hg : TestClass prob a g) :
    DifferentiableOn ℂ (mellinMGW g) {z : ℂ | 0 < z.re} :=
  differentiableOn_mellinMGW hg.cont hg.int_cardy (polyDom_cardyV prob ha ha0)

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.TestClass.integrableOn_mellin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.TestClass.integrableOn_mellin

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.TestClass.differentiableOn_mellinMG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.TestClass.differentiableOn_mellinMG

end FormalResearch.ModularBootstrap.FixedWeightBand
