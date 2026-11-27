module

public import FormalResearch.ModularBootstrap.Integrality.RepairTaylor
public import FormalResearch.ModularBootstrap.Integrality.RepairIdentity
public import FormalResearch.ModularBootstrap.Crossing.Setup

/-!
# Hankel Measure, Symmetric Kernel, and Weber's Exponential Integral (`int:repair` (1))

Proves Weber's identity for integer weights `1 ≤ w`:
`∫_0^∞ exp(-2π β t) · (2π t^{w-1} (2π)^{w-1} S_{w-1}(-4π² t s)) dt = β^{-w} exp(-2π s / β)`,
reusing `Crossing.kernelK_laplace hw (-s) hβ`. Consequently, the Hankel transform against
`hankelMeasure w` and symmetric kernel `hankelKernel w` satisfies `U Ξ_β = -Ξ_β` (`kerTransform_thermalDiff`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Nat

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Hankel
open FormalResearch.ModularBootstrap.WeightAxioms

/-- Weighted measure `dm_w(t) = t^{w-1} dt` supported on `Ioi (0 : ℝ)`. -/
noncomputable def hankelMeasure (w : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (t ^ (w - 1)))

/-- Symmetric smooth Bessel kernel `k_w(t, s) = 2π (2π)^{w-1} S_{w-1}(-4π² t s)` (`t, s ∈ ℝ`),
agreeing with `2π (t s)^{-(w-1)/2} J_{w-1}(4π √(ts))` for `t, s > 0`. -/
noncomputable def hankelKernel (w : ℕ) (t s : ℝ) : ℝ :=
  2 * π * ((2 * π) ^ (w - 1) * Sre (w - 1) (-(4 * π ^ 2 * t * s)))

lemma sigmaFinite_hankelMeasure (w : ℕ) : SigmaFinite (hankelMeasure w) :=
  inferInstance

lemma hankelKernel_symm (w : ℕ) (t s : ℝ) : hankelKernel w t s = hankelKernel w s t := by
  unfold hankelKernel
  congr 3
  ring

lemma continuous_hankelKernel (w : ℕ) :
    Continuous (fun p : ℝ × ℝ => hankelKernel w p.1 p.2) := by
  unfold hankelKernel Sre
  refine continuous_const.mul (continuous_const.mul ?_)
  have hcont_S : Continuous (besselSC (w - 1)) :=
    (differentiable_iff_continuous_differentiableAt.mp (fun z => (hasDerivAt_besselSC (w - 1) z).differentiableAt)
      |> fun _ => continuous_iff_continuousAt.mpr fun z => (hasDerivAt_besselSC (w - 1) z).continuousAt)
  exact Complex.continuous_re.comp
    (hcont_S.comp (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun p : ℝ × ℝ => -(4 * π ^ 2 * p.1 * p.2))))

lemma hankelKernel_eq_besselKernelR (w : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    hankelKernel w t s = 2 * π * (1 / Real.sqrt t) ^ (w - 1) * besselKernelR (w - 1) t s := by
  rw [besselKernelR_eq (w - 1) ht hs]
  unfold hankelKernel
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : (1 / Real.sqrt t) ^ (w - 1) * (2 * π * Real.sqrt t) ^ (w - 1) = (2 * π) ^ (w - 1) := by
    rw [← mul_pow]
    congr 1
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp [hst]
  calc 2 * π * ((2 * π) ^ (w - 1) * Sre (w - 1) (-(4 * π ^ 2 * t * s)))
      = 2 * π * ((1 / Real.sqrt t) ^ (w - 1) * (2 * π * Real.sqrt t) ^ (w - 1)) *
          Sre (w - 1) (-(4 * π ^ 2 * t * s)) := by rw [h1]; ring
    _ = 2 * π * (1 / Real.sqrt t) ^ (w - 1) *
          ((2 * π * Real.sqrt t) ^ (w - 1) * Sre (w - 1) (-(4 * π ^ 2 * t * s))) := by ring

lemma hankelKernel_eq_besselJ (w : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    hankelKernel w t s =
      2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) *
        (Complex.besselJ ((w - 1 : ℕ) : ℂ) ((4 * π * Real.sqrt (t * s) : ℝ) : ℂ)).re := by
  rw [hankelKernel_eq_besselKernelR w ht hs]
  unfold besselKernelR
  rw [← mul_assoc, mul_assoc (2 * π), ← mul_pow, one_div, one_div, ← mul_inv,
    ← Real.sqrt_mul ht.le s, one_div]
  ring

lemma hankelKernel_abs_le (w : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    |hankelKernel w t s| ≤ 2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) := by
  rw [hankelKernel_eq_besselJ w ht hs, abs_mul,
    abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))]
  have hb := (Complex.abs_re_le_norm _).trans (norm_besselJ_nat_le_one (w - 1) (4 * π * Real.sqrt (t * s)))
  calc 2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) *
        |(Complex.besselJ ((w - 1 : ℕ) : ℂ) ((4 * π * Real.sqrt (t * s) : ℝ) : ℂ)).re|
      ≤ 2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) * 1 := by gcongr
    _ = _ := mul_one _

lemma sre_eq_tsum_kernelKTerm (w : ℕ) (t s : ℝ) :
    Sre (w - 1) (-(4 * π ^ 2 * t * s)) = ∑' k : ℕ, kernelKTerm w (-s) t k := by
  have hts : besselSC (w - 1) ((-(4 * π ^ 2 * t * s) : ℝ) : ℂ) =
      ∑' k : ℕ, (((-(4 * π ^ 2 * t * s) : ℝ) : ℂ) ^ k) / ((k ! : ℂ) * ((k + (w - 1))! : ℂ)) :=
    besselSC_eq_tsum (w - 1) _
  have hre : (besselSC (w - 1) ((-(4 * π ^ 2 * t * s) : ℝ) : ℂ)).re =
      ∑' k : ℕ, (((((-(4 * π ^ 2 * t * s) : ℝ) : ℂ) ^ k) /
        ((k ! : ℂ) * ((k + (w - 1))! : ℂ))).re) := by
    have hsum : Summable (fun k : ℕ => (((-(4 * π ^ 2 * t * s) : ℝ) : ℂ) ^ k) /
        ((k ! : ℂ) * ((k + (w - 1))! : ℂ))) := by
      refine Summable.of_norm_bounded (g := fun k => |4 * π ^ 2 * t * s| ^ k / (k ! : ℝ))
        (Real.summable_pow_div_factorial _) fun k => ?_
      rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_neg]
      have hfac : (1 : ℝ) ≤ ((k + (w - 1))! : ℝ) :=
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
      have hk_pos : (0 : ℝ) < (k ! : ℝ) := by positivity
      calc |4 * π ^ 2 * t * s| ^ k / ((k ! : ℝ) * ((k + (w - 1))! : ℝ))
          ≤ |4 * π ^ 2 * t * s| ^ k / ((k ! : ℝ) * 1) := by gcongr
        _ = _ := by rw [mul_one]
    rw [hts]
    exact Complex.reCLM.map_tsum hsum
  change (besselSC (w - 1) ((-(4 * π ^ 2 * t * s) : ℝ) : ℂ)).re = _
  rw [hre]
  refine tsum_congr fun k => ?_
  have hcast : (((-(4 * π ^ 2 * t * s) : ℝ) : ℂ) ^ k / ((k ! : ℂ) * ((k + (w - 1))! : ℂ))) =
      (((-(4 * π ^ 2 * t * s) ^ k / ((k ! : ℝ) * ((k + (w - 1))! : ℝ)) : ℝ) : ℂ)) := by
    push_cast; rfl
  rw [hcast, Complex.ofReal_re]
  unfold kernelKTerm
  have hkw : k + (w - 1) = k + w - 1 := by omega
  rw [hkw]
  congr 1
  congr 1
  ring

lemma pow_mul_hankelKernel_eq_kernelK (w : ℕ) (t s : ℝ) :
    t ^ (w - 1) * hankelKernel w t s = 2 * π * kernelK w (-s) t := by
  unfold hankelKernel kernelK
  rw [sre_eq_tsum_kernelKTerm w t s, mul_pow]
  ring

/-- **Weber's exponential integral (`int:repair`)** for `1 ≤ w : ℕ`, `β > 0`, `s ∈ ℝ`. -/
theorem weber_laplace {w : ℕ} (hw : 1 ≤ w) (s : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => Real.exp (-2 * π * β * t) * (t ^ (w - 1) * hankelKernel w t s)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-2 * π * β * t) * (t ^ (w - 1) * hankelKernel w t s) =
        β ^ (-(w : ℝ)) * Real.exp (-2 * π * s / β) := by
  have hk := kernelK_laplace hw (-s) hβ
  have heq : ∀ t : ℝ, Real.exp (-2 * π * β * t) * (t ^ (w - 1) * hankelKernel w t s) =
      2 * π * (kernelK w (-s) t * Real.exp (-2 * π * β * t)) := fun t => by
    rw [pow_mul_hankelKernel_eq_kernelK]; ring
  refine ⟨(hk.1.const_mul (2 * π)).congr_fun (fun t _ => (heq t).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => heq t, integral_const_mul, hk.2]
  congr 2
  ring

/-- Helper: `t ^ (w - 1) * hankelKernel w t s` expressed in `integral_withDensity` form. -/
lemma integral_hankelMeasure_eq {w : ℕ} (f : ℝ → ℝ) :
    ∫ s, f s ∂(hankelMeasure w) = ∫ s in Ioi (0 : ℝ), s ^ (w - 1) * f s := by
  unfold hankelMeasure
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (w - 1))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, ENNReal.toReal_ofReal (pow_nonneg (mem_Ioi.mp ht).le _)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    exact ENNReal.ofReal_lt_top

lemma integrable_hankelMeasure_iff {w : ℕ} (f : ℝ → ℝ) :
    Integrable f (hankelMeasure w) ↔ IntegrableOn (fun s => s ^ (w - 1) * f s) (Ioi 0) := by
  unfold hankelMeasure
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (w - 1))) := by fun_prop
  rw [integrable_withDensity_iff_integrable_smul' hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [smul_eq_mul, ENNReal.toReal_ofReal (pow_nonneg (mem_Ioi.mp ht).le _)]

/-- **Pointwise crossing eigenfunction identity `U Ξ_β = -Ξ_β`** for `1 ≤ w : ℕ`, `β > 0`,
for every `t : ℝ`. -/
theorem kerTransform_thermalDiff {w : ℕ} (hw : 1 ≤ w) {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    kerTransform (hankelMeasure w) (hankelKernel w) (thermalDiff w β) t = -thermalDiff w β t := by
  unfold kerTransform
  rw [integral_hankelMeasure_eq]
  have hw1 := weber_laplace hw t hβ
  have hw2 := weber_laplace hw t (inv_pos.mpr hβ)
  have heq : ∀ s : ℝ, s ^ (w - 1) * (hankelKernel w t s * thermalDiff w β s) =
      Real.exp (-2 * π * β * s) * (s ^ (w - 1) * hankelKernel w s t) -
        β ^ (-(w : ℝ)) * (Real.exp (-2 * π * β⁻¹ * s) * (s ^ (w - 1) * hankelKernel w s t)) := by
    intro s
    unfold thermalDiff
    rw [hankelKernel_symm w t s, div_eq_mul_inv]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi fun s _ => heq s,
    integral_sub hw1.1 (hw2.1.const_mul _), integral_const_mul, hw1.2, hw2.2]
  have hbw : β ^ (-(w : ℝ)) * (β⁻¹) ^ (-(w : ℝ)) = 1 := by
    rw [Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv, ← Real.rpow_add hβ, neg_add_cancel,
      Real.rpow_zero]
  have hexp : Real.exp (-2 * π * t / β⁻¹) = Real.exp (-2 * π * β * t) := by
    congr 1; rw [div_inv_eq_mul]; ring
  rw [← mul_assoc, hbw, one_mul]
  unfold thermalDiff
  rw [show -2 * π * t / β = -2 * π * β⁻¹ * t by rw [div_eq_mul_inv]; ring]
  simp only [neg_sub]
  rw [div_eq_mul_inv]
  congr 1; ring

/-- Integrability of `t ^ ((w - 1 : ℕ) / 2 : ℝ) * |thermalDiff w β t|` on `(0, ∞)`. -/
lemma integrableOn_rpow_mul_abs_thermalDiff {w : ℕ} {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t|) (Ioi 0) := by
  have h1 : ∀ {r : ℝ}, 0 < r →
      IntegrableOn (fun t : ℝ => t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)) (Ioi 0) := by
    intro r hr
    have hpow : (((w - 1 : ℕ) : ℝ) / 2 + 1) - 1 = ((w - 1 : ℕ) : ℝ) / 2 := by ring
    have hint := Real.integrableOn_rpow_mul_exp_neg_mul_Ioi
      (s := ((w - 1 : ℕ) : ℝ) / 2 + 1) (by positivity) hr
    simpa [hpow] using hint
  have hdom : IntegrableOn (fun t : ℝ =>
      t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * π * β) * t) +
        β ^ (-(w : ℝ)) * (t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * π / β) * t))) (Ioi 0) :=
    (h1 (by positivity)).add ((h1 (by positivity)).const_mul _)
  refine hdom.mono' ((by unfold thermalDiff; fun_prop : Continuous fun t : ℝ =>
      t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t|).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0 _) (abs_nonneg _))]
  have htri : |thermalDiff w β t| ≤ Real.exp (-(2 * π * β) * t) +
      β ^ (-(w : ℝ)) * Real.exp (-(2 * π / β) * t) := by
    unfold thermalDiff
    calc |Real.exp (-2 * π * β * t) - β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β)|
        ≤ |Real.exp (-2 * π * β * t)| + |β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β)| := abs_sub _ _
      _ = Real.exp (-(2 * π * β) * t) + β ^ (-(w : ℝ)) * Real.exp (-(2 * π / β) * t) := by
          rw [abs_of_pos (Real.exp_pos _), abs_of_pos (mul_pos (Real.rpow_pos_of_pos hβ _) (Real.exp_pos _))]
          congr 2 <;> ring
  calc t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t|
      ≤ t ^ (((w - 1 : ℕ) : ℝ) / 2) * (Real.exp (-(2 * π * β) * t) +
          β ^ (-(w : ℝ)) * Real.exp (-(2 * π / β) * t)) :=
        mul_le_mul_of_nonneg_left htri (Real.rpow_nonneg ht0 _)
    _ = _ := by ring

/-- info: 'FormalResearch.ModularBootstrap.Integrality.weber_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weber_laplace

/-- info: 'FormalResearch.ModularBootstrap.Integrality.kerTransform_thermalDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kerTransform_thermalDiff

end FormalResearch.ModularBootstrap.Integrality