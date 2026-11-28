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
open scoped Nat ENNReal

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

lemma sigmaFinite_hankelMeasure (w : ℕ) : SigmaFinite (hankelMeasure w) := by
  refine ⟨⟨{
    set := fun n => Iic (n : ℝ)
    set_mem := fun _ => trivial
    finite := fun n => ?_
    spanning := iUnion_eq_univ_iff.mpr fun x =>
      ⟨Nat.ceil (max x 0), le_trans (le_max_left _ _) (Nat.le_ceil _)⟩ }⟩⟩
  unfold hankelMeasure
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (w - 1))) := by fun_prop
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hs : MeasurableSet (Iic (n : ℝ) ∩ Ioi (0 : ℝ)) := measurableSet_Iic.inter measurableSet_Ioi
  have hle : ∫⁻ a in Iic (n : ℝ) ∩ Ioi 0, ENNReal.ofReal (a ^ (w - 1)) ≤
      ∫⁻ _a in Iic (n : ℝ) ∩ Ioi 0, ENNReal.ofReal ((n : ℝ) ^ (w - 1)) := by
    refine setLIntegral_mono' hs fun t ⟨htn, ht0⟩ => ?_
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht0.le htn _)
  refine hle.trans_lt ?_
  rw [setLIntegral_const]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  calc volume (Iic (n : ℝ) ∩ Ioi 0) ≤ volume (Iic (n : ℝ) ∩ Ici 0) :=
        measure_mono (inter_subset_inter_right _ Ioi_subset_Ici_self)
    _ = volume (Icc (0 : ℝ) n) := by congr 1; ext t; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    _ < ⊤ := by simp [Real.volume_Icc]

lemma hankelKernel_symm (w : ℕ) (t s : ℝ) : hankelKernel w t s = hankelKernel w s t := by
  unfold hankelKernel
  congr 3
  ring

lemma continuous_hankelKernel (w : ℕ) :
    Continuous (fun p : ℝ × ℝ => hankelKernel w p.1 p.2) := by
  unfold hankelKernel Sre
  refine continuous_const.mul (continuous_const.mul ?_)
  have hcont_S : Continuous (besselSC (w - 1)) :=
    continuous_iff_continuousAt.mpr fun z => (hasDerivAt_besselSC (w - 1) z).continuousAt
  exact Complex.continuous_re.comp
    (hcont_S.comp (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun p : ℝ × ℝ => -(4 * π ^ 2 * p.1 * p.2))))

lemma hankelKernel_eq_besselKernelR (w : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    hankelKernel w t s = 2 * π * (1 / Real.sqrt t) ^ (w - 1) * besselKernelR (w - 1) t s := by
  rw [besselKernelR_eq (w - 1) ht hs]
  unfold hankelKernel
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

lemma hankelKernel_abs_le (w : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    |hankelKernel w t s| ≤ 2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) := by
  rw [hankelKernel_eq_besselJ w ht hs, abs_mul,
    abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg (by positivity) _))]
  have hb := (Complex.abs_re_le_norm _).trans (norm_besselJ_nat_le_one (w - 1) (4 * π * Real.sqrt (t * s)))
  calc 2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) *
        |(Complex.besselJ ((w - 1 : ℕ) : ℂ) ((4 * π * Real.sqrt (t * s) : ℝ) : ℂ)).re|
      ≤ 2 * π * (1 / Real.sqrt (t * s)) ^ (w - 1) * 1 := by gcongr
    _ = _ := mul_one _

lemma sre_eq_tsum_kernelKTerm {w : ℕ} (hw : 1 ≤ w) (t s : ℝ) :
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
      have hfac : (1 : ℝ) ≤ ((k + (w - 1))! : ℝ) := by
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
      (((-(4 * π ^ 2 * t * s)) ^ k / ((k ! : ℝ) * ((k + (w - 1))! : ℝ)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.ofReal_re]
  unfold kernelKTerm
  have hkw : k + (w - 1) = k + w - 1 := by omega
  rw [hkw]
  congr 1
  ring

lemma pow_mul_hankelKernel_eq_kernelK {w : ℕ} (hw : 1 ≤ w) (t s : ℝ) :
    t ^ (w - 1) * hankelKernel w t s = 2 * π * kernelK w (-s) t := by
  unfold hankelKernel kernelK
  rw [sre_eq_tsum_kernelKTerm hw t s, mul_pow]
  ring

/-- **Weber's exponential integral (`int:repair`)** for `1 ≤ w : ℕ`, `β > 0`, `s ∈ ℝ`. -/
theorem weber_laplace {w : ℕ} (hw : 1 ≤ w) (s : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => Real.exp (-2 * π * β * t) * (t ^ (w - 1) * hankelKernel w t s)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-2 * π * β * t) * (t ^ (w - 1) * hankelKernel w t s) =
        β ^ (-(w : ℝ)) * Real.exp (-2 * π * s / β) := by
  have hk := kernelK_laplace hw (-s) hβ
  have heq : ∀ t : ℝ, Real.exp (-2 * π * β * t) * (t ^ (w - 1) * hankelKernel w t s) =
      2 * π * (kernelK w (-s) t * Real.exp (-2 * π * β * t)) := fun t => by
    rw [pow_mul_hankelKernel_eq_kernelK hw]; ring
  have hint : IntegrableOn (fun t => 2 * π * (kernelK w (-s) t * Real.exp (-2 * π * β * t))) (Ioi 0) :=
    hk.1.const_mul (2 * π)
  refine ⟨hint.congr_fun (fun t _ => (heq t).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => heq t, integral_const_mul, hk.2]
  congr 2
  ring

/-- Helper: `∫ f ∂(hankelMeasure w)` expressed as a set integral over `Ioi 0`. -/
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
    rw [Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv,
      Real.rpow_natCast, inv_mul_cancel₀ (pow_pos hβ w).ne']
  have hexp : Real.exp (-2 * π * t / β⁻¹) = Real.exp (-2 * π * β * t) := by
    congr 1; rw [div_inv_eq_mul]; ring
  rw [← mul_assoc, hbw, one_mul, hexp]
  unfold thermalDiff
  simp only [neg_sub]

/-- Integrability of `t ^ ((w - 1 : ℕ) / 2 : ℝ) * |thermalDiff w β t|` on `(0, ∞)`. -/
lemma integrableOn_rpow_mul_abs_thermalDiff {w : ℕ} {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ => t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t|) (Ioi 0) := by
  have h1 : ∀ {r : ℝ}, 0 < r →
      IntegrableOn (fun t : ℝ => t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)) (Ioi 0) := by
    intro r hr
    have hpow_dom : IntegrableOn (fun t : ℝ =>
        (1 + ((w - 1)! : ℝ) / (r / 2) ^ (w - 1)) * Real.exp (-(r / 2) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul _
    refine hpow_dom.mono' ((by fun_prop : Continuous fun t : ℝ =>
        t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
    have hpow_le_exp : t ^ (w - 1) ≤ (((w - 1)! : ℝ) / (r / 2) ^ (w - 1)) * Real.exp ((r / 2) * t) := by
      have hx : ((r / 2 * t) ^ (w - 1)) / ((w - 1)! : ℝ) ≤ Real.exp (r / 2 * t) :=
        Real.pow_div_factorial_le_exp (r / 2 * t) (by positivity) (w - 1)
      have hfac : (0 : ℝ) < ((w - 1)! : ℝ) := by positivity
      have hr2 : (0 : ℝ) < (r / 2) ^ (w - 1) := by positivity
      calc t ^ (w - 1)
          = ((r / 2) ^ (w - 1))⁻¹ * (r / 2 * t) ^ (w - 1) := by
              rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ hr2.ne', one_mul]
        _ ≤ ((r / 2) ^ (w - 1))⁻¹ * (((w - 1)! : ℝ) * Real.exp (r / 2 * t)) := by
              gcongr
              simpa [mul_comm] using (div_le_iff₀ hfac).mp hx
        _ = (((w - 1)! : ℝ) / (r / 2) ^ (w - 1)) * Real.exp ((r / 2) * t) := by ring
    have hle : t ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ 1 + t ^ (w - 1) := by
      rcases le_or_gt t 1 with ht1 | ht1
      · have h1' : t ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ 1 :=
          Real.rpow_le_one ht0.le ht1 (by positivity)
        linarith [pow_nonneg ht0.le (w - 1)]
      · have hexp : (((w - 1 : ℕ) : ℝ) / 2) ≤ ((w - 1 : ℕ) : ℝ) := by
          have : (0 : ℝ) ≤ ((w - 1 : ℕ) : ℝ) := by positivity
          linarith
        have h1' : t ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ t ^ ((w - 1 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ht1.le hexp
        rw [Real.rpow_natCast] at h1'
        linarith
    have h1exp : (1 : ℝ) ≤ Real.exp ((r / 2) * t) := Real.one_le_exp (by positivity)
    calc t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)
        ≤ (1 + t ^ (w - 1)) * Real.exp (-r * t) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ (Real.exp ((r / 2) * t) + (((w - 1)! : ℝ) / (r / 2) ^ (w - 1)) * Real.exp ((r / 2) * t)) *
            Real.exp (-r * t) := by gcongr
      _ = (1 + ((w - 1)! : ℝ) / (r / 2) ^ (w - 1)) * (Real.exp ((r / 2) * t) * Real.exp (-r * t)) := by ring
      _ = (1 + ((w - 1)! : ℝ) / (r / 2) ^ (w - 1)) * Real.exp (-(r / 2) * t) := by
            rw [← Real.exp_add]; congr 2; ring
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