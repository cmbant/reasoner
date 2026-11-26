module

public import FormalResearch.SignUncertainty.FctPhiKillCore
public import FormalResearch.SignUncertainty.FctMomentCore
public import FormalResearch.SignUncertainty.UctStripIntegrals
public import FormalResearch.SignUncertainty.CtOuterEntire
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# `fct:phikill`: properties of `φ_kill` and exact `O(a^8)` finite-part cancellation (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.4 (`fct:phikill`),
parts (1), (2), and (3) (lines 298–393).

Main results proved here:
* `fp_cancel_of_laurent`: general finite-part cancellation lemma for any even Laurent expansion
  `F(t) = b_{-4}/t^4 + b_{-2}/t^2 + b_0 + b_2 t^2 + b_4 t^4 + b_6 t^6 + R(t)` with `R(t) = O(t^8)`
  on `(0, 1]` and `O(t^6)` on `[1, ∞)`, yielding `O(a^8)` for `0 < a ≤ 1`.
* `fct_phikill_fp_CE` and `fct_phikill_fp_star`: part (3) (`(fct:pk-fp)`) for both `H_0 ∈ {H_*, H_CE}`,
  with exact singular coefficients `c_{-1}(H_*) = (47/20) α_osc` and `c_{-1}(H_CE) = -(13/20) α_osc`.
* `fct_phikill`: bundled headline theorem combining parts (1), (2), and (3).

Class: proved, no hypotheses. Kernel-dependence guards at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctPhiKill

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.CohnElkies

/-! ### General `O(a^8)` finite-part cancellation lemma -/

lemma integrableOn_inv_pow_Ioi {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun t : ℝ => t ^ (-(m : ℤ))) (Ioi ε) ∧
      ∫ t in Ioi ε, t ^ (-(m : ℤ)) = ε ^ (1 - (m : ℤ)) / ((m : ℝ) - 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  let F : ℝ → ℝ := fun t => -(t ^ (1 - (m : ℤ)) / ((m : ℝ) - 1))
  have hd : ∀ t : ℝ, ε ≤ t → HasDerivAt F (t ^ (-(m : ℤ))) t := by
    intro t ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le hε ht).ne'
    have h1 := hasDerivAt_zpow (1 - (m : ℤ)) t (Or.inl ht0)
    have h2 := (h1.div_const ((m : ℝ) - 1)).neg
    refine h2.congr_deriv ?_
    have hexp : (1 - (m : ℤ)) - 1 = -(m : ℤ) := by omega
    rw [hexp]
    have hcast : ((1 - (m : ℤ) : ℤ) : ℝ) = -((m : ℝ) - 1) := by push_cast; ring
    rw [hcast]
    field_simp [hm1.ne']
  have hnn : ∀ t : ℝ, ε < t → 0 ≤ t ^ (-(m : ℤ)) := fun t ht =>
    (zpow_pos (hε.trans ht) _).le
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => t ^ (1 - (m : ℤ))) atTop (𝓝 0) := by
      have heq : (fun t : ℝ => t ^ (1 - (m : ℤ))) = fun t => (t ^ (m - 1))⁻¹ := by
        ext t; rw [show 1 - (m : ℤ) = -((m - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
      rw [heq]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : m - 1 ≠ 0))
    simpa [F] using (hpow.div_const ((m : ℝ) - 1)).neg
  have key := ftc_Ioi hd hnn hlim
  refine ⟨key.1, ?_⟩
  rw [key.2]; simp only [F, neg_neg]

lemma tendsto_setIntegral_Ioi_zero {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi ε, f t) (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Ioi (0 : ℝ), f t)) := by
  have hdom : Tendsto (fun ε : ℝ => ∫ t : ℝ, (Ioi ε).indicator f t) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, (Ioi (0 : ℝ)).indicator f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖(Ioi (0 : ℝ)).indicator f t‖) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hm := (integrable_indicator_iff measurableSet_Ioi).mpr hf
      exact (hm.aestronglyMeasurable.indicator (s := Ioi ε) measurableSet_Ioi).congr
        (Filter.Eventually.of_forall fun t => by
          by_cases h1 : t ∈ Ioi (0 : ℝ) <;> by_cases h2 : t ∈ Ioi ε
          · simp [h1, h2]
          · simp [h2]
          · exact absurd (lt_trans hε h2) h1
          · simp [h2])
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Filter.Eventually.of_forall fun t => ?_
      by_cases h2 : t ∈ Ioi ε
      · have h1 : t ∈ Ioi (0 : ℝ) := lt_trans hε h2
        simp [h1, h2]
      · simp [h2]
    · exact ((integrable_indicator_iff measurableSet_Ioi).mpr hf).norm
    · refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : 0 < t
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT ht] with ε hε
        have h1 : t ∈ Ioi (0 : ℝ) := ht
        have h2 : t ∈ Ioi ε := hε.2
        simp [h1, h2]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have h1 : t ∉ Ioi (0 : ℝ) := ht
        have h2 : t ∉ Ioi ε := fun h => ht (lt_trans hε h)
        simp [h1, h2]
  simpa only [integral_indicator measurableSet_Ioi] using hdom

lemma continuous_phiKill_imag_re {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re) := by
  have hcontC : Continuous (fun t : ℝ => phiKill a ((t : ℂ) * Complex.I)) := by
    refine (differentiableOn_phiPQ 8 8 a).continuousOn.comp_continuous
      (Complex.continuous_ofReal.mul continuous_const) fun t => ?_
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
      Complex.I_im, mul_one, sub_self, Complex.neg_re] at hre
    linarith
  exact Complex.continuous_re.comp hcontC

/-- General `O(a^8)` finite-part cancellation lemma (proof of `fct:phikill` (3), lines 355–374). -/
lemma fp_cancel_of_laurent {F : ℝ → ℝ} (hF_cont : ContinuousOn F (Ioi 0))
    {b_m4 b_m2 b0 b2 b4 b6 C_R : ℝ} (hCR : 0 ≤ C_R)
    (hR_small : ∀ t ∈ Ioc (0 : ℝ) 1,
      |F t - (b_m4 / t ^ 4 + b_m2 / t ^ 2 + b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 8)
    (hR_large : ∀ t : ℝ, 1 ≤ t →
      |F t - (b_m4 / t ^ 4 + b_m2 / t ^ 2 + b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 6) :
    ∃ C_fp ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      let R : ℝ → ℝ := fun t => F t - (b_m4 / t ^ 4 + b_m2 / t ^ 2 + b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)
      IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 0) ∧
      |∫ t in Ioi (0 : ℝ), R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| ≤ C_fp * a ^ 8 ∧
      Tendsto (fun ε : ℝ =>
        (∫ t in Ioi ε, F t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) - b_m4 / (3 * ε ^ 3) - b_m2 / ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in Ioi (0 : ℝ), R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))) := by
  obtain ⟨C_phi, hC_phi, hphi_bd⟩ := norm_one_sub_phiPQ_le_one_and_tail 8 8 (by norm_num)
  obtain ⟨C_phi0, hC_phi0, hphi0_bd⟩ := norm_phiPQ_le 8 8
  refine ⟨3 * C_phi * C_R, by positivity, fun {a} ha ha1 => ?_⟩
  set R : ℝ → ℝ := fun t => F t - (b_m4 / t ^ 4 + b_m2 / t ^ 2 + b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)
  have h1sub_cont : Continuous (fun t : ℝ => 1 - (phiKill a ((t : ℂ) * Complex.I)).re) :=
    continuous_const.sub (continuous_phiKill_imag_re ha)
  have hR_cont : ContinuousOn R (Ioi 0) := by
    refine hF_cont.sub ?_
    refine (((((continuousOn_const.div (continuousOn_id.pow 4) fun t ht => pow_ne_zero 4 (mem_Ioi.mp ht).ne').add
      (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (mem_Ioi.mp ht).ne')).add
      continuousOn_const).add (continuousOn_const.mul (continuousOn_id.pow 2))).add
      (continuousOn_const.mul (continuousOn_id.pow 4))).add
      (continuousOn_const.mul (continuousOn_id.pow 6))
  have h1sub_bd : ∀ t : ℝ, 0 < t →
      |1 - (phiKill a ((t : ℂ) * Complex.I)).re| ≤ C_phi ∧
      |1 - (phiKill a ((t : ℂ) * Complex.I)).re| ≤ C_phi * (a / t) ^ 8 := by
    intro t ht
    have hre0 : (0 : ℝ) ≤ ((t : ℂ) * Complex.I).re := by simp
    have hne : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') Complex.I_ne_zero
    have hnorm : ‖(t : ℂ) * Complex.I‖ = t := by
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    have hbd := hphi_bd ha hre0
    have hre_le : |1 - (phiKill a ((t : ℂ) * Complex.I)).re| ≤ ‖1 - phiKill a ((t : ℂ) * Complex.I)‖ := by
      have := Complex.abs_re_le_norm (1 - phiKill a ((t : ℂ) * Complex.I))
      simpa using this
    exact ⟨hre_le.trans hbd.1, by have := hre_le.trans (hbd.2 hne); rwa [hnorm] at this⟩
  -- 1. Integrability and `O(a^8)` bound for `R * (1 - Re φ_kill)` on `Ioi 0`
  have hR_int_and_bd : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 0) ∧
      |∫ t in Ioi (0 : ℝ), R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| ≤ 3 * C_phi * C_R * a ^ 8 := by
    -- Split `Ioi 0` into `Ioc 0 a`, `Ioc a 1`, `Ioi 1`
    have hdom_a : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioc 0 a) ∧
        ∫ t in Ioc 0 a, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| ≤ C_phi * C_R * a ^ 8 := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
          (volume.restrict (Ioc 0 a)) :=
        ((hR_cont.mono Ioc_subset_Ioi_self).mul h1sub_cont.continuousOn).aestronglyMeasurable measurableSet_Ioc
      have hpt : ∀ t ∈ Ioc (0 : ℝ) a, ‖R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)‖ ≤ C_phi * C_R * a ^ 8 := by
        intro t ht
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := hR_small t ⟨ht.1, ht.2.trans ha1⟩
        have h2 := (h1sub_bd t ht.1).1
        have ht8 : t ^ 8 ≤ a ^ 8 := pow_le_pow_left₀ ht.1.le ht.2 8
        calc |R t| * |1 - (phiKill a ((t : ℂ) * Complex.I)).re|
            ≤ (C_R * t ^ 8) * C_phi := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ ≤ (C_R * a ^ 8) * C_phi := by gcongr
          _ = C_phi * C_R * a ^ 8 := by ring
      have hint : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioc 0 a) :=
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono' hmeas
          (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
      refine ⟨hint, ?_⟩
      have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top)
        (f := fun t => |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|)
        (fun t ht => by rw [Real.norm_eq_abs, abs_abs]; exact hpt t ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ => abs_nonneg _),
        Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha.le] at hbd
      calc ∫ t in Ioc 0 a, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|
          ≤ C_phi * C_R * a ^ 8 * a := hbd
        _ ≤ C_phi * C_R * a ^ 8 * 1 := mul_le_mul_of_nonneg_left ha1 (by positivity)
        _ = C_phi * C_R * a ^ 8 := mul_one _
    have hdom_mid : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioc a 1) ∧
        ∫ t in Ioc a 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| ≤ C_phi * C_R * a ^ 8 := by
      have hmeas : AEStronglyMeasurable (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
          (volume.restrict (Ioc a 1)) :=
        ((hR_cont.mono (fun t (ht : t ∈ Ioc a 1) => ha.trans ht.1)).mul h1sub_cont.continuousOn).aestronglyMeasurable measurableSet_Ioc
      have hpt : ∀ t ∈ Ioc a 1, ‖R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)‖ ≤ C_phi * C_R * a ^ 8 := by
        intro t ht
        rw [Real.norm_eq_abs, abs_mul]
        have ht0 : 0 < t := ha.trans ht.1
        have h1 := hR_small t ⟨ht0, ht.2⟩
        have h2 := (h1sub_bd t ht0).2
        calc |R t| * |1 - (phiKill a ((t : ℂ) * Complex.I)).re|
            ≤ (C_R * t ^ 8) * (C_phi * (a / t) ^ 8) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ = C_phi * C_R * a ^ 8 := by rw [div_pow]; field_simp [ht0.ne']
      have hint : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioc a 1) :=
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono' hmeas
          (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
      refine ⟨hint, ?_⟩
      have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top)
        (f := fun t => |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|)
        (fun t ht => by rw [Real.norm_eq_abs, abs_abs]; exact hpt t ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ => abs_nonneg _),
        Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at hbd
      calc ∫ t in Ioc a 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|
          ≤ C_phi * C_R * a ^ 8 * (1 - a) := hbd
        _ ≤ C_phi * C_R * a ^ 8 * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = C_phi * C_R * a ^ 8 := mul_one _
    have hdom_tail : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 1) ∧
        ∫ t in Ioi 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| ≤ C_phi * C_R * a ^ 8 := by
      have hinv2 := integrableOn_inv_pow_Ioi (ε := 1) one_pos (m := 2) le_rfl
      have hmeas : AEStronglyMeasurable (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
          (volume.restrict (Ioi 1)) :=
        ((hR_cont.mono fun t ht => zero_lt_one.trans ht).mul h1sub_cont.continuousOn).aestronglyMeasurable measurableSet_Ioi
      have hpt : ∀ t ∈ Ioi (1 : ℝ), ‖R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)‖ ≤
          (C_phi * C_R * a ^ 8) * t ^ (-2 : ℤ) := by
        intro t ht
        rw [Real.norm_eq_abs, abs_mul]
        have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
        have ht0 : 0 < t := zero_lt_one.trans ht
        have h1 := hR_large t ht1
        have h2 := (h1sub_bd t ht0).2
        calc |R t| * |1 - (phiKill a ((t : ℂ) * Complex.I)).re|
            ≤ (C_R * t ^ 6) * (C_phi * (a / t) ^ 8) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ = (C_phi * C_R * a ^ 8) * t ^ (-2 : ℤ) := by
              rw [div_pow, zpow_neg, show t ^ (2 : ℤ) = t ^ 2 by norm_cast]; field_simp [ht0.ne']
      have hint : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 1) :=
        (hinv2.1.const_mul (C_phi * C_R * a ^ 8)).mono' hmeas
          (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
      refine ⟨hint, ?_⟩
      have hle := setIntegral_mono_on hint.norm (hinv2.1.const_mul (C_phi * C_R * a ^ 8)) measurableSet_Ioi
        (fun t ht => by simpa [Real.norm_eq_abs] using hpt t ht)
      rw [integral_const_mul, hinv2.2] at hle
      norm_num at hle
      simpa [Real.norm_eq_abs] using hle
    have hu1 : Ioc (0 : ℝ) a ∪ Ioc a 1 = Ioc (0 : ℝ) 1 := Ioc_union_Ioc_eq_Ioc ha.le ha1
    have hu2 : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi zero_le_one
    have hint01 : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioc 0 1) := by
      rw [← hu1]; exact hdom_a.1.union hdom_mid.1
    have hint_all : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 0) := by
      rw [← hu2]; exact hint01.union hdom_tail.1
    refine ⟨hint_all, ?_⟩
    have hnorm_le : |∫ t in Ioi (0 : ℝ), R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| ≤
        ∫ t in Ioi (0 : ℝ), |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| := by
      have h := norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi (0 : ℝ)))
        (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      simp only [Real.norm_eq_abs] at h
      exact h
    have hsplit1 : ∫ t in Ioi (0 : ℝ), |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| =
        (∫ t in Ioc 0 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|) +
        (∫ t in Ioi 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|) := by
      rw [← hu2, setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi hint01.abs hdom_tail.1.abs]
    have hsplit2 : ∫ t in Ioc (0 : ℝ) 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)| =
        (∫ t in Ioc 0 a, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|) +
        (∫ t in Ioc a 1, |R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)|) := by
      rw [← hu1, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hdom_a.1.abs hdom_mid.1.abs]
    linarith [hdom_a.2, hdom_mid.2, hdom_tail.2]
  refine ⟨hR_int_and_bd.1, hR_int_and_bd.2, ?_⟩
  -- 2. Integrability of each monomial piece on `Ioi 0`
  have hint_neg : ∀ j : ℕ, 1 ≤ j → 2 * j ≤ 8 →
      IntegrableOn (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)) (Ioi 0) := by
    intro j hj h2j
    have hcont : ContinuousOn (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)) (Ioi 0) :=
      (continuous_phiKill_imag_re ha).continuousOn.div (continuousOn_id.pow _)
        fun t ht => pow_ne_zero _ (mem_Ioi.mp ht).ne'
    have h01 : IntegrableOn (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)) (Ioc 0 1) := by
      have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(phiKill a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)‖ ≤ C_phi0 / a ^ 8 := by
        intro t ht
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht.1 _)]
        have hre_le : |(phiKill a ((t : ℂ) * Complex.I)).re| ≤ ‖phiKill a ((t : ℂ) * Complex.I)‖ :=
          Complex.abs_re_le_norm _
        have hbd := hphi0_bd ha (by simp : (0 : ℝ) ≤ ((t : ℂ) * Complex.I).re)
        have hnorm : ‖(t : ℂ) * Complex.I‖ = t := by
          rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
        have hmin : min ((t / a) ^ 8) 1 ≤ (t / a) ^ 8 := min_le_left _ _
        have hle1 : ‖phiKill a ((t : ℂ) * Complex.I)‖ ≤ C_phi0 * (t / a) ^ 8 := by
          rw [phiKill]; rw [hnorm] at hbd; exact hbd.trans (mul_le_mul_of_nonneg_left hmin hC_phi0)
        have ht_pow : t ^ 8 / t ^ (2 * j) ≤ 1 := by
          rw [div_le_one (pow_pos ht.1 _)]
          exact pow_le_pow_of_le_one ht.1.le ht.2 h2j
        calc |(phiKill a ((t : ℂ) * Complex.I)).re| / t ^ (2 * j)
            ≤ (C_phi0 * (t / a) ^ 8) / t ^ (2 * j) :=
              div_le_div_of_nonneg_right (hre_le.trans hle1) (pow_pos ht.1 _).le
          _ = (C_phi0 / a ^ 8) * (t ^ 8 / t ^ (2 * j)) := by rw [div_pow]; ring
          _ ≤ (C_phi0 / a ^ 8) * 1 := mul_le_mul_of_nonneg_left ht_pow (by positivity)
          _ = C_phi0 / a ^ 8 := mul_one _
      exact (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
    have h1inf : IntegrableOn (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)) (Ioi 1) := by
      have hinv := integrableOn_inv_pow_Ioi (ε := 1) one_pos (m := 2 * j) (by omega)
      refine (hinv.1.const_mul C_phi0).mono'
        ((hcont.mono fun t ht => zero_lt_one.trans ht).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (zero_lt_one.trans ht) _)]
      have hbd := hphi0_bd ha (by simp : (0 : ℝ) ≤ ((t : ℂ) * Complex.I).re)
      have hre_le : |(phiKill a ((t : ℂ) * Complex.I)).re| ≤ C_phi0 :=
        (Complex.abs_re_le_norm _).trans (hbd.trans (by simpa using mul_le_mul_of_nonneg_left (min_le_right _ 1) hC_phi0))
      rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hre_le (pow_pos (zero_lt_one.trans ht) _).le
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact h01.union h1inf
  have hint_pos : ∀ k : ℕ, k ≤ 3 →
      IntegrableOn (fun t : ℝ => t ^ (2 * k) * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 0) := by
    intro k hk
    have hcont : Continuous (fun t : ℝ => t ^ (2 * k) * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) :=
      (continuous_id.pow _).mul h1sub_cont
    have h01 : IntegrableOn (fun t : ℝ => t ^ (2 * k) * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioc 0 1) :=
      hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h1inf : IntegrableOn (fun t : ℝ => t ^ (2 * k) * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi 1) := by
      have hinv2 := integrableOn_inv_pow_Ioi (ε := 1) one_pos (m := 2) le_rfl
      refine (hinv2.1.const_mul (C_phi * a ^ 8)).mono'
        (hcont.aestronglyMeasurable)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have ht0 : 0 < t := zero_lt_one.trans ht
      have ht1 : 1 ≤ t := (mem_Ioi.mp ht).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ht0 _)]
      have h2 := (h1sub_bd t ht0).2
      have hpow_le : t ^ (2 * k) ≤ t ^ 6 := pow_le_pow_right₀ ht1 (by omega)
      calc t ^ (2 * k) * |1 - (phiKill a ((t : ℂ) * Complex.I)).re|
          ≤ t ^ 6 * (C_phi * (a / t) ^ 8) := mul_le_mul hpow_le h2 (abs_nonneg _) (by positivity)
        _ = C_phi * a ^ 8 * t ^ (-2 : ℤ) := by
            rw [div_pow, zpow_neg, show t ^ (2 : ℤ) = t ^ 2 by norm_cast]; field_simp [ht0.ne']
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact h01.union h1inf
  -- 3. Algebraic decomposition for `ε > 0` and limit as `ε ↓ 0`
  have hdecomp : ∀ ε : ℝ, 0 < ε →
      (∫ t in Ioi ε, F t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) - b_m4 / (3 * ε ^ 3) - b_m2 / ε =
      -b_m4 * (∫ t in Ioi ε, (phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)
      - b_m2 * (∫ t in Ioi ε, (phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)
      + b0 * (∫ t in Ioi ε, t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      + b2 * (∫ t in Ioi ε, t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      + b4 * (∫ t in Ioi ε, t ^ 4 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      + b6 * (∫ t in Ioi ε, t ^ 6 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      + (∫ t in Ioi ε, R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) := by
    intro ε hε
    have hsub : Ioi ε ⊆ Ioi (0 : ℝ) := fun t ht => hε.trans ht
    have hinv4 := integrableOn_inv_pow_Ioi hε (m := 4) (by norm_num)
    have hinv2 := integrableOn_inv_pow_Ioi hε (m := 2) (by norm_num)
    have hn4 : IntegrableOn (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4) (Ioi ε) :=
      (hint_neg 2 (by norm_num) (by norm_num)).mono_set hsub
    have hn2 : IntegrableOn (fun t : ℝ => (phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2) (Ioi ε) :=
      (hint_neg 1 (by norm_num) (by norm_num)).mono_set hsub
    have hp0 : IntegrableOn (fun t : ℝ => t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi ε) :=
      (hint_pos 0 (by norm_num)).mono_set hsub
    have hp2 : IntegrableOn (fun t : ℝ => t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi ε) :=
      (hint_pos 1 (by norm_num)).mono_set hsub
    have hp4 : IntegrableOn (fun t : ℝ => t ^ 4 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi ε) :=
      (hint_pos 2 (by norm_num)).mono_set hsub
    have hp6 : IntegrableOn (fun t : ℝ => t ^ 6 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi ε) :=
      (hint_pos 3 (by norm_num)).mono_set hsub
    have hRε : IntegrableOn (fun t : ℝ => R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi ε) :=
      hR_int_and_bd.1.mono_set hsub
    have hpt_eq : EqOn (fun t : ℝ => F t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
        (fun t : ℝ =>
          b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4) +
          (b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)) +
          b0 * (t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
          b2 * (t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
          b4 * (t ^ 4 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
          b6 * (t ^ 6 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
          R t * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) (Ioi ε) := by
      intro t ht
      have ht0 : t ≠ 0 := (hε.trans ht).ne'
      simp only [R, zpow_neg, show t ^ (4 : ℤ) = t ^ 4 by norm_cast, show t ^ (2 : ℤ) = t ^ 2 by norm_cast, pow_zero]
      field_simp [ht0]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt_eq]
    have hinv4' : IntegrableOn (fun t : ℝ => t ^ (-4 : ℤ)) (Ioi ε) := hinv4.1
    have hinv2' : IntegrableOn (fun t : ℝ => t ^ (-2 : ℤ)) (Ioi ε) := hinv2.1
    have hi1 : Integrable (fun t : ℝ => b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4))
        (volume.restrict (Ioi ε)) := (hinv4'.const_mul b_m4).sub (hn4.const_mul b_m4)
    have hi2 : Integrable (fun t : ℝ => b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2))
        (volume.restrict (Ioi ε)) := (hinv2'.const_mul b_m2).sub (hn2.const_mul b_m2)
    have hi12 : Integrable (fun t : ℝ =>
        (b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)) +
        (b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)))
        (volume.restrict (Ioi ε)) := hi1.add hi2
    have hi120 : Integrable (fun t : ℝ =>
        (b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)) +
        (b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)) +
        b0 * (t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)))
        (volume.restrict (Ioi ε)) := hi12.add (hp0.const_mul b0)
    have hi1202 : Integrable (fun t : ℝ =>
        (b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)) +
        (b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)) +
        b0 * (t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
        b2 * (t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)))
        (volume.restrict (Ioi ε)) := hi120.add (hp2.const_mul b2)
    have hi12024 : Integrable (fun t : ℝ =>
        (b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)) +
        (b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)) +
        b0 * (t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
        b2 * (t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
        b4 * (t ^ 4 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)))
        (volume.restrict (Ioi ε)) := hi1202.add (hp4.const_mul b4)
    have hi120246 : Integrable (fun t : ℝ =>
        (b_m4 * t ^ (-4 : ℤ) - b_m4 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)) +
        (b_m2 * t ^ (-2 : ℤ) - b_m2 * ((phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)) +
        b0 * (t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
        b2 * (t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
        b4 * (t ^ 4 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) +
        b6 * (t ^ 6 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)))
        (volume.restrict (Ioi ε)) := hi12024.add (hp6.const_mul b6)
    rw [integral_add hi120246 hRε, integral_add hi12024 (hp6.const_mul b6),
      integral_add hi1202 (hp4.const_mul b4), integral_add hi120 (hp2.const_mul b2),
      integral_add hi12 (hp0.const_mul b0), integral_add hi1 hi2,
      integral_sub (hinv4'.const_mul b_m4) (hn4.const_mul b_m4),
      integral_sub (hinv2'.const_mul b_m2) (hn2.const_mul b_m2),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      show ∫ t in Ioi ε, t ^ (-4 : ℤ) = ε ^ (1 - (4 : ℤ)) / ((4 : ℝ) - 1) from hinv4.2,
      show ∫ t in Ioi ε, t ^ (-2 : ℤ) = ε ^ (1 - (2 : ℤ)) / ((2 : ℝ) - 1) from hinv2.2]
    have h3 : b_m4 * (ε ^ (1 - (4 : ℤ)) / ((4 : ℝ) - 1)) = b_m4 / (3 * ε ^ 3) := by
      rw [show (1 : ℤ) - 4 = -3 by norm_num, zpow_neg, show ε ^ (3 : ℤ) = ε ^ 3 by norm_cast]
      field_simp [hε.ne']; ring
    have h1' : b_m2 * (ε ^ (1 - (2 : ℤ)) / ((2 : ℝ) - 1)) = b_m2 / ε := by
      rw [show (1 : ℤ) - 2 = -1 by norm_num, zpow_neg_one]
      field_simp [hε.ne']; ring
    rw [h3, h1']; ring
  -- Take the limit as `ε ↓ 0` using `phiPQ_moment_neg` and `phiPQ_moment_pos`
  have hlim_n4 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, (phiKill a ((t : ℂ) * Complex.I)).re / t ^ 4)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 := phiPQ_moment_neg (p := 8) (q := 8) (j := 2) (by norm_num) (by norm_num) (by norm_num) ha
    simpa [phiKill, h0] using tendsto_setIntegral_Ioi_zero (hint_neg 2 (by norm_num) (by norm_num))
  have hlim_n2 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, (phiKill a ((t : ℂ) * Complex.I)).re / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 := phiPQ_moment_neg (p := 8) (q := 8) (j := 1) (by norm_num) (by norm_num) (by norm_num) ha
    simpa [phiKill, h0] using tendsto_setIntegral_Ioi_zero (hint_neg 1 (by norm_num) (by norm_num))
  have hlim_p0 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, t ^ 0 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 := phiPQ_moment_pos (p := 8) (q := 8) (k := 0) (by norm_num) ha
    have hlim := tendsto_setIntegral_Ioi_zero (hint_pos 0 (by norm_num))
    rw [show (∫ t in Ioi (0 : ℝ), t ^ (2 * 0) * (1 - (phiKill a ((t : ℂ) * Complex.I)).re)) = 0 from h0] at hlim
    exact hlim
  have hlim_p2 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, t ^ 2 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 := phiPQ_moment_pos (p := 8) (q := 8) (k := 1) (by norm_num) ha
    simpa [phiKill, h0] using tendsto_setIntegral_Ioi_zero (hint_pos 1 (by norm_num))
  have hlim_p4 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, t ^ 4 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 := phiPQ_moment_pos (p := 8) (q := 8) (k := 2) (by norm_num) ha
    simpa [phiKill, h0] using tendsto_setIntegral_Ioi_zero (hint_pos 2 (by norm_num))
  have hlim_p6 : Tendsto (fun ε : ℝ => ∫ t in Ioi ε, t ^ 6 * (1 - (phiKill a ((t : ℂ) * Complex.I)).re))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h0 := phiPQ_moment_pos (p := 8) (q := 8) (k := 3) (by norm_num) ha
    simpa [phiKill, h0] using tendsto_setIntegral_Ioi_zero (hint_pos 3 (by norm_num))
  have hlim_R := tendsto_setIntegral_Ioi_zero hR_int_and_bd.1
  have hcomb := ((((((hlim_n4.const_mul (-b_m4)).sub (hlim_n2.const_mul b_m2)).add
    (hlim_p0.const_mul b0)).add (hlim_p2.const_mul b2)).add
    (hlim_p4.const_mul b4)).add (hlim_p6.const_mul b6)).add hlim_R
  simp only [mul_zero, sub_zero, zero_add] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hdecomp ε hε).symm

/-! ### Elementary 4th-order Taylor expansions for `ceEll`, `m(t)`, and `m(t)^{-3/2}` -/

lemma sinh_taylor5_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)| ≤ x ^ 7 := by
  have h1 := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) (n := 7) (by norm_num)
  have h2 := Real.exp_bound (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1) (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  rw [abs_of_nonneg hx0] at h1
  rw [abs_neg, abs_of_nonneg hx0] at h2
  norm_num at h1 h2
  rw [Real.sinh_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

lemma cosh_taylor4_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)| ≤ x ^ 6 := by
  have h1 := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) (n := 6) (by norm_num)
  have h2 := Real.exp_bound (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; exact hx1) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  rw [abs_of_nonneg hx0] at h1
  rw [abs_neg, abs_of_nonneg hx0] at h2
  norm_num at h1 h2
  rw [Real.cosh_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

lemma log_one_add_taylor2 {u : ℝ} (hu0 : 0 ≤ u) :
    0 ≤ Real.log (1 + u) - (u - u ^ 2 / 2) ∧ Real.log (1 + u) - (u - u ^ 2 / 2) ≤ u ^ 3 / 3 := by
  constructor
  · have hmono : MonotoneOn (fun t : ℝ => Real.log (1 + t) - (t - t ^ 2 / 2)) (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ fun t ht => ?_
      · exact (Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id)
          fun t ht => by show (1 : ℝ) + t ≠ 0; linarith [mem_Ici.mp ht]).sub (by fun_prop)
      · exact ((DifferentiableOn.log (differentiableOn_const _ |>.add differentiableOn_id)
          fun t ht => by have ht0 : 0 ≤ t := interior_subset ht; show (1 : ℝ) + t ≠ 0; linarith).sub (by fun_prop))
      · have ht0 : 0 ≤ t := interior_subset ht
        have h1 : HasDerivAt (fun s : ℝ => Real.log (1 + s) - (s - s ^ 2 / 2))
            (1 / (1 + t) - (1 - t)) t := by
          have hl : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
            simpa [one_div] using ((hasDerivAt_id t).const_add 1).log (by show 1 + t ≠ 0; linarith)
          have hp : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - t) t := by
            have := (hasDerivAt_id t).sub (((hasDerivAt_pow 2 t).div_const 2))
            refine this.congr_deriv ?_; ring
          exact hl.sub hp
        rw [h1.deriv]
        have : 1 / (1 + t) - (1 - t) = t ^ 2 / (1 + t) := by field_simp [show 1 + t ≠ 0 by linarith]; ring
        rw [this]; positivity
    have := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) hu0 hu0
    simpa using this
  · have hmono : MonotoneOn (fun t : ℝ => t ^ 3 / 3 - (Real.log (1 + t) - (t - t ^ 2 / 2))) (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ fun t ht => ?_
      · exact (by fun_prop : ContinuousOn (fun t : ℝ => t ^ 3 / 3) (Ici 0)).sub
          ((Real.continuousOn_log.comp (continuousOn_const.add continuousOn_id)
            fun t ht => by show (1 : ℝ) + t ≠ 0; linarith [mem_Ici.mp ht]).sub (by fun_prop))
      · exact ((by fun_prop : DifferentiableOn ℝ (fun t : ℝ => t ^ 3 / 3) (interior (Ici 0))).sub
          ((DifferentiableOn.log (differentiableOn_const _ |>.add differentiableOn_id)
            fun t ht => by have ht0 : 0 ≤ t := interior_subset ht; show (1 : ℝ) + t ≠ 0; linarith).sub (by fun_prop)))
      · have ht0 : 0 ≤ t := interior_subset ht
        have h1 : HasDerivAt (fun s : ℝ => s ^ 3 / 3 - (Real.log (1 + s) - (s - s ^ 2 / 2)))
            (t ^ 2 - (1 / (1 + t) - (1 - t))) t := by
          have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
            simpa using ((hasDerivAt_pow 3 t).div_const 3).congr_deriv (by ring)
          have hl : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
            simpa [one_div] using ((hasDerivAt_id t).const_add 1).log (by show 1 + t ≠ 0; linarith)
          have hp : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - t) t := by
            have := (hasDerivAt_id t).sub (((hasDerivAt_pow 2 t).div_const 2))
            refine this.congr_deriv ?_; ring
          exact h3.sub (hl.sub hp)
        rw [h1.deriv]
        have : t ^ 2 - (1 / (1 + t) - (1 - t)) = t ^ 3 / (1 + t) := by
          field_simp [show 1 + t ≠ 0 by linarith]; ring
        rw [this]; positivity
    have := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) hu0 hu0
    simp only [zero_pow (by norm_num : 3 ≠ 0), zero_div, add_zero, Real.log_one, sub_zero,
      zero_pow (by norm_num : 2 ≠ 0)] at this
    linarith

/-- Fourth-order expansion of `ℓ(x) = log(x coth x)`: `|ℓ(x) - (x²/3 - 7/90 x⁴)| ≤ 20 x⁶` on `(0, 1/2]`. -/
lemma ceEll_taylor4 {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    |ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)| ≤ 20 * x ^ 6 := by
  have hs := sinh_taylor5_bound hx0.le (by linarith)
  have hc := cosh_taylor4_bound hx0.le (by linarith)
  have hsh_pos : x ≤ Real.sinh x := self_le_sinh_nonneg hx0.le
  have hsh0 : 0 < Real.sinh x := lt_of_lt_of_le hx0 hsh_pos
  set u : ℝ := x * Real.cosh x / Real.sinh x - 1
  have hu_eq : 1 + u = x / Real.tanh x := by
    simp only [u, Real.tanh_eq_sinh_div_cosh]
    field_simp [hsh0.ne', (zero_lt_one.trans_le (one_le_cosh_real x)).ne']; ring
  have hu_nn : 0 ≤ u := by
    have hlog_pos : 0 < Real.log (1 + u) := by rw [hu_eq]; exact ceEll_pos hx0
    have h1u_pos : 0 ≤ 1 + u := by
      rw [hu_eq, Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg hx0.le (div_nonneg hsh0.le (zero_lt_one.trans_le (one_le_cosh_real x)).le)
    have h1 : 1 < 1 + u := (Real.log_pos_iff h1u_pos).mp hlog_pos
    linarith
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hx4 : x ^ 4 ≤ 1 / 16 := by nlinarith
  -- Bound `|u - (x²/3 - x⁴/45)| ≤ 4 x⁶`
  have hu_bd : |u - (x ^ 2 / 3 - x ^ 4 / 45)| ≤ 4 * x ^ 6 := by
    have hnum : (u - (x ^ 2 / 3 - x ^ 4 / 45)) * (Real.sinh x / x) =
        Real.cosh x - (1 + x ^ 2 / 3 - x ^ 4 / 45) * (Real.sinh x / x) := by
      simp only [u]; field_simp [hx0.ne', hsh0.ne']; ring
    have hsh_div : |Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)| ≤ x ^ 6 := by
      rw [show Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120) =
          (Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)) / x by field_simp [hx0.ne'],
        abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
      linarith [hs]
    have hcoeff_bd : |1 + x ^ 2 / 3 - x ^ 4 / 45| ≤ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, pow_nonneg hx0.le 4]
    have halg : Real.cosh x - (1 + x ^ 2 / 3 - x ^ 4 / 45) * (Real.sinh x / x) =
        (Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)) -
        (1 + x ^ 2 / 3 - x ^ 4 / 45) * (Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)) -
        x ^ 6 * (-1 / 1080 - x ^ 2 / 5400) := by ring
    have hprod_le : |(u - (x ^ 2 / 3 - x ^ 4 / 45)) * (Real.sinh x / x)| ≤ 4 * x ^ 6 := by
      rw [hnum, halg]
      have h1 : |Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)| ≤ x ^ 6 := hc
      have h2 : |(1 + x ^ 2 / 3 - x ^ 4 / 45) * (Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120))| ≤ 2 * x ^ 6 := by
        rw [abs_mul]; exact mul_le_mul hcoeff_bd hsh_div (abs_nonneg _) zero_le_two
      have h3 : |x ^ 6 * (-1 / 1080 - x ^ 2 / 5400)| ≤ x ^ 6 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0.le 6)]
        have : |-1 / 1080 - x ^ 2 / 5400| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg x]
        nlinarith [pow_nonneg hx0.le 6]
      have htri1 := abs_sub (Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24) -
        (1 + x ^ 2 / 3 - x ^ 4 / 45) * (Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)))
        (x ^ 6 * (-1 / 1080 - x ^ 2 / 5400))
      have htri2 := abs_sub (Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24))
        ((1 + x ^ 2 / 3 - x ^ 4 / 45) * (Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)))
      linarith
    have hge1 : 1 ≤ Real.sinh x / x := (one_le_div hx0).mpr hsh_pos
    rw [abs_mul, abs_of_pos (by linarith : 0 < Real.sinh x / x)] at hprod_le
    nlinarith [abs_nonneg (u - (x ^ 2 / 3 - x ^ 4 / 45))]
  have hlog := log_one_add_taylor2 hu_nn
  have hu_le : u ≤ x ^ 2 := by
    have := (abs_le.mp hu_bd).2
    have hx6 : x ^ 6 ≤ x ^ 2 / 16 := by nlinarith [sq_nonneg x]
    nlinarith [pow_nonneg hx0.le 4]
  have hu3 : u ^ 3 / 3 ≤ x ^ 6 := by
    have : u ^ 3 ≤ (x ^ 2) ^ 3 := pow_le_pow_left₀ hu_nn hu_le 3
    nlinarith [pow_nonneg hx0.le 6]
  have hsq_diff : |u ^ 2 / 2 - x ^ 4 / 18| ≤ 2 * x ^ 6 := by
    have h1 : |u - x ^ 2 / 3| ≤ 2 * x ^ 4 := by
      have := abs_le.mp hu_bd
      have hx6 : x ^ 6 ≤ x ^ 4 / 4 := by nlinarith [pow_nonneg hx0.le 4]
      rw [abs_le]; constructor <;> nlinarith [pow_nonneg hx0.le 4]
    have h2 : |u + x ^ 2 / 3| ≤ 2 * x ^ 2 := by
      rw [abs_of_nonneg (by linarith [sq_nonneg x])]; linarith
    have heq : u ^ 2 / 2 - x ^ 4 / 18 = (u - x ^ 2 / 3) * (u + x ^ 2 / 3) / 2 := by ring
    rw [heq, abs_div, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    nlinarith
  have hell_eq : ceEll x = Real.log (1 + u) := by unfold ceEll; rw [hu_eq]
  rw [hell_eq]
  have hsplit : Real.log (1 + u) - (x ^ 2 / 3 - 7 / 90 * x ^ 4) =
      (Real.log (1 + u) - (u - u ^ 2 / 2)) + (u - (x ^ 2 / 3 - x ^ 4 / 45)) - (u ^ 2 / 2 - x ^ 4 / 18) := by
    ring
  rw [hsplit]
  have htri1 := abs_sub ((Real.log (1 + u) - (u - u ^ 2 / 2)) + (u - (x ^ 2 / 3 - x ^ 4 / 45))) (u ^ 2 / 2 - x ^ 4 / 18)
  have htri2 := abs_add_le (Real.log (1 + u) - (u - u ^ 2 / 2)) (u - (x ^ 2 / 3 - x ^ 4 / 45))
  have hlog_abs : |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ x ^ 6 := by
    rw [abs_of_nonneg hlog.1]; exact hlog.2.trans hu3
  linarith [pow_nonneg hx0.le 6]

/-- Elementary bound `|(1 + y)^{-3/2} - (1 - 3y/2)| ≤ 10 y²` for `|y| ≤ 1/4`. -/
lemma rpow_neg_three_halves_taylor {y : ℝ} (hy : |y| ≤ 1 / 4) :
    |(1 + y) ^ (-(3 / 2 : ℝ)) - (1 - 3 / 2 * y)| ≤ 10 * y ^ 2 := by
  have hy1 : 3 / 4 ≤ 1 + y := by linarith [(abs_le.mp hy).1]
  have hy2 : 1 + y ≤ 5 / 4 := by linarith [(abs_le.mp hy).2]
  -- Let `s = √(1 + y) > 0`; then `(1+y)^{-3/2} = s^{-3}` and `s^2 = 1 + y`
  set s := Real.sqrt (1 + y)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 + y := Real.sq_sqrt (by linarith)
  have hs_ge : 4 / 5 ≤ s := by
    exact le_of_sq_le_sq (by rw [hs2]; nlinarith) hs_pos.le
  have hrpow : (1 + y) ^ (-(3 / 2 : ℝ)) = s⁻¹ ^ 3 := by
    rw [show -(3 / 2 : ℝ) = (1 / 2 : ℝ) * (-3 : ℝ) by norm_num, Real.rpow_mul (by linarith),
      ← Real.sqrt_eq_rpow, show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast,
      zpow_neg, inv_pow]
    rfl
  rw [hrpow]
  -- `|s^{-3} - (1 - 3y/2)| = |(1 - (1 - 3y/2) s^3) / s^3|`
  -- And `1 - (1 - 3y/2)^2 s^6 = 1 - (1 - 3y/2)^2 (1+y)^3 = y^2 (15/4 + 5y/4 - 15y^2/4 - 9y^3/4)`
  have hsq_id : 1 - (1 - 3 / 2 * y) ^ 2 * (1 + y) ^ 3 =
      y ^ 2 * (15 / 4 + 5 / 4 * y - 15 / 4 * y ^ 2 - 9 / 4 * y ^ 3) := by ring
  have h1 : |1 - (1 - 3 / 2 * y) * s ^ 3| ≤ 4 * y ^ 2 := by
    have hprod : (1 - (1 - 3 / 2 * y) * s ^ 3) * (1 + (1 - 3 / 2 * y) * s ^ 3) =
        1 - (1 - 3 / 2 * y) ^ 2 * (1 + y) ^ 3 := by
      have : (s ^ 3) ^ 2 = (1 + y) ^ 3 := by rw [← pow_mul, mul_comm 3 2, pow_mul, hs2]
      calc (1 - (1 - 3 / 2 * y) * s ^ 3) * (1 + (1 - 3 / 2 * y) * s ^ 3)
          = 1 - (1 - 3 / 2 * y) ^ 2 * (s ^ 3) ^ 2 := by ring
        _ = 1 - (1 - 3 / 2 * y) ^ 2 * (1 + y) ^ 3 := by rw [this]
    have hfac_ge : 1 ≤ 1 + (1 - 3 / 2 * y) * s ^ 3 := by
      have : 0 ≤ 1 - 3 / 2 * y := by linarith [(abs_le.mp hy).2]
      have : 0 ≤ s ^ 3 := pow_nonneg hs_pos.le 3
      nlinarith
    have hrhs_le : |1 - (1 - 3 / 2 * y) ^ 2 * (1 + y) ^ 3| ≤ 4 * y ^ 2 := by
      rw [hsq_id, abs_mul, abs_of_nonneg (sq_nonneg y)]
      have hpoly : |15 / 4 + 5 / 4 * y - 15 / 4 * y ^ 2 - 9 / 4 * y ^ 3| ≤ 4 := by
        have hy_ab := abs_le.mp hy
        have hy2_le : y ^ 2 ≤ 1 / 16 := by nlinarith
        have hy3_le : |y ^ 3| ≤ 1 / 64 := by
          rw [abs_pow]; exact (pow_le_pow_left₀ (abs_nonneg y) hy 3).trans (by norm_num)
        have hy3_ab := abs_le.mp hy3_le
        rw [abs_le]; constructor <;> nlinarith
      nlinarith [sq_nonneg y]
    rw [← hprod, abs_mul, abs_of_pos (by linarith : 0 < 1 + (1 - 3 / 2 * y) * s ^ 3)] at hrhs_le
    nlinarith [abs_nonneg (1 - (1 - 3 / 2 * y) * s ^ 3)]
  have hrewrite : s⁻¹ ^ 3 - (1 - 3 / 2 * y) = (1 - (1 - 3 / 2 * y) * s ^ 3) / s ^ 3 := by
    field_simp [hs_pos.ne']
  rw [hrewrite, abs_div, abs_of_pos (pow_pos hs_pos 3), div_le_iff₀ (pow_pos hs_pos 3)]
  have hs3_ge : (4 / 5 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs_ge 3
  nlinarith [sq_nonneg y]

/-- Exact singular expansion of the floor integral `∫_ε^∞ α_fl m'(t) / m(t)^{5/2} dt = (2/3) α_fl m(ε)^{-3/2}`:
`|(2/3) α_fl m(ε)^{-3/2} - (4 α_osc / (π² ε³) + 7 α_osc / (20 ε))| ≤ C ε` for `0 < ε ≤ 1/4`. -/
lemma floor_tail_integral_and_asymp :
    (∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun t : ℝ => uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ)) (Ioi ε) ∧
      ∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ) =
        (2 / 3) * uctAlphaFl * uctM ε ^ (-(3 / 2 : ℝ))) ∧
    ∃ C ≥ 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      |(2 / 3) * uctAlphaFl * uctM ε ^ (-(3 / 2 : ℝ)) -
        (4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + 7 * uctAlphaOsc / (20 * ε))| ≤ C * ε := by
  constructor
  · intro ε hε
    let F : ℝ → ℝ := fun t => -((2 / 3) * uctAlphaFl * uctM t ^ (-(3 / 2 : ℝ)))
    have hd : ∀ t : ℝ, ε ≤ t → HasDerivAt F (uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ)) t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hε ht
      have hm0 : 0 < uctM t := uctM_pos ht0
      have h1 : HasDerivAt uctM (uctMderiv t) t := hasDerivAt_uctM ht0
      have h2 : HasDerivAt (fun s => uctM s ^ (-(3 / 2 : ℝ)))
          (-(3 / 2 : ℝ) * uctM t ^ (-(3 / 2 : ℝ) - 1) * uctMderiv t) t :=
        (h1.rpow_const (Or.inl hm0.ne')).congr_deriv (by ring)
      have h3 := (h2.const_mul ((2 / 3 : ℝ) * uctAlphaFl)).neg
      refine h3.congr_deriv ?_
      have hexp : -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) := by norm_num
      rw [hexp, Real.rpow_neg hm0.le]
      field_simp [(Real.rpow_pos_of_pos hm0 _).ne']
    have hnn : ∀ t : ℝ, ε < t → 0 ≤ uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := hε.trans ht
      have hfl : 0 < uctAlphaFl := by
        unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
      have hmd := uctMderiv_pos ht0
      have hm := Real.rpow_pos_of_pos (uctM_pos ht0) (5 / 2 : ℝ)
      positivity
    have hlim : Tendsto F atTop (𝓝 0) := by
      -- `uctM t = ceEll (π t / 2) → ∞`, so `uctM t ^ (-3/2) → 0`
      have hm_top : Tendsto uctM atTop atTop := by
        have h1 : Tendsto (fun t : ℝ => Real.log (π * t / 2)) atTop atTop :=
          Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos |>.atTop_div_const two_pos)
        refine tendsto_atTop_mono' atTop ?_ h1
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        unfold uctM ceEll
        have hx : 0 < π * t / 2 := by positivity
        have htanh : Real.tanh (π * t / 2) < 1 := by
          rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (by linarith [one_le_cosh_real (π * t / 2)])]
          rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-(π * t / 2))]
        have htanh_pos : 0 < Real.tanh (π * t / 2) := by
          rw [Real.tanh_eq_sinh_div_cosh]
          exact div_pos (sinh_pos_of_pos hx) (by linarith [one_le_cosh_real (π * t / 2)])
        exact Real.log_le_log hx ((le_div_iff₀ htanh_pos).mpr (by nlinarith))
      have hrp : Tendsto (fun t : ℝ => uctM t ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp hm_top
      simpa [F] using (hrp.const_mul ((2 / 3) * uctAlphaFl)).neg
    have key := ftc_Ioi hd hnn hlim
    refine ⟨key.1, ?_⟩
    rw [key.2]; simp only [F, neg_neg]
  · -- Asymptotic bound on `(0, 1/4]`
    have hfl_pos : 0 < uctAlphaFl := by
      unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    have hosc_pos : 0 < uctAlphaOsc := by
      rw [uctAlphaOsc_eq]; have := Real.pi_pos; positivity
    refine ⟨10000 * uctAlphaOsc, by positivity, fun ε hε hε4 => ?_⟩
    set x : ℝ := π * ε / 2
    have hx0 : 0 < x := by positivity
    have hx1 : x ≤ 1 / 2 := by
      have hpi4 : π < 4 := Real.pi_lt_four
      simp only [x]; nlinarith
    have hce := ceEll_taylor4 hx0 hx1
    -- Write `uctM ε = (x^2 / 3) * (1 + y)` with `y = 3 * ceEll x / x^2 - 1`
    set y : ℝ := 3 * ceEll x / x ^ 2 - 1
    have hy_eq : uctM ε = (x ^ 2 / 3) * (1 + y) := by
      unfold uctM; simp only [y]; field_simp [hx0.ne']; ring
    have hy_bd : |y - (-7 / 30 * x ^ 2)| ≤ 60 * x ^ 4 := by
      have : y - (-7 / 30 * x ^ 2) = 3 * (ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2 := by
        simp only [y]; field_simp [hx0.ne']; ring
      rw [this, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (sq_pos_of_pos hx0),
        div_le_iff₀ (sq_pos_of_pos hx0)]
      nlinarith [hce]
    have hy_small : |y| ≤ 1 / 4 := by
      have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
      have hx4 : x ^ 4 ≤ 1 / 16 := by nlinarith
      have htri := abs_le.mp hy_bd
      -- Wait: `60 * (1/16)` is too big! Let's bound `|y|` directly from `ceEll_lt_sq_div_three` and `ceEll ≥ x^2/3 - 2/15 x^4`!
      have hlt := ceEll_lt_sq_div_three hx0
      have hge : x ^ 2 / 3 - 2 / 15 * x ^ 4 ≤ ceEll x := by
        have h1 := ceHth_le_of_le_one hx0 (by linarith : x ≤ 1)
        have e : ceEll x = x ^ 2 / 3 - ceHth x := by
          unfold ceEll ceHth
          rw [show x / Real.tanh x = (Real.tanh x / x)⁻¹ by rw [inv_div], Real.log_inv]; ring
        linarith
      have hy_le0 : y ≤ 0 := by
        simp only [y]; rw [sub_nonpos, div_le_one (sq_pos_of_pos hx0)]; linarith
      have hy_ge : -(2 / 5 * x ^ 2) ≤ y := by
        simp only [y]; rw [le_sub_iff_add_le, le_div_iff₀ (sq_pos_of_pos hx0)]; nlinarith
      rw [abs_le]; constructor <;> nlinarith
    have hrpow_y := rpow_neg_three_halves_taylor hy_small
    -- Now combine `(2/3) α_fl (x^2/3)^{-3/2} = 4 α_osc / (π² ε³)`
    have hpref : (2 / 3) * uctAlphaFl * (x ^ 2 / 3) ^ (-(3 / 2 : ℝ)) = 4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) := by
      have h1 : (x ^ 2 / 3) ^ (-(3 / 2 : ℝ)) = 3 * Real.sqrt 3 / x ^ 3 := by
        have hx3 : (x ^ 2) ^ (-(3 / 2 : ℝ)) = (x ^ 3)⁻¹ := by
          rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le,
            show ((2 : ℕ) : ℝ) * -(3 / 2 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast]
        have h3_rp : (3 : ℝ) ^ (-(3 / 2 : ℝ)) = (3 * Real.sqrt 3)⁻¹ := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
            show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
            Real.rpow_one, ← Real.sqrt_eq_rpow]
        rw [Real.div_rpow (sq_nonneg x) (by norm_num), hx3, h3_rp]
        field_simp [hx0.ne', (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
      rw [h1, uctAlphaOsc_eq]
      simp only [x]
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp [Real.pi_pos.ne', hε.ne']
      nlinarith [h3]
    have hmul_rpow : uctM ε ^ (-(3 / 2 : ℝ)) = (x ^ 2 / 3) ^ (-(3 / 2 : ℝ)) * (1 + y) ^ (-(3 / 2 : ℝ)) := by
      rw [hy_eq, Real.mul_rpow (by positivity) (by linarith [(abs_le.mp hy_small).1])]
    rw [hmul_rpow, ← mul_assoc, hpref]
    have hlead : 4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) * (1 - 3 / 2 * (-7 / 30 * x ^ 2)) =
        4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + 7 * uctAlphaOsc / (20 * ε) := by
      simp only [x]; field_simp [Real.pi_pos.ne', hε.ne']; ring
    rw [← hlead, ← mul_sub]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * uctAlphaOsc / (π ^ 2 * ε ^ 3))]
    have hdiff_y : |(1 + y) ^ (-(3 / 2 : ℝ)) - (1 - 3 / 2 * (-7 / 30 * x ^ 2))| ≤ 100 * x ^ 4 := by
      have hsplit : (1 + y) ^ (-(3 / 2 : ℝ)) - (1 - 3 / 2 * (-7 / 30 * x ^ 2)) =
          ((1 + y) ^ (-(3 / 2 : ℝ)) - (1 - 3 / 2 * y)) - 3 / 2 * (y - (-7 / 30 * x ^ 2)) := by ring
      rw [hsplit]
      have hy2_le : y ^ 2 ≤ x ^ 4 := by
        have hlt := ceEll_lt_sq_div_three hx0
        have hge : x ^ 2 / 3 - 2 / 15 * x ^ 4 ≤ ceEll x := by
          have h1 := ceHth_le_of_le_one hx0 (by linarith : x ≤ 1)
          have e : ceEll x = x ^ 2 / 3 - ceHth x := by
            unfold ceEll ceHth
            rw [show x / Real.tanh x = (Real.tanh x / x)⁻¹ by rw [inv_div], Real.log_inv]; ring
          linarith
        have hy_le0 : y ≤ 0 := by simp only [y]; rw [sub_nonpos, div_le_one (sq_pos_of_pos hx0)]; linarith
        have hy_ge : -(2 / 5 * x ^ 2) ≤ y := by
          simp only [y]; rw [le_sub_iff_add_le, le_div_iff₀ (sq_pos_of_pos hx0)]; nlinarith
        nlinarith [sq_nonneg x]
      have htri := abs_sub ((1 + y) ^ (-(3 / 2 : ℝ)) - (1 - 3 / 2 * y)) (3 / 2 * (y - (-7 / 30 * x ^ 2)))
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at htri
      linarith [hrpow_y, hy_bd, hy2_le]
    have hpi4 : π < 4 := Real.pi_lt_four
    have hpi2 : π ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
    calc 4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) * |(1 + y) ^ (-(3 / 2 : ℝ)) - (1 - 3 / 2 * (-7 / 30 * x ^ 2))|
        ≤ 4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) * (100 * x ^ 4) := by gcongr
      _ = 25 * π ^ 2 * (uctAlphaOsc * ε) := by simp only [x]; field_simp [Real.pi_pos.ne', hε.ne']; ring
      _ ≤ 10000 * (uctAlphaOsc * ε) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 10000 * uctAlphaOsc * ε := by ring

/-! ### Holomorphic local extension of `t⁴ |H_0(it)| / m(t)` near `0` and Laurent expansions -/

/-- Holomorphic `ℓ(w) = log(cosh w / sinhQ w)` on `ball (0 : ℂ) (1/2)`. -/
noncomputable def ellC (w : ℂ) : ℂ := Complex.log (Complex.cosh w / CtOuter.sinhQ w)

/-- Holomorphic `ℓ(w) / w²` on `ball (0 : ℂ) (1/2)` via two applications of `dslope`. -/
noncomputable def ellQ (w : ℂ) : ℂ := dslope (dslope ellC 0) 0 w

lemma ellC_even (w : ℂ) : ellC (-w) = ellC w := by
  unfold ellC
  rw [Complex.cosh_neg]
  have hq : CtOuter.sinhQ (-w) = CtOuter.sinhQ w := by
    unfold CtOuter.sinhQ
    refine tsum_congr fun n => ?_
    rw [(even_two_mul n).neg_pow]
  rw [hq]

lemma differentiableOn_ellC : DifferentiableOn ℂ ellC (Metric.ball (0 : ℂ) (1 / 2)) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have hw2 : ‖w‖ ≤ 2 := by linarith
  have hQ_re : 0 < (CtOuter.sinhQ w).re := CtOuter.re_sinhQ_pos hw2
  have hQ_ne : CtOuter.sinhQ w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hQ_re; linarith
  -- Bound `‖cosh w / sinhQ w - 1‖ < 1` so `Re(cosh w / sinhQ w) > 0`
  have hQ_sub : ‖CtOuter.sinhQ w - 1‖ ≤ 1 / 4 := by
    have hT := CtOuter.sinhQ_sub_one w
    have hT_bd : ‖CtOuter.sinhT w‖ ≤ 1 := by
      have h1 := CtOuter.norm_six_sinhT_sub_one_lt_one hw2
      have htri := norm_sub_norm_le (6 * CtOuter.sinhT w) 1
      rw [norm_mul, Complex.norm_ofNat, norm_one] at htri
      linarith
    rw [hT, norm_mul, norm_pow]
    have : ‖w‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg w]
    nlinarith [norm_nonneg (CtOuter.sinhT w)]
  have hQ_norm_ge : 3 / 4 ≤ ‖CtOuter.sinhQ w‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (1 - CtOuter.sinhQ w)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at htri
    linarith
  have hcosh_sub : ‖Complex.cosh w - 1‖ ≤ 1 / 4 := by
    have h2p := Complex.exp_bound (x := w) (by linarith) (n := 2) (by norm_num)
    have h2m := Complex.exp_bound (x := -w) (by rw [norm_neg]; linarith) (n := 2) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Nat.factorial, Nat.cast_one, div_one, Nat.cast_ofNat, norm_neg] at h2p h2m
    have hcb : Complex.cosh w - 1 = ((Complex.exp w - (1 + w)) + (Complex.exp (-w) - (1 + -w))) / 2 := by
      rw [Complex.cosh]; ring
    rw [hcb, norm_div, Complex.norm_ofNat]
    have htri := norm_add_le (Complex.exp w - (1 + w)) (Complex.exp (-w) - (1 + -w))
    have hwsq : ‖w‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg w]
    norm_num at h2p h2m
    linarith
  have hrat_re : 0 < (Complex.cosh w / CtOuter.sinhQ w).re := by
    have hdiff : Complex.cosh w / CtOuter.sinhQ w - 1 =
        ((Complex.cosh w - 1) - (CtOuter.sinhQ w - 1)) / CtOuter.sinhQ w := by
      field_simp [hQ_ne]; ring
    have hnorm_lt : ‖Complex.cosh w / CtOuter.sinhQ w - 1‖ < 1 := by
      rw [hdiff, norm_div, div_lt_one (by linarith)]
      have htri := norm_sub_le (Complex.cosh w - 1) (CtOuter.sinhQ w - 1)
      linarith
    have hre := (Complex.abs_re_le_norm (Complex.cosh w / CtOuter.sinhQ w - 1)).trans_lt hnorm_lt
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith [(abs_lt.mp hre).1]
  have hd_quot : DifferentiableAt ℂ (fun u => Complex.cosh u / CtOuter.sinhQ u) w :=
    (Complex.differentiable_cosh w).div (CtOuter.differentiable_sinhQ w) hQ_ne
  exact (hd_quot.clog (Or.inl hrat_re)).differentiableWithinAt

lemma ellC_ofReal {x : ℝ} (hx0 : 0 < x) :
    ellC (x : ℂ) = ((ceEll x : ℝ) : ℂ) := by
  unfold ellC ceEll
  rw [← Complex.ofReal_cosh, CtOuter.sinhQ_ofReal hx0.ne']
  have hsh_pos : 0 < Real.sinh x := sinh_pos_of_pos hx0
  have h1 : ((Real.cosh x : ℝ) : ℂ) / (((Real.sinh x / x : ℝ) : ℂ)) =
      (((x / Real.tanh x : ℝ) : ℂ)) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hsh_pos.ne', Complex.ofReal_ne_zero.mpr hx0.ne',
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le (one_le_cosh_real x)).ne']
  rw [h1, Complex.ofReal_log (by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg hx0.le (div_nonneg hsh_pos.le (by linarith [one_le_cosh_real x])))]

lemma differentiableOn_ellQ : DifferentiableOn ℂ ellQ (Metric.ball (0 : ℂ) (1 / 2)) := by
  have h1 : DifferentiableOn ℂ (dslope ellC 0) (Metric.ball (0 : ℂ) (1 / 2)) :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr
      differentiableOn_ellC
  exact (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr h1

lemma ellC_zero : ellC 0 = 0 := by
  simp [ellC, CtOuter.sinhQ_zero]

lemma deriv_ellC_zero : deriv ellC 0 = 0 := by
  have h1 := deriv_comp_neg ellC 0
  have hfun : (fun w => ellC (-w)) = ellC := funext ellC_even
  rw [hfun, neg_zero] at h1
  -- `deriv ellC 0 = - deriv ellC 0`
  have h2 : deriv ellC 0 + deriv ellC 0 = 0 := by linear_combination h1
  have h2' : (2 : ℂ) * deriv ellC 0 = 0 := by linear_combination h2
  exact (mul_eq_zero.mp h2').resolve_left (by norm_num)

lemma ellQ_eq_div {w : ℂ} (hw : w ≠ 0) : ellQ w = ellC w / w ^ 2 := by
  unfold ellQ
  rw [dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, dslope_same, deriv_ellC_zero,
    slope_def_field, ellC_zero, sub_zero, sub_zero, sub_zero]
  field_simp [hw]

lemma ellQ_zero : ellQ 0 = (1 / 3 : ℂ) := by
  have hcont : ContinuousAt ellQ 0 :=
    (differentiableOn_ellQ.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).continuousAt
  have ht1 : Tendsto (fun x : ℝ => ellQ (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (ellQ 0)) :=
    hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ht2 : Tendsto (fun x : ℝ => ellQ (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3 : ℂ)) := by
    have hreal : Tendsto (fun x : ℝ => ceEll x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3 : ℝ)) := by
      refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      have hmem : Ioo (0 : ℝ) (min (1 / 2) (Real.sqrt (ε / 10))) ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT (lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity)))
      filter_upwards [hmem] with x hx
      rw [Real.dist_eq]
      have hx0 : 0 < x := hx.1
      have hx12 : x ≤ 1 / 2 := hx.2.le.trans (min_le_left _ _)
      have hce := ceEll_taylor4 hx0 hx12
      have hdiff : |ceEll x / x ^ 2 - 1 / 3| ≤ 10 * x ^ 2 := by
        rw [show ceEll x / x ^ 2 - 1 / 3 = (ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2 - 7 / 90 * x ^ 2 by
          field_simp [hx0.ne']; ring]
        have h1 : |(ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2| ≤ 20 * x ^ 4 := by
          rw [abs_div, abs_of_pos (sq_pos_of_pos hx0), div_le_iff₀ (sq_pos_of_pos hx0)]
          nlinarith [hce]
        have hx2_le : x ^ 2 ≤ 1 / 4 := by nlinarith
        have htri := abs_sub ((ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2) (7 / 90 * x ^ 2)
        rw [abs_of_nonneg (by positivity : 0 ≤ 7 / 90 * x ^ 2)] at htri
        nlinarith [sq_nonneg x]
      have hxsq : x ^ 2 < ε / 10 := by
        have hlt : x < Real.sqrt (ε / 10) := lt_of_lt_of_le hx.2 (min_le_right _ _)
        calc x ^ 2 < (Real.sqrt (ε / 10)) ^ 2 := sq_lt_sq' (by linarith) hlt
          _ = ε / 10 := Real.sq_sqrt (by positivity)
      linarith
    have hC : Tendsto (fun x : ℝ => ((ceEll x / x ^ 2 : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3 : ℂ)) := by
      have h1 : Tendsto (fun x : ℝ => ((ceEll x / x ^ 2 : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (((1 / 3 : ℝ) : ℂ))) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      simpa using h1
    refine hC.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    rw [ellQ_eq_div (Complex.ofReal_ne_zero.mpr hx.1.ne'), ellC_ofReal hx.1]
    push_cast; rfl
  exact tendsto_nhds_unique ht1 ht2

/-- Even `C^∞` functions on `(-r, r)` have a 12th-order even Taylor polynomial with `O(t^{12})` remainder. -/
private lemma even_taylor12 {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioo (-r) r))
    (heven : ∀ t ∈ Ioo (-r) r, g (-t) = g t) :
    ∃ (c0 c2 c4 c6 c8 c10 C : ℝ), 0 ≤ C ∧
      ∀ t ∈ Icc (-(r / 2)) (r / 2),
        |g t - (c0 + c2 * t ^ 2 + c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10)| ≤ C * |t| ^ 12 := by
  let c : ℕ → ℝ := fun k => iteratedDeriv (2 * k) g 0 / ((2 * k).factorial : ℝ)
  let P : ℝ → ℝ := fun t => ∑ k ∈ Finset.range 6, c k * t ^ (2 * k)
  let R : ℝ → ℝ := fun t => g t - P t
  have hR_cd : ContDiffOn ℝ (⊤ : ℕ∞) R (Ioo (-r) r) :=
    hg.sub ((ContDiff.sum fun k _ => contDiff_const.mul (contDiff_id.pow (2 * k))).contDiffOn)
  -- All derivatives of `R` of order `< 12` vanish at `0`
  have hR_zero : ∀ j < 12, iteratedDeriv j R 0 = 0 := by
    intro j hj
    have hg_at : ContDiffAt ℝ (j : WithTop ℕ∞) g 0 :=
      (hg.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, hr⟩)).of_le (WithTop.coe_le_coe.mpr le_top)
    have hP_at : ContDiffAt ℝ (j : WithTop ℕ∞) P 0 :=
      ((ContDiff.sum fun k _ => contDiff_const.mul (contDiff_id.pow (2 * k))).contDiffAt).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hsub : iteratedDeriv j R 0 = iteratedDeriv j g 0 - iteratedDeriv j P 0 := by
      show iteratedDeriv j (g - P) 0 = _
      exact iteratedDeriv_sub hg_at hP_at
    rw [hsub]
    have hP_deriv : iteratedDeriv j P 0 =
        ∑ k ∈ Finset.range 6, c k * iteratedDeriv j (fun t : ℝ => t ^ (2 * k)) 0 := by
      have h1 := iteratedDeriv_sum (I := Finset.range 6)
        (f := fun k (t : ℝ) => c k * t ^ (2 * k)) (n := j) (x := 0)
        fun k _ => (contDiff_const.mul (contDiff_id.pow (2 * k))).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr le_top)
      rw [show P = ∑ k ∈ Finset.range 6, fun t : ℝ => c k * t ^ (2 * k) by ext t; simp [P], h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [iteratedDeriv_const_mul_field]
    have hpow_zero : ∀ m : ℕ, iteratedDeriv j (fun t : ℝ => t ^ m) 0 =
        if j = m then (m.factorial : ℝ) else 0 := by
      intro m
      have h1 : ∀ n d : ℕ, iteratedDeriv n (fun t : ℝ => t ^ d) 0 =
          if n = d then (d.factorial : ℝ) else 0 := by
        intro n
        induction n with
        | zero =>
          intro d; cases d <;> simp
        | succ n ih =>
          intro d
          rw [iteratedDeriv_succ']
          have hd : deriv (fun t : ℝ => t ^ d) = fun t => (d : ℝ) * t ^ (d - 1) := by
            ext t; exact (hasDerivAt_pow d t).deriv
          rw [hd, iteratedDeriv_const_mul_field]
          cases d with
          | zero => simp
          | succ d =>
            simp only [Nat.add_sub_cancel, ih d]
            split_ifs with h1 h2
            · rw [Nat.factorial_succ]; push_cast; ring
            · omega
            · omega
            · ring
      exact h1 j m
    rw [hP_deriv]
    simp_rw [hpow_zero]
    rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk6 : k < 6 := by omega
      have hsum_val : ∑ m ∈ Finset.range 6, c m * (if j = 2 * m then ((2 * m).factorial : ℝ) else 0) =
          iteratedDeriv j g 0 := by
        rw [Finset.sum_eq_single k]
        · have hjeq : j = 2 * k := by omega
          simp only [hjeq, ↓reduceIte, c]
          exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        · intro m _ hmk
          have hne : j ≠ 2 * m := by omega
          simp [hne]
        · intro hnot; exact absurd (Finset.mem_range.mpr hk6) hnot
      rw [hsum_val, sub_self]
    · have hsum_val : ∑ m ∈ Finset.range 6, c m * (if j = 2 * m then ((2 * m).factorial : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun m _ => ?_
        have hne : j ≠ 2 * m := by omega
        simp [hne]
      rw [hsum_val, sub_zero]
      -- Odd derivative of even `g` at `0` is `0`
      have hev : (fun t => g (-t)) =ᶠ[𝓝 0] g :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, hr⟩) heven
      have h1 := (hev.iteratedDeriv j).eq_of_nhds
      rw [iteratedDeriv_comp_neg, neg_zero, smul_eq_mul, hk,
        show (-1 : ℝ) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; norm_num] at h1
      rw [hk]; linarith
  -- Bound `iteratedDeriv 12 R` on `[-r/2, r/2]` and apply iterated MVT
  have hR_cd12 : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv n R) (Ioo (-r) r) := by
    intro n
    induction n with
    | zero => simpa using hR_cd
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
  have hsub_Icc : Icc (-(r / 2)) (r / 2) ⊆ Ioo (-r) r := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hR_cd12 12).continuousOn.mono hsub_Icc)
  set C := max M 0
  -- Local iterated MVT on `Icc (-(r/2)) (r/2)`
  have hmvt : ∀ (m : ℕ) (h : ℝ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) h (Ioo (-r) r) →
      (∀ j < m, iteratedDeriv j h 0 = 0) →
      (∀ s ∈ Icc (-(r / 2)) (r / 2), |iteratedDeriv m h s| ≤ C) →
      ∀ t ∈ Icc (-(r / 2)) (r / 2), |h t| ≤ C * |t| ^ m := by
    intro m
    induction m with
    | zero => intro h _ _ hbd t ht; simpa using hbd t ht
    | succ m ih =>
      intro h hh h0 hbd t ht
      have hderiv_bd : ∀ s ∈ Icc (-(r / 2)) (r / 2), |deriv h s| ≤ C * |s| ^ m := by
        refine ih (deriv h) (hh.deriv_of_isOpen isOpen_Ioo (by simp)) (fun j hj => ?_) (fun s hs => ?_)
        · rw [← iteratedDeriv_succ']; exact h0 (j + 1) (Nat.succ_lt_succ hj)
        · rw [← iteratedDeriv_succ']; exact hbd s hs
      have h00 : h 0 = 0 := by simpa using h0 0 (Nat.zero_lt_succ m)
      have ht_abs : |t| ≤ r / 2 := abs_le.mpr ht
      have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := h) (f' := deriv h) (s := Icc (-|t|) |t|) (C := C * |t| ^ m)
        (fun x hx => ((hh.differentiableOn (by simp) x
          ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt
          (isOpen_Ioo.mem_nhds ⟨by linarith [hx.1], by linarith [hx.2]⟩)).hasDerivAt.hasDerivWithinAt)
        (fun x hx => by
          have hxabs : |x| ≤ |t| := abs_le.mpr hx
          rw [Real.norm_eq_abs]
          exact (hderiv_bd x (abs_le.mp (hxabs.trans ht_abs))).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hxabs m) (le_max_right M 0)))
        (convex_Icc _ _) ⟨by linarith [abs_nonneg t], abs_nonneg t⟩ (abs_le.mp le_rfl)
      rw [h00, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hlip
      simpa [pow_succ, mul_assoc] using hlip
  refine ⟨c 0, c 1, c 2, c 3, c 4, c 5, C, le_max_right M 0, fun t ht => ?_⟩
  have hP_exp : P t = c 0 + c 1 * t ^ 2 + c 2 * t ^ 4 + c 3 * t ^ 6 + c 4 * t ^ 8 + c 5 * t ^ 10 := by
    simp only [P, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero, mul_one]
  rw [← hP_exp]
  exact hmvt 12 R hR_cd hR_zero
    (fun s hs => (Real.norm_eq_abs _ ▸ hM s hs).trans (le_max_left M 0)) t ht

/-- Identify the first two even Taylor coefficients `c0, c2` from an `O(t^4)` asymptotic as `t ↓ 0`. -/
private lemma eq_of_even_asymp4 {g : ℝ → ℝ} {r c0 c2 b0 b2 C1 C2 : ℝ} (hr : 0 < r)
    (h1 : ∀ t ∈ Ioo (0 : ℝ) r, |g t - (c0 + c2 * t ^ 2)| ≤ C1 * t ^ 4)
    (h2 : ∀ t ∈ Ioo (0 : ℝ) r, |g t - (b0 + b2 * t ^ 2)| ≤ C2 * t ^ 4) :
    c0 = b0 ∧ c2 = b2 := by
  have hdiff : ∀ t ∈ Ioo (0 : ℝ) r, |(c0 - b0) + (c2 - b2) * t ^ 2| ≤ (C1 + C2) * t ^ 4 := by
    intro t ht
    have heq : (c0 - b0) + (c2 - b2) * t ^ 2 = (g t - (b0 + b2 * t ^ 2)) - (g t - (c0 + c2 * t ^ 2)) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith [h1 t ht, h2 t ht])
  have hc0 : c0 = b0 := by
    by_contra hne
    have hpos : 0 < |c0 - b0| := abs_pos.mpr (sub_ne_zero.mpr hne)
    set M := |c2 - b2| + |C1 + C2| + 1
    set t := min (r / 2) (min 1 (Real.sqrt (|c0 - b0| / (2 * M))))
    have ht0 : 0 < t := lt_min (half_pos hr) (lt_min one_pos (Real.sqrt_pos.mpr (by positivity)))
    have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
    have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have ht2 : t ^ 2 ≤ |c0 - b0| / (2 * M) := by
      have hle : t ≤ Real.sqrt (|c0 - b0| / (2 * M)) := (min_le_right _ _).trans (min_le_right _ _)
      calc t ^ 2 ≤ (Real.sqrt (|c0 - b0| / (2 * M))) ^ 2 := pow_le_pow_left₀ ht0.le hle 2
        _ = |c0 - b0| / (2 * M) := Real.sq_sqrt (by positivity)
    have ht4 : t ^ 4 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
    have hd := hdiff t ⟨ht0, htr⟩
    have htri := abs_sub_abs_le_abs_sub (c0 - b0) (-((c2 - b2) * t ^ 2))
    rw [sub_neg_eq_add, abs_neg, abs_mul, abs_of_pos (sq_pos_of_pos ht0)] at htri
    have hbd : |c0 - b0| ≤ M * t ^ 2 := by
      have h1 : (C1 + C2) * t ^ 4 ≤ |C1 + C2| * t ^ 2 := by
        calc (C1 + C2) * t ^ 4 ≤ |C1 + C2| * t ^ 4 := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg ht0.le 4)
          _ ≤ |C1 + C2| * t ^ 2 := mul_le_mul_of_nonneg_left ht4 (abs_nonneg _)
      have : M * t ^ 2 = |c2 - b2| * t ^ 2 + |C1 + C2| * t ^ 2 + t ^ 2 := by simp only [M]; ring
      linarith [sq_nonneg t]
    have hM2 : M * t ^ 2 ≤ |c0 - b0| / 2 := by
      calc M * t ^ 2 ≤ M * (|c0 - b0| / (2 * M)) := mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ = |c0 - b0| / 2 := by field_simp [show (M : ℝ) ≠ 0 by positivity]
    linarith
  refine ⟨hc0, ?_⟩
  subst hc0
  by_contra hne
  have hpos : 0 < |c2 - b2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set M := |C1 + C2| + 1
  set t := min (r / 2) (Real.sqrt (|c2 - b2| / (2 * M)))
  have ht0 : 0 < t := lt_min (half_pos hr) (Real.sqrt_pos.mpr (by positivity))
  have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have ht2 : t ^ 2 ≤ |c2 - b2| / (2 * M) := by
    have hle : t ≤ Real.sqrt (|c2 - b2| / (2 * M)) := min_le_right _ _
    calc t ^ 2 ≤ (Real.sqrt (|c2 - b2| / (2 * M))) ^ 2 := pow_le_pow_left₀ ht0.le hle 2
      _ = |c2 - b2| / (2 * M) := Real.sq_sqrt (by positivity)
  have hd := hdiff t ⟨ht0, htr⟩
  simp only [sub_self, zero_add, abs_mul, abs_of_pos (sq_pos_of_pos ht0)] at hd
  have hdiv : |c2 - b2| ≤ (C1 + C2) * t ^ 2 := by
    have : |c2 - b2| * t ^ 2 ≤ ((C1 + C2) * t ^ 2) * t ^ 2 := by linarith
    exact le_of_mul_le_mul_right this (sq_pos_of_pos ht0)
  have hM2 : M * t ^ 2 ≤ |c2 - b2| / 2 := by
    calc M * t ^ 2 ≤ M * (|c2 - b2| / (2 * M)) := mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = |c2 - b2| / 2 := by field_simp [show (M : ℝ) ≠ 0 by positivity]
  have : C1 + C2 ≤ M := by linarith [le_abs_self (C1 + C2)]
  nlinarith [sq_nonneg t]

set_option maxHeartbeats 400000 in
/-- Laurent expansion of `F_CE(t) = α_osc |H_CE(it)| / m(t)` with exact leading coefficients
`b_{-4} = 12 α_osc / π²` and `b_{-2} = -(3/10) α_osc = c_{-1}(H_CE) + (7/20) α_osc`. -/
lemma laurent_FCE :
    let F : ℝ → ℝ := fun t => uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t
    ContinuousOn F (Ioi 0) ∧
    ∃ b0 b2 b4 b6 C_R : ℝ, 0 ≤ C_R ∧
      (∀ t ∈ Ioc (0 : ℝ) 1,
        |F t - (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + (-(3 / 10) * uctAlphaOsc) / t ^ 2 +
          b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 8) ∧
      (∀ t : ℝ, 1 ≤ t →
        |F t - (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + (-(3 / 10) * uctAlphaOsc) / t ^ 2 +
          b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 6) := by
  let F : ℝ → ℝ := fun t => uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t
  have hF_eq : ∀ t : ℝ, 0 < t → F t = uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2)) / uctM t := by
    intro t ht; simp only [F, norm_uctHCE_imag ht]
  have hF_cont : ContinuousOn F (Ioi 0) := by
    have h1 : ContinuousOn (fun t : ℝ => uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2)) / uctM t) (Ioi 0) := by
      refine (continuousOn_const.mul (continuousOn_const.div
        (continuousOn_const.mul ((contDiff_sinh_real.continuous.comp
          ((continuous_const.mul continuous_id).div_const 2)).continuousOn.pow 2))
        fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2
          (sinh_pos_of_pos (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne'))).div ?_
        fun t ht => (uctM_pos ht).ne'
      unfold uctM ceEll
      refine (Real.continuousOn_log.comp ?_ fun t ht => ?_)
      · have hx : ContinuousOn (fun t : ℝ => π * t / 2) (Ioi 0) :=
          (continuousOn_const.mul continuousOn_id).div_const 2
        refine hx.div ?_ fun t ht => ?_
        · have htanh : Continuous (fun s : ℝ => Real.tanh s) := by
            have : Real.tanh = fun s => Real.sinh s / Real.cosh s := funext Real.tanh_eq_sinh_div_cosh
            rw [this]
            exact contDiff_sinh_real.continuous.div
              (by
                have : Real.cosh = fun s => (Real.exp s + Real.exp (-s)) / 2 := funext Real.cosh_eq
                rw [this]; fun_prop)
              fun s => (zero_lt_one.trans_le (one_le_cosh_real s)).ne'
          exact htanh.continuousOn.comp hx (mapsTo_univ _ _)
        · rw [Real.tanh_eq_sinh_div_cosh]
          exact div_ne_zero (sinh_pos_of_pos (by have : 0 < t := ht; have := Real.pi_pos; positivity)).ne'
            (zero_lt_one.trans_le (one_le_cosh_real _)).ne'
      · have hx : 0 < π * t / 2 := by have : 0 < t := ht; positivity
        rw [Real.tanh_eq_sinh_div_cosh]
        exact (div_pos hx (div_pos (sinh_pos_of_pos hx) (by linarith [one_le_cosh_real (π * t / 2)]))).ne'
    exact h1.congr fun t ht => hF_eq t ht
  refine ⟨hF_cont, ?_⟩
  -- Holomorphic `g_CE(z) = α_osc * (4/π²) / (sinhQ(πz/2)² * ellQ(πz/2))` on a small disc
  have hQ_ne0 : ellQ 0 ≠ 0 := by rw [ellQ_zero]; norm_num
  have hQ_cont : ContinuousAt ellQ 0 :=
    (differentiableOn_ellQ.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).continuousAt
  have hev_ne : ∀ᶠ w in 𝓝 (0 : ℂ), ellQ w ≠ 0 := hQ_cont.eventually (isOpen_ne.mem_nhds hQ_ne0)
  rw [Metric.eventually_nhds_iff] at hev_ne
  obtain ⟨δ, hδ, hδ_ne⟩ := hev_ne
  set r : ℝ := min (1 / 8) (min (δ / 4) (1 / 4))
  have hr : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (by norm_num))
  let gC : ℂ → ℂ := fun z =>
    (uctAlphaOsc : ℂ) * (4 / (π : ℂ) ^ 2) /
      (CtOuter.sinhQ ((π : ℂ) * z / 2) ^ 2 * ellQ ((π : ℂ) * z / 2))
  have hgC_diff : DifferentiableOn ℂ gC (Metric.ball (0 : ℂ) r) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have hw_lt : ‖(π : ℂ) * z / 2‖ < min (1 / 2) δ := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_ofNat]
      have hpi4 : π < 4 := Real.pi_lt_four
      have hr1 : r ≤ 1 / 8 := min_le_left _ _
      have hr2 : r ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
      rw [lt_min_iff]; constructor <;> nlinarith [norm_nonneg z]
    have hQ1 : CtOuter.sinhQ ((π : ℂ) * z / 2) ≠ 0 :=
      CtOuter.sinhQ_ne_zero (by linarith [hw_lt.trans_le (min_le_left _ _), Real.pi_gt_three])
    have hQ2 : ellQ ((π : ℂ) * z / 2) ≠ 0 :=
      hδ_ne (by rw [dist_zero_right]; exact hw_lt.trans_le (min_le_right _ _))
    have hlin : DifferentiableAt ℂ (fun u : ℂ => (π : ℂ) * u / 2) z := by fun_prop
    have hd1 : DifferentiableAt ℂ (fun u : ℂ => CtOuter.sinhQ ((π : ℂ) * u / 2) ^ 2) z :=
      ((CtOuter.differentiable_sinhQ _).comp z hlin).pow 2
    have hd2 : DifferentiableAt ℂ (fun u : ℂ => ellQ ((π : ℂ) * u / 2)) z :=
      (differentiableOn_ellQ.differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hw_lt.trans_le (min_le_left _ _))))).comp z hlin
    exact ((differentiableAt_const _).div (hd1.mul hd2) (mul_ne_zero (pow_ne_zero 2 hQ1) hQ2)).differentiableWithinAt
  let g : ℝ → ℝ := fun t => (gC (t : ℂ)).re
  have hg_cd : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioo (-r) r) := by
    have h1 : ContDiffOn ℂ (⊤ : ℕ∞) gC (Metric.ball 0 r) :=
      (hgC_diff.contDiffOn Metric.isOpen_ball).of_le le_top
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => gC (t : ℂ)) (Ioo (-r) r) :=
      (h1.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.of_le le_top).contDiffOn fun t ht => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ht
    exact (Complex.reCLM.contDiff.of_le le_top).comp_contDiffOn h2
  have hg_even : ∀ t ∈ Ioo (-r) r, g (-t) = g t := by
    intro t _
    simp only [g, gC, Complex.ofReal_neg]
    have hsq_even : ∀ w : ℂ, CtOuter.sinhQ (-w) = CtOuter.sinhQ w := fun w => by
      unfold CtOuter.sinhQ; exact tsum_congr fun n => by rw [even_two_mul n |>.neg_pow]
    have hell_even : ∀ w : ℂ, ellQ (-w) = ellQ w := fun w => by
      by_cases hw : w = 0
      · simp [hw]
      · rw [ellQ_eq_div (neg_ne_zero.mpr hw), ellQ_eq_div hw, neg_sq]
        unfold ellC; rw [Complex.cosh_neg, hsq_even]
    have harg : (π : ℂ) * (-(t : ℂ)) / 2 = -((π : ℂ) * (t : ℂ) / 2) := by ring
    rw [harg, hsq_even, hell_even]
  have hg_eq_F : ∀ t ∈ Ioo (0 : ℝ) r, g t = t ^ 4 * F t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hx0 : 0 < π * t / 2 := by positivity
    have hshQ := CtOuter.sinhQ_ofReal hx0.ne'
    have hell := ellQ_eq_div (Complex.ofReal_ne_zero.mpr hx0.ne')
    rw [ellC_ofReal hx0] at hell
    simp only [g, gC]
    have harg : (π : ℂ) * (t : ℂ) / 2 = ((π * t / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [harg, hshQ, hell]
    have hval : (uctAlphaOsc : ℂ) * (4 / (π : ℂ) ^ 2) /
        (((Real.sinh (π * t / 2) / (π * t / 2) : ℝ) : ℂ) ^ 2 *
          (((ceEll (π * t / 2) : ℝ) : ℂ) / ((π * t / 2 : ℝ) : ℂ) ^ 2)) =
        (((t ^ 4 * (uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2)) / uctM t) : ℝ)) : ℂ) := by
      unfold uctM
      push_cast
      have h1 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have h2 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      have h3 : (Real.sinh (π * t / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sinh_pos_of_pos hx0).ne'
      have h4 : (ceEll (π * t / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ceEll_pos hx0).ne'
      field_simp [h1, h2, h3, h4]; ring
    rw [hval, Complex.ofReal_re, hF_eq t ht0]
  -- Apply `even_taylor12` to `g`
  obtain ⟨c0, c2, c4, c6, c8, c10, C12, hC12, htay⟩ := even_taylor12 hr hg_cd hg_even
  -- Identify `c0 = 12 α_osc / π²` and `c2 = -(3/10) α_osc` via `eq_of_even_asymp4`
  have hasymp_g : ∃ C2 ≥ 0, ∀ t ∈ Ioo (0 : ℝ) (r / 2),
      |g t - (12 * uctAlphaOsc / π ^ 2 + (-(3 / 10) * uctAlphaOsc) * t ^ 2)| ≤ C2 * t ^ 4 := by
    have hosc_nn : 0 ≤ uctAlphaOsc := by
      rw [uctAlphaOsc_eq]; unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    refine ⟨10000 * uctAlphaOsc, by positivity, fun t ht => ?_⟩
    rw [hg_eq_F t ⟨ht.1, lt_trans ht.2 (half_lt_self hr)⟩, hF_eq t ht.1]
    set x : ℝ := π * t / 2
    have hx0 : 0 < x := by have := ht.1; have := Real.pi_pos; positivity
    have hx12 : x ≤ 1 / 2 := by
      have hpi4 : π < 4 := Real.pi_lt_four
      have hr1 : r ≤ 1 / 8 := min_le_left _ _
      have ht_lt : t < 1 / 8 := lt_of_lt_of_le (lt_trans ht.2 (half_lt_self hr)) hr1
      simp only [x]; nlinarith [ht.1]
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have hx4 : x ^ 4 ≤ 1 / 16 := by nlinarith
    have hsh := sinh_taylor5_bound hx0.le (by linarith)
    have hce := ceEll_taylor4 hx0 hx12
    -- `t^4 * F t = α_osc * (4/π²) / ((sinh x / x)² * (ceEll x / x²))`
    have hden_eq : t ^ 4 * (uctAlphaOsc * (π ^ 2 / (4 * Real.sinh x ^ 2)) / ceEll x) =
        uctAlphaOsc * (4 / π ^ 2) / ((Real.sinh x / x) ^ 2 * (ceEll x / x ^ 2)) := by
      simp only [x]
      have h1 : π ≠ 0 := Real.pi_pos.ne'
      have h2 : t ≠ 0 := ht.1.ne'
      have h3 : Real.sinh (π * t / 2) ≠ 0 := (sinh_pos_of_pos hx0).ne'
      have h4 : ceEll (π * t / 2) ≠ 0 := (ceEll_pos hx0).ne'
      field_simp [h1, h2, h3, h4]; ring
    have hden_pos : 1 / 6 ≤ (Real.sinh x / x) ^ 2 * (ceEll x / x ^ 2) := by
      have h1 : 1 ≤ Real.sinh x / x := (one_le_div hx0).mpr (self_le_sinh_nonneg hx0.le)
      have h2 : 1 / 6 ≤ ceEll x / x ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hx0)]
        have hge : x ^ 2 / 3 - 2 / 15 * x ^ 4 ≤ ceEll x := by
          have hth := ceHth_le_of_le_one hx0 (by linarith : x ≤ 1)
          have e : ceEll x = x ^ 2 / 3 - ceHth x := by
            unfold ceEll ceHth
            rw [show x / Real.tanh x = (Real.tanh x / x)⁻¹ by rw [inv_div], Real.log_inv]; ring
          linarith
        nlinarith [sq_nonneg x]
      nlinarith
    -- `(sinh x / x)^2 * (ceEll x / x^2) = 1/3 + (1/30) x^2 + O(x^4)`
    have hsh_q : |Real.sinh x / x - (1 + x ^ 2 / 6)| ≤ x ^ 4 := by
      have h1 : |Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)| ≤ x ^ 6 := by
        rw [show Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120) =
            (Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)) / x by field_simp [hx0.ne'],
          abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
        linarith [hsh]
      have htri := abs_add_le (Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)) (x ^ 4 / 120)
      have hrew : Real.sinh x / x - (1 + x ^ 2 / 6) = (Real.sinh x / x - (1 + x ^ 2 / 6 + x ^ 4 / 120)) + x ^ 4 / 120 := by ring
      rw [hrew]
      rw [abs_of_nonneg (by positivity : 0 ≤ x ^ 4 / 120)] at htri
      have hx6 : x ^ 6 ≤ x ^ 4 / 4 := by nlinarith [pow_nonneg hx0.le 4]
      linarith [pow_nonneg hx0.le 4]
    have hsh_sq : |(Real.sinh x / x) ^ 2 - (1 + x ^ 2 / 3)| ≤ 4 * x ^ 4 := by
      have h1 : |Real.sinh x / x + (1 + x ^ 2 / 6)| ≤ 3 := by
        have := abs_le.mp hsh_q
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, pow_nonneg hx0.le 4]
      have heq : (Real.sinh x / x) ^ 2 - (1 + x ^ 2 / 3) =
          (Real.sinh x / x - (1 + x ^ 2 / 6)) * (Real.sinh x / x + (1 + x ^ 2 / 6)) + x ^ 4 / 36 := by ring
      rw [heq]
      have htri := abs_add_le ((Real.sinh x / x - (1 + x ^ 2 / 6)) * (Real.sinh x / x + (1 + x ^ 2 / 6))) (x ^ 4 / 36)
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 4 / 36)] at htri
      have := mul_le_mul hsh_q h1 (abs_nonneg _) (pow_nonneg hx0.le 4)
      linarith [pow_nonneg hx0.le 4]
    have hce_q : |ceEll x / x ^ 2 - (1 / 3 - 7 / 90 * x ^ 2)| ≤ 20 * x ^ 4 := by
      rw [show ceEll x / x ^ 2 - (1 / 3 - 7 / 90 * x ^ 2) =
          (ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2 by field_simp [hx0.ne'],
        abs_div, abs_of_pos (sq_pos_of_pos hx0), div_le_iff₀ (sq_pos_of_pos hx0)]
      nlinarith [hce]
    have hprod_q : |(Real.sinh x / x) ^ 2 * (ceEll x / x ^ 2) - (1 / 3 + 1 / 30 * x ^ 2)| ≤ 40 * x ^ 4 := by
      have heq : (Real.sinh x / x) ^ 2 * (ceEll x / x ^ 2) - (1 / 3 + 1 / 30 * x ^ 2) =
          ((Real.sinh x / x) ^ 2 - (1 + x ^ 2 / 3)) * (ceEll x / x ^ 2) +
          (1 + x ^ 2 / 3) * (ceEll x / x ^ 2 - (1 / 3 - 7 / 90 * x ^ 2)) - 7 / 270 * x ^ 4 := by ring
      rw [heq]
      have hce_le1 : |ceEll x / x ^ 2| ≤ 1 := by
        have hpos : 0 < ceEll x / x ^ 2 := div_pos (ceEll_pos hx0) (sq_pos_of_pos hx0)
        have hlt : ceEll x / x ^ 2 < 1 / 3 := (div_lt_iff₀ (sq_pos_of_pos hx0)).mpr (by linarith [ceEll_lt_sq_div_three hx0])
        rw [abs_of_pos hpos]; linarith
      have h1x : |1 + x ^ 2 / 3| ≤ 3 / 2 := by
        rw [abs_of_nonneg (by positivity)]; nlinarith
      have h1 := mul_le_mul hsh_sq hce_le1 (abs_nonneg _) (by positivity)
      have h2 := mul_le_mul h1x hce_q (abs_nonneg _) (by positivity)
      have htri1 := abs_sub (((Real.sinh x / x) ^ 2 - (1 + x ^ 2 / 3)) * (ceEll x / x ^ 2) +
        (1 + x ^ 2 / 3) * (ceEll x / x ^ 2 - (1 / 3 - 7 / 90 * x ^ 2))) (7 / 270 * x ^ 4)
      have htri2 := abs_add_le (((Real.sinh x / x) ^ 2 - (1 + x ^ 2 / 3)) * (ceEll x / x ^ 2))
        ((1 + x ^ 2 / 3) * (ceEll x / x ^ 2 - (1 / 3 - 7 / 90 * x ^ 2)))
      rw [abs_mul, abs_mul] at htri2
      rw [abs_of_nonneg (by positivity : 0 ≤ 7 / 270 * x ^ 4)] at htri1
      linarith [pow_nonneg hx0.le 4]
    -- Now compare `4/(π² D) - (12/π² - (3/10) t²) = (4/π²) (1 - (3 - (3/10) x²) D) / D`
    rw [show uctM t = ceEll x from rfl, hden_eq]
    set D := (Real.sinh x / x) ^ 2 * (ceEll x / x ^ 2)
    have hD_ne : D ≠ 0 := (by linarith : 0 < D).ne'
    have hrewrite : uctAlphaOsc * (4 / π ^ 2) / D - (12 * uctAlphaOsc / π ^ 2 + -(3 / 10) * uctAlphaOsc * t ^ 2) =
        uctAlphaOsc * (4 / π ^ 2) * (1 - (3 - 3 / 10 * x ^ 2) * D) / D := by
      simp only [x]; field_simp [Real.pi_pos.ne', hD_ne]; ring
    rw [hrewrite, abs_div, abs_mul, abs_mul, abs_of_nonneg hosc_nn,
      abs_of_pos (by positivity : 0 < 4 / π ^ 2), abs_of_pos (by linarith : 0 < D)]
    have hnum_le : |1 - (3 - 3 / 10 * x ^ 2) * D| ≤ 130 * x ^ 4 := by
      have heq : 1 - (3 - 3 / 10 * x ^ 2) * D =
          -(3 - 3 / 10 * x ^ 2) * (D - (1 / 3 + 1 / 30 * x ^ 2)) + 1 / 100 * x ^ 4 := by ring
      rw [heq]
      have h3x : |-(3 - 3 / 10 * x ^ 2)| ≤ 3 := by
        rw [abs_neg, abs_of_nonneg (by nlinarith)]; nlinarith [sq_nonneg x]
      have htri := abs_add_le (-(3 - 3 / 10 * x ^ 2) * (D - (1 / 3 + 1 / 30 * x ^ 2))) (1 / 100 * x ^ 4)
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / 100 * x ^ 4)] at htri
      have hmul := mul_le_mul h3x hprod_q (abs_nonneg _) (by norm_num)
      have hx4nn : 0 ≤ x ^ 4 := pow_nonneg hx0.le 4
      linarith
    have hpi4 : π < 4 := Real.pi_lt_four
    have hpi2 : π ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
    calc uctAlphaOsc * (4 / π ^ 2) * |1 - (3 - 3 / 10 * x ^ 2) * D| / D
        ≤ uctAlphaOsc * (4 / π ^ 2) * (130 * x ^ 4) / (1 / 6) :=
          div_le_div₀ (by positivity) (by gcongr) (by norm_num) hden_pos
      _ = 195 * π ^ 2 * (uctAlphaOsc * t ^ 4) := by simp only [x]; field_simp [Real.pi_pos.ne']; ring
      _ ≤ 10000 * (uctAlphaOsc * t ^ 4) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 10000 * uctAlphaOsc * t ^ 4 := by ring
  obtain ⟨C2, hC2, h2⟩ := hasymp_g
  have h1_trunc : ∀ t ∈ Ioo (0 : ℝ) (r / 2), |g t - (c0 + c2 * t ^ 2)| ≤
      (|c4| + |c6| + |c8| + |c10| + C12) * t ^ 4 := by
    intro t ht
    have ht1 : t ≤ 1 := by linarith [ht.2, show r ≤ 1 / 8 from min_le_left _ _]
    have hmem : t ∈ Icc (-(r / 2)) (r / 2) := ⟨by linarith [ht.1], ht.2.le⟩
    have h12 := htay t hmem
    rw [abs_of_pos ht.1] at h12
    have hsplit : g t - (c0 + c2 * t ^ 2) =
        (g t - (c0 + c2 * t ^ 2 + c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10)) +
        (c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10) := by ring
    rw [hsplit]
    have ht12 : t ^ 12 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have ht10 : t ^ 10 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have ht8 : t ^ 8 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have ht6 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have htri := abs_add_le (g t - (c0 + c2 * t ^ 2 + c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10))
      (c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10)
    have hpoly : |c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10| ≤
        (|c4| + |c6| + |c8| + |c10|) * t ^ 4 := by
      have ha1 := abs_add_le (c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8) (c10 * t ^ 10)
      have ha2 := abs_add_le (c4 * t ^ 4 + c6 * t ^ 6) (c8 * t ^ 8)
      have ha3 := abs_add_le (c4 * t ^ 4) (c6 * t ^ 6)
      simp only [abs_mul, abs_of_pos (pow_pos ht.1 _)] at ha1 ha2 ha3
      nlinarith [abs_nonneg c4, abs_nonneg c6, abs_nonneg c8, abs_nonneg c10]
    nlinarith [h12, hC12]
  obtain ⟨hc0, hc2⟩ := eq_of_even_asymp4 (half_pos hr) h1_trunc h2
  subst hc0; subst hc2
  -- Now extend the remainder bound from `(0, r/2]` to `(0, 1]` and `[1, ∞)`!
  set R : ℝ → ℝ := fun t => F t - (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + (-(3 / 10) * uctAlphaOsc) / t ^ 2 +
    c4 + c6 * t ^ 2 + c8 * t ^ 4 + c10 * t ^ 6)
  have hR_cont : ContinuousOn R (Ioi 0) :=
    hF_cont.sub ((((((continuousOn_const.div (continuousOn_id.pow 4) fun t ht => pow_ne_zero 4 (mem_Ioi.mp ht).ne').add
      (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (mem_Ioi.mp ht).ne')).add
      continuousOn_const).add (continuousOn_const.mul (continuousOn_id.pow 2))).add
      (continuousOn_const.mul (continuousOn_id.pow 4))).add
      (continuousOn_const.mul (continuousOn_id.pow 6)))
  obtain ⟨M_mid, hM_mid⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hR_cont.mono (show Icc (r / 2) 1 ⊆ Ioi (0 : ℝ) from fun t ht => lt_of_lt_of_le (half_pos hr) ht.1))
  have hF_large_bd : ∀ t : ℝ, 1 ≤ t → |F t| ≤ uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π / 2) ^ 2)) / uctM 1 := by
    intro t ht
    rw [hF_eq t (zero_lt_one.trans_le ht)]
    have hosc_nn : 0 ≤ uctAlphaOsc := by
      rw [uctAlphaOsc_eq]; unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    have hsh_le : Real.sinh (π / 2) ≤ Real.sinh (π * t / 2) := by
      have hmono : Monotone Real.sinh := monotone_of_deriv_nonneg
        (contDiff_sinh_real.differentiable (by simp))
        fun s => by rw [(hasDerivAt_sinh_real s).deriv]; linarith [one_le_cosh_real s]
      exact hmono (by nlinarith [Real.pi_pos])
    have hm_le : uctM 1 ≤ uctM t := uctM_strictMonoOn.monotoneOn zero_lt_one (zero_lt_one.trans_le ht) ht
    rw [abs_of_nonneg (by
      have := uctM_pos (zero_lt_one.trans_le ht)
      positivity)]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
        (by have := sinh_pos_of_pos (show 0 < π / 2 by positivity); positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sinh_pos_of_pos (by positivity)).le hsh_le 2) (by norm_num)))
        hosc_nn)
      (uctM_pos one_pos) hm_le
  set B_inf : ℝ := uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π / 2) ^ 2)) / uctM 1 +
    |12 * uctAlphaOsc / π ^ 2| + |-(3 / 10) * uctAlphaOsc| + |c4| + |c6| + |c8| + |c10|
  set C_R : ℝ := max (max C12 (max M_mid 0 / (r / 2) ^ 8)) (max B_inf 0)
  refine ⟨c4, c6, c8, c10, C_R, le_trans (le_max_right B_inf 0) (le_max_right _ _), ?_, ?_⟩
  · intro t ht
    by_cases hsm : t ≤ r / 2
    · have hmem : t ∈ Icc (-(r / 2)) (r / 2) := ⟨by linarith [ht.1], hsm⟩
      have h12 := htay t hmem
      rw [hg_eq_F t ⟨ht.1, lt_of_le_of_lt hsm (half_lt_self hr)⟩, abs_of_pos ht.1] at h12
      have hdiv : |R t| = |t ^ 4 * F t - (12 * uctAlphaOsc / π ^ 2 + -(3 / 10) * uctAlphaOsc * t ^ 2 +
          c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10)| / t ^ 4 := by
        rw [← abs_of_pos (pow_pos ht.1 4), ← abs_div]
        congr 1
        have hpos4 : |t ^ 4| = t ^ 4 := abs_of_pos (pow_pos ht.1 4)
        simp only [R, hpos4]; field_simp [ht.1.ne']
      rw [hdiv, div_le_iff₀ (pow_pos ht.1 4)]
      calc |t ^ 4 * F t - (12 * uctAlphaOsc / π ^ 2 + -(3 / 10) * uctAlphaOsc * t ^ 2 +
              c4 * t ^ 4 + c6 * t ^ 6 + c8 * t ^ 8 + c10 * t ^ 10)|
          ≤ C12 * t ^ 12 := h12
        _ ≤ C_R * t ^ 12 := mul_le_mul_of_nonneg_right
            ((le_max_left _ _).trans (le_max_left _ _)) (pow_nonneg ht.1.le 12)
        _ = C_R * t ^ 8 * t ^ 4 := by ring
    · have hge : r / 2 ≤ t := le_of_not_ge hsm
      have hbd : |R t| ≤ max M_mid 0 :=
        (Real.norm_eq_abs _ ▸ hM_mid t ⟨hge, ht.2⟩).trans (le_max_left _ _)
      have hpow : (r / 2) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (half_pos hr).le hge 8
      calc |R t| ≤ max M_mid 0 := hbd
        _ = (max M_mid 0 / (r / 2) ^ 8) * (r / 2) ^ 8 := by field_simp [(pow_pos (half_pos hr) 8).ne']
        _ ≤ C_R * t ^ 8 := mul_le_mul ((le_max_right _ _).trans (le_max_left _ _)) hpow
            (pow_nonneg (half_pos hr).le 8) (le_trans (le_max_right B_inf 0) (le_max_right _ _))
  · intro t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht
    have ht4 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
    have ht2 : t ^ 2 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
    have hinv4 : 1 / t ^ 4 ≤ t ^ 6 := (div_le_one (pow_pos ht0 4) |>.mpr (one_le_pow₀ ht)).trans ht6
    have hinv2 : 1 / t ^ 2 ≤ t ^ 6 := (div_le_one (pow_pos ht0 2) |>.mpr (one_le_pow₀ ht)).trans ht6
    have htri : |R t| ≤ |F t| + |12 * uctAlphaOsc / π ^ 2| * (1 / t ^ 4) +
        |-(3 / 10) * uctAlphaOsc| * (1 / t ^ 2) + |c4| + |c6| * t ^ 2 + |c8| * t ^ 4 + |c10| * t ^ 6 := by
      simp only [R]
      have h1 := abs_sub (F t) (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2 +
        c4 + c6 * t ^ 2 + c8 * t ^ 4 + c10 * t ^ 6)
      have h2 := abs_add_le (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2 +
        c4 + c6 * t ^ 2 + c8 * t ^ 4) (c10 * t ^ 6)
      have h3 := abs_add_le (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2 +
        c4 + c6 * t ^ 2) (c8 * t ^ 4)
      have h4 := abs_add_le (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2 + c4) (c6 * t ^ 2)
      have h5 := abs_add_le (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2) c4
      have h6 := abs_add_le (12 * uctAlphaOsc / π ^ 2 / t ^ 4) (-(3 / 10) * uctAlphaOsc / t ^ 2)
      have ha1 : |12 * uctAlphaOsc / π ^ 2 / t ^ 4| = |12 * uctAlphaOsc / π ^ 2| * (1 / t ^ 4) := by
        rw [abs_div, abs_of_pos (pow_pos ht0 4)]; ring
      have ha2 : |-(3 / 10) * uctAlphaOsc / t ^ 2| = |-(3 / 10) * uctAlphaOsc| * (1 / t ^ 2) := by
        rw [abs_div, abs_of_pos (pow_pos ht0 2)]; ring
      have ha3 : |c6 * t ^ 2| = |c6| * t ^ 2 := by rw [abs_mul, abs_of_pos (pow_pos ht0 2)]
      have ha4 : |c8 * t ^ 4| = |c8| * t ^ 4 := by rw [abs_mul, abs_of_pos (pow_pos ht0 4)]
      have ha5 : |c10 * t ^ 6| = |c10| * t ^ 6 := by rw [abs_mul, abs_of_pos (pow_pos ht0 6)]
      linarith
    have hFbd := hF_large_bd t ht
    have hB_le : |R t| ≤ B_inf * t ^ 6 := by
      simp only [B_inf]
      nlinarith [hFbd, abs_nonneg (12 * uctAlphaOsc / π ^ 2), abs_nonneg (-(3 / 10) * uctAlphaOsc),
        abs_nonneg c4, abs_nonneg c6, abs_nonneg c8, abs_nonneg c10,
        show 0 ≤ uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π / 2) ^ 2)) / uctM 1 by
          have : 0 ≤ uctAlphaOsc := by
            rw [uctAlphaOsc_eq]; unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
          have := uctM_pos one_pos; positivity]
    exact hB_le.trans (mul_le_mul_of_nonneg_right ((le_max_left B_inf 0).trans (le_max_right _ _)) (pow_nonneg ht0.le 6))

set_option maxHeartbeats 400000 in
/-- Laurent expansion of `F_*(t) = α_osc |H_*(it)| / m(t)` with exact leading coefficients
`b_{-4} = 12 α_osc / π²` and `b_{-2} = (27/10) α_osc = c_{-1}(H_*) + (7/20) α_osc`.
Follows immediately from `laurent_FCE` since `|H_*(it)| = |H_CE(it)| + π² / (4 cosh²(πt/2))`! -/
lemma laurent_Fstar :
    let F : ℝ → ℝ := fun t => uctAlphaOsc * ‖uctHstar ((t : ℂ) * Complex.I)‖ / uctM t
    ContinuousOn F (Ioi 0) ∧
    ∃ b0 b2 b4 b6 C_R : ℝ, 0 ≤ C_R ∧
      (∀ t ∈ Ioc (0 : ℝ) 1,
        |F t - (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + ((27 / 10) * uctAlphaOsc) / t ^ 2 +
          b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 8) ∧
      (∀ t : ℝ, 1 ≤ t →
        |F t - (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + ((27 / 10) * uctAlphaOsc) / t ^ 2 +
          b0 + b2 * t ^ 2 + b4 * t ^ 4 + b6 * t ^ 6)| ≤ C_R * t ^ 6) := by
  obtain ⟨hFCE_cont, b0_ce, b2_ce, b4_ce, b6_ce, C_ce, hC_ce, hce_sm, hce_lg⟩ := laurent_FCE
  -- Difference `ΔF(t) = F_*(t) - F_CE(t) = α_osc * π² / (4 cosh²(πt/2) * m(t))`
  let ΔF : ℝ → ℝ := fun t => uctAlphaOsc * (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) / uctM t
  have hsplit_F : ∀ t : ℝ, 0 < t →
      uctAlphaOsc * ‖uctHstar ((t : ℂ) * Complex.I)‖ / uctM t =
        uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t + ΔF t := by
    intro t ht
    have hstar : ‖uctHstar ((t : ℂ) * Complex.I)‖ =
        ‖uctHCE ((t : ℂ) * Complex.I)‖ + π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) := by
      have h1 := uct_H_split (ζ := (t : ℂ) * Complex.I) fun n h => by
        have hre := congrArg Complex.re h
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
          Complex.I_im, mul_one, sub_self, Complex.intCast_re] at hre
        have him := congrArg Complex.im h
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
          Complex.I_re, mul_zero, add_zero, Complex.intCast_im] at him
        linarith
      have h2 := uctHCE_imag t
      have h3 : 1 - (t : ℂ) * Complex.I = 1 + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h1, h2, h3, uctHCE_one_add_imag (-t), show π * (-t) / 2 = -(π * t / 2) by ring, Real.cosh_neg]
      rw [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have hp1 : 0 < π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) := by
        have := sinh_pos_of_pos (show 0 < π * t / 2 by positivity); positivity
      have hp2 : 0 < π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) := by
        have := one_le_cosh_real (π * t / 2); positivity
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
    rw [hstar]; simp only [ΔF]; ring
  have hΔF_cont : ContinuousOn ΔF (Ioi 0) := by
    have hcosh_cont : Continuous (fun s : ℝ => Real.cosh s) := by
      have : Real.cosh = fun s => (Real.exp s + Real.exp (-s)) / 2 := funext Real.cosh_eq
      rw [this]; fun_prop
    refine (continuousOn_const.mul (continuousOn_const.div
      (continuousOn_const.mul ((hcosh_cont.comp ((continuous_const.mul continuous_id).div_const 2)).continuousOn.pow 2))
      fun t _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (zero_lt_one.trans_le (one_le_cosh_real _)).ne'))).div ?_
      fun t ht => (uctM_pos ht).ne'
    have hF_m : ContinuousOn uctM (Ioi 0) := by
      unfold uctM ceEll
      refine Real.continuousOn_log.comp ?_ fun t ht => ?_
      · have hx : ContinuousOn (fun t : ℝ => π * t / 2) (Ioi 0) :=
          (continuousOn_const.mul continuousOn_id).div_const 2
        refine hx.div ?_ fun t ht => ?_
        · have htanh : Continuous Real.tanh := by
            have : Real.tanh = fun s => Real.sinh s / Real.cosh s := funext Real.tanh_eq_sinh_div_cosh
            rw [this]; exact contDiff_sinh_real.continuous.div hcosh_cont fun s => (zero_lt_one.trans_le (one_le_cosh_real s)).ne'
          exact htanh.continuousOn.comp hx (mapsTo_univ _ _)
        · rw [Real.tanh_eq_sinh_div_cosh]
          exact div_ne_zero (sinh_pos_of_pos (by have : 0 < t := ht; have := Real.pi_pos; positivity)).ne'
            (zero_lt_one.trans_le (one_le_cosh_real _)).ne'
      · have hx : 0 < π * t / 2 := by have : 0 < t := ht; positivity
        rw [Real.tanh_eq_sinh_div_cosh]
        exact (div_pos hx (div_pos (sinh_pos_of_pos hx) (by linarith [one_le_cosh_real (π * t / 2)]))).ne'
    exact hF_m
  refine ⟨(hFCE_cont.add hΔF_cont).congr fun t ht => hsplit_F t ht, ?_⟩
  -- Holomorphic `h_Δ(z) = α_osc * z^2 / (cosh(πz/2)^2 * ellQ(πz/2))` = `t^4 ΔF(t)` on `ball 0 r`
  have hQ_ne0 : ellQ 0 ≠ 0 := by rw [ellQ_zero]; norm_num
  have hQ_cont : ContinuousAt ellQ 0 :=
    (differentiableOn_ellQ.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).continuousAt
  have hev_ne : ∀ᶠ w in 𝓝 (0 : ℂ), ellQ w ≠ 0 ∧ Complex.cosh w ≠ 0 :=
    (hQ_cont.eventually (isOpen_ne.mem_nhds hQ_ne0)).and
      (Complex.continuous_cosh.continuousAt.eventually (isOpen_ne.mem_nhds (by simp)))
  rw [Metric.eventually_nhds_iff] at hev_ne
  obtain ⟨δ, hδ, hδ_ne⟩ := hev_ne
  set r : ℝ := min (1 / 8) (min (δ / 4) (1 / 4))
  have hr : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (by norm_num))
  let hC : ℂ → ℂ := fun z =>
    (uctAlphaOsc : ℂ) * z ^ 2 / (Complex.cosh ((π : ℂ) * z / 2) ^ 2 * ellQ ((π : ℂ) * z / 2))
  have hhC_diff : DifferentiableOn ℂ hC (Metric.ball (0 : ℂ) r) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have hw_lt : ‖(π : ℂ) * z / 2‖ < min (1 / 2) δ := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
      have hpi4 : π < 4 := Real.pi_lt_four
      have hr1 : r ≤ 1 / 8 := min_le_left _ _
      have hr2 : r ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
      rw [lt_min_iff]; constructor <;> nlinarith [norm_nonneg z]
    obtain ⟨hQ2, hch2⟩ := hδ_ne (y := (π : ℂ) * z / 2) (by rw [dist_zero_right]; exact hw_lt.trans_le (min_le_right _ _))
    have hlin : DifferentiableAt ℂ (fun u : ℂ => (π : ℂ) * u / 2) z := by fun_prop
    have hd1 : DifferentiableAt ℂ (fun u : ℂ => Complex.cosh ((π : ℂ) * u / 2) ^ 2) z :=
      ((Complex.differentiable_cosh _).comp z hlin).pow 2
    have hd2 : DifferentiableAt ℂ (fun u : ℂ => ellQ ((π : ℂ) * u / 2)) z :=
      (differentiableOn_ellQ.differentiableAt
        (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hw_lt.trans_le (min_le_left _ _))))).comp z hlin
    exact (((differentiableAt_const _).mul (differentiableAt_id.pow 2)).div
      (hd1.mul hd2) (mul_ne_zero (pow_ne_zero 2 hch2) hQ2)).differentiableWithinAt
  let hR : ℝ → ℝ := fun t => (hC (t : ℂ)).re
  have hhR_cd : ContDiffOn ℝ (⊤ : ℕ∞) hR (Ioo (-r) r) := by
    have h1 : ContDiffOn ℂ (⊤ : ℕ∞) hC (Metric.ball 0 r) :=
      (hhC_diff.contDiffOn Metric.isOpen_ball).of_le le_top
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => hC (t : ℂ)) (Ioo (-r) r) :=
      (h1.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.of_le le_top).contDiffOn fun t ht => by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ht
    exact (Complex.reCLM.contDiff.of_le le_top).comp_contDiffOn h2
  have hhR_even : ∀ t ∈ Ioo (-r) r, hR (-t) = hR t := by
    intro t _
    simp only [hR, hC, Complex.ofReal_neg, neg_sq]
    have hsq_even : ∀ w : ℂ, CtOuter.sinhQ (-w) = CtOuter.sinhQ w := fun w => by
      unfold CtOuter.sinhQ; exact tsum_congr fun n => by rw [even_two_mul n |>.neg_pow]
    have hell_even : ∀ w : ℂ, ellQ (-w) = ellQ w := fun w => by
      by_cases hw : w = 0
      · simp [hw]
      · rw [ellQ_eq_div (neg_ne_zero.mpr hw), ellQ_eq_div hw, neg_sq]
        unfold ellC; rw [Complex.cosh_neg, hsq_even]
    have harg : (π : ℂ) * (-(t : ℂ)) / 2 = -((π : ℂ) * (t : ℂ) / 2) := by ring
    rw [harg, Complex.cosh_neg, hell_even]
  have hhR_eq : ∀ t ∈ Ioo (0 : ℝ) r, hR t = t ^ 4 * ΔF t := by
    intro t ht
    have hx0 : 0 < π * t / 2 := by have := ht.1; positivity
    have hell := ellQ_eq_div (Complex.ofReal_ne_zero.mpr hx0.ne')
    rw [ellC_ofReal hx0] at hell
    simp only [hR, hC]
    have harg : (π : ℂ) * (t : ℂ) / 2 = ((π * t / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_cosh, hell]
    have hval : (uctAlphaOsc : ℂ) * (t : ℂ) ^ 2 /
        (((Real.cosh (π * t / 2) : ℝ) : ℂ) ^ 2 *
          (((ceEll (π * t / 2) : ℝ) : ℂ) / ((π * t / 2 : ℝ) : ℂ) ^ 2)) =
        (((t ^ 4 * ΔF t : ℝ)) : ℂ) := by
      simp only [ΔF, uctM]; push_cast
      have h1 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have h2 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
      have h3 : (Real.cosh (π * t / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le (one_le_cosh_real _)).ne'
      have h4 : (ceEll (π * t / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ceEll_pos hx0).ne'
      field_simp [h1, h2, h3, h4]; ring
    rw [hval, Complex.ofReal_re]
  obtain ⟨d0, d2, d4, d6, d8, d10, D12, hD12, htay⟩ := even_taylor12 hr hhR_cd hhR_even
  -- Identify `d0 = 0` and `d2 = 3 * α_osc` via `eq_of_even_asymp4`
  have hasymp_h : ∃ C2 ≥ 0, ∀ t ∈ Ioo (0 : ℝ) (r / 2), |hR t - (0 + 3 * uctAlphaOsc * t ^ 2)| ≤ C2 * t ^ 4 := by
    have hosc_nn : 0 ≤ uctAlphaOsc := by
      rw [uctAlphaOsc_eq]; unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    refine ⟨1000 * uctAlphaOsc, by positivity, fun t ht => ?_⟩
    rw [hhR_eq t ⟨ht.1, lt_trans ht.2 (half_lt_self hr)⟩, zero_add]
    set x : ℝ := π * t / 2
    have hx0 : 0 < x := by have := ht.1; have := Real.pi_pos; positivity
    have hx12 : x ≤ 1 / 2 := by
      have hpi4 : π < 4 := Real.pi_lt_four
      have hr1 : r ≤ 1 / 8 := min_le_left _ _
      have ht_lt : t < 1 / 8 := lt_of_lt_of_le (lt_trans ht.2 (half_lt_self hr)) hr1
      simp only [x]; nlinarith [ht.1]
    have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have hx4 : x ^ 4 ≤ 1 / 16 := by nlinarith
    have hx6 : x ^ 6 ≤ x ^ 2 / 16 := by nlinarith [sq_nonneg x]
    have hch := cosh_taylor4_bound hx0.le (by linarith)
    have hce := ceEll_taylor4 hx0 hx12
    have hden_eq : t ^ 4 * ΔF t = uctAlphaOsc * t ^ 2 / (Real.cosh x ^ 2 * (ceEll x / x ^ 2)) := by
      simp only [ΔF, uctM, x]
      field_simp [Real.pi_pos.ne', ht.1.ne', (zero_lt_one.trans_le (one_le_cosh_real _)).ne', (ceEll_pos hx0).ne']; ring
    rw [hden_eq]
    set D := Real.cosh x ^ 2 * (ceEll x / x ^ 2)
    have hD_ge : 1 / 6 ≤ D := by
      have h1 : 1 ≤ Real.cosh x ^ 2 := one_le_pow₀ (one_le_cosh_real x)
      have h2 : 1 / 6 ≤ ceEll x / x ^ 2 := by
        rw [le_div_iff₀ (sq_pos_of_pos hx0)]
        have hge : x ^ 2 / 3 - 2 / 15 * x ^ 4 ≤ ceEll x := by
          have hth := ceHth_le_of_le_one hx0 (by linarith : x ≤ 1)
          have e : ceEll x = x ^ 2 / 3 - ceHth x := by
            unfold ceEll ceHth
            rw [show x / Real.tanh x = (Real.tanh x / x)⁻¹ by rw [inv_div], Real.log_inv]; ring
          linarith
        nlinarith [sq_nonneg x]
      nlinarith
    have hD_close : |D - 1 / 3| ≤ 10 * x ^ 2 := by
      have hch_bd : |Real.cosh x - 1| ≤ x ^ 2 := by
        have := abs_le.mp hch
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, pow_nonneg hx0.le 4, pow_nonneg hx0.le 6]
      have hch_sq : |Real.cosh x ^ 2 - 1| ≤ 3 * x ^ 2 := by
        have : Real.cosh x ^ 2 - 1 = (Real.cosh x - 1) * (Real.cosh x + 1) := by ring
        rw [this, abs_mul]
        have hsum : |Real.cosh x + 1| ≤ 3 := by
          have := abs_le.mp hch_bd; rw [abs_le]; constructor <;> nlinarith [sq_nonneg x]
        have := mul_le_mul hch_bd hsum (abs_nonneg _) (sq_nonneg x)
        linarith
      have hce_q : |ceEll x / x ^ 2 - 1 / 3| ≤ 6 * x ^ 2 := by
        rw [show ceEll x / x ^ 2 - 1 / 3 = (ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2 - 7 / 90 * x ^ 2 by
          field_simp [hx0.ne']; ring]
        have h1 : |(ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2| ≤ 20 * x ^ 4 := by
          rw [abs_div, abs_of_pos (sq_pos_of_pos hx0), div_le_iff₀ (sq_pos_of_pos hx0)]; nlinarith [hce]
        have htri := abs_sub ((ceEll x - (x ^ 2 / 3 - 7 / 90 * x ^ 4)) / x ^ 2) (7 / 90 * x ^ 2)
        rw [abs_of_nonneg (by positivity : 0 ≤ 7 / 90 * x ^ 2)] at htri
        have hx4_le : x ^ 4 ≤ x ^ 2 / 4 := by nlinarith [sq_nonneg x]
        linarith [sq_nonneg x]
      have heq : D - 1 / 3 = (Real.cosh x ^ 2 - 1) * (ceEll x / x ^ 2) + (ceEll x / x ^ 2 - 1 / 3) := by
        simp only [D]; ring
      rw [heq]
      have hce_le1 : |ceEll x / x ^ 2| ≤ 1 := by
        have hpos : 0 < ceEll x / x ^ 2 := div_pos (ceEll_pos hx0) (sq_pos_of_pos hx0)
        have hlt : ceEll x / x ^ 2 < 1 / 3 := (div_lt_iff₀ (sq_pos_of_pos hx0)).mpr (by linarith [ceEll_lt_sq_div_three hx0])
        rw [abs_of_pos hpos]; linarith
      have htri := abs_add_le ((Real.cosh x ^ 2 - 1) * (ceEll x / x ^ 2)) (ceEll x / x ^ 2 - 1 / 3)
      rw [abs_mul] at htri
      have hmul := mul_le_mul hch_sq hce_le1 (abs_nonneg _) (by positivity)
      linarith [sq_nonneg x]
    have hrewrite : uctAlphaOsc * t ^ 2 / D - 3 * uctAlphaOsc * t ^ 2 =
        uctAlphaOsc * t ^ 2 * (3 * (1 / 3 - D)) / D := by
      field_simp [(by linarith : 0 < D).ne']
    rw [hrewrite, abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hosc_nn,
      abs_of_pos (sq_pos_of_pos ht.1), abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_sub_comm, abs_of_pos (by linarith : 0 < D)]
    have hpi4 : π < 4 := Real.pi_lt_four
    have hpi2 : π ^ 2 ≤ 16 := by nlinarith [Real.pi_pos]
    calc uctAlphaOsc * t ^ 2 * (3 * |D - 1 / 3|) / D
        ≤ uctAlphaOsc * t ^ 2 * (3 * (10 * x ^ 2)) / (1 / 6) :=
          div_le_div₀ (by positivity) (by gcongr) (by norm_num) hD_ge
      _ = 45 * π ^ 2 * (uctAlphaOsc * t ^ 4) := by simp only [x]; field_simp; ring
      _ ≤ 1000 * (uctAlphaOsc * t ^ 4) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1000 * uctAlphaOsc * t ^ 4 := by ring
  obtain ⟨C2, hC2, h2⟩ := hasymp_h
  have h1_trunc : ∀ t ∈ Ioo (0 : ℝ) (r / 2), |hR t - (d0 + d2 * t ^ 2)| ≤
      (|d4| + |d6| + |d8| + |d10| + D12) * t ^ 4 := by
    intro t ht
    have ht1 : t ≤ 1 := by linarith [ht.2, show r ≤ 1 / 8 from min_le_left _ _]
    have h12 := htay t ⟨by linarith [ht.1], ht.2.le⟩
    rw [abs_of_pos ht.1] at h12
    have hsplit : hR t - (d0 + d2 * t ^ 2) =
        (hR t - (d0 + d2 * t ^ 2 + d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10)) +
        (d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10) := by ring
    rw [hsplit]
    have ht12 : t ^ 12 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have ht10 : t ^ 10 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have ht8 : t ^ 8 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have ht6 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht.1.le ht1 (by norm_num)
    have htri := abs_add_le (hR t - (d0 + d2 * t ^ 2 + d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10))
      (d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10)
    have hpoly : |d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10| ≤
        (|d4| + |d6| + |d8| + |d10|) * t ^ 4 := by
      have ha1 := abs_add_le (d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8) (d10 * t ^ 10)
      have ha2 := abs_add_le (d4 * t ^ 4 + d6 * t ^ 6) (d8 * t ^ 8)
      have ha3 := abs_add_le (d4 * t ^ 4) (d6 * t ^ 6)
      simp only [abs_mul, abs_of_pos (pow_pos ht.1 _)] at ha1 ha2 ha3
      nlinarith [abs_nonneg d4, abs_nonneg d6, abs_nonneg d8, abs_nonneg d10]
    nlinarith [h12, hD12]
  obtain ⟨hd0, hd2⟩ := eq_of_even_asymp4 (half_pos hr) h1_trunc h2
  subst hd0; subst hd2
  -- Bound `R_Δ(t) = ΔF(t) - (3 α_osc / t^2 + d4 + d6 t^2 + d8 t^4 + d10 t^6)` on `(0, 1]` and `[1, ∞)`
  set RΔ : ℝ → ℝ := fun t => ΔF t - (3 * uctAlphaOsc / t ^ 2 + d4 + d6 * t ^ 2 + d8 * t ^ 4 + d10 * t ^ 6)
  have hRΔ_cont : ContinuousOn RΔ (Ioi 0) :=
    hΔF_cont.sub (((((continuousOn_const.div (continuousOn_id.pow 2) fun t ht => pow_ne_zero 2 (mem_Ioi.mp ht).ne').add
      continuousOn_const).add (continuousOn_const.mul (continuousOn_id.pow 2))).add
      (continuousOn_const.mul (continuousOn_id.pow 4))).add
      (continuousOn_const.mul (continuousOn_id.pow 6)))
  obtain ⟨M_mid, hM_mid⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hRΔ_cont.mono (show Icc (r / 2) 1 ⊆ Ioi (0 : ℝ) from fun t ht => lt_of_lt_of_le (half_pos hr) ht.1))
  have hΔF_lg : ∀ t : ℝ, 1 ≤ t → |ΔF t| ≤ uctAlphaOsc * (π ^ 2 / 4) / uctM 1 := by
    intro t ht
    have hosc_nn : 0 ≤ uctAlphaOsc := by
      rw [uctAlphaOsc_eq]; unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
    have hch1 : 1 ≤ Real.cosh (π * t / 2) ^ 2 := one_le_pow₀ (one_le_cosh_real _)
    have hm_le : uctM 1 ≤ uctM t := uctM_strictMonoOn.monotoneOn zero_lt_one (zero_lt_one.trans_le ht) ht
    simp only [ΔF]
    rw [abs_of_nonneg (by have := uctM_pos (zero_lt_one.trans_le ht); positivity)]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)) hosc_nn)
      (uctM_pos one_pos) hm_le
  set B_inf : ℝ := uctAlphaOsc * (π ^ 2 / 4) / uctM 1 + |3 * uctAlphaOsc| + |d4| + |d6| + |d8| + |d10|
  set C_Δ : ℝ := max (max D12 (max M_mid 0 / (r / 2) ^ 8)) (max B_inf 0)
  have hC_Δ : 0 ≤ C_Δ := le_trans (le_max_right B_inf 0) (le_max_right _ _)
  refine ⟨b0_ce + d4, b2_ce + d6, b4_ce + d8, b6_ce + d10, C_ce + C_Δ, add_nonneg hC_ce hC_Δ, ?_, ?_⟩
  · intro t ht
    dsimp only
    rw [hsplit_F t ht.1]
    have heq : (uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t + ΔF t) -
        (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + 27 / 10 * uctAlphaOsc / t ^ 2 +
          (b0_ce + d4) + (b2_ce + d6) * t ^ 2 + (b4_ce + d8) * t ^ 4 + (b6_ce + d10) * t ^ 6) =
        (uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t -
          (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2 +
            b0_ce + b2_ce * t ^ 2 + b4_ce * t ^ 4 + b6_ce * t ^ 6)) + RΔ t := by
      simp only [RΔ]; ring
    rw [heq]
    have hRΔ_sm : |RΔ t| ≤ C_Δ * t ^ 8 := by
      by_cases hsm : t ≤ r / 2
      · have h12 := htay t ⟨by linarith [ht.1], hsm⟩
        rw [hhR_eq t ⟨ht.1, lt_of_le_of_lt hsm (half_lt_self hr)⟩, abs_of_pos ht.1] at h12
        have hdiv : |RΔ t| = |t ^ 4 * ΔF t - (0 + 3 * uctAlphaOsc * t ^ 2 +
            d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10)| / t ^ 4 := by
          rw [← abs_of_pos (pow_pos ht.1 4), ← abs_div]
          congr 1
          have hpos4 : |t ^ 4| = t ^ 4 := abs_of_pos (pow_pos ht.1 4)
          simp only [RΔ, hpos4]; field_simp [ht.1.ne']; ring
        rw [hdiv, div_le_iff₀ (pow_pos ht.1 4)]
        calc |t ^ 4 * ΔF t - (0 + 3 * uctAlphaOsc * t ^ 2 + d4 * t ^ 4 + d6 * t ^ 6 + d8 * t ^ 8 + d10 * t ^ 10)|
            ≤ D12 * t ^ 12 := h12
          _ ≤ C_Δ * t ^ 12 := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (pow_nonneg ht.1.le 12)
          _ = C_Δ * t ^ 8 * t ^ 4 := by ring
      · have hge : r / 2 ≤ t := le_of_not_ge hsm
        have hbd : |RΔ t| ≤ max M_mid 0 := (Real.norm_eq_abs _ ▸ hM_mid t ⟨hge, ht.2⟩).trans (le_max_left _ _)
        have hpow : (r / 2) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (half_pos hr).le hge 8
        calc |RΔ t| ≤ max M_mid 0 := hbd
          _ = (max M_mid 0 / (r / 2) ^ 8) * (r / 2) ^ 8 := by field_simp [(pow_pos (half_pos hr) 8).ne']
          _ ≤ C_Δ * t ^ 8 := mul_le_mul ((le_max_right _ _).trans (le_max_left _ _)) hpow
              (pow_nonneg (half_pos hr).le 8) hC_Δ
    exact (abs_add_le _ _).trans (by linarith [hce_sm t ht, hRΔ_sm])
  · intro t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    dsimp only
    rw [hsplit_F t ht0]
    have heq : (uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t + ΔF t) -
        (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + 27 / 10 * uctAlphaOsc / t ^ 2 +
          (b0_ce + d4) + (b2_ce + d6) * t ^ 2 + (b4_ce + d8) * t ^ 4 + (b6_ce + d10) * t ^ 6) =
        (uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t -
          (12 * uctAlphaOsc / π ^ 2 / t ^ 4 + -(3 / 10) * uctAlphaOsc / t ^ 2 +
            b0_ce + b2_ce * t ^ 2 + b4_ce * t ^ 4 + b6_ce * t ^ 6)) + RΔ t := by
      simp only [RΔ]; ring
    rw [heq]
    have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht
    have ht4 : t ^ 4 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
    have ht2 : t ^ 2 ≤ t ^ 6 := pow_le_pow_right₀ ht (by norm_num)
    have hinv2 : 1 / t ^ 2 ≤ t ^ 6 := (div_le_one (pow_pos ht0 2) |>.mpr (one_le_pow₀ ht)).trans ht6
    have hRΔ_lg : |RΔ t| ≤ C_Δ * t ^ 6 := by
      have htri : |RΔ t| ≤ |ΔF t| + |3 * uctAlphaOsc| * (1 / t ^ 2) + |d4| + |d6| * t ^ 2 + |d8| * t ^ 4 + |d10| * t ^ 6 := by
        simp only [RΔ]
        have h1 := abs_sub (ΔF t) (3 * uctAlphaOsc / t ^ 2 + d4 + d6 * t ^ 2 + d8 * t ^ 4 + d10 * t ^ 6)
        have h2 := abs_add_le (3 * uctAlphaOsc / t ^ 2 + d4 + d6 * t ^ 2 + d8 * t ^ 4) (d10 * t ^ 6)
        have h3 := abs_add_le (3 * uctAlphaOsc / t ^ 2 + d4 + d6 * t ^ 2) (d8 * t ^ 4)
        have h4 := abs_add_le (3 * uctAlphaOsc / t ^ 2 + d4) (d6 * t ^ 2)
        have h5 := abs_add_le (3 * uctAlphaOsc / t ^ 2) d4
        have ha1 : |3 * uctAlphaOsc / t ^ 2| = |3 * uctAlphaOsc| * (1 / t ^ 2) := by
          rw [abs_div, abs_of_pos (pow_pos ht0 2)]; ring
        have ha2 : |d6 * t ^ 2| = |d6| * t ^ 2 := by rw [abs_mul, abs_of_pos (pow_pos ht0 2)]
        have ha3 : |d8 * t ^ 4| = |d8| * t ^ 4 := by rw [abs_mul, abs_of_pos (pow_pos ht0 4)]
        have ha4 : |d10 * t ^ 6| = |d10| * t ^ 6 := by rw [abs_mul, abs_of_pos (pow_pos ht0 6)]
        linarith
      have hB : |RΔ t| ≤ B_inf * t ^ 6 := by
        simp only [B_inf]
        nlinarith [hΔF_lg t ht, abs_nonneg (3 * uctAlphaOsc), abs_nonneg d4, abs_nonneg d6,
          abs_nonneg d8, abs_nonneg d10,
          show 0 ≤ uctAlphaOsc * (π ^ 2 / 4) / uctM 1 by
            have : 0 ≤ uctAlphaOsc := by
              rw [uctAlphaOsc_eq]; unfold uctAlphaFl; have := ceK_pos; have := ceCs_pos; have := Real.pi_pos; positivity
            have := uctM_pos one_pos; positivity]
      exact hB.trans (mul_le_mul_of_nonneg_right ((le_max_left B_inf 0).trans (le_max_right _ _)) (pow_nonneg ht0.le 6))
    exact (abs_add_le _ _).trans (by linarith [hce_lg t ht, hRΔ_lg])

/-! ### Part (3) (`(fct:pk-fp)`) and bundled headline theorem `fct_phikill` -/

/-- Exact `O(a^8)` finite-part cancellation `(fct:pk-fp)` for `H_CE` (`c_{-1}(H_CE) = -(13/20) α_osc`). -/
theorem fct_phikill_fp_CE :
    ∃ C ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
        Tendsto (fun ε : ℝ =>
          (∫ t in Ioi ε, uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ *
            (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t)
          - (∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ))
          - (-(13 / 20 : ℝ) * uctAlphaOsc) / ε)
          (𝓝[>] (0 : ℝ)) (𝓝 I_a) := by
  obtain ⟨hF_cont, b0, b2, b4, b6, C_R, hCR, hsm, hlg⟩ := laurent_FCE
  obtain ⟨C_fp, hC_fp, hfp⟩ := fp_cancel_of_laurent hF_cont hCR hsm hlg
  obtain ⟨hfl_int, C_fl, hC_fl, hfl_asymp⟩ := floor_tail_integral_and_asymp
  refine ⟨C_fp, hC_fp, fun {a} ha ha1 => ?_⟩
  obtain ⟨_, hIa_bd, hIa_lim⟩ := hfp ha ha1
  refine ⟨_, hIa_bd, ?_⟩
  have hsub_zero : Tendsto (fun ε : ℝ =>
      (4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + 7 * uctAlphaOsc / (20 * ε)) -
      (2 / 3) * uctAlphaFl * uctM ε ^ (-(3 / 2 : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun ε : ℝ => C_fl * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).const_mul C_fl)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ε hε
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hfl_asymp ε hε.1 hε.2.le
  have hcomb := hIa_lim.add hsub_zero
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [(hfl_int ε hε).2]
  have hmul_div : ∀ t : ℝ, uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ / uctM t *
      (1 - (phiKill a ((t : ℂ) * Complex.I)).re) =
      uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ *
        (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t := fun t => by ring
  simp_rw [hmul_div]
  ring

/-- Exact `O(a^8)` finite-part cancellation `(fct:pk-fp)` for `H_*` (`c_{-1}(H_*) = (47/20) α_osc`). -/
theorem fct_phikill_fp_star :
    ∃ C ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
        Tendsto (fun ε : ℝ =>
          (∫ t in Ioi ε, uctAlphaOsc * ‖uctHstar ((t : ℂ) * Complex.I)‖ *
            (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t)
          - (∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ))
          - ((47 / 20 : ℝ) * uctAlphaOsc) / ε)
          (𝓝[>] (0 : ℝ)) (𝓝 I_a) := by
  obtain ⟨hF_cont, b0, b2, b4, b6, C_R, hCR, hsm, hlg⟩ := laurent_Fstar
  obtain ⟨C_fp, hC_fp, hfp⟩ := fp_cancel_of_laurent hF_cont hCR hsm hlg
  obtain ⟨hfl_int, C_fl, hC_fl, hfl_asymp⟩ := floor_tail_integral_and_asymp
  refine ⟨C_fp, hC_fp, fun {a} ha ha1 => ?_⟩
  obtain ⟨_, hIa_bd, hIa_lim⟩ := hfp ha ha1
  refine ⟨_, hIa_bd, ?_⟩
  have hsub_zero : Tendsto (fun ε : ℝ =>
      (4 * uctAlphaOsc / (π ^ 2 * ε ^ 3) + 7 * uctAlphaOsc / (20 * ε)) -
      (2 / 3) * uctAlphaFl * uctM ε ^ (-(3 / 2 : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun ε : ℝ => C_fl * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).const_mul C_fl)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ε hε
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hfl_asymp ε hε.1 hε.2.le
  have hcomb := hIa_lim.add hsub_zero
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [(hfl_int ε hε).2]
  have hmul_div : ∀ t : ℝ, uctAlphaOsc * ‖uctHstar ((t : ℂ) * Complex.I)‖ / uctM t *
      (1 - (phiKill a ((t : ℂ) * Complex.I)).re) =
      uctAlphaOsc * ‖uctHstar ((t : ℂ) * Complex.I)‖ *
        (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t := fun t => by ring
  simp_rw [hmul_div]
  ring

/-- **Lemma FCT.4 (`fct:phikill`)** (`constant_terms_five.tex`, lines 304–393):
Complete statement bundling parts (1), (2), and (3) for `φ_kill = φ_{8,8}` and the general
binomial cutoff `φ_{p,q}`:
- (1) Holomorphicity on `ℂ \ {-a}`, real symmetry, `0 < φ_kill(σ; a) < 1` on `(0, ∞)`,
  near-zero and near-infinity expansions `(fct:pk-zero)` and `(fct:pk-inf)`, uniform bounds
  on `{Re z ≥ 0}` for `φ_kill`, `1 - φ_kill`, `∂_z^r φ_kill` (`r ≥ 1`), and `Im φ_kill(it; a)`.
- (2) Exact Cauchy moment vanishing `(fct:pk-cauchy)` for all `p, q ≥ 1`.
- (3) Exact `O(a^8)` finite-part cancellation `(fct:pk-fp)` for both `H_0 ∈ {H_*, H_CE}`. -/
theorem fct_phikill :
    -- (1a) Holomorphicity, real symmetry, and strict positivity in (0, 1) on (0, ∞)
    (∀ a : ℝ, DifferentiableOn ℂ (phiKill a) {z : ℂ | z ≠ -(a : ℂ)}) ∧
    (∀ a : ℝ, ∀ z : ℂ, phiKill a (starRingEnd ℂ z) = starRingEnd ℂ (phiKill a z)) ∧
    (∀ a σ : ℝ, 0 < a → 0 < σ →
      0 < (phiKill a (σ : ℂ)).re ∧ (phiKill a (σ : ℂ)).re < 1 ∧ (phiKill a (σ : ℂ)).im = 0) ∧
    -- (1b) Near-zero and near-infinity expansions `(fct:pk-zero)`, `(fct:pk-inf)`
    (∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → ‖z‖ ≤ a / 2 →
      ‖phiKill a z - ((Nat.choose 15 8 : ℝ) : ℂ) * (z / a) ^ 8‖ ≤ C * (‖z‖ / a) ^ 9) ∧
    (∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re → 2 * a ≤ ‖z‖ →
      ‖(1 - phiKill a z) - ((Nat.choose 15 7 : ℝ) : ℂ) * ((a : ℂ) / z) ^ 8‖ ≤ C * (a / ‖z‖) ^ 9) ∧
    -- (1c) Uniform bounds on `{Re z ≥ 0}` and imaginary bound on `z = it`
    (∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re → ‖phiKill a z‖ ≤ C * min ((‖z‖ / a) ^ 8) 1) ∧
    (∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖1 - phiKill a z‖ ≤ C ∧ (z ≠ 0 → ‖1 - phiKill a z‖ ≤ C * (a / ‖z‖) ^ 8)) ∧
    (∀ r : ℕ, 1 ≤ r → ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re → z ≠ 0 →
      ‖iteratedDeriv r (phiKill a) z‖ ≤
        C * min (‖z‖ ^ ((8 : ℤ) - r) * a ^ (-8 : ℤ)) (a ^ 8 * ‖z‖ ^ (-((8 + r : ℕ) : ℤ)))) ∧
    (∃ C ≥ 0, ∀ {a t : ℝ}, 0 < a → t ≠ 0 →
      |(phiKill a ((t : ℂ) * Complex.I)).im| ≤ C * min ((|t| / a) ^ 9) ((a / |t|) ^ 8)) ∧
    -- (2) Exact Cauchy moment vanishing `(fct:pk-cauchy)` for general `(p, q)`
    (∀ {p q j : ℕ} {a : ℝ}, 1 ≤ q → 1 ≤ j → 2 * j ≤ p → 0 < a →
      ∫ t in Ioi (0 : ℝ), (phiPQ p q a ((t : ℂ) * Complex.I)).re / t ^ (2 * j) = 0) ∧
    (∀ {p q k : ℕ} {a : ℝ}, 2 * k + 2 ≤ q → 0 < a →
      ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (1 - (phiPQ p q a ((t : ℂ) * Complex.I)).re) = 0) ∧
    -- (3) Exact `O(a^8)` finite-part cancellation `(fct:pk-fp)` for `H_*` and `H_CE`
    (∃ C ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
        Tendsto (fun ε : ℝ =>
          (∫ t in Ioi ε, uctAlphaOsc * ‖uctHstar ((t : ℂ) * Complex.I)‖ *
            (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t)
          - (∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ))
          - ((47 / 20 : ℝ) * uctAlphaOsc) / ε)
          (𝓝[>] (0 : ℝ)) (𝓝 I_a)) ∧
    (∃ C ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
        Tendsto (fun ε : ℝ =>
          (∫ t in Ioi ε, uctAlphaOsc * ‖uctHCE ((t : ℂ) * Complex.I)‖ *
            (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t)
          - (∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ))
          - (-(13 / 20 : ℝ) * uctAlphaOsc) / ε)
          (𝓝[>] (0 : ℝ)) (𝓝 I_a)) :=
  ⟨fun a => differentiableOn_phiPQ 8 8 a,
   fun a z => phiPQ_conj 8 8 a z,
   fun _ _ ha hσ => phiPQ_pos_and_lt_one_real (by norm_num) (by norm_num) ha hσ,
   phiKill_near_zero,
   one_sub_phiKill_near_inf,
   norm_phiPQ_le 8 8,
   norm_one_sub_phiPQ_le_one_and_tail 8 8 (by norm_num),
   fun r hr => norm_iteratedDeriv_phiPQ_le 8 8 r (by norm_num) (by norm_num) hr,
   abs_im_phiKill_le,
   fun hq hj h2j ha => phiPQ_moment_neg hq hj h2j ha,
   fun hq ha => phiPQ_moment_pos hq ha,
   fct_phikill_fp_star,
   fct_phikill_fp_CE⟩

/-- info: 'FormalResearch.SignUncertainty.FctPhiKill.fct_phikill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.FctPhiKill.fct_phikill

end FormalResearch.SignUncertainty.FctPhiKill
