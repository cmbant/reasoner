/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctVacuumCancelBounds

/-!
# `fct:physical-budget` (c): the `L`-variable finite-part cancellation `hcancel` for the concrete datum (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:physical-budget` (c), with `(fct:bump-1L)` (Lemma `fct:comp-D` (2))
and `(fct:pk-fp)` (Lemma `fct:phikill` (3)).

**Proved here** (`fct_vac_cancel`), for the concrete datum `P = I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)` (`vacP`, so that `vacD P = D_*` of `fct:comp-D` (2)),
`Φ = φ_kill(iτ₀(·); a)` (`vacPhi`), `a³ = τ₁ = c^{-1/4}`:
`|∫_{3δ_L}^∞ D_*/u - ∫_{3δ_L}^∞ Re Φ · P/u| ≤ K (a³ + |α| a⁻³ + a⁸)`,
which is the field `hcancel` of `VacDisp` (`FctVacuumBudget`).

Route (all in Lean): (1) `vacG_tendsto`: `lim_{ε↓0} ∫_ε^∞ F₀ρ = f.p.₁ - I_a` with `|I_a| ≲ a⁸`, from `(fct:bump-1L)` (`bg_fp_asymptotic`) and
`(fct:pk-fp)` (`fct_phikill_fp_star/CE`) in the `t`-variable `u = m(t)`; (2) `vacG_cancel_core`: the piece on `(0, t₃]` is `≲ a⁻⁸ t₃⁵` (`|ρ| ≲ (t/a)⁸`,
`F₀ ≲ t⁻⁴`); (3) `vacGW_bound`: replacing `F₀ρ` by `F₀ρ e^{v}(1 + Δ_curv)` costs `≲ a³` (pointwise bounds `|e^v - 1| ≲ τ₁²`, `Δ_curv` of
`FctVacuumCancelBounds`); (4) change of variables `u = m(t)` on `(t₃, ∞)`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.CohnElkies FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctPhiKill FormalResearch.SignUncertainty.FctMoment

/-! ### The data in the `t`-variable -/

/-- `ρ_a(t) = Re φ_kill(it; a)`. -/
noncomputable def vacRho (a t : ℝ) : ℝ := (phiKill a ((t : ℂ) * Complex.I)).re

lemma continuous_vacRho {a : ℝ} (ha : 0 < a) : Continuous (vacRho a) := continuous_phiKill_imag_re ha

lemma abs_vacRho_le : ∃ K ≥ 0, ∀ {a t : ℝ}, 0 < a → 0 < t → |vacRho a t| ≤ K * min ((t / a) ^ 8) 1 :=
  phiKill_re_le

lemma vacF0_continuousOn (kind : StripKernelChoice) : ContinuousOn (vacF0 kind) (Ioi 0) := by
  have hH_c : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
    cases kind
    · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
      exact (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
        ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
        fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
        (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun _ _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
    · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
      exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
        ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
        fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')
  exact (continuousOn_const.mul hH_c).div uctM_continuousOn fun t ht => (uctM_pos ht).ne'

/-- `F₀ = α_osc |H₀(it)| / m(t)` is integrable on `(ε, ∞)` for `ε > 0`. -/
lemma vacF0_integrableOn (kind : StripKernelChoice) {ε : ℝ} (hε : 0 < ε) : IntegrableOn (vacF0 kind) (Ioi ε) := by
  obtain ⟨hbg, -, -⟩ := bg_fp_asymptotic kind
  obtain ⟨hfl, -⟩ := floor_tail_integral_and_asymp
  have h1 := hbg (p := 1) le_rfl hε
  have h2 := (hfl ε hε).1
  refine (h1.add h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := hε.trans ht
  have hm := uctM_pos ht0
  have hr := Real.rpow_pos_of_pos hm (3 / 2 : ℝ)
  have e : uctM t ^ (5 / 2 : ℝ) = uctM t ^ (3 / 2 : ℝ) * uctM t := by
    rw [← Real.rpow_add_one hm.ne']; norm_num
  simp only [Pi.add_apply, vacF0, pow_one]
  rw [e]
  generalize ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = N
  field_simp
  ring

lemma vacG_integrableOn (kind : StripKernelChoice) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    IntegrableOn (fun t => vacRho a t * vacF0 kind t) (Ioi ε) := by
  obtain ⟨K, hK0, hK⟩ := abs_vacRho_le
  have hF := vacF0_integrableOn kind hε
  refine (hF.const_mul K).mono' ((continuous_vacRho ha).aestronglyMeasurable.mul hF.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hε.trans ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vacF0_nonneg kind ht0)]
  refine mul_le_mul_of_nonneg_right ?_ (vacF0_nonneg kind ht0)
  exact (hK ha ht0).trans (mul_le_of_le_one_right hK0 (min_le_right _ _))

/-- `(fct:pk-fp)` for both kernels, in the form used by `fct:physical-budget`. -/
lemma phikill_fp_kind (kind : StripKernelChoice) : ∃ C ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
    ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
      Tendsto (fun ε : ℝ =>
        (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
          (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t)
        - (∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ))
        - stripCneg1 kind / ε) (𝓝[>] (0 : ℝ)) (𝓝 I_a) := by
  cases kind
  · exact fct_phikill_fp_star
  · exact fct_phikill_fp_CE

/-- **`lim_{ε↓0} ∫_ε^∞ F₀ρ = f.p.₁ - I_a`** with `|I_a| ≤ C a⁸` (`(fct:bump-1L)` with `(fct:pk-fp)`; `f.p.₁ = stripFp1`). -/
lemma vacG_tendsto (kind : StripKernelChoice) : ∃ C ≥ 0, ∀ {a : ℝ}, 0 < a → a ≤ 1 →
    ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
      Tendsto (fun ε : ℝ => ∫ t in Ioi ε, vacRho a t * vacF0 kind t) (𝓝[>] (0 : ℝ)) (𝓝 (stripFp1 kind - I_a)) := by
  obtain ⟨C, hC0, hC⟩ := phikill_fp_kind kind
  obtain ⟨hbg, hT1, -⟩ := bg_fp_asymptotic kind
  obtain ⟨hfl, -⟩ := floor_tail_integral_and_asymp
  refine ⟨C, hC0, fun {a} ha ha1 => ?_⟩
  obtain ⟨I_a, hIa, hT2⟩ := hC ha ha1
  refine ⟨I_a, hIa, ?_⟩
  refine (hT1.sub hT2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hF := vacF0_integrableOn kind hε0
  have hG := vacG_integrableOn kind ha hε0
  have hfl_ε := (hfl ε hε0).1
  have hbg_eq : (∫ t in Ioi ε, (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ -
      uctAlphaFl * uctMderiv t / uctM t ^ (3 / 2 : ℝ)) / uctM t) =
      (∫ t in Ioi ε, vacF0 kind t) - ∫ t in Ioi ε, uctAlphaFl * uctMderiv t / uctM t ^ (5 / 2 : ℝ) := by
    rw [← integral_sub hF hfl_ε]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := hε0.trans ht
    have hm := uctM_pos ht0
    have hr := Real.rpow_pos_of_pos hm (3 / 2 : ℝ)
    have e : uctM t ^ (5 / 2 : ℝ) = uctM t ^ (3 / 2 : ℝ) * uctM t := by
      rw [← Real.rpow_add_one hm.ne']; norm_num
    simp only [vacF0]
    rw [e]
    generalize ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = N
    field_simp
  have hphi_eq : (∫ t in Ioi ε, uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
      (1 - (phiKill a ((t : ℂ) * Complex.I)).re) / uctM t) =
      (∫ t in Ioi ε, vacF0 kind t) - ∫ t in Ioi ε, vacRho a t * vacF0 kind t := by
    rw [← integral_sub hF hG]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [vacF0, vacRho]
    ring
  simp only [hbg_eq, hphi_eq]
  ring

/-! ### The piece on `(0, t₃]` -/

lemma vacG_small (kind : StripKernelChoice) : ∃ K ≥ 0, ∀ {a t : ℝ}, 0 < a → 0 < t → t ≤ 1 / 8 →
    |vacRho a t * vacF0 kind t| ≤ K * t ^ 4 / a ^ 8 := by
  obtain ⟨Kr, hKr0, hKr⟩ := abs_vacRho_le
  obtain ⟨K0, hK00, hK0⟩ := vacF0_bounds kind
  refine ⟨Kr * K0, mul_nonneg hKr0 hK00, fun {a t} ha ht ht18 => ?_⟩
  rw [abs_mul, abs_of_nonneg (vacF0_nonneg kind ht)]
  have h1 : |vacRho a t| ≤ Kr * (t / a) ^ 8 := (hKr ha ht).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hKr0)
  have h2 : vacF0 kind t ≤ K0 / t ^ 4 := (hK0 t ht).1 ht18
  calc |vacRho a t| * vacF0 kind t ≤ (Kr * (t / a) ^ 8) * (K0 / t ^ 4) :=
        mul_le_mul h1 h2 (vacF0_nonneg kind ht) (by positivity)
    _ = Kr * K0 * t ^ 4 / a ^ 8 := by field_simp

/-- The finite-part cancellation on `(t₃, ∞)`: `∫_{t₃}^∞ F₀ρ = f.p.₁ - I_a + O(t₃⁵/a⁸)`, `|I_a| ≲ a⁸`. -/
lemma vacG_cancel_core (kind : StripKernelChoice) : ∃ C ≥ 0, ∀ {a t₃ : ℝ}, 0 < a → a ≤ 1 → 0 < t₃ → t₃ ≤ 1 / 8 →
    ∃ I_a : ℝ, |I_a| ≤ C * a ^ 8 ∧
      |(∫ t in Ioi t₃, vacRho a t * vacF0 kind t) - (stripFp1 kind - I_a)| ≤ C * t₃ ^ 5 / a ^ 8 := by
  obtain ⟨C1, hC10, hC1⟩ := vacG_tendsto kind
  obtain ⟨K, hK0, hK⟩ := vacG_small kind
  refine ⟨max C1 K, le_max_of_le_left hC10, fun {a t₃} ha ha1 ht3 ht318 => ?_⟩
  obtain ⟨I_a, hIa, hlim⟩ := hC1 ha ha1
  refine ⟨I_a, hIa.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), ?_⟩
  have hGint := fun {ε : ℝ} (hε : 0 < ε) => vacG_integrableOn kind ha hε
  have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(∫ t in Ioi t₃, vacRho a t * vacF0 kind t) -
      ∫ t in Ioi ε, vacRho a t * vacF0 kind t| ≤ K * t₃ ^ 5 / a ^ 8 := by
    filter_upwards [Ioo_mem_nhdsGT ht3] with ε hε
    have hε0 : 0 < ε := hε.1
    have hsplit : (∫ t in Ioi ε, vacRho a t * vacF0 kind t) =
        (∫ t in Ioc ε t₃, vacRho a t * vacF0 kind t) + ∫ t in Ioi t₃, vacRho a t * vacF0 kind t := by
      rw [← Ioc_union_Ioi_eq_Ioi hε.2.le]
      exact setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
        measurableSet_Ioi ((hGint hε0).mono_set Ioc_subset_Ioi_self)
        (hGint ht3)
    rw [hsplit, show (∫ t in Ioi t₃, vacRho a t * vacF0 kind t) -
        ((∫ t in Ioc ε t₃, vacRho a t * vacF0 kind t) + ∫ t in Ioi t₃, vacRho a t * vacF0 kind t) =
        -(∫ t in Ioc ε t₃, vacRho a t * vacF0 kind t) by ring, abs_neg]
    have hpt : ∀ t ∈ Ioc ε t₃, ‖vacRho a t * vacF0 kind t‖ ≤ K * t₃ ^ 4 / a ^ 8 := by
      intro t ht
      have ht0 : 0 < t := hε0.trans_le ht.1.le
      rw [Real.norm_eq_abs]
      refine (hK ha ht0 (ht.2.trans ht318)).trans ?_
      have : t ^ 4 ≤ t₃ ^ 4 := pow_le_pow_left₀ ht0.le ht.2 4
      gcongr
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc ε t₃) (hs := measure_Ioc_lt_top)
      (f := fun t => vacRho a t * vacF0 kind t) hpt
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hε.2])] at this
    refine this.trans ?_
    have hlen : t₃ - ε ≤ t₃ := by linarith
    calc K * t₃ ^ 4 / a ^ 8 * (t₃ - ε) ≤ K * t₃ ^ 4 / a ^ 8 * t₃ :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = K * t₃ ^ 5 / a ^ 8 := by ring
  have hlim2 : Tendsto (fun ε : ℝ => |(∫ t in Ioi t₃, vacRho a t * vacF0 kind t) -
      ∫ t in Ioi ε, vacRho a t * vacF0 kind t|) (𝓝[>] (0 : ℝ))
      (𝓝 |(∫ t in Ioi t₃, vacRho a t * vacF0 kind t) - (stripFp1 kind - I_a)|) :=
    (tendsto_const_nhds.sub hlim).abs
  have := le_of_tendsto hlim2 hbd
  refine this.trans ?_
  have h5 : 0 ≤ t₃ ^ 5 / a ^ 8 := by positivity
  calc K * t₃ ^ 5 / a ^ 8 = K * (t₃ ^ 5 / a ^ 8) := by ring
    _ ≤ max C1 K * (t₃ ^ 5 / a ^ 8) := mul_le_mul_of_nonneg_right (le_max_right _ _) h5
    _ = max C1 K * t₃ ^ 5 / a ^ 8 := by ring

/-! ### Replacing `F₀ρ` by `F₀ρ e^v (1 + Δ_curv)` -/

lemma exp_mul_one_add_sub (x d : ℝ) : Real.exp x * (1 + d) - 1 = (Real.exp x - 1) * (1 + d) + d := by ring

lemma one_add_mul_exp_le_one {t : ℝ} (ht : 0 ≤ t) : (1 + t) * Real.exp (-(π / 2) * t) ≤ 1 := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  calc (1 + t) * Real.exp (-(π / 2) * t) ≤ Real.exp t * Real.exp (-(π / 2) * t) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (t + -(π / 2) * t) := (Real.exp_add _ _).symm
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_gt_three]

/-- Replacing `F₀ρ` by `F₀ρ e^{v}(1 + Δ_curv)` on `(t₃, ∞)` (`t₃ ∈ [τ₁, 2τ₁]`) costs `O(a³)`, `a³ = τ₁`:
`|e^v - 1| ≲ τ₁²`, `Δ_curv` of `stripDeltaCurv_bounds`, `|ρ| ≲ (t/a)⁸`, `F₀ ≲ t⁻⁴`. -/
lemma vacGW_bound (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧ ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0, ∀ {c α τ₁ a t₃ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 → 0 < a → a ^ 3 = τ₁ → τ₁ ≤ t₃ → t₃ ≤ 2 * τ₁ →
      IntegrableOn (fun t => vacRho a t * vacF0 kind t *
        (Real.exp (vTotal kind K4 c α τ₁ t) * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t) - 1)) (Ioi t₃) ∧
      |∫ t in Ioi t₃, vacRho a t * vacF0 kind t *
        (Real.exp (vTotal kind K4 c α τ₁ t) * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t) - 1)| ≤ C * a ^ 3 := by
  obtain ⟨τv, hτv, hv⟩ := vTotal_bounds kind
  obtain ⟨τd, hτd, hτd100, hd⟩ := stripDeltaCurv_bounds kind
  obtain ⟨Kr, hKr0, hKr⟩ := abs_vacRho_le
  obtain ⟨K0, hK00, hK0⟩ := vacF0_bounds kind
  obtain ⟨KG, hKG0, hKG⟩ := vacG_small kind
  refine ⟨min τv τd, lt_min hτv hτd, (min_le_right _ _).trans hτd100, fun K4 hK4 => ?_⟩
  obtain ⟨Mv, hMv0, hMv⟩ := hv K4 hK4
  obtain ⟨CΔ, hCΔ0, hΔ⟩ := hd K4 hK4
  set Cexp : ℝ := Mv + Real.exp Mv * Mv ^ 2 / 2 with hCexp
  set CW : ℝ := Cexp * (1 + CΔ) + CΔ with hCW
  set B1 : ℝ := KG * 12 ^ 4 * CW + KG * CΔ with hB1
  set B2 : ℝ := Kr * K0 * CΔ with hB2
  have hCexp0 : 0 ≤ Cexp := by positivity
  have hCW0 : 0 ≤ CW := by positivity
  have hB10 : 0 ≤ B1 := by positivity
  have hB20 : 0 ≤ B2 := by positivity
  refine ⟨B1 + B2, by positivity, fun {c α τ₁ a t₃} hc hτ₁ hτ₁_le hc_eq hα_le ha ha3 ht3l ht3u => ?_⟩
  have hτ₁_v : τ₁ ≤ τv := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_d : τ₁ ≤ τd := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_d.trans hτd100
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have ha1 : a ≤ 1 := by
    by_contra h
    have h1 : 1 < a := not_le.mp h
    have : 1 < a ^ 3 := one_lt_pow₀ h1 (by norm_num)
    linarith
  have ha0 : 0 < a := ha
  obtain ⟨hv_cont, hv_abs, hv_zero⟩ := hMv hc hτ₁ hτ₁_v hc_eq hα_le
  obtain ⟨hD1, hD2, hD3, hDc⟩ := hΔ hc hτ₁ hτ₁_d hc_eq hα_le
  set v : ℝ → ℝ := vTotal kind K4 c α τ₁ with hv_def
  set Δ : ℝ → ℝ := stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) with hΔ_def
  have ht3_pos : 0 < t₃ := hτ₁.trans_le ht3l
  have ht3_18 : t₃ ≤ 1 / 8 := by linarith
  have hτ2 : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁.le hτ₁_1
  -- `|e^{v} - 1| ≤ C_exp τ₁²`
  have hexp : ∀ t, |Real.exp (v t) - 1| ≤ Cexp * τ₁ ^ 2 := by
    intro t
    have hx := hv_abs t
    have hM : Mv * τ₁ ^ 2 ≤ Mv := mul_le_of_le_one_right hMv0 hτ2
    have h1 := abs_exp_sub_one_sub_le hx
    have h2 : |Real.exp (v t) - 1| ≤ |Real.exp (v t) - 1 - v t| + |v t| := by
      have := abs_add_le (Real.exp (v t) - 1 - v t) (v t)
      rwa [sub_add_cancel] at this
    have h3 : (v t) ^ 2 ≤ (Mv * τ₁ ^ 2) ^ 2 := by
      rw [← sq_abs (v t)]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have h4 : Real.exp (Mv * τ₁ ^ 2) / 2 * (v t) ^ 2 ≤ Real.exp Mv / 2 * (Mv ^ 2 * τ₁ ^ 2 * τ₁ ^ 2) := by
      calc Real.exp (Mv * τ₁ ^ 2) / 2 * (v t) ^ 2 ≤ Real.exp Mv / 2 * (Mv * τ₁ ^ 2) ^ 2 := by
            gcongr
        _ = Real.exp Mv / 2 * (Mv ^ 2 * τ₁ ^ 2 * τ₁ ^ 2) := by ring
    have h5 : Real.exp Mv / 2 * (Mv ^ 2 * τ₁ ^ 2 * τ₁ ^ 2) ≤ Real.exp Mv * Mv ^ 2 / 2 * τ₁ ^ 2 := by
      have : 0 ≤ Real.exp Mv * Mv ^ 2 / 2 * τ₁ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hτ2 this]
    calc |Real.exp (v t) - 1| ≤ |Real.exp (v t) - 1 - v t| + |v t| := h2
      _ ≤ Real.exp (Mv * τ₁ ^ 2) / 2 * (v t) ^ 2 + Mv * τ₁ ^ 2 := add_le_add h1 hx
      _ ≤ Real.exp Mv * Mv ^ 2 / 2 * τ₁ ^ 2 + Mv * τ₁ ^ 2 := by linarith
      _ = Cexp * τ₁ ^ 2 := by rw [hCexp]; ring
  -- inner region: `|e^v(1+Δ) - 1| ≤ C_W τ₁²`
  have hE_inner : ∀ t, 0 < t → t ≤ 12 * τ₁ → |Real.exp (v t) * (1 + Δ t) - 1| ≤ CW * τ₁ ^ 2 := by
    intro t ht0 ht12
    have hΔt := hD1 t ht0 ht12
    have hτ3 : τ₁ ^ 3 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    rw [exp_mul_one_add_sub]
    have h1 : |1 + Δ t| ≤ 1 + CΔ := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      have : CΔ * τ₁ ^ 3 ≤ CΔ := mul_le_of_le_one_right hCΔ0 (pow_le_one₀ hτ₁.le hτ₁_1)
      linarith
    calc |(Real.exp (v t) - 1) * (1 + Δ t) + Δ t| ≤ |(Real.exp (v t) - 1) * (1 + Δ t)| + |Δ t| := abs_add_le _ _
      _ ≤ (Cexp * τ₁ ^ 2) * (1 + CΔ) + CΔ * τ₁ ^ 2 := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul (hexp t) h1 (abs_nonneg _) (by positivity))
            (hΔt.trans (mul_le_mul_of_nonneg_left hτ3 hCΔ0))
      _ = CW * τ₁ ^ 2 := by rw [hCW]; ring
  -- continuity on `(0, ∞)`
  have hcontG : ContinuousOn (fun t => vacRho a t * vacF0 kind t *
      (Real.exp (v t) * (1 + Δ t) - 1)) (Ioi 0) :=
    (((continuous_vacRho ha).continuousOn.mul (vacF0_continuousOn kind)).mul
      (((Real.continuous_exp.comp hv_cont).continuousOn.mul (continuousOn_const.add hDc)).sub continuousOn_const))
  have hmeas : ∀ s : Set ℝ, s ⊆ Ioi 0 → MeasurableSet s → AEStronglyMeasurable (fun t => vacRho a t * vacF0 kind t *
      (Real.exp (v t) * (1 + Δ t) - 1)) (volume.restrict s) :=
    fun s hs hms => (hcontG.mono hs).aestronglyMeasurable hms
  -- pointwise bound on `[τ₁, 1/8]`
  have hAB : ∀ t ∈ Ioc t₃ (1 / 8), ‖vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)‖ ≤ B1 * a ^ 10 := by
    intro t ht
    have ht0 : 0 < t := ht3_pos.trans ht.1
    have ht18 : t ≤ 1 / 8 := ht.2
    have hG := hKG ha ht0 ht18
    have htτ : τ₁ ≤ t := ht3l.trans ht.1.le
    rw [Real.norm_eq_abs, abs_mul]
    rcases le_or_gt t (12 * τ₁) with ht12 | ht12
    · have hE := hE_inner t ht0 ht12
      have ht4 : t ^ 4 ≤ (12 * τ₁) ^ 4 := pow_le_pow_left₀ ht0.le ht12 4
      calc |vacRho a t * vacF0 kind t| * |Real.exp (v t) * (1 + Δ t) - 1|
          ≤ (KG * (12 * τ₁) ^ 4 / a ^ 8) * (CW * τ₁ ^ 2) := by
            refine mul_le_mul (hG.trans ?_) hE (abs_nonneg _) (by positivity)
            gcongr
        _ = KG * 12 ^ 4 * CW * a ^ 10 := by rw [← ha3]; field_simp
        _ ≤ B1 * a ^ 10 := by
            rw [hB1]; gcongr; linarith [mul_nonneg hKG0 hCΔ0]
    · have hvt : v t = 0 := hv_zero t (by linarith)
      have hΔt := hD2 t ht12.le ht18
      rw [hvt, Real.exp_zero, one_mul, add_sub_cancel_left]
      calc |vacRho a t * vacF0 kind t| * |Δ t| ≤ (KG * t ^ 4 / a ^ 8) * (CΔ * τ₁ ^ 7 / t ^ 4) :=
            mul_le_mul hG hΔt (abs_nonneg _) (by positivity)
        _ = KG * CΔ * a ^ 13 := by rw [← ha3]; field_simp
        _ ≤ KG * CΔ * a ^ 10 := by
            have : a ^ 13 ≤ a ^ 10 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ B1 * a ^ 10 := by
            rw [hB1]; gcongr; linarith [mul_nonneg (mul_nonneg hKG0 (by norm_num : (0 : ℝ) ≤ 12 ^ 4)) hCW0]
  -- pointwise bound on `[1/8, ∞)`
  have hC : ∀ t ∈ Ioi (1 / 8 : ℝ), ‖vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)‖ ≤
      (B2 * τ₁ ^ 7) * Real.exp (-π * t) := by
    intro t ht
    have ht18 : (1 / 8 : ℝ) ≤ t := ht.le
    have ht0 : 0 < t := by linarith
    have hvt : v t = 0 := hv_zero t (by linarith)
    rw [Real.norm_eq_abs, abs_mul, hvt, Real.exp_zero, one_mul, add_sub_cancel_left]
    have hρ : |vacRho a t| ≤ Kr := (hKr ha ht0).trans (mul_le_of_le_one_right hKr0 (min_le_right _ _))
    have hF := ((hK0 t ht0).2 ht18)
    have hΔt : |Δ t| ≤ CΔ * τ₁ ^ 7 := by
      refine (hD3 t ht18).trans ?_
      have := one_add_mul_exp_le_one ht0.le
      calc CΔ * τ₁ ^ 7 * ((1 + t) * Real.exp (-(π / 2) * t)) ≤ CΔ * τ₁ ^ 7 * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = CΔ * τ₁ ^ 7 := mul_one _
    rw [abs_mul, abs_of_nonneg (vacF0_nonneg kind ht0), neg_mul]
    calc |vacRho a t| * vacF0 kind t * |Δ t| ≤ (Kr * (K0 * Real.exp (-(π * t)))) * (CΔ * τ₁ ^ 7) :=
          mul_le_mul (mul_le_mul hρ hF (vacF0_nonneg kind ht0) hKr0) hΔt (abs_nonneg _) (by positivity)
      _ = (B2 * τ₁ ^ 7) * Real.exp (-(π * t)) := by rw [hB2]; ring
  -- integrability and integral bound
  have hexpI : IntegrableOn (fun t : ℝ => (B2 * τ₁ ^ 7) * Real.exp (-π * t)) (Ioi (1 / 8)) :=
    (integrableOn_exp_mul_Ioi (a := -π) (by linarith [Real.pi_pos]) (1 / 8)).const_mul _
  have hI1 : IntegrableOn (fun t => vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)) (Ioc t₃ (1 / 8)) :=
    (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
      (hmeas _ (fun t ht => lt_trans ht3_pos ht.1) measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc hAB)
  have hI2 : IntegrableOn (fun t => vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)) (Ioi (1 / 8)) :=
    hexpI.mono' (hmeas _ (fun t ht => lt_trans (by norm_num) ht) measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi hC)
  have hsplit : Ioc t₃ (1 / 8) ∪ Ioi (1 / 8) = Ioi t₃ := Ioc_union_Ioi_eq_Ioi ht3_18
  refine ⟨by rw [← hsplit]; exact hI1.union hI2, ?_⟩
  rw [← hsplit, setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
    measurableSet_Ioi hI1 hI2]
  have hb1 : |∫ t in Ioc t₃ (1 / 8), vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)| ≤ B1 * a ^ 10 := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc t₃ (1 / 8)) (hs := measure_Ioc_lt_top)
      (f := fun t => vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)) hAB
    rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at this
    refine this.trans ?_
    have hlen : 1 / 8 - t₃ ≤ 1 := by linarith
    calc B1 * a ^ 10 * (1 / 8 - t₃) ≤ B1 * a ^ 10 * 1 := mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = B1 * a ^ 10 := mul_one _
  have hb2 : |∫ t in Ioi (1 / 8 : ℝ), vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)| ≤ B2 * τ₁ ^ 7 := by
    have h1 := norm_integral_le_of_norm_le hexpI (ae_restrict_of_forall_mem measurableSet_Ioi hC)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [Real.pi_pos])]
    have hpi : 0 < π := Real.pi_pos
    have : -Real.exp (-π * (1 / 8)) / -π ≤ 1 := by
      rw [neg_div_neg_eq, div_le_one hpi]
      have h1 : Real.exp (-π * (1 / 8)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith [Real.pi_gt_three]
    have h0 : 0 ≤ B2 * τ₁ ^ 7 := by positivity
    calc B2 * τ₁ ^ 7 * (-Real.exp (-π * (1 / 8)) / -π) ≤ B2 * τ₁ ^ 7 * 1 := mul_le_mul_of_nonneg_left this h0
      _ = B2 * τ₁ ^ 7 := mul_one _
  have h10 : a ^ 10 ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  have h21 : τ₁ ^ 7 ≤ a ^ 3 := by
    rw [← ha3]; calc (a ^ 3) ^ 7 = a ^ 21 := by ring
      _ ≤ a ^ 3 := pow_le_pow_of_le_one ha.le ha1 (by norm_num)
  calc _ ≤ |∫ t in Ioc t₃ (1 / 8), vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)| +
        |∫ t in Ioi (1 / 8 : ℝ), vacRho a t * vacF0 kind t * (Real.exp (v t) * (1 + Δ t) - 1)| := abs_add_le _ _
    _ ≤ B1 * a ^ 10 + B2 * τ₁ ^ 7 := add_le_add hb1 hb2
    _ ≤ B1 * a ^ 3 + B2 * a ^ 3 := add_le_add (mul_le_mul_of_nonneg_left h10 hB10) (mul_le_mul_of_nonneg_left h21 hB20)
    _ = (B1 + B2) * a ^ 3 := by ring

/-! ### The concrete datum and `hcancel` -/

/-- The concrete datum `P = I_osc^{DH₀} (1 + Δ_curv ∘ τ₀)` of the vacuum integral (`fct:comp-D` (2)), so that `vacD P = D_*`. -/
noncomputable def vacP (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) (L : ℝ) : ℝ :=
  stripIoscD kind (vTotal kind K4 c α τ₁) L *
    (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) (FormalResearch.CohnElkies.tau0 L))

lemma vacD_vacP (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) :
    vacD (vacP kind K4 c α τ₁) = stripDstar kind c (vTotal kind K4 c α τ₁) (v0 kind K4 τ₁) := rfl

/-- **`hcancel` of `VacDisp`** (`fct:physical-budget` (c), with `(fct:bump-1L)` and `(fct:pk-fp)`), for the concrete datum:
with `a³ = τ₁ = c^{-1/4}`, `δ_L = m(τ₁)`, `D_* = vacD P`, `Φ = φ_kill(iτ₀(·); a)`,
`|∫_{3δ_L}^∞ D_*/u - ∫_{3δ_L}^∞ Re Φ · P/u| ≤ K (a³ + |α| a⁻³ + a⁸)`. -/
theorem fct_vac_cancel (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 100 ∧ ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0, ∀ {c α τ₁ a : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ →
      τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 → 0 < a → a ^ 3 = τ₁ →
      |(∫ u in Ioi (3 * uctM τ₁), vacD (vacP kind K4 c α τ₁) u / u) -
        ∫ u in Ioi (3 * uctM τ₁), (vacPhi a u).re * vacP kind K4 c α τ₁ u / u| ≤
        C * (a ^ 3 + |α| * (a⁻¹) ^ 3 + a ^ 8) := by
  obtain ⟨τ2, hτ2, hτ2_100, h2⟩ := fct_comp_D_part2 kind
  obtain ⟨τW, hτW, hτW100, hW⟩ := vacGW_bound kind
  obtain ⟨C3, hC30, hC3⟩ := vacG_cancel_core kind
  refine ⟨min τ2 τW, lt_min hτ2 hτW, (min_le_left _ _).trans hτ2_100, fun K4 hK4 => ?_⟩
  obtain ⟨C2, hC20, hC2⟩ := h2 K4 hK4
  obtain ⟨CW, hCW0, hCW⟩ := hW K4 hK4
  refine ⟨C2 + 33 * C3 + CW, by positivity, fun {c α τ₁ a} hc hτ₁ hτ₁_le hc_eq hα_le ha ha3 => ?_⟩
  have hτ₁_2 : τ₁ ≤ τ2 := hτ₁_le.trans (min_le_left _ _)
  have hτ₁_W : τ₁ ≤ τW := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_2.trans hτ2_100
  have ha1 : a ≤ 1 := by
    by_contra h
    have h1 : 1 < a := not_le.mp h
    have : 1 < a ^ 3 := one_lt_pow₀ h1 (by norm_num)
    linarith
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hb1, _, _⟩ := hC2 hc hτ₁ hτ₁_2 hc_eq hα_le
  -- the point `t₃ = τ₀(3 δ_L)`
  have ht3 := saddleTau0_three_uctM_bounds hτ₁ (by linarith)
  set t₃ : ℝ := tau0 (3 * uctM τ₁) with ht3_def
  have ht3_pos : 0 < t₃ := hτ₁.trans ht3.1
  have h3m : 0 < 3 * uctM τ₁ := mul_pos (by norm_num) (uctM_pos hτ₁)
  have hmt3 : uctM t₃ = 3 * uctM τ₁ := ceEll_tau0 h3m
  have ht3_18 : t₃ ≤ 1 / 8 := by linarith [ht3.2]
  -- change of variables `u = m(t)`
  have hsub := uct_subst ht3_pos (fun u => (vacPhi a u).re * vacP kind K4 c α τ₁ u / u)
  rw [hmt3] at hsub
  have hpt : ∀ t ∈ Ioi t₃, uctMderiv t * ((vacPhi a (uctM t)).re * vacP kind K4 c α τ₁ (uctM t) / uctM t) =
      vacRho a t * vacF0 kind t *
        (Real.exp (vTotal kind K4 c α τ₁ t) * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t)) := by
    intro t ht
    have ht0 : 0 < t := ht3_pos.trans ht
    have hm := uctM_pos ht0
    have htau : tau0 (uctM t) = t := tau0_ceEll ht0
    have h' := uctMderiv_mul_stripIosc kind ht0
    simp only [vacPhi, vacP, stripIoscD, htau, vacRho, vacF0]
    rw [← h']
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt] at hsub
  obtain ⟨I_a, hIa, hcore⟩ := hC3 ha ha1 ht3_pos ht3_18
  obtain ⟨hWint, hWbd⟩ := hCW hc hτ₁ hτ₁_W hc_eq hα_le ha ha3 ht3.1.le ht3.2.le
  have hGint := vacG_integrableOn kind ha ht3_pos
  set G : ℝ → ℝ := fun t => vacRho a t * vacF0 kind t with hG
  set Ef : ℝ → ℝ := fun t => Real.exp (vTotal kind K4 c α τ₁ t) * (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) t) with hEf
  have hsum : (∫ t in Ioi t₃, G t * Ef t) = (∫ t in Ioi t₃, G t) + ∫ t in Ioi t₃, G t * (Ef t - 1) := by
    rw [← integral_add hGint hWint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [vacD_vacP, hsub, hsum]
  have hτinv : τ₁⁻¹ = (a⁻¹) ^ 3 := by rw [← ha3, inv_pow]
  have hDL : |(∫ u in Ioi (3 * uctM τ₁), stripDstar kind c (vTotal kind K4 c α τ₁) (v0 kind K4 τ₁) u / u) -
      stripFp1 kind| ≤ C2 * (a ^ 3 + |α| * (a⁻¹) ^ 3) := by
    have e : τ₁ + |α| * τ₁⁻¹ = a ^ 3 + |α| * (a⁻¹) ^ 3 := by rw [hτinv, ← ha3]
    rw [← e]; exact hb1
  -- the bound on `t₃⁵ / a⁸`
  have ht35 : C3 * t₃ ^ 5 / a ^ 8 ≤ 32 * C3 * a ^ 3 := by
    have h5 : t₃ ^ 5 ≤ (2 * τ₁) ^ 5 := pow_le_pow_left₀ ht3_pos.le ht3.2.le 5
    have ha8 : 0 < a ^ 8 := by positivity
    rw [div_le_iff₀ ha8]
    calc C3 * t₃ ^ 5 ≤ C3 * (2 * τ₁) ^ 5 := mul_le_mul_of_nonneg_left h5 hC30
      _ = 32 * C3 * a ^ 15 := by rw [← ha3]; ring
      _ ≤ 32 * C3 * a ^ 3 * a ^ 8 := by
          have : a ^ 15 ≤ a ^ 3 * a ^ 8 := by
            rw [← pow_add]; exact pow_le_pow_of_le_one ha.le ha1 (by norm_num)
          calc 32 * C3 * a ^ 15 ≤ 32 * C3 * (a ^ 3 * a ^ 8) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = 32 * C3 * a ^ 3 * a ^ 8 := by ring
  have hIa8 : |I_a| ≤ C3 * a ^ 8 := hIa
  have hcore' : |(∫ t in Ioi t₃, G t) - (stripFp1 kind - I_a)| ≤ 32 * C3 * a ^ 3 := by
    refine hcore.trans ?_
    simpa only [mul_div_assoc] using ht35
  have key : (∫ u in Ioi (3 * uctM τ₁), stripDstar kind c (vTotal kind K4 c α τ₁) (v0 kind K4 τ₁) u / u) -
      ((∫ t in Ioi t₃, G t) + ∫ t in Ioi t₃, G t * (Ef t - 1)) =
      ((∫ u in Ioi (3 * uctM τ₁), stripDstar kind c (vTotal kind K4 c α τ₁) (v0 kind K4 τ₁) u / u) - stripFp1 kind) -
        ((∫ t in Ioi t₃, G t) - (stripFp1 kind - I_a)) + I_a - ∫ t in Ioi t₃, G t * (Ef t - 1) := by ring
  rw [key]
  have hα0 : 0 ≤ |α| * (a⁻¹) ^ 3 := by positivity
  have ha3' : 0 ≤ a ^ 3 := by positivity
  have ha8' : 0 ≤ a ^ 8 := by positivity
  have hS : C2 * (a ^ 3 + |α| * (a⁻¹) ^ 3) + 32 * C3 * a ^ 3 + C3 * a ^ 8 + CW * a ^ 3 ≤
      (C2 + 33 * C3 + CW) * (a ^ 3 + |α| * (a⁻¹) ^ 3 + a ^ 8) := by
    nlinarith [mul_nonneg hC20 hα0, mul_nonneg hC30 ha3', mul_nonneg hC30 ha8', mul_nonneg hCW0 ha3',
      mul_nonneg hC20 ha8', mul_nonneg hCW0 hα0, mul_nonneg hC30 hα0, mul_nonneg hCW0 ha8']
  calc _ ≤ |(∫ u in Ioi (3 * uctM τ₁), stripDstar kind c (vTotal kind K4 c α τ₁) (v0 kind K4 τ₁) u / u) - stripFp1 kind| +
        |(∫ t in Ioi t₃, G t) - (stripFp1 kind - I_a)| + |I_a| + |∫ t in Ioi t₃, G t * (Ef t - 1)| := by
        exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ C2 * (a ^ 3 + |α| * (a⁻¹) ^ 3) + 32 * C3 * a ^ 3 + C3 * a ^ 8 + CW * a ^ 3 :=
        add_le_add (add_le_add (add_le_add hDL hcore') hIa8) hWbd
    _ ≤ _ := hS

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacG_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacG_tendsto

/-- info: 'FormalResearch.SignUncertainty.FctSym.vacGW_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacGW_bound

/-- info: 'FormalResearch.SignUncertainty.FctSym.fct_vac_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fct_vac_cancel

end FormalResearch.SignUncertainty.FctSym
