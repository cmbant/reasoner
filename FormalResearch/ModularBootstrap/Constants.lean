module

public import FormalResearch.Special.AiryCftSignUncertainty
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Shared constants and local Airy extremal for the Spinless Virasoro Modular Bootstrap

Source: `CFT/modular_bootstrap/paper/local_airy_model.tex` and
`CFT/modular_bootstrap/notes/AIRY_SCALE.md`.

Defines the spinless Virasoro fold-tip constants `xiStar` ($\xi_* = \operatorname{arsinh}(1)/\pi$),
`lambdaV` ($\Lambda_V = 12\pi^2/(\pi^2 + 4\operatorname{arsinh}^2 1)$),
`xiBar` ($\bar\xi = \xi_*^2/3 = 1/\Lambda_V - 1/12$), `kTip`, `KTip`, `betaTip`, `cStar`, `Aopt`,
`sNode`, `localExtremalC` ($\Phi^*(s) = \operatorname{Ai}(-\beta s)^2/(s - s_1)$), `LStar`, and the
normalized unit-$L^1$ rigidity profile `phiStar`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap

open FormalResearch.Special

/-- Fold tip $\xi_* = \operatorname{arsinh}(1)/\pi$. -/
noncomputable def xiStar : ℝ := Real.arsinh 1 / π

/-- Spinless Hexagon slope $\Lambda_V = 12\pi^2/(\pi^2 + 4\operatorname{arsinh}^2 1)$. -/
noncomputable def lambdaV : ℝ := 12 * π ^ 2 / (π ^ 2 + 4 * Real.arsinh 1 ^ 2)

/-- Rescaled fold position $\bar\xi = \xi_*^2 / 3$. -/
noncomputable def xiBar : ℝ := xiStar ^ 2 / 3

/-- Tip density prefactor $k_{\mathrm{tip}} = 4 \cdot 2^{3/4} / (9\sqrt\pi)$. -/
noncomputable def kTip : ℝ := 4 * (2 : ℝ) ^ (3 / 4 : ℝ) / (9 * √π)

/-- Tip potential prefactor $K = 2\pi k_{\mathrm{tip}}$. -/
noncomputable def KTip : ℝ := 2 * π * kTip

/-- Scaling parameter $\beta = (3 K / 4)^{2/3}$. -/
noncomputable def betaTip : ℝ := (3 * KTip / 4) ^ (2 / 3 : ℝ)

/-- Threshold scale $c_* = 2\xi_* / (3\beta)$. -/
noncomputable def cStar : ℝ := 2 * xiStar / (3 * betaTip)

/-- Sharp spinless Airy coefficient $A_{\mathrm{opt}} = c_* |a_1|$. -/
noncomputable def Aopt : ℝ := cStar * |airyZero 1|

/-- Scaled Airy zeros $s_n = |a_n|/\beta$. -/
noncomputable def sNode (n : ℕ) : ℝ := |airyZero n| / betaTip

/-- First scaled Airy zero $s_1 = |a_1|/\beta$. -/
noncomputable def s1 : ℝ := sNode 1

lemma sinh_pi_mul_xiStar : Real.sinh (π * xiStar) = 1 := by
  unfold xiStar
  rw [mul_div_cancel₀ _ Real.pi_pos.ne']
  exact Real.sinh_arsinh 1

lemma xiStar_pos : 0 < xiStar := by
  unfold xiStar
  have ha : 0 < Real.arsinh 1 := by
    rw [← Real.sinh_lt_sinh, Real.sinh_zero, Real.sinh_arsinh]
    exact one_pos
  exact div_pos ha Real.pi_pos

lemma lambdaV_pos : 0 < lambdaV := by
  unfold lambdaV
  positivity

lemma xiBar_eq_inv_lambdaV_sub : xiBar = 1 / lambdaV - 1 / 12 := by
  unfold xiBar xiStar lambdaV
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

lemma kTip_pos : 0 < kTip := by
  unfold kTip; positivity

lemma KTip_pos : 0 < KTip := by
  unfold KTip; have := kTip_pos; positivity

lemma betaTip_pos : 0 < betaTip := by
  unfold betaTip; have := KTip_pos; positivity

lemma cStar_pos : 0 < cStar := by
  unfold cStar; have := xiStar_pos; have := betaTip_pos; positivity

lemma s1_pos : 0 < s1 := by
  unfold s1 sNode
  have h1 : airyZero 1 < 0 := airyZero_neg 1
  exact div_pos (abs_pos.mpr h1.ne) betaTip_pos

lemma four_thirds_betaTip_rpow : (4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ) = KTip := by
  unfold betaTip
  have hK : 0 < 3 * KTip / 4 := div_pos (mul_pos (by norm_num) KTip_pos) (by norm_num)
  rw [← Real.rpow_mul hK.le]
  norm_num

lemma betaTip_cube_eq : betaTip ^ 3 = (9 / 16 : ℝ) * KTip ^ 2 := by
  have h := four_thirds_betaTip_rpow
  have hb : 0 ≤ betaTip := betaTip_pos.le
  calc betaTip ^ 3 = (betaTip ^ (3 / 2 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast betaTip 3, ← Real.rpow_natCast (betaTip ^ (3 / 2 : ℝ)) 2,
          ← Real.rpow_mul hb]; norm_num
    _ = ((3 / 4 : ℝ) * KTip) ^ 2 := by rw [show betaTip ^ (3 / 2 : ℝ) = (3 / 4 : ℝ) * KTip by linarith]
    _ = (9 / 16 : ℝ) * KTip ^ 2 := by ring

lemma cStar_eq_closed :
    cStar = Real.arsinh 1 / ((3 * √2 * π ^ 4) ^ (1 / 3 : ℝ)) := by
  have hcube : (3 * betaTip) ^ 3 * (π / 2) ^ 3 = (3 * √2 * π ^ 4) := by
    have hb3 := betaTip_cube_eq
    have hk : KTip ^ 2 = (64 / 81 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) * π := by
      unfold KTip kTip
      have hp : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
      calc (2 * π * (4 * (2 : ℝ) ^ (3 / 4 : ℝ) / (9 * √π))) ^ 2
          = (64 / 81 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 * (π ^ 2 / √π ^ 2) := by ring
        _ = (64 / 81 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) * π := by
            rw [hp, ← Real.rpow_natCast ((2 : ℝ) ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul (by norm_num)]
            have hpi : π ≠ 0 := Real.pi_pos.ne'
            norm_num; field_simp
    have h2 : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * √2 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add two_pos, Real.rpow_one,
        Real.sqrt_eq_rpow]
    calc (3 * betaTip) ^ 3 * (π / 2) ^ 3
        = 27 * ((9 / 16 : ℝ) * KTip ^ 2) * (π ^ 3 / 8) := by rw [mul_pow, hb3]; ring
      _ = 27 * ((9 / 16 : ℝ) * ((64 / 81 : ℝ) * (2 * √2) * π)) * (π ^ 3 / 8) := by rw [hk, h2]
      _ = 3 * √2 * π ^ 4 := by ring
  have hrhs_cube : (((3 / 2 : ℝ) * π * betaTip) ^ 3) = 3 * √2 * π ^ 4 := by
    calc ((3 / 2 : ℝ) * π * betaTip) ^ 3 = (3 * betaTip) ^ 3 * (π / 2) ^ 3 := by ring
      _ = 3 * √2 * π ^ 4 := hcube
  have hbase : (3 / 2 : ℝ) * π * betaTip = (3 * √2 * π ^ 4) ^ (1 / 3 : ℝ) := by
    have hlhs_pos : 0 < (3 / 2 : ℝ) * π * betaTip := by
      have := Real.pi_pos; have := betaTip_pos; positivity
    calc (3 / 2 : ℝ) * π * betaTip
        = (((3 / 2 : ℝ) * π * betaTip) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast ((3 / 2 : ℝ) * π * betaTip) 3, ← Real.rpow_mul hlhs_pos.le]; norm_num
      _ = (3 * √2 * π ^ 4) ^ (1 / 3 : ℝ) := by rw [hrhs_cube]
  unfold cStar xiStar
  rw [← hbase]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  field_simp

lemma Aopt_eq_closed :
    Aopt = |airyZero 1| * Real.arsinh 1 / ((3 * √2 * π ^ 4) ^ (1 / 3 : ℝ)) := by
  unfold Aopt
  rw [cStar_eq_closed]
  ring

/-- Complex local extremal $\Phi^*(s) = \operatorname{Ai}(-\beta s)^2 / (s - s_1)$ with removable
value `0` at `s = s_1`. -/
noncomputable def localExtremalC (s : ℂ) : ℂ :=
  (betaTip : ℂ) * airyExtremal (-(betaTip : ℂ) * s)

lemma differentiable_localExtremalC : Differentiable ℂ localExtremalC := by
  unfold localExtremalC
  exact (differentiable_airyExtremal.comp ((differentiable_const _).mul differentiable_id)).const_mul _

lemma localExtremalC_eq {s : ℂ} (hs : s ≠ (s1 : ℂ)) :
    localExtremalC s = airyAiC (-(betaTip : ℂ) * s) ^ 2 / (s - (s1 : ℂ)) := by
  unfold localExtremalC
  have hs1 : (s1 : ℂ) = -((airyZero 1 : ℂ) / (betaTip : ℂ)) := by
    have ha1 : airyZero 1 < 0 := airyZero_neg 1
    unfold s1 sNode
    rw [abs_of_neg ha1]
    push_cast; ring
  have hne : -(betaTip : ℂ) * s ≠ (airyZero 1 : ℂ) := by
    intro h
    apply hs
    rw [hs1]
    have hb : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    calc s = -((-(betaTip : ℂ) * s) / (betaTip : ℂ)) := by field_simp
      _ = -((airyZero 1 : ℂ) / (betaTip : ℂ)) := by rw [h]
  rw [airyExtremal_eq hne]
  have hb : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
  have hsum : (betaTip : ℂ) * s + (airyZero 1 : ℂ) ≠ 0 := by
    intro h; exact hne (by linear_combination -h)
  have hs' : s - -((airyZero 1 : ℂ) / (betaTip : ℂ)) ≠ 0 := by
    rw [← hs1]; exact sub_ne_zero.mpr hs
  rw [hs1, show -(betaTip : ℂ) * s - (airyZero 1 : ℂ) = -((betaTip : ℂ) * s + (airyZero 1 : ℂ)) by ring]
  field_simp [hb, hsum, hs']
  ring

lemma localExtremalC_ofReal (s : ℝ) :
    localExtremalC (s : ℂ) = ((betaTip * (airyExtremal ((-betaTip * s : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  unfold localExtremalC
  rw [show -(betaTip : ℂ) * (s : ℂ) = ((-betaTip * s : ℝ) : ℂ) by push_cast; ring]
  rw [airyExtremal_ofReal]
  simp only [Complex.ofReal_re, Complex.ofReal_mul]

lemma localExtremalC_re (s : ℝ) :
    (localExtremalC (s : ℂ)).re = airyAi (-betaTip * s) ^ 2 / (s - s1) := by
  by_cases hs : s = s1
  · subst hs
    have hs1_eq : -betaTip * s1 = airyZero 1 := by
      unfold s1 sNode
      rw [abs_of_neg (airyZero_neg 1)]
      have hb : betaTip ≠ 0 := betaTip_pos.ne'
      field_simp
    unfold localExtremalC
    rw [show -(betaTip : ℂ) * (s1 : ℂ) = ((-betaTip * s1 : ℝ) : ℂ) by push_cast; ring, hs1_eq]
    unfold airyExtremal
    rw [airyAiC_airyZero, sub_self, div_zero]
    simp
  · have hsc : (s : ℂ) ≠ (s1 : ℂ) := fun h => hs (Complex.ofReal_injective h)
    rw [localExtremalC_eq hsc, show -(betaTip : ℂ) * (s : ℂ) = ((-betaTip * s : ℝ) : ℂ) by push_cast; ring,
      airyAiC_ofReal]
    norm_cast

lemma localExtremalC_nonneg {s : ℝ} (hs : s1 ≤ s) : 0 ≤ (localExtremalC (s : ℂ)).re := by
  rw [localExtremalC_re]
  exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr hs)

lemma localExtremalC_integrable : Integrable (fun s : ℝ => localExtremalC (s : ℂ)) := by
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  have hint := (airyExtremal_integrable).comp_mul_left' (neg_ne_zero.mpr hb)
  have heq : (fun s : ℝ => (betaTip : ℂ) * airyExtremal ((-betaTip * s : ℝ) : ℂ)) =
      fun s : ℝ => localExtremalC (s : ℂ) := by
    ext s; unfold localExtremalC; push_cast; rfl
  rw [← heq]
  exact hint.const_mul (betaTip : ℂ)

lemma localExtremalC_integral : ∫ s : ℝ, localExtremalC (s : ℂ) = 0 := by
  unfold localExtremalC
  have h1 : (fun s : ℝ => (betaTip : ℂ) * airyExtremal (-(betaTip : ℂ) * (s : ℂ))) =
      fun s : ℝ => (betaTip : ℂ) * airyExtremal ((-betaTip * s : ℝ) : ℂ) := by
    ext s; push_cast; rfl
  rw [h1, integral_const_mul, Measure.integral_comp_mul_left
    (fun x : ℝ => airyExtremal (x : ℂ)) (-betaTip)]
  rw [airyExtremal_integral]
  simp

/-- Normalization integral $L_* = \int_{a_1}^\infty \frac{\operatorname{Ai}(u)^2}{u - a_1}\,du
= \frac12 \|\Phi^*\|_1$. -/
noncomputable def LStar : ℝ :=
  ∫ u in Ioi (airyZero 1), airyAi u ^ 2 / (u - airyZero 1)

private lemma integral_norm_localExtremalC :
    (∫ s : ℝ, ‖localExtremalC (s : ℂ)‖) = ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖ := by
  have hnorm_s : ∀ s : ℝ, ‖localExtremalC (s : ℂ)‖ = betaTip * ‖airyExtremal ((-betaTip * s : ℝ) : ℂ)‖ := by
    intro s
    unfold localExtremalC
    rw [show -(betaTip : ℂ) * (s : ℂ) = ((-betaTip * s : ℝ) : ℂ) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos betaTip_pos]
  simp_rw [hnorm_s, integral_const_mul, Measure.integral_comp_mul_left
    (fun u : ℝ => ‖airyExtremal (u : ℂ)‖) (-betaTip)]
  rw [abs_inv, abs_neg, abs_of_pos betaTip_pos, smul_eq_mul]
  have hp : betaTip ≠ 0 := betaTip_pos.ne'
  field_simp

lemma LStar_eq_half_norm_integral :
    LStar = (1 / 2 : ℝ) * ∫ s : ℝ, ‖localExtremalC (s : ℂ)‖ := by
  have hiC : Integrable (fun u : ℝ => airyExtremal (u : ℂ)) := airyExtremal_integrable
  have hiRe : Integrable (fun u : ℝ => (airyExtremal (u : ℂ)).re) := hiC.re
  have hzero : ∫ u : ℝ, (airyExtremal (u : ℂ)).re = 0 := by
    have h2 : ∫ u : ℝ, (airyExtremal (u : ℂ)).re = (∫ u : ℝ, airyExtremal (u : ℂ)).re :=
      integral_re hiC
    rw [h2, airyExtremal_integral]; rfl
  have hsplit :
      (∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re) +
        ∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re =
      ∫ u : ℝ, (airyExtremal (u : ℂ)).re := by
    simpa only [compl_Iic] using integral_add_compl measurableSet_Iic hiRe
  have hnorm_u : ∀ u : ℝ, ‖airyExtremal (u : ℂ)‖ = |(airyExtremal (u : ℂ)).re| := fun u => by
    rw [airyExtremal_ofReal, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
  have hsplit_abs :
      (∫ u in Iic (airyZero 1), ‖airyExtremal (u : ℂ)‖) +
        ∫ u in Ioi (airyZero 1), ‖airyExtremal (u : ℂ)‖ =
      ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖ := by
    simpa only [compl_Iic] using integral_add_compl measurableSet_Iic hiC.norm
  have hIic : ∫ u in Iic (airyZero 1), ‖airyExtremal (u : ℂ)‖ =
      ∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re := by
    refine setIntegral_congr_fun measurableSet_Iic fun u hu => ?_
    rw [hnorm_u u, abs_of_nonneg (airyExtremal_nonneg hu)]
  have hIoi_abs : ∫ u in Ioi (airyZero 1), ‖airyExtremal (u : ℂ)‖ =
      -(∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [hnorm_u u, airyExtremal_re]
    have hnonpos : -(airyAi u ^ 2 / (u - airyZero 1)) ≤ 0 := by
      have : 0 ≤ airyAi u ^ 2 / (u - airyZero 1) := div_nonneg (sq_nonneg _) (sub_pos.mpr hu).le
      linarith
    rw [abs_of_nonpos hnonpos]
  have hIoi_L : -(∫ u in Ioi (airyZero 1), (airyExtremal (u : ℂ)).re) = LStar := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [airyExtremal_re, neg_neg]
  have hiic_val : ∫ u in Iic (airyZero 1), (airyExtremal (u : ℂ)).re = LStar := by
    rw [hzero] at hsplit
    linarith [hIoi_L]
  have hhalf : LStar = (1 / 2 : ℝ) * ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖ := by
    linarith [hsplit_abs, hIic, hIoi_abs, hIoi_L, hiic_val]
  rw [hhalf, integral_norm_localExtremalC]

lemma LStar_pos : 0 < LStar := by
  rw [LStar_eq_half_norm_integral, integral_norm_localExtremalC]
  have hcont : Continuous (fun u : ℝ => ‖airyExtremal (u : ℂ)‖) :=
    (differentiable_airyExtremal.continuous.comp Complex.continuous_ofReal).norm
  have hnx0 : 0 < ‖airyExtremal ((0 : ℝ) : ℂ)‖ := by
    have ha := airyAi_pos (le_refl (0 : ℝ))
    have hz := airyZero_neg 1
    rw [airyExtremal_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact abs_pos.mpr (div_pos (pow_pos ha 2) (by linarith)).ne'
  have hpos : 0 < ∫ u : ℝ, ‖airyExtremal (u : ℂ)‖ := by
    refine (integral_pos_iff_support_of_nonneg (fun u : ℝ => norm_nonneg (airyExtremal (u : ℂ)))
      airyExtremal_integrable.norm).mpr ?_
    have hopen : IsOpen {u : ℝ | 0 < ‖airyExtremal (u : ℂ)‖} := isOpen_lt continuous_const hcont
    have hsupp : Function.support (fun u : ℝ => ‖airyExtremal (u : ℂ)‖) =
        {u : ℝ | 0 < ‖airyExtremal (u : ℂ)‖} := by
      ext u; simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq, norm_pos_iff, norm_ne_zero_iff]
    rw [hsupp]
    exact hopen.measure_pos volume ⟨0, hnx0⟩
  positivity

/-- Unit-$L^1$ normalized rigidity profile $\Phi_*(s) = (2L_*)^{-1} \operatorname{Ai}(-\beta s)^2/(s - s_1)$. -/
noncomputable def phiStar (s : ℂ) : ℂ :=
  ((2 * LStar)⁻¹ : ℂ) * localExtremalC s

lemma differentiable_phiStar : Differentiable ℂ phiStar :=
  differentiable_localExtremalC.const_mul _

lemma phiStar_integrable : Integrable (fun s : ℝ => phiStar (s : ℂ)) :=
  localExtremalC_integrable.const_mul _

lemma phiStar_integral : ∫ s : ℝ, phiStar (s : ℂ) = 0 := by
  unfold phiStar
  rw [integral_const_mul, localExtremalC_integral, mul_zero]

lemma phiStar_norm_integral : ∫ s : ℝ, ‖phiStar (s : ℂ)‖ = 1 := by
  unfold phiStar
  have h2L : 0 < 2 * LStar := by have := LStar_pos; positivity
  have hnorm : ∀ s : ℝ, ‖((2 * (LStar : ℂ))⁻¹) * localExtremalC (s : ℂ)‖ =
      (2 * LStar)⁻¹ * ‖localExtremalC (s : ℂ)‖ := by
    intro s
    have : (2 * (LStar : ℂ))⁻¹ = (((2 * LStar)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h2L)]
  simp_rw [hnorm, integral_const_mul]
  have hL : (∫ s : ℝ, ‖localExtremalC (s : ℂ)‖) = 2 * LStar := by
    linarith [LStar_eq_half_norm_integral]
  rw [hL, inv_mul_cancel₀ h2L.ne']

/-- info: 'FormalResearch.ModularBootstrap.Aopt_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Aopt_eq_closed

/-- info: 'FormalResearch.ModularBootstrap.phiStar_norm_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.phiStar_norm_integral

end FormalResearch.ModularBootstrap
