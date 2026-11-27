/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctConcreteCfu
public import FormalResearch.SignUncertainty.FctInnerCoord
public import FormalResearch.SignUncertainty.FctInnerB1
public import FormalResearch.SignUncertainty.FctWarpZero
public import FormalResearch.SignUncertainty.FctWarpAdmiss
public import FormalResearch.SignUncertainty.FctLeftEdgeBound
public import FormalResearch.SignUncertainty.CtBoasFreeze
public import FormalResearch.SignUncertainty.UctSeedEdgeKW

/-!
# Concrete edge reduction and `FctPhaseBox` for `concretePhiTilde` (`fct:warp-asymp`, `fct:inner-symbols` (b1))

Paper I (`constant_terms_five.tex`):
* `fctWarpIntegrand_eq_edge`: exact imaginary-axis factorization
  `K₀(iτ, ξ₁) A_ε(iτ) = exp(i(c Φ̃(τ; L₁, α) - π/4)) · a(τ)` on `τ > 0` (`(fct:K0A-edge)` / `(fct:inner-symbols)` (b));
* `fctWarpIntegrand_eq_inner_edge`: on `0 < τ ≤ 2 τ₁`, substituting `v = -log r₀ - K₄ τ⁴ + v₁ + α τ²` from
  `fct_comp_D_part1` simplifies `a(τ)` to `(π²/12) √(m'(τ)/(2 m(τ))) exp(B_c(iτ) - K₄ τ⁴ + v₁(τ) + α τ²) (1 - L₁ φ_kill / m)`
  (matching `(fct:inner-symbols)` (b3));
* `concretePhaseDom`, `concreteTau0`, `concretePhaseBox_exist`: instantiates `FctPhaseBox (concretePhiTilde K4 ε c)`
  together with `τ̃₀ < 2 τ₁`, the exact envelope derivatives `∂_{L₁} ã = S.V (A)` and `∂_α ã = c⁻¹ ϑ^{(1)}(τ̃₀)/√ã`,
  and the `(b1)` quantitative bounds.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### 1. Exact edge factorization of `fctWarpIntegrand` -/

lemma edgeS_eq_neg_exp_mul {τ : ℝ} (hτ : 0 < τ) :
    edgeS τ = -((τ ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I) := by
  rw [edgeS_eq]
  have harg : (((τ : ℂ) * Complex.I)).arg = π / 2 :=
    Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp, by simpa using hτ⟩
  have hne : (τ : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ.ne') Complex.I_ne_zero
  have hnorm : ‖(τ : ℂ) * Complex.I‖ = τ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
  have hlogc : Complex.log ((τ : ℂ) * Complex.I) = ((Real.log τ : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, harg]
  have hcpow : ((τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ) =
      ((τ ^ (5 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * ((5 * π / 4 : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlogc]
    have hadd : (↑(Real.log τ) + ↑(π / 2) * Complex.I) * (5 / 2 : ℂ) =
        ((Real.log τ * (5 / 2 : ℝ) : ℝ) : ℂ) + Complex.I * ((5 * π / 4 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hadd, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hτ]
  have hexp5 : Complex.exp (Complex.I * ((5 * π / 4 : ℝ) : ℂ)) =
      -Complex.exp (Complex.I * ((π / 4 : ℝ) : ℂ)) := by
    rw [show Complex.I * ((5 * π / 4 : ℝ) : ℂ) = Complex.I * ((π / 4 : ℝ) : ℂ) + (π : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hcpow, hexp5, Real.rpow_neg hτ.le]
  have hexp_inv : (Complex.exp (Complex.I * ((π / 4 : ℝ) : ℂ)))⁻¹ =
      Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring
  rw [mul_neg, inv_neg, mul_inv, hexp_inv]
  push_cast
  ring

/-- Exact edge amplitude `a(τ)` on `τ > 0`:
`K₀(iτ, ξ₁) A_ε(iτ) = exp(i(c Φ̃(τ; L₁, α) - π/4)) · concreteEdgeAmp K4 c L1 α τ`. -/
noncomputable def concreteEdgeAmp (K4 c L1 α τ : ℝ) : ℂ :=
  let v := vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))
  Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)) + (v τ : ℂ)) *
    ((uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ) : ℝ) : ℂ) *
    ((1 : ℂ) - (L1 : ℂ) * phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ))

/-- **`(fct:K0A-edge)` / `(fct:inner-symbols)` (b)**: exact imaginary-axis factorization of `fctWarpIntegrand`
for every `τ > 0` (`ε = ±1`, `0 < c`). -/
theorem fctWarpIntegrand_eq_edge {K4 ε c L1 α τ : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hτ : 0 < τ) :
    fctWarpIntegrand K4 ε c L1 α τ =
      Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ)) *
        concreteEdgeAmp K4 c L1 α τ := by
  set a := c ^ (-(1 / 12 : ℝ))
  set v := vTotal StripKernelChoice.star K4 c α (c ^ (-(1 / 4 : ℝ)))
  have hξ : 0 < fctXi1 L1 := by unfold fctXi1; positivity
  have hlog : Real.log (π ^ 2 * fctXi1 L1) = L1 := by
    unfold fctXi1
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
  have hm_ne : (uctM τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (uctM_pos hτ).ne'
  have hsg : stripG ((τ : ℂ) * Complex.I) + (L1 : ℂ) * phiKill a ((τ : ℂ) * Complex.I) =
      -((uctM τ : ℂ)) * ((1 : ℂ) - (L1 : ℂ) * phiKill a ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) := by
    rw [stripG_imag_eq_neg_m hτ.ne', abs_of_pos hτ]
    have hm_eq : hankelEdgeM τ = uctM τ := rfl
    rw [hm_eq]; field_simp [hm_ne]; ring
  have h1sub_pos : (1 : ℂ) - Complex.I * (τ : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hR_cancel : (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * edgeR τ = 1 := by
    rw [edgeR_eq]
    have hpow0 : (1 - (τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h, -⟩; apply h1sub_pos; linear_combination h
    rw [show Complex.I * (τ : ℂ) = (τ : ℂ) * Complex.I by ring]
    exact mul_inv_cancel₀ hpow0
  have hK : mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 L1) =
      ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)))) *
        Complex.exp (Complex.I * ((c * concretePhiPh τ L1 : ℝ) : ℂ)) := by
    rw [mellinK0_imag_outer c (fctXi1 L1) τ hξ, hlog]
    have hphi_eq : edgePhi L1 τ = concretePhiPh τ L1 := by
      unfold edgePhi concretePhiPh hankelEdgeM ceEll
      rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
      congr 2; ext u
      by_cases hu : u = 0
      · simp [hu]
      · have hpi := Real.pi_pos
        have hpiu : π * u / 2 ≠ 0 := by positivity
        rw [← Real.log_inv, inv_div]
    rw [hphi_eq]
    unfold outerK
    congr 2
    congr 1
    norm_num
  have hD : fctDcompAt K4 c α ((τ : ℂ) * Complex.I) =
      Complex.exp ((v τ : ℂ) + Complex.I * (fctThetaD v τ : ℂ)) := by
    unfold fctDcompAt
    rw [stripCompGExt_left]
  have hmPrime : mPrime τ = uctMderiv τ := by
    unfold uctMderiv uctEllDeriv mPrime
    rw [show 2 * (π * τ / 2) = π * τ by ring]
    have := Real.pi_pos
    field_simp
  have hAstar : (τ ^ (-(5 / 2 : ℝ)) : ℝ) * uctAstar τ =
      ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ) := by
    rw [uctAstar_eq_paper hτ, hmPrime]
    have hpow0 : τ ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hτ _).ne'
    rw [Real.rpow_neg hτ.le]; field_simp
  have hcore := seedZ_edge_core hε hτ
  have hphase : Complex.exp (Complex.I * ((c * concretePhiPh τ L1 : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
      Complex.exp (Complex.I * (fctThetaD v τ : ℂ)) *
      Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * concretePhiTilde K4 ε c τ (L1, α) - π / 4 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [concretePhiTilde, concretePhiLambda, concretePhiPh]
    have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    dsimp only [v]
    push_cast
    field_simp
    ring
  unfold fctWarpIntegrand fctWarpA concreteEdgeAmp
  rw [hK, ctHG_edge, hD, hsg, edgeS_eq_neg_exp_mul hτ]
  have hmul_comm : ((τ : ℂ) * Complex.I) = Complex.I * (τ : ℂ) := mul_comm _ _
  calc (((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)))) *
        Complex.exp (Complex.I * ((c * concretePhiPh τ L1 : ℝ) : ℂ))) *
        ((-(uctM τ : ℂ) * ((1 : ℂ) - (L1 : ℂ) * phiKill a ((τ : ℂ) * Complex.I) / (uctM τ : ℂ))) *
          Complex.exp ((v τ : ℂ) + Complex.I * (fctThetaD v τ : ℂ)) *
          (uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)) *
            edgeR τ * (-((τ ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I))))
      = (Complex.exp (Complex.I * ((c * concretePhiPh τ L1 : ℝ) : ℂ)) *
          ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
            (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ))))) * edgeR τ) *
        (Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
          Complex.exp ((v τ : ℂ) + Complex.I * (fctThetaD v τ : ℂ)) *
          Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I)) *
        ((uctM τ : ℂ) * ((τ ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) *
        ((1 : ℂ) - (L1 : ℂ) * phiKill a ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) := by
          rw [← hmul_comm]; ring
    _ = (Complex.exp (Complex.I * ((c * concretePhiPh τ L1 : ℝ) : ℂ)) *
          (Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
            ((1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * edgeR τ) * (uctAstar τ : ℂ))) *
        (Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
          (Complex.exp (v τ : ℂ) * Complex.exp (Complex.I * (fctThetaD v τ : ℂ))) *
          Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I)) *
        ((uctM τ : ℂ) * ((τ ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)) *
        ((1 : ℂ) - (L1 : ℂ) * phiKill a ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) := by
          rw [hcore, Complex.exp_add]; ring_nf
    _ = (Complex.exp (Complex.I * ((c * concretePhiPh τ L1 : ℝ) : ℂ)) *
          Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
          Complex.exp (Complex.I * (fctThetaD v τ : ℂ)) *
          Complex.exp ((-(π / 4 : ℝ) : ℂ) * Complex.I)) *
        (Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)) + (v τ : ℂ)) *
          ((uctM τ * ((τ ^ (-(5 / 2 : ℝ)) : ℝ) * uctAstar τ) : ℝ) : ℂ) *
          ((1 : ℂ) - (L1 : ℂ) * phiKill a ((τ : ℂ) * Complex.I) / (uctM τ : ℂ))) := by
          rw [hR_cancel, Complex.exp_add]; push_cast; ring
    _ = _ := by rw [hphase, hAstar]; push_cast; ring

lemma uctAlphaFl_div_osc :
    uctAlphaFl / (uctAlphaOsc * Real.sqrt (6 / π ^ 2)) = π ^ 2 / (12 * Real.sqrt 2) := by
  have hpi : 0 < π := Real.pi_pos
  have hfl : 0 < uctAlphaFl := uctAlphaFl_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  rw [uctAlphaOsc_eq, Real.sqrt_div (by norm_num), Real.sqrt_sq hpi.le, h6]
  have h32 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [h32]
  norm_num

/-- Inner simplification of `concreteEdgeAmp` on `0 < τ ≤ 2 τ₁` (matching `(fct:inner-symbols)` (b3)). -/
theorem concreteEdgeAmp_inner {K4 c L1 α τ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hα : |α| ≤ (c ^ (-(1 / 4 : ℝ))) ^ 2) (hτ0 : 0 < τ)
    (hτ2 : τ ≤ 2 * c ^ (-(1 / 4 : ℝ))) :
    concreteEdgeAmp K4 c L1 α τ =
      (((π ^ 2 / 12) * Real.sqrt (uctMderiv τ / (2 * uctM τ)) : ℝ) : ℂ) *
        Complex.exp (-((K4 * τ ^ 4 : ℝ) : ℂ) + (v1 StripKernelChoice.star K4 c (c ^ (-(1 / 4 : ℝ))) τ : ℂ) +
          ((α * τ ^ 2 : ℝ) : ℂ) + FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
        ((1 : ℂ) - (L1 : ℂ) * phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) := by
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  obtain ⟨hτD_pos, hτD_le, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have hb := hmain hK4 hc hτ₁_pos hτ₁ hcτ hα
  have hv_inner := (hb.2.2.2.2.2.1 τ (by rw [abs_of_pos hτ0]; exact hτ2)).2.2.2.2.2 hτ0.ne'
  have hm_pos : 0 < uctM τ := uctM_pos hτ0
  have hmp_pos : 0 < uctMderiv τ := uctMderiv_pos hτ0
  have hτ20 : τ < 1 / 4 := by
    have : τ₁ ≤ 1 / 20 := hτ₁.trans hτD_le
    linarith
  have hr0_pos : 0 < stripR0 StripKernelChoice.star τ := by
    rw [← r0Smooth_eq_stripR0 (by rw [abs_of_pos hτ0]; exact hτ20)]
    exact r0Smooth_pos (by rw [abs_of_pos hτ0]; exact hτ20)
  have hsr0 : stripR0 StripKernelChoice.star τ =
      stripIosc StripKernelChoice.star (uctM τ) / uctIfl (uctM τ) :=
    stripR0_eq_div hτ0
  have hveq : vTotal StripKernelChoice.star K4 c α τ₁ τ =
      -Real.log (stripR0 StripKernelChoice.star τ) - K4 * τ ^ 4 +
        v1 StripKernelChoice.star K4 c τ₁ τ + α * τ ^ 2 := by
    have h1 := hv_inner.2.2
    have h3 := hv_inner.2.1
    rw [← hsr0] at h1
    linarith only [h1, h3]
  have hexp_v : Real.exp (vTotal StripKernelChoice.star K4 c α τ₁ τ) =
      (stripR0 StripKernelChoice.star τ)⁻¹ *
        Real.exp (-K4 * τ ^ 4 + v1 StripKernelChoice.star K4 c τ₁ τ + α * τ ^ 2) := by
    have heq : vTotal StripKernelChoice.star K4 c α τ₁ τ =
        -Real.log (stripR0 StripKernelChoice.star τ) + (-K4 * τ ^ 4 + v1 StripKernelChoice.star K4 c τ₁ τ + α * τ ^ 2) := by
      linarith only [hveq]
    rw [heq, Real.exp_add, Real.exp_neg, Real.exp_log hr0_pos]
  have hr_factor : (stripR0 StripKernelChoice.star τ)⁻¹ *
      (uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ)) =
      (π ^ 2 / 12) * Real.sqrt (uctMderiv τ / (2 * uctM τ)) := by
    unfold stripR0
    rw [ite_eq_right_iff.mpr fun h => absurd h hτ0.ne', abs_of_pos hτ0]
    have hH_pos : 0 < ‖stripH0 StripKernelChoice.star ((τ : ℂ) * Complex.I)‖ := by
      change 0 < ‖uctHstar ((τ : ℂ) * Complex.I)‖
      rw [mul_comm, norm_uctHstar_edge hτ0]
      positivity
    have hH_eq : ‖stripH0 StripKernelChoice.star ((τ : ℂ) * Complex.I)‖ =
        ‖uctHstar (Complex.I * (τ : ℂ))‖ := by
      change ‖uctHstar ((τ : ℂ) * Complex.I)‖ = _; rw [mul_comm]
    have hm32 : uctM τ ^ (3 / 2 : ℝ) = uctM τ * Real.sqrt (uctM τ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm_pos, Real.rpow_one, Real.sqrt_eq_rpow]
    have hs1 : Real.sqrt (uctMderiv τ / (2 * uctM τ)) =
        Real.sqrt (uctMderiv τ) / (Real.sqrt 2 * Real.sqrt (uctM τ)) := by
      rw [Real.sqrt_div hmp_pos.le, Real.sqrt_mul (by norm_num)]
    have hs2 : Real.sqrt (6 / π ^ 2 * uctMderiv τ) =
        Real.sqrt (6 / π ^ 2) * Real.sqrt (uctMderiv τ) :=
      Real.sqrt_mul (by positivity) _
    rw [hH_eq, hm32, hs1, hs2]
    have hsq : Real.sqrt (uctMderiv τ) ^ 2 = uctMderiv τ := Real.sq_sqrt hmp_pos.le
    have h6p : 0 < Real.sqrt (6 / π ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [inv_div]
    calc uctAlphaFl * uctMderiv τ / (uctAlphaOsc * ‖uctHstar (Complex.I * (τ : ℂ))‖ * (uctM τ * Real.sqrt (uctM τ))) *
          (uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / (Real.sqrt (6 / π ^ 2) * Real.sqrt (uctMderiv τ)))
        = (uctAlphaFl / (uctAlphaOsc * Real.sqrt (6 / π ^ 2))) *
            ((uctMderiv τ / Real.sqrt (uctMderiv τ)) / Real.sqrt (uctM τ)) := by
          have hs_hm := (Real.sqrt_pos.mpr hm_pos).ne'
          have hs_hmp := (Real.sqrt_pos.mpr hmp_pos).ne'
          have hHu := (hH_eq ▸ hH_pos).ne'
          field_simp [hHu, hm_pos.ne', hs_hm, hs_hmp, uctAlphaOsc_pos.ne', h6p.ne']
      _ = (π ^ 2 / (12 * Real.sqrt 2)) * (Real.sqrt (uctMderiv τ) / Real.sqrt (uctM τ)) := by
          rw [uctAlphaFl_div_osc]
          have hdiv_sq : uctMderiv τ / Real.sqrt (uctMderiv τ) = Real.sqrt (uctMderiv τ) :=
            (div_eq_iff (Real.sqrt_pos.mpr hmp_pos).ne').mpr (by nlinarith only [hsq])
          rw [hdiv_sq]
      _ = (π ^ 2 / 12) * (Real.sqrt (uctMderiv τ) / (Real.sqrt 2 * Real.sqrt (uctM τ))) := by ring
  unfold concreteEdgeAmp
  dsimp only []
  rw [Complex.exp_add, ← Complex.ofReal_exp, hexp_v]
  have hrC := congrArg (fun r : ℝ => (r : ℂ)) hr_factor
  calc (Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
          (((stripR0 StripKernelChoice.star τ)⁻¹ *
            Real.exp (-K4 * τ ^ 4 + v1 StripKernelChoice.star K4 c τ₁ τ + α * τ ^ 2) : ℝ) : ℂ)) *
        ((uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ) : ℝ) : ℂ) *
        ((1 : ℂ) - (L1 : ℂ) * phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ))
      = (((stripR0 StripKernelChoice.star τ)⁻¹ *
            (uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * uctMderiv τ)) : ℝ) : ℂ) *
          (Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) *
            ((Real.exp (-K4 * τ ^ 4 + v1 StripKernelChoice.star K4 c τ₁ τ + α * τ ^ 2) : ℝ) : ℂ)) *
          ((1 : ℂ) - (L1 : ℂ) * phiKill (c ^ (-(1 / 12 : ℝ))) ((τ : ℂ) * Complex.I) / (uctM τ : ℂ)) := by
          push_cast; ring
    _ = _ := by
          rw [hrC, Complex.ofReal_exp, ← Complex.exp_add, add_comm (FormalResearch.Asymptotics.binetDiff _ _)]
          push_cast; ring

/-! ### 2. `FctPhaseBox` instantiation for `concretePhiTilde` -/

/-- Scaled parameter `ℓ₁(L₁) = (L₁ - θ₁^ε / c) / τ₁²`, `τ₁ = c^{-1/4}`. -/
noncomputable def concreteEll1 (ε c L1 : ℝ) : ℝ :=
  (L1 - ctTheta1 ε / c) / (c ^ (-(1 / 4 : ℝ))) ^ 2

/-- Open parameter box `Ω` in `(L₁, α)` for `concretePhiTilde K4 ε c`:
`ℓ₁ ∈ (ellMin · c^{-1/2}, 2.55)` and `|α| < 2 c^{-1/2}`. -/
def concretePhaseDom (ellMin ε c : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | ellMin * c ^ (-(1 / 2 : ℝ)) < concreteEll1 ε c p.1 ∧
    concreteEll1 ε c p.1 < 2.55 ∧ |p.2| < 2 * c ^ (-(1 / 2 : ℝ))}

lemma isOpen_concretePhaseDom (ellMin ε c : ℝ) : IsOpen (concretePhaseDom ellMin ε c) := by
  have hc1 : Continuous (fun p : ℝ × ℝ => concreteEll1 ε c p.1) :=
    ((continuous_fst.sub continuous_const).div_const _)
  have h1 : IsOpen {p : ℝ × ℝ | ellMin * c ^ (-(1 / 2 : ℝ)) < concreteEll1 ε c p.1} :=
    isOpen_lt continuous_const hc1
  have h2 : IsOpen {p : ℝ × ℝ | concreteEll1 ε c p.1 < 2.55} :=
    isOpen_lt hc1 continuous_const
  have h3 : IsOpen {p : ℝ × ℝ | |p.2| < 2 * c ^ (-(1 / 2 : ℝ))} :=
    isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  simpa [concretePhaseDom, Set.inter_def, and_assoc] using (h1.inter h2).inter h3

lemma concreteEll1_mem_OmT {ellMin ε c : ℝ} (hc : 0 < c) (hell : 0 ≤ ellMin)
    {p : ℝ × ℝ} (hp : p ∈ concretePhaseDom ellMin ε c) :
    (concreteEll1 ε c p.1, (1 : ℝ), p.2) ∈ OmT (c ^ (-(1 / 4 : ℝ))) := by
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hsq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  have hp1 : 0 < concreteEll1 ε c p.1 := by
    have : 0 ≤ ellMin * c ^ (-(1 / 2 : ℝ)) := mul_nonneg hell (Real.rpow_nonneg hc.le _)
    linarith [hp.1]
  refine ⟨⟨by linarith, by linarith [hp.2.1]⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [hsq]
  exact abs_lt.mp hp.2.2

/-- Critical point `τ̃₀(L₁, α) = τ₁ √(S.Z ((ℓ₁, 1, α), S.A (ℓ₁, 1, α)))` from a `ChartSetup`. -/
noncomputable def concreteTau0 (ε c : ℝ) (S : ChartSetup (ℝ × ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  c ^ (-(1 / 4 : ℝ)) * Real.sqrt (S.Z ((concreteEll1 ε c p.1, (1 : ℝ), p.2), S.A (concreteEll1 ε c p.1, (1 : ℝ), p.2)))

private lemma concretePhiTilde_hasFDerivAt {K4 ε c τ : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ_le : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hτ : 0 < τ) (p : ℝ × ℝ) :
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    let v := vTotal StripKernelChoice.star K4 c p.2 τ₁
    HasFDerivAt (fctPh (concretePhiTilde K4 ε c))
      (((p.1 - hankelEdgeM τ - c⁻¹ * deriv (outerTheta ε) τ + c⁻¹ * deriv (fctThetaD v) τ) •
          ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
        (τ • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
        ((c⁻¹ * fctThetaD (vAlpha 1 τ₁) τ) •
          (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) (τ, p) := by
  intro τ₁ v
  have hτ₁ : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmain⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  have h0 := hmain hK4 hc hτ₁ hτ_le hcτ (show |(0 : ℝ)| ≤ τ₁ ^ 2 by rw [abs_zero]; positivity)
  rcases h0 with ⟨hcd0, _, _, hsupp0, _⟩
  rcases hsupp0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hv0b_cs, hv0m_cs, _, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs, _⟩
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 StripKernelChoice.star K4 τ₁) := hcd0.1.add (contDiff_const.mul hcd0.2.1)
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 StripKernelChoice.star K4 c τ₁) := hcd0.2.2.2.1.add (contDiff_const.mul hcd0.2.2.2.2.1)
  have hv01_cd := hv0_cd.add hv1_cd
  have hv01_cs := hv0_cs.add hv1_cs
  have hva_eq := fctThetaD_vAlpha_eq hK4 hc hτ₁ hτ_le hcτ
  have hv1a_cd := (hva_eq 1 0).2.1
  have hv1a_cs := (hva_eq 1 0).2.2
  have hth01_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
      v1 StripKernelChoice.star K4 c τ₁ s)) := contDiff_fctThetaD hv01_cd hv01_cs
  have hthα_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD (vAlpha 1 τ₁)) := contDiff_fctThetaD hv1a_cd hv1a_cs
  have hva_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha p.2 τ₁) := by
    have : vAlpha p.2 τ₁ = fun s => p.2 * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul p.2 τ₁)
    rw [this]; exact contDiff_const.mul hv1a_cd
  have hva_cs : HasCompactSupport (vAlpha p.2 τ₁) := by
    have : vAlpha p.2 τ₁ = fun s => p.2 * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul p.2 τ₁)
    rw [this]; exact hv1a_cs.comp_left (mul_zero _)
  have hv_cd : ContDiff ℝ (⊤ : ℕ∞) v := hv01_cd.add hva_cd
  have hv_cs : HasCompactSupport v := hv01_cs.add hva_cs
  -- Derivatives of the components at `(τ, p)`
  have hd_tau : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (τ, p) :=
    hasFDerivAt_fst
  have hd_L : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (τ, p) :=
    hasFDerivAt_fst.comp (τ, p) hasFDerivAt_snd
  have hd_A : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (τ, p) :=
    hasFDerivAt_snd.comp (τ, p) hasFDerivAt_snd
  have hd_int : HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..x, hankelEdgeM u) (hankelEdgeM τ) τ := by
    have hint : IntervalIntegrable hankelEdgeM volume 0 τ :=
      (hankelEdgeM_continuousOn.mono fun x hx => by
        rw [Set.uIcc_of_le hτ.le] at hx; exact hx.1).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter hankelEdgeM (𝓝 τ) :=
      (hankelEdgeM_continuousOn.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas (hankelEdgeM_hasDerivAt hτ).continuousAt
  have hd_θ : HasDerivAt (outerTheta ε) (deriv (outerTheta ε) τ) τ :=
    ((contDiff_outerTheta ε).differentiable (by simp) τ).hasDerivAt
  have hd_th01 : HasDerivAt (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
      v1 StripKernelChoice.star K4 c τ₁ s))
      (deriv (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
        v1 StripKernelChoice.star K4 c τ₁ s)) τ) τ :=
    (hth01_cd.differentiable (by simp) τ).hasDerivAt
  have hd_thα : HasDerivAt (fctThetaD (vAlpha 1 τ₁)) (deriv (fctThetaD (vAlpha 1 τ₁)) τ) τ :=
    (hthα_cd.differentiable (by simp) τ).hasDerivAt
  have hlin_v : ∀ s : ℝ, fctThetaD (vTotal StripKernelChoice.star K4 c p.2 τ₁) s =
      fctThetaD (fun u => v0 StripKernelChoice.star K4 τ₁ u + v1 StripKernelChoice.star K4 c τ₁ u) s +
        p.2 * fctThetaD (vAlpha 1 τ₁) s := fun s => by
    have hlin := fctThetaD_linear hv01_cd hv01_cs hva_cd hva_cs 1 1 s
    simp only [one_mul] at hlin
    change fctThetaD (fun u => (v0 StripKernelChoice.star K4 τ₁ u +
      v1 StripKernelChoice.star K4 c τ₁ u) + vAlpha p.2 τ₁ u) s = _
    rw [hlin, (hva_eq p.2 s).1]
  have hderiv_v : deriv (fctThetaD v) τ =
      deriv (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
        v1 StripKernelChoice.star K4 c τ₁ s)) τ + p.2 * deriv (fctThetaD (vAlpha 1 τ₁)) τ := by
    have hfn : fctThetaD v = fun s => fctThetaD (fun u => v0 StripKernelChoice.star K4 τ₁ u +
        v1 StripKernelChoice.star K4 c τ₁ u) s + p.2 * fctThetaD (vAlpha 1 τ₁) s := funext hlin_v
    rw [hfn]
    exact (hd_th01.add (hd_thα.const_mul p.2)).deriv
  have hcomb := (((hd_L.mul hd_tau).sub (hd_int.comp_hasFDerivAt (τ, p) hd_tau)).sub
    ((hd_θ.comp_hasFDerivAt (τ, p) hd_tau).const_mul c⁻¹)).add
    (((hd_th01.comp_hasFDerivAt (τ, p) hd_tau).add
      (hd_A.mul (hd_thα.comp_hasFDerivAt (τ, p) hd_tau))).const_mul c⁻¹)
  have heq : (fun q : ℝ × ℝ × ℝ =>
      q.2.1 * q.1 - (∫ u in (0 : ℝ)..q.1, hankelEdgeM u) - c⁻¹ * outerTheta ε q.1 +
        c⁻¹ * (fctThetaD (fun s => v0 StripKernelChoice.star K4 τ₁ s +
          v1 StripKernelChoice.star K4 c τ₁ s) q.1 + q.2.2 * fctThetaD (vAlpha 1 τ₁) q.1)) =
      fctPh (concretePhiTilde K4 ε c) := by
    ext q
    unfold fctPh concretePhiTilde concretePhiLambda concretePhiPh vTotal
    have hva_q_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha q.2.2 τ₁) := by
      have : vAlpha q.2.2 τ₁ = fun s => q.2.2 * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul q.2.2 τ₁)
      rw [this]; exact contDiff_const.mul hv1a_cd
    have hva_q_cs : HasCompactSupport (vAlpha q.2.2 τ₁) := by
      have : vAlpha q.2.2 τ₁ = fun s => q.2.2 * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul q.2.2 τ₁)
      rw [this]; exact hv1a_cs.comp_left (mul_zero _)
    have hlin := fctThetaD_linear hv01_cd hv01_cs hva_q_cd hva_q_cs 1 1 q.1
    simp only [one_mul] at hlin
    change q.2.1 * q.1 - _ - _ + c⁻¹ * _ = q.2.1 * q.1 - _ - _ +
      1 * c⁻¹ * fctThetaD (fun s => (v0 StripKernelChoice.star K4 τ₁ s +
        v1 StripKernelChoice.star K4 c τ₁ s) + vAlpha q.2.2 τ₁ s) q.1
    rw [hlin, (hva_eq q.2.2 q.1).1, one_mul]
  rw [← heq]
  refine hcomb.congr_fderiv ?_
  ext
  · simp [hderiv_v]; ring
  · simp [hderiv_v]
  · simp [hderiv_v]

private lemma mQ_ge_point8 : ∃ δQ : ℝ, 0 < δQ ∧ δQ < 1 / 4 ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ δQ → (0.8 : ℝ) ≤ mQ τ := by
  have hmQ_cont : ContinuousAt mQ 0 :=
    contDiffOn_mQ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  have hmQ_08 : (0.8 : ℝ) < mQ 0 := by
    rw [mQ_zero]
    have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
    have hpi2 : (9.8 : ℝ) < π ^ 2 := by nlinarith only [hpi]
    linarith only [hpi2]
  obtain ⟨δQ, hδQ0, hδQ⟩ := Metric.continuousAt_iff.mp hmQ_cont (mQ 0 - 0.8) (by linarith only [hmQ_08])
  refine ⟨min (δQ / 2) (1 / 8), by positivity, by linarith only [min_le_right (δQ / 2) (1 / 8)], fun τ hτ0 hτ => ?_⟩
  have hd : dist τ 0 < δQ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ0]
    linarith only [hτ, min_le_left (δQ / 2) (1 / 8), hδQ0]
  have h1 := abs_lt.mp (by simpa [Real.dist_eq] using hδQ hd)
  linarith only [h1.1]

private lemma concrete_thetaD_deriv_bd :
    ∃ (D_v τ_lim_D : ℝ), 0 ≤ D_v ∧ 0 < τ_lim_D ∧
      ∀ {K4 c α τ : ℝ}, 1 ≤ K4 → 0 < c →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        τ₁ ≤ τ_lim_D → K4 * τ₁ ^ 2 ≤ 1 → |α| ≤ 2 * τ₁ ^ 2 → 2 * τ₁ ≤ τ →
        c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ D_v * τ₁ ^ 3 := by
  let τD := (fct_comp_D_part1 StripKernelChoice.star).choose
  obtain ⟨hτD_pos, hτD_le, _, _, _, _, _, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    CL0b, CL0m, CLa, CL1b, CL1m, Ctail, _, _, hCth_nn, hCL_nn, hCtail_nn, hmain_D⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  set D_in : ℝ := Cth0b 1 + Cth0m 1 + Cth1b 1 + Cth1m 1 + 2 * Ctha 1
  set D_tail : ℝ := Ctail 1 * (CL0b + CL0m + CL1b + CL1m + 2 * CLa) / 144
  have hDin0 : 0 ≤ D_in := by
    have h := hCth_nn 1
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h.1 h.2.1) h.2.2.2.1) h.2.2.2.2) (mul_nonneg (by norm_num) h.2.2.1)
  have hDtail0 : 0 ≤ D_tail := by
    have h1 := (hCtail_nn 1).1
    have h2 : 0 ≤ CL0b + CL0m + CL1b + CL1m + 2 * CLa := by
      linarith only [hCL_nn.1, hCL_nn.2.1, hCL_nn.2.2.1, hCL_nn.2.2.2.1, hCL_nn.2.2.2.2]
    exact div_nonneg (mul_nonneg h1 h2) (by norm_num)
  refine ⟨D_in + D_tail, τD, add_nonneg hDin0 hDtail0, hτD_pos, ?_⟩
  intro K4 c α τ hK4 hc τ₁ hτ₁_τD hK4t hα hτ2
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hτ₁_le1 : τ₁ ≤ 1 := (hτ₁_τD.trans hτD_le).trans (by norm_num)
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  have hcinv : c⁻¹ = τ₁ ^ 4 := by
    calc c⁻¹ = τ₁ ^ 4 * c * c⁻¹ := by rw [hcτ, one_mul]
      _ = τ₁ ^ 4 := by field_simp [hc.ne']
  have hα1 := hmain_D hK4 hc hτ₁_pos hτ₁_τD hcτ (show |τ₁ ^ 2| ≤ τ₁ ^ 2 by rw [abs_of_nonneg (sq_nonneg _)])
  have hva_eq := fctThetaD_vAlpha_eq hK4 hc hτ₁_pos hτ₁_τD hcτ
  rcases hα1 with ⟨hcd1, _, _, hsupp1, _, _, _, _, hth_in1, hth_tail1, _⟩
  rcases hsupp1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hv0b_cs, hv0m_cs, _, hv1b_cs, hv1m_cs, hv0_cs, hv1_cs, _⟩
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 StripKernelChoice.star K4 τ₁) := hcd1.1.add (contDiff_const.mul hcd1.2.1)
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 StripKernelChoice.star K4 c τ₁) := hcd1.2.2.2.1.add (contDiff_const.mul hcd1.2.2.2.2.1)
  have hv01_cd := hv0_cd.add hv1_cd
  have hv01_cs := hv0_cs.add hv1_cs
  have hv1a_cd := (hva_eq 1 0).2.1
  have hv1a_cs := (hva_eq 1 0).2.2
  have hva_cd : ContDiff ℝ (⊤ : ℕ∞) (vAlpha α τ₁) := by
    have : vAlpha α τ₁ = fun s => α * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul α τ₁)
    rw [this]; exact contDiff_const.mul hv1a_cd
  have hva_cs : HasCompactSupport (vAlpha α τ₁) := by
    have : vAlpha α τ₁ = fun s => α * vAlpha 1 τ₁ s := funext (vAlpha_eq_smul α τ₁)
    rw [this]; exact hv1a_cs.comp_left (mul_zero _)
  have hlin_fn : fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁) =
      fun s => fctThetaD (v0 StripKernelChoice.star K4 τ₁) s +
        fctThetaD (v1 StripKernelChoice.star K4 c τ₁) s + α * fctThetaD (vAlpha 1 τ₁) s := by
    ext s
    have h1 := fctThetaD_linear hv0_cd hv0_cs hv1_cd hv1_cs 1 1 s
    have h2 := fctThetaD_linear hv01_cd hv01_cs hva_cd hva_cs 1 1 s
    simp only [one_mul] at h1 h2
    change fctThetaD (fun u => (v0 StripKernelChoice.star K4 τ₁ u +
      v1 StripKernelChoice.star K4 c τ₁ u) + vAlpha α τ₁ u) s = _
    rw [h2, h1, (hva_eq α s).1]
  have hcd_v0 := contDiff_fctThetaD hv0_cd hv0_cs
  have hcd_v1 := contDiff_fctThetaD hv1_cd hv1_cs
  have hcd_va := contDiff_fctThetaD hv1a_cd hv1a_cs
  have hderiv_split : deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ =
      deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ +
      deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ + α * deriv (fctThetaD (vAlpha 1 τ₁)) τ := by
    rw [hlin_fn]
    exact (((hcd_v0.differentiable (by simp) τ).hasDerivAt.add
      (hcd_v1.differentiable (by simp) τ).hasDerivAt).add
      (((hcd_va.differentiable (by simp) τ).hasDerivAt).const_mul α)).deriv
  have htri : |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤
      |deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ| +
      |deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ| +
      |α| * |deriv (fctThetaD (vAlpha 1 τ₁)) τ| := by
    rw [hderiv_split]
    have h1 := abs_add_le
      (deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ + deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ)
      (α * deriv (fctThetaD (vAlpha 1 τ₁)) τ)
    have h2 := abs_add_le
      (deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ)
      (deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ)
    rw [abs_mul] at h1
    linarith only [h1, h2]
  have hbd_deriv :
      c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ (D_in + D_tail) * τ₁ ^ 3 := by
    have htri_mul :
        c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤
          c⁻¹ * |deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ| +
          c⁻¹ * |deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ| +
          c⁻¹ * (|α| * |deriv (fctThetaD (vAlpha 1 τ₁)) τ|) := by
      have hc0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
      calc c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ|
          ≤ c⁻¹ * (|deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ| +
              |deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ| +
              |α| * |deriv (fctThetaD (vAlpha 1 τ₁)) τ|) := mul_le_mul_of_nonneg_left htri hc0
        _ = _ := by ring
    rcases le_or_gt τ (12 * τ₁) with hle12 | hgt12
    · have ht12 : |τ| ≤ 12 * τ₁ := by rw [abs_of_pos (by linarith)]; exact hle12
      have hb := hth_in1 1 τ ht12
      have h0b := contDiff_fctThetaD hcd1.1 hv0b_cs
      have h0m := contDiff_fctThetaD hcd1.2.1 hv0m_cs
      have h1b := contDiff_fctThetaD hcd1.2.2.2.1 hv1b_cs
      have h1m := contDiff_fctThetaD hcd1.2.2.2.2.1 hv1m_cs
      have hv0_d : |deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ| ≤
          |deriv (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ| + K4 * |deriv (fctThetaD (v0Marg τ₁)) τ| := by
        have fn : fctThetaD (v0 StripKernelChoice.star K4 τ₁) =
            fun s => fctThetaD (v0Base StripKernelChoice.star τ₁) s + K4 * fctThetaD (v0Marg τ₁) s := by
          ext s
          have hlin := fctThetaD_linear hcd1.1 hv0b_cs hcd1.2.1 hv0m_cs 1 K4 s
          simp only [one_mul] at hlin
          unfold v0
          exact hlin
        have hder := (h0b.differentiable (by simp) τ).hasDerivAt.add
          ((h0m.differentiable (by simp) τ).hasDerivAt.const_mul K4)
        have hder' : HasDerivAt (fun s => fctThetaD (v0Base StripKernelChoice.star τ₁) s +
            K4 * fctThetaD (v0Marg τ₁) s)
            (deriv (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ +
              K4 * deriv (fctThetaD (v0Marg τ₁)) τ) τ := hder
        rw [fn, hder'.deriv]
        have ha := abs_add_le (deriv (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ)
          (K4 * deriv (fctThetaD (v0Marg τ₁)) τ)
        rw [abs_mul, abs_of_pos (by linarith only [hK4] : 0 < K4)] at ha
        exact ha
      have hv1_d : |deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ| ≤
          |deriv (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ| + K4 * |deriv (fctThetaD (v1Marg c τ₁)) τ| := by
        have fn : fctThetaD (v1 StripKernelChoice.star K4 c τ₁) =
            fun s => fctThetaD (v1Base StripKernelChoice.star c τ₁) s + K4 * fctThetaD (v1Marg c τ₁) s := by
          ext s
          have hlin := fctThetaD_linear hcd1.2.2.2.1 hv1b_cs hcd1.2.2.2.2.1 hv1m_cs 1 K4 s
          simp only [one_mul] at hlin
          unfold v1
          exact hlin
        have hder := (h1b.differentiable (by simp) τ).hasDerivAt.add
          ((h1m.differentiable (by simp) τ).hasDerivAt.const_mul K4)
        have hder' : HasDerivAt (fun s => fctThetaD (v1Base StripKernelChoice.star c τ₁) s +
            K4 * fctThetaD (v1Marg c τ₁) s)
            (deriv (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ +
              K4 * deriv (fctThetaD (v1Marg c τ₁)) τ) τ := hder
        rw [fn, hder'.deriv]
        have ha := abs_add_le (deriv (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ)
          (K4 * deriv (fctThetaD (v1Marg c τ₁)) τ)
        rw [abs_mul, abs_of_pos (by linarith only [hK4] : 0 < K4)] at ha
        exact ha
      have hmin1 : min 1 ((|τ| / τ₁) ^ (11 - 1)) ≤ 1 := min_le_left _ _
      have hm0b : |deriv (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ| ≤ Cth0b 1 := by
        have h := hb.1; rw [iteratedDeriv_one, show τ₁ ^ ((2 : ℤ) - (1 : ℕ)) = τ₁ by norm_num] at h
        have h1 : |deriv (fctThetaD (v0Base StripKernelChoice.star τ₁)) τ| ≤ Cth0b 1 * τ₁ :=
          h.trans (mul_le_of_le_one_right (mul_nonneg (hCth_nn 1).1 hτ₁_pos.le) hmin1)
        exact h1.trans (mul_le_of_le_one_right (hCth_nn 1).1 hτ₁_le1)
      have hm0m : K4 * |deriv (fctThetaD (v0Marg τ₁)) τ| ≤ Cth0m 1 := by
        have h := hb.2.1; rw [iteratedDeriv_one, show τ₁ ^ ((4 : ℤ) - (1 : ℕ)) = τ₁ ^ 3 by norm_num] at h
        have h1 : |deriv (fctThetaD (v0Marg τ₁)) τ| ≤ Cth0m 1 * τ₁ ^ 3 :=
          h.trans (mul_le_of_le_one_right (mul_nonneg (hCth_nn 1).2.1 (pow_nonneg hτ₁_pos.le 3)) hmin1)
        have hk : K4 * τ₁ ^ 3 ≤ 1 := by
          calc K4 * τ₁ ^ 3 = (K4 * τ₁ ^ 2) * τ₁ := by ring
            _ ≤ 1 * 1 := mul_le_mul hK4t hτ₁_le1 hτ₁_pos.le zero_le_one
            _ = 1 := one_mul 1
        calc K4 * |deriv (fctThetaD (v0Marg τ₁)) τ| ≤ K4 * (Cth0m 1 * τ₁ ^ 3) := mul_le_mul_of_nonneg_left h1 (by linarith only [hK4])
          _ = Cth0m 1 * (K4 * τ₁ ^ 3) := by ring
          _ ≤ Cth0m 1 := mul_le_of_le_one_right (hCth_nn 1).2.1 hk
      have hm1b : |deriv (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ| ≤ Cth1b 1 := by
        have h := hb.2.2.2.1; rw [iteratedDeriv_one, hcinv] at h
        have hpw : τ₁ ^ 4 * τ₁ ^ ((-1 : ℤ) - (1 : ℕ)) = τ₁ ^ 2 := by
          rw [show ((-1 : ℤ) - (1 : ℕ)) = -2 by norm_num, zpow_neg,
            show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]; field_simp [hτ₁_pos.ne']
        rw [mul_assoc (Cth1b 1), hpw] at h
        have h1 : |deriv (fctThetaD (v1Base StripKernelChoice.star c τ₁)) τ| ≤ Cth1b 1 * τ₁ ^ 2 :=
          h.trans (mul_le_of_le_one_right (mul_nonneg (hCth_nn 1).2.2.2.1 (sq_nonneg _)) hmin1)
        exact h1.trans (mul_le_of_le_one_right (hCth_nn 1).2.2.2.1 (by nlinarith only [hτ₁_pos, hτ₁_le1]))
      have hm1m : K4 * |deriv (fctThetaD (v1Marg c τ₁)) τ| ≤ Cth1m 1 := by
        have h := hb.2.2.2.2; rw [iteratedDeriv_one, hcinv, show ((1 : ℤ) - (1 : ℕ)) = 0 by norm_num,
          zpow_zero, mul_one] at h
        have h1 : |deriv (fctThetaD (v1Marg c τ₁)) τ| ≤ Cth1m 1 * τ₁ ^ 4 :=
          h.trans (mul_le_of_le_one_right (mul_nonneg (hCth_nn 1).2.2.2.2 (pow_nonneg hτ₁_pos.le 4)) hmin1)
        have hk : K4 * τ₁ ^ 4 ≤ 1 := by
          calc K4 * τ₁ ^ 4 = (K4 * τ₁ ^ 2) * τ₁ ^ 2 := by ring
            _ ≤ 1 * 1 := mul_le_mul hK4t (by nlinarith only [hτ₁_pos, hτ₁_le1]) (sq_nonneg _) zero_le_one
            _ = 1 := one_mul _
        calc K4 * |deriv (fctThetaD (v1Marg c τ₁)) τ| ≤ K4 * (Cth1m 1 * τ₁ ^ 4) := mul_le_mul_of_nonneg_left h1 (by linarith only [hK4])
          _ = Cth1m 1 * (K4 * τ₁ ^ 4) := by ring
          _ ≤ Cth1m 1 := mul_le_of_le_one_right (hCth_nn 1).2.2.2.2 hk
      have hma : |α| * |deriv (fctThetaD (vAlpha 1 τ₁)) τ| ≤ 2 * Ctha 1 := by
        have h := hb.2.2.1; rw [iteratedDeriv_one] at h
        have hfn : fctThetaD (vAlpha (τ₁ ^ 2) τ₁) = fun s => τ₁ ^ 2 * fctThetaD (vAlpha 1 τ₁) s :=
          funext fun s => (hva_eq (τ₁ ^ 2) s).1
        rw [hfn, deriv_const_mul_field, abs_mul, abs_of_pos (sq_pos_of_pos hτ₁_pos),
          show τ₁ ^ ((2 : ℤ) - (1 : ℕ)) = τ₁ by norm_num, mul_assoc (Ctha 1)] at h
        have h1 : τ₁ ^ 2 * |deriv (fctThetaD (vAlpha 1 τ₁)) τ| ≤ Ctha 1 * (τ₁ ^ 2 * τ₁) :=
          h.trans (mul_le_of_le_one_right (mul_nonneg (hCth_nn 1).2.2.1 (mul_nonneg (sq_nonneg _) hτ₁_pos.le)) hmin1)
        have h2 : |deriv (fctThetaD (vAlpha 1 τ₁)) τ| ≤ Ctha 1 :=
          (le_of_mul_le_mul_left (h1.trans_eq (by ring)) (sq_pos_of_pos hτ₁_pos)).trans
            (mul_le_of_le_one_right (hCth_nn 1).2.2.1 hτ₁_le1)
        have h2t : |α| ≤ 2 := hα.trans (by nlinarith only [hτ₁_pos, hτ₁_le1])
        exact (mul_le_mul h2t h2 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      have hin : |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ D_in := by
        linarith only [htri, hv0_d, hv1_d, hm0b, hm0m, hm1b, hm1m, hma]
      have hτ4_le : τ₁ ^ 4 ≤ τ₁ ^ 3 := by nlinarith only [hτ₁_pos, hτ₁_le1, pow_nonneg hτ₁_pos.le 3]
      calc c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ|
          ≤ τ₁ ^ 4 * D_in := by rw [hcinv]; exact mul_le_mul_of_nonneg_left hin (pow_nonneg hτ₁_pos.le 4)
        _ ≤ τ₁ ^ 3 * (D_in + D_tail) := mul_le_mul hτ4_le (by linarith only [hDtail0]) hDin0 (pow_nonneg hτ₁_pos.le 3)
        _ = (D_in + D_tail) * τ₁ ^ 3 := by ring
    · have ht12 : 12 * τ₁ ≤ |τ| := by rw [abs_of_pos (by linarith only [hτ₁_pos, hτ2])]; exact hgt12.le
      have hb := hth_tail1 1 τ ht12
      have hexp1 : Real.exp (-(π / 2) * |τ|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith only [Real.pi_pos, abs_nonneg τ])
      have hpow_le : |τ| ^ (-(1 + (1 : ℕ) : ℤ)) ≤ τ₁ ^ (-2 : ℤ) / 144 := by
        rw [show (-(1 + (1 : ℕ) : ℤ)) = (-2 : ℤ) by norm_num, zpow_neg, zpow_neg,
          show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, zpow_natCast]
        have h12τ : 0 < 12 * τ₁ := mul_pos (by norm_num) hτ₁_pos
        calc (|τ| ^ 2)⁻¹ ≤ ((12 * τ₁) ^ 2)⁻¹ :=
            inv_anti₀ (pow_pos h12τ 2) (pow_le_pow_left₀ h12τ.le ht12 2)
          _ = (τ₁ ^ 2)⁻¹ / 144 := by ring
      have hfac : |τ| ^ (-(1 + (1 : ℕ) : ℤ)) * Real.exp (-(π / 2) * |τ|) ≤ τ₁ ^ (-2 : ℤ) / 144 :=
        (mul_le_mul_of_nonneg_left hexp1 (zpow_nonneg (abs_nonneg τ) _)).trans (by rw [mul_one]; exact hpow_le)
      have ht_nn : 0 ≤ Ctail 1 := (hCtail_nn 1).1
      have hc0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
      have hτ2_le1 : τ₁ ^ 2 ≤ 1 := by nlinarith only [hτ₁_pos, hτ₁_le1]
      have h0_le : c⁻¹ * |deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ| ≤
          Ctail 1 * (CL0b + CL0m) / 144 * τ₁ ^ 3 := by
        have h := hb.1; rw [iteratedDeriv_one, mul_assoc (Ctail 1 * (CL0b + K4 * CL0m) * τ₁ ^ 3)] at h
        have h1 : |deriv (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) τ| ≤
            Ctail 1 * (CL0b + K4 * CL0m) * τ₁ ^ 3 * (τ₁ ^ (-2 : ℤ) / 144) :=
          h.trans (mul_le_mul_of_nonneg_left hfac
            (mul_nonneg (mul_nonneg ht_nn (add_nonneg hCL_nn.1 (mul_nonneg (by linarith only [hK4]) hCL_nn.2.1))) (pow_nonneg hτ₁_pos.le 3)))
        have heq : c⁻¹ * (Ctail 1 * (CL0b + K4 * CL0m) * τ₁ ^ 3 * (τ₁ ^ (-2 : ℤ) / 144)) =
            Ctail 1 * (CL0b * τ₁ ^ 2 + CL0m * (K4 * τ₁ ^ 2)) / 144 * τ₁ ^ 3 := by
          rw [hcinv, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
          field_simp [hτ₁_pos.ne']
        have h2 : Ctail 1 * (CL0b * τ₁ ^ 2 + CL0m * (K4 * τ₁ ^ 2)) / 144 * τ₁ ^ 3 ≤
            Ctail 1 * (CL0b + CL0m) / 144 * τ₁ ^ 3 := by
          have hCL : CL0b * τ₁ ^ 2 + CL0m * (K4 * τ₁ ^ 2) ≤ CL0b + CL0m := by
            have hA := mul_le_of_le_one_right hCL_nn.1 hτ2_le1
            have hB := mul_le_of_le_one_right hCL_nn.2.1 hK4t
            linarith only [hA, hB]
          have hC : Ctail 1 * (CL0b * τ₁ ^ 2 + CL0m * (K4 * τ₁ ^ 2)) / 144 ≤
              Ctail 1 * (CL0b + CL0m) / 144 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCL ht_nn) (by norm_num)
          exact mul_le_mul_of_nonneg_right hC (pow_nonneg hτ₁_pos.le 3)
        exact (mul_le_mul_of_nonneg_left h1 hc0).trans (heq ▸ h2)
      have h1_le : c⁻¹ * |deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ| ≤
          Ctail 1 * (CL1b + CL1m) / 144 * τ₁ ^ 3 := by
        have h := hb.2.1; rw [iteratedDeriv_one, mul_assoc (Ctail 1 * (CL1b + K4 * CL1m) * c⁻¹)] at h
        have h1 : |deriv (fctThetaD (v1 StripKernelChoice.star K4 c τ₁)) τ| ≤
            Ctail 1 * (CL1b + K4 * CL1m) * c⁻¹ * (τ₁ ^ (-2 : ℤ) / 144) :=
          h.trans (mul_le_mul_of_nonneg_left hfac
            (mul_nonneg (mul_nonneg ht_nn (add_nonneg hCL_nn.2.2.2.1 (mul_nonneg (by linarith only [hK4]) hCL_nn.2.2.2.2))) hc0))
        have heq : c⁻¹ * (Ctail 1 * (CL1b + K4 * CL1m) * c⁻¹ * (τ₁ ^ (-2 : ℤ) / 144)) =
            Ctail 1 * (CL1b * τ₁ ^ 3 + CL1m * (K4 * τ₁ ^ 2) * τ₁) / 144 * τ₁ ^ 3 := by
          rw [hcinv, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
          field_simp [hτ₁_pos.ne']
        have h2 : Ctail 1 * (CL1b * τ₁ ^ 3 + CL1m * (K4 * τ₁ ^ 2) * τ₁) / 144 * τ₁ ^ 3 ≤
            Ctail 1 * (CL1b + CL1m) / 144 * τ₁ ^ 3 := by
          have hCL : CL1b * τ₁ ^ 3 + CL1m * (K4 * τ₁ ^ 2) * τ₁ ≤ CL1b + CL1m := by
            have hA : CL1b * τ₁ ^ 3 ≤ CL1b :=
              mul_le_of_le_one_right hCL_nn.2.2.2.1 (pow_le_one₀ hτ₁_pos.le hτ₁_le1)
            have hB : CL1m * (K4 * τ₁ ^ 2) * τ₁ ≤ CL1m := by
              have hb1 : CL1m * (K4 * τ₁ ^ 2) ≤ CL1m := mul_le_of_le_one_right hCL_nn.2.2.2.2 hK4t
              calc CL1m * (K4 * τ₁ ^ 2) * τ₁ ≤ CL1m * 1 := mul_le_mul hb1 hτ₁_le1 hτ₁_pos.le hCL_nn.2.2.2.2
                _ = CL1m := mul_one _
            linarith only [hA, hB]
          have hC : Ctail 1 * (CL1b * τ₁ ^ 3 + CL1m * (K4 * τ₁ ^ 2) * τ₁) / 144 ≤
              Ctail 1 * (CL1b + CL1m) / 144 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCL ht_nn) (by norm_num)
          exact mul_le_mul_of_nonneg_right hC (pow_nonneg hτ₁_pos.le 3)
        exact (mul_le_mul_of_nonneg_left h1 hc0).trans (heq ▸ h2)
      have ha_le : c⁻¹ * (|α| * |deriv (fctThetaD (vAlpha 1 τ₁)) τ|) ≤
          Ctail 1 * (2 * CLa) / 144 * τ₁ ^ 3 := by
        have h := hb.2.2; rw [iteratedDeriv_one] at h
        have hfn : fctThetaD (vAlpha (τ₁ ^ 2) τ₁) = fun s => τ₁ ^ 2 * fctThetaD (vAlpha 1 τ₁) s :=
          funext fun s => (hva_eq (τ₁ ^ 2) s).1
        rw [hfn, deriv_const_mul_field, abs_mul, abs_of_pos (sq_pos_of_pos hτ₁_pos),
          mul_assoc (Ctail 1 * CLa * τ₁ ^ 2 * τ₁ ^ 3)] at h
        have h1 : τ₁ ^ 2 * |deriv (fctThetaD (vAlpha 1 τ₁)) τ| ≤
            Ctail 1 * CLa * τ₁ ^ 2 * τ₁ ^ 3 * (τ₁ ^ (-2 : ℤ) / 144) :=
          h.trans (mul_le_mul_of_nonneg_left hfac
            (mul_nonneg (mul_nonneg (mul_nonneg ht_nn hCL_nn.2.2.1) (sq_nonneg τ₁)) (pow_nonneg hτ₁_pos.le 3)))
        have h2 : |deriv (fctThetaD (vAlpha 1 τ₁)) τ| ≤ Ctail 1 * CLa * τ₁ ^ 3 * (τ₁ ^ (-2 : ℤ) / 144) :=
          le_of_mul_le_mul_left (h1.trans_eq (by ring)) (sq_pos_of_pos hτ₁_pos)
        have h3 : c⁻¹ * (|α| * (Ctail 1 * CLa * τ₁ ^ 3 * (τ₁ ^ (-2 : ℤ) / 144))) ≤
            Ctail 1 * (2 * CLa) / 144 * τ₁ ^ 3 := by
          have heq : c⁻¹ * (|α| * (Ctail 1 * CLa * τ₁ ^ 3 * (τ₁ ^ (-2 : ℤ) / 144))) =
              Ctail 1 * CLa / 144 * τ₁ ^ 3 * (τ₁ ^ 2 * |α|) := by
            rw [hcinv, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
            field_simp [hτ₁_pos.ne']
          have hα_bd : τ₁ ^ 2 * |α| ≤ 2 := by
            have h2t : |α| ≤ 2 := hα.trans (by nlinarith only [hτ₁_pos, hτ₁_le1])
            calc τ₁ ^ 2 * |α| ≤ 1 * 2 := mul_le_mul hτ2_le1 h2t (abs_nonneg _) zero_le_one
              _ = 2 := one_mul 2
          rw [heq]
          calc Ctail 1 * CLa / 144 * τ₁ ^ 3 * (τ₁ ^ 2 * |α|)
              ≤ Ctail 1 * CLa / 144 * τ₁ ^ 3 * 2 :=
                mul_le_mul_of_nonneg_left hα_bd (mul_nonneg (div_nonneg (mul_nonneg ht_nn hCL_nn.2.2.1) (by norm_num)) (pow_nonneg hτ₁_pos.le 3))
            _ = Ctail 1 * (2 * CLa) / 144 * τ₁ ^ 3 := by ring
        exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) hc0).trans h3
      have htail : c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c α τ₁)) τ| ≤ D_tail * τ₁ ^ 3 := by
        have hsum := add_le_add (add_le_add h0_le h1_le) ha_le
        have hD : D_tail * τ₁ ^ 3 =
            Ctail 1 * (CL0b + CL0m) / 144 * τ₁ ^ 3 + Ctail 1 * (CL1b + CL1m) / 144 * τ₁ ^ 3 +
              Ctail 1 * (2 * CLa) / 144 * τ₁ ^ 3 := by
          change Ctail 1 * (CL0b + CL0m + CL1b + CL1m + 2 * CLa) / 144 * τ₁ ^ 3 = _
          ring
        linarith only [htri_mul, hsum, hD]
      exact htail.trans (mul_le_mul_of_nonneg_right (by linarith only [hDin0]) (pow_nonneg hτ₁_pos.le 3))
  exact hbd_deriv

set_option maxHeartbeats 400000 in
/-- **Instantiation of `FctPhaseBox` and `(b1)` data** for `concretePhiTilde K4 ε c`,
with all structural constants `(ellMin, τ_lim_box)` independent of `(K4, ε, c)` for `K4 τ₁² ≤ 1`. -/
theorem concretePhaseBox_exist :
    ∃ (ellMin τ_lim_box : ℝ), 0 < ellMin ∧ 0 < τ_lim_box ∧ τ_lim_box ≤ 1 / 20 ∧
      ∀ {K4 ε c : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → 0 < c →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        τ₁ ≤ τ_lim_box → K4 * τ₁ ^ 2 ≤ 1 →
        ∃ (B d : ℝ × ℝ × ℝ → ℝ) (R Z : (ℝ × ℝ × ℝ) × ℝ → ℝ) (S : ChartSetup (ℝ × ℝ × ℝ)),
          S.Ω = OmT τ₁ ∧ S.ℓ = (fun p : ℝ × ℝ × ℝ => p.1) ∧
          S.B = B ∧ S.d = d ∧ S.R = R ∧ S.Z = Z ∧
          FctPhaseBox (concretePhiTilde K4 ε c) (concretePhaseDom ellMin ε c) (concreteTau0 ε c S) ∧
          (∀ p ∈ concretePhaseDom ellMin ε c,
            let q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
            concreteTau0 ε c S p < 2 * τ₁ ∧
            S.A q ∈ Ioo (0 : ℝ) 2.9 ∧
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p = τ₁ ^ 2 * S.A q ∧
            fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (1, 0) =
              S.V (q, S.A q) ∧
            fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (0, 1) =
              c⁻¹ * fctThetaD (vAlpha 1 τ₁) (concreteTau0 ε c S p) /
                Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p)) := by
  obtain ⟨M_cfu, cB, cd, cR, cD, cZ, cV, C0, τ_lim_cfu, hM0, hcB, hcd, hcR, hcD, hcZ, hcV, hC0,
    hτlim_pos, hτlim_le, hcfu⟩ := concrete_cfu_exist
  let τD := (fct_comp_D_part1 StripKernelChoice.star).choose
  obtain ⟨hτD_pos, hτD_le, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    (fct_comp_D_part1 StripKernelChoice.star).choose_spec
  obtain ⟨Cθ, hCθ0, hθ'⟩ := ct_outer_theta_deriv_bound
  obtain ⟨Dv, τv, hDv0, hτv0, hv_bd⟩ := concrete_thetaD_deriv_bd
  obtain ⟨δQ, hδQ0, hδQ14, hmQ_ge⟩ := mQ_ge_point8
  set ellMin : ℝ := 2 * (cB * C0 + 1) with hellMin
  have hellMin_pos : 0 < ellMin := by positivity
  set D1 : ℝ := |ctTheta1 1| + |ctTheta1 (-1)| + Cθ + Dv
  have hD1_0 : 0 ≤ D1 := by positivity
  -- Ensure `τ_lim_box` satisfies all smallness conditions cleanly
  set τ_ell : ℝ := (2 * ellMin + 1) ^ (-(1 / 2 : ℝ))
  set τ_D1 : ℝ := (10 * (D1 + 1))⁻¹
  set τ_lim_box : ℝ := min (min τ_lim_cfu (min τD τv)) (min (min (δQ / 2) τ_ell) τ_D1)
  have hτ_ell0 : 0 < τ_ell := Real.rpow_pos_of_pos (by positivity) _
  have hτ_D10 : 0 < τ_D1 := by positivity
  have hτlim_box_pos : 0 < τ_lim_box := by positivity
  have hτlim_box_le : τ_lim_box ≤ 1 / 20 := ((min_le_left _ _).trans (min_le_left _ _)).trans hτlim_le
  refine ⟨ellMin, τ_lim_box, hellMin_pos, hτlim_box_pos, hτlim_box_le, ?_⟩
  intro K4 ε c hK4 hε hc τ₁ hτ₁_box hK4t
  have hτ₁_pos : 0 < τ₁ := Real.rpow_pos_of_pos hc _
  have hτ₁_cfu : τ₁ ≤ τ_lim_cfu := hτ₁_box.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ₁_τD : τ₁ ≤ τD := hτ₁_box.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτ₁_τv : τ₁ ≤ τv := hτ₁_box.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hτ₁_δQ : τ₁ ≤ δQ / 2 := hτ₁_box.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hτ₁_ell : τ₁ ≤ τ_ell := hτ₁_box.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hτ₁_D1 : τ₁ ≤ τ_D1 := hτ₁_box.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτ₁_1 : τ₁ ≤ 1 := (hτ₁_cfu.trans hτlim_le).trans (by norm_num)
  have hτsq_eq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  have hcτ : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num [Real.rpow_neg_one]
    rw [this]; field_simp
  have hcinv : c⁻¹ = τ₁ ^ 4 := by
    calc c⁻¹ = τ₁ ^ 4 * c * c⁻¹ := by rw [hcτ, one_mul]
      _ = τ₁ ^ 4 := by field_simp [hc.ne']
  have hτ₁_sq_ell : ellMin * τ₁ ^ 2 ≤ 1 / 2 := by
    have h1 : τ₁ ^ 2 ≤ τ_ell ^ 2 := pow_le_pow_left₀ hτ₁_pos.le hτ₁_ell 2
    have h2 : τ_ell ^ 2 = (2 * ellMin + 1)⁻¹ := by
      simp only [τ_ell]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num [Real.rpow_neg_one]
    rw [h2] at h1
    have hpos : (0 : ℝ) < 2 * ellMin + 1 := by positivity
    calc ellMin * τ₁ ^ 2 ≤ ellMin * (2 * ellMin + 1)⁻¹ := mul_le_mul_of_nonneg_left h1 hellMin_pos.le
      _ ≤ 1 / 2 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]; linarith
  have hτ₁_D1_10 : D1 * τ₁ ≤ 1 / 10 := by
    have hpos : (0 : ℝ) < 10 * (D1 + 1) := by positivity
    calc D1 * τ₁ ≤ (D1 + 1) * τ_D1 := mul_le_mul (by linarith) hτ₁_D1 hτ₁_pos.le (by positivity)
      _ = 1 / 10 := by simp only [τ_D1]; field_simp [hpos.ne']
  obtain ⟨T, -, hT_id, B, d, R, Z, S, hSΩ, hSℓ, hSr, hSε, hcBs, hcds, hcRs, hcDs, hcZs, hcVs,
    hSB, hSd, hSR, hSZ, hout⟩ := hcfu hK4 hε hc hτ₁_cfu hK4t
  refine ⟨B, d, R, Z, S, hSΩ, hSℓ, hSB, hSd, hSR, hSZ, ?_⟩
  -- Shared geometric facts for `p ∈ concretePhaseDom ellMin ε c`
  have hp_facts : ∀ p ∈ concretePhaseDom ellMin ε c,
      let q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
      q ∈ S.Ω ∧ 0 < S.B q ∧ S.B q < 3.2 ∧ S.A q ∈ Ioo (0 : ℝ) 2.9 ∧
        0 < S.Z (q, S.A q) ∧ S.Z (q, S.A q) < 4 ∧
        0 < concreteTau0 ε c S p ∧ concreteTau0 ε c S p < 2 * τ₁ := by
    intro p hp q
    have hqOm : q ∈ OmT τ₁ := concreteEll1_mem_OmT hc hellMin_pos.le hp
    have hqΩ : q ∈ S.Ω := hSΩ ▸ hqOm
    have hB_est : |S.B q - 12 / π ^ 2 * S.ℓ q| ≤ cB * C0 * τ₁ ^ 2 := by
      have h1 := JB.apply_le hout.1.2 hqOm
      rw [← hSB, ← hSℓ] at h1
      exact h1.trans_eq (mul_assoc _ _ _).symm
    have hℓ_eq : S.ℓ q = concreteEll1 ε c p.1 := by simp [hSℓ, q]
    have hB_abs := abs_le.mp (hℓ_eq ▸ hB_est)
    have hℓ_lo : ellMin * τ₁ ^ 2 < concreteEll1 ε c p.1 := by rw [hτsq_eq]; exact hp.1
    have hℓ_hi : concreteEll1 ε c p.1 < 2.55 := hp.2.1
    have hpi_lo : (3.14 : ℝ) < π := Real.pi_gt_d2
    have hpi_hi : π < (3.15 : ℝ) := Real.pi_lt_d2
    have hpi2_hi : π ^ 2 < 10 := by nlinarith only [Real.pi_pos, hpi_hi]
    have hpi2_lo : 9.8 < π ^ 2 := by nlinarith only [hpi_lo]
    have hc12_lo : (1.2 : ℝ) < 12 / π ^ 2 := by
      rw [lt_div_iff₀ (pow_pos Real.pi_pos 2)]; nlinarith only [hpi2_hi]
    have hc12_hi : 12 / π ^ 2 < (1.23 : ℝ) := by
      rw [div_lt_iff₀ (pow_pos Real.pi_pos 2)]; nlinarith only [hpi2_lo]
    have hB_pos : 0 < S.B q := by
      have h1 : 1.2 * (ellMin * τ₁ ^ 2) < 12 / π ^ 2 * concreteEll1 ε c p.1 :=
        mul_lt_mul'' hc12_lo hℓ_lo (by norm_num) (mul_nonneg hellMin_pos.le (sq_nonneg _))
      have h2 : 12 / π ^ 2 * concreteEll1 ε c p.1 - cB * C0 * τ₁ ^ 2 ≤ S.B q := by
        linarith only [hB_abs.1]
      have h3 : cB * C0 * τ₁ ^ 2 < 1.2 * (ellMin * τ₁ ^ 2) := by
        have hsq : 0 < τ₁ ^ 2 := sq_pos_of_pos hτ₁_pos
        have hm0 : 0 ≤ cB * C0 := mul_nonneg hcB hC0
        calc cB * C0 * τ₁ ^ 2 < (1.2 * 2 * (cB * C0 + 1)) * τ₁ ^ 2 :=
            mul_lt_mul_of_pos_right (by linarith only [hm0]) hsq
          _ = 1.2 * (ellMin * τ₁ ^ 2) := by rw [hellMin]; ring
      linarith only [h1, h2, h3]
    have hB_hi : S.B q < 3.2 := by
      have hcB_small : cB * C0 * τ₁ ^ 2 ≤ 1 / 100 := by
        simpa only [hcBs, hSε, ← mul_assoc] using S.hcB
      have hℓ_pos : 0 ≤ concreteEll1 ε c p.1 :=
        (mul_nonneg hellMin_pos.le (sq_nonneg _)).trans hℓ_lo.le
      have h1 : 12 / π ^ 2 * concreteEll1 ε c p.1 < 1.23 * 2.55 :=
        mul_lt_mul'' hc12_hi hℓ_hi (by positivity) hℓ_pos
      linarith only [hB_abs.2, h1, hcB_small]
    have hd_bnd : |S.d q - dStar| ≤ 1 / 100 := by
      have h1 := JB.apply_le hout.2.2.1.2 hqOm
      rw [← hSd] at h1
      have hcd_small : cd * (C0 * τ₁ ^ 2) ≤ 1 / 100 := by
        simpa only [hcds, hSε] using S.hcd
      exact h1.trans hcd_small
    have hd_abs := abs_le.mp hd_bnd
    have hd_lo : (0.92 : ℝ) ≤ S.d q := by
      linarith only [hd_abs.1, dStar_bounds.1]
    have hd_hi : S.d q ≤ (0.95 : ℝ) := by
      linarith only [hd_abs.2, dStar_bounds.2]
    have hA_pos : 0 < S.A q := by
      unfold ChartSetup.A; positivity
    have hA_hi : S.A q < 2.9 := by
      unfold ChartSetup.A
      have hd2 : S.d q ^ 2 ≤ 0.9025 := by nlinarith only [hd_lo, hd_hi]
      nlinarith only [hB_pos, hB_hi, hd2]
    have hAY : (q, S.A q) ∈ S.Ω ×ˢ Yint := ⟨hqΩ, by constructor <;> linarith only [hA_pos, hA_hi]⟩
    have hZ_D : S.Z (q, S.A q) * S.D (q, S.Z (q, S.A q)) ^ 2 = S.A q := S.Z_D hAY
    have hZ_mem : S.Z (q, S.A q) ∈ Ioo (-1 : ℝ) 6 := S.Z_mem hAY
    have hD_bnd := S.D_bounds (q := (q, S.Z (q, S.A q))) ⟨hqΩ, hZ_mem⟩
    have hD_pos : 0 < S.D (q, S.Z (q, S.A q)) := by linarith only [hD_bnd.1]
    have hZ_pos : 0 < S.Z (q, S.A q) := by nlinarith only [sq_pos_of_pos hD_pos, hZ_D, hA_pos]
    have hZ_hi : S.Z (q, S.A q) < 4 := by
      have hD2 : (0.92 : ℝ) ^ 2 ≤ S.D (q, S.Z (q, S.A q)) ^ 2 := by nlinarith only [hD_bnd.1]
      nlinarith only [hZ_pos, hA_hi, hZ_D, hD2]
    have htau0_pos : 0 < concreteTau0 ε c S p := by
      unfold concreteTau0; exact mul_pos hτ₁_pos (Real.sqrt_pos.mpr hZ_pos)
    have htau0_hi : concreteTau0 ε c S p < 2 * τ₁ := by
      unfold concreteTau0
      have hsq : Real.sqrt (S.Z (q, S.A q)) < 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num; exact hZ_hi
      nlinarith only [hτ₁_pos, hsq]
    exact ⟨hqΩ, hB_pos, hB_hi, ⟨hA_pos, hA_hi⟩, hZ_pos, hZ_hi, htau0_pos, htau0_hi⟩
  -- Key scaled identity and derivative for `0 < τ ≤ 2.4 τ₁`
  have hPhi_chart : ∀ p ∈ concretePhaseDom ellMin ε c, ∀ {τ : ℝ}, 0 < τ → τ ≤ 2.4 * τ₁ →
      let q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
      let x := τ / τ₁
      let W := x * S.D (q, x ^ 2)
      concretePhiTilde K4 ε c τ p = τ₁ ^ 3 * (S.A q * W - W ^ 3 / 3) := by
    intro p _ τ hτ0 hτ24 q x W
    have hx0 : 0 ≤ x := (div_pos hτ0 hτ₁_pos).le
    have hx24 : x ≤ 2.4 := (div_le_iff₀ hτ₁_pos).mpr hτ24
    have hqΩ : q ∈ S.Ω := by
      rw [hSΩ]; exact concreteEll1_mem_OmT hc hellMin_pos.le (by assumption)
    have hx2_mem : x ^ 2 ∈ Ioo (-1 : ℝ) 6 := by
      constructor
      · linarith only [sq_nonneg x]
      · have hsq24 : x ^ 2 ≤ 2.4 ^ 2 := by nlinarith only [hx0, hx24]
        linarith only [hsq24]
    have h1 := hT_id (lam := 1) (L1 := p.1) (α := p.2) hx0 hx24
    have hτx : τ₁ * x = τ := mul_div_cancel₀ τ hτ₁_pos.ne'
    have h2 := S.hid (q := (q, x ^ 2)) ⟨hqΩ, hx2_mem⟩
    rw [hSℓ, hSr] at h2
    have h1' : τ₁ ^ 3 * (x * (concreteEll1 ε c p.1 - π ^ 2 / 36 * x ^ 2 + T.r τ₁ K4 (q, x ^ 2))) =
        concretePhiLambda K4 ε c 1 τ p.1 p.2 := by
      rw [← hτx]
      dsimp only [q]
      unfold concreteEll1
      exact h1
    unfold concretePhiTilde
    rw [← h1', h2]
    dsimp only [W]
    ring
  -- Formula for `W'(x) ≥ 0.84` on `0 ≤ x ≤ 2`
  have hW_deriv : ∀ p ∈ concretePhaseDom ellMin ε c,
      let q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
      let W : ℝ → ℝ := fun x => x * S.D (q, x ^ 2)
      ∀ x ∈ Ioo (-0.5 : ℝ) 2.2,
        HasDerivAt W (S.D (q, x ^ 2) + 2 * x ^ 2 * fderiv ℝ S.D (q, x ^ 2) (0, 1)) x ∧
        (0 ≤ x → x ≤ 2 → 0.84 ≤ S.D (q, x ^ 2) + 2 * x ^ 2 * fderiv ℝ S.D (q, x ^ 2) (0, 1)) := by
    intro p hp q W x hx
    have hqΩ : q ∈ S.Ω := (hp_facts p hp).1
    have hx2_mem : x ^ 2 ∈ Ioo (-1 : ℝ) 6 := by
      have habs : |x| < 2.2 := abs_lt.mpr ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
      have h1 : x ^ 2 < 4.84 := by nlinarith only [habs, sq_abs x, abs_nonneg x]
      exact ⟨by linarith only [sq_nonneg x], by linarith only [h1]⟩
    have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
    have hD_at : DifferentiableAt ℝ S.D (q, x ^ 2) :=
      S.D_diff.differentiableAt (hO.mem_nhds ⟨hqΩ, hx2_mem⟩)
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x :=
      (hasDerivAt_pow 2 x).congr_deriv (by simp [pow_one])
    have hpair : HasDerivAt (fun u : ℝ => (q, u ^ 2)) (0, 2 * x) x :=
      (hasDerivAt_const x q).prodMk hsq
    have hcomp : HasDerivAt (fun u : ℝ => S.D (q, u ^ 2)) (fderiv ℝ S.D (q, x ^ 2) (0, 1) * (2 * x)) x :=
      (hD_at.hasFDerivAt.comp_hasDerivAt x hpair).congr_deriv (by
        have hsmul : ((0 : ℝ × ℝ × ℝ), 2 * x) = (2 * x) • ((0 : ℝ × ℝ × ℝ), (1 : ℝ)) := by
          ext <;> simp
        rw [hsmul, map_smul, smul_eq_mul, mul_comm])
    have hW := (hasDerivAt_id x).mul hcomp
    refine ⟨hW.congr_deriv (by dsimp only [id_eq]; ring), fun hx0 hx2 => ?_⟩
    have hDb := (S.D_bounds (q := (q, x ^ 2)) ⟨hqΩ, hx2_mem⟩).1
    have hDz := abs_le.mp (S.Dz_bound (q := (q, x ^ 2)) ⟨hqΩ, hx2_mem⟩)
    have hx2_4 : x ^ 2 ≤ 4 := by nlinarith only [hx0, hx2]
    have hmul : -(1 / 100 : ℝ) * (2 * 4) ≤ 2 * x ^ 2 * fderiv ℝ S.D (q, x ^ 2) (0, 1) := by
      nlinarith only [sq_nonneg x, hx2_4, hDz.1, hDz.2]
    linarith only [hDb, hmul]
  -- Formula for `fctPhTau` on `(0, 2.1 * τ₁)` via `W(x) = x S.D(q, x²)`
  have hPhTau_chart : ∀ p ∈ concretePhaseDom ellMin ε c, ∀ {τ : ℝ}, 0 < τ → τ < 2.1 * τ₁ →
      let q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
      let x := τ / τ₁
      fctPhTau (concretePhiTilde K4 ε c) τ p =
        τ₁ ^ 2 * (S.A q - (x * S.D (q, x ^ 2)) ^ 2) *
          (S.D (q, x ^ 2) + 2 * x ^ 2 * fderiv ℝ S.D (q, x ^ 2) (0, 1)) := by
    intro p hp τ hτ0 hτ21 q x
    have hO : IsOpen (Ioo (0 : ℝ) (2.1 * τ₁)) := isOpen_Ioo
    have hev : (fun u : ℝ => concretePhiTilde K4 ε c u p) =ᶠ[𝓝 τ]
        fun u => τ₁ ^ 3 * (S.A q * ((u / τ₁) * S.D (q, (u / τ₁) ^ 2)) -
          ((u / τ₁) * S.D (q, (u / τ₁) ^ 2)) ^ 3 / 3) := by
      filter_upwards [hO.mem_nhds ⟨hτ0, hτ21⟩] with u hu
      exact hPhi_chart p hp hu.1 (by linarith only [hu.2, hτ₁_pos])
    have hx_pos : 0 < x := div_pos hτ0 hτ₁_pos
    have hx_lt21 : x < 2.1 := (div_lt_iff₀ hτ₁_pos).mpr hτ21
    have hx_mem : x ∈ Ioo (-0.5 : ℝ) 2.2 := ⟨by linarith only [hx_pos], by linarith only [hx_lt21]⟩
    have hW_at := (hW_deriv p hp x hx_mem).1
    set Wx := x * S.D (q, x ^ 2)
    set Wx' := S.D (q, x ^ 2) + 2 * x ^ 2 * fderiv ℝ S.D (q, x ^ 2) (0, 1)
    have hW_τ : HasDerivAt (fun u : ℝ => (u / τ₁) * S.D (q, (u / τ₁) ^ 2)) (Wx' * τ₁⁻¹) τ := by
      have hc := hW_at.comp τ ((hasDerivAt_id τ).div_const τ₁)
      dsimp only [Function.comp_def, id_eq] at hc
      exact hc.congr_deriv (by ring)
    have hP_at : HasDerivAt (fun u => τ₁ ^ 3 * (S.A q * ((u / τ₁) * S.D (q, (u / τ₁) ^ 2)) -
        ((u / τ₁) * S.D (q, (u / τ₁) ^ 2)) ^ 3 / 3))
        (τ₁ ^ 3 * (S.A q * (Wx' * τ₁⁻¹) - Wx ^ 2 * (Wx' * τ₁⁻¹))) τ := by
      have hcube : HasDerivAt (fun u => ((u / τ₁) * S.D (q, (u / τ₁) ^ 2)) ^ 3 / 3)
          (3 * Wx ^ 2 * (Wx' * τ₁⁻¹) / 3) τ :=
        ((hW_τ.pow 3).div_const 3).congr_deriv (by dsimp only [Wx]; ring)
      exact (((hW_τ.const_mul (S.A q)).sub hcube).const_mul (τ₁ ^ 3)).congr_deriv (by ring)
    have hd_phi : HasDerivAt (fun u => concretePhiTilde K4 ε c u p)
        (fctPhTau (concretePhiTilde K4 ε c) τ p) τ := by
      have hd_p := concretePhiTilde_hasFDerivAt (ε := ε) hK4 hc hτ₁_τD hτ0 p
      have hτp : HasDerivAt (fun u : ℝ => (u, p)) ((1 : ℝ), (0 : ℝ × ℝ)) τ :=
        (hasDerivAt_id τ).prodMk (hasDerivAt_const τ p)
      have hc' := hd_p.comp_hasDerivAt τ hτp
      unfold fctPhTau
      rw [hd_p.fderiv]
      exact hc'
    rw [(hd_phi.congr_of_eventuallyEq hev.symm).unique hP_at]
    change τ₁ ^ 3 * (S.A q * (Wx' * τ₁⁻¹) - Wx ^ 2 * (Wx' * τ₁⁻¹)) = τ₁ ^ 2 * (S.A q - Wx ^ 2) * Wx'
    field_simp [hτ₁_pos.ne']
  -- Package `box : FctPhaseBox ...`
  have hbox : FctPhaseBox (concretePhiTilde K4 ε c) (concretePhaseDom ellMin ε c) (concreteTau0 ε c S) :=
    { isOpen := isOpen_concretePhaseDom ellMin ε c
      smooth := (concretePhiLambda_contDiffOn hK4 hc hτ₁_τD).mono
        (Set.prod_mono Subset.rfl (Set.subset_univ _))
      dL := fun τ hτ p _ => by
        have hd := concretePhiTilde_hasFDerivAt (ε := ε) hK4 hc hτ₁_τD hτ p
        rw [hd.fderiv]
        change (_ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
          τ • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          _ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (0, (1, 0)) = τ
        simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
          mul_zero, mul_one, zero_add, add_zero]
      pos := fun p hp => (hp_facts p hp).2.2.2.2.2.2.1
      crit := fun p hp => by
        set q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
        set τ₀ := concreteTau0 ε c S p
        obtain ⟨hqΩ, _, _, hA_mem, hZ_pos, _, hτ0_pos, hτ0_2⟩ := hp_facts p hp
        rw [hPhTau_chart p hp hτ0_pos (by linarith only [hτ0_2, hτ₁_pos])]
        have hτZ : (τ₀ / τ₁) ^ 2 = S.Z (q, S.A q) := by
          dsimp only [τ₀]; unfold concreteTau0
          rw [mul_div_cancel_left₀ _ hτ₁_pos.ne', Real.sq_sqrt hZ_pos.le]
        have hW0_sq : ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2 = S.A q := by
          calc ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2
              = (τ₀ / τ₁) ^ 2 * S.D (q, (τ₀ / τ₁) ^ 2) ^ 2 := by ring
            _ = S.Z (q, S.A q) * S.D (q, S.Z (q, S.A q)) ^ 2 := by rw [hτZ]
            _ = S.A q := S.Z_D ⟨hqΩ, by constructor <;> linarith only [hA_mem.1, hA_mem.2]⟩
        rw [hW0_sq, sub_self, mul_zero, zero_mul]
      nondeg := fun p hp => by
        set q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
        set τ₀ := concreteTau0 ε c S p
        obtain ⟨hqΩ, _, _, hA_mem, hZ_pos, _, hτ0_pos, hτ0_2⟩ := hp_facts p hp
        have hO : IsOpen (Ioo (0 : ℝ) (2.1 * τ₁)) := isOpen_Ioo
        have hmem : τ₀ ∈ Ioo (0 : ℝ) (2.1 * τ₁) := ⟨hτ0_pos, by linarith only [hτ0_2, hτ₁_pos]⟩
        have hx0_mem : τ₀ / τ₁ ∈ Ioo (-0.5 : ℝ) 2.2 :=
          ⟨by have h0x := div_pos hτ0_pos hτ₁_pos; linarith only [h0x],
           by have h2x : τ₀ / τ₁ < 2 := (div_lt_iff₀ hτ₁_pos).mpr hτ0_2; linarith only [h2x]⟩
        have hW_at := (hW_deriv p hp (τ₀ / τ₁) hx0_mem).1
        have hW'_ge := (hW_deriv p hp (τ₀ / τ₁) hx0_mem).2
          (div_pos hτ0_pos hτ₁_pos).le ((div_lt_iff₀ hτ₁_pos).mpr hτ0_2).le
        have hW_τ := hW_at.comp τ₀ ((hasDerivAt_id τ₀).div_const τ₁)
        set W : ℝ → ℝ := fun u => (u / τ₁) * S.D (q, (u / τ₁) ^ 2)
        set W' : ℝ → ℝ := fun u => S.D (q, (u / τ₁) ^ 2) + 2 * (u / τ₁) ^ 2 * fderiv ℝ S.D (q, (u / τ₁) ^ 2) (0, 1)
        have hW'_diff : DifferentiableAt ℝ W' τ₀ := by
          have hOD : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
          have hD_cd : ContDiffOn ℝ 16 S.D (S.Ω ×ˢ Ioo (-1 : ℝ) 6) :=
            (S.out.2.2.2.2.2.2.1.1.add (contDiffOn_const (c := dStar))).congr
              fun y _ => by simp [ChartSetup.D]
          have hf_cd : ContDiffOn ℝ 15 (fun z : ℝ => fderiv ℝ S.D (q, z) (0, 1)) (Ioo (-1 : ℝ) 6) := by
            have hfd : ContDiffOn ℝ 15 (fun y => fderiv ℝ S.D y) (S.Ω ×ˢ Ioo (-1 : ℝ) 6) :=
              hD_cd.fderiv_of_isOpen hOD (by norm_num)
            have hline : ContDiffOn ℝ 15 (fun z : ℝ => (q, z)) (Ioo (-1 : ℝ) 6) :=
              contDiffOn_const.prodMk contDiffOn_id
            exact (hfd.comp hline fun z hz => ⟨hqΩ, hz⟩).clm_apply contDiffOn_const
          have hz0_mem : (τ₀ / τ₁) ^ 2 ∈ Ioo (-1 : ℝ) 6 := by
            have h0x : 0 < τ₀ / τ₁ := div_pos hτ0_pos hτ₁_pos
            have h2x : τ₀ / τ₁ < 2 := (div_lt_iff₀ hτ₁_pos).mpr hτ0_2
            have h1 : (τ₀ / τ₁) ^ 2 < 4 := by nlinarith only [h0x, h2x]
            exact ⟨by linarith only [sq_nonneg (τ₀ / τ₁)], by linarith only [h1]⟩
          have hDz_at := (hf_cd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hz0_mem)
          have hD_at := (hD_cd.differentiableOn (by norm_num)).differentiableAt
            (hOD.mem_nhds (show ((q, (τ₀ / τ₁) ^ 2)) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 from ⟨hqΩ, hz0_mem⟩))
          have hq_sq : DifferentiableAt ℝ (fun u : ℝ => (q, (u / τ₁) ^ 2)) τ₀ :=
            (differentiableAt_const _).prodMk ((differentiableAt_id.div_const _).pow 2)
          have hz_sq : DifferentiableAt ℝ (fun u : ℝ => (u / τ₁) ^ 2) τ₀ :=
            (differentiableAt_id.div_const _).pow 2
          have hDz_u : DifferentiableAt ℝ ((fun z : ℝ => fderiv ℝ S.D (q, z) (0, 1)) ∘
              fun u : ℝ => (u / τ₁) ^ 2) τ₀ :=
            hDz_at.comp τ₀ hz_sq
          exact (hD_at.comp τ₀ hq_sq).add ((hz_sq.const_mul 2).mul hDz_u)
        have hA_zero : S.A q - W τ₀ ^ 2 = 0 := by
          have hτZ : (τ₀ / τ₁) ^ 2 = S.Z (q, S.A q) := by
            dsimp only [τ₀]; unfold concreteTau0; rw [mul_div_cancel_left₀ _ hτ₁_pos.ne', Real.sq_sqrt hZ_pos.le]
          calc S.A q - W τ₀ ^ 2 = S.A q - S.Z (q, S.A q) * S.D (q, S.Z (q, S.A q)) ^ 2 := by
                simp only [W]; rw [← hτZ]; ring
            _ = 0 := by rw [S.Z_D ⟨hqΩ, by constructor <;> linarith only [hA_mem.1, hA_mem.2]⟩, sub_self]
        have hAW_der : HasDerivAt (fun u => τ₁ ^ 2 * (S.A q - W u ^ 2))
            (τ₁ ^ 2 * (-(2 * W τ₀ * (W' τ₀ * τ₁⁻¹)))) τ₀ := by
          have hW_τ' : HasDerivAt W (W' τ₀ * τ₁⁻¹) τ₀ := by
            dsimp only [W, W']
            have hc := hW_at.comp τ₀ ((hasDerivAt_id τ₀).div_const τ₁)
            dsimp only [Function.comp_def, id_eq] at hc
            exact hc.congr_deriv (by ring)
          exact (((hW_τ'.pow 2).const_sub (S.A q)).const_mul (τ₁ ^ 2)).congr_deriv (by ring)
        have hprod := hAW_der.mul hW'_diff.hasDerivAt
        have hev : (fun τ => fctPhTau (concretePhiTilde K4 ε c) τ p) =ᶠ[𝓝 τ₀]
            fun u => τ₁ ^ 2 * (S.A q - W u ^ 2) * W' u := by
          filter_upwards [hO.mem_nhds hmem] with u hu using hPhTau_chart p hp hu.1 hu.2
        have hder_0 : deriv (fun τ => fctPhTau (concretePhiTilde K4 ε c) τ p) τ₀ =
            deriv ((fun u => τ₁ ^ 2 * (S.A q - W u ^ 2)) * W') τ₀ := hev.deriv_eq
        rw [hder_0, hprod.deriv, hA_zero, mul_zero, zero_mul, add_zero]
        have hW0_pos : 0 < W τ₀ := by
          have hz0_mem : (τ₀ / τ₁) ^ 2 ∈ Ioo (-1 : ℝ) 6 := by
            have h0x : 0 < τ₀ / τ₁ := div_pos hτ0_pos hτ₁_pos
            have h2x : τ₀ / τ₁ < 2 := (div_lt_iff₀ hτ₁_pos).mpr hτ0_2
            exact ⟨by linarith only [sq_nonneg (τ₀ / τ₁)], by nlinarith only [h0x, h2x]⟩
          have hDb := (S.D_bounds (q := (q, (τ₀ / τ₁) ^ 2)) ⟨hqΩ, hz0_mem⟩).1
          exact mul_pos (div_pos hτ0_pos hτ₁_pos) (by linarith only [hDb])
        have hW'_pos : 0 < W' τ₀ := by linarith only [hW'_ge]
        have hmul_pos : 0 < 2 * W τ₀ * W' τ₀ ^ 2 * τ₁ := by positivity
        calc τ₁ ^ 2 * -(2 * W τ₀ * (W' τ₀ * τ₁⁻¹)) * W' τ₀
            = -(2 * W τ₀ * W' τ₀ ^ 2 * τ₁) := by field_simp [hτ₁_pos.ne']
          _ < 0 := by linarith only [hmul_pos]
      unique := fun p hp τ hτ0 hcrit => by
        set q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
        set τ₀ := concreteTau0 ε c S p
        obtain ⟨hqΩ, _, _, hA_mem, hZ_pos, _, hτ0_pos, hτ0_2⟩ := hp_facts p hp
        rcases lt_or_ge τ (2 * τ₁) with hlt2 | hge2
        · rw [hPhTau_chart p hp hτ0 (by linarith only [hlt2, hτ₁_pos])] at hcrit
          have hx_pos : 0 < τ / τ₁ := div_pos hτ0 hτ₁_pos
          have hx_lt2 : τ / τ₁ < 2 := (div_lt_iff₀ hτ₁_pos).mpr hlt2
          have hW'_ge := (hW_deriv p hp (τ / τ₁) ⟨by linarith only [hx_pos], by linarith only [hx_lt2]⟩).2 hx_pos.le hx_lt2.le
          have hA_eq : ((τ / τ₁) * S.D (q, (τ / τ₁) ^ 2)) ^ 2 = S.A q := by
            rcases mul_eq_zero.mp hcrit with h1 | h2
            · rcases mul_eq_zero.mp h1 with ht2 | hsub
              · exact absurd ht2 (pow_ne_zero 2 hτ₁_pos.ne')
              · linarith only [hsub]
            · linarith only [h2, hW'_ge]
          have hz_mem : (τ / τ₁) ^ 2 ∈ Ioo (-1 : ℝ) 6 :=
            ⟨by linarith only [sq_nonneg (τ / τ₁)], by nlinarith only [hx_pos, hx_lt2]⟩
          have hW_pos : 0 < (τ / τ₁) * S.D (q, (τ / τ₁) ^ 2) :=
            mul_pos hx_pos (by linarith only [(S.D_bounds (q := (q, (τ / τ₁) ^ 2)) ⟨hqΩ, hz_mem⟩).1])
          have hW0_sq : ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2 = S.A q := by
            have hτZ : (τ₀ / τ₁) ^ 2 = S.Z (q, S.A q) := by
              dsimp only [τ₀]; unfold concreteTau0; rw [mul_div_cancel_left₀ _ hτ₁_pos.ne', Real.sq_sqrt hZ_pos.le]
            calc ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2
                = (τ₀ / τ₁) ^ 2 * S.D (q, (τ₀ / τ₁) ^ 2) ^ 2 := by ring
              _ = S.Z (q, S.A q) * S.D (q, S.Z (q, S.A q)) ^ 2 := by rw [hτZ]
              _ = S.A q := S.Z_D ⟨hqΩ, by constructor <;> linarith only [hA_mem.1, hA_mem.2]⟩
          have hW0_pos : 0 < (τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2) := by
            have h0x : 0 < τ₀ / τ₁ := div_pos hτ0_pos hτ₁_pos
            have hτ0x := (div_lt_iff₀ hτ₁_pos).mpr hτ0_2
            have hz0_mem : (τ₀ / τ₁) ^ 2 ∈ Ioo (-1 : ℝ) 6 :=
              ⟨by linarith only [sq_nonneg (τ₀ / τ₁)], by nlinarith only [h0x, hτ0x]⟩
            exact mul_pos h0x (by linarith only [(S.D_bounds (q := (q, (τ₀ / τ₁) ^ 2)) ⟨hqΩ, hz0_mem⟩).1])
          have hW_eq : (τ / τ₁) * S.D (q, (τ / τ₁) ^ 2) = (τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2) := by
            have hsq : ((τ / τ₁) * S.D (q, (τ / τ₁) ^ 2)) ^ 2 = ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2 := by
              rw [hA_eq, hW0_sq]
            nlinarith only [hsq, hW_pos, hW0_pos]
          have hW_strict : StrictMonoOn (fun x => x * S.D (q, x ^ 2)) (Icc (0 : ℝ) 2) := by
            refine strictMonoOn_of_deriv_pos (convex_Icc 0 2) ?_ ?_
            · exact (continuous_id.continuousOn.mul (S.D_diff.continuousOn.comp
                ((continuous_const.prodMk (continuous_id.pow 2)).continuousOn)
                fun x hx => ⟨hqΩ, by constructor <;> nlinarith only [hx.1, hx.2, sq_nonneg x]⟩))
            · intro x hx
              rw [interior_Icc] at hx
              have hxI : x ∈ Ioo (-0.5 : ℝ) 2.2 := ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
              have hd := (hW_deriv p hp x hxI).1
              have hpos := (hW_deriv p hp x hxI).2 hx.1.le hx.2.le
              rw [hd.deriv]
              linarith only [hpos]
          have hτx_mem : τ / τ₁ ∈ Icc (0 : ℝ) 2 := ⟨hx_pos.le, hx_lt2.le⟩
          have hτ0x_mem : τ₀ / τ₁ ∈ Icc (0 : ℝ) 2 :=
            ⟨(div_pos hτ0_pos hτ₁_pos).le, ((div_lt_iff₀ hτ₁_pos).mpr hτ0_2).le⟩
          have hdiv_eq : τ / τ₁ = τ₀ / τ₁ := hW_strict.injOn hτx_mem hτ0x_mem hW_eq
          exact (div_left_inj₀ hτ₁_pos.ne').mp hdiv_eq
        · -- `τ ≥ 2 τ₁`: `fctPhTau < 0` directly from `p.1 - m(τ) - c⁻¹ θ' + c⁻¹ ϑ_D' < 0`
          have hd := concretePhiTilde_hasFDerivAt (ε := ε) hK4 hc hτ₁_τD hτ0 p
          have hph_tau : fctPhTau (concretePhiTilde K4 ε c) τ p =
              p.1 - hankelEdgeM τ - c⁻¹ * deriv (outerTheta ε) τ +
                c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c p.2 τ₁)) τ := by
            unfold fctPhTau
            rw [hd.fderiv]
            simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
              Prod.fst_zero, Prod.snd_zero, mul_one, mul_zero, add_zero]
            rfl
          have hm_ge : (3.2 : ℝ) * τ₁ ^ 2 ≤ hankelEdgeM τ := by
            have hmono : uctM (2 * τ₁) ≤ uctM τ :=
              uctM_strictMonoOn.monotoneOn (by positivity : (0 : ℝ) < 2 * τ₁)
                (by linarith only [hge2, hτ₁_pos] : (0 : ℝ) < τ) hge2
            have hm_eq : hankelEdgeM τ = uctM τ := rfl
            have h2_eq : uctM (2 * τ₁) = (2 * τ₁) ^ 2 * mQ (2 * τ₁) := uctM_eq_sq_mul_mQ (by positivity)
            have hmQ : (0.8 : ℝ) ≤ mQ (2 * τ₁) := hmQ_ge (2 * τ₁) (by positivity) (by linarith only [hτ₁_δQ])
            rw [hm_eq]
            calc (3.2 : ℝ) * τ₁ ^ 2 = (2 * τ₁) ^ 2 * 0.8 := by ring
              _ ≤ (2 * τ₁) ^ 2 * mQ (2 * τ₁) := mul_le_mul_of_nonneg_left hmQ (sq_nonneg _)
              _ = uctM (2 * τ₁) := h2_eq.symm
              _ ≤ uctM τ := hmono
          have hp1_le : p.1 ≤ |ctTheta1 ε| * τ₁ ^ 4 + 2.55 * τ₁ ^ 2 := by
            have hℓ : concreteEll1 ε c p.1 < 2.55 := hp.2.1
            have hp1_eq : p.1 = ctTheta1 ε * c⁻¹ + τ₁ ^ 2 * concreteEll1 ε c p.1 := by
              unfold concreteEll1; field_simp [hτ₁_pos.ne']; ring
            rw [hp1_eq, hcinv]
            have hth1 : ctTheta1 ε * τ₁ ^ 4 ≤ |ctTheta1 ε| * τ₁ ^ 4 :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hτ₁_pos.le 4)
            have hℓ2 := mul_le_mul_of_nonneg_left hℓ.le (sq_nonneg τ₁)
            linarith only [hth1, hℓ2]
          have hθ_bd : c⁻¹ * |deriv (outerTheta ε) τ| ≤ Cθ * τ₁ ^ 4 := by
            rw [hcinv]
            have h1 := hθ' ε (hε.symm) τ
            have hden : 1 ≤ (1 + |τ|) ^ 2 := one_le_pow₀ (by linarith only [abs_nonneg τ])
            have h2 : |deriv (outerTheta ε) τ| ≤ Cθ := h1.trans (div_le_self hCθ0 hden)
            exact (mul_le_mul_of_nonneg_left h2 (pow_nonneg hτ₁_pos.le 4)).trans_eq (mul_comm _ _)
          have hα_bd : |p.2| ≤ 2 * τ₁ ^ 2 := by
            have := hp.2.2; rw [← hτsq_eq] at this; exact this.le
          have hv_bds := hv_bd hK4 hc hτ₁_τv hK4t hα_bd hge2
          have hsum_bd : |ctTheta1 ε| * τ₁ ^ 4 + Cθ * τ₁ ^ 4 + Dv * τ₁ ^ 3 ≤ D1 * τ₁ * τ₁ ^ 2 := by
            have hε_le : |ctTheta1 ε| ≤ |ctTheta1 1| + |ctTheta1 (-1)| := by
              rcases hε with rfl | rfl <;> linarith only [abs_nonneg (ctTheta1 1), abs_nonneg (ctTheta1 (-1))]
            have h43 : τ₁ ^ 4 ≤ τ₁ ^ 3 := by nlinarith only [hτ₁_pos, hτ₁_1, pow_nonneg hτ₁_pos.le 3]
            have hA : |ctTheta1 ε| * τ₁ ^ 4 ≤ (|ctTheta1 1| + |ctTheta1 (-1)|) * τ₁ ^ 3 :=
              mul_le_mul hε_le h43 (pow_nonneg hτ₁_pos.le 4) (by positivity)
            have hB : Cθ * τ₁ ^ 4 ≤ Cθ * τ₁ ^ 3 := mul_le_mul_of_nonneg_left h43 hCθ0
            calc |ctTheta1 ε| * τ₁ ^ 4 + Cθ * τ₁ ^ 4 + Dv * τ₁ ^ 3
                ≤ (|ctTheta1 1| + |ctTheta1 (-1)|) * τ₁ ^ 3 + Cθ * τ₁ ^ 3 + Dv * τ₁ ^ 3 := by
                  linarith only [hA, hB]
              _ = D1 * τ₁ * τ₁ ^ 2 := by ring
          have hneg : fctPhTau (concretePhiTilde K4 ε c) τ p < 0 := by
            have hc1 : -(c⁻¹ * deriv (outerTheta ε) τ) ≤ c⁻¹ * |deriv (outerTheta ε) τ| := by
              calc -(c⁻¹ * deriv (outerTheta ε) τ) = c⁻¹ * (-deriv (outerTheta ε) τ) := by ring
                _ ≤ c⁻¹ * |deriv (outerTheta ε) τ| :=
                  mul_le_mul_of_nonneg_left (neg_le_abs _) (inv_nonneg.mpr hc.le)
            have hc2 : c⁻¹ * deriv (fctThetaD (vTotal StripKernelChoice.star K4 c p.2 τ₁)) τ ≤
                c⁻¹ * |deriv (fctThetaD (vTotal StripKernelChoice.star K4 c p.2 τ₁)) τ| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (inv_nonneg.mpr hc.le)
            have hD1_small : D1 * τ₁ * τ₁ ^ 2 ≤ (1 / 10 : ℝ) * τ₁ ^ 2 :=
              mul_le_mul_of_nonneg_right hτ₁_D1_10 (sq_nonneg τ₁)
            have hτ2_pos : 0 < τ₁ ^ 2 := sq_pos_of_pos hτ₁_pos
            linarith only [hph_tau, hm_ge, hp1_le, hθ_bd, hv_bds, hsum_bd, hc1, hc2, hD1_small, hτ2_pos]
          exact absurd hcrit hneg.ne
      val_pos := fun p hp => by
        set q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
        set τ₀ := concreteTau0 ε c S p
        obtain ⟨hqΩ, _, _, hA_mem, hZ_pos, _, hτ0_pos, hτ0_2⟩ := hp_facts p hp
        rw [hPhi_chart p hp hτ0_pos (by linarith only [hτ0_2, hτ₁_pos])]
        have hτZ : (τ₀ / τ₁) ^ 2 = S.Z (q, S.A q) := by
          dsimp only [τ₀]; unfold concreteTau0; rw [mul_div_cancel_left₀ _ hτ₁_pos.ne', Real.sq_sqrt hZ_pos.le]
        have hD_pos : 0 < S.D (q, (τ₀ / τ₁) ^ 2) := by
          have h0x : 0 < τ₀ / τ₁ := div_pos hτ0_pos hτ₁_pos
          have h2x : τ₀ / τ₁ < 2 := (div_lt_iff₀ hτ₁_pos).mpr hτ0_2
          have hz0_mem : (τ₀ / τ₁) ^ 2 ∈ Ioo (-1 : ℝ) 6 :=
            ⟨by linarith only [sq_nonneg (τ₀ / τ₁)], by nlinarith only [h0x, h2x]⟩
          linarith only [(S.D_bounds (q := (q, (τ₀ / τ₁) ^ 2)) ⟨hqΩ, hz0_mem⟩).1]
        have hW0_pos : 0 < (τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2) := mul_pos (div_pos hτ0_pos hτ₁_pos) hD_pos
        have hW0_sq : ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2 = S.A q := by
          calc ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2
              = (τ₀ / τ₁) ^ 2 * S.D (q, (τ₀ / τ₁) ^ 2) ^ 2 := by ring
            _ = S.Z (q, S.A q) * S.D (q, S.Z (q, S.A q)) ^ 2 := by rw [hτZ]
            _ = S.A q := S.Z_D ⟨hqΩ, by constructor <;> linarith only [hA_mem.1, hA_mem.2]⟩
        have hval : S.A q * ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) -
            ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 3 / 3 =
            2 / 3 * S.A q * ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) := by
          have h3 : ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 3 =
              S.A q * ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) := by
            rw [pow_succ', hW0_sq]; ring
          rw [h3]; ring
        rw [hval]
        exact mul_pos (pow_pos hτ₁_pos 3) (mul_pos (mul_pos (by norm_num) hA_mem.1) hW0_pos) }
  refine ⟨hbox, ?_⟩
  -- `(b1)` properties on `concretePhaseDom ellMin ε c`
  intro p hp
  set q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
  obtain ⟨hqΩ, _, _, hA_mem, hZ_pos, _, hτ0_pos, hτ0_2⟩ := hp_facts p hp
  have hatil_val : fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p = τ₁ ^ 2 * S.A q := by
    set τ₀ := concreteTau0 ε c S p
    have hτZ : (τ₀ / τ₁) ^ 2 = S.Z (q, S.A q) := by
      dsimp only [τ₀]; unfold concreteTau0; rw [mul_div_cancel_left₀ _ hτ₁_pos.ne', Real.sq_sqrt hZ_pos.le]
    have hW0_sq : ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2 = S.A q := by
      calc ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 2
          = (τ₀ / τ₁) ^ 2 * S.D (q, (τ₀ / τ₁) ^ 2) ^ 2 := by ring
        _ = S.Z (q, S.A q) * S.D (q, S.Z (q, S.A q)) ^ 2 := by rw [hτZ]
        _ = S.A q := S.Z_D ⟨hqΩ, by constructor <;> linarith only [hA_mem.1, hA_mem.2]⟩
    have hD_pos : 0 < S.D (q, (τ₀ / τ₁) ^ 2) := by
      have h0x : 0 < τ₀ / τ₁ := div_pos hτ0_pos hτ₁_pos
      have h2x : τ₀ / τ₁ < 2 := (div_lt_iff₀ hτ₁_pos).mpr hτ0_2
      have hz0_mem : (τ₀ / τ₁) ^ 2 ∈ Ioo (-1 : ℝ) 6 :=
        ⟨by linarith only [sq_nonneg (τ₀ / τ₁)], by nlinarith only [h0x, h2x]⟩
      linarith only [(S.D_bounds (q := (q, (τ₀ / τ₁) ^ 2)) ⟨hqΩ, hz0_mem⟩).1]
    have hW0_pos : 0 < (τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2) := mul_pos (div_pos hτ0_pos hτ₁_pos) hD_pos
    have hPhi_val : concretePhiTilde K4 ε c τ₀ p =
        τ₁ ^ 3 * (2 / 3 * S.A q * ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2))) := by
      rw [hPhi_chart p hp hτ0_pos (by linarith only [hτ0_2, hτ₁_pos])]
      have h3 : ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) ^ 3 =
          S.A q * ((τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2)) := by
        rw [pow_succ', hW0_sq]; ring
      rw [h3]; ring
    have hW0_eq : (τ₀ / τ₁) * S.D (q, (τ₀ / τ₁) ^ 2) = Real.sqrt (S.A q) := by
      rw [← Real.sqrt_sq hW0_pos.le, hW0_sq]
    have h32 : 3 / 2 * concretePhiTilde K4 ε c τ₀ p = (τ₁ * Real.sqrt (S.A q)) ^ 3 := by
      rw [hPhi_val, hW0_eq]
      have hsqA : Real.sqrt (S.A q) ^ 2 = S.A q := Real.sq_sqrt hA_mem.1.le
      calc 3 / 2 * (τ₁ ^ 3 * (2 / 3 * S.A q * Real.sqrt (S.A q)))
          = τ₁ ^ 3 * (S.A q * Real.sqrt (S.A q)) := by ring
        _ = τ₁ ^ 3 * (Real.sqrt (S.A q) ^ 2 * Real.sqrt (S.A q)) := by rw [hsqA]
        _ = (τ₁ * Real.sqrt (S.A q)) ^ 3 := by ring
    unfold fctAtil
    rw [h32, ← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg hτ₁_pos.le (Real.sqrt_nonneg _))]
    norm_num [Real.rpow_two, mul_pow, Real.sq_sqrt hA_mem.1.le]
  have hdf := hbox.hasFDerivAt_atil hp
  refine ⟨hτ0_2, hA_mem, hatil_val, ?_, ?_⟩
  · have hd10 : fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (1, 0) =
        concreteTau0 ε c S p / Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) := by
      rw [hdf.fderiv]
      simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul, mul_one, mul_zero, add_zero]
    rw [hd10, hatil_val]
    have hAY' : (q, S.A q) ∈ S.Ω ×ˢ Yint := ⟨hqΩ, by constructor <;> linarith only [hA_mem.1, hA_mem.2]⟩
    have hZ_eq : S.Z (q, S.A q) = S.A q * S.V (q, S.A q) ^ 2 := (S.V_eq hAY').symm
    have hV_pos : 0 < S.V (q, S.A q) := by linarith only [(S.V_bounds hAY').1]
    have hsqrt_a : Real.sqrt (τ₁ ^ 2 * S.A q) = τ₁ * Real.sqrt (S.A q) := by
      rw [Real.sqrt_mul (sq_nonneg τ₁), Real.sqrt_sq hτ₁_pos.le]
    have hsqrt_Z : Real.sqrt (S.Z (q, S.A q)) = Real.sqrt (S.A q) * S.V (q, S.A q) := by
      rw [hZ_eq, Real.sqrt_mul hA_mem.1.le, Real.sqrt_sq hV_pos.le]
    have hsqA_ne : Real.sqrt (S.A q) ≠ 0 := (Real.sqrt_pos.mpr hA_mem.1).ne'
    unfold concreteTau0
    rw [hsqrt_a, hsqrt_Z]
    field_simp [hτ₁_pos.ne', hsqA_ne]
  · have hd01 : fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (0, 1) =
        fderiv ℝ (fctPh (concretePhiTilde K4 ε c)) (concreteTau0 ε c S p, p) (0, (0, 1)) /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p) := by
      rw [hdf.fderiv]
      simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul, mul_zero, mul_one, zero_add]
      unfold fctPhAlpha
      rfl
    have hd_ph01 := concretePhiTilde_hasFDerivAt (ε := ε) hK4 hc hτ₁_τD hτ0_pos p
    have heq01 : fderiv ℝ (fctPh (concretePhiTilde K4 ε c)) (concreteTau0 ε c S p, p) (0, (0, 1)) =
        c⁻¹ * fctThetaD (vAlpha 1 τ₁) (concreteTau0 ε c S p) := by
      rw [hd_ph01.fderiv]
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
        mul_zero, mul_one, zero_add]
      rfl
    rw [hd01, heq01]

/-- info: 'FormalResearch.SignUncertainty.fctWarpIntegrand_eq_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpIntegrand_eq_edge

/-- info: 'FormalResearch.SignUncertainty.concreteEdgeAmp_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concreteEdgeAmp_inner

/-- info: 'FormalResearch.SignUncertainty.concretePhaseBox_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concretePhaseBox_exist

end FormalResearch.SignUncertainty
