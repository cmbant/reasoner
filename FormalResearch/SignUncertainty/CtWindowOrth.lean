module

public import Mathlib
public import FormalResearch.Complex.HalfDiscCauchy
public import FormalResearch.SignUncertainty.CtAiryHplus
public import FormalResearch.SignUncertainty.CtRoscUpper
public import FormalResearch.SignUncertainty.CtRoscEta
public import FormalResearch.SignUncertainty.CtRoscBookProof
public import FormalResearch.SignUncertainty.CtDyadicCombined

/-!
# `ct:dyadic` (3)-(4), `window` Step W1 (`ct:H2-orth` and `|ctOscS1| ≤ η_R`)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` Part (3) `(ct:H2-orth)` and Part (4) `(iv) |s₁| ≤ η_R`.

Defines `calD_up u := -(π/2) * (2 h₊(u) h₊'(u)) - airyUpE u`, which is continuous on `closedHalfDisc R`, holomorphic on
`openHalfDisc R`, agrees with `CtAiryHplus.calD` on `Im u ≥ 0, u ≠ 0`, and has imaginary part `D(x) = -π(Ai Bi)'(x) + 1_{x<0} sin((4/3)(-x)^{3/2})`
on `ℝ`.  Cauchy's theorem on the upper half-disc (`halfDisc_cauchy`) applied to `f_c · calD_up`, `f_c · h₊²`, and `f_c · airyUpE` yields
all three orthogonality/oscillation estimates against `ctEta c₁ ε c f R`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.HalfDiscCauchy CtAiryHplus

/-- Upper-half-plane continuation of `CtAiryHplus.calD`: uses `airyUpE` in place of `cexp ((4/3) u^{3/2})` so that it is
continuous on the closed upper half-plane (including `u ≤ 0`) and holomorphic on the open upper half-plane. -/
noncomputable def calD_up (u : ℂ) : ℂ :=
  -((π : ℂ) / 2) * (2 * hplus u * hplus' u) - airyUpE u

lemma calD_up_eq_calD {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) : calD_up u = calD u := by
  unfold calD_up calD airyUpE
  rw [airyUp_pow_eq hu h0]

lemma calD_up_zero : calD_up 0 = calD 0 := by
  unfold calD_up calD airyUpE
  simp [Complex.zero_cpow (show (3 / 2 : ℂ) ≠ 0 by norm_num)]

lemma calD_up_eq_calD_real (x : ℝ) : calD_up (x : ℂ) = calD (x : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact calD_up_zero
  · exact calD_up_eq_calD (by simp) (Complex.ofReal_ne_zero.mpr hx)

lemma calD_up_im_real (x : ℝ) :
    (calD_up (x : ℂ)).im = -π * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x) +
      (if x < 0 then Real.sin ((4 / 3) * (-x) ^ (3 / 2 : ℝ)) else 0) := by
  rw [calD_up_eq_calD_real]
  exact calD_im_real x

lemma airyUpE_im_real (x : ℝ) :
    (airyUpE (x : ℂ)).im = if x < 0 then -Real.sin ((4 / 3) * (-x) ^ (3 / 2 : ℝ)) else 0 := by
  by_cases hx : x < 0
  · simp only [hx, ↓reduceIte]
    have hx' : x = -(-x) := by ring
    conv_lhs => rw [hx']
    rw [airyUpE_ofReal_neg (by linarith)]
    have he : -(((4 / 3 * (-x) ^ (3 / 2 : ℝ) : ℝ) : ℂ)) * I =
        ((-((4 / 3) * (-x) ^ (3 / 2 : ℝ)) : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  · simp only [hx, ↓reduceIte]
    rw [airyUpE_ofReal_nonneg (not_lt.mp hx), Complex.ofReal_im]

lemma differentiable_hplus : Differentiable ℂ hplus := fun u =>
  (hasDerivAt_hplus u).differentiableAt

lemma differentiable_hplus_sq_deriv : Differentiable ℂ (fun u => 2 * hplus u * hplus' u) := by
  have hsq : Differentiable ℂ (fun u => hplus u ^ 2) := differentiable_hplus.pow 2
  have hder : DifferentiableOn ℂ (deriv (fun u => hplus u ^ 2)) univ :=
    hsq.differentiableOn.deriv isOpen_univ
  have heq : (fun u => 2 * hplus u * hplus' u) = deriv (fun u => hplus u ^ 2) :=
    funext fun u => (hasDerivAt_hplus_sq u).deriv.symm
  rw [heq]
  exact fun u => (hder u (mem_univ u)).differentiableAt (isOpen_univ.mem_nhds (mem_univ u))

lemma continuousOn_calD_up {R : ℝ} : ContinuousOn calD_up (closedHalfDisc R) := by
  have hc1 : Continuous (fun u : ℂ => -((π : ℂ) / 2) * (2 * hplus u * hplus' u)) :=
    continuous_const.mul differentiable_hplus_sq_deriv.continuous
  exact hc1.continuousOn.sub (continuousOn_airyUpE.mono fun _ hu => hu.2)

lemma differentiableOn_calD_up {R : ℝ} : DifferentiableOn ℂ calD_up (openHalfDisc R) := by
  intro u hu
  have hd1 : DifferentiableAt ℂ (fun u : ℂ => -((π : ℂ) / 2) * (2 * hplus u * hplus' u)) u :=
    (differentiable_hplus_sq_deriv u).const_mul _
  exact (hd1.sub (differentiableAt_airyUpE hu.2)).differentiableWithinAt

/-- Single Cauchy mechanism on `closedHalfDisc R` for any real-analytic multiplier `F` and upper-half-plane kernel `K`:
bounding `‖K(Re^{iθ})‖ ≤ B ‖airyUpE(Re^{iθ})‖` on `θ ∈ [0, π]` bounds `|∫_{-R}^R (Re F(t))(Im K(t)) dt|` by
`B ∫_0^π R ‖F(Re^{iθ})‖ ‖airyUpE(Re^{iθ})‖ dθ`. -/
lemma halfDisc_im_bound {F K : ℂ → ℂ} {ρ R B : ℝ} (hR : 0 < R) (hRρ : R < ρ) (_hB : 0 ≤ B)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hK_cont : ContinuousOn K (closedHalfDisc R))
    (hK_diff : DifferentiableOn ℂ K (openHalfDisc R))
    (hK_bound : ∀ θ ∈ Icc (0 : ℝ) π, ‖K (circleMap 0 R θ)‖ ≤ B * ‖airyUpE (circleMap 0 R θ)‖) :
    |∫ t in (-R)..R, (F (t : ℂ)).re * (K (t : ℂ)).im| ≤
      B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
  have hsub_closed : closedHalfDisc R ⊆ ball 0 ρ := fun z hz => by
    rw [mem_ball_zero_iff]; exact hz.1.trans_lt hRρ
  have hsub_open : openHalfDisc R ⊆ ball 0 ρ := fun z hz => by
    rw [mem_ball_zero_iff]; exact hz.1.trans hRρ
  have hFc : ContinuousOn F (closedHalfDisc R) := (hF_diff.mono hsub_closed).continuousOn
  have hc : ContinuousOn (fun z => F z * K z) (closedHalfDisc R) := hFc.mul hK_cont
  have hd : DifferentiableOn ℂ (fun z => F z * K z) (openHalfDisc R) :=
    (hF_diff.mono hsub_open).mul hK_diff
  have hC := halfDisc_cauchy hR hc hd
  have hIint : IntervalIntegrable (fun t : ℝ => F (t : ℂ) * K (t : ℂ)) volume (-R) R := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    exact hc.comp Complex.continuous_ofReal.continuousOn fun t ht => ofReal_mem_closedHalfDisc ht
  have hre : ∫ t in (-R)..R, (F (t : ℂ)).re * (K (t : ℂ)).im =
      (∫ t in (-R)..R, F (t : ℂ) * K (t : ℂ)).im := by
    have hcomm := Complex.imCLM.intervalIntegral_comp_comm hIint
    simp only [Complex.imCLM_apply] at hcomm
    rw [← hcomm]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    have htr : |t| ≤ R := abs_le.2 ht
    simp only [Complex.mul_im, hF_real t htr, zero_mul, add_zero]
  have hEq : (∫ t in (-R)..R, F (t : ℂ) * K (t : ℂ)).im =
      -(I * ∫ θ in (0 : ℝ)..π,
        F (R * Complex.exp (θ * I)) * K (R * Complex.exp (θ * I)) * (R * Complex.exp (θ * I))).im := by
    have := congrArg Complex.im (eq_neg_of_add_eq_zero_left hC)
    simpa [Complex.neg_im] using this
  rw [hre, hEq, abs_neg]
  have hnorm_le :
      |(I * ∫ θ in (0 : ℝ)..π,
          F (R * Complex.exp (θ * I)) * K (R * Complex.exp (θ * I)) * (R * Complex.exp (θ * I))).im| ≤
        ‖∫ θ in (0 : ℝ)..π,
          F (R * Complex.exp (θ * I)) * K (R * Complex.exp (θ * I)) * (R * Complex.exp (θ * I))‖ := by
    calc _ ≤ ‖I * ∫ θ in (0 : ℝ)..π,
            F (R * Complex.exp (θ * I)) * K (R * Complex.exp (θ * I)) * (R * Complex.exp (θ * I))‖ :=
          Complex.abs_im_le_norm _
      _ = _ := by rw [norm_mul, norm_I, one_mul]
  refine hnorm_le.trans ?_
  have hwcont : ContinuousOn (fun θ : ℝ => circleMap 0 R θ) (Icc 0 π) :=
    (continuous_circleMap 0 R).continuousOn
  have hmaps_closed : MapsTo (circleMap 0 R) (Icc 0 π) (closedHalfDisc R) := fun θ hθ => by
    refine ⟨by simp [circleMap, abs_of_pos hR], ?_⟩
    rw [cftDef_im_circleMap]
    exact mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
  have hEcont : ContinuousOn (fun θ => ‖airyUpE (circleMap 0 R θ)‖) (Icc 0 π) :=
    (continuousOn_airyUpE.comp hwcont (fun θ hθ => (hmaps_closed hθ).2)).norm
  have hFcont : ContinuousOn (fun θ => ‖F (circleMap 0 R θ)‖) (Icc 0 π) :=
    (hFc.comp hwcont hmaps_closed).norm
  have hint_rhs : IntervalIntegrable
      (fun θ : ℝ => B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖)) volume 0 π := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le Real.pi_pos.le]
    exact continuousOn_const.mul ((continuousOn_const.mul hFcont).mul hEcont)
  calc ‖∫ θ in (0 : ℝ)..π,
        F (R * Complex.exp (θ * I)) * K (R * Complex.exp (θ * I)) * (R * Complex.exp (θ * I))‖
      ≤ ∫ θ in (0 : ℝ)..π, B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) := by
        refine intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
          (Eventually.of_forall fun θ hθ => ?_) hint_rhs
        have hθ' : θ ∈ Icc (0 : ℝ) π := ⟨hθ.1.le, hθ.2⟩
        have hcm : R * Complex.exp (θ * I) = circleMap 0 R θ := by simp [circleMap]
        rw [hcm, norm_mul, norm_mul, norm_circleMap_zero, abs_of_pos hR]
        calc ‖F (circleMap 0 R θ)‖ * ‖K (circleMap 0 R θ)‖ * R
            = R * ‖F (circleMap 0 R θ)‖ * ‖K (circleMap 0 R θ)‖ := by ring
          _ ≤ R * ‖F (circleMap 0 R θ)‖ * (B * ‖airyUpE (circleMap 0 R θ)‖) := by
              gcongr
              exact hK_bound θ hθ'
          _ = B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) := by ring
    _ = B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ :=
        intervalIntegral.integral_const_mul _ _

lemma hplus_sq_norm_le_circle {u : ℂ} (hu : 0 ≤ u.im) (hR : 1 ≤ ‖u‖) :
    ‖hplus u ^ 2‖ ≤ 2 * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hR; linarith
  have h1 : ‖T1 u‖ ≤ 1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by
    unfold T1
    rw [norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_inv, norm_cpow_half, airyUpE_eq_cexp hu hu0, Complex.norm_exp]
    have hrw : (‖u‖ ^ (1 / 2 : ℝ))⁻¹ = ‖u‖ ^ (-(1 / 2 : ℝ)) :=
      (Real.rpow_neg (norm_nonneg u) (1 / 2)).symm
    have hre : ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)).re = 4 / 3 * (u ^ (3 / 2 : ℂ)).re := by
      simp [Complex.mul_re]
    rw [hrw, hre]
  have h2 := hplus_sq_asymp hu hu0 hR
  have hrw2 : (√‖u‖)⁻¹ = ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (norm_nonneg u)]
  have hexp : Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) = ‖airyUpE u‖ := by
    rw [airyUpE_eq_cexp hu hu0, Complex.norm_exp]; simp [Complex.mul_re]
  rw [hrw2, hexp] at h2
  have ht1 : ‖u‖ ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)
  have hE0 : 0 ≤ ‖airyUpE u‖ := norm_nonneg _
  have hu_nn : 0 ≤ ‖u‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hsub_le : 4 * ‖u‖ ^ (-(3 / 2 : ℝ)) * (1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) ≤
      4 / π * (‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by
    have hq : 0 ≤ 1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by positivity
    calc 4 * ‖u‖ ^ (-(3 / 2 : ℝ)) * (1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖)
        ≤ 4 * 1 * (1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by gcongr
      _ = 4 / π * (‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by ring
  have hsum : 1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ +
      4 / π * (‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) =
      (5 / π) * (‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by ring
  calc ‖hplus u ^ 2‖ = ‖T1 u + (hplus u ^ 2 - T1 u)‖ := by ring_nf
    _ ≤ ‖T1 u‖ + ‖hplus u ^ 2 - T1 u‖ := norm_add_le _ _
    _ ≤ (5 / π) * (‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by linarith [h1, h2, hsub_le, hsum]
    _ ≤ 2 * (‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by
        have hle : 5 / π ≤ 2 := by rw [div_le_iff₀ Real.pi_pos]; linarith
        exact mul_le_mul_of_nonneg_right hle (mul_nonneg hu_nn hE0)
    _ = 2 * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by ring

lemma ctFcC_real_of_holo {c₁ ε c : ℝ} {f : ℝ → ℝ} {ρ : ℝ} (hR : ctRmax c₁ c < ρ)
    (hconj : ∀ u ∈ ball (0 : ℂ) ρ, ctFcC c₁ ε c f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (ctFcC c₁ ε c f u))
    {x : ℝ} (hx : |x| ≤ ctRmax c₁ c) :
    (ctFcC c₁ ε c f (x : ℂ)).im = 0 := by
  have hxball : (x : ℂ) ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx.trans_lt hR
  have h := hconj (x : ℂ) hxball
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.1 h.symm

lemma eqOn_deriv_of_eqOn_ball {f₁ f₂ : ℂ → ℂ} {ρ : ℝ} (h : EqOn f₁ f₂ (ball (0 : ℂ) ρ))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) : deriv f₁ z = deriv f₂ z := by
  have hev : f₁ =ᶠ[𝓝 z] f₂ := Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball 0 ρ, isOpen_ball.mem_nhds hz, h⟩
  exact hev.deriv_eq

/-- For `c₁ ≤ ctChartC1` with a chart agreement `EqOn (ctPhiC c₁) (ctPhiC ctChartC1) (ball 0 ρ₁)`,
`ctFcC ctChartC1 ε c f` and `ctFcC c₁ ε c f` agree on `ball 0 ρ₁`. -/
lemma ctFcC_agree_on_ball {c₁ ε c ρ₁ : ℝ} {f : ℝ → ℝ}
    (hagree : EqOn (ctPhiC c₁ ε c) (ctPhiC ctChartC1 ε c) (ball 0 ρ₁)) :
    EqOn (ctFcC ctChartC1 ε c f) (ctFcC c₁ ε c f) (ball 0 ρ₁) := by
  intro u hu
  unfold ctFcC
  rw [(hagree hu).symm, eqOn_deriv_of_eqOn_ball hagree hu]

/-- Bridge between the symmetric interval integral `∫ x in (-R)..R, (Re f_c(x)) * 1_{x<0} sin((4/3)(-x)^{3/2})`
and `ctOscS1 R ε c f = ∫ v in Ioo 0 R, (Re f_c(-v)) sin((4/3)v^{3/2})`. -/
lemma intervalIntegral_indicator_sin_eq_ctOscS1 {ε c R : ℝ} {f : ℝ → ℝ} (hR : 0 ≤ R)
    (hcont : ContinuousOn (fun x : ℝ => ctFcC ctChartC1 ε c f (x : ℂ)) (Icc (-R) R)) :
    ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re *
        (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0) =
      ctOscS1 R ε c f := by
  set F : ℝ → ℝ := fun x => (ctFcC ctChartC1 ε c f (x : ℂ)).re with hF
  have hFc : ContinuousOn F (Icc (-R) R) := Complex.continuous_re.comp_continuousOn hcont
  have hS : Continuous fun x : ℝ => Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) :=
    Real.continuous_sin.comp (continuous_const.mul (continuous_neg.rpow_const fun _ => Or.inr (by norm_num)))
  have h1 : IntervalIntegrable (fun x => F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0))
      volume (-R) 0 := by
    have hcont1 : ContinuousOn (fun x => F x * Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ))) (uIcc (-R) 0) := by
      rw [uIcc_of_le (by linarith)]
      exact (hFc.mono (Icc_subset_Icc_right hR)).mul hS.continuousOn
    refine hcont1.intervalIntegrable.congr fun x hx => ?_
    rw [uIoc_of_le (by linarith)] at hx
    rcases hx.2.eq_or_lt with rfl | hlt
    · simp [Real.zero_rpow (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
    · simp [hlt]
  have h2 : IntervalIntegrable (fun x => F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0))
      volume 0 R := by
    refine (intervalIntegrable_const (c := (0 : ℝ))).congr fun x hx => ?_
    rw [uIoc_of_le hR] at hx
    simp only [not_lt.mpr hx.1.le, ite_false, mul_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hzero : ∫ x in (0 : ℝ)..R, F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0) = 0 := by
    have hz : ∫ x in (0 : ℝ)..R, F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0) =
        ∫ x in (0 : ℝ)..R, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hR] at hx
      simp [not_lt.mpr hx.1]
    rw [hz, intervalIntegral.integral_zero]
  have hleft : ∫ x in (-R)..0, F x * (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0) =
      ∫ x in (-R)..0, F x * Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    rcases hx.2.eq_or_lt with rfl | hlt
    · simp [Real.zero_rpow (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
    · simp [hlt]
  have hcomp := intervalIntegral.integral_comp_neg (a := 0) (b := R)
    (fun x : ℝ => F x * Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)))
  simp only [neg_zero, neg_neg] at hcomp
  rw [hzero, add_zero, hleft, ← hcomp, intervalIntegral.integral_of_le hR, integral_Ioc_eq_integral_Ioo]
  unfold ctOscS1
  refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  simp only [hF, Complex.ofReal_neg]

/-- Interval integral of `(Re f_c(x)) * (airyUpE x).im` on `(-R)..R` equals `-ctOscS1 R ε c f`. -/
lemma intervalIntegral_airyUpE_im_eq_neg_ctOscS1 {ε c R : ℝ} {f : ℝ → ℝ} (hR : 0 ≤ R)
    (hcont : ContinuousOn (fun x : ℝ => ctFcC ctChartC1 ε c f (x : ℂ)) (Icc (-R) R)) :
    ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyUpE (x : ℂ)).im =
      -ctOscS1 R ε c f := by
  have heq : ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyUpE (x : ℂ)).im =
      -(∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re *
        (if x < 0 then Real.sin (4 / 3 * (-x) ^ (3 / 2 : ℝ)) else 0)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [airyUpE_im_real]
    split_ifs <;> ring
  rw [heq, intervalIntegral_indicator_sin_eq_ctOscS1 hR hcont]

/-- **W1 (`ct:H2-orth` and `(iv) |s₁| ≤ η_R`)**: for sufficiently small `c₁ > 0` and large `c`,
at every radius `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]` and for every Hankel eigenfunction `f`:
1. `|∫_{-R}^R Re f_c(x) D(x) dx| ≤ (11 c₁^{-3}) · c⁻¹ η_R(f)`,
2. `c^{-2/3} |∫_{-R}^R Re f_c(x) Ai(x) Bi(x) dx| ≤ c₁⁻¹ · c⁻¹ η_R(f)`,
3. `|ctOscS1 R ε c f| ≤ η_R(f)`,
4. `|∫_{-R}^R Re f_c(x) (-π (Ai Bi)'(x)) dx| ≤ (1 + 11 c₁^{-3} c⁻¹) η_R(f)`. -/
theorem ct_h2_orth_bounds :
    ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ →
      ∃ C c₀ : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c →
        ∀ f : ℝ → ℝ, IsHankelEigenfn c ε f →
          ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) →
            |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im| ≤
                C * (c⁻¹ * ctEta c₁ ε c f R) ∧
              c ^ (-(2 / 3 : ℝ)) *
                  |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x)| ≤
                C * (c⁻¹ * ctEta c₁ ε c f R) ∧
              |ctOscS1 R ε c f| ≤ ctEta c₁ ε c f R ∧
              |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re *
                  (-π * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x))| ≤
                (1 + C * c⁻¹) * ctEta c₁ ε c f R := by
  obtain ⟨c₁C, hc₁C, hCC⟩ := ct_chart_complex
  obtain ⟨C₂, c₀₂, hC₂, hbody₂, hwin₂⟩ := ct_rosc_setup
  obtain ⟨ρ₁, M₁, hW₁, -⟩ := hwin₂ 1 (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hW₂, -⟩ := hwin₂ (-1) (Or.inr rfl)
  have hρmin : 0 < min ρ₁ ρ₂ := lt_min hW₁.1 hW₂.1
  have hrad : 0 < Real.sqrt (min ρ₁ ρ₂ / 16) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨min c₁C (min ctChartC1 (Real.sqrt (min ρ₁ ρ₂ / 16))),
    lt_min hc₁C (lt_min ctChartC1_pos hrad), fun c₁ hc₁ hle => ?_⟩
  have hleC : c₁ ≤ c₁C := hle.trans (min_le_left _ _)
  have hleCh : c₁ ≤ ctChartC1 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlerad : c₁ ≤ Real.sqrt (min ρ₁ ρ₂ / 16) :=
    hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsq_rho : 16 * c₁ ^ 2 ≤ min ρ₁ ρ₂ := by
    have := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ min ρ₁ ρ₂ / 16)
    have hsq : c₁ ^ 2 ≤ min ρ₁ ρ₂ / 16 := by
      calc c₁ ^ 2 ≤ (Real.sqrt (min ρ₁ ρ₂ / 16)) ^ 2 := pow_le_pow_left₀ hc₁.le hlerad 2
        _ = min ρ₁ ρ₂ / 16 := this
    linarith
  obtain ⟨C₁, c₀₁, hC₁, hCC₁⟩ := (ctChartComplex_iff c₁).1 (hCC c₁ hc₁ hleC)
  have hev : ∀ᶠ c : ℝ in atTop,
      c₀₁ ≤ c ∧ c₀₂ ≤ c ∧ 3e6 ≤ c ∧ C₂ * c ^ (-(1 / 3 : ℝ)) < 1 ∧
      1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧ M₁ < 2 * c₁ ^ 2 * c ∧ M₂ < 2 * c₁ ^ 2 * c := by
    filter_upwards [eventually_ge_atTop c₀₁, eventually_ge_atTop c₀₂, eventually_ge_atTop (3e6 : ℝ),
      eventually_rpow_neg_le (by norm_num : (0 : ℝ) < 1 / 3) (2 * C₂ + 1) (by norm_num : (0 : ℝ) < 1),
      eventually_rpow_ge (by norm_num : (0 : ℝ) < 2 / 3) (by positivity : 0 < c₁ ^ 2) 1,
      eventually_gt_atTop (M₁ / (2 * c₁ ^ 2)), eventually_gt_atTop (M₂ / (2 * c₁ ^ 2))]
      with c h1 h2 h3 h4 h5 h6 h7
    refine ⟨h1, h2, h3, ?_, h5, ?_, ?_⟩
    · have hnn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      nlinarith
    · rw [div_lt_iff₀ (by positivity)] at h6; linarith
    · rw [div_lt_iff₀ (by positivity)] at h7; linarith
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹, max c₀ 1, by positivity, fun ε hε c hc f hf R hR => ?_⟩
  obtain ⟨hc₀₁, hc₀₂, hc3, hcC₂, hR1_lb, hM1c, hM2c⟩ := hc₀ c ((le_max_left _ _).trans hc)
  have hc0 : 0 < c := by linarith [le_max_right c₀ 1]
  have hR1 : 1 ≤ R := hR1_lb.trans hR.1
  have hR0 : 0 < R := by linarith
  have hRm : R ≤ ctRmax c₁ c := hR.2
  have hRm_Ch : R ≤ ctRmax ctChartC1 c := hRm.trans (ctRmax_mono hc0.le hc₁.le hleCh)
  have hb₁ : CtChartBody c₁ ε c C₁ := hCC₁ ε hε c hc₀₁
  have hb₂ : CtChartBody ctChartC1 ε c C₂ := hbody₂ ε hε c hc₀₂
  obtain ⟨ρF, hρF, hFdiff, -, hFconj⟩ := ctFcC_holo ctChartC1_pos ctChartC1_le hb₂ hc3 hcC₂ hf
  have hagree : ∃ ρA : ℝ, ctRmax c₁ c < ρA ∧ EqOn (ctPhiC c₁ ε c) (ctPhiC ctChartC1 ε c) (ball 0 ρA) := by
    rcases hε with rfl | rfl
    · exact ctPhiC_agree hc0 hc₁ hleCh hb₁ hb₂ hW₁ (by linarith [min_le_left ρ₁ ρ₂]) hM1c
    · exact ctPhiC_agree hc0 hc₁ hleCh hb₁ hb₂ hW₂ (by linarith [min_le_right ρ₁ ρ₂]) hM2c
  obtain ⟨ρA, hρA, hphiAgree⟩ := hagree
  have hFcAgree : EqOn (ctFcC ctChartC1 ε c f) (ctFcC c₁ ε c f) (ball 0 ρA) :=
    ctFcC_agree_on_ball hphiAgree
  have hRρF : R < ρF := hRm_Ch.trans_lt hρF
  have hRρA : R < ρA := hRm.trans_lt hρA
  have hFreal : ∀ x : ℝ, |x| ≤ R → (ctFcC ctChartC1 ε c f (x : ℂ)).im = 0 := fun x hx =>
    ctFcC_real_of_holo hρF hFconj (hx.trans hRm_Ch)
  have hFcont_Icc : ContinuousOn (fun x : ℝ => ctFcC ctChartC1 ε c f (x : ℂ)) (Icc (-R) R) := by
    refine hFdiff.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => ?_
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [hx.1, hRρF], by linarith [hx.2, hRρF]⟩
  -- Compare `∫_0^π R ‖ctFcC ctChartC1‖ ‖airyUpE‖` against `ctEta c₁ ε c f R`.
  have hcircle_le :
      (∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) ≤
        ctEta c₁ ε c f R := by
    have hcongr : ∫ θ in (0 : ℝ)..π, R * ‖ctFcC ctChartC1 ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ =
        ∫ θ in (0 : ℝ)..π, R * ‖ctFcC c₁ ε c f (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have hmem : circleMap 0 R θ ∈ ball (0 : ℂ) ρA := by
        rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hR0]; exact hRρA
      rw [hFcAgree hmem]
    rw [hcongr]
    have hΨ_cont : ContinuousOn (hankelPsi c f) (sphere 0 R) := by
      have hsub : sphere (0 : ℂ) R ⊆ closedBall 0 (langerRadius c) := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu
        rw [mem_closedBall_zero_iff, hu]
        have hlt : ctRmax ctChartC1 c < langerRadius c := by
          have h1 := hankelBand_radius_ge_one hc3
          have hp : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
          have h2 : ctRmax ctChartC1 c ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
            unfold ctRmax
            have hlt1 : 4 * ctChartC1 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith [ctChartC1_pos, ctChartC1_le]
            nlinarith
          linarith
        exact hRm_Ch.trans hlt.le
      rw [langerRadius_eq] at hsub
      exact (analyticOnNhd_hankelPsi hc0 hf).differentiableOn.continuousOn.mono hsub
    have hG_cont : ContinuousOn (ctFcC c₁ ε c f) (sphere 0 R) := by
      have hsubA : sphere (0 : ℂ) R ⊆ ball 0 ρA := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_ball_zero_iff, hu]; exact hRρA
      have hsubF : sphere (0 : ℂ) R ⊆ ball 0 ρF := fun u hu => by
        rw [mem_sphere_zero_iff_norm] at hu; rw [mem_ball_zero_iff, hu]; exact hRρF
      exact (hFdiff.continuousOn.mono hsubF).congr fun u hu => (hFcAgree (hsubA hu)).symm
    exact ctEta_ge_half hR0 hΨ_cont hG_cont
  -- Common `R`-power bounds in terms of `c₁` and `c`.
  have hR_m32 : R ^ (-(3 / 2 : ℝ)) ≤ c₁ ^ (-(3 : ℝ)) * c⁻¹ := by
    have e1 : (c₁ ^ 2) ^ (-(3 / 2 : ℝ)) = c₁ ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_natCast c₁ 2, ← Real.rpow_mul hc₁.le]; norm_num
    have e2 : (c ^ (2 / 3 : ℝ)) ^ (-(3 / 2 : ℝ)) = c⁻¹ := by
      rw [← Real.rpow_mul hc0.le, show (2 / 3 : ℝ) * -(3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have hpow : (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(3 / 2 : ℝ)) = c₁ ^ (-(3 : ℝ)) * c⁻¹ := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hc0.le _), e1, e2]
    rw [← hpow]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hR.1 (by norm_num)
  have hR_m12 : c ^ (-(2 / 3 : ℝ)) * R ^ (-(1 / 2 : ℝ)) ≤ c₁⁻¹ * c⁻¹ := by
    have e1 : (c₁ ^ 2) ^ (-(1 / 2 : ℝ)) = c₁⁻¹ := by
      rw [← Real.rpow_natCast c₁ 2, ← Real.rpow_mul hc₁.le,
        show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have e2 : (c ^ (2 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_mul hc0.le]; norm_num
    have hpow : (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ^ (-(1 / 2 : ℝ)) = c₁⁻¹ * c ^ (-(1 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hc0.le _), e1, e2]
    have hleR : R ^ (-(1 / 2 : ℝ)) ≤ c₁⁻¹ * c ^ (-(1 / 3 : ℝ)) := by
      rw [← hpow]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hR.1 (by norm_num)
    have hcc : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) = c⁻¹ := by
      rw [← Real.rpow_add hc0, show -(2 / 3 : ℝ) + -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    calc c ^ (-(2 / 3 : ℝ)) * R ^ (-(1 / 2 : ℝ))
        ≤ c ^ (-(2 / 3 : ℝ)) * (c₁⁻¹ * c ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hleR (Real.rpow_nonneg hc0.le _)
      _ = c₁⁻¹ * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := by ring
      _ = c₁⁻¹ * c⁻¹ := by rw [hcc]
  have hEta_nn : 0 ≤ ctEta c₁ ε c f R := ctEta_nonneg c₁ ε c f hR0.le
  -- Bound 1: `D(x) = (calD x).im = (calD_up x).im`
  have hB1 :
      |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im| ≤
        max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by
    have hcongr : ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im =
        ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (calD_up (x : ℂ)).im := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [calD_up_eq_calD_real]
    rw [hcongr]
    have hK_bd : ∀ θ ∈ Icc (0 : ℝ) π,
        ‖calD_up (circleMap 0 R θ)‖ ≤ (11 * R ^ (-(3 / 2 : ℝ))) * ‖airyUpE (circleMap 0 R θ)‖ := by
      intro θ hθ
      have hu0 : circleMap 0 R θ ≠ 0 := by simp [circleMap, hR0.ne']
      have huim : 0 ≤ (circleMap 0 R θ).im := by
        rw [cftDef_im_circleMap]; exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      have hun : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR0]
      rw [calD_up_eq_calD huim hu0]
      have hcb := calD_bound huim hu0 (by linarith)
      rw [hun] at hcb
      have hexp : Real.exp ((4 / 3) * (circleMap 0 R θ ^ (3 / 2 : ℂ)).re) = ‖airyUpE (circleMap 0 R θ)‖ := by
        rw [airyUpE_eq_cexp huim hu0, Complex.norm_exp]; simp [Complex.mul_re]
      rwa [hexp] at hcb
    have hmain := halfDisc_im_bound (F := ctFcC ctChartC1 ε c f) (K := calD_up) hR0 hRρF (by positivity)
      hFdiff hFreal continuousOn_calD_up differentiableOn_calD_up hK_bd
    have hpos_coef : 0 ≤ 11 * R ^ (-(3 / 2 : ℝ)) := by positivity
    calc _ ≤ 11 * R ^ (-(3 / 2 : ℝ)) * ctEta c₁ ε c f R :=
          hmain.trans (mul_le_mul_of_nonneg_left hcircle_le hpos_coef)
      _ ≤ 11 * (c₁ ^ (-(3 : ℝ)) * c⁻¹) * ctEta c₁ ε c f R := by gcongr
      _ = (11 * c₁ ^ (-(3 : ℝ))) * (c⁻¹ * ctEta c₁ ε c f R) := by ring
      _ ≤ max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by
          gcongr; exact le_max_left _ _
  -- Bound 2: `Ai(x) * Bi(x) = (h₊(x)²).im / 2`
  have hB2 :
      c ^ (-(2 / 3 : ℝ)) * |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x)| ≤
        max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by
    have hK_cont : ContinuousOn (fun u => hplus u ^ 2) (closedHalfDisc R) :=
      (differentiable_hplus.pow 2).continuous.continuousOn
    have hK_diff : DifferentiableOn ℂ (fun u => hplus u ^ 2) (openHalfDisc R) :=
      (differentiable_hplus.pow 2).differentiableOn
    have hK_bd : ∀ θ ∈ Icc (0 : ℝ) π,
        ‖hplus (circleMap 0 R θ) ^ 2‖ ≤ (2 * R ^ (-(1 / 2 : ℝ))) * ‖airyUpE (circleMap 0 R θ)‖ := by
      intro θ hθ
      have huim : 0 ≤ (circleMap 0 R θ).im := by
        rw [cftDef_im_circleMap]; exact mul_nonneg hR0.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      have hun : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR0]
      have h := hplus_sq_norm_le_circle huim (by linarith)
      rwa [hun] at h
    have hmain := halfDisc_im_bound (F := ctFcC ctChartC1 ε c f) (K := fun u => hplus u ^ 2)
      hR0 hRρF (by positivity) hFdiff hFreal hK_cont hK_diff hK_bd
    have hhalf : ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (hplus (x : ℂ) ^ 2).im =
        2 * ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hplus_sq_im x]; ring
    rw [hhalf, abs_mul, abs_two] at hmain
    have hhalf_le : |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x)| ≤
        R ^ (-(1 / 2 : ℝ)) * ctEta c₁ ε c f R := by
      have h2 := hmain.trans (mul_le_mul_of_nonneg_left hcircle_le (by positivity))
      linarith
    calc c ^ (-(2 / 3 : ℝ)) * |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyAi x * airyBi x)|
        ≤ c ^ (-(2 / 3 : ℝ)) * (R ^ (-(1 / 2 : ℝ)) * ctEta c₁ ε c f R) :=
          mul_le_mul_of_nonneg_left hhalf_le (Real.rpow_nonneg hc0.le _)
      _ = (c ^ (-(2 / 3 : ℝ)) * R ^ (-(1 / 2 : ℝ))) * ctEta c₁ ε c f R := by ring
      _ ≤ (c₁⁻¹ * c⁻¹) * ctEta c₁ ε c f R := by gcongr
      _ = c₁⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by ring
      _ ≤ max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by
          gcongr; exact le_max_right _ _
  -- Bound 3: `|ctOscS1 R ε c f| ≤ ctEta c₁ ε c f R`
  have hB3 : |ctOscS1 R ε c f| ≤ ctEta c₁ ε c f R := by
    have hK_bd : ∀ θ ∈ Icc (0 : ℝ) π,
        ‖airyUpE (circleMap 0 R θ)‖ ≤ 1 * ‖airyUpE (circleMap 0 R θ)‖ := fun _ _ => by rw [one_mul]
    have hmain := halfDisc_im_bound (F := ctFcC ctChartC1 ε c f) (K := airyUpE)
      hR0 hRρF zero_le_one hFdiff hFreal
      (continuousOn_airyUpE.mono fun _ hu => hu.2)
      (fun u hu => (differentiableAt_airyUpE hu.2).differentiableWithinAt)
      hK_bd
    rw [intervalIntegral_airyUpE_im_eq_neg_ctOscS1 hR0.le hFcont_Icc, abs_neg, one_mul] at hmain
    exact hmain.trans hcircle_le
  -- Bound 4: `-π (Ai' Bi + Ai Bi') = Im calD - 1_{x<0} sin((4/3)(-x)^{3/2})`
  have hB4 : |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re *
      (-π * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x))| ≤
      (1 + max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * c⁻¹) * ctEta c₁ ε c f R := by
    have hF_re_cont : ContinuousOn (fun x : ℝ => (ctFcC ctChartC1 ε c f (x : ℂ)).re) (uIcc (-R) R) := by
      rw [uIcc_of_le (by linarith)]
      exact Complex.continuous_re.comp_continuousOn hFcont_Icc
    have hi_D : IntervalIntegrable
        (fun x : ℝ => (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im) volume (-R) R := by
      have hcont_D : ContinuousOn (fun x : ℝ => (ctFcC ctChartC1 ε c f (x : ℂ)).re * (calD_up (x : ℂ)).im)
          (uIcc (-R) R) := by
        rw [uIcc_of_le (by linarith)]
        refine (Complex.continuous_re.comp_continuousOn hFcont_Icc).mul ?_
        exact Complex.continuous_im.comp_continuousOn
          (continuousOn_calD_up.comp Complex.continuous_ofReal.continuousOn fun _ hx =>
            ofReal_mem_closedHalfDisc hx)
      refine hcont_D.intervalIntegrable.congr fun x _ => ?_
      rw [calD_up_eq_calD_real]
    have hi_E : IntervalIntegrable
        (fun x : ℝ => (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyUpE (x : ℂ)).im) volume (-R) R := by
      have hcont_E : ContinuousOn (fun x : ℝ => (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyUpE (x : ℂ)).im)
          (uIcc (-R) R) := by
        rw [uIcc_of_le (by linarith)]
        refine (Complex.continuous_re.comp_continuousOn hFcont_Icc).mul ?_
        exact Complex.continuous_im.comp_continuousOn
          ((continuousOn_airyUpE.mono fun (u : ℂ) (hu : u ∈ closedHalfDisc R) => hu.2).comp
            Complex.continuous_ofReal.continuousOn fun _ hx => ofReal_mem_closedHalfDisc hx)
      exact hcont_E.intervalIntegrable
    have hcomb : ∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re *
          (-π * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x)) =
        (∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im) +
        (∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (airyUpE (x : ℂ)).im) := by
      rw [← intervalIntegral.integral_add hi_D hi_E]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [calD_im_real, airyUpE_im_real]
      split_ifs <;> ring
    rw [hcomb, intervalIntegral_airyUpE_im_eq_neg_ctOscS1 hR0.le hFcont_Icc]
    calc |(∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im) + (-ctOscS1 R ε c f)|
        ≤ |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im| +
            |-ctOscS1 R ε c f| := abs_add_le _ _
      _ = |∫ x in (-R)..R, (ctFcC ctChartC1 ε c f (x : ℂ)).re * (CtAiryHplus.calD (x : ℂ)).im| +
            |ctOscS1 R ε c f| := by rw [abs_neg]
      _ ≤ max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) + ctEta c₁ ε c f R := add_le_add hB1 hB3
      _ = (1 + max (11 * c₁ ^ (-(3 : ℝ))) c₁⁻¹ * c⁻¹) * ctEta c₁ ε c f R := by ring
  exact ⟨hB1, hB2, hB3, hB4⟩

/-- info: 'FormalResearch.SignUncertainty.ct_h2_orth_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_h2_orth_bounds

end FormalResearch.SignUncertainty
