module

public import FormalResearch.SignUncertainty.FctCompDStrip
public import FormalResearch.SignUncertainty.FctPhiKill
public import FormalResearch.SignUncertainty.UctStripIntegrals
public import FormalResearch.SignUncertainty.CtOuterEntire
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `fct:comp-D` targets: smooth local extensions of `m(t)/t²`, `m'(t)/t`, `r₀(t)`, and `Δ_curv(t)`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.3 (`fct:comp-D`),
Part (1) target constructions (lines 167–235).

This module defines `StripKernelChoice` (`H_*` vs `H_CE`), proves that
- `m(t) = t² mQ(t)` and `m'(t) = t mD(t)` with `mQ, mD` even, `C^∞` on `(-1/4, 1/4)`,
  and `mQ(0) = π²/12 > 0`, `mD(0) = π²/6 > 0`;
- `r₀(t) = α_osc |H₀(it)| m(t)^{3/2} / (α_fl m'(t))` extends to an even `C^∞` function
  `r0Smooth kind` near `0` with `r0Smooth kind 0 = 1`;
- `f0Base kind t = -log (r0Smooth kind t)` is even, `C^∞` near `0`, `f0Base kind 0 = 0`,
  with uniform target bounds `|f^{(r)}(t)| ≤ C_r τ₁^{2-r}` on `[-3τ₁, 3τ₁]`;
- Hadamard division `divT_theta2 θ t = ∫₀¹ θ'''(st) ds` (`= θ''(t)/t`) and
  `divT2_theta1 θ t = ∫₀¹ (1-s) θ'''(st) ds` (`= θ'(t)/t²`) give smooth, even
  `deltaCurvSmooth c θ t` matching `Δ_curv(t)` on `(0, 1/8)`, with all-order derivative
  bounds via the Leibniz rule.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCompD

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.CohnElkies

/-! ### Choice of strip kernel `H₀ ∈ {H_*, H_CE}` -/

/-- The two strip kernels `H₀ ∈ {H_*, H_CE}` in Lemma FCT.3 (`fct:comp-D`). -/
inductive StripKernelChoice : Type
  | star : StripKernelChoice
  | ce : StripKernelChoice
deriving DecidableEq

/-- The strip kernel `H₀(ζ)` (`H_*` or `H_CE`). -/
noncomputable def stripH0 : StripKernelChoice → ℂ → ℂ
  | .star => uctHstar
  | .ce => uctHCE

/-- The oscillatory envelope `I_osc^{H₀}(L)`. -/
noncomputable def stripIosc : StripKernelChoice → ℝ → ℝ
  | .star => uctIoscStar
  | .ce => uctIoscCE

/-- The exact floor constant `C_fl(H₀)`: `0` for `H_*`, `-(π/2) α_osc` for `H_CE`. -/
noncomputable def stripCfl : StripKernelChoice → ℝ
  | .star => 0
  | .ce => -(π / 2) * uctAlphaOsc

/-- The finite-part singular coefficient `c_{-1}(H₀)`: `(47/20) α_osc` for `H_*`, `-(13/20) α_osc` for `H_CE`. -/
noncomputable def stripCneg1 : StripKernelChoice → ℝ
  | .star => (47 / 20 : ℝ) * uctAlphaOsc
  | .ce => -(13 / 20 : ℝ) * uctAlphaOsc

/-- The ratio `r₀(τ) = α_osc |H₀(iτ)| m(|τ|)^{3/2} / (α_fl m'(|τ|))` for `τ ≠ 0`, and `1` at `τ = 0`. -/
noncomputable def stripR0 (kind : StripKernelChoice) (τ : ℝ) : ℝ :=
  if τ = 0 then 1
  else uctAlphaOsc * ‖stripH0 kind ((τ : ℂ) * Complex.I)‖ * uctM |τ| ^ (3 / 2 : ℝ) /
    (uctAlphaFl * uctMderiv |τ|)

lemma stripR0_eq_div {kind : StripKernelChoice} {τ : ℝ} (hτ : 0 < τ) :
    stripR0 kind τ = stripIosc kind (uctM τ) / uctIfl (uctM τ) := by
  unfold stripR0 uctIfl
  rw [ite_eq_right_iff.mpr fun h => absurd h hτ.ne', abs_of_pos hτ]
  have hm_pos : 0 < uctM τ := uctM_pos hτ
  have htau0 : tau0 (uctM τ) = τ := by
    have h1 : uctM (tau0 (uctM τ)) = uctM τ := ceEll_tau0 hm_pos
    exact uctM_strictMonoOn.injOn (tau0_pos hm_pos) hτ h1
  have hrpow : (uctM τ) ^ (-(3 / 2 : ℝ)) = ((uctM τ) ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hm_pos.le _
  cases kind <;> simp only [stripIosc, stripH0, uctIoscStar, uctIoscCE, htau0]
  · rw [hrpow]; field_simp [uctAlphaFl_pos.ne', (uctMderiv_pos hτ).ne', (Real.rpow_pos_of_pos hm_pos _).ne']
  · rw [hrpow]; field_simp [uctAlphaFl_pos.ne', (uctMderiv_pos hτ).ne', (Real.rpow_pos_of_pos hm_pos _).ne']

/-! ### Holomorphic local extensions of `ℓ(w)`, `ℓ(w)/w²`, and `ℓ'(w)/w` near `0` -/

/-- Holomorphic `ℓ(w) = log(cosh w / sinhQ w)` on `ball (0 : ℂ) (1/2)`. -/
noncomputable def compEllC (w : ℂ) : ℂ := Complex.log (Complex.cosh w / CtOuter.sinhQ w)

/-- Holomorphic `ℓ(w)/w²` on `ball (0 : ℂ) (1/2)`. -/
noncomputable def compEllQ (w : ℂ) : ℂ := dslope (dslope compEllC 0) 0 w

/-- Holomorphic `ℓ'(w)/w` on `ball (0 : ℂ) (1/2)`. -/
noncomputable def compEllD (w : ℂ) : ℂ := dslope (deriv compEllC) 0 w

lemma compEllC_even (w : ℂ) : compEllC (-w) = compEllC w := by
  unfold compEllC
  rw [Complex.cosh_neg]
  have hq : CtOuter.sinhQ (-w) = CtOuter.sinhQ w := by
    unfold CtOuter.sinhQ
    refine tsum_congr fun n => ?_
    rw [(even_two_mul n).neg_pow]
  rw [hq]

lemma differentiableOn_compEllC : DifferentiableOn ℂ compEllC (Metric.ball (0 : ℂ) (1 / 2)) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have hw2 : ‖w‖ ≤ 2 := by linarith
  have hQ_re : 0 < (CtOuter.sinhQ w).re := CtOuter.re_sinhQ_pos hw2
  have hQ_ne : CtOuter.sinhQ w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hQ_re; linarith
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

lemma compEllC_zero : compEllC 0 = 0 := by
  simp [compEllC, CtOuter.sinhQ_zero]

lemma deriv_compEllC_zero : deriv compEllC 0 = 0 := by
  have hd : HasDerivAt compEllC (deriv compEllC 0) 0 :=
    (differentiableOn_compEllC.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).hasDerivAt
  have hd' : HasDerivAt compEllC (deriv compEllC (-0)) (-0) := by simpa using hd
  have hneg : HasDerivAt (fun w => compEllC (-w)) (-deriv compEllC 0) 0 := by
    have h := hd'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    simp only [neg_zero, mul_neg, mul_one] at h
    exact h
  have hneg' : HasDerivAt (fun w => compEllC (-w)) (deriv compEllC 0) 0 := by
    simpa [compEllC_even] using hd
  have heq := hneg.unique hneg'
  have h2 : (2 : ℂ) * deriv compEllC 0 = 0 := by linear_combination -heq
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

lemma differentiableOn_compEllQ : DifferentiableOn ℂ compEllQ (Metric.ball (0 : ℂ) (1 / 2)) := by
  have h1 : DifferentiableOn ℂ (dslope compEllC 0) (Metric.ball (0 : ℂ) (1 / 2)) :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr
      differentiableOn_compEllC
  exact (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr h1

lemma differentiableOn_compEllD : DifferentiableOn ℂ compEllD (Metric.ball (0 : ℂ) (1 / 2)) := by
  have hana : AnalyticOnNhd ℂ compEllC (Metric.ball (0 : ℂ) (1 / 2)) :=
    differentiableOn_compEllC.analyticOnNhd Metric.isOpen_ball
  have hdiff' : DifferentiableOn ℂ (deriv compEllC) (Metric.ball (0 : ℂ) (1 / 2)) :=
    fun z hz => (hana z hz).deriv.differentiableAt.differentiableWithinAt
  exact (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr hdiff'

lemma compEllC_ofReal {x : ℝ} (hx0 : 0 < x) :
    compEllC (x : ℂ) = ((ceEll x : ℝ) : ℂ) := by
  unfold compEllC ceEll
  rw [← Complex.ofReal_cosh, CtOuter.sinhQ_ofReal hx0.ne']
  have hsh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
  have hch_pos : 0 < Real.cosh x := Real.cosh_pos x
  have h1 : ((Real.cosh x : ℝ) : ℂ) / ((Real.sinh x / x : ℝ) : ℂ) = ((x / Real.tanh x : ℝ) : ℂ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hsh_pos.ne', Complex.ofReal_ne_zero.mpr hx0.ne',
      Complex.ofReal_ne_zero.mpr hch_pos.ne']
  rw [h1, Complex.ofReal_log (by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg hx0.le (div_nonneg hsh_pos.le hch_pos.le))]

lemma compEllQ_eq_div {w : ℂ} (hw : w ≠ 0) : compEllQ w = compEllC w / w ^ 2 := by
  unfold compEllQ
  rw [dslope_of_ne _ hw]
  simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul, dslope_of_ne _ hw, dslope_same,
    compEllC_zero, deriv_compEllC_zero]
  field_simp [hw]

lemma compEllD_eq_div {w : ℂ} (hw : w ≠ 0) : compEllD w = deriv compEllC w / w := by
  unfold compEllD
  rw [dslope_of_ne _ hw]
  simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul, deriv_compEllC_zero]
  field_simp [hw]

lemma compEllQ_even (w : ℂ) : compEllQ (-w) = compEllQ w := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [compEllQ_eq_div (neg_ne_zero.mpr hw), compEllQ_eq_div hw, compEllC_even, neg_sq]

lemma compEllD_even {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) (1 / 2)) : compEllD (-w) = compEllD w := by
  by_cases hw0 : w = 0
  · simp [hw0]
  · rw [compEllD_eq_div (neg_ne_zero.mpr hw0), compEllD_eq_div hw0]
    have hmw : -w ∈ Metric.ball (0 : ℂ) (1 / 2) := by simpa [mem_ball_zero_iff] using hw
    have hd : HasDerivAt compEllC (deriv compEllC (-w)) (-w) :=
      (differentiableOn_compEllC.differentiableAt (Metric.isOpen_ball.mem_nhds hmw)).hasDerivAt
    have hcomp : HasDerivAt (fun u => compEllC (-u)) (-deriv compEllC (-w)) w := by
      have h := hd.comp w (hasDerivAt_neg w)
      simp only [mul_neg, mul_one] at h
      exact h
    have hcomp' : HasDerivAt (fun u => compEllC (-u)) (deriv compEllC w) w := by
      have hd2 := (differentiableOn_compEllC.differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
      simpa [compEllC_even] using hd2
    have hodd : deriv compEllC (-w) = -deriv compEllC w := by
      have := hcomp.unique hcomp'; linear_combination -this
    rw [hodd, neg_div_neg_eq]

lemma deriv_compEllC_ofReal {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    deriv compEllC (x : ℂ) = ((uctEllDeriv x : ℝ) : ℂ) := by
  have hx_ball : (x : ℂ) ∈ Metric.ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
  have hd_C : HasDerivAt (fun t : ℝ => compEllC (t : ℂ)) (deriv compEllC (x : ℂ)) x := by
    have hd := (differentiableOn_compEllC.differentiableAt (Metric.isOpen_ball.mem_nhds hx_ball)).hasDerivAt
    simpa using hd.comp_ofReal
  have hd_R : HasDerivAt (fun t : ℝ => ((ceEll t : ℝ) : ℂ)) ((uctEllDeriv x : ℝ) : ℂ) x := by
    have h1 := ceEll_hasDerivAt hx0
    exact h1.ofReal_comp
  have hev : (fun t : ℝ => compEllC (t : ℂ)) =ᶠ[𝓝 x] fun t : ℝ => ((ceEll t : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hx0] with t ht using compEllC_ofReal ht
  exact hd_C.unique (hd_R.congr_of_eventuallyEq hev)

/-! ### Real smooth factors `mQ(t) = m(t)/t²` and `mD(t) = m'(t)/t` on `(-1/4, 1/4)` -/

/-- Even `C^∞` factor `mQ(t) = m(t)/t²` on `(-1/4, 1/4)`, with `mQ(0) = π²/12`. -/
noncomputable def mQ (t : ℝ) : ℝ := (π / 2) ^ 2 * (compEllQ ((π * t / 2 : ℝ) : ℂ)).re

/-- Even `C^∞` factor `mD(t) = m'(t)/t` on `(-1/4, 1/4)`, with `mD(0) = π²/6`. -/
noncomputable def mD (t : ℝ) : ℝ := (π / 2) ^ 2 * (compEllD ((π * t / 2 : ℝ) : ℂ)).re

lemma mQ_even (t : ℝ) : mQ (-t) = mQ t := by
  unfold mQ
  rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg, compEllQ_even]

lemma mD_even {t : ℝ} (ht : |t| < 1 / 4) : mD (-t) = mD t := by
  unfold mD
  rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg]
  have hmem : ((π * t / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [Real.pi_lt_four, abs_nonneg t]
  rw [compEllD_even hmem]

lemma uctM_eq_sq_mul_mQ {t : ℝ} (ht0 : 0 < t) : uctM t = t ^ 2 * mQ t := by
  unfold uctM mQ
  have hx : 0 < π * t / 2 := by positivity
  rw [compEllQ_eq_div (Complex.ofReal_ne_zero.mpr hx.ne'), compEllC_ofReal hx, ← Complex.ofReal_pow,
    ← Complex.ofReal_div, Complex.ofReal_re]
  field_simp [Real.pi_ne_zero, ht0.ne']

lemma uctMderiv_eq_mul_mD {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 4) : uctMderiv t = t * mD t := by
  unfold uctMderiv mD
  have hx0 : 0 < π * t / 2 := by positivity
  have hx1 : π * t / 2 < 1 / 2 := by nlinarith [Real.pi_lt_four]
  rw [compEllD_eq_div (Complex.ofReal_ne_zero.mpr hx0.ne'), deriv_compEllC_ofReal hx0 hx1,
    ← Complex.ofReal_div, Complex.ofReal_re]
  field_simp [Real.pi_ne_zero, ht0.ne']

lemma contDiffOn_mQ : ContDiffOn ℝ (⊤ : ℕ∞) mQ (Ioo (-1 / 4) (1 / 4)) := by
  have hana : AnalyticOnNhd ℂ compEllQ (Metric.ball (0 : ℂ) (1 / 2)) :=
    differentiableOn_compEllQ.analyticOnNhd Metric.isOpen_ball
  have hcd_C : ContDiffOn ℂ (⊤ : ℕ∞) compEllQ (Metric.ball (0 : ℂ) (1 / 2)) :=
    hana.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  have hcd_R : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => (compEllQ w).re) (Metric.ball (0 : ℂ) (1 / 2)) :=
    Complex.reCLM.contDiff.comp_contDiffOn (hcd_C.restrict_scalars ℝ)
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => ((π * t / 2 : ℝ) : ℂ)) (Ioo (-1 / 4) (1 / 4)) :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2)).contDiffOn
  refine contDiffOn_const.mul (hcd_R.comp hmap fun t ht => ?_)
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
    show |(2 : ℝ)| = 2 by norm_num]
  have habs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  nlinarith [Real.pi_lt_four, abs_nonneg t]

lemma contDiffOn_mD : ContDiffOn ℝ (⊤ : ℕ∞) mD (Ioo (-1 / 4) (1 / 4)) := by
  have hana : AnalyticOnNhd ℂ compEllD (Metric.ball (0 : ℂ) (1 / 2)) :=
    differentiableOn_compEllD.analyticOnNhd Metric.isOpen_ball
  have hcd_C : ContDiffOn ℂ (⊤ : ℕ∞) compEllD (Metric.ball (0 : ℂ) (1 / 2)) :=
    hana.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  have hcd_R : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => (compEllD w).re) (Metric.ball (0 : ℂ) (1 / 2)) :=
    Complex.reCLM.contDiff.comp_contDiffOn (hcd_C.restrict_scalars ℝ)
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => ((π * t / 2 : ℝ) : ℂ)) (Ioo (-1 / 4) (1 / 4)) :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2)).contDiffOn
  refine contDiffOn_const.mul (hcd_R.comp hmap fun t ht => ?_)
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
    show |(2 : ℝ)| = 2 by norm_num]
  have habs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  nlinarith [Real.pi_lt_four, abs_nonneg t]

lemma mQ_zero : mQ 0 = π ^ 2 / 12 := by
  have hcont : ContinuousAt mQ 0 :=
    (contDiffOn_mQ.continuousOn).continuousAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  have htend1 : Tendsto mQ (𝓝[>] (0 : ℝ)) (𝓝 (mQ 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have htend2 : Tendsto mQ (𝓝[>] (0 : ℝ)) (𝓝 (π ^ 2 / 12)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_
      (show Tendsto (fun t : ℝ => (6 * π ^ 4 / 16) * t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) by
        simpa using (((continuous_id.pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul (6 * π ^ 4 / 16))
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    have hx0 : 0 < π * t / 2 := by positivity
    have hx1 : π * t / 2 ≤ 1 / 2 := by nlinarith [Real.pi_lt_four, ht.2]
    have h4 := ceEll_taylor4 hx0 hx1
    have hmq : mQ t = ceEll (π * t / 2) / t ^ 2 := by
      have := uctM_eq_sq_mul_mQ ht0
      unfold uctM at this
      field_simp [ht0.ne'] at this ⊢; linarith
    rw [Real.norm_eq_abs, hmq]
    have hsub : ceEll (π * t / 2) / t ^ 2 - π ^ 2 / 12 =
        ((ceEll (π * t / 2) - ((π * t / 2) ^ 2 / 3 - 7 / 90 * (π * t / 2) ^ 4)) - 7 / 90 * (π * t / 2) ^ 4) / t ^ 2 := by
      field_simp [ht0.ne']; ring
    rw [hsub, abs_div, abs_pow, abs_of_pos ht0]
    have htri := abs_sub (ceEll (π * t / 2) - ((π * t / 2) ^ 2 / 3 - 7 / 90 * (π * t / 2) ^ 4)) (7 / 90 * (π * t / 2) ^ 4)
    have h4' : |7 / 90 * (π * t / 2) ^ 4| = 7 / 90 * (π * t / 2) ^ 4 := abs_of_nonneg (by positivity)
    have h6 : (π * t / 2) ^ 6 ≤ (1 / 4) * (π * t / 2) ^ 4 := by
      have : (π * t / 2) ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [pow_nonneg hx0.le 4]
    have hnum : |(ceEll (π * t / 2) - ((π * t / 2) ^ 2 / 3 - 7 / 90 * (π * t / 2) ^ 4)) - 7 / 90 * (π * t / 2) ^ 4| ≤
        6 * (π * t / 2) ^ 4 := by
      have htri' : |(ceEll (π * t / 2) - ((π * t / 2) ^ 2 / 3 - 7 / 90 * (π * t / 2) ^ 4)) - 7 / 90 * (π * t / 2) ^ 4| ≤
          |ceEll (π * t / 2) - ((π * t / 2) ^ 2 / 3 - 7 / 90 * (π * t / 2) ^ 4)| + |7 / 90 * (π * t / 2) ^ 4| :=
        abs_sub _ _
      have hx4 : 0 ≤ (π * t / 2) ^ 4 := pow_nonneg hx0.le 4
      linarith [h4, htri', h4', h6, hx4]
    calc |(ceEll (π * t / 2) - ((π * t / 2) ^ 2 / 3 - 7 / 90 * (π * t / 2) ^ 4)) - 7 / 90 * (π * t / 2) ^ 4| / t ^ 2
        ≤ (6 * (π * t / 2) ^ 4) / t ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg t)
      _ = (6 * π ^ 4 / 16) * t ^ 2 := by field_simp [ht0.ne']; ring
  exact tendsto_nhds_unique htend1 htend2

lemma mD_zero : mD 0 = π ^ 2 / 6 := by
  have hcontD : ContinuousAt mD 0 :=
    (contDiffOn_mD.continuousOn).continuousAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  have hcontQ : ContinuousAt mQ 0 :=
    (contDiffOn_mQ.continuousOn).continuousAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  have hcontQ' : ContinuousAt (deriv mQ) 0 := by
    have h1 := contDiffOn_mQ.deriv_of_isOpen isOpen_Ioo (m := (0 : ℕ∞)) (by simp)
    exact h1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))
  have htend1 : Tendsto mD (𝓝[>] (0 : ℝ)) (𝓝 (mD 0)) := hcontD.tendsto.mono_left nhdsWithin_le_nhds
  have htend2 : Tendsto (fun t : ℝ => 2 * mQ t + t * deriv mQ t) (𝓝[>] (0 : ℝ)) (𝓝 (2 * mQ 0 + 0 * deriv mQ 0)) :=
    ((hcontQ.tendsto.const_mul 2).add (tendsto_id.mul hcontQ'.tendsto)).mono_left nhdsWithin_le_nhds
  have heq : ∀ᶠ t in 𝓝[>] (0 : ℝ), mD t = 2 * mQ t + t * deriv mQ t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 / 4 := ht.2
    have hmem : t ∈ Ioo (-1 / 4 : ℝ) (1 / 4) := ⟨by linarith, ht1⟩
    have hd1 : HasDerivAt uctM (uctMderiv t) t := hasDerivAt_uctM ht0
    have hdQ : HasDerivAt mQ (deriv mQ t) t :=
      ((contDiffOn_mQ.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem)).hasDerivAt
    have hd2 : HasDerivAt (fun s : ℝ => s ^ 2 * mQ s) (2 * t * mQ t + t ^ 2 * deriv mQ t) t := by
      have := (hasDerivAt_pow 2 t).mul hdQ
      exact this.congr_deriv (by ring)
    have hev : uctM =ᶠ[𝓝 t] fun s => s ^ 2 * mQ s := by
      filter_upwards [Ioi_mem_nhds ht0] with s hs using uctM_eq_sq_mul_mQ hs
    have hderiv_eq := hd1.unique (hd2.congr_of_eventuallyEq hev)
    rw [uctMderiv_eq_mul_mD ht0 ht1] at hderiv_eq
    have hmul : t * mD t = t * (2 * mQ t + t * deriv mQ t) := by linarith
    exact mul_left_cancel₀ ht0.ne' hmul
  have hlim := tendsto_nhds_unique htend1 (htend2.congr' (heq.mono fun _ h => h.symm))
  rw [hlim, zero_mul, add_zero, mQ_zero]; ring

lemma mQ_pos_of_mem {t : ℝ} (_ht : |t| < 1 / 4) : 0 < mQ t := by
  by_cases ht0 : t = 0
  · rw [ht0, mQ_zero]; positivity
  · have habs : 0 < |t| := abs_pos.mpr ht0
    have h1 := uctM_eq_sq_mul_mQ habs
    have h2 : mQ |t| = mQ t := by
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mQ_even]
    rw [h2] at h1
    have hm_pos : 0 < uctM |t| := uctM_pos habs
    have hsq : 0 < |t| ^ 2 := sq_pos_of_pos habs
    nlinarith

lemma mD_pos_of_mem {t : ℝ} (ht : |t| < 1 / 4) : 0 < mD t := by
  by_cases ht0 : t = 0
  · rw [ht0, mD_zero]; positivity
  · have habs : 0 < |t| := abs_pos.mpr ht0
    have h1 := uctMderiv_eq_mul_mD habs ht
    have h2 : mD |t| = mD t := by
      rcases le_or_gt 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mD_even ht]
    rw [h2] at h1
    have hm_pos : 0 < uctMderiv |t| := uctMderiv_pos habs
    nlinarith

/-! ### Smooth local extension `r0Smooth` and `f0Base = -log r0Smooth` -/

/-- Smooth real even extension of `r₀(t)` on `(-1/4, 1/4)`. -/
noncomputable def r0Smooth (kind : StripKernelChoice) (t : ℝ) : ℝ :=
  let sQ := (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re
  let hFac := match kind with
    | .ce => 1 / sQ ^ 2
    | .star => 1 / sQ ^ 2 + (π * t / 2) ^ 2 / Real.cosh (π * t / 2) ^ 2
  (4 * Real.sqrt 3 / π) * hFac * (mQ t) ^ (3 / 2 : ℝ) / mD t

lemma r0Smooth_even {kind : StripKernelChoice} {t : ℝ} (ht : |t| < 1 / 4) :
    r0Smooth kind (-t) = r0Smooth kind t := by
  unfold r0Smooth
  have hq : CtOuter.sinhQ (((π * -t / 2 : ℝ) : ℂ)) = CtOuter.sinhQ (((π * t / 2 : ℝ) : ℂ)) := by
    rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg]
    unfold CtOuter.sinhQ
    refine tsum_congr fun n => ?_
    rw [(even_two_mul n).neg_pow]
  have hc : Real.cosh (π * -t / 2) = Real.cosh (π * t / 2) := by
    rw [show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg]
  have hsq : (π * -t / 2) ^ 2 = (π * t / 2) ^ 2 := by ring
  cases kind <;> simp only [hq, hc, hsq, mQ_even, mD_even ht]

lemma r0Smooth_zero (kind : StripKernelChoice) : r0Smooth kind 0 = 1 := by
  unfold r0Smooth
  have hq : (CtOuter.sinhQ (0 : ℂ)).re = 1 := by
    simp [CtOuter.sinhQ_zero]
  have hrpow : (π ^ 2 / 12 : ℝ) ^ (3 / 2 : ℝ) = π ^ 3 / (24 * Real.sqrt 3) := by
    have h1 : (π ^ 2 / 12 : ℝ) = (π / (2 * Real.sqrt 3)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    rw [div_pow, mul_pow, pow_succ (Real.sqrt 3) 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  cases kind <;> simp only [mul_zero, zero_div, Complex.ofReal_zero, hq, mQ_zero, mD_zero, hrpow,
    zero_pow two_ne_zero, add_zero, one_pow, div_one]
  · field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']; ring
  · field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']; ring

lemma r0Smooth_pos {kind : StripKernelChoice} {t : ℝ} (ht : |t| < 1 / 4) : 0 < r0Smooth kind t := by
  unfold r0Smooth
  have hx2 : ‖((π * t / 2 : ℝ) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [Real.pi_lt_four, abs_nonneg t]
  have hsQ_pos : 0 < (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re := CtOuter.re_sinhQ_pos hx2
  have hmQ_pos : 0 < mQ t := mQ_pos_of_mem ht
  have hmD_pos : 0 < mD t := mD_pos_of_mem ht
  cases kind <;> positivity

lemma r0Smooth_eq_stripR0 {kind : StripKernelChoice} {t : ℝ} (ht : |t| < 1 / 4) :
    r0Smooth kind t = stripR0 kind t := by
  by_cases ht0 : t = 0
  · rw [ht0, r0Smooth_zero]; simp [stripR0]
  · have habs : 0 < |t| := abs_pos.mpr ht0
    -- By evenness of both sides, reduce to `0 < t`
    suffices ∀ u : ℝ, 0 < u → u < 1 / 4 → r0Smooth kind u = stripR0 kind u by
      rcases lt_or_gt_of_ne ht0 with h | h
      · have h1 : r0Smooth kind t = r0Smooth kind (-t) := (r0Smooth_even ht).symm
        have h2 : stripR0 kind t = stripR0 kind (-t) := by
          unfold stripR0
          rw [ite_eq_right_iff.mpr fun h0 => absurd h0 ht0,
            ite_eq_right_iff.mpr fun h0 => absurd h0 (neg_ne_zero.mpr ht0), abs_neg]
          congr 2; congr 1
          cases kind
          · dsimp only [stripH0]; unfold uctHstar
            rw [Complex.ofReal_neg, neg_mul, mul_neg, Complex.cos_neg, Complex.sin_neg, neg_sq]
          · dsimp only [stripH0]; unfold uctHCE
            rw [Complex.ofReal_neg, neg_mul, mul_neg, neg_div, Complex.sin_neg, neg_sq]
        rw [h1, h2]
        exact this (-t) (neg_pos.mpr h) (by rwa [abs_of_neg h] at ht)
      · exact this t h (by rwa [abs_of_pos h] at ht)
    intro u hu0 hu1
    unfold r0Smooth stripR0
    rw [ite_eq_right_iff.mpr fun h => absurd h hu0.ne', abs_of_pos hu0, uctM_eq_sq_mul_mQ hu0,
      uctMderiv_eq_mul_mD hu0 hu1, uctAlphaOsc_eq]
    have hx : 0 < π * u / 2 := by positivity
    have hsQ : (CtOuter.sinhQ ((π * u / 2 : ℝ) : ℂ)).re = Real.sinh (π * u / 2) / (π * u / 2) := by
      rw [CtOuter.sinhQ_ofReal hx.ne', Complex.ofReal_re]
    have hmQ_pos : 0 < mQ u := mQ_pos_of_mem (by rw [abs_of_pos hu0]; exact hu1)
    have hmD_pos : 0 < mD u := mD_pos_of_mem (by rw [abs_of_pos hu0]; exact hu1)
    have hrpow : (u ^ 2 * mQ u) ^ (3 / 2 : ℝ) = u ^ 3 * (mQ u) ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (sq_nonneg u) hmQ_pos.le, ← Real.rpow_natCast u 2, ← Real.rpow_mul hu0.le]
      norm_num
    have hsh_pos : 0 < Real.sinh (π * u / 2) := Real.sinh_pos_iff.mpr hx
    have hch_pos : 0 < Real.cosh (π * u / 2) := Real.cosh_pos _
    rw [hrpow, hsQ]
    cases kind
    · have hHstar : ‖stripH0 .star ((u : ℂ) * Complex.I)‖ =
          π ^ 2 / (4 * Real.sinh (π * u / 2) ^ 2) + π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) := by
        dsimp only [stripH0]
        have hnotint : ∀ n : ℤ, ((u : ℂ) * Complex.I) ≠ n := fun n h => by
          have := congrArg Complex.im h; simp at this; linarith
        rw [uct_H_split hnotint, uctHCE_imag]
        have h1sub : uctHCE (1 - (u : ℂ) * Complex.I) =
            ((π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) : ℝ) : ℂ) := by
          have h := uctHCE_one_add_imag (-u)
          rw [show (1 : ℂ) + ((-u : ℝ) : ℂ) * Complex.I = 1 - (u : ℂ) * Complex.I by push_cast; ring,
            show π * -u / 2 = -(π * u / 2) by ring, Real.cosh_neg] at h
          exact h
        rw [h1sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          show -(π ^ 2 / (4 * Real.sinh (π * u / 2) ^ 2)) - π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) =
            -(π ^ 2 / (4 * Real.sinh (π * u / 2) ^ 2) + π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2)) by ring,
          abs_neg, abs_of_pos (by positivity)]
      rw [hHstar]
      field_simp [uctAlphaFl_pos.ne', Real.pi_ne_zero, hu0.ne', hsh_pos.ne', hch_pos.ne', hmD_pos.ne']
      ring
    · have hHCE : ‖stripH0 .ce ((u : ℂ) * Complex.I)‖ = π ^ 2 / (4 * Real.sinh (π * u / 2) ^ 2) := by
        dsimp only [stripH0]
        rw [uctHCE_imag, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
      rw [hHCE]
      field_simp [uctAlphaFl_pos.ne', Real.pi_ne_zero, hu0.ne', hsh_pos.ne', hmD_pos.ne']
      ring

lemma contDiffOn_r0Smooth (kind : StripKernelChoice) :
    ContDiffOn ℝ (⊤ : ℕ∞) (r0Smooth kind) (Ioo (-1 / 4) (1 / 4)) := by
  have hsQ_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re) (Ioo (-1 / 4) (1 / 4)) := by
    have hana : AnalyticOnNhd ℂ CtOuter.sinhQ univ :=
      (CtOuter.differentiable_sinhQ.differentiableOn).analyticOnNhd isOpen_univ
    have hcd_C : ContDiff ℂ (⊤ : ℕ∞) CtOuter.sinhQ :=
      contDiffOn_univ.mp (hana.contDiffOn isOpen_univ.uniqueDiffOn)
    have hcd_R : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (CtOuter.sinhQ w).re) :=
      Complex.reCLM.contDiff.comp (hcd_C.restrict_scalars ℝ)
    exact (hcd_R.comp (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2))).contDiffOn
  have hsQ_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2 ≠ 0 := by
    intro t ht
    have hx2 : ‖((π * t / 2 : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
        show |(2 : ℝ)| = 2 by norm_num]
      have habs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      nlinarith [Real.pi_lt_four, abs_nonneg t]
    exact pow_ne_zero 2 (CtOuter.re_sinhQ_pos hx2).ne'
  have hmQ_rpow : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (mQ t) ^ (3 / 2 : ℝ)) (Ioo (-1 / 4) (1 / 4)) := by
    intro t ht
    have habs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (Real.contDiffAt_rpow_const_of_ne (mQ_pos_of_mem habs).ne').comp_contDiffWithinAt t (contDiffOn_mQ t ht)
  have hmD_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), mD t ≠ 0 := fun t ht =>
    (mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  unfold r0Smooth
  cases kind
  · have hfac : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun t : ℝ => 1 / (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2 +
          (π * t / 2) ^ 2 / Real.cosh (π * t / 2) ^ 2) (Ioo (-1 / 4) (1 / 4)) := by
      refine (contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne).add ?_
      refine (((contDiff_const.mul contDiff_id).div_const 2).pow 2).contDiffOn.div
        ((Real.contDiff_cosh.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2).contDiffOn
        fun t _ => pow_ne_zero 2 (Real.cosh_pos _).ne'
    exact ((contDiffOn_const.mul hfac).mul hmQ_rpow).div contDiffOn_mD hmD_ne
  · have hfac : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun t : ℝ => 1 / (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2) (Ioo (-1 / 4) (1 / 4)) :=
      contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne
    exact ((contDiffOn_const.mul hfac).mul hmQ_rpow).div contDiffOn_mD hmD_ne

/-- Base target `f_0^base(t) = -log (r0Smooth kind t)`. -/
noncomputable def f0Base (kind : StripKernelChoice) (t : ℝ) : ℝ := -Real.log (r0Smooth kind t)

lemma f0Base_zero (kind : StripKernelChoice) : f0Base kind 0 = 0 := by
  simp [f0Base, r0Smooth_zero]

lemma f0Base_even {kind : StripKernelChoice} {t : ℝ} (ht : |t| < 1 / 4) :
    f0Base kind (-t) = f0Base kind t := by
  simp [f0Base, r0Smooth_even ht]

lemma contDiffOn_f0Base (kind : StripKernelChoice) :
    ContDiffOn ℝ (⊤ : ℕ∞) (f0Base kind) (Ioo (-1 / 4) (1 / 4)) := by
  unfold f0Base
  refine ContDiffOn.neg ?_
  intro t ht
  have habs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact (Real.contDiffAt_log.mpr (r0Smooth_pos habs).ne').comp_contDiffWithinAt t (contDiffOn_r0Smooth kind t ht)

/-! ### Generic derivative scaling for any fixed even `C^∞` target with `f(0) = 0` -/

/-- If `f` is `C^∞` on `(-1/4, 1/4)`, even on `(-1/4, 1/4)`, and `f(0) = 0`, then for every `r : ℕ`,
there is `C_r ≥ 0` such that for all `0 < τ₁ ≤ 1/16` and `t ∈ [-3τ₁, 3τ₁]`,
`|iteratedDeriv r f t| ≤ C_r * τ₁^{2 - r}`. -/
lemma even_smooth_target_bounds {f : ℝ → ℝ}
    (hcd : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioo (-1 / 4) (1 / 4)))
    (heven : ∀ t, |t| < 1 / 4 → f (-t) = f t) (hf0 : f 0 = 0) :
    ∀ r : ℕ, ∃ C ≥ 0, ∀ {τ₁ : ℝ}, 0 < τ₁ → τ₁ ≤ 1 / 16 →
      ∀ t ∈ Icc (-3 * τ₁) (3 * τ₁), |iteratedDeriv r f t| ≤ C * τ₁ ^ ((2 : ℤ) - r) := by
  have hcont_k : ∀ k : ℕ, ContinuousOn (iteratedDeriv k f) (Icc (-3 / 16) (3 / 16)) := by
    intro k
    have hsub : Icc (-3 / 16 : ℝ) (3 / 16) ⊆ Ioo (-1 / 4) (1 / 4) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) (Ioo (-1 / 4) (1 / 4)) := by
      induction k with
      | zero => simpa using hcd
      | succ k ih =>
        rw [show iteratedDeriv (k + 1) f = deriv (iteratedDeriv k f) by ext x; rw [iteratedDeriv_succ]]
        exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
    exact (h1.continuousOn).mono hsub
  have hB : ∀ k : ℕ, ∃ B ≥ 0, ∀ x ∈ Icc (-3 / 16 : ℝ) (3 / 16), |iteratedDeriv k f x| ≤ B := by
    intro k
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-3 / 16 : ℝ)) (b := 3 / 16)).exists_bound_of_continuousOn (hcont_k k)
    refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
    have h1 : |iteratedDeriv k f x| ≤ B := by simpa [Real.norm_eq_abs] using hB x hx
    exact h1.trans (le_max_left _ _)
  have hf'_zero : deriv f 0 = 0 := by
    have hd := ((hcd.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))).hasDerivAt
    have hd' : HasDerivAt f (deriv f (-0)) (-0) := by simpa using hd
    have hneg : HasDerivAt (fun x => f (-x)) (-deriv f 0) 0 := by
      have h := hd'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      simp only [neg_zero, mul_neg, mul_one] at h
      exact h
    have hev : (fun x => f (-x)) =ᶠ[𝓝 (0 : ℝ)] f := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 4 by norm_num)] with x hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
      exact heven x hx
    have heq := (hd.congr_of_eventuallyEq hev).unique hneg
    linarith
  obtain ⟨B₂, hB₂_nn, hB₂⟩ := hB 2
  intro r
  match r with
  | 0 =>
    refine ⟨9 * B₂, by positivity, fun {τ₁} hτ₁ hτ₁16 t ht => ?_⟩
    -- `|f(t)| ≤ B₂ * t² ≤ 9 B₂ τ₁²` via MVT twice
    have hsub : Icc (-3 * τ₁) (3 * τ₁) ⊆ Icc (-3 / 16) (3 / 16) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hderiv1 : ∀ x ∈ Icc (-3 * τ₁) (3 * τ₁), |deriv f x| ≤ B₂ * |x| := by
      intro x hx
      have hdiff : ∀ y ∈ Icc (-3 / 16 : ℝ) (3 / 16), DifferentiableAt ℝ (deriv f) y := fun y hy => by
        have hcd1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv f) (Ioo (-1 / 4) (1 / 4)) :=
          hcd.deriv_of_isOpen isOpen_Ioo (by simp)
        exact (hcd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds ⟨by linarith [hy.1], by linarith [hy.2]⟩)
      have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (s := Icc (-3 / 16 : ℝ) (3 / 16))
        (C := B₂) (fun y hy => hdiff y hy)
        (fun y hy => by
          rw [Real.norm_eq_abs, show deriv (deriv f) y = iteratedDeriv 2 f y by
            rw [iteratedDeriv_succ, iteratedDeriv_one]]
          exact hB₂ y hy)
        (convex_Icc _ _) (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (-3 / 16) (3 / 16)) (hsub hx)
      simpa [hf'_zero, Real.norm_eq_abs] using hlip
    have hlip0 := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Icc (-3 * τ₁) (3 * τ₁))
      (C := B₂ * (3 * τ₁))
      (fun y hy => (hcd.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds ⟨by linarith [(hsub hy).1], by linarith [(hsub hy).2]⟩))
      (fun y hy => by
        rw [Real.norm_eq_abs]
        have habs : |y| ≤ 3 * τ₁ := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
        exact (hderiv1 y hy).trans (mul_le_mul_of_nonneg_left habs hB₂_nn))
      (convex_Icc _ _) (show (0 : ℝ) ∈ Icc (-3 * τ₁) (3 * τ₁) from ⟨by linarith, by linarith⟩) ht
    simp only [hf0, sub_zero, Real.norm_eq_abs, iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hlip0 ⊢
    have habs : |t| ≤ 3 * τ₁ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc |f t| ≤ B₂ * (3 * τ₁) * |t| := hlip0
      _ ≤ B₂ * (3 * τ₁) * (3 * τ₁) := mul_le_mul_of_nonneg_left habs (by positivity)
      _ = 9 * B₂ * τ₁ ^ (2 : ℤ) := by rw [zpow_two]; ring
  | 1 =>
    refine ⟨3 * B₂, by positivity, fun {τ₁} hτ₁ hτ₁16 t ht => ?_⟩
    have hsub : Icc (-3 * τ₁) (3 * τ₁) ⊆ Icc (-3 / 16) (3 / 16) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hdiff : ∀ y ∈ Icc (-3 / 16 : ℝ) (3 / 16), DifferentiableAt ℝ (deriv f) y := fun y hy => by
      have hcd1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv f) (Ioo (-1 / 4) (1 / 4)) :=
        hcd.deriv_of_isOpen isOpen_Ioo (by simp)
      exact (hcd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (s := Icc (-3 / 16 : ℝ) (3 / 16))
      (C := B₂) (fun y hy => hdiff y hy)
      (fun y hy => by
        rw [Real.norm_eq_abs, show deriv (deriv f) y = iteratedDeriv 2 f y by
          rw [iteratedDeriv_succ, iteratedDeriv_one]]
        exact hB₂ y hy)
      (convex_Icc _ _) (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (-3 / 16) (3 / 16)) (hsub ht)
    simp only [hf'_zero, sub_zero, Real.norm_eq_abs, iteratedDeriv_one, Nat.cast_one] at hlip ⊢
    have habs : |t| ≤ 3 * τ₁ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc |deriv f t| ≤ B₂ * |t| := hlip
      _ ≤ B₂ * (3 * τ₁) := mul_le_mul_of_nonneg_left habs hB₂_nn
      _ = 3 * B₂ * τ₁ ^ ((2 : ℤ) - 1) := by norm_num; ring
  | k + 2 =>
    obtain ⟨B, hB_nn, hB_bd⟩ := hB (k + 2)
    refine ⟨B, hB_nn, fun {τ₁} hτ₁ hτ₁16 t ht => ?_⟩
    have ht_in : t ∈ Icc (-3 / 16 : ℝ) (3 / 16) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpow_ge : (1 : ℝ) ≤ τ₁ ^ ((2 : ℤ) - ((k + 2 : ℕ) : ℤ)) := by
      have hexp : (2 : ℤ) - ((k + 2 : ℕ) : ℤ) = -(k : ℤ) := by omega
      rw [hexp, zpow_neg, zpow_natCast]
      exact one_le_inv₀ (pow_pos hτ₁ k) |>.mpr (pow_le_one₀ hτ₁.le (by linarith))
    calc |iteratedDeriv (k + 2) f t| ≤ B := hB_bd t ht_in
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * τ₁ ^ ((2 : ℤ) - ((k + 2 : ℕ) : ℤ)) := mul_le_mul_of_nonneg_left hpow_ge hB_nn

/-! ### Hadamard division for `Δ_curv(t) = (1/(2c)) (ϑ''(t)/m'(t) - ϑ'(t)/m(t))` -/

/-- Hadamard integral `divT_theta2 θ t = ∫₀¹ θ'''(s t) ds` (equals `θ''(t)/t` when `θ''(0) = 0`). -/
noncomputable def divT_theta2 (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, iteratedDeriv 3 θ (s * t)

/-- Hadamard integral `divT2_theta1 θ t = ∫₀¹ (1 - s) θ'''(s t) ds` (equals `θ'(t)/t²` when `θ'(0) = θ''(0) = 0`). -/
noncomputable def divT2_theta1 (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * iteratedDeriv 3 θ (s * t)

/-- Smooth curvature target `Δ_curv(t)` on `(-1/4, 1/4)`. -/
noncomputable def deltaCurvSmooth (c : ℝ) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / (2 * c)) * (divT_theta2 θ t / mD t - divT2_theta1 θ t / mQ t)

lemma divT_theta2_eq_div {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ20 : iteratedDeriv 2 θ 0 = 0)
    {t : ℝ} (ht : t ≠ 0) :
    divT_theta2 θ t = iteratedDeriv 2 θ t / t := by
  unfold divT_theta2
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u => iteratedDeriv 2 θ (u * t) / t) (iteratedDeriv 3 θ (s * t)) s := by
    intro s _
    have h1 := ((contDiff_iteratedDeriv_infty hθ 2).differentiable (by simp) (s * t)).hasDerivAt
    have h2 := (h1.comp s ((hasDerivAt_id s).mul_const t)).div_const t
    refine h2.congr_deriv ?_
    rw [← iteratedDeriv_succ]
    field_simp [ht]
  have hcont : Continuous (fun s : ℝ => iteratedDeriv 3 θ (s * t)) :=
    (contDiff_iteratedDeriv_infty hθ 3).continuous.comp (continuous_id.mul continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
  simp [hθ20]

lemma divT2_theta1_eq_div {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθ10 : deriv θ 0 = 0) (hθ20 : iteratedDeriv 2 θ 0 = 0) {t : ℝ} (ht : t ≠ 0) :
    divT2_theta1 θ t = deriv θ t / t ^ 2 := by
  unfold divT2_theta1
  -- Antiderivative: `P(s) = ((1 - s) * θ''(st) * t + θ'(st)) / t^2`!
  -- Check: `P'(s) = (-θ''(st)*t + (1-s)*θ'''(st)*t^2 + θ''(st)*t) / t^2 = (1 - s) * θ'''(st)`!
  -- And `P(1) - P(0) = (θ'(t) - (θ''(0)*t + θ'(0))) / t^2 = θ'(t) / t^2`!
  let P : ℝ → ℝ := fun s => ((1 - s) * iteratedDeriv 2 θ (s * t) * t + deriv θ (s * t)) / t ^ 2
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt P ((1 - s) * iteratedDeriv 3 θ (s * t)) s := by
    intro s _
    have h1 : HasDerivAt (fun u : ℝ => (1 - u)) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ => iteratedDeriv 2 θ (u * t)) (iteratedDeriv 3 θ (s * t) * t) s := by
      have ha := ((contDiff_iteratedDeriv_infty hθ 2).differentiable (by simp) (s * t)).hasDerivAt
      have h := ha.comp s ((hasDerivAt_id s).mul_const t)
      rw [← iteratedDeriv_succ] at h
      simpa [Function.comp_def] using h
    have h3 : HasDerivAt (fun u : ℝ => deriv θ (u * t)) (iteratedDeriv 2 θ (s * t) * t) s := by
      have ha := ((contDiff_iteratedDeriv_infty hθ 1).differentiable (by simp) (s * t)).hasDerivAt
      rw [show iteratedDeriv 1 θ = deriv θ by ext x; exact congrFun (iteratedDeriv_one (f := θ)) x] at ha
      have h := ha.comp s ((hasDerivAt_id s).mul_const t)
      rw [show deriv (deriv θ) (s * t) = iteratedDeriv 2 θ (s * t) by
        rw [iteratedDeriv_succ, iteratedDeriv_one]] at h
      simpa [Function.comp_def] using h
    have hcomb := (((h1.mul h2).mul_const t).add h3).div_const (t ^ 2)
    refine hcomb.congr_deriv ?_
    field_simp [ht]; ring
  have hcont : Continuous (fun s : ℝ => (1 - s) * iteratedDeriv 3 θ (s * t)) :=
    (continuous_const.sub continuous_id).mul ((contDiff_iteratedDeriv_infty hθ 3).continuous.comp (continuous_id.mul continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
  simp [P, hθ10, hθ20]

lemma deltaCurvSmooth_eq {c : ℝ} {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθ10 : deriv θ 0 = 0) (hθ20 : iteratedDeriv 2 θ 0 = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 4) :
    deltaCurvSmooth c θ t = (1 / (2 * c)) * (iteratedDeriv 2 θ t / uctMderiv t - deriv θ t / uctM t) := by
  unfold deltaCurvSmooth
  rw [divT_theta2_eq_div hθ hθ20 ht0.ne', divT2_theta1_eq_div hθ hθ10 hθ20 ht0.ne',
    uctMderiv_eq_mul_mD ht0 ht1, uctM_eq_sq_mul_mQ ht0]
  congr 1; ring

lemma deltaCurvSmooth_even {c : ℝ} {θ : ℝ → ℝ} (hθ_odd : ∀ t, θ (-t) = -θ t)
    {t : ℝ} (ht : |t| < 1 / 4) :
    deltaCurvSmooth c θ (-t) = deltaCurvSmooth c θ t := by
  have h3_even : ∀ u, iteratedDeriv 3 θ (-u) = iteratedDeriv 3 θ u := fun u => by
    have h := iteratedDeriv_odd_fn θ hθ_odd 3 u
    norm_num at h; exact h
  have h1 : divT_theta2 θ (-t) = divT_theta2 θ t := by
    unfold divT_theta2
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [mul_neg, h3_even]
  have h2 : divT2_theta1 θ (-t) = divT2_theta1 θ t := by
    unfold divT2_theta1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [mul_neg, h3_even]
  unfold deltaCurvSmooth
  rw [h1, h2, mD_even ht, mQ_even]

/-- Derivative under the integral sign for `t ↦ ∫₀¹ w(s) f(s t) ds` for any smooth `f` and continuous `w`. -/
lemma hasDerivAt_hadamard_integral {w f : ℝ → ℝ} (hw : Continuous w) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..1, w s * f (s * x))
      (∫ s in (0 : ℝ)..1, (w s * s) * deriv f (s * t)) t := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(|t| + 1)) (b := |t| + 1)).exists_bound_of_continuousOn
    (hf.continuous_deriv (by simp)).continuousOn
  obtain ⟨Bw, hBw⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hw.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hBw0 : 0 ≤ max Bw 0 := le_max_right _ _
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x s => w s * f (s * x))
    (F' := fun x s => (w s * s) * deriv f (s * x))
    (a := 0) (b := 1) (x₀ := t) (s := Metric.ball t 1) (Metric.ball_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun x =>
      (hw.mul (hf.continuous.comp (continuous_id.mul continuous_const))).aestronglyMeasurable)
    ((hw.mul (hf.continuous.comp (continuous_id.mul continuous_const))).intervalIntegrable _ _)
    ((hw.mul continuous_id |>.mul ((hf.continuous_deriv (by simp)).comp (continuous_id.mul continuous_const))).aestronglyMeasurable)
    (by
      refine Filter.Eventually.of_forall fun s hs x hx => ?_
      rw [uIoc_of_le zero_le_one] at hs
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      have hsx : s * x ∈ Icc (-(|t| + 1)) (|t| + 1) := by
        have hx_abs : |x| ≤ |t| + 1 := by
          have := abs_sub_abs_le_abs_sub x t; linarith
        have habs : |s * x| ≤ |t| + 1 := by
          rw [abs_mul, abs_of_nonneg hs01.1]
          calc s * |x| ≤ 1 * (|t| + 1) := mul_le_mul hs01.2 hx_abs (abs_nonneg _) zero_le_one
            _ = |t| + 1 := one_mul _
        exact abs_le.mp habs
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs01.1]
      have hw_le0 : |w s| ≤ Bw := by simpa [Real.norm_eq_abs] using hBw s hs01
      have hw_le : |w s| ≤ max Bw 0 := hw_le0.trans (le_max_left _ _)
      have hf_le0 : |deriv f (s * x)| ≤ B := by simpa [Real.norm_eq_abs] using hB (s * x) hsx
      have hf_le : |deriv f (s * x)| ≤ max B 0 := hf_le0.trans (le_max_left _ _)
      calc |w s| * s * |deriv f (s * x)| ≤ (max Bw 0 * 1) * max B 0 :=
            mul_le_mul (mul_le_mul hw_le hs01.2 hs01.1 hBw0) hf_le (abs_nonneg _) (by positivity)
        _ = max Bw 0 * max B 0 := by ring)
    (intervalIntegrable_const (μ := volume))
    (Filter.Eventually.of_forall fun s _ x _ => by
      have h1 := ((hf.differentiable (by simp) (s * x)).hasDerivAt).comp x ((hasDerivAt_id x).const_mul s)
      have h2 := h1.const_mul (w s)
      refine h2.congr_deriv ?_; ring)
  exact hd.2

/-- All-order derivative formula for `t ↦ ∫₀¹ w(s) f(s t) ds`. -/
lemma iteratedDeriv_hadamard_integral (r : ℕ) {w f : ℝ → ℝ} (hw : Continuous w) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ t : ℝ, iteratedDeriv r (fun x => ∫ s in (0 : ℝ)..1, w s * f (s * x)) t =
      ∫ s in (0 : ℝ)..1, (w s * s ^ r) * iteratedDeriv r f (s * t) := by
  induction r generalizing w f with
  | zero => intro t; simp
  | succ r ih =>
    intro t
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv r (fun x => ∫ s in (0 : ℝ)..1, w s * f (s * x)) =
        fun x => ∫ s in (0 : ℝ)..1, (w s * s ^ r) * iteratedDeriv r f (s * x) :=
      funext (ih hw hf)
    rw [hfun]
    have hd := hasDerivAt_hadamard_integral (w := fun s => w s * s ^ r) (f := iteratedDeriv r f)
      (hw.mul (continuous_id.pow r)) (contDiff_iteratedDeriv_infty hf r) t
    rw [hd.deriv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [pow_succ, ← iteratedDeriv_succ]; ring

/-- Smoothness of `t ↦ ∫₀¹ w(s) f(s t) ds`. -/
lemma contDiff_hadamard_integral {w f : ℝ → ℝ} (hw : Continuous w) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ s in (0 : ℝ)..1, w s * f (s * x)) := by
  have hfin : ∀ n : ℕ, ∀ (w f : ℝ → ℝ), Continuous w → ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => ∫ s in (0 : ℝ)..1, w s * f (s * x)) := by
    intro n
    induction n with
    | zero =>
      intro w f hw hf
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_hadamard_integral hw hf t).continuousAt
    | succ n ih =>
      intro w f hw hf
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t => (hasDerivAt_hadamard_integral hw hf t).differentiableAt, by simp, ?_⟩
      have hfun : deriv (fun x => ∫ s in (0 : ℝ)..1, w s * f (s * x)) =
          fun t => ∫ s in (0 : ℝ)..1, (w s * s) * deriv f (s * t) :=
        funext fun t => (hasDerivAt_hadamard_integral hw hf t).deriv
      rw [hfun]
      have hdf : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := by
        rw [show deriv f = iteratedDeriv 1 f by ext x; exact (congrFun (iteratedDeriv_one (f := f)) x).symm]
        exact contDiff_iteratedDeriv_infty hf 1
      exact ih (fun s => w s * s) (deriv f) (hw.mul continuous_id) hdf
  exact contDiff_infty.mpr fun n => hfin n w f hw hf

lemma contDiffOn_deltaCurvSmooth {c : ℝ} {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (deltaCurvSmooth c θ) (Ioo (-1 / 4) (1 / 4)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (divT_theta2 θ) := by
    have := contDiff_hadamard_integral (w := fun _ => 1) (f := iteratedDeriv 3 θ)
      continuous_const (contDiff_iteratedDeriv_infty hθ 3)
    unfold divT_theta2
    simpa only [one_mul] using this
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (divT2_theta1 θ) :=
    contDiff_hadamard_integral (w := fun s => 1 - s) (f := iteratedDeriv 3 θ)
      (continuous_const.sub continuous_id) (contDiff_iteratedDeriv_infty hθ 3)
  have hmD_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), mD t ≠ 0 := fun t ht =>
    (mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  have hmQ_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), mQ t ≠ 0 := fun t ht =>
    (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  unfold deltaCurvSmooth
  exact contDiffOn_const.mul ((h1.contDiffOn.div contDiffOn_mD hmD_ne).sub (h2.contDiffOn.div contDiffOn_mQ hmQ_ne))

/-- Quantitative all-order derivative bound for `deltaCurvSmooth c θ` on `[-3τ₁, 3τ₁]`:
if `|θ^{(k)}(u)| ≤ B_k * M * τ₁^{2 - k}` on `|u| ≤ 3τ₁` for all `k`, then
`|∂_t^r (deltaCurvSmooth c θ)(t)| ≤ C_r * (c⁻¹ * M * τ₁^{-3}) * τ₁^{2 - r}` on `|t| ≤ 3τ₁`. -/
lemma abs_iteratedDeriv_deltaCurvSmooth_le (r : ℕ) (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) :
    ∃ C ≥ 0, ∀ {c M τ₁ : ℝ} {θ : ℝ → ℝ}, 0 < c → 0 ≤ M → 0 < τ₁ → τ₁ ≤ 1 / 16 →
      ContDiff ℝ (⊤ : ℕ∞) θ →
      (∀ k u, |u| ≤ 3 * τ₁ → |iteratedDeriv k θ u| ≤ B k * M * τ₁ ^ ((2 : ℤ) - k)) →
      ∀ t ∈ Icc (-3 * τ₁) (3 * τ₁),
        |iteratedDeriv r (deltaCurvSmooth c θ) t| ≤ C * (c⁻¹ * M * τ₁ ^ (-3 : ℤ)) * τ₁ ^ ((2 : ℤ) - r) := by
  -- Smooth reciprocal factors `invMD = 1/mD` and `invMQ = 1/mQ` have bounded derivatives on `[-3/16, 3/16]`
  have hinvMD_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => (mD t)⁻¹) (Ioo (-1 / 4) (1 / 4)) :=
    contDiffOn_mD.inv fun t ht => (mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  have hinvMQ_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => (mQ t)⁻¹) (Ioo (-1 / 4) (1 / 4)) :=
    contDiffOn_mQ.inv fun t ht => (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  have hbd_inv : ∀ (g : ℝ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) g (Ioo (-1 / 4) (1 / 4)) →
      ∀ k : ℕ, ∃ K ≥ 0, ∀ t ∈ Icc (-3 / 16 : ℝ) (3 / 16), |iteratedDeriv k g t| ≤ K := by
    intro g hg k
    have hcd_k : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k g) (Ioo (-1 / 4) (1 / 4)) := by
      induction k with
      | zero => simpa using hg
      | succ k ih =>
        rw [show iteratedDeriv (k + 1) g = deriv (iteratedDeriv k g) by ext x; rw [iteratedDeriv_succ]]
        exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
    have hsub : Icc (-3 / 16 : ℝ) (3 / 16) ⊆ Ioo (-1 / 4) (1 / 4) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-3 / 16 : ℝ)) (b := 3 / 16)).exists_bound_of_continuousOn
      ((hcd_k.continuousOn).mono hsub)
    refine ⟨max K 0, le_max_right _ _, fun t ht => ?_⟩
    have hK1 : |iteratedDeriv k g t| ≤ K := by simpa [Real.norm_eq_abs] using hK t ht
    exact hK1.trans (le_max_left _ _)
  have hKD : ∀ k, ∃ K ≥ 0, ∀ t ∈ Icc (-3 / 16 : ℝ) (3 / 16), |iteratedDeriv k (fun x => (mD x)⁻¹) t| ≤ K :=
    hbd_inv _ hinvMD_cd
  have hKQ : ∀ k, ∃ K ≥ 0, ∀ t ∈ Icc (-3 / 16 : ℝ) (3 / 16), |iteratedDeriv k (fun x => (mQ x)⁻¹) t| ≤ K :=
    hbd_inv _ hinvMQ_cd
  choose KD hKD_nn hKD_bd using hKD
  choose KQ hKQ_nn hKQ_bd using hKQ
  set C_sum : ℝ := (1 / 2) * ∑ j ∈ Finset.range (r + 1),
      ((Nat.choose r j : ℝ) * B (j + 3) * (KD (r - j) + KQ (r - j)))
  have hC_sum_nn : 0 ≤ C_sum := mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB (j + 3))) (add_nonneg (hKD_nn (r - j)) (hKQ_nn (r - j))))
  refine ⟨C_sum, hC_sum_nn,
    fun {c M τ₁ θ} hc hM hτ₁ hτ₁16 hθ hθ_bd t ht => ?_⟩
  have ht_abs : |t| ≤ 3 * τ₁ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht_in : t ∈ Icc (-3 / 16 : ℝ) (3 / 16) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ht_open : t ∈ Ioo (-1 / 4 : ℝ) (1 / 4) := ⟨by linarith [ht_in.1], by linarith [ht_in.2]⟩
  -- Derivative bounds on `divT_theta2 θ` and `divT2_theta1 θ` at `t`
  have hdiv2_bd : ∀ j : ℕ, |iteratedDeriv j (divT_theta2 θ) t| ≤ B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := by
    intro j
    have h1 := iteratedDeriv_hadamard_integral j (w := fun _ => 1) (f := iteratedDeriv 3 θ)
      continuous_const (contDiff_iteratedDeriv_infty hθ 3) t
    simp only [one_mul, iteratedDeriv_iteratedDeriv_eq] at h1
    unfold divT_theta2
    rw [h1]
    calc |∫ s in (0 : ℝ)..1, s ^ j * iteratedDeriv (j + 3) θ (s * t)|
        = ‖∫ s in (0 : ℝ)..1, s ^ j * iteratedDeriv (j + 3) θ (s * t)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in (0 : ℝ)..1, ‖s ^ j * iteratedDeriv (j + 3) θ (s * t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ s in (0 : ℝ)..1, B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := by
          refine intervalIntegral.integral_mono_on zero_le_one
            (((continuous_id.pow j).mul ((contDiff_iteratedDeriv_infty hθ (j + 3)).continuous.comp
              (continuous_id.mul continuous_const))).norm.intervalIntegrable _ _)
            (intervalIntegrable_const (μ := volume)) fun s hs => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs.1]
          have hst_abs : |s * t| ≤ 3 * τ₁ := by
            rw [abs_mul, abs_of_nonneg hs.1]
            calc s * |t| ≤ 1 * (3 * τ₁) := mul_le_mul hs.2 ht_abs (abs_nonneg _) zero_le_one
              _ = 3 * τ₁ := one_mul _
          have hpow1 : s ^ j ≤ 1 := pow_le_one₀ hs.1 hs.2
          have hθj := hθ_bd (j + 3) (s * t) hst_abs
          have hexp : (2 : ℤ) - ((j + 3 : ℕ) : ℤ) = (-1 : ℤ) - j := by omega
          rw [hexp] at hθj
          calc s ^ j * |iteratedDeriv (j + 3) θ (s * t)|
              ≤ 1 * (B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j)) :=
                mul_le_mul hpow1 hθj (abs_nonneg _) zero_le_one
            _ = B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := one_mul _
      _ = B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := by simp
  have hdiv1_bd : ∀ j : ℕ, |iteratedDeriv j (divT2_theta1 θ) t| ≤ B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := by
    intro j
    have h1 := iteratedDeriv_hadamard_integral j (w := fun s => 1 - s) (f := iteratedDeriv 3 θ)
      (continuous_const.sub continuous_id) (contDiff_iteratedDeriv_infty hθ 3) t
    simp only [iteratedDeriv_iteratedDeriv_eq] at h1
    change |iteratedDeriv j (fun x => ∫ s in (0 : ℝ)..1, (1 - s) * iteratedDeriv 3 θ (s * x)) t| ≤ _
    rw [h1]
    calc |∫ s in (0 : ℝ)..1, (1 - s) * s ^ j * iteratedDeriv (j + 3) θ (s * t)|
        = ‖∫ s in (0 : ℝ)..1, (1 - s) * s ^ j * iteratedDeriv (j + 3) θ (s * t)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in (0 : ℝ)..1, ‖(1 - s) * s ^ j * iteratedDeriv (j + 3) θ (s * t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ s in (0 : ℝ)..1, B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := by
          refine intervalIntegral.integral_mono_on zero_le_one
            ((((continuous_const.sub continuous_id).mul (continuous_id.pow j)).mul
              ((contDiff_iteratedDeriv_infty hθ (j + 3)).continuous.comp
                (continuous_id.mul continuous_const))).norm.intervalIntegrable _ _)
            (intervalIntegrable_const (μ := volume)) fun s hs => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by linarith [hs.2]), abs_pow, abs_of_nonneg hs.1]
          have hst_abs : |s * t| ≤ 3 * τ₁ := by
            rw [abs_mul, abs_of_nonneg hs.1]
            calc s * |t| ≤ 1 * (3 * τ₁) := mul_le_mul hs.2 ht_abs (abs_nonneg _) zero_le_one
              _ = 3 * τ₁ := one_mul _
          have h1s : (1 - s) * s ^ j ≤ 1 := by
            calc (1 - s) * s ^ j ≤ 1 * 1 := mul_le_mul (by linarith [hs.1]) (pow_le_one₀ hs.1 hs.2) (pow_nonneg hs.1 _) zero_le_one
              _ = 1 := one_mul 1
          have hθj := hθ_bd (j + 3) (s * t) hst_abs
          have hexp : (2 : ℤ) - ((j + 3 : ℕ) : ℤ) = (-1 : ℤ) - j := by omega
          rw [hexp] at hθj
          calc (1 - s) * s ^ j * |iteratedDeriv (j + 3) θ (s * t)|
              ≤ 1 * (B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j)) :=
                mul_le_mul h1s hθj (abs_nonneg _) zero_le_one
            _ = B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := one_mul _
      _ = B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - j) := by simp
  -- Leibniz rule on `deltaCurvSmooth c θ = (1/(2c)) * (divT_theta2 θ * mD⁻¹ - divT2_theta1 θ * mQ⁻¹)`
  have hdiv2_cd : ContDiff ℝ (⊤ : ℕ∞) (divT_theta2 θ) := by
    have h1 := contDiff_hadamard_integral (w := fun _ => 1) (f := iteratedDeriv 3 θ)
      continuous_const (contDiff_iteratedDeriv_infty hθ 3)
    unfold divT_theta2
    simpa only [one_mul] using h1
  have hdiv1_cd : ContDiff ℝ (⊤ : ℕ∞) (divT2_theta1 θ) :=
    contDiff_hadamard_integral (w := fun s => 1 - s) (f := iteratedDeriv 3 θ)
      (continuous_const.sub continuous_id) (contDiff_iteratedDeriv_infty hθ 3)
  have hinvMD_at : ContDiffAt ℝ (r : WithTop ℕ∞) (fun x => (mD x)⁻¹) t :=
    (hinvMD_cd.contDiffAt (isOpen_Ioo.mem_nhds ht_open)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hinvMQ_at : ContDiffAt ℝ (r : WithTop ℕ∞) (fun x => (mQ x)⁻¹) t :=
    (hinvMQ_cd.contDiffAt (isOpen_Ioo.mem_nhds ht_open)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hdiv2_at : ContDiffAt ℝ (r : WithTop ℕ∞) (divT_theta2 θ) t :=
    hdiv2_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdiv1_at : ContDiffAt ℝ (r : WithTop ℕ∞) (divT2_theta1 θ) t :=
    hdiv1_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hrew : deltaCurvSmooth c θ = fun x => (1 / (2 * c)) *
      (divT_theta2 θ x * (mD x)⁻¹ - divT2_theta1 θ x * (mQ x)⁻¹) := by
    ext x; unfold deltaCurvSmooth; simp [div_eq_mul_inv]
  rw [hrew, iteratedDeriv_const_mul_field]
  change |1 / (2 * c) * iteratedDeriv r ((fun x => divT_theta2 θ x * (mD x)⁻¹) -
      (fun x => divT2_theta1 θ x * (mQ x)⁻¹)) t| ≤ _
  rw [iteratedDeriv_sub (hdiv2_at.mul hinvMD_at) (hdiv1_at.mul hinvMQ_at),
    show (fun x => divT_theta2 θ x * (mD x)⁻¹) = divT_theta2 θ * (fun x => (mD x)⁻¹) from rfl,
    show (fun x => divT2_theta1 θ x * (mQ x)⁻¹) = divT2_theta1 θ * (fun x => (mQ x)⁻¹) from rfl,
    iteratedDeriv_mul hdiv2_at hinvMD_at, iteratedDeriv_mul hdiv1_at hinvMQ_at]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * c))]
  have hpow_le : ∀ j ∈ Finset.range (r + 1), τ₁ ^ ((-1 : ℤ) - j) ≤ τ₁ ^ ((-1 : ℤ) - r) := by
    intro j hj
    have hj_le : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdiff : τ₁ ^ ((-1 : ℤ) - r) = τ₁ ^ ((-1 : ℤ) - j) / τ₁ ^ (r - j) := by
      rw [show (-1 : ℤ) - r = ((-1 : ℤ) - j) - ((r - j : ℕ) : ℤ) by omega, zpow_sub₀ hτ₁.ne', zpow_natCast]
    rw [hdiff]
    exact le_div_iff₀ (pow_pos hτ₁ (r - j)) |>.mpr (mul_le_of_le_one_right (zpow_nonneg hτ₁.le _) (pow_le_one₀ hτ₁.le (by linarith)))
  have hterm1 : |∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) *
        iteratedDeriv j (divT_theta2 θ) t * iteratedDeriv (r - j) (fun x => (mD x)⁻¹) t| ≤
      (∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * KD (r - j)) * M * τ₁ ^ ((-1 : ℤ) - r) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := (hdiv2_bd j).trans (mul_le_mul_of_nonneg_left (hpow_le j hj) (mul_nonneg (hB (j + 3)) hM))
    have h2 := hKD_bd (r - j) t ht_in
    calc (Nat.choose r j : ℝ) * |iteratedDeriv j (divT_theta2 θ) t| * |iteratedDeriv (r - j) (fun x => (mD x)⁻¹) t|
        ≤ (Nat.choose r j : ℝ) * (B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - r)) * KD (r - j) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _) (by have := hB (j + 3); positivity)
      _ = (Nat.choose r j : ℝ) * B (j + 3) * KD (r - j) * M * τ₁ ^ ((-1 : ℤ) - r) := by ring
  have hterm2 : |∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) *
        iteratedDeriv j (divT2_theta1 θ) t * iteratedDeriv (r - j) (fun x => (mQ x)⁻¹) t| ≤
      (∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * KQ (r - j)) * M * τ₁ ^ ((-1 : ℤ) - r) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 := (hdiv1_bd j).trans (mul_le_mul_of_nonneg_left (hpow_le j hj) (mul_nonneg (hB (j + 3)) hM))
    have h2 := hKQ_bd (r - j) t ht_in
    calc (Nat.choose r j : ℝ) * |iteratedDeriv j (divT2_theta1 θ) t| * |iteratedDeriv (r - j) (fun x => (mQ x)⁻¹) t|
        ≤ (Nat.choose r j : ℝ) * (B (j + 3) * M * τ₁ ^ ((-1 : ℤ) - r)) * KQ (r - j) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _) (by have := hB (j + 3); positivity)
      _ = (Nat.choose r j : ℝ) * B (j + 3) * KQ (r - j) * M * τ₁ ^ ((-1 : ℤ) - r) := by ring
  have hexp_eq : τ₁ ^ (-3 : ℤ) * τ₁ ^ ((2 : ℤ) - r) = τ₁ ^ ((-1 : ℤ) - r) := by
    rw [← zpow_add₀ hτ₁.ne']; congr 1; omega
  calc 1 / (2 * c) * |∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) *
          iteratedDeriv j (divT_theta2 θ) t * iteratedDeriv (r - j) (fun x => (mD x)⁻¹) t -
        ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) *
          iteratedDeriv j (divT2_theta1 θ) t * iteratedDeriv (r - j) (fun x => (mQ x)⁻¹) t|
      ≤ 1 / (2 * c) * ((∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * KD (r - j)) * M * τ₁ ^ ((-1 : ℤ) - r) +
          (∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * KQ (r - j)) * M * τ₁ ^ ((-1 : ℤ) - r)) :=
        mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hterm1 hterm2)) (by positivity)
    _ = C_sum * (c⁻¹ * M * τ₁ ^ (-3 : ℤ)) * τ₁ ^ ((2 : ℤ) - r) := by
        dsimp only [C_sum]
        have hsum_eq : ∑ j ∈ Finset.range (r + 1),
            ((Nat.choose r j : ℝ) * B (j + 3) * KD (r - j) + (Nat.choose r j : ℝ) * B (j + 3) * KQ (r - j)) =
            ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * (KD (r - j) + KQ (r - j)) :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [show (∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * KD (r - j)) * M * τ₁ ^ ((-1 : ℤ) - r) +
              (∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * B (j + 3) * KQ (r - j)) * M * τ₁ ^ ((-1 : ℤ) - r) =
              (∑ j ∈ Finset.range (r + 1), ((Nat.choose r j : ℝ) * B (j + 3) * KD (r - j) +
                (Nat.choose r j : ℝ) * B (j + 3) * KQ (r - j))) * M * τ₁ ^ ((-1 : ℤ) - r) by
                rw [Finset.sum_add_distrib]; ring,
          hsum_eq, ← hexp_eq]
        field_simp [hc.ne']

end FormalResearch.SignUncertainty.FctCompD
