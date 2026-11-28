/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpTailBounds
public import FormalResearch.SignUncertainty.FctCuspEdgeIbp
public import FormalResearch.SignUncertainty.FctWarpOuterPhase
public import FormalResearch.SignUncertainty.MiddleBandVdc
public import FormalResearch.SignUncertainty.StripGExpansion

/-!
# Left-tail oscillatory error bounds: amplitude jets and Mid-band estimate (`fct:warp-asymp`)

Leaf helper module for `FctPhysicalPositive.lean` and `FctWarpLeftTailFar.lean`:
* `warpAmpLeft`: oscillatory amplitude for `warpLeftTailDensity` after factoring out
  `exp (i c edgePhi L τ)` from `mellinK0 c (iτ) ξ`.
* `warpAmpLeft_bounds`: `ContDiffOn ℝ 2` on `{τ ≠ 0}`, near-0 bounds `O(c⁻¹ |τ|^{1/2-k})`, and
  outer exponential decay bounds `O(c⁻¹ (1+|τ|)^{14} e^{-π|τ|})` for `k = 0, 1, 2`.
* `warpLeftTailDensity_mid_bound`: `|warpLeftTailDensity h ε c ξ| ≤ C * c ^ (-(15 / 8 : ℝ))`
  on the Mid-band (`π² * 100 * c^{-2/3} ≤ L ≤ 3 * physDelta c`).

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.Analysis FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCuspEdge FormalResearch.SignUncertainty.FctEdgeIbp

namespace FormalResearch.SignUncertainty

/-! ### Smoothness and bounds for `(1 - iτ)^{-1/2}` and `exp(B_c(iτ))` -/

/-- The kernel prefactor `(1 - iτ)^{-1/2}` on the imaginary axis. -/
noncomputable def oneSubITauInvSqrt (τ : ℝ) : ℂ :=
  (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))

private lemma oneSubITau_re (τ : ℝ) : (1 - (τ : ℂ) * Complex.I).re = 1 := by simp

private lemma oneSubITau_slit (τ : ℝ) : 1 - (τ : ℂ) * Complex.I ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))

private lemma oneSubITau_norm_ge_one (τ : ℝ) : 1 ≤ ‖1 - (τ : ℂ) * Complex.I‖ := by
  have hre : (1 : ℝ) = (1 - (τ : ℂ) * Complex.I).re := by simp
  calc (1 : ℝ) ≤ |(1 - (τ : ℂ) * Complex.I).re| := by rw [← hre]; norm_num
    _ ≤ ‖1 - (τ : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _

private lemma norm_oneSubITau_cpow_le_one (τ : ℝ) {s : ℝ} (hs : s ≤ 0) :
    ‖(1 - (τ : ℂ) * Complex.I) ^ (s : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_cpow_real]
  exact Real.rpow_le_one_of_one_le_of_nonpos (oneSubITau_norm_ge_one τ) hs

lemma oneSubITauInvSqrt_bounds :
    ContDiff ℝ 2 oneSubITauInvSqrt ∧
      ∀ τ : ℝ, ‖oneSubITauInvSqrt τ‖ ≤ 1 ∧
        ‖deriv oneSubITauInvSqrt τ‖ ≤ 1 ∧
        ‖deriv (deriv oneSubITauInvSqrt) τ‖ ≤ 1 := by
  have hline : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => (1 : ℂ) - (τ : ℂ) * Complex.I) :=
    contDiff_const.sub ((Complex.ofRealCLM.contDiff.of_le le_top).mul contDiff_const)
  have hcd_cpow : ∀ s : ℂ, ContDiff ℝ 2 (fun τ : ℝ => (1 - (τ : ℂ) * Complex.I) ^ s) := fun s => by
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => z ^ s) Complex.slitPlane := fun z hz =>
      ((hasDerivAt_id z).cpow_const hz).differentiableAt.differentiableWithinAt
    have hcd_slit : ContDiffOn ℂ (⊤ : ℕ∞) (fun z : ℂ => z ^ s) Complex.slitPlane :=
      (hdiff.contDiffOn Complex.isOpen_slitPlane).of_le le_top
    have hcd_top : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => (1 - (τ : ℂ) * Complex.I) ^ s) :=
      (hcd_slit.restrict_scalars ℝ).comp_contDiff hline fun τ => oneSubITau_slit τ
    exact hcd_top.of_le (by norm_num)
  have hhd_line : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I) (-Complex.I) τ := by
    intro τ
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I).const_sub (1 : ℂ)
    exact h1.congr_deriv (by simp)
  have hd1_fn : deriv oneSubITauInvSqrt =
      fun τ : ℝ => ((1 / 2 : ℂ) * Complex.I) * (1 - (τ : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ)) := by
    ext τ
    have hcpow := ((hasDerivAt_id (1 - (τ : ℂ) * Complex.I)).cpow_const
      (oneSubITau_slit τ) (c := (-(1 / 2 : ℂ)))).hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt τ
      (hhd_line τ)
    refine hcpow.deriv.trans ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      id_eq, smul_eq_mul, mul_one]
    rw [show (-(1 / 2 : ℂ)) - 1 = (-(3 / 2 : ℂ)) by norm_num]; ring
  have hd2_fn : deriv (deriv oneSubITauInvSqrt) =
      fun τ : ℝ => (-(3 / 4 : ℂ)) * (1 - (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by
    ext τ
    rw [hd1_fn]
    have hcpow := ((hasDerivAt_id (1 - (τ : ℂ) * Complex.I)).cpow_const
      (oneSubITau_slit τ) (c := (-(3 / 2 : ℂ)))).hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt τ
      (hhd_line τ)
    have hd := (hcpow.const_mul ((1 / 2 : ℂ) * Complex.I)).deriv
    refine hd.trans ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      id_eq, smul_eq_mul, mul_one]
    rw [show (-(3 / 2 : ℂ)) - 1 = (-(5 / 2 : ℂ)) by norm_num]
    calc ((1 / 2 : ℂ) * Complex.I) *
          ((-Complex.I) * ((-(3 / 2 : ℂ)) * (1 - (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ))))
        = (3 / 4 : ℂ) * Complex.I ^ 2 * (1 - (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by ring
      _ = (-(3 / 4 : ℂ)) * (1 - (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by rw [Complex.I_sq]; ring
  refine ⟨hcd_cpow (-(1 / 2 : ℂ)), fun τ => ⟨?_, ?_, ?_⟩⟩
  · simpa [oneSubITauInvSqrt, show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num] using
      norm_oneSubITau_cpow_le_one τ (s := -(1 / 2 : ℝ)) (by norm_num)
  · rw [hd1_fn, norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num, Complex.norm_I,
      mul_one, show (-(3 / 2 : ℂ)) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) by norm_num]
    have h1 := norm_oneSubITau_cpow_le_one τ (s := -(3 / 2 : ℝ)) (by norm_num)
    linarith
  · rw [hd2_fn, norm_mul, show ‖-(3 / 4 : ℂ)‖ = (3 / 4 : ℝ) by norm_num,
      show (-(5 / 2 : ℂ)) = ((-(5 / 2 : ℝ) : ℝ) : ℂ) by norm_num]
    have h1 := norm_oneSubITau_cpow_le_one τ (s := -(5 / 2 : ℝ)) (by norm_num)
    linarith

/-- The exponential Binet factor `exp(B_c(iτ))`. -/
noncomputable def expBinetImag (c : ℝ) (τ : ℝ) : ℂ :=
  Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I))

lemma expBinetImag_bounds {c : ℝ} (hc : 1 ≤ c) :
    ContDiff ℝ 2 (expBinetImag c) ∧
      ∀ τ : ℝ, ‖expBinetImag c τ‖ ≤ 2 ∧
        ‖deriv (expBinetImag c) τ‖ ≤ 2 ∧
        ‖deriv (deriv (expBinetImag c)) τ‖ ≤ 3 := by
  have hc0 : 0 < c := by linarith
  have hB := binetImag_edge_bounds 2 hc
  have hfn : (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) =
      fun t : ℝ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (t : ℂ)) := by
    ext t; ring_nf
  have hB_cd : ContDiff ℝ 2 (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) := by
    rw [hfn]; exact hB.1.of_le (by norm_num)
  have hB0 : ∀ τ : ℝ, ‖FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)‖ ≤ 1 / 6 := by
    intro τ; rw [mul_comm (τ : ℂ) Complex.I]; exact hB.2.1 τ
  have hB_holo : ContDiffOn ℂ ⊤ (FormalResearch.Asymptotics.binetDiff c) {ζ : ℂ | ζ.re < 1} := by
    have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have h1 : DifferentiableOn ℂ (fun ζ : ℂ => FormalResearch.Asymptotics.binetRem ((c : ℂ) * (1 - ζ)))
        {ζ : ℂ | ζ.re < 1} := by
      refine FormalResearch.Asymptotics.binetRem_differentiableOn.comp
        (differentiable_const _ |>.mul (differentiable_const _ |>.sub differentiable_id)).differentiableOn
        fun ζ hζ => by
          simp only [mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, zero_mul, sub_zero]
          exact mul_pos hc0 (sub_pos.mpr hζ)
    exact (h1.sub (differentiableOn_const _)).contDiffOn hopen
  have hB_dk : ∀ k, 1 ≤ k → k ≤ 2 → ∀ τ : ℝ,
      ‖iteratedDeriv k (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ‖ ≤ 1 := by
    have hiter : ∀ k : ℕ, ∀ τ : ℝ,
        iteratedDeriv k (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ =
          Complex.I ^ k * iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I) := by
      intro k
      induction k with
      | zero => intro τ; simp
      | succ k ih =>
        intro τ
        have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
        have hfun : iteratedDeriv k (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) =
            fun t : ℝ => Complex.I ^ k * iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c) ((t : ℂ) * Complex.I) :=
          funext ih
        have hcd_k : ContDiffOn ℂ ⊤ (iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c)) {ζ : ℂ | ζ.re < 1} := by
          have h0 : ContDiffOn ℂ ⊤ (iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c)) {ζ : ℂ | ζ.re < 1} := by
            clear hfun ih τ
            induction k with
            | zero => simpa using hB_holo
            | succ m ihm =>
              have h1 := ihm.derivWithin hopen.uniqueDiffOn (m := ⊤) (by decide)
              exact h1.congr fun ζ hζ => by
                rw [iteratedDeriv_succ, derivWithin_of_isOpen hopen hζ]
          exact h0
        have hd_C : HasDerivAt (iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c))
            (iteratedDeriv (k + 1) (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I))
            ((τ : ℂ) * Complex.I) := by
          rw [iteratedDeriv_succ]
          exact (hcd_k.differentiableOn (by decide) ((τ : ℂ) * Complex.I) (by simp)).differentiableAt
            (hopen.mem_nhds (by simp)) |>.hasDerivAt
        have hline : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I τ := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
        have hcomp := ((hd_C.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hline).const_mul (Complex.I ^ k)
        rw [iteratedDeriv_succ, hfun]
        change deriv (fun y : ℝ => Complex.I ^ k * (iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c) ∘ fun t : ℝ => (t : ℂ) * Complex.I) y) τ = _
        rw [hcomp.deriv]
        simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
          smul_eq_mul]
        rw [pow_succ]; ring
    intro k hk1 hk2 τ
    rw [hiter k τ, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    have hre : ((τ : ℂ) * Complex.I).re ≤ 0 := by simp
    have hbd := FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le hc0 hre hk1
    have hfac : (k.factorial : ℝ) ≤ 2 := by
      have : k.factorial ≤ 2 := by interval_cases k <;> norm_num
      exact_mod_cast this
    calc ‖iteratedDeriv k (FormalResearch.Asymptotics.binetDiff c) ((τ : ℂ) * Complex.I)‖
        ≤ (k.factorial : ℝ) / (12 * c) := hbd
      _ ≤ 2 / (12 * 1) := div_le_div₀ (by positivity) hfac (by positivity) (by linarith)
      _ ≤ 1 := by norm_num
  have hB1 : ∀ τ : ℝ, ‖deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ‖ ≤ 1 := by
    intro τ; rw [← iteratedDeriv_one]; exact hB_dk 1 le_rfl (by norm_num) τ
  have hB2 : ∀ τ : ℝ,
      ‖deriv (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I))) τ‖ ≤ 1 := by
    intro τ; rw [← iteratedDeriv_one, ← iteratedDeriv_succ']; exact hB_dk 2 (by norm_num) le_rfl τ
  have hcd_exp : ContDiff ℝ 2 (expBinetImag c) := hB_cd.cexp
  have hexp_le : ∀ τ : ℝ, ‖expBinetImag c τ‖ ≤ Real.exp (1 / 6) := fun τ => by
    unfold expBinetImag
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hB0 τ))
  have hexp_2 : Real.exp (1 / 6 : ℝ) ≤ 2 := by
    have := Real.exp_one_lt_d9
    have h6 : Real.exp (1 / 6 : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    have : Real.exp (1 / 6 : ℝ) ^ 6 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 6 : ℝ), pow_pos (Real.exp_pos (1 / 6 : ℝ)) 2,
      pow_pos (Real.exp_pos (1 / 6 : ℝ)) 3, pow_pos (Real.exp_pos (1 / 6 : ℝ)) 4,
      pow_pos (Real.exp_pos (1 / 6 : ℝ)) 5]
  have hd1_eq : deriv (expBinetImag c) =
      fun τ : ℝ => expBinetImag c τ *
        deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ := by
    ext τ
    have hd := (hB_cd.differentiable (by norm_num) τ).hasDerivAt.cexp
    unfold expBinetImag; exact hd.deriv
  have hdB1_cd : ContDiff ℝ 1 (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I))) := by
    have h1 := (hB_cd.contDiffOn (s := univ)).derivWithin uniqueDiffOn_univ (m := 1) (by norm_num)
    exact contDiffOn_univ.mp (h1.congr fun t _ => by rw [derivWithin_univ])
  have hd2_eq : deriv (deriv (expBinetImag c)) =
      fun τ : ℝ => deriv (expBinetImag c) τ *
          deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ +
        expBinetImag c τ *
          deriv (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I))) τ := by
    ext τ
    conv_lhs => rw [hd1_eq]
    have h1 : HasDerivAt (expBinetImag c) (deriv (expBinetImag c) τ) τ :=
      (hcd_exp.differentiable (by norm_num) τ).hasDerivAt
    have h2 : HasDerivAt (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)))
        (deriv (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I))) τ) τ :=
      (hdB1_cd.differentiable (by norm_num) τ).hasDerivAt
    exact (h1.mul h2).deriv
  refine ⟨hcd_exp, fun τ => ⟨(hexp_le τ).trans hexp_2, ?_, ?_⟩⟩
  · rw [hd1_eq, norm_mul]
    calc _ ≤ Real.exp (1 / 6) * 1 := mul_le_mul (hexp_le τ) (hB1 τ) (norm_nonneg _) (by positivity)
      _ ≤ 2 := by linarith
  · have hE2 : Real.exp (1 / 6 : ℝ) ≤ 1.2 := by
      have hexp1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have : Real.exp (1 / 6 : ℝ) ^ 6 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      have hpos : 0 < Real.exp (1 / 6 : ℝ) := Real.exp_pos _
      by_contra hge
      push Not at hge
      have : (1.2 : ℝ) ^ 6 ≤ Real.exp (1 / 6 : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hge.le 6
      norm_num at this; linarith
    have h1d : ‖deriv (expBinetImag c) τ‖ ≤ 1.2 := by
      rw [hd1_eq, norm_mul]
      calc _ ≤ 1.2 * 1 := mul_le_mul ((hexp_le τ).trans hE2) (hB1 τ) (norm_nonneg _) (by positivity)
        _ = 1.2 := by ring
    rw [hd2_eq]
    calc ‖_‖ ≤ ‖deriv (expBinetImag c) τ *
            deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ‖ +
          ‖expBinetImag c τ *
            deriv (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I))) τ‖ :=
          norm_add_le _ _
      _ = ‖deriv (expBinetImag c) τ‖ *
            ‖deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I)) τ‖ +
          ‖expBinetImag c τ‖ *
            ‖deriv (deriv (fun t : ℝ => FormalResearch.Asymptotics.binetDiff c ((t : ℂ) * Complex.I))) τ‖ := by
          simp only [norm_mul]
      _ ≤ 1.2 * 1 + 1.2 * 1 := by
          gcongr
          · exact hB1 τ
          · exact (hexp_le τ).trans hE2
          · exact hB2 τ
      _ = 2.4 := by norm_num
      _ ≤ 3 := by norm_num

/-! ### `C^2` product-rule helper on open sets -/

private lemma mul_c2_on_bounds {S : Set ℝ} (hS : IsOpen S) {f g : ℝ → ℂ} {bf0 bf1 bf2 bg0 bg1 bg2 : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f S) (hg : ContDiffOn ℝ 2 g S)
    (hbf0 : ∀ τ ∈ S, 0 ≤ bf0 τ) (hbf1 : ∀ τ ∈ S, 0 ≤ bf1 τ) (_hbf2 : ∀ τ ∈ S, 0 ≤ bf2 τ)
    (_hbg0 : ∀ τ ∈ S, 0 ≤ bg0 τ) (_hbg1 : ∀ τ ∈ S, 0 ≤ bg1 τ) (_hbg2 : ∀ τ ∈ S, 0 ≤ bg2 τ)
    (hf_bd : ∀ τ ∈ S, ‖f τ‖ ≤ bf0 τ ∧ ‖deriv f τ‖ ≤ bf1 τ ∧ ‖deriv (deriv f) τ‖ ≤ bf2 τ)
    (hg_bd : ∀ τ ∈ S, ‖g τ‖ ≤ bg0 τ ∧ ‖deriv g τ‖ ≤ bg1 τ ∧ ‖deriv (deriv g) τ‖ ≤ bg2 τ) :
    ContDiffOn ℝ 2 (fun τ => f τ * g τ) S ∧
      ∀ τ ∈ S, ‖f τ * g τ‖ ≤ bf0 τ * bg0 τ ∧
        ‖deriv (fun t => f t * g t) τ‖ ≤ bf1 τ * bg0 τ + bf0 τ * bg1 τ ∧
        ‖deriv (deriv (fun t => f t * g t)) τ‖ ≤ bf2 τ * bg0 τ + 2 * (bf1 τ * bg1 τ) + bf0 τ * bg2 τ := by
  refine ⟨hf.mul hg, fun τ hτ => ?_⟩
  have hd1 : ∀ t ∈ S, deriv (fun s => f s * g s) t = deriv f t * g t + f t * deriv g t := fun t ht => by
    have hfa := ((hf.contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
    have hga := ((hg.contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
    exact (hfa.mul hga).deriv
  have heq1 : deriv (fun s => f s * g s) =ᶠ[𝓝 τ] fun t => deriv f t * g t + f t * deriv g t :=
    Filter.eventuallyEq_of_mem (hS.mem_nhds hτ) hd1
  have hdf_cd : ContDiffOn ℝ 1 (deriv f) S :=
    (hf.derivWithin hS.uniqueDiffOn (m := 1) (by norm_num)).congr fun t ht => (derivWithin_of_isOpen hS ht).symm
  have hdg_cd : ContDiffOn ℝ 1 (deriv g) S :=
    (hg.derivWithin hS.uniqueDiffOn (m := 1) (by norm_num)).congr fun t ht => (derivWithin_of_isOpen hS ht).symm
  have hfa1 : HasDerivAt (deriv f) (deriv (deriv f) τ) τ :=
    ((hdf_cd.contDiffAt (hS.mem_nhds hτ)).differentiableAt (by norm_num)).hasDerivAt
  have hga1 : HasDerivAt (deriv g) (deriv (deriv g) τ) τ :=
    ((hdg_cd.contDiffAt (hS.mem_nhds hτ)).differentiableAt (by norm_num)).hasDerivAt
  have hfa0 : HasDerivAt f (deriv f τ) τ :=
    ((hf.contDiffAt (hS.mem_nhds hτ)).differentiableAt (by norm_num)).hasDerivAt
  have hga0 : HasDerivAt g (deriv g τ) τ :=
    ((hg.contDiffAt (hS.mem_nhds hτ)).differentiableAt (by norm_num)).hasDerivAt
  have hd2_val : deriv (deriv (fun s => f s * g s)) τ =
      deriv (deriv f) τ * g τ + 2 * (deriv f τ * deriv g τ) + f τ * deriv (deriv g) τ := by
    rw [heq1.deriv_eq]
    change deriv (deriv f * g + f * deriv g) τ = _
    rw [((hfa1.mul hga0).add (hfa0.mul hga1)).deriv]
    ring
  obtain ⟨hf0, hf1, hf2⟩ := hf_bd τ hτ
  obtain ⟨hg0, hg1, hg2⟩ := hg_bd τ hτ
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]; exact mul_le_mul hf0 hg0 (norm_nonneg _) (hbf0 τ hτ)
  · rw [hd1 τ hτ]
    calc ‖deriv f τ * g τ + f τ * deriv g τ‖
        ≤ ‖deriv f τ‖ * ‖g τ‖ + ‖f τ‖ * ‖deriv g τ‖ :=
          (norm_add_le _ _).trans (by simp only [norm_mul]; rfl)
      _ ≤ bf1 τ * bg0 τ + bf0 τ * bg1 τ :=
          add_le_add (mul_le_mul hf1 hg0 (norm_nonneg _) (hbf1 τ hτ))
            (mul_le_mul hf0 hg1 (norm_nonneg _) (hbf0 τ hτ))
  · rw [hd2_val]
    have hnorm2 : ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ ≤ 2 * (bf1 τ * bg1 τ) := by
      rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hf1 hg1 (norm_nonneg _) (hbf1 τ hτ)) (by norm_num)
    calc ‖deriv (deriv f) τ * g τ + 2 * (deriv f τ * deriv g τ) + f τ * deriv (deriv g) τ‖
        ≤ ‖deriv (deriv f) τ * g τ‖ + ‖(2 : ℂ) * (deriv f τ * deriv g τ)‖ + ‖f τ * deriv (deriv g) τ‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ bf2 τ * bg0 τ + 2 * (bf1 τ * bg1 τ) + bf0 τ * bg2 τ := by
          refine add_le_add (add_le_add ?_ hnorm2) ?_
          · rw [norm_mul]; exact mul_le_mul hf2 hg0 (norm_nonneg _) (norm_nonneg _ |>.trans hf2)
          · rw [norm_mul]; exact mul_le_mul hf0 hg2 (norm_nonneg _) (hbf0 τ hτ)

/-! ### Left-tail oscillatory amplitude and `C^2` bounds -/

/-- Oscillatory amplitude of `warpLeftTailDensity` after pulling out
`exp (i c edgePhi (Real.log (π² ξ)) τ)`. -/
noncomputable def warpAmpLeft {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ : ℝ) (τ : ℝ) : ℂ :=
  let _ := ξ
  oneSubITauInvSqrt τ * expBinetImag c τ *
    (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
      fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
      fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
      ctHG ε ((τ : ℂ) * Complex.I))

lemma warpAmpLeft_eq_integrand {K4 : ℝ} (h : FctWarpSolveStmt K4) (ε c ξ τ : ℝ) (hξ : 0 < ξ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
        fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I) *
        fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) *
        ctHG ε ((τ : ℂ) * Complex.I)) =
      Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Real.log (π ^ 2 * ξ)) τ : ℂ)) *
        warpAmpLeft h ε c ξ τ := by
  have hm := FormalResearch.CohnElkies.mellinK0_imag_eq c ξ τ hξ
  have hed : Real.log (π ^ 2 * ξ) * τ - π ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ =
      edgePhi (Real.log (π ^ 2 * ξ)) τ := by
    rw [edgePhi_eq_stripS0Tilde]
    have hed' : FormalResearch.CohnElkies.edgeR5 τ =
        stripS0Tilde ((τ : ℂ) * Complex.I) - (π ^ 2 / 36 : ℂ) * ((τ : ℂ) * Complex.I) ^ 3 := rfl
    have hi3 : ((τ : ℂ) * Complex.I) ^ 3 = -(((τ ^ 3 : ℝ) : ℂ) * Complex.I) := by
      calc ((τ : ℂ) * Complex.I) ^ 3 = (τ : ℂ) ^ 3 * (Complex.I ^ 2 * Complex.I) := by ring
        _ = -(((τ ^ 3 : ℝ) : ℂ) * Complex.I) := by rw [Complex.I_sq]; push_cast; ring
    rw [hi3] at hed'
    have him := congr_arg Complex.im (FormalResearch.CohnElkies.edgeR5_eq_I_mul_edgeR (τ := τ))
    have hed'' : (FormalResearch.CohnElkies.edgeR5 τ).im =
        (stripS0Tilde ((τ : ℂ) * Complex.I)).im + π ^ 2 / 36 * τ ^ 3 := by
      simp only [hed', Complex.sub_im, Complex.mul_im, Complex.neg_im, Complex.neg_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
      norm_cast
      simp [Complex.ofReal_pow]
    have him' : FormalResearch.CohnElkies.edgeR τ = (stripS0Tilde ((τ : ℂ) * Complex.I)).im + π ^ 2 / 36 * τ ^ 3 := by
      rw [← hed'']; simpa using him.symm
    linarith
  rw [hm, hed]
  unfold warpAmpLeft oneSubITauInvSqrt expBinetImag
  ring

private lemma baseLeft_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C_mid1 C_gl1 c₀ : ℝ, 0 ≤ C_mid1 ∧ 0 ≤ C_gl1 ∧ 1 ≤ c₀ ∧
      ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        ContDiffOn ℝ 2 (fun τ => oneSubITauInvSqrt τ * expBinetImag c τ *
            fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
            fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) {τ : ℝ | τ ≠ 0} ∧
        (∀ τ : ℝ, τ ≠ 0 →
          ‖oneSubITauInvSqrt τ * expBinetImag c τ *
              fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
              fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ C_gl1 * c⁻¹ * (1 + |τ|) ^ 2 ∧
          ‖deriv (fun t => oneSubITauInvSqrt t * expBinetImag c t *
              fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) t *
              fctPhiHat h ε c (1 - (t : ℂ) * Complex.I)) τ‖ ≤ C_gl1 * c⁻¹ * (1 + |τ|) ^ 2 ∧
          ‖deriv (deriv (fun t => oneSubITauInvSqrt t * expBinetImag c t *
              fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) t *
              fctPhiHat h ε c (1 - (t : ℂ) * Complex.I))) τ‖ ≤ C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) ∧
        (∀ τ : ℝ, τ ≠ 0 → |τ| < 1 / 8 →
          ‖oneSubITauInvSqrt τ * expBinetImag c τ *
              fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
              fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ C_mid1 * c⁻¹ * |τ| ^ 3 ∧
          ‖deriv (fun t => oneSubITauInvSqrt t * expBinetImag c t *
              fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) t *
              fctPhiHat h ε c (1 - (t : ℂ) * Complex.I)) τ‖ ≤ C_mid1 * c⁻¹ * |τ| ^ 2 ∧
          ‖deriv (deriv (fun t => oneSubITauInvSqrt t * expBinetImag c t *
              fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) t *
              fctPhiHat h ε c (1 - (t : ℂ) * Complex.I))) τ‖ ≤ C_mid1 * c⁻¹ * |τ|) := by
  obtain ⟨ML, c0L, hML0, _, hLT⟩ := fctLeftTail_deriv_bounds hK4 h
  obtain ⟨CR, c0R, hCR0, _, hRT⟩ := fctRightTail_bounds hK4 h
  set c₀ := max c0L (max c0R 1)
  set C_p1 : ℝ := 1 + 2 * 1 + 3
  set C_phi : ℝ := max 1 CR
  set C_mid1 : ℝ := (C_p1 * 4 * ML) * (5 * C_phi)
  set C_gl1 : ℝ := (C_p1 * 4 * ML) * (4 * C_phi)
  refine ⟨C_mid1, C_gl1, c₀, by positivity, by positivity, le_max_of_le_right (le_max_right _ _),
    fun ε c hε hc => ?_⟩
  have hcL : c0L ≤ c := (le_max_left _ _).trans hc
  have hcR : c0R ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc1 : 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  obtain ⟨hLT_cd, hLT_sm, hLT_gl⟩ := hLT ε c hε hcL
  obtain ⟨hRT_cd, hRT_bd⟩ := hRT ε c hε hcR
  have h1S := oneSubITauInvSqrt_bounds
  have hEB := expBinetImag_bounds hc1
  set S : Set ℝ := {τ : ℝ | τ ≠ 0}
  have hS : IsOpen S := isOpen_ne
  have hp1 := mul_c2_on_bounds hS h1S.1.contDiffOn (hEB.1.contDiffOn)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun τ _ => h1S.2 τ) (fun τ _ => hEB.2 τ)
  have hPhiR_cd : ContDiff ℝ 2 (fun τ : ℝ => fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) := by
    have : (fun τ : ℝ => fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) = fun τ => 1 + fctRightTail h ε c τ := by
      ext τ; unfold fctRightTail; ring
    rw [this]; exact contDiff_const.add hRT_cd
  have hPhiR_bd : ∀ τ : ℝ,
      ‖fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)‖ ≤ C_phi * (1 + |τ|) ∧
      ‖deriv (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I)) τ‖ ≤ C_phi ∧
      ‖deriv (deriv (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I))) τ‖ ≤ C_phi := by
    intro τ
    have heq : (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I)) = fun t => 1 + fctRightTail h ε c t := by
      ext t; unfold fctRightTail; ring
    have hd1 : deriv (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I)) = deriv (fctRightTail h ε c) := by
      ext t; rw [heq]; exact deriv_const_add 1
    have hd2 : deriv (deriv (fun t : ℝ => fctPhiHat h ε c (1 - (t : ℂ) * Complex.I))) =
        deriv (deriv (fctRightTail h ε c)) := by
      rw [hd1]
    have hCRc : CR * c⁻¹ ≤ CR := by
      have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      calc CR * c⁻¹ ≤ CR * 1 := mul_le_mul_of_nonneg_left this hCR0
        _ = CR := mul_one _
    refine ⟨?_, ?_, ?_⟩
    · rw [congrFun heq τ]
      calc ‖(1 : ℂ) + fctRightTail h ε c τ‖ ≤ 1 + ‖fctRightTail h ε c τ‖ := by
            simpa [norm_one] using norm_add_le (1 : ℂ) (fctRightTail h ε c τ)
        _ ≤ 1 + CR * c⁻¹ * |τ| := by linarith [(hRT_bd τ).1]
        _ ≤ 1 + CR * |τ| := by gcongr
        _ ≤ C_phi + C_phi * |τ| := add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg τ))
        _ = C_phi * (1 + |τ|) := by ring
    · rw [hd1]; exact (hRT_bd τ).2.1.trans (hCRc.trans (le_max_right _ _))
    · rw [hd2]; exact (hRT_bd τ).2.2.trans (hCRc.trans (le_max_right _ _))
  have hp1_LT := mul_c2_on_bounds (bf0 := fun _ => 2) (bf1 := fun _ => 4) (bf2 := fun _ => 9)
    hS hp1.1 hLT_cd.contDiffOn
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun τ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun τ hτ => by
      obtain ⟨b0, b1, b2⟩ := hp1.2 τ hτ
      exact ⟨b0.trans (by norm_num), b1.trans (by norm_num), b2.trans (by norm_num)⟩)
    (fun τ _ => hLT_gl τ)
  have hp1_LT_Phi := mul_c2_on_bounds
    (bf0 := fun τ => C_p1 * 4 * ML * c⁻¹ * (1 + |τ|))
    (bf1 := fun τ => C_p1 * 4 * ML * c⁻¹ * (1 + |τ|))
    (bf2 := fun τ => C_p1 * 4 * ML * c⁻¹ * (1 + |τ|))
    (bg0 := fun τ => C_phi * (1 + |τ|)) (bg1 := fun _ => C_phi) (bg2 := fun _ => C_phi)
    hS hp1_LT.1 hPhiR_cd.contDiffOn
    (fun τ _ => by positivity) (fun τ _ => by positivity) (fun τ _ => by positivity)
    (fun τ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun τ hτ => by
      obtain ⟨b0, b1, b2⟩ := hp1_LT.2 τ hτ
      have h1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
      have h_mul : ML * c⁻¹ ≤ ML * c⁻¹ * (1 + |τ|) := le_mul_of_one_le_right (by positivity) h1
      have hnn : 0 ≤ ML * c⁻¹ * (1 + |τ|) := by positivity
      refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩ <;> simp only [C_p1] <;> linarith)
    (fun τ _ => hPhiR_bd τ)
  set U_near : Set ℝ := {t : ℝ | t ≠ 0 ∧ |t| < 1 / 8}
  have hU_near : IsOpen U_near := isOpen_ne.inter (isOpen_lt continuous_abs continuous_const)
  have hp1_LT_n := mul_c2_on_bounds
    (bf0 := fun _ => 2) (bf1 := fun _ => 4) (bf2 := fun _ => 9)
    (bg0 := fun t => ML * c⁻¹ * |t| ^ 3) (bg1 := fun t => ML * c⁻¹ * |t| ^ 2) (bg2 := fun t => ML * c⁻¹ * |t|)
    hU_near (hp1.1.mono fun _ ht => ht.1) (hLT_cd.contDiffOn)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun t _ => by positivity) (fun t _ => by positivity) (fun t _ => by positivity)
    (fun t ht => by
      obtain ⟨b0, b1, b2⟩ := hp1.2 t ht.1
      exact ⟨b0.trans (by norm_num), b1.trans (by norm_num), b2.trans (by norm_num)⟩)
    (fun t ht => hLT_sm t ht.2.le)
  have hp1_LT_Phi_n := mul_c2_on_bounds
    (bf0 := fun t => C_p1 * 4 * ML * c⁻¹ * |t| ^ 3)
    (bf1 := fun t => C_p1 * 4 * ML * c⁻¹ * |t| ^ 2)
    (bf2 := fun t => C_p1 * 4 * ML * c⁻¹ * |t|)
    (bg0 := fun _ => 2 * C_phi) (bg1 := fun _ => C_phi) (bg2 := fun _ => C_phi)
    hU_near hp1_LT_n.1 hPhiR_cd.contDiffOn
    (fun t _ => by positivity) (fun t _ => by positivity) (fun t _ => by positivity)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun t ht => by
      obtain ⟨b0, b1, b2⟩ := hp1_LT_n.2 t ht
      have ht1 : |t| ≤ 1 := by linarith [ht.2]
      have ht32 : |t| ^ 3 ≤ |t| ^ 2 := by nlinarith [abs_nonneg t, sq_nonneg t]
      have ht21 : |t| ^ 2 ≤ |t| := by nlinarith [abs_nonneg t]
      have hnn : 0 ≤ ML * c⁻¹ := by positivity
      have h_32 : ML * c⁻¹ * |t| ^ 3 ≤ ML * c⁻¹ * |t| ^ 2 := mul_le_mul_of_nonneg_left ht32 hnn
      have h_21 : ML * c⁻¹ * |t| ^ 2 ≤ ML * c⁻¹ * |t| := mul_le_mul_of_nonneg_left ht21 hnn
      have h_31 : ML * c⁻¹ * |t| ^ 3 ≤ ML * c⁻¹ * |t| := h_32.trans h_21
      refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
      · have : 0 ≤ ML * c⁻¹ * |t| ^ 3 := by positivity
        simp only [C_p1]; linarith
      · have : 0 ≤ ML * c⁻¹ * |t| ^ 2 := by positivity
        simp only [C_p1]; linarith
      · have : 0 ≤ ML * c⁻¹ * |t| := by positivity
        simp only [C_p1]; linarith)
    (fun t ht => by
      obtain ⟨b0, b1, b2⟩ := hPhiR_bd t
      exact ⟨b0.trans (by calc C_phi * (1 + |t|) ≤ C_phi * 2 := by gcongr; linarith [ht.2]
        _ = 2 * C_phi := by ring), b1, b2⟩)
  refine ⟨hp1_LT_Phi.1, fun τ hτ => ?_, fun τ hτ hτ8 => ?_⟩
  · obtain ⟨b0, b1, b2⟩ := hp1_LT_Phi.2 τ hτ
    have h1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have h_m1 : C_p1 * 4 * ML * c⁻¹ * (1 + |τ|) * C_phi ≤
        C_p1 * 4 * ML * c⁻¹ * (1 + |τ|) * (C_phi * (1 + |τ|)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) h1) (by positivity)
    have hpow : (C_p1 * 4 * ML * c⁻¹ * (1 + |τ|)) * (C_phi * (1 + |τ|)) =
        (C_p1 * 4 * ML) * C_phi * c⁻¹ * (1 + |τ|) ^ 2 := by ring
    have hnn : 0 ≤ (C_p1 * 4 * ML) * C_phi * c⁻¹ * (1 + |τ|) ^ 2 := by positivity
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩ <;> [skip; skip; skip]
    · simp only [C_gl1]; nlinarith
    · simp only [C_gl1]; nlinarith
    · simp only [C_gl1]; nlinarith
  · obtain ⟨b0, b1, b2⟩ := hp1_LT_Phi_n.2 τ ⟨hτ, hτ8⟩
    have hτ1 : |τ| ≤ 1 := by linarith
    have hτ32 : |τ| ^ 3 ≤ |τ| ^ 2 := by nlinarith [abs_nonneg τ, sq_nonneg τ]
    have hτ21 : |τ| ^ 2 ≤ |τ| := by nlinarith [abs_nonneg τ]
    have hnn : 0 ≤ C_p1 * 4 * ML * c⁻¹ := by positivity
    have h_32 : C_p1 * 4 * ML * c⁻¹ * |τ| ^ 3 ≤ C_p1 * 4 * ML * c⁻¹ * |τ| ^ 2 := mul_le_mul_of_nonneg_left hτ32 hnn
    have h_21 : C_p1 * 4 * ML * c⁻¹ * |τ| ^ 2 ≤ C_p1 * 4 * ML * c⁻¹ * |τ| := mul_le_mul_of_nonneg_left hτ21 hnn
    have h_31 : C_p1 * 4 * ML * c⁻¹ * |τ| ^ 3 ≤ C_p1 * 4 * ML * c⁻¹ * |τ| := h_32.trans h_21
    have h_cp : 0 ≤ C_p1 * 4 * ML * C_phi * c⁻¹ * |τ| := by positivity
    have h_cp2 : 0 ≤ C_p1 * 4 * ML * C_phi * c⁻¹ * |τ| ^ 2 := by positivity
    have h_cp3 : 0 ≤ C_p1 * 4 * ML * C_phi * c⁻¹ * |τ| ^ 3 := by positivity
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · simp only [C_mid1]; nlinarith
    · simp only [C_mid1]; nlinarith
    · simp only [C_mid1]; nlinarith

lemma warpAmpLeft_bounds {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ 1 ≤ c₀ ∧ ∀ ε c ξ : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ContDiffOn ℝ 2 (warpAmpLeft h ε c ξ) {τ : ℝ | τ ≠ 0} ∧
      (∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 / 16 →
        ‖warpAmpLeft h ε c ξ τ‖ ≤ C * c⁻¹ * |τ| ^ (1 / 2 : ℝ) ∧
        ‖deriv (warpAmpLeft h ε c ξ) τ‖ ≤ C * c⁻¹ * |τ| ^ (-(1 / 2 : ℝ)) ∧
        ‖deriv (deriv (warpAmpLeft h ε c ξ)) τ‖ ≤ C * c⁻¹ * |τ| ^ (-(3 / 2 : ℝ))) ∧
      (∀ τ : ℝ, 1 / 16 ≤ |τ| →
        ‖warpAmpLeft h ε c ξ τ‖ ≤ C * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) ∧
        ‖deriv (warpAmpLeft h ε c ξ) τ‖ ≤ C * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) ∧
        ‖deriv (deriv (warpAmpLeft h ε c ξ)) τ‖ ≤ C * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|))) := by
  obtain ⟨C_mid1, C_gl1, c0B, hC_mid_nn, hC_gl_nn, hc0B, hBase⟩ := baseLeft_bounds hK4 h
  obtain ⟨MD, c0D, hMD0, _, hDHG⟩ := dcomp_ctHG_EJ hK4 h
  set c₀ := max c0B c0D
  set C_tot : ℝ := 4 * max C_mid1 C_gl1 * MD * max (2 ^ 12) (16 ^ (9 / 2 : ℝ))
  refine ⟨C_tot, c₀, by positivity, le_max_of_le_left hc0B, fun ε c ξ hε hc => ?_⟩
  have hcB : c0B ≤ c := (le_max_left _ _).trans hc
  have hcD : c0D ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hEJ := hDHG ε c hε hcD
  obtain ⟨hB_cd, hB_gl, hB_sm⟩ := hBase ε c hε hcB
  set S : Set ℝ := {τ : ℝ | τ ≠ 0}
  have hS : IsOpen S := isOpen_ne
  set U_near : Set ℝ := {t : ℝ | t ≠ 0 ∧ |t| < 1 / 8}
  have hU_near : IsOpen U_near := isOpen_ne.inter (isOpen_lt continuous_abs continuous_const)
  have hDHG_bd : ∀ τ : ℝ, τ ≠ 0 →
      ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)‖ ≤
        MD * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)) ∧
      ‖deriv (fun t : ℝ => fctDcompAt K4 c (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I)) τ‖ ≤
        MD * |τ| ^ (-(7 / 2 : ℝ)) * (1 + |τ|) ^ 11 * Real.exp (-(π * |τ|)) ∧
      ‖deriv (deriv (fun t : ℝ => fctDcompAt K4 c (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I) * ctHG ε ((t : ℂ) * Complex.I))) τ‖ ≤
        MD * |τ| ^ (-(9 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)) := by
    intro τ hτ
    have h0 := hEJ.b0 τ hτ
    have h1 := hEJ.b1 τ hτ
    have h2 := hEJ.b2 τ hτ
    unfold ejW at h0 h1 h2
    simp only [Nat.cast_zero, sub_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2
    rw [show -(5 / 2 : ℝ) - 1 = -(7 / 2 : ℝ) by norm_num] at h1
    rw [show -(5 / 2 : ℝ) - 2 = -(9 / 2 : ℝ) by norm_num] at h2
    exact ⟨by simpa only [mul_one, mul_assoc] using h0,
      by simpa only [mul_one, mul_assoc] using h1,
      by simpa only [mul_one, mul_assoc] using h2⟩
  have hMain := mul_c2_on_bounds
    (bf0 := fun τ => C_gl1 * c⁻¹ * (1 + |τ|) ^ 2)
    (bf1 := fun τ => C_gl1 * c⁻¹ * (1 + |τ|) ^ 2)
    (bf2 := fun τ => C_gl1 * c⁻¹ * (1 + |τ|) ^ 2)
    (bg0 := fun τ => MD * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)))
    (bg1 := fun τ => MD * |τ| ^ (-(7 / 2 : ℝ)) * (1 + |τ|) ^ 11 * Real.exp (-(π * |τ|)))
    (bg2 := fun τ => MD * |τ| ^ (-(9 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)))
    hS hB_cd (hEJ.c2)
    (fun τ _ => by positivity) (fun τ _ => by positivity) (fun τ _ => by positivity)
    (fun τ _ => by positivity) (fun τ _ => by positivity) (fun τ _ => by positivity)
    (fun τ hτ => hB_gl τ hτ)
    (fun τ hτ => hDHG_bd τ hτ)
  have hMain_near := mul_c2_on_bounds
    (bf0 := fun t => C_mid1 * c⁻¹ * |t| ^ 3)
    (bf1 := fun t => C_mid1 * c⁻¹ * |t| ^ 2)
    (bf2 := fun t => C_mid1 * c⁻¹ * |t|)
    (bg0 := fun t => MD * 2 ^ 12 * |t| ^ (-(5 / 2 : ℝ)))
    (bg1 := fun t => MD * 2 ^ 12 * |t| ^ (-(7 / 2 : ℝ)))
    (bg2 := fun t => MD * 2 ^ 12 * |t| ^ (-(9 / 2 : ℝ)))
    hU_near (hB_cd.mono fun _ ht => ht.1) (hEJ.c2.mono fun _ ht => ht.1)
    (fun t _ => by positivity) (fun t _ => by positivity) (fun t _ => by positivity)
    (fun t _ => by positivity) (fun t _ => by positivity) (fun t _ => by positivity)
    (fun t ht => hB_sm t ht.1 ht.2)
    (fun t ht => by
      obtain ⟨b0, b1, b2⟩ := hDHG_bd t ht.1
      have hp12 : ∀ m : ℕ, m ≤ 12 → (1 + |t|) ^ m ≤ (2 : ℝ) ^ 12 := fun m hm =>
        calc (1 + |t|) ^ m ≤ (1 + |t|) ^ 12 := pow_le_pow_right₀ (by linarith [abs_nonneg t]) hm
          _ ≤ 2 ^ 12 := pow_le_pow_left₀ (by positivity) (by linarith [ht.2]) 12
      have hexp1 : Real.exp (-(π * |t|)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (abs_nonneg t)))
      have hrp : ∀ q : ℝ, 0 ≤ MD * |t| ^ q := fun q => mul_nonneg hMD0 (Real.rpow_nonneg (abs_nonneg t) q)
      refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
      · have hp := hp12 10 (by norm_num)
        calc _ ≤ (MD * |t| ^ (-(5 / 2 : ℝ))) * 2 ^ 12 * 1 := by gcongr
          _ = MD * 2 ^ 12 * |t| ^ (-(5 / 2 : ℝ)) := by ring
      · have hp := hp12 11 (by norm_num)
        calc _ ≤ (MD * |t| ^ (-(7 / 2 : ℝ))) * 2 ^ 12 * 1 := by gcongr
          _ = MD * 2 ^ 12 * |t| ^ (-(7 / 2 : ℝ)) := by ring
      · have hp := hp12 12 le_rfl
        calc _ ≤ (MD * |t| ^ (-(9 / 2 : ℝ))) * 2 ^ 12 * 1 := by gcongr
          _ = MD * 2 ^ 12 * |t| ^ (-(9 / 2 : ℝ)) := by ring)
  have hMain_fn : (fun τ : ℝ => (oneSubITauInvSqrt τ * expBinetImag c τ *
      fctLeftTail K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) τ *
      fctPhiHat h ε c (1 - (τ : ℂ) * Complex.I)) *
      (fctDcompAt K4 c (fctWarpAlpha h ε c) ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))) =
      warpAmpLeft h ε c ξ := by
    ext τ; unfold warpAmpLeft; ring
  have hcd_amp : ContDiffOn ℝ 2 (warpAmpLeft h ε c ξ) S := by
    rw [← hMain_fn]; exact hMain.1
  refine ⟨hcd_amp, fun τ hτ hτ16 => ?_, fun τ hτ16 => ?_⟩
  · -- Near `0 < |τ| ≤ 1/16`
    have hτU : τ ∈ U_near := ⟨hτ, by linarith⟩
    have hτpos : 0 < |τ| := abs_pos.mpr hτ
    obtain ⟨b0, b1, b2⟩ := hMain_near.2 τ hτU
    rw [congrFun hMain_fn τ] at b0
    rw [hMain_fn] at b1 b2
    have hpow_3_52 : |τ| ^ 3 * |τ| ^ (-(5 / 2 : ℝ)) = |τ| ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast |τ|, ← Real.rpow_add hτpos]; congr 1; norm_num
    have hpow_2_52 : |τ| ^ 2 * |τ| ^ (-(5 / 2 : ℝ)) = |τ| ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast |τ|, ← Real.rpow_add hτpos]; congr 1; norm_num
    have hpow_3_72 : |τ| ^ 3 * |τ| ^ (-(7 / 2 : ℝ)) = |τ| ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast |τ|, ← Real.rpow_add hτpos]; congr 1; norm_num
    have hpow_1_52 : |τ| * |τ| ^ (-(5 / 2 : ℝ)) = |τ| ^ (-(3 / 2 : ℝ)) := by
      nth_rw 1 [← Real.rpow_one |τ|]; rw [← Real.rpow_add hτpos]; congr 1; norm_num
    have hpow_2_72 : |τ| ^ 2 * |τ| ^ (-(7 / 2 : ℝ)) = |τ| ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast |τ|, ← Real.rpow_add hτpos]; congr 1; norm_num
    have hpow_3_92 : |τ| ^ 3 * |τ| ^ (-(9 / 2 : ℝ)) = |τ| ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast |τ|, ← Real.rpow_add hτpos]; congr 1; norm_num
    have hC_le : ∀ m : ℝ, 0 ≤ m → m ≤ 4 → m * (C_mid1 * MD * 2 ^ 12) ≤ C_tot := fun m hm0 hm4 => by
      have h1 : C_mid1 ≤ max C_mid1 C_gl1 := le_max_left _ _
      have h2 : (2 : ℝ) ^ 12 ≤ max (2 ^ 12) (16 ^ (9 / 2 : ℝ)) := le_max_left _ _
      calc m * (C_mid1 * MD * 2 ^ 12) ≤ 4 * (max C_mid1 C_gl1 * MD * max (2 ^ 12) (16 ^ (9 / 2 : ℝ))) := by
            gcongr
        _ = C_tot := by simp only [C_tot]; ring
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · calc (C_mid1 * c⁻¹ * |τ| ^ 3) * (MD * 2 ^ 12 * |τ| ^ (-(5 / 2 : ℝ)))
          = 1 * (C_mid1 * MD * 2 ^ 12) * c⁻¹ * (|τ| ^ 3 * |τ| ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ C_tot * c⁻¹ * |τ| ^ (1 / 2 : ℝ) := by
            rw [hpow_3_52]; have := hC_le 1 zero_le_one (by norm_num); gcongr
    · calc (C_mid1 * c⁻¹ * |τ| ^ 2) * (MD * 2 ^ 12 * |τ| ^ (-(5 / 2 : ℝ))) +
            (C_mid1 * c⁻¹ * |τ| ^ 3) * (MD * 2 ^ 12 * |τ| ^ (-(7 / 2 : ℝ)))
          = (C_mid1 * MD * 2 ^ 12) * c⁻¹ *
              (|τ| ^ 2 * |τ| ^ (-(5 / 2 : ℝ)) + |τ| ^ 3 * |τ| ^ (-(7 / 2 : ℝ))) := by ring
        _ = 2 * (C_mid1 * MD * 2 ^ 12) * c⁻¹ * |τ| ^ (-(1 / 2 : ℝ)) := by
            rw [hpow_2_52, hpow_3_72]; ring
        _ ≤ C_tot * c⁻¹ * |τ| ^ (-(1 / 2 : ℝ)) := by
            have := hC_le 2 (by norm_num) (by norm_num); gcongr
    · calc (C_mid1 * c⁻¹ * |τ|) * (MD * 2 ^ 12 * |τ| ^ (-(5 / 2 : ℝ))) +
            2 * ((C_mid1 * c⁻¹ * |τ| ^ 2) * (MD * 2 ^ 12 * |τ| ^ (-(7 / 2 : ℝ)))) +
            (C_mid1 * c⁻¹ * |τ| ^ 3) * (MD * 2 ^ 12 * |τ| ^ (-(9 / 2 : ℝ)))
          = (C_mid1 * MD * 2 ^ 12) * c⁻¹ *
              (|τ| * |τ| ^ (-(5 / 2 : ℝ)) + 2 * (|τ| ^ 2 * |τ| ^ (-(7 / 2 : ℝ))) +
                |τ| ^ 3 * |τ| ^ (-(9 / 2 : ℝ))) := by ring
        _ = 4 * (C_mid1 * MD * 2 ^ 12) * c⁻¹ * |τ| ^ (-(3 / 2 : ℝ)) := by
            rw [hpow_1_52, hpow_2_72, hpow_3_92]; ring
        _ ≤ C_tot * c⁻¹ * |τ| ^ (-(3 / 2 : ℝ)) := by
            have := hC_le 4 (by norm_num) le_rfl; gcongr
  · -- Outer `1/16 ≤ |τ|`
    have hτne : τ ≠ 0 := abs_pos.mp (by linarith)
    obtain ⟨b0, b1, b2⟩ := hMain.2 τ hτne
    rw [congrFun hMain_fn τ] at b0
    rw [hMain_fn] at b1 b2
    have hτ16' : (1 / 16 : ℝ) ≤ |τ| := hτ16
    have hpow_neg : ∀ q : ℝ, 0 ≤ q → q ≤ 9 / 2 → |τ| ^ (-q) ≤ 16 ^ (9 / 2 : ℝ) := fun q hq0 hq9 => by
      rw [Real.rpow_neg (by linarith)]
      have h1 : |τ| ^ q ≥ (1 / 16 : ℝ) ^ q := Real.rpow_le_rpow (by norm_num) hτ16' hq0
      have h2 : (|τ| ^ q)⁻¹ ≤ ((1 / 16 : ℝ) ^ q)⁻¹ := inv_anti₀ (by positivity) h1
      calc (|τ| ^ q)⁻¹ ≤ ((1 / 16 : ℝ) ^ q)⁻¹ := h2
        _ = 16 ^ q := by rw [one_div, Real.inv_rpow (by norm_num), inv_inv]
        _ ≤ 16 ^ (9 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq9
    have hp12 : ∀ m : ℕ, m ≤ 12 → (1 + |τ|) ^ m ≤ (1 + |τ|) ^ 12 := fun m hm =>
      pow_le_pow_right₀ (by linarith [abs_nonneg τ]) hm
    have hp10 : (1 + |τ|) ^ 10 ≤ (1 + |τ|) ^ 12 := hp12 10 (by norm_num)
    have hp11 : (1 + |τ|) ^ 11 ≤ (1 + |τ|) ^ 12 := hp12 11 (by norm_num)
    have hpow_52 : |τ| ^ (-(5 / 2 : ℝ)) ≤ 16 ^ (9 / 2 : ℝ) := by
      simpa using hpow_neg (5 / 2) (by norm_num) (by norm_num)
    have hpow_72 : |τ| ^ (-(7 / 2 : ℝ)) ≤ 16 ^ (9 / 2 : ℝ) := by
      simpa using hpow_neg (7 / 2) (by norm_num) (by norm_num)
    have hpow_92 : |τ| ^ (-(9 / 2 : ℝ)) ≤ 16 ^ (9 / 2 : ℝ) := by
      simpa using hpow_neg (9 / 2) (by norm_num) le_rfl
    have hexp0 : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
    have hC_le : ∀ m : ℝ, 0 ≤ m → m ≤ 4 → m * (C_gl1 * MD * 16 ^ (9 / 2 : ℝ)) ≤ C_tot := fun m hm0 hm4 => by
      have h1 : C_gl1 ≤ max C_mid1 C_gl1 := le_max_right _ _
      have h2 : (16 : ℝ) ^ (9 / 2 : ℝ) ≤ max (2 ^ 12) (16 ^ (9 / 2 : ℝ)) := le_max_right _ _
      calc m * (C_gl1 * MD * 16 ^ (9 / 2 : ℝ)) ≤ 4 * (max C_mid1 C_gl1 * MD * max (2 ^ 12) (16 ^ (9 / 2 : ℝ))) := by
            gcongr
        _ = C_tot := by simp only [C_tot]; ring
    have hgl_nn : 0 ≤ C_gl1 * c⁻¹ * (1 + |τ|) ^ 2 := by positivity
    refine ⟨b0.trans ?_, b1.trans ?_, b2.trans ?_⟩
    · calc (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|)))
          ≤ (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * 16 ^ (9 / 2 : ℝ) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by gcongr
        _ = 1 * (C_gl1 * MD * 16 ^ (9 / 2 : ℝ)) * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := by ring
        _ ≤ C_tot * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := by
            have := hC_le 1 zero_le_one (by norm_num); gcongr
    · calc (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) +
            (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * |τ| ^ (-(7 / 2 : ℝ)) * (1 + |τ|) ^ 11 * Real.exp (-(π * |τ|)))
          ≤ (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * 16 ^ (9 / 2 : ℝ) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) +
            (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * 16 ^ (9 / 2 : ℝ) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by gcongr
        _ = 2 * (C_gl1 * MD * 16 ^ (9 / 2 : ℝ)) * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := by ring
        _ ≤ C_tot * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := by
            have := hC_le 2 (by norm_num) (by norm_num); gcongr
    · calc (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * |τ| ^ (-(5 / 2 : ℝ)) * (1 + |τ|) ^ 10 * Real.exp (-(π * |τ|))) +
            2 * ((C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * |τ| ^ (-(7 / 2 : ℝ)) * (1 + |τ|) ^ 11 * Real.exp (-(π * |τ|)))) +
            (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * |τ| ^ (-(9 / 2 : ℝ)) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)))
          ≤ (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * 16 ^ (9 / 2 : ℝ) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) +
            2 * ((C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * 16 ^ (9 / 2 : ℝ) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|)))) +
            (C_gl1 * c⁻¹ * (1 + |τ|) ^ 2) * (MD * 16 ^ (9 / 2 : ℝ) * (1 + |τ|) ^ 12 * Real.exp (-(π * |τ|))) := by gcongr
        _ = 4 * (C_gl1 * MD * 16 ^ (9 / 2 : ℝ)) * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := by ring
        _ ≤ C_tot * c⁻¹ * (1 + |τ|) ^ 14 * Real.exp (-(π * |τ|)) := by
            have := hC_le 4 (by norm_num) le_rfl; gcongr

/-- info: 'FormalResearch.SignUncertainty.warpAmpLeft_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms warpAmpLeft_bounds

end FormalResearch.SignUncertainty

