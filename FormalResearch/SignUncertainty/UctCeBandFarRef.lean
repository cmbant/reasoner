module

public import FormalResearch.SignUncertainty.UctAiryTransPhi
public import FormalResearch.SignUncertainty.CtOuterCutoff
public import FormalResearch.SignUncertainty.CtOuterTheta3
public import FormalResearch.CohnElkies.DualPhaseAndO3
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `uct:ce-band` (1): global `O(c^{-1/2})` bound, IBP helpers, and smooth-cutoff Gamma reference

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:ce-band` (1).

Main results:
* `uctAlphaHhat`, `uctIflHhat`, `uctHnormCE`: the paper's `α_{ĥ} = (π^{3/2}/4) |C_Ai|`,
  `I_fl^{ĥ}(L) = α_{ĥ} L^{-1/2} e^{-L}`, and normalized density `h_norm^{ĥ}(L)`.
* `uctHnormCE_eq_mellin`: identifies `h_norm^{ĥ}(L)` with `(c^{1/3}/(2π)) ∫ K₀(iτ, ξ) W̃_{ĥ}(iτ) dτ`
  under the imaginary-edge factorization `(uct:KW-hhat-edge)`.
* `uct_ce_band_global_bound`: under `|A(τ)| ≤ C₀ e^{-η|τ|}` (`η > 0`), the edge integral converges
  absolutely and `‖h_norm^{ĥ}(L)‖ ≤ C c^{-1/2}` uniformly for all `c > 0` and `L ∈ ℝ`.
* `regSqrt` derivative bounds, `smoothCutoff0`, `ibp_one_phase`, `ibp_two_linear`.
* `regSqrt_cutoff_fourier`: for `lam, ω, ς > 0`,
  `‖(2π)⁻¹ ∫ χ₀(τ/ς) (lam + iτ)^{-1/2} e^{i ω τ} dτ - π^{-1/2} ω^{-1/2} e^{-lam ω}‖ ≤ C ω^{-2} ς^{-3/2}`.

Class: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### Constants and normalized density -/

/-- `α_{ĥ} = (π^{3/2} / 4) |C_Ai|` (`constant_terms_upper.tex`). -/
noncomputable def uctAlphaHhat : ℝ := (π ^ (3 / 2 : ℝ) / 4) * |uctCAi|

/-- `I_fl^{ĥ}(L) = α_{ĥ} L^{-1/2} e^{-L}` (`constant_terms_upper.tex`). -/
noncomputable def uctIflHhat (L : ℝ) : ℝ := uctAlphaHhat * L ^ (-(1 / 2 : ℝ)) * Real.exp (-L)

/-- Regularized square-root factor `R_lam(τ) = (lam + i τ)^{-1/2}`. -/
noncomputable def regSqrt (lam τ : ℝ) : ℂ := ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))

/-- Normalized density `h_norm^{ĥ}(L)` written in terms of the combined amplitude `A(τ) = e^{iϑ(τ)} M(τ)`
via `(uct:KW-hhat-edge)`. -/
noncomputable def uctHnormCE (c L : ℝ) (A : ℝ → ℂ) : ℂ :=
  ((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) *
    ∫ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ

/-- Identification of `(c^{1/3} / (2π)) ∫ K₀(iτ, ξ) W̃(iτ) dτ` with `uctHnormCE c L A` under
`(uct:KW-hhat-edge)`. -/
lemma uctHnormCE_eq_mellin {c L ξ : ℝ} (hc : 0 < c) {W : ℂ → ℂ} {A : ℝ → ℂ}
    (hfac : ∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) =
      ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
        A τ * regSqrt (1 / c) τ) :
    ((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
        ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) =
      uctHnormCE c L A := by
  have hint_eq : ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) =
      ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
        ∫ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
          A τ * regSqrt (1 / c) τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    dsimp only; rw [hfac τ]; ring
  rw [hint_eq]
  unfold uctHnormCE
  have hpow : c ^ (1 / 3 : ℝ) * c ^ (-(5 / 6 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hc]; norm_num
  have hpref : ((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) =
      ((c ^ (-(1 / 2 : ℝ)) / (2 * π) : ℝ) : ℂ) * ((π ^ 2 / 4 * |uctCAi| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc c ^ (1 / 3 : ℝ) / (2 * π) * (π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)))
        = (c ^ (1 / 3 : ℝ) * c ^ (-(5 / 6 : ℝ))) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) := by ring
      _ = c ^ (-(1 / 2 : ℝ)) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) := by rw [hpow]
  rw [← mul_assoc, hpref]

/-! ### Small algebraic/calculus helpers -/

private lemma rpow_neg_two_eq (x : ℝ) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp [zpow_neg]

private lemma contDiff_one_deriv_of_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ) + 1) f from hf)).2.2

/-! ### Bounds and derivatives for `regSqrt` -/

lemma norm_regSqrt_eq {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ‖regSqrt lam τ‖ = (lam ^ 2 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  unfold regSqrt
  have hz_ne : (lam : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hnorm_sq : ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 = lam ^ 2 + τ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [sq]
  have hnorm_eq : ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ = (lam ^ 2 + τ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hnorm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hnorm_pos : 0 < ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ := norm_pos_iff.mpr hz_ne
  rw [Complex.cpow_def_of_ne_zero hz_ne, Complex.norm_exp,
    show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
    ← Real.rpow_def_of_pos hnorm_pos, hnorm_eq, ← Real.rpow_mul (by positivity)]
  norm_num

lemma norm_regSqrt_le_abs_rpow {lam : ℝ} (hlam : 0 < lam) {τ : ℝ} (hτ : τ ≠ 0) :
    ‖regSqrt lam τ‖ ≤ |τ| ^ (-(1 / 2 : ℝ)) := by
  rw [norm_regSqrt_eq hlam]
  have h1 : |τ| ^ 2 ≤ lam ^ 2 + τ ^ 2 := by rw [sq_abs]; linarith [sq_nonneg lam]
  have h2 : (lam ^ 2 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ (|τ| ^ 2) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (abs_pos.mpr hτ)) h1 (by norm_num)
  refine h2.trans_eq ?_
  rw [← Real.rpow_natCast |τ| 2, ← Real.rpow_mul (abs_nonneg τ)]; norm_num

/-- Exact upper bound `‖(lam + iτ)^{-1/2}‖ ≤ 2^{1/4} (lam + |τ|)^{-1/2}`. -/
lemma norm_regSqrt_le_sum {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ‖regSqrt lam τ‖ ≤ 2 ^ (1 / 4 : ℝ) * (lam + |τ|) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_regSqrt_eq hlam]
  have h1 : (lam + |τ|) ^ 2 / 2 ≤ lam ^ 2 + τ ^ 2 := by
    have hsq : |τ| ^ 2 = τ ^ 2 := sq_abs τ
    nlinarith [sq_nonneg (lam - |τ|), hsq]
  have h2 : (lam ^ 2 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ ((lam + |τ|) ^ 2 / 2) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  refine h2.trans_eq ?_
  have h2inv : ((2 : ℝ)⁻¹) ^ (-(1 / 4 : ℝ)) = 2 ^ (1 / 4 : ℝ) := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  rw [div_eq_mul_inv, Real.mul_rpow (sq_nonneg _) (by norm_num), h2inv,
    ← Real.rpow_natCast (lam + |τ|) 2, ← Real.rpow_mul (by positivity), mul_comm]
  norm_num

private lemma hasDerivAt_regSqrt_pow {lam : ℝ} (hlam : 0 < lam) (p : ℂ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => ((lam : ℂ) + (t : ℂ) * Complex.I) ^ p)
      (p * Complex.I * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (p - 1)) τ := by
  have hlin : HasDerivAt (fun t : ℝ => (lam : ℂ) + (t : ℂ) * Complex.I) Complex.I τ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (1 * Complex.I) τ :=
      (Complex.ofRealCLM.hasDerivAt (x := τ)).mul_const Complex.I
    exact (h1.const_add (lam : ℂ)).congr_deriv (one_mul Complex.I)
  have hslit : (lam : ℂ) + (τ : ℂ) * Complex.I ∈ Complex.slitPlane := Or.inl (by simp [hlam])
  have hcp := ((hasDerivAt_id ((lam : ℂ) + (τ : ℂ) * Complex.I)).cpow_const hslit (c := p)).comp τ hlin
  exact hcp.congr_deriv (by simp [id_eq]; ring)

lemma hasDerivAt_regSqrt {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    HasDerivAt (regSqrt lam) (-(1 / 2 : ℂ) * Complex.I * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ))) τ := by
  have h := hasDerivAt_regSqrt_pow hlam (-(1 / 2 : ℂ)) τ
  refine h.congr_deriv ?_
  have : -(1 / 2 : ℂ) - 1 = -(3 / 2 : ℂ) := by ring
  rw [this]

lemma hasDerivAt_deriv_regSqrt {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    HasDerivAt (deriv (regSqrt lam)) (-(3 / 4 : ℂ) * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ))) τ := by
  have heq : deriv (regSqrt lam) = fun t : ℝ =>
      -(1 / 2 : ℂ) * Complex.I * ((lam : ℂ) + (t : ℂ) * Complex.I) ^ (-(3 / 2 : ℂ)) :=
    funext fun t => (hasDerivAt_regSqrt hlam t).deriv
  rw [heq]
  have h := (hasDerivAt_regSqrt_pow hlam (-(3 / 2 : ℂ)) τ).const_mul (-(1 / 2 : ℂ) * Complex.I)
  refine h.congr_deriv ?_
  have h1 : -(3 / 2 : ℂ) - 1 = -(5 / 2 : ℂ) := by ring
  rw [h1]
  calc -(1 / 2 : ℂ) * Complex.I * (-(3 / 2 : ℂ) * Complex.I * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)))
      = (3 / 4 : ℂ) * (Complex.I * Complex.I) * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by ring
    _ = -(3 / 4 : ℂ) * ((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) := by rw [Complex.I_mul_I]; ring

lemma contDiff_regSqrt {lam : ℝ} (hlam : 0 < lam) : ContDiff ℝ 2 (regSqrt lam) := by
  rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun τ => (hasDerivAt_regSqrt hlam τ).differentiableAt, by simp, ?_⟩
  rw [show ((1 : ℕ) : WithTop ℕ∞) = (0 : ℕ) + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun τ => (hasDerivAt_deriv_regSqrt hlam τ).differentiableAt, by simp, contDiff_zero.mpr ?_⟩
  have heq : deriv (deriv (regSqrt lam)) = fun t : ℝ =>
      -(3 / 4 : ℂ) * ((lam : ℂ) + (t : ℂ) * Complex.I) ^ (-(5 / 2 : ℂ)) :=
    funext fun t => (hasDerivAt_deriv_regSqrt hlam t).deriv
  rw [heq]
  exact continuous_const.mul (Continuous.cpow (by fun_prop) continuous_const fun t => Or.inl (by simp [hlam]))

private lemma norm_cpow_neg_real_le_sum {lam p : ℝ} (hlam : 0 < lam) (hp : 0 < p) (τ : ℝ) :
    ‖((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(p : ℂ))‖ ≤ 2 ^ (p / 2) * (lam + |τ|) ^ (-p) := by
  have hz_ne : (lam : ℂ) + (τ : ℂ) * Complex.I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hnorm_sq : ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 = lam ^ 2 + τ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [sq]
  have hnorm_pos : 0 < ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ := norm_pos_iff.mpr hz_ne
  rw [Complex.cpow_def_of_ne_zero hz_ne, Complex.norm_exp,
    show -(p : ℂ) = ((-p : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
    ← Real.rpow_def_of_pos hnorm_pos]
  have hnorm_ge : (lam + |τ|) / √2 ≤ ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ := by
    have hsq : ((lam + |τ|) / √2) ^ 2 ≤ ‖(lam : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 := by
      rw [hnorm_sq, div_pow, Real.sq_sqrt (by norm_num)]
      have : |τ| ^ 2 = τ ^ 2 := sq_abs τ
      nlinarith [sq_nonneg (lam - |τ|), this]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hnorm_ge (by linarith : -p ≤ 0)
  refine h1.trans_eq ?_
  have h2inv : ((√2)⁻¹) ^ (-p) = 2 ^ (p / 2) := by
    rw [Real.inv_rpow (Real.sqrt_nonneg _), Real.rpow_neg (Real.sqrt_nonneg _), inv_inv,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity), h2inv, mul_comm]

lemma norm_deriv_regSqrt_le {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ‖deriv (regSqrt lam) τ‖ ≤ 2 * (lam + |τ|) ^ (-(3 / 2 : ℝ)) := by
  rw [(hasDerivAt_regSqrt hlam τ).deriv, norm_mul, norm_mul, Complex.norm_I, mul_one,
    norm_neg, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have h := norm_cpow_neg_real_le_sum hlam (p := 3 / 2) (by norm_num) τ
  have hcast : -(3 / 2 : ℂ) = -(((3 / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [hcast]
  have h2pow : (1 / 2 : ℝ) * 2 ^ ((3 / 2 : ℝ) / 2) ≤ 2 := by
    have : (2 : ℝ) ^ ((3 / 2 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    norm_num at this; linarith
  calc (1 / 2 : ℝ) * ‖((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(((3 / 2 : ℝ) : ℂ)))‖
      ≤ (1 / 2 : ℝ) * (2 ^ ((3 / 2 : ℝ) / 2) * (lam + |τ|) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ((1 / 2 : ℝ) * 2 ^ ((3 / 2 : ℝ) / 2)) * (lam + |τ|) ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ 2 * (lam + |τ|) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h2pow (by positivity)

lemma norm_iteratedDeriv2_regSqrt_le {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ‖iteratedDeriv 2 (regSqrt lam) τ‖ ≤ 3 * (lam + |τ|) ^ (-(5 / 2 : ℝ)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (hasDerivAt_deriv_regSqrt hlam τ).deriv,
    norm_mul, norm_neg, show ‖(3 / 4 : ℂ)‖ = 3 / 4 by norm_num]
  have h := norm_cpow_neg_real_le_sum hlam (p := 5 / 2) (by norm_num) τ
  have hcast : -(5 / 2 : ℂ) = -(((5 / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [hcast]
  have h2pow : (3 / 4 : ℝ) * 2 ^ ((5 / 2 : ℝ) / 2) ≤ 3 := by
    have : (2 : ℝ) ^ ((5 / 2 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    norm_num at this; linarith
  calc (3 / 4 : ℝ) * ‖((lam : ℂ) + (τ : ℂ) * Complex.I) ^ (-(((5 / 2 : ℝ) : ℂ)))‖
      ≤ (3 / 4 : ℝ) * (2 ^ ((5 / 2 : ℝ) / 2) * (lam + |τ|) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ((3 / 4 : ℝ) * 2 ^ ((5 / 2 : ℝ) / 2)) * (lam + |τ|) ^ (-(5 / 2 : ℝ)) := by ring
    _ ≤ 3 * (lam + |τ|) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h2pow (by positivity)

/-! ### Global `O(c^{-1/2})` bound (end of `uct:ce-band` (1)) -/

/-- **Lemma `uct:ce-band` (1), global `O(c^{-1/2})` bound** (`constant_terms_upper.tex`):
under the exponential decay bound `‖A(τ)‖ ≤ C₀ e^{-η|τ|}` (`η > 0`, `C₀ ≥ 0`), the edge integral
converges absolutely and `‖h_norm^{ĥ}(L)‖ ≤ (π^{3/2} |C_Ai| C₀ / (4 √η)) c^{-1/2}` for all `c > 0`
and all `L ∈ ℝ`. -/
theorem uct_ce_band_global_bound {C₀ η : ℝ} (hC₀ : 0 ≤ C₀) (hη : 0 < η)
    {A : ℝ → ℂ} (hA_cont : Continuous A) (hA_bd : ∀ τ : ℝ, ‖A τ‖ ≤ C₀ * Real.exp (-η * |τ|))
    {c : ℝ} (hc : 0 < c) (L : ℝ) :
    Integrable (fun τ : ℝ =>
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
        A τ * regSqrt (1 / c) τ) ∧
    ‖uctHnormCE c L A‖ ≤ (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) * c ^ (-(1 / 2 : ℝ)) := by
  have h1c : 0 < 1 / c := one_div_pos.mpr hc
  have hGamma_half : IntegrableOn (fun t : ℝ => Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) = √π / √η := by
    have hG := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
    have hG_eq : ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) = √π := by
      have h := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 1 / 2)
      rw [Real.Gamma_one_half_eq] at h
      rw [h]; refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by norm_num
    have hcomp := (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) 0 hη).mpr (by
        simpa only [mul_zero] using hG.congr_fun (fun t _ => by norm_num) measurableSet_Ioi)
    have hint : IntegrableOn (fun t : ℝ => Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
      refine (hcomp.const_mul (η ^ (1 / 2 : ℝ))).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [Real.mul_rpow hη.le ht0.le, show -(η * t) = -η * t by ring]
      have hcancel : η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hη]; norm_num
      calc η ^ (1 / 2 : ℝ) * (Real.exp (-η * t) * (η ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))))
          = (η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ))) * (Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))) := by ring
        _ = Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) := by rw [hcancel, one_mul]
    have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) = √π / √η := by
      have hcov := MeasureTheory.integral_comp_mul_left_Ioi
        (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) (0 : ℝ) hη
      simp only [mul_zero, smul_eq_mul, hG_eq] at hcov
      have hstep : ∫ t in Ioi (0 : ℝ), Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ)) =
          η ^ (1 / 2 : ℝ) * ∫ t in Ioi (0 : ℝ), Real.exp (-(η * t)) * (η * t) ^ (-(1 / 2 : ℝ)) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        rw [Real.mul_rpow hη.le ht0.le, show -η * t = -(η * t) by ring]
        have hcancel : η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hη]; norm_num
        calc Real.exp (-(η * t)) * t ^ (-(1 / 2 : ℝ))
            = (η ^ (1 / 2 : ℝ) * η ^ (-(1 / 2 : ℝ))) * (Real.exp (-(η * t)) * t ^ (-(1 / 2 : ℝ))) := by
              rw [hcancel, one_mul]
          _ = _ := by ring
      rw [hstep, hcov]
      have hpow : η ^ (1 / 2 : ℝ) * η⁻¹ = (√η)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hη, Real.sqrt_eq_rpow, ← Real.rpow_neg hη.le]; norm_num
      calc η ^ (1 / 2 : ℝ) * (η⁻¹ * √π) = (η ^ (1 / 2 : ℝ) * η⁻¹) * √π := by ring
        _ = (√η)⁻¹ * √π := by rw [hpow]
        _ = √π / √η := by rw [div_eq_mul_inv, mul_comm]
    exact ⟨hint, hval⟩
  have hmaj_int : Integrable (fun τ : ℝ => C₀ * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ)))) := by
    have heven : Integrable (fun τ : ℝ => Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) := by
      have hpos : IntegrableOn (fun τ : ℝ => Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) (Ioi (0 : ℝ)) :=
        hGamma_half.1.congr_fun (fun τ hτ => by rw [abs_of_pos hτ]) measurableSet_Ioi
      have hneg : IntegrableOn (fun τ : ℝ => Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) (Iio (0 : ℝ)) := by
        have hcomp := hGamma_half.1.comp_neg
        have h1 : IntegrableOn (fun τ : ℝ => Real.exp (-η * (-τ)) * (-τ) ^ (-(1 / 2 : ℝ))) (Iio (0 : ℝ)) := by
          convert hcomp using 1
          ext x; simp only [mem_Iio, Set.mem_neg, mem_Ioi]; constructor <;> intro h <;> linarith
        exact h1.congr_fun (fun τ hτ => by rw [abs_of_neg hτ]) measurableSet_Iio
      have hU : (Iio (0 : ℝ) ∪ Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume] univ := by
        rw [show (Iio (0 : ℝ) ∪ Ioi (0 : ℝ) : Set ℝ) = ({0} : Set ℝ)ᶜ by
          ext x; simp only [mem_union, mem_Iio, mem_Ioi, mem_compl_iff, mem_singleton_iff]
          exact lt_or_lt_iff_ne, ae_eq_univ]
        exact compl_mem_ae_iff.mpr (measure_singleton 0)
      rw [← integrableOn_univ]
      exact (hneg.union hpos).congr_set_ae hU.symm
    exact heven.const_mul C₀
  have hmaj_val : ∫ τ : ℝ, C₀ * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) = 2 * C₀ * (√π / √η) := by
    rw [integral_const_mul, integral_comp_abs (f := fun t : ℝ => Real.exp (-η * t) * t ^ (-(1 / 2 : ℝ))),
      hGamma_half.2]
    ring
  have hcont : Continuous (fun τ : ℝ =>
      Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
        A τ * regSqrt (1 / c) τ) := by
    have hphi : Continuous (edgePhi L) := by
      rw [show edgePhi L = fun τ => L * τ - π ^ 2 / 36 * τ ^ 3 + edgeR τ from
        funext (edgePhi_eq_cubic_add_ceHth L)]
      exact (((continuous_const.mul continuous_id).sub (continuous_const.mul (continuous_id.pow 3))).add
        edgeR_contDiff.continuous)
    have hθ : Continuous (CtOuter.outerTheta (-1)) := (CtOuter.contDiff_outerTheta (-1)).continuous
    have hreg : Continuous (regSqrt (1 / c)) := (contDiff_regSqrt h1c).continuous
    exact ((Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_const.mul hphi).sub hθ)))).mul hA_cont).mul hreg
  have hbd_ae : ∀ᵐ τ : ℝ, ‖Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ‖ ≤ C₀ * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with τ hτ
    rw [norm_mul, norm_mul, show Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ) =
        ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    calc ‖A τ‖ * ‖regSqrt (1 / c) τ‖
        ≤ (C₀ * Real.exp (-η * |τ|)) * |τ| ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul (hA_bd τ) (norm_regSqrt_le_abs_rpow h1c hτ) (norm_nonneg _) (by positivity)
      _ = C₀ * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) := by ring
  have hint := hmaj_int.mono' hcont.aestronglyMeasurable hbd_ae
  refine ⟨hint, ?_⟩
  unfold uctHnormCE
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hint_le : ‖∫ τ : ℝ, Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
      A τ * regSqrt (1 / c) τ‖ ≤ 2 * C₀ * (√π / √η) := by
    calc ‖∫ τ : ℝ, _‖ ≤ ∫ τ : ℝ, ‖Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
            A τ * regSqrt (1 / c) τ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ τ : ℝ, C₀ * (Real.exp (-η * |τ|) * |τ| ^ (-(1 / 2 : ℝ))) :=
          integral_mono_ae hint.norm hmaj_int hbd_ae
      _ = 2 * C₀ * (√π / √η) := hmaj_val
  have hpi32 : π ^ (3 / 2 : ℝ) = π * √π := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one]
  calc c ^ (-(1 / 2 : ℝ)) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) * ‖∫ τ : ℝ, _‖
      ≤ c ^ (-(1 / 2 : ℝ)) / (2 * π) * (π ^ 2 / 4 * |uctCAi|) * (2 * C₀ * (√π / √η)) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) * c ^ (-(1 / 2 : ℝ)) := by
        rw [hpi32]; field_simp [Real.pi_ne_zero]

/-! ### Smooth cutoff `χ₀(t) = CtOuter.chi (2 t)` (`1` on `|t| ≤ 1/2`, `0` on `|t| ≥ 1`) -/

/-- Smooth even cutoff equal to `1` on `|t| ≤ 1/2` and `0` on `|t| ≥ 1`. -/
noncomputable def smoothCutoff0 (t : ℝ) : ℝ := CtOuter.chi (2 * t)

lemma smoothCutoff0_nonneg (t : ℝ) : 0 ≤ smoothCutoff0 t := CtOuter.chi_nonneg _
lemma smoothCutoff0_le_one (t : ℝ) : smoothCutoff0 t ≤ 1 := CtOuter.chi_le_one _

lemma smoothCutoff0_eq_one {t : ℝ} (ht : |t| ≤ 1 / 2) : smoothCutoff0 t = 1 :=
  CtOuter.chi_eq_one (by rw [abs_mul, abs_of_pos two_pos]; linarith)

lemma smoothCutoff0_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : smoothCutoff0 t = 0 :=
  CtOuter.chi_eq_zero (by rw [abs_mul, abs_of_pos two_pos]; linarith)

lemma contDiff_smoothCutoff0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) smoothCutoff0 :=
  CtOuter.contDiff_chi.comp (contDiff_const.mul contDiff_id)

lemma smoothCutoff0_deriv_bounds :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      |deriv smoothCutoff0 t| ≤ B ∧ |iteratedDeriv 2 smoothCutoff0 t| ≤ B ∧
      (|t| < 1 / 2 → deriv smoothCutoff0 t = 0 ∧ iteratedDeriv 2 smoothCutoff0 t = 0) ∧
      (1 < |t| → deriv smoothCutoff0 t = 0 ∧ iteratedDeriv 2 smoothCutoff0 t = 0) := by
  have hcd := contDiff_smoothCutoff0
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (hcd.continuous_deriv (by decide)).continuousOn
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) (hcd.continuous_iteratedDeriv 2 (by simp)).continuousOn
  have hzero_in : ∀ t : ℝ, |t| < 1 / 2 → deriv smoothCutoff0 t = 0 ∧ iteratedDeriv 2 smoothCutoff0 t = 0 := by
    intro t ht
    have hev : smoothCutoff0 =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with s hs
      exact smoothCutoff0_eq_one hs.le
    refine ⟨by rw [hev.deriv_eq, deriv_const], ?_⟩
    rw [hev.iteratedDeriv_eq 2, iteratedDeriv_const]; simp
  have hzero_out : ∀ t : ℝ, 1 < |t| → deriv smoothCutoff0 t = 0 ∧ iteratedDeriv 2 smoothCutoff0 t = 0 := by
    intro t ht
    have hev : smoothCutoff0 =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs
      exact smoothCutoff0_eq_zero hs.le
    refine ⟨by rw [hev.deriv_eq, deriv_const], ?_⟩
    rw [hev.iteratedDeriv_eq 2, iteratedDeriv_const]; simp
  refine ⟨max 1 (max B₁ B₂), lt_of_lt_of_le one_pos (le_max_left _ _), fun t => ?_⟩
  refine ⟨?_, ?_, hzero_in t, hzero_out t⟩
  · by_cases ht : |t| ≤ 1
    · have hmem : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp ht
      exact (hB₁ t hmem).trans ((le_max_left B₁ B₂).trans (le_max_right 1 _))
    · rw [(hzero_out t (not_le.mp ht)).1, abs_zero]
      exact (lt_of_lt_of_le one_pos (le_max_left _ _)).le
  · by_cases ht : |t| ≤ 1
    · have hmem : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp ht
      exact (hB₂ t hmem).trans ((le_max_right B₁ B₂).trans (le_max_right 1 _))
    · rw [(hzero_out t (not_le.mp ht)).2, abs_zero]
      exact (lt_of_lt_of_le one_pos (le_max_left _ _)).le

/-! ### Two-fold integration by parts for compactly supported `C²` amplitudes -/

/-- One-step IBP for a `C¹` function `f` supported in `[-M, M]` against `e^{i ψ(τ)}`. -/
lemma ibp_one_phase {M : ℝ} (hM : 0 < M) {f : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 2 ψ)
    (hsupp : ∀ τ : ℝ, M ≤ |τ| → f τ = 0)
    (hψ' : ∀ τ ∈ Icc (-M) M, deriv ψ τ ≠ 0) :
    ∫ τ : ℝ, f τ * Complex.exp (Complex.I * (ψ τ : ℂ)) =
      Complex.I * ∫ τ in Icc (-M) M,
        deriv (fun t : ℝ => f t / ((deriv ψ t : ℝ) : ℂ)) τ * Complex.exp (Complex.I * (ψ τ : ℂ)) := by
  have hsupp_eq : ∫ τ : ℝ, f τ * Complex.exp (Complex.I * (ψ τ : ℂ)) =
      ∫ τ in (-M)..M, f τ * Complex.exp (Complex.I * (ψ τ : ℂ)) := by
    have hind : (fun τ : ℝ => f τ * Complex.exp (Complex.I * (ψ τ : ℂ))) =
        (Icc (-M) M).indicator (fun τ : ℝ => f τ * Complex.exp (Complex.I * (ψ τ : ℂ))) := by
      ext τ; simp only [Set.indicator, mem_Icc]
      split_ifs with h
      · rfl
      · simp only [not_and_or, not_le] at h
        have hge : M ≤ |τ| := by
          rcases h with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        simp [hsupp τ hge]
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc, ← hind]
  rw [hsupp_eq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  let g : ℝ → ℂ := fun t => f t / ((deriv ψ t : ℝ) : ℂ)
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := contDiff_one_deriv_of_two hψ
  have hg_deriv : ∀ τ ∈ uIcc (-M) M, HasDerivAt g (deriv g τ) τ := by
    intro τ hτ
    rw [uIcc_of_le (by linarith)] at hτ
    have h1 : DifferentiableAt ℝ f τ := (hf.differentiable (by decide)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun t : ℝ => ((deriv ψ t : ℝ) : ℂ)) τ :=
      Complex.ofRealCLM.differentiableAt.comp τ (hψ1.differentiable (by decide)).differentiableAt
    exact (h1.div h2 (by exact_mod_cast hψ' τ hτ)).hasDerivAt
  have he_deriv : ∀ τ ∈ uIcc (-M) M,
      HasDerivAt (fun t : ℝ => -Complex.I * Complex.exp (Complex.I * (ψ t : ℂ)))
        (((deriv ψ τ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ τ : ℂ))) τ := by
    intro τ _
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * (ψ t : ℂ)) (Complex.I * ((deriv ψ τ : ℝ) : ℂ)) τ :=
      ((hψ.differentiable (by decide)).differentiableAt.hasDerivAt.ofReal_comp).const_mul Complex.I
    have h2 := ((Complex.hasDerivAt_exp _).comp τ h1).const_mul (-Complex.I)
    refine h2.congr_deriv ?_
    calc -Complex.I * (Complex.exp (Complex.I * (ψ τ : ℂ)) * (Complex.I * ((deriv ψ τ : ℝ) : ℂ)))
        = -(Complex.I * Complex.I) * ((deriv ψ τ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ τ : ℂ)) := by ring
      _ = ((deriv ψ τ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ τ : ℂ)) := by rw [Complex.I_mul_I]; ring
  have hg'_int : IntervalIntegrable (deriv g) volume (-M) M := by
    have hcont : ContinuousOn (deriv g) (Icc (-M) M) := by
      have hcd_g : ContDiffOn ℝ 1 g (Icc (-M) M) := by
        have hgeq : g = fun t => f t * ((deriv ψ t : ℝ) : ℂ)⁻¹ := funext fun t => div_eq_mul_inv _ _
        rw [hgeq]
        refine hf.contDiffOn.mul (((Complex.ofRealCLM.contDiff.of_le (le_top : (1 : WithTop ℕ∞) ≤ ⊤)).comp hψ1).contDiffOn.inv ?_)
        intro τ hτ; show ((deriv ψ τ : ℝ) : ℂ) ≠ 0; exact_mod_cast hψ' τ hτ
      have heq : EqOn (deriv g) (derivWithin g (Icc (-M) M)) (Icc (-M) M) := fun τ hτ => by
        exact ((hg_deriv τ (by rwa [uIcc_of_le (by linarith)])).hasDerivWithinAt.derivWithin
          (uniqueDiffOn_Icc (by linarith) τ hτ)).symm
      exact (hcd_g.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl).congr heq
    exact hcont.intervalIntegrable_of_Icc (by linarith)
  have he'_int : IntervalIntegrable (fun τ : ℝ => ((deriv ψ τ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ τ : ℂ)))
      volume (-M) M := by
    have hcont : Continuous fun τ : ℝ => ((deriv ψ τ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ τ : ℂ)) :=
      (Complex.continuous_ofReal.comp (hψ.continuous_deriv (by decide))).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hψ.continuous)))
    exact hcont.intervalIntegrable (-M) M
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg_deriv he_deriv hg'_int he'_int
  have hlhs_congr : ∫ τ in (-M)..M, f τ * Complex.exp (Complex.I * (ψ τ : ℂ)) =
      ∫ τ in (-M)..M, g τ * (((deriv ψ τ : ℝ) : ℂ) * Complex.exp (Complex.I * (ψ τ : ℂ))) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le (by linarith)] at hτ
    have hne : ((deriv ψ τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hψ' τ hτ
    dsimp only [g]; field_simp [hne]
  rw [hlhs_congr, hparts]
  have hbd_M : g M = 0 := by simp [g, hsupp M (by rw [abs_of_pos hM])]
  have hbd_nM : g (-M) = 0 := by simp [g, hsupp (-M) (by rw [abs_neg, abs_of_pos hM])]
  rw [hbd_M, hbd_nM, zero_mul, zero_mul, sub_self, zero_sub]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun τ _ => by ring

/-- Two-fold IBP for a `C²` function `f` supported in `[-M, M]` against `e^{i ω τ}` (`ω ≠ 0`). -/
lemma ibp_two_linear {M ω : ℝ} (hM : 0 < M) (hω : ω ≠ 0) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ τ : ℝ, M ≤ |τ| → f τ = 0) :
    ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ ≤
      ω ^ (-(2 : ℝ)) * ∫ τ in Icc (-M) M, ‖iteratedDeriv 2 f τ‖ := by
  have hf1 : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hf).2.2
  have hsupp_f' : ∀ τ : ℝ, M ≤ |τ| → deriv f τ = 0 := fun τ hτ => by
    have hcont : Continuous (deriv f) := hf.continuous_deriv (by decide)
    by_cases hgt : M < |τ|
    · have hev : f =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hgt] with s hs
        exact hsupp s hs.le
      rw [hev.deriv_eq, deriv_const]
    · have heq : |τ| = M := le_antisymm (not_lt.mp hgt) hτ
      rcases eq_or_eq_neg_of_abs_eq heq with rfl | hneg
      · have hlim : Tendsto (deriv f) (𝓝[>] τ) (𝓝 (deriv f τ)) :=
          hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have hzero : Tendsto (deriv f) (𝓝[>] τ) (𝓝 0) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [self_mem_nhdsWithin] with s (hs : τ < s)
            have hs' : τ < |s| := by rw [abs_of_pos (lt_trans hM hs)]; exact hs
            have hev : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := by
              filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs'] with u hu
              exact hsupp u hu.le
            exact (hev.deriv_eq.trans (deriv_const s (0 : ℂ))).symm)
        exact tendsto_nhds_unique hlim hzero
      · subst hneg
        have hlim : Tendsto (deriv f) (𝓝[<] (-M)) (𝓝 (deriv f (-M))) :=
          hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have hzero : Tendsto (deriv f) (𝓝[<] (-M)) (𝓝 0) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [self_mem_nhdsWithin] with s (hs : s < -M)
            have hs' : M < |s| := by rw [abs_of_neg (by linarith)]; linarith
            have hev : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := by
              filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs'] with u hu
              exact hsupp u hu.le
            exact (hev.deriv_eq.trans (deriv_const s (0 : ℂ))).symm)
        exact tendsto_nhds_unique hlim hzero
  have hψ : ContDiff ℝ 2 (fun t : ℝ => ω * t) := contDiff_const.mul contDiff_id
  have hψ' : ∀ τ : ℝ, deriv (fun t : ℝ => ω * t) τ = ω := fun τ => by
    have := ((hasDerivAt_id τ).const_mul ω).deriv
    simpa using this
  have hstep1 := ibp_one_phase hM (hf.of_le (by decide)) hψ hsupp (fun τ _ => by rw [hψ']; exact hω)
  have hstep2 := ibp_one_phase hM hf1 hψ hsupp_f' (fun τ _ => by rw [hψ']; exact hω)
  have h1_simp : ∀ τ : ℝ, deriv (fun t : ℝ => f t / ((deriv (fun s => ω * s) t : ℝ) : ℂ)) τ =
      deriv f τ / (ω : ℂ) := fun τ => by
    simp_rw [hψ']; exact deriv_div_const (ω : ℂ)
  have h2_simp : ∀ τ : ℝ, deriv (fun t : ℝ => deriv f t / ((deriv (fun s => ω * s) t : ℝ) : ℂ)) τ =
      iteratedDeriv 2 f τ / (ω : ℂ) := fun τ => by
    simp_rw [hψ']; rw [deriv_div_const (ω : ℂ), iteratedDeriv_succ, iteratedDeriv_one]
  simp_rw [h1_simp] at hstep1
  simp_rw [h2_simp] at hstep2
  have hstep1' : ∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
      (Complex.I / (ω : ℂ)) * ∫ τ : ℝ, deriv f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
    rw [hstep1]
    have hdiv : ∫ τ in Icc (-M) M, deriv f τ / (ω : ℂ) * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
        (ω : ℂ)⁻¹ * ∫ τ in Icc (-M) M, deriv f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
      rw [← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Icc fun τ _ => by ring
    rw [hdiv]
    have hsupp_int : ∫ τ in Icc (-M) M, deriv f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
        ∫ τ : ℝ, deriv f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
      have hind : (fun τ : ℝ => deriv f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) =
          (Icc (-M) M).indicator (fun τ : ℝ => deriv f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) := by
        ext τ; simp only [Set.indicator, mem_Icc]
        split_ifs with h
        · rfl
        · simp only [not_and_or, not_le] at h
          have hge : M ≤ |τ| := by
            rcases h with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          simp [hsupp_f' τ hge]
      conv_rhs => rw [hind, integral_indicator measurableSet_Icc]
    rw [hsupp_int]; ring
  rw [hstep1', hstep2]
  have hdiv2 : ∫ τ in Icc (-M) M, iteratedDeriv 2 f τ / (ω : ℂ) * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
      (ω : ℂ)⁻¹ * ∫ τ in Icc (-M) M, iteratedDeriv 2 f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
    rw [← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Icc fun τ _ => by ring
  rw [hdiv2]
  have hnorm_pref : ‖Complex.I / (ω : ℂ) * (Complex.I * ((ω : ℂ)⁻¹ * ∫ τ in Icc (-M) M,
      iteratedDeriv 2 f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))))‖ =
      |ω|⁻¹ ^ 2 * ‖∫ τ in Icc (-M) M, iteratedDeriv 2 f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ := by
    simp only [norm_mul, norm_div, norm_inv, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_div, one_mul]
    ring
  rw [hnorm_pref]
  have hpow : |ω|⁻¹ ^ 2 = ω ^ (-(2 : ℝ)) := by
    rw [rpow_neg_two_eq, inv_pow, sq_abs]
  rw [hpow]
  refine mul_le_mul_of_nonneg_left ?_ (by rw [rpow_neg_two_eq]; positivity)
  calc ‖∫ τ in Icc (-M) M, iteratedDeriv 2 f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖
      ≤ ∫ τ in Icc (-M) M, ‖iteratedDeriv 2 f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ τ in Icc (-M) M, ‖iteratedDeriv 2 f τ‖ := by
        refine setIntegral_congr_fun measurableSet_Icc fun τ _ => ?_
        rw [norm_mul, show Complex.I * ((ω * τ : ℝ) : ℂ) = ((ω * τ : ℝ) : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ### Exact smooth-cutoff Fourier inversion of `(lam + iτ)^{-1/2}` -/

/-- Laplace transform of `t^{-1/2}` on `Re z > 0`:
`∫₀^∞ t^{-1/2} e^{-z t} dt = √π z^{-1/2}`. -/
lemma integral_rpow_neg_half_mul_exp_neg {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-z * (t : ℂ)) =
      (√π : ℂ) * z ^ (-(1 / 2 : ℂ)) := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  let F : ℂ → ℂ := fun w => ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-w * (t : ℂ))
  let G : ℂ → ℂ := fun w => (√π : ℂ) * w ^ (-(1 / 2 : ℂ))
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hF_diff : DifferentiableOn ℂ F U := by
    intro w₀ hw₀
    set r : ℝ := w₀.re / 2 with hr_def
    have hr : 0 < r := half_pos hw₀
    have hball_re : ∀ w ∈ Metric.ball w₀ r, r ≤ w.re := fun w hw => by
      have h1 := Complex.abs_re_le_norm (w - w₀)
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h2 := (abs_le.mp (h1.trans hw.le)).1
      simp only [Complex.sub_re] at h2; linarith
    have hint_pow : ∀ (p : ℝ), -1 < p → ∀ {a : ℝ}, 0 < a →
        IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-a * t)) (Ioi (0 : ℝ)) := by
      intro p hp a ha
      have hG := Real.GammaIntegral_convergent (by linarith : 0 < p + 1)
      have hcomp := (integrableOn_Ioi_comp_mul_left_iff
        (fun t : ℝ => Real.exp (-t) * t ^ p) 0 ha).mpr (by
          simpa only [mul_zero] using hG.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi)
      refine (hcomp.const_mul (a ^ (-p))).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [Real.mul_rpow ha.le ht0.le, show -(a * t) = -a * t by ring]
      have hcancel : a ^ (-p) * a ^ p = 1 := by rw [← Real.rpow_add ha]; simp
      calc a ^ (-p) * (Real.exp (-a * t) * (a ^ p * t ^ p))
          = (a ^ (-p) * a ^ p) * (t ^ p * Real.exp (-a * t)) := by ring
        _ = t ^ p * Real.exp (-a * t) := by rw [hcancel, one_mul]
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (w : ℂ) (t : ℝ) => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-w * (t : ℂ)))
      (F' := fun (w : ℂ) (t : ℝ) => -(((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-w * (t : ℂ))))
      (Metric.ball_mem_nhds w₀ hr)
      (Eventually.of_forall fun w =>
        ((Complex.continuous_ofReal.comp_continuousOn
          (ContinuousOn.rpow_const continuousOn_id (fun t (ht : t ∈ Ioi 0) => Or.inl ht.ne'))).mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).aestronglyMeasurable
          measurableSet_Ioi)
      (by
        refine (hint_pow (-(1 / 2)) (by norm_num) hw₀).mono' ?_ ?_
        · exact ((Complex.continuous_ofReal.comp_continuousOn
            (ContinuousOn.rpow_const continuousOn_id (fun t (ht : t ∈ Ioi 0) => Or.inl ht.ne'))).mul
            (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).aestronglyMeasurable
            measurableSet_Ioi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := ht
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos ht0 _).le,
            Complex.norm_exp, show (-w₀ * (t : ℂ)).re = -w₀.re * t by simp])
      (by
        exact (((Complex.continuous_ofReal.comp_continuousOn
          (ContinuousOn.rpow_const continuousOn_id (fun t (ht : t ∈ Ioi 0) => Or.inl ht.ne'))).mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn).neg).aestronglyMeasurable
          measurableSet_Ioi)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
        have ht0 : 0 < t := ht
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos ht0 _).le,
          Complex.norm_exp, show (-w * (t : ℂ)).re = -w.re * t by simp]
        gcongr; nlinarith [hball_re w hw, ht0])
      (hint_pow (1 / 2) (by norm_num) hr)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w _
        have ht0 : 0 < t := ht
        have h1 : HasDerivAt (fun u : ℂ => -u * (t : ℂ)) (-(t : ℂ)) w := by
          simpa using (hasDerivAt_id w).neg.mul_const (t : ℂ)
        have h2 := ((Complex.hasDerivAt_exp _).comp w h1).const_mul ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        refine h2.congr_deriv ?_
        have htpow : ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (t : ℂ) = ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]; congr 1
          calc t ^ (-(1 / 2 : ℝ)) * t = t ^ (-(1 / 2 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = t ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add ht0]; norm_num
        calc ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.exp (-w * (t : ℂ)) * -(t : ℂ))
            = -((((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (t : ℂ)) * Complex.exp (-w * (t : ℂ))) := by ring
          _ = -(((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-w * (t : ℂ))) := by rw [htpow])
    exact hderiv.2.differentiableAt.differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ G U := fun w hw =>
    ((differentiableAt_id.cpow_const (Or.inl hw)).const_mul _).differentiableWithinAt
  have hF_an : AnalyticOnNhd ℂ F U := hF_diff.analyticOnNhd hU_open
  have hG_an : AnalyticOnNhd ℂ G U := hG_diff.analyticOnNhd hU_open
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = G w := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨ε, hε, hsub⟩ := hs
    let x : ℝ := 1 + min (ε / 2) (1 / 2)
    have hx_pos : 0 < x := by positivity
    have hx_ne : (x : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp [x] at this
      have : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
      linarith
    have hx_mem : (x : ℂ) ∈ s := by
      apply hsub
      refine ⟨?_, hx_ne⟩
      rw [Metric.mem_ball, dist_eq_norm, show (x : ℂ) - 1 = ((min (ε / 2) (1 / 2) : ℝ) : ℂ) by
        simp [x], Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith [min_le_left (ε / 2) (1 / 2)]
    refine ⟨(x : ℂ), hx_mem, ?_⟩
    dsimp [F, G]
    have hreal : ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(x : ℂ) * (t : ℂ)) =
        ((∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        simp [Complex.ofReal_exp, mul_comm]
    have hG_eq : ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (-(1 / 2 : ℝ)) = √π := by
      have h := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 1 / 2)
      rw [Real.Gamma_one_half_eq] at h
      rw [h]; refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by norm_num
    have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (-(1 / 2 : ℝ)) = √π / √x := by
      have hcov := MeasureTheory.integral_comp_mul_left_Ioi
        (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) (0 : ℝ) hx_pos
      simp only [mul_zero, smul_eq_mul, hG_eq] at hcov
      have hstep : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * t ^ (-(1 / 2 : ℝ)) =
          x ^ (1 / 2 : ℝ) * ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * (x * t) ^ (-(1 / 2 : ℝ)) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        rw [Real.mul_rpow hx_pos.le ht0.le, show -x * t = -(x * t) by ring]
        have hcancel : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hx_pos]; norm_num
        calc Real.exp (-(x * t)) * t ^ (-(1 / 2 : ℝ))
            = (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ))) * (Real.exp (-(x * t)) * t ^ (-(1 / 2 : ℝ))) := by
              rw [hcancel, one_mul]
          _ = _ := by ring
      rw [hstep, hcov]
      have hpow : x ^ (1 / 2 : ℝ) * x⁻¹ = (√x)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hx_pos, Real.sqrt_eq_rpow, ← Real.rpow_neg hx_pos.le]; norm_num
      calc x ^ (1 / 2 : ℝ) * (x⁻¹ * √π) = (x ^ (1 / 2 : ℝ) * x⁻¹) * √π := by ring
        _ = (√x)⁻¹ * √π := by rw [hpow]
        _ = √π / √x := by rw [div_eq_mul_inv, mul_comm]
    have hx_cpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = (((√x)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx_pos.ne'), ← Complex.ofReal_log hx_pos.le,
        show ((Real.log x : ℝ) : ℂ) * -(1 / 2 : ℂ) = ((-(Real.log x / 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      congr 1
      rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]; congr 2; ring
    rw [hreal, hval, hx_cpow]; push_cast; ring
  exact hF_an.eqOn_of_preconnected_of_frequently_eq hG_an hU_conn (by simp [U] : (1 : ℂ) ∈ U) hfreq hz

/-- Step 1 of `regSqrt_cutoff_fourier`: uniform difference bound between cutoff scales `R ≥ 2 ς` and `ς`. -/
private lemma regSqrt_diff_cutoff_bound :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ {lam ω ς R : ℝ}, 0 < lam → 0 < ω → 0 < ς → 2 * ς ≤ R →
      ‖((1 / (2 * π) : ℝ) : ℂ) *
          (∫ τ : ℝ, ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * regSqrt lam τ *
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) -
        ((1 / (2 * π) : ℝ) : ℂ) *
          (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt lam τ *
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)))‖ ≤
        C0 * ω ^ (-(2 : ℝ)) * ς ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Bχ, hBχ_pos, hBχ⟩ := smoothCutoff0_deriv_bounds
  refine ⟨20 * (1 + Bχ), by positivity, fun {lam ω ς R} hlam hω hς hR => ?_⟩
  have hR_pos : 0 < R := by linarith
  let ψR : ℝ → ℂ := fun τ => (((smoothCutoff0 (τ / R) - smoothCutoff0 (τ / ς)) : ℝ) : ℂ)
  let f : ℝ → ℂ := fun τ => ψR τ * regSqrt lam τ
  have hψR_cd : ContDiff ℝ 2 ψR :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const R)).sub
        ((contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const ς)))
  have hf_cd : ContDiff ℝ 2 f := hψR_cd.mul (contDiff_regSqrt hlam)
  have hf_supp : ∀ τ : ℝ, R ≤ |τ| → f τ = 0 := fun τ hτ => by
    have h1 : 1 ≤ |τ / R| := by rw [abs_div, abs_of_pos hR_pos, one_le_div hR_pos]; exact hτ
    have h2 : 1 ≤ |τ / ς| := by rw [abs_div, abs_of_pos hς, one_le_div hς]; linarith
    simp [f, ψR, smoothCutoff0_eq_zero h1, smoothCutoff0_eq_zero h2]
  have hint_scale : ∀ s : ℝ, 0 < s →
      Integrable (fun τ : ℝ => ((smoothCutoff0 (τ / s) : ℝ) : ℂ) * regSqrt lam τ *
        Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) := fun s hs => by
    have hcont : Continuous (fun τ : ℝ => ((smoothCutoff0 (τ / s) : ℝ) : ℂ) * regSqrt lam τ *
        Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) :=
      ((Complex.continuous_ofReal.comp (contDiff_smoothCutoff0.continuous.comp (continuous_id.div_const s))).mul
        (contDiff_regSqrt hlam).continuous).mul (by fun_prop)
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -s) (b := s)) fun τ hτ => ?_
    rw [Function.mem_support] at hτ
    by_contra hnot
    have hge : s ≤ |τ| := by
      simp only [mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact hτ (by rw [smoothCutoff0_eq_zero (by rw [abs_div, abs_of_pos hs, one_le_div hs]; exact hge),
      Complex.ofReal_zero, zero_mul, zero_mul])
  have hsub_eq : ((1 / (2 * π) : ℝ) : ℂ) * (∫ τ : ℝ, ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * regSqrt lam τ *
        Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) -
      ((1 / (2 * π) : ℝ) : ℂ) * (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt lam τ *
        Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) := by
    rw [← mul_sub, ← integral_sub (hint_scale R hR_pos) (hint_scale ς hς)]
    congr 1; refine integral_congr_ae (Eventually.of_forall fun τ => by dsimp [f, ψR]; push_cast; ring)
  rw [hsub_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hibp := ibp_two_linear hR_pos hω.ne' hf_cd hf_supp
  have hleib : ∀ τ : ℝ, ‖iteratedDeriv 2 f τ‖ ≤
      ‖iteratedDeriv 2 ψR τ‖ * ‖regSqrt lam τ‖ +
      2 * ‖deriv ψR τ‖ * ‖deriv (regSqrt lam) τ‖ +
      ‖ψR τ‖ * ‖iteratedDeriv 2 (regSqrt lam) τ‖ := fun τ => by
    have h := iteratedDeriv_fun_mul (n := 2) (hψR_cd.contDiffAt) ((contDiff_regSqrt hlam).contDiffAt) (x := τ)
    dsimp only [f]
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one,
      Nat.cast_ofNat, one_mul, iteratedDeriv_zero, iteratedDeriv_one, Nat.sub_zero, Nat.sub_self,
      show 2 - 1 = 1 by rfl]
    calc ‖ψR τ * iteratedDeriv 2 (regSqrt lam) τ + 2 * deriv ψR τ * deriv (regSqrt lam) τ +
          iteratedDeriv 2 ψR τ * regSqrt lam τ‖
        ≤ ‖ψR τ * iteratedDeriv 2 (regSqrt lam) τ + 2 * deriv ψR τ * deriv (regSqrt lam) τ‖ +
          ‖iteratedDeriv 2 ψR τ * regSqrt lam τ‖ := norm_add_le _ _
      _ ≤ (‖ψR τ * iteratedDeriv 2 (regSqrt lam) τ‖ + ‖2 * deriv ψR τ * deriv (regSqrt lam) τ‖) +
          ‖iteratedDeriv 2 ψR τ * regSqrt lam τ‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = ‖iteratedDeriv 2 ψR τ‖ * ‖regSqrt lam τ‖ +
          2 * ‖deriv ψR τ‖ * ‖deriv (regSqrt lam) τ‖ +
          ‖ψR τ‖ * ‖iteratedDeriv 2 (regSqrt lam) τ‖ := by
          simp only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; ring
  let G0 : ℝ → ℝ := fun τ => if ς / 2 ≤ |τ| then 3 * |τ| ^ (-(5 / 2 : ℝ)) else 0
  let G1 : ℝ → ℝ := fun τ =>
    (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then 4 * Bχ * ς⁻¹ * (ς / 2) ^ (-(3 / 2 : ℝ)) else 0) +
    (if R / 2 ≤ |τ| ∧ |τ| ≤ R then 4 * Bχ * R⁻¹ * (R / 2) ^ (-(3 / 2 : ℝ)) else 0)
  let G2 : ℝ → ℝ := fun τ =>
    (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) * (ς / 2) ^ (-(1 / 2 : ℝ)) else 0) +
    (if R / 2 ≤ |τ| ∧ |τ| ≤ R then Bχ * R ^ (-(2 : ℝ)) * (R / 2) ^ (-(1 / 2 : ℝ)) else 0)
  have hψ_pt : ∀ τ : ℝ, ‖ψR τ‖ ≤ if ς / 2 ≤ |τ| then 1 else 0 := fun τ => by
    dsimp [ψR]; rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_le]; constructor <;> linarith [smoothCutoff0_nonneg (τ / R), smoothCutoff0_le_one (τ / R),
        smoothCutoff0_nonneg (τ / ς), smoothCutoff0_le_one (τ / ς)]
    · push Not at h
      have h1 : |τ / ς| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hς, div_le_iff₀ hς]; linarith
      have h2 : |τ / R| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hR_pos, div_le_iff₀ hR_pos]; linarith
      rw [smoothCutoff0_eq_one h1, smoothCutoff0_eq_one h2, sub_self, abs_zero]
  have hd1_scale : ∀ (s : ℝ), 0 < s → ∀ τ : ℝ,
      deriv (fun t : ℝ => smoothCutoff0 (t / s)) τ = s⁻¹ * deriv smoothCutoff0 (τ / s) := fun s hs τ => by
    have h := ((contDiff_smoothCutoff0.differentiable (by decide)).differentiableAt.hasDerivAt).comp τ
      ((hasDerivAt_id τ).div_const s)
    rw [show (fun t : ℝ => smoothCutoff0 (t / s)) = smoothCutoff0 ∘ (fun x : ℝ => id x / s) by rfl, h.deriv]
    simp [id_eq]; ring
  have hd2_scale : ∀ (s : ℝ), 0 < s → ∀ τ : ℝ,
      iteratedDeriv 2 (fun t : ℝ => smoothCutoff0 (t / s)) τ =
        s ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / s) := fun s hs τ => by
    rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
    have heq : deriv (fun t : ℝ => smoothCutoff0 (t / s)) = fun t => s⁻¹ * deriv smoothCutoff0 (t / s) :=
      funext (hd1_scale s hs)
    rw [heq]
    have hcd1 : ContDiff ℝ 1 (deriv smoothCutoff0) :=
      contDiff_one_deriv_of_two (contDiff_smoothCutoff0.of_le (by simp))
    have h := ((hcd1.differentiable (by decide)).differentiableAt.hasDerivAt).comp τ ((hasDerivAt_id τ).div_const s)
    rw [show (fun t : ℝ => s⁻¹ * deriv smoothCutoff0 (t / s)) = fun t => s⁻¹ * (deriv smoothCutoff0 ∘ (fun x => id x / s)) t by rfl,
      (h.const_mul s⁻¹).deriv]
    have hpow : s⁻¹ * (1 / s) = s ^ (-(2 : ℝ)) := by
      rw [rpow_neg_two_eq, one_div, sq, mul_inv]
    calc s⁻¹ * (deriv (deriv smoothCutoff0) (id τ / s) * (1 / s))
        = (s⁻¹ * (1 / s)) * deriv (deriv smoothCutoff0) (τ / s) := by simp [id_eq]; ring
      _ = s ^ (-(2 : ℝ)) * deriv (deriv smoothCutoff0) (τ / s) := by rw [hpow]
  have hψ1_pt : ∀ τ : ℝ, ‖deriv ψR τ‖ ≤
      (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) +
      (if R / 2 ≤ |τ| ∧ |τ| ≤ R then Bχ * R⁻¹ else 0) := fun τ => by
    have hd : deriv ψR τ = ((deriv (fun t => smoothCutoff0 (t / R)) τ -
        deriv (fun t => smoothCutoff0 (t / ς)) τ : ℝ) : ℂ) := by
      have h1 : HasDerivAt (fun t => smoothCutoff0 (t / R)) (deriv (fun t => smoothCutoff0 (t / R)) τ) τ :=
        ((contDiff_smoothCutoff0.differentiable (by decide)).comp (differentiable_id.div_const R)).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun t => smoothCutoff0 (t / ς)) (deriv (fun t => smoothCutoff0 (t / ς)) τ) τ :=
        ((contDiff_smoothCutoff0.differentiable (by decide)).comp (differentiable_id.div_const ς)).differentiableAt.hasDerivAt
      exact (h1.sub h2).ofReal_comp.deriv
    rw [hd, Complex.norm_real, Real.norm_eq_abs, hd1_scale R hR_pos, hd1_scale ς hς]
    have hbound_s : ∀ (s : ℝ), 0 < s → |s⁻¹ * deriv smoothCutoff0 (τ / s)| ≤
        if s / 2 ≤ |τ| ∧ |τ| ≤ s then Bχ * s⁻¹ else 0 := fun s hs => by
      split_ifs with h
      · rw [abs_mul, abs_of_pos (inv_pos.mpr hs), mul_comm]
        exact mul_le_mul_of_nonneg_right (hBχ (τ / s)).1 (inv_nonneg.mpr hs.le)
      · push Not at h
        by_cases hlt : |τ| < s / 2
        · have h1 : |τ / s| < 1 / 2 := by rw [abs_div, abs_of_pos hs, div_lt_iff₀ hs]; linarith
          rw [((hBχ (τ / s)).2.2.1 h1).1, mul_zero, abs_zero]
        · have hgt : s < |τ| := h (not_lt.mp hlt)
          have h1 : 1 < |τ / s| := by rw [abs_div, abs_of_pos hs, one_lt_div hs]; exact hgt
          rw [((hBχ (τ / s)).2.2.2 h1).1, mul_zero, abs_zero]
    calc |R⁻¹ * deriv smoothCutoff0 (τ / R) - ς⁻¹ * deriv smoothCutoff0 (τ / ς)|
        ≤ |R⁻¹ * deriv smoothCutoff0 (τ / R)| + |ς⁻¹ * deriv smoothCutoff0 (τ / ς)| := abs_sub _ _
      _ ≤ (if R / 2 ≤ |τ| ∧ |τ| ≤ R then Bχ * R⁻¹ else 0) +
          (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς⁻¹ else 0) :=
          add_le_add (hbound_s R hR_pos) (hbound_s ς hς)
      _ = _ := add_comm _ _
  have hψ2_pt : ∀ τ : ℝ, ‖iteratedDeriv 2 ψR τ‖ ≤
      (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) else 0) +
      (if R / 2 ≤ |τ| ∧ |τ| ≤ R then Bχ * R ^ (-(2 : ℝ)) else 0) := fun τ => by
    have hcdR : ContDiff ℝ 2 (fun t => smoothCutoff0 (t / R)) :=
      (contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const R)
    have hcdς : ContDiff ℝ 2 (fun t => smoothCutoff0 (t / ς)) :=
      (contDiff_smoothCutoff0.of_le (by simp)).comp (contDiff_id.div_const ς)
    have hd : iteratedDeriv 2 ψR τ = ((iteratedDeriv 2 (fun t => smoothCutoff0 (t / R)) τ -
        iteratedDeriv 2 (fun t => smoothCutoff0 (t / ς)) τ : ℝ) : ℂ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
        iteratedDeriv_succ, iteratedDeriv_one]
      have h1 : deriv ψR = fun t => ((deriv (fun u => smoothCutoff0 (u / R)) t -
          deriv (fun u => smoothCutoff0 (u / ς)) t : ℝ) : ℂ) := funext fun t =>
        (((hcdR.differentiable (by decide)).differentiableAt.hasDerivAt.sub
          (hcdς.differentiable (by decide)).differentiableAt.hasDerivAt).ofReal_comp).deriv
      rw [h1]
      exact ((((contDiff_one_deriv_of_two hcdR).differentiable (by decide)).differentiableAt.hasDerivAt.sub
        ((contDiff_one_deriv_of_two hcdς).differentiable (by decide)).differentiableAt.hasDerivAt).ofReal_comp).deriv
    rw [hd, Complex.norm_real, Real.norm_eq_abs, hd2_scale R hR_pos, hd2_scale ς hς]
    have hbound_s : ∀ (s : ℝ), 0 < s → |s ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / s)| ≤
        if s / 2 ≤ |τ| ∧ |τ| ≤ s then Bχ * s ^ (-(2 : ℝ)) else 0 := fun s hs => by
      split_ifs with h
      · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hBχ (τ / s)).2.1 (by positivity)
      · push Not at h
        by_cases hlt : |τ| < s / 2
        · have h1 : |τ / s| < 1 / 2 := by rw [abs_div, abs_of_pos hs, div_lt_iff₀ hs]; linarith
          rw [((hBχ (τ / s)).2.2.1 h1).2, mul_zero, abs_zero]
        · have hgt : s < |τ| := h (not_lt.mp hlt)
          have h1 : 1 < |τ / s| := by rw [abs_div, abs_of_pos hs, one_lt_div hs]; exact hgt
          rw [((hBχ (τ / s)).2.2.2 h1).2, mul_zero, abs_zero]
    calc |R ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / R) -
          ς ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / ς)|
        ≤ |R ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / R)| +
          |ς ^ (-(2 : ℝ)) * iteratedDeriv 2 smoothCutoff0 (τ / ς)| := abs_sub _ _
      _ ≤ (if R / 2 ≤ |τ| ∧ |τ| ≤ R then Bχ * R ^ (-(2 : ℝ)) else 0) +
          (if ς / 2 ≤ |τ| ∧ |τ| ≤ ς then Bχ * ς ^ (-(2 : ℝ)) else 0) :=
          add_le_add (hbound_s R hR_pos) (hbound_s ς hς)
      _ = _ := add_comm _ _
  have hpt : ∀ τ : ℝ, ‖iteratedDeriv 2 f τ‖ ≤ G2 τ + G1 τ + G0 τ := fun τ => by
    refine (hleib τ).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · refine (mul_le_mul_of_nonneg_right (hψ2_pt τ) (norm_nonneg _)).trans ?_
      rw [add_mul]
      refine add_le_add ?_ ?_
      · split_ifs with h
        · have hτ0 : τ ≠ 0 := by intro h0; subst h0; simp at h; linarith
          calc Bχ * ς ^ (-(2 : ℝ)) * ‖regSqrt lam τ‖
              ≤ Bχ * ς ^ (-(2 : ℝ)) * |τ| ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (norm_regSqrt_le_abs_rpow hlam hτ0) (by positivity)
            _ ≤ Bχ * ς ^ (-(2 : ℝ)) * (ς / 2) ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) h.1 (by norm_num)) (by positivity)
        · simp
      · split_ifs with h
        · have hτ0 : τ ≠ 0 := by intro h0; subst h0; simp at h; linarith
          calc Bχ * R ^ (-(2 : ℝ)) * ‖regSqrt lam τ‖
              ≤ Bχ * R ^ (-(2 : ℝ)) * |τ| ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (norm_regSqrt_le_abs_rpow hlam hτ0) (by positivity)
            _ ≤ Bχ * R ^ (-(2 : ℝ)) * (R / 2) ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) h.1 (by norm_num)) (by positivity)
        · simp
    · have h1 := mul_le_mul_of_nonneg_left (hψ1_pt τ) (by norm_num : (0 : ℝ) ≤ 2)
      refine (mul_le_mul h1 (norm_deriv_regSqrt_le hlam τ) (norm_nonneg _) (by positivity)).trans ?_
      rw [mul_add, add_mul]
      refine add_le_add ?_ ?_
      · split_ifs with h
        · have hpow : (lam + |τ|) ^ (-(3 / 2 : ℝ)) ≤ (ς / 2) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
          calc 2 * (Bχ * ς⁻¹) * (2 * (lam + |τ|) ^ (-(3 / 2 : ℝ)))
              = 4 * Bχ * ς⁻¹ * (lam + |τ|) ^ (-(3 / 2 : ℝ)) := by ring
            _ ≤ 4 * Bχ * ς⁻¹ * (ς / 2) ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hpow (by positivity)
        · simp
      · split_ifs with h
        · have hpow : (lam + |τ|) ^ (-(3 / 2 : ℝ)) ≤ (R / 2) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
          calc 2 * (Bχ * R⁻¹) * (2 * (lam + |τ|) ^ (-(3 / 2 : ℝ)))
              = 4 * Bχ * R⁻¹ * (lam + |τ|) ^ (-(3 / 2 : ℝ)) := by ring
            _ ≤ 4 * Bχ * R⁻¹ * (R / 2) ^ (-(3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hpow (by positivity)
        · simp
    · refine (mul_le_mul (hψ_pt τ) (norm_iteratedDeriv2_regSqrt_le hlam τ) (norm_nonneg _)
        (by split_ifs <;> norm_num)).trans ?_
      dsimp [G0]; split_ifs with h
      · rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)) (by norm_num)
      · simp
  have hInt_G0 : Integrable G0 ∧ ∫ τ : ℝ, G0 τ = 4 * (ς / 2) ^ (-(3 / 2 : ℝ)) := by
    have hpos : IntegrableOn (fun t : ℝ => 3 * t ^ (-(5 / 2 : ℝ))) (Ici (ς / 2)) :=
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) (by positivity)).congr_set_ae
        Ioi_ae_eq_Ici.symm).const_mul 3
    have hval_pos : ∫ t in Ici (ς / 2), 3 * t ^ (-(5 / 2 : ℝ)) = 2 * (ς / 2) ^ (-(3 / 2 : ℝ)) := by
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : -(5 / 2 : ℝ) < -1) (by positivity)]
      ring
    have hG0_int : Integrable G0 := by
      have heq : G0 = (Iic (-(ς / 2)) ∪ Ici (ς / 2)).indicator (fun τ => 3 * |τ| ^ (-(5 / 2 : ℝ))) := by
        ext τ; simp only [G0, Set.indicator, mem_union, mem_Iic, mem_Ici]
        by_cases h : ς / 2 ≤ |τ|
        · have h1 : τ ≤ -(ς / 2) ∨ ς / 2 ≤ τ := by
            rcases le_abs.mp h with h1 | h1
            · exact Or.inr h1
            · exact Or.inl (by linarith)
          simp [h, h1]
        · have h1 : ¬(τ ≤ -(ς / 2) ∨ ς / 2 ≤ τ) := by
            push Not; exact abs_lt.mp (not_le.mp h)
          simp [h, h1]
      rw [heq, integrable_indicator_iff (measurableSet_Iic.union measurableSet_Ici), integrableOn_union]
      refine ⟨?_, hpos.congr_fun (fun t ht => by rw [abs_of_pos (lt_of_lt_of_le (by positivity) ht)]) measurableSet_Ici⟩
      have hneg : IntegrableOn (fun t : ℝ => 3 * (-t) ^ (-(5 / 2 : ℝ))) (Iic (-(ς / 2))) := by
        have := hpos.comp_neg
        convert this using 1
        ext x; simp only [mem_Iic, Set.mem_neg, mem_Ici]; constructor <;> intro h <;> linarith
      exact hneg.congr_fun (fun t ht => by rw [abs_of_neg (by linarith [Set.mem_Iic.mp ht])]) measurableSet_Iic
    have hG0_val : ∫ τ : ℝ, G0 τ = 4 * (ς / 2) ^ (-(3 / 2 : ℝ)) := by
      have heven : ∫ τ : ℝ, G0 τ = 2 * ∫ t in Ioi (0 : ℝ), G0 t := by
        have h1 := integral_comp_abs (f := fun t : ℝ => if ς / 2 ≤ t then 3 * t ^ (-(5 / 2 : ℝ)) else 0)
        rw [show (fun τ : ℝ => G0 τ) = fun τ => if ς / 2 ≤ |τ| then 3 * |τ| ^ (-(5 / 2 : ℝ)) else 0 from rfl, h1]
        congr 1; refine setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp [G0, abs_of_pos ht]
      rw [heven]
      have h2 : ∫ t in Ioi (0 : ℝ), G0 t = ∫ t in Ici (ς / 2), 3 * t ^ (-(5 / 2 : ℝ)) := by
        have hcongr : ∫ t in Ioi (0 : ℝ), G0 t =
            ∫ t in Ioi (0 : ℝ), (Ici (ς / 2)).indicator (fun t => 3 * t ^ (-(5 / 2 : ℝ))) t := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          simp only [G0, Set.indicator, mem_Ici, abs_of_pos ht]
        rw [hcongr, setIntegral_indicator measurableSet_Ici,
          inter_eq_right.mpr (fun t (ht : t ∈ Ici (ς / 2)) => lt_of_lt_of_le (by positivity) ht)]
      rw [h2, hval_pos]; ring
    exact ⟨hG0_int, hG0_val⟩
  have hannulus : ∀ (s K : ℝ), 0 < s →
      Integrable (fun τ : ℝ => if s / 2 ≤ |τ| ∧ |τ| ≤ s then K else 0) ∧
      ∫ τ : ℝ, (if s / 2 ≤ |τ| ∧ |τ| ≤ s then K else 0) = s * K := by
    intro s K hs
    have hset : {τ : ℝ | s / 2 ≤ |τ| ∧ |τ| ≤ s} = Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s := by
      ext τ; simp only [mem_ofPred_eq, mem_union, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        rcases le_total 0 τ with hτ | hτ
        · rw [abs_of_nonneg hτ] at h1 h2; exact Or.inr ⟨h1, h2⟩
        · rw [abs_of_nonpos hτ] at h1 h2; exact Or.inl ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rw [abs_of_nonpos (by linarith)]; exact ⟨by linarith, by linarith⟩
        · rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
    have heq : (fun τ : ℝ => if s / 2 ≤ |τ| ∧ |τ| ≤ s then K else 0) =
        (Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s).indicator (fun _ => K) := by
      ext τ; simp only [Set.indicator]
      by_cases h : τ ∈ Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s
      · have h' : s / 2 ≤ |τ| ∧ |τ| ≤ s := by simpa [← hset] using h
        simp [h, h']
      · have h' : ¬(s / 2 ≤ |τ| ∧ |τ| ≤ s) := by simpa [← hset] using h
        simp [h, h']
    rw [heq]
    have hdisj : Disjoint (Icc (-s) (-(s / 2))) (Icc (s / 2) s) :=
      Set.disjoint_left.mpr fun τ h1 h2 => by linarith [h1.2, h2.1]
    have hint_u : Integrable ((Icc (-s) (-(s / 2)) ∪ Icc (s / 2) s).indicator (fun _ => K)) := by
      rw [integrable_indicator_iff (measurableSet_Icc.union measurableSet_Icc)]
      exact integrableOn_const (by rw [measure_union hdisj measurableSet_Icc]; simp)
    refine ⟨hint_u, ?_⟩
    rw [integral_indicator (measurableSet_Icc.union measurableSet_Icc),
      setIntegral_union hdisj measurableSet_Icc (integrableOn_const (by simp)) (integrableOn_const (by simp)),
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul,
      Measure.real, Measure.real, Real.volume_Icc, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
    ring
  have hG1_int : Integrable G1 := (hannulus ς _ hς).1.add (hannulus R _ hR_pos).1
  have hG2_int : Integrable G2 := (hannulus ς _ hς).1.add (hannulus R _ hR_pos).1
  have hG_int : Integrable (fun τ => G2 τ + G1 τ + G0 τ) := (hG2_int.add hG1_int).add hInt_G0.1
  have hf2_int : IntegrableOn (fun τ => ‖iteratedDeriv 2 f τ‖) (Icc (-R) R) :=
    ((hf_cd.continuous_iteratedDeriv 2 le_rfl).norm).continuousOn.integrableOn_compact isCompact_Icc
  have hle_R : ∫ τ in Icc (-R) R, ‖iteratedDeriv 2 f τ‖ ≤ ∫ τ : ℝ, (G2 τ + G1 τ + G0 τ) := by
    calc ∫ τ in Icc (-R) R, ‖iteratedDeriv 2 f τ‖
        ≤ ∫ τ in Icc (-R) R, (G2 τ + G1 τ + G0 τ) :=
          setIntegral_mono_on hf2_int hG_int.integrableOn measurableSet_Icc fun τ _ => hpt τ
      _ ≤ ∫ τ : ℝ, (G2 τ + G1 τ + G0 τ) :=
          setIntegral_le_integral hG_int (Eventually.of_forall fun τ => by
            dsimp [G0, G1, G2]; positivity)
  have hsum_val : ∫ τ : ℝ, (G2 τ + G1 τ + G0 τ) =
      (ς * (Bχ * ς ^ (-(2 : ℝ)) * (ς / 2) ^ (-(1 / 2 : ℝ))) +
       R * (Bχ * R ^ (-(2 : ℝ)) * (R / 2) ^ (-(1 / 2 : ℝ)))) +
      (ς * (4 * Bχ * ς⁻¹ * (ς / 2) ^ (-(3 / 2 : ℝ))) +
       R * (4 * Bχ * R⁻¹ * (R / 2) ^ (-(3 / 2 : ℝ)))) +
      4 * (ς / 2) ^ (-(3 / 2 : ℝ)) := by
    rw [integral_add (f := fun τ => G2 τ + G1 τ) (g := G0) (hG2_int.add hG1_int) hInt_G0.1,
      integral_add hG2_int hG1_int, hInt_G0.2]
    dsimp [G1, G2]
    rw [integral_add (hannulus ς _ hς).1 (hannulus R _ hR_pos).1,
      integral_add (hannulus ς _ hς).1 (hannulus R _ hR_pos).1,
      (hannulus ς _ hς).2, (hannulus R _ hR_pos).2, (hannulus ς _ hς).2, (hannulus R _ hR_pos).2]
  have h2_32 : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    have : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    norm_num at this; exact this
  have h2_12 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    norm_num at this; exact this
  have hhalf32 : ∀ (s : ℝ), 0 < s → (s / 2) ^ (-(3 / 2 : ℝ)) = 2 ^ (3 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) := fun s hs => by
    have h2i : ((2 : ℝ)⁻¹) ^ (-(3 / 2 : ℝ)) = 2 ^ (3 / 2 : ℝ) := by
      rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
    rw [div_eq_mul_inv, Real.mul_rpow hs.le (by norm_num), h2i, mul_comm]
  have hhalf12 : ∀ (s : ℝ), 0 < s → s * (s ^ (-(2 : ℝ)) * (s / 2) ^ (-(1 / 2 : ℝ))) =
      2 ^ (1 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) := fun s hs => by
    have h2i : ((2 : ℝ)⁻¹) ^ (-(1 / 2 : ℝ)) = 2 ^ (1 / 2 : ℝ) := by
      rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
    rw [div_eq_mul_inv, Real.mul_rpow hs.le (by norm_num), h2i]
    have h1 : s * (s ^ (-(2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) = s ^ (-(3 / 2 : ℝ)) := by
      calc s * (s ^ (-(2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))
          = s ^ (1 : ℝ) * (s ^ (-(2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) := by rw [Real.rpow_one]
        _ = s ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hs, ← Real.rpow_add hs]; norm_num
    calc s * (s ^ (-(2 : ℝ)) * (s ^ (-(1 / 2 : ℝ)) * 2 ^ (1 / 2 : ℝ)))
        = 2 ^ (1 / 2 : ℝ) * (s * (s ^ (-(2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))) := by ring
      _ = 2 ^ (1 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) := by rw [h1]
  have hR_le_ς : R ^ (-(3 / 2 : ℝ)) ≤ ς ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hς (by linarith) (by norm_num)
  have hf2_bd : ∫ τ in Icc (-R) R, ‖iteratedDeriv 2 f τ‖ ≤ 100 * (1 + Bχ) * ς ^ (-(3 / 2 : ℝ)) := by
    refine hle_R.trans (hsum_val ▸ ?_)
    have ht1 : ς * (Bχ * ς ^ (-(2 : ℝ)) * (ς / 2) ^ (-(1 / 2 : ℝ))) ≤ 2 * Bχ * ς ^ (-(3 / 2 : ℝ)) := by
      calc _ = Bχ * (ς * (ς ^ (-(2 : ℝ)) * (ς / 2) ^ (-(1 / 2 : ℝ)))) := by ring
        _ = Bχ * (2 ^ (1 / 2 : ℝ) * ς ^ (-(3 / 2 : ℝ))) := by rw [hhalf12 ς hς]
        _ ≤ Bχ * (2 * ς ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
    have ht2 : R * (Bχ * R ^ (-(2 : ℝ)) * (R / 2) ^ (-(1 / 2 : ℝ))) ≤ 2 * Bχ * ς ^ (-(3 / 2 : ℝ)) := by
      calc _ = Bχ * (R * (R ^ (-(2 : ℝ)) * (R / 2) ^ (-(1 / 2 : ℝ)))) := by ring
        _ = Bχ * (2 ^ (1 / 2 : ℝ) * R ^ (-(3 / 2 : ℝ))) := by rw [hhalf12 R hR_pos]
        _ ≤ Bχ * (2 * ς ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
    have ht3 : ς * (4 * Bχ * ς⁻¹ * (ς / 2) ^ (-(3 / 2 : ℝ))) ≤ 16 * Bχ * ς ^ (-(3 / 2 : ℝ)) := by
      rw [hhalf32 ς hς]
      have hinv : ς * ς⁻¹ = 1 := mul_inv_cancel₀ hς.ne'
      calc ς * (4 * Bχ * ς⁻¹ * (2 ^ (3 / 2 : ℝ) * ς ^ (-(3 / 2 : ℝ))))
          = (ς * ς⁻¹) * (4 * Bχ * 2 ^ (3 / 2 : ℝ) * ς ^ (-(3 / 2 : ℝ))) := by ring
        _ = 4 * Bχ * 2 ^ (3 / 2 : ℝ) * ς ^ (-(3 / 2 : ℝ)) := by rw [hinv, one_mul]
        _ ≤ 4 * Bχ * 4 * ς ^ (-(3 / 2 : ℝ)) := by gcongr
        _ = _ := by ring
    have ht4 : R * (4 * Bχ * R⁻¹ * (R / 2) ^ (-(3 / 2 : ℝ))) ≤ 16 * Bχ * ς ^ (-(3 / 2 : ℝ)) := by
      rw [hhalf32 R hR_pos]
      have hinv : R * R⁻¹ = 1 := mul_inv_cancel₀ hR_pos.ne'
      calc R * (4 * Bχ * R⁻¹ * (2 ^ (3 / 2 : ℝ) * R ^ (-(3 / 2 : ℝ))))
          = (R * R⁻¹) * (4 * Bχ * 2 ^ (3 / 2 : ℝ) * R ^ (-(3 / 2 : ℝ))) := by ring
        _ = 4 * Bχ * 2 ^ (3 / 2 : ℝ) * R ^ (-(3 / 2 : ℝ)) := by rw [hinv, one_mul]
        _ ≤ 4 * Bχ * 4 * ς ^ (-(3 / 2 : ℝ)) := by gcongr
        _ = _ := by ring
    have ht5 : 4 * (ς / 2) ^ (-(3 / 2 : ℝ)) ≤ 16 * ς ^ (-(3 / 2 : ℝ)) := by
      rw [hhalf32 ς hς]; nlinarith [Real.rpow_pos_of_pos hς (-(3 / 2 : ℝ))]
    nlinarith [Real.rpow_pos_of_pos hς (-(3 / 2 : ℝ))]
  have h2pi_ge : (5 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  calc 1 / (2 * π) * ‖∫ τ : ℝ, f τ * Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))‖
      ≤ 1 / (2 * π) * (ω ^ (-(2 : ℝ)) * ∫ τ in Icc (-R) R, ‖iteratedDeriv 2 f τ‖) :=
        mul_le_mul_of_nonneg_left hibp (by positivity)
    _ ≤ 1 / 5 * (ω ^ (-(2 : ℝ)) * (100 * (1 + Bχ) * ς ^ (-(3 / 2 : ℝ)))) := by
        refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left hf2_bd (by positivity)) (by positivity) (by positivity)
        exact one_div_le_one_div_of_le (by norm_num) h2pi_ge
    _ = 20 * (1 + Bχ) * ω ^ (-(2 : ℝ)) * ς ^ (-(3 / 2 : ℝ)) := by ring

/-- Inverse Fourier kernel `K(u) = (2π)⁻¹ ∫ χ₀(s) e^{i u s} ds` of `smoothCutoff0`. -/
private noncomputable def cutoffKernel (u : ℝ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ s : ℝ, ((smoothCutoff0 s : ℝ) : ℂ) * Complex.exp (Complex.I * ((u * s : ℝ) : ℂ))

private lemma cutoffKernel_props :
    Continuous cutoffKernel ∧
    (∃ CK : ℝ, 0 < CK ∧ ∀ u : ℝ, ‖cutoffKernel u‖ ≤ CK / (1 + u ^ 2)) ∧
    Integrable cutoffKernel ∧
    ∫ u : ℝ, cutoffKernel u = 1 := by
  obtain ⟨Bχ, hBχ_pos, hBχ⟩ := smoothCutoff0_deriv_bounds
  have hK_cont : Continuous cutoffKernel := by
    have h1 : Continuous (fun u : ℝ => ∫ s : ℝ, ((smoothCutoff0 s : ℝ) : ℂ) * Complex.exp (Complex.I * ((u * s : ℝ) : ℂ))) := by
      refine continuous_of_dominated (bound := fun s => if |s| ≤ 1 then 1 else 0) ?_ ?_ ?_ ?_
      · intro u; exact ((Complex.continuous_ofReal.comp contDiff_smoothCutoff0.continuous).mul (by fun_prop)).aestronglyMeasurable
      · intro u; filter_upwards with s
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (smoothCutoff0_nonneg s),
          show Complex.I * ((u * s : ℝ) : ℂ) = ((u * s : ℝ) : ℂ) * Complex.I by ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        split_ifs with h
        · exact smoothCutoff0_le_one s
        · rw [smoothCutoff0_eq_zero (not_le.mp h).le]
      · have heq : (fun s : ℝ => if |s| ≤ 1 then (1 : ℝ) else 0) = (Icc (-1 : ℝ) 1).indicator (fun _ => 1) := by
          ext s; simp only [Set.indicator, mem_Icc, abs_le]
        rw [heq, integrable_indicator_iff measurableSet_Icc]
        exact integrableOn_const (by simp)
      · filter_upwards with s; exact continuous_const.mul (by fun_prop)
    exact continuous_const.mul h1
  have hK_bd : ∃ CK : ℝ, 0 < CK ∧ ∀ u : ℝ, ‖cutoffKernel u‖ ≤ CK / (1 + u ^ 2) := by
    refine ⟨1 + 2 * Bχ, by positivity, fun u => ?_⟩
    have h0 : ‖cutoffKernel u‖ ≤ 1 / π := by
      unfold cutoffKernel
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hind : (fun s : ℝ => ((smoothCutoff0 s : ℝ) : ℂ) * Complex.exp (Complex.I * ((u * s : ℝ) : ℂ))) =
          (Icc (-1 : ℝ) 1).indicator (fun s : ℝ => ((smoothCutoff0 s : ℝ) : ℂ) * Complex.exp (Complex.I * ((u * s : ℝ) : ℂ))) := by
        ext s; simp only [Set.indicator, mem_Icc]
        split_ifs with h
        · rfl
        · simp only [not_and_or, not_le] at h
          have hge : 1 ≤ |s| := by
            rcases h with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          simp [smoothCutoff0_eq_zero hge]
      rw [hind, integral_indicator measurableSet_Icc]
      have hle := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-1 : ℝ) 1)
        (f := fun s : ℝ => ((smoothCutoff0 s : ℝ) : ℂ) * Complex.exp (Complex.I * ((u * s : ℝ) : ℂ)))
        (by simp) (C := 1) (fun s _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (smoothCutoff0_nonneg s),
            show Complex.I * ((u * s : ℝ) : ℂ) = ((u * s : ℝ) : ℂ) * Complex.I by ring,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          exact smoothCutoff0_le_one s)
      simp only [Measure.real, Real.volume_Icc, show (1 : ℝ) - (-1) = 2 by norm_num,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at hle
      calc 1 / (2 * π) * ‖∫ s in Icc (-1 : ℝ) 1, _‖ ≤ 1 / (2 * π) * (1 * 2) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 1 / π := by field_simp [Real.pi_ne_zero]
    by_cases hu : |u| ≤ 1
    · have h1 : 1 + u ^ 2 ≤ 2 := by nlinarith [sq_abs u, abs_nonneg u]
      have h2 : 1 / π ≤ (1 + 2 * Bχ) / (1 + u ^ 2) := by
        rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
        nlinarith [Real.pi_gt_three]
      exact h0.trans h2
    · have hu_ne : u ≠ 0 := fun h0 => hu (by simp [h0])
      have hcd2 : ContDiff ℝ 2 (fun t : ℝ => (smoothCutoff0 t : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_smoothCutoff0.of_le (by simp))
      have hibp := ibp_two_linear (M := 1) one_pos hu_ne hcd2
        (fun s hs => by simp [smoothCutoff0_eq_zero hs])
      have hd2 : ∀ s : ℝ, ‖iteratedDeriv 2 (fun t : ℝ => (smoothCutoff0 t : ℂ)) s‖ ≤ Bχ := fun s => by
        have hcd1 : ContDiff ℝ 1 (deriv smoothCutoff0) :=
          contDiff_one_deriv_of_two (contDiff_smoothCutoff0.of_le (by simp))
        have heq : iteratedDeriv 2 (fun t : ℝ => (smoothCutoff0 t : ℂ)) s =
            ((iteratedDeriv 2 smoothCutoff0 s : ℝ) : ℂ) := by
          rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
          have h1 : deriv (fun t : ℝ => (smoothCutoff0 t : ℂ)) = fun t => ((deriv smoothCutoff0 t : ℝ) : ℂ) :=
            funext fun t => ((contDiff_smoothCutoff0.differentiable (by decide)).differentiableAt.hasDerivAt.ofReal_comp).deriv
          rw [h1]
          exact (hcd1.differentiable (by decide)).differentiableAt.hasDerivAt.ofReal_comp.deriv
        rw [heq, Complex.norm_real, Real.norm_eq_abs]
        exact (hBχ s).2.1
      have hint_d2 : ∫ s in Icc (-1 : ℝ) 1, ‖iteratedDeriv 2 (fun t : ℝ => (smoothCutoff0 t : ℂ)) s‖ ≤ 2 * Bχ := by
        have hle := setIntegral_mono_on
          ((hcd2.continuous_iteratedDeriv 2 le_rfl).norm.continuousOn.integrableOn_compact isCompact_Icc)
          (integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => Bχ) (Icc (-1 : ℝ) 1))
          measurableSet_Icc (fun s _ => hd2 s)
        simpa [Measure.real, Real.volume_Icc, show (1 : ℝ) - (-1) = 2 by norm_num,
          ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using hle
      have hku : ‖cutoffKernel u‖ ≤ (2 * Bχ) / (2 * π * u ^ 2) := by
        unfold cutoffKernel
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hpow : u ^ (-(2 : ℝ)) = (u ^ 2)⁻¹ := rpow_neg_two_eq u
        calc 1 / (2 * π) * ‖∫ s : ℝ, _‖
            ≤ 1 / (2 * π) * (u ^ (-(2 : ℝ)) * (2 * Bχ)) :=
              mul_le_mul_of_nonneg_left (hibp.trans (mul_le_mul_of_nonneg_left hint_d2 (by rw [hpow]; positivity))) (by positivity)
          _ = (2 * Bχ) / (2 * π * u ^ 2) := by rw [hpow]; ring
      refine hku.trans ?_
      have h1u : 1 + u ^ 2 ≤ 2 * u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u, not_le.mp hu]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpi_u : 6 * u ^ 2 ≤ 2 * π * u ^ 2 := by nlinarith [Real.pi_gt_three, sq_nonneg u]
      nlinarith [h1u, hpi_u, sq_nonneg u]
  obtain ⟨CK, hCK_pos, hK_le⟩ := hK_bd
  have hK_int : Integrable cutoffKernel :=
    (integrable_inv_one_add_sq.const_mul CK).mono' hK_cont.aestronglyMeasurable
      (Eventually.of_forall fun u => (hK_le u).trans_eq (div_eq_mul_inv _ _))
  have hK_total : ∫ u : ℝ, cutoffKernel u = 1 := by
    have hcd : ContDiff ℝ 2 (fun s : ℝ => (smoothCutoff0 s : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_smoothCutoff0.of_le (by simp))
    have hint_χ : Integrable (fun s : ℝ => (smoothCutoff0 s : ℂ)) := by
      refine hcd.continuous.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) fun s hs => ?_
      rw [Function.mem_support] at hs
      by_contra hnot
      have hge : 1 ≤ |s| := by
        simp only [mem_Icc, not_and_or, not_le] at hnot
        rcases hnot with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact hs (by simp [smoothCutoff0_eq_zero hge])
    have hF_eq : ∀ ξ : ℝ, (𝓕 (fun s : ℝ => (smoothCutoff0 s : ℂ))) ξ = (2 * π : ℂ) * cutoffKernel (-(2 * π * ξ)) := by
      intro ξ
      rw [Real.fourier_real_eq_integral_exp_smul]
      unfold cutoffKernel
      rw [← mul_assoc, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
        show 2 * π * (1 / (2 * π)) = 1 by field_simp [Real.pi_ne_zero],
        Complex.ofReal_one, one_mul]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      dsimp only
      rw [smul_eq_mul, mul_comm]
      congr 2; push_cast; ring
    have hF_int : Integrable (𝓕 (fun s : ℝ => (smoothCutoff0 s : ℂ))) := by
      have hcomp := hK_int.comp_mul_left' (neg_ne_zero.mpr (by positivity : (2 * π : ℝ) ≠ 0))
      refine (hcomp.const_mul (2 * π : ℂ)).congr (Eventually.of_forall fun ξ => ?_)
      dsimp only; rw [hF_eq ξ, show -(2 * π) * ξ = -(2 * π * ξ) by ring]
    have hinv := congrFun (hcd.continuous.fourierInv_fourier_eq hint_χ hF_int) 0
    rw [Real.fourierInv_eq'] at hinv
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at hinv
    have hcov := Measure.integral_comp_mul_left (g := cutoffKernel) (a := -(2 * π))
    rw [abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), Complex.real_smul] at hcov
    have hstep : ∫ ξ : ℝ, (𝓕 (fun s : ℝ => (smoothCutoff0 s : ℂ))) ξ = ∫ u : ℝ, cutoffKernel u := by
      calc ∫ ξ : ℝ, (𝓕 (fun s : ℝ => (smoothCutoff0 s : ℂ))) ξ
          = ∫ ξ : ℝ, (2 * π : ℂ) * cutoffKernel (-(2 * π) * ξ) := by
            refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
            rw [hF_eq ξ]; congr 2; ring
        _ = (2 * π : ℂ) * ∫ ξ : ℝ, cutoffKernel (-(2 * π) * ξ) := by rw [integral_const_mul]
        _ = (2 * π : ℂ) * ((((2 * π)⁻¹ : ℝ) : ℂ) * ∫ u : ℝ, cutoffKernel u) := by rw [hcov]
        _ = ∫ u : ℝ, cutoffKernel u := by
            rw [← mul_assoc, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
              mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0),
              Complex.ofReal_one, one_mul]
    rw [← hstep, hinv, smoothCutoff0_eq_one (by norm_num), Complex.ofReal_one]
  exact ⟨hK_cont, ⟨CK, hCK_pos, hK_le⟩, hK_int, hK_total⟩

/-- Step 2 of `regSqrt_cutoff_fourier`: as `R → ∞`, the smoothed integral converges to
`π^{-1/2} ω^{-1/2} e^{-lam ω}` by Fubini and approximate identity. -/
private lemma regSqrt_cutoff_tendsto {lam ω : ℝ} (hlam : 0 < lam) (hω : 0 < ω) :
    Tendsto (fun R : ℝ =>
      ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ τ : ℝ, ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * regSqrt lam τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)))
      atTop (𝓝 (((1 / √π) * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * ω) : ℝ) : ℂ)) := by
  obtain ⟨hK_cont, ⟨CK, hCK_pos, hK_le⟩, hK_int, hK_total⟩ := cutoffKernel_props
  let g : ℝ → ℝ := fun t => t ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * t)
  have hG_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hG := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)
    have hcomp := (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ (-(1 / 2 : ℝ))) 0 hlam).mpr (by
        simpa only [mul_zero] using hG.congr_fun (fun t _ => by norm_num) measurableSet_Ioi)
    refine (hcomp.const_mul (lam ^ (1 / 2 : ℝ))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    dsimp only [g]
    rw [Real.mul_rpow hlam.le ht0.le, show -(lam * t) = -lam * t by ring]
    have hcancel : lam ^ (1 / 2 : ℝ) * lam ^ (-(1 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hlam]; norm_num
    calc lam ^ (1 / 2 : ℝ) * (Real.exp (-lam * t) * (lam ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ))))
        = (lam ^ (1 / 2 : ℝ) * lam ^ (-(1 / 2 : ℝ))) * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * t)) := by ring
      _ = t ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * t) := by rw [hcancel, one_mul]
  have hfub_R : ∀ R : ℝ, 0 < R →
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ τ : ℝ, ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * regSqrt lam τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
        ((1 / √π : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ),
          ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))) := by
    intro R hR
    let J : ℝ → ℝ → ℂ := fun τ t =>
      ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ))) *
        Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))
    have hJ_int : Integrable (Function.uncurry J) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
      have hmeas : AEStronglyMeasurable (Function.uncurry J) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
        let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2}
        have hS_open : IsOpen S := isOpen_lt continuous_const continuous_snd
        have hS_ae : ∀ᵐ p ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))), p ∈ S :=
          MeasureTheory.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_restrict_mem measurableSet_Ioi)
        have hcont_S : ContinuousOn (Function.uncurry J) S := by
          intro p hp
          have h1 : ContinuousAt (fun q : ℝ × ℝ => ((smoothCutoff0 (q.1 / R) : ℝ) : ℂ)) p :=
            (Complex.continuous_ofReal.comp (contDiff_smoothCutoff0.continuous.comp (continuous_id.div_const R))).continuousAt.comp continuousAt_fst
          have h2 : ContinuousAt (fun q : ℝ × ℝ => ((q.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) p :=
            Complex.continuous_ofReal.continuousAt.comp (ContinuousAt.rpow_const continuousAt_snd (Or.inl hp.ne'))
          have h3 : ContinuousAt (fun q : ℝ × ℝ => Complex.exp (-(((lam : ℂ) + (q.1 : ℂ) * Complex.I) * (q.2 : ℂ)))) p := by
            fun_prop
          have h4 : ContinuousAt (fun q : ℝ × ℝ => Complex.exp (Complex.I * ((ω * q.1 : ℝ) : ℂ))) p := by
            fun_prop
          exact (((h1.mul h2).mul h3).mul h4).continuousWithinAt
        have hrestrict := Measure.restrict_eq_self_of_ae_mem hS_ae
        have h := hcont_S.aestronglyMeasurable (μ := volume.prod (volume.restrict (Ioi (0 : ℝ)))) hS_open.measurableSet
        rwa [hrestrict] at h
      have hdom_τ : Integrable (fun τ : ℝ => smoothCutoff0 (τ / R)) volume := by
        refine (contDiff_smoothCutoff0.continuous.comp (continuous_id.div_const R)).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R)) fun τ hτ => ?_
        rw [Function.mem_support] at hτ
        by_contra hnot
        have hge : R ≤ |τ| := by
          simp only [mem_Icc, not_and_or, not_le] at hnot
          rcases hnot with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        exact hτ (smoothCutoff0_eq_zero (by rw [abs_div, abs_of_pos hR, one_le_div hR]; exact hge))
      refine (hdom_τ.mul_prod hG_int).mono' hmeas ?_
      have hae := MeasureTheory.QuasiMeasurePreserving.ae
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))))
        (ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ))))
      filter_upwards [hae] with ⟨τ, t⟩ ht
      have ht0 : 0 < t := ht
      dsimp only [Function.uncurry, J, g]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (smoothCutoff0_nonneg _), Real.norm_of_nonneg (Real.rpow_pos_of_pos ht0 _).le,
        Complex.norm_exp, show (-(((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ))).re = -lam * t by simp,
        show Complex.I * ((ω * τ : ℝ) : ℂ) = ((ω * τ : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      ring_nf; exact le_rfl
    have hswap := integral_integral_swap hJ_int
    have hlhs : ∫ τ : ℝ, ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * regSqrt lam τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
        ((1 / √π : ℝ) : ℂ) * ∫ τ : ℝ, ∫ t in Ioi (0 : ℝ), J τ t := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      have hlap := integral_rpow_neg_half_mul_exp_neg (z := (lam : ℂ) + (τ : ℂ) * Complex.I) (by simp [hlam])
      have hreg : regSqrt lam τ = ((1 / √π : ℝ) : ℂ) *
          ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ)) := by
        unfold regSqrt; rw [hlap, ← mul_assoc, ← Complex.ofReal_mul,
          show 1 / √π * √π = 1 by field_simp, Complex.ofReal_one, one_mul]
      dsimp only
      rw [hreg]
      rw [show ((smoothCutoff0 (τ / R) : ℝ) : ℂ) *
          (((1 / √π : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ))) *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)) =
        ((1 / √π : ℝ) : ℂ) * ((((smoothCutoff0 (τ / R) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) *
          ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ))) by ring]
      congr 1
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp [J]; ring
    rw [hlhs, hswap, mul_left_comm, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hcov := Measure.integral_comp_mul_left
      (g := fun s : ℝ => ((smoothCutoff0 s : ℝ) : ℂ) * Complex.exp (Complex.I * (((R * (ω - t)) * s : ℝ) : ℂ)))
      (a := R⁻¹)
    rw [abs_inv, abs_of_pos (inv_pos.mpr hR), inv_inv, Complex.real_smul] at hcov
    have hinner : ∫ τ : ℝ, J τ t =
        ((g t : ℝ) : ℂ) *
          ∫ τ : ℝ, ((smoothCutoff0 (R⁻¹ * τ) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (((R * (ω - t)) * (R⁻¹ * τ) : ℝ) : ℂ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      dsimp only [J, g]
      rw [show R⁻¹ * τ = τ / R by ring,
        show R * (ω - t) * (τ / R) = (ω - t) * τ by field_simp [hR.ne']]
      conv_rhs => rw [Complex.ofReal_mul, Complex.ofReal_exp]
      calc ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (-(((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ))) *
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))
          = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((smoothCutoff0 (τ / R) : ℝ) : ℂ) *
            (Complex.exp (-(((lam : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ))) *
             Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) := by ring
        _ = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((smoothCutoff0 (τ / R) : ℝ) : ℂ) *
            (Complex.exp (((-lam * t : ℝ) : ℂ)) * Complex.exp (Complex.I * (((ω - t) * τ : ℝ) : ℂ))) := by
            rw [← Complex.exp_add, ← Complex.exp_add]; congr 2; push_cast; ring
        _ = _ := by ring
    rw [hinner, hcov]
    unfold cutoffKernel; ring
  have hg_cont : ContinuousAt g ω :=
    (ContinuousAt.rpow_const continuousAt_id (Or.inl hω.ne')).mul (by fun_prop)
  have happrox : Tendsto (fun R : ℝ =>
      ∫ t in Ioi (0 : ℝ), ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))))
      atTop (𝓝 ((g ω : ℝ) : ℂ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set MK : ℝ := ∫ u : ℝ, ‖cutoffKernel u‖ with hMK_def
    have hMK_nn : 0 ≤ MK := integral_nonneg fun _ => norm_nonneg _
    have hε1 : 0 < ε / (4 * (MK + 1)) := by positivity
    obtain ⟨δ0, hδ0_pos, hδ0⟩ := Metric.continuousAt_iff.mp hg_cont (ε / (4 * (MK + 1))) hε1
    set δ : ℝ := min (δ0 / 2) (ω / 2) with hδ_def
    have hδ_pos : 0 < δ := lt_min (half_pos hδ0_pos) (half_pos hω)
    have hδ_lt_ω : δ < ω := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hω)
    have hg_close : ∀ t : ℝ, |ω - t| ≤ δ → |g t - g ω| < ε / (4 * (MK + 1)) := fun t ht => by
      have hd : dist t ω < δ0 := by
        rw [Real.dist_eq, abs_sub_comm]
        exact lt_of_le_of_lt ht (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ0_pos))
      simpa [Real.dist_eq] using hδ0 hd
    set Ig : ℝ := ∫ t in Ioi (0 : ℝ), |g t| with hIg_def
    have hIg_nn : 0 ≤ Ig := setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _
    refine ⟨max 1 (max (4 * CK * (Ig + 1) / (ε * δ ^ 2)) (8 * CK * (|g ω| + 1) / (ε * δ))), fun R hR => ?_⟩
    have hR_pos : 0 < R := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hR)
    rw [dist_eq_norm]
    have hK_shift : ∫ u : ℝ, (R : ℂ) * cutoffKernel (R * (ω - u)) = 1 := by
      have h1 := Measure.integral_comp_mul_left (g := cutoffKernel) (a := R)
      rw [abs_inv, abs_of_pos hR_pos, Complex.real_smul, hK_total] at h1
      have h2 : ∫ u : ℝ, cutoffKernel (R * (ω - u)) = ∫ s : ℝ, cutoffKernel (R * s) :=
        integral_sub_left_eq_self (fun s : ℝ => cutoffKernel (R * s)) volume ω
      rw [integral_const_mul, h2, h1, mul_one, ← Complex.ofReal_mul, mul_inv_cancel₀ hR_pos.ne',
        Complex.ofReal_one]
    have hint_RK : Integrable (fun t : ℝ => (R : ℂ) * cutoffKernel (R * (ω - t))) :=
      ((hK_int.comp_mul_left' hR_pos.ne').comp_sub_left ω).const_mul (R : ℂ)
    have hint_gRK : IntegrableOn (fun t : ℝ => ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) (Ioi (0 : ℝ)) := by
      refine (hG_int.norm.const_mul (R * CK)).mono' ?_ ?_
      · exact ((Complex.continuous_ofReal.comp_continuousOn
          ((ContinuousOn.rpow_const continuousOn_id (fun t (ht : t ∈ Ioi 0) => Or.inl ht.ne')).mul
            (by fun_prop))).mul (continuous_const.mul (hK_cont.comp (by fun_prop))).continuousOn).aestronglyMeasurable
          measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hR_pos.le]
        have hKu : ‖cutoffKernel (R * (ω - t))‖ ≤ CK :=
          (hK_le _).trans (div_le_self hCK_pos.le (by nlinarith [sq_nonneg (R * (ω - t))]))
        calc ‖g t‖ * (R * ‖cutoffKernel (R * (ω - t))‖) ≤ ‖g t‖ * (R * CK) := by gcongr
          _ = R * CK * ‖g t‖ := by ring
    let S_in : Set ℝ := Icc (ω - δ) (ω + δ)
    have hSin_sub : S_in ⊆ Ioi (0 : ℝ) := fun t ht => show 0 < t by linarith [ht.1, hδ_lt_ω]
    have hdecomp : (∫ t in Ioi (0 : ℝ), ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) - ((g ω : ℝ) : ℂ) =
        (∫ t in S_in, (((g t - g ω : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))))) +
        (∫ t in Ioi (0 : ℝ) \ S_in, ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) -
        ((g ω : ℝ) : ℂ) * ∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t)) := by
      have h1 : ∫ t in Ioi (0 : ℝ), ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))) =
          (∫ t in S_in, ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) +
          (∫ t in Ioi (0 : ℝ) \ S_in, ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) := by
        rw [← setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioi.diff measurableSet_Icc)
          (hint_gRK.mono_set hSin_sub) (hint_gRK.mono_set sdiff_subset), union_sdiff_cancel hSin_sub]
      have h2 : ((g ω : ℝ) : ℂ) = ((g ω : ℝ) : ℂ) * (∫ t in S_in, (R : ℂ) * cutoffKernel (R * (ω - t))) +
          ((g ω : ℝ) : ℂ) * (∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t))) := by
        rw [← mul_add, ← setIntegral_union (s := S_in) (t := S_inᶜ) disjoint_compl_right measurableSet_Icc.compl
          hint_RK.integrableOn hint_RK.integrableOn, union_compl_self, setIntegral_univ, hK_shift, mul_one]
      have h3 : (∫ t in S_in, ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) -
          ((g ω : ℝ) : ℂ) * (∫ t in S_in, (R : ℂ) * cutoffKernel (R * (ω - t))) =
          ∫ t in S_in, (((g t - g ω : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))) := by
        rw [← integral_const_mul, ← integral_sub (hint_gRK.mono_set hSin_sub) (hint_RK.integrableOn.const_mul ((g ω : ℝ) : ℂ))]
        refine setIntegral_congr_fun measurableSet_Icc fun t _ => by push_cast; ring
      conv_lhs => rw [h1, h2]
      linear_combination h3
    rw [hdecomp]
    have hT1 : ‖∫ t in S_in, (((g t - g ω : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))))‖ ≤ ε / 4 := by
      calc ‖∫ t in S_in, _‖ ≤ ∫ t in S_in, ‖(((g t - g ω : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t in S_in, (ε / (4 * (MK + 1))) * (R * ‖cutoffKernel (R * (ω - t))‖) := by
            refine setIntegral_mono_on
              (((hint_gRK.mono_set hSin_sub).sub (hint_RK.integrableOn.const_mul ((g ω : ℝ) : ℂ))).congr_fun
                (fun t _ => by simp only [Pi.sub_apply]; push_cast; ring) measurableSet_Icc).norm
              ((hint_RK.norm.const_mul (ε / (4 * (MK + 1)))).integrableOn.congr_fun
                (fun t _ => by dsimp only; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR_pos.le]) measurableSet_Icc)
              measurableSet_Icc fun t ht => ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_of_nonneg hR_pos.le]
            exact mul_le_mul_of_nonneg_right (hg_close t (abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩)).le
              (by positivity)
        _ ≤ ∫ t : ℝ, (ε / (4 * (MK + 1))) * (R * ‖cutoffKernel (R * (ω - t))‖) :=
            setIntegral_le_integral ((hint_RK.norm.const_mul (ε / (4 * (MK + 1)))).congr (Eventually.of_forall fun t => by
              dsimp only; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR_pos.le]))
              (Eventually.of_forall fun t => by positivity)
        _ = (ε / (4 * (MK + 1))) * MK := by
            rw [integral_const_mul, integral_const_mul]
            have h1 := Measure.integral_comp_mul_left (g := fun u => ‖cutoffKernel u‖) (a := R)
            rw [abs_inv, abs_of_pos hR_pos, smul_eq_mul] at h1
            have h2 : ∫ t : ℝ, ‖cutoffKernel (R * (ω - t))‖ = ∫ s : ℝ, ‖cutoffKernel (R * s)‖ :=
              integral_sub_left_eq_self (fun s => ‖cutoffKernel (R * s)‖) volume ω
            rw [h2, h1, ← mul_assoc R, mul_inv_cancel₀ hR_pos.ne', one_mul, hMK_def]
        _ ≤ ε / 4 := by
            have : MK / (MK + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
            calc (ε / (4 * (MK + 1))) * MK = (ε / 4) * (MK / (MK + 1)) := by field_simp
              _ ≤ (ε / 4) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
              _ = ε / 4 := mul_one _
    have hT2 : ‖∫ t in Ioi (0 : ℝ) \ S_in, ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))‖ ≤ ε / 4 := by
      have hR_bd : 4 * CK * (Ig + 1) / (ε * δ ^ 2) ≤ R :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans hR
      calc ‖∫ t in Ioi (0 : ℝ) \ S_in, _‖
          ≤ ∫ t in Ioi (0 : ℝ) \ S_in, ‖((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t)))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioi (0 : ℝ) \ S_in, (CK / (R * δ ^ 2)) * |g t| := by
            refine setIntegral_mono_on (hint_gRK.mono_set sdiff_subset).norm
              (IntegrableOn.mono_set (hG_int.norm.const_mul (CK / (R * δ ^ 2))) sdiff_subset)
              (measurableSet_Ioi.diff measurableSet_Icc) fun t ht => ?_
            have hδ_lt : δ < |ω - t| := by
              have hnot := ht.2
              simp only [S_in, mem_Icc, not_and_or, not_le] at hnot
              rcases hnot with h | h
              · rw [abs_of_pos (by linarith)]; linarith
              · rw [abs_of_neg (by linarith)]; linarith
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_of_nonneg hR_pos.le]
            have hK_out : R * ‖cutoffKernel (R * (ω - t))‖ ≤ CK / (R * δ ^ 2) := by
              have hsq : R ^ 2 * δ ^ 2 ≤ 1 + (R * (ω - t)) ^ 2 := by
                have : (R * δ) ^ 2 ≤ (R * |ω - t|) ^ 2 :=
                  pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hδ_lt.le hR_pos.le) 2
                rw [mul_pow, mul_pow, sq_abs] at this; linarith
              calc R * ‖cutoffKernel (R * (ω - t))‖ ≤ R * (CK / (1 + (R * (ω - t)) ^ 2)) :=
                    mul_le_mul_of_nonneg_left (hK_le _) hR_pos.le
                _ ≤ R * (CK / (R ^ 2 * δ ^ 2)) :=
                    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hCK_pos.le (by positivity) hsq) hR_pos.le
                _ = CK / (R * δ ^ 2) := by field_simp [hR_pos.ne']
            calc |g t| * (R * ‖cutoffKernel (R * (ω - t))‖) ≤ |g t| * (CK / (R * δ ^ 2)) :=
                  mul_le_mul_of_nonneg_left hK_out (abs_nonneg _)
              _ = (CK / (R * δ ^ 2)) * |g t| := mul_comm _ _
        _ ≤ ∫ t in Ioi (0 : ℝ), (CK / (R * δ ^ 2)) * |g t| :=
            setIntegral_mono_set (hG_int.norm.const_mul _)
              (ae_of_all _ fun t => by positivity) (Eventually.of_forall sdiff_subset)
        _ = (CK / (R * δ ^ 2)) * Ig := integral_const_mul _ _
        _ ≤ ε / 4 := by
            rw [div_le_iff₀ (by positivity)] at hR_bd
            rw [mul_comm, ← mul_div_assoc, div_le_iff₀ (by positivity)]
            nlinarith
    have hT3 : ‖((g ω : ℝ) : ℂ) * ∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t))‖ ≤ ε / 4 := by
      have hR_bd : 8 * CK * (|g ω| + 1) / (ε * δ) ≤ R :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hR
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have htail : ‖∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t))‖ ≤ 2 * CK / (R * δ) := by
        have hint_f : Integrable (fun t : ℝ => R * (CK / (1 + (R * (ω - t)) ^ 2))) :=
          (((integrable_inv_one_add_sq.const_mul CK).congr (Eventually.of_forall fun u => (div_eq_mul_inv _ _).symm)).comp_mul_left' hR_pos.ne').comp_sub_left ω |>.const_mul R
        have h1 : ‖∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t))‖ ≤
            ∫ t in S_inᶜ, R * (CK / (1 + (R * (ω - t)) ^ 2)) := by
          calc ‖∫ t in S_inᶜ, _‖ ≤ ∫ t in S_inᶜ, ‖(R : ℂ) * cutoffKernel (R * (ω - t))‖ :=
                norm_integral_le_integral_norm _
            _ ≤ ∫ t in S_inᶜ, R * (CK / (1 + (R * (ω - t)) ^ 2)) := by
                refine setIntegral_mono_on hint_RK.norm.integrableOn hint_f.integrableOn measurableSet_Icc.compl fun t _ => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR_pos.le]
                exact mul_le_mul_of_nonneg_left (hK_le _) hR_pos.le
        have hcompl : S_inᶜ = Iio (ω - δ) ∪ Ioi (ω + δ) := by
          ext t; simp only [S_in, mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
          constructor
          · intro h; rcases not_and_or.mp h with h1 | h1
            · exact Or.inl (lt_of_not_ge h1)
            · exact Or.inr (lt_of_not_ge h1)
          · rintro (h | h) ⟨h1, h2⟩ <;> linarith
        have hdisj : Disjoint (Iio (ω - δ)) (Ioi (ω + δ)) :=
          Set.disjoint_left.mpr fun t h1 h2 => by linarith [Set.mem_Iio.mp h1, Set.mem_Ioi.mp h2]
        have hright_eq : ∫ t in Ioi (ω + δ), R * (CK / (1 + (R * (ω - t)) ^ 2)) =
            ∫ s in Ioi δ, R * (CK / (1 + (R * s) ^ 2)) := by
          have hsub := integral_add_left_eq_self (μ := volume)
            (fun t : ℝ => (Ioi (ω + δ)).indicator (fun x => R * (CK / (1 + (R * (ω - x)) ^ 2))) t) ω
          rw [integral_indicator measurableSet_Ioi] at hsub
          rw [← hsub]
          have hind : (fun s : ℝ => (Ioi (ω + δ)).indicator (fun x => R * (CK / (1 + (R * (ω - x)) ^ 2))) (ω + s)) =
              (Ioi δ).indicator (fun s => R * (CK / (1 + (R * s) ^ 2))) := by
            ext s; simp only [Set.indicator, mem_Ioi]
            by_cases hs : δ < s
            · have h1 : ω + δ < ω + s := by linarith
              simp [hs, h1]
            · have h1 : ¬(ω + δ < ω + s) := by linarith
              simp [hs, h1]
          rw [hind, integral_indicator measurableSet_Ioi]
        have hleft_eq : ∫ t in Iio (ω - δ), R * (CK / (1 + (R * (ω - t)) ^ 2)) =
            ∫ s in Ioi δ, R * (CK / (1 + (R * s) ^ 2)) := by
          have hsub := integral_sub_left_eq_self
            (fun t : ℝ => (Iio (ω - δ)).indicator (fun x => R * (CK / (1 + (R * (ω - x)) ^ 2))) t) volume ω
          rw [integral_indicator measurableSet_Iio] at hsub
          rw [← hsub]
          have hind : (fun s : ℝ => (Iio (ω - δ)).indicator (fun x => R * (CK / (1 + (R * (ω - x)) ^ 2))) (ω - s)) =
              (Ioi δ).indicator (fun s => R * (CK / (1 + (R * s) ^ 2))) := by
            ext s; simp only [Set.indicator, mem_Iio, mem_Ioi]
            by_cases hs : δ < s
            · have h1 : ω - s < ω - δ := by linarith
              simp [hs, h1]
            · have h1 : ¬(ω - s < ω - δ) := by linarith
              simp [hs, h1]
          rw [hind, integral_indicator measurableSet_Ioi]
        have hpiece_le : ∫ s in Ioi δ, R * (CK / (1 + (R * s) ^ 2)) ≤ CK / (R * δ) := by
          have hscale := MeasureTheory.integral_comp_mul_left_Ioi (fun u : ℝ => CK / (1 + u ^ 2)) δ hR_pos
          simp only [smul_eq_mul] at hscale
          rw [integral_const_mul, hscale, ← mul_assoc, mul_inv_cancel₀ hR_pos.ne', one_mul]
          calc ∫ u in Ioi (R * δ), CK / (1 + u ^ 2)
              ≤ ∫ u in Ioi (R * δ), CK * u ^ (-(2 : ℝ)) := by
                refine setIntegral_mono_on
                  ((integrable_inv_one_add_sq.const_mul CK).congr (Eventually.of_forall fun u => (div_eq_mul_inv _ _).symm)).integrableOn
                  ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) (by positivity)).const_mul CK)
                  measurableSet_Ioi fun u hu => ?_
                have hu0 : 0 < u := lt_trans (by positivity) hu
                rw [rpow_neg_two_eq, ← div_eq_mul_inv]
                exact div_le_div_of_nonneg_left hCK_pos.le (sq_pos_of_pos hu0) (by linarith)
            _ = CK / (R * δ) := by
                rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) (by positivity),
                  show -(2 : ℝ) + 1 = -(1 : ℝ) by norm_num, Real.rpow_neg_one]; ring
        calc ‖∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t))‖
            ≤ ∫ t in Iio (ω - δ) ∪ Ioi (ω + δ), R * (CK / (1 + (R * (ω - t)) ^ 2)) := by
              rw [← hcompl]; exact h1
          _ = (∫ t in Iio (ω - δ), R * (CK / (1 + (R * (ω - t)) ^ 2))) +
              (∫ t in Ioi (ω + δ), R * (CK / (1 + (R * (ω - t)) ^ 2))) :=
              setIntegral_union hdisj measurableSet_Ioi hint_f.integrableOn hint_f.integrableOn
          _ ≤ CK / (R * δ) + CK / (R * δ) := by rw [hleft_eq, hright_eq]; exact add_le_add hpiece_le hpiece_le
          _ = 2 * CK / (R * δ) := by ring
      calc |g ω| * ‖∫ t in S_inᶜ, (R : ℂ) * cutoffKernel (R * (ω - t))‖
          ≤ |g ω| * (2 * CK / (R * δ)) := mul_le_mul_of_nonneg_left htail (abs_nonneg _)
        _ ≤ ε / 4 := by
            rw [div_le_iff₀ (by positivity)] at hR_bd
            rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
            nlinarith
    calc ‖(∫ t in S_in, _) + (∫ t in Ioi (0 : ℝ) \ S_in, _) - _‖
        ≤ ‖(∫ t in S_in, _) + (∫ t in Ioi (0 : ℝ) \ S_in, _)‖ + ‖((g ω : ℝ) : ℂ) * _‖ := norm_sub_le _ _
      _ ≤ (‖∫ t in S_in, _‖ + ‖∫ t in Ioi (0 : ℝ) \ S_in, _‖) + ‖((g ω : ℝ) : ℂ) * _‖ :=
          add_le_add_left (norm_add_le _ _) _
      _ ≤ (ε / 4 + ε / 4) + ε / 4 := add_le_add (add_le_add hT1 hT2) hT3
      _ < ε := by linarith
  have hlim' : Tendsto (fun R : ℝ =>
      ((1 / √π : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), ((g t : ℝ) : ℂ) * ((R : ℂ) * cutoffKernel (R * (ω - t))))
      atTop (𝓝 (((1 / √π) * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * ω) : ℝ) : ℂ)) := by
    have h := happrox.const_mul ((1 / √π : ℝ) : ℂ)
    simpa [g, mul_assoc] using h
  refine hlim'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (hfub_R R hR).symm

/-- **Smooth-cutoff Fourier inversion of `(lam + iτ)^{-1/2}`:**
there is an absolute constant `C_ref > 0` such that for all `lam > 0`, `ω > 0`, and `ς > 0`,
`‖(2π)⁻¹ ∫_ℝ χ₀(τ/ς) (lam + iτ)^{-1/2} e^{i ω τ} dτ - π^{-1/2} ω^{-1/2} e^{-lam ω}‖ ≤ C_ref ω^{-2} ς^{-3/2}`. -/
theorem regSqrt_cutoff_fourier :
    ∃ C_ref : ℝ, 0 < C_ref ∧ ∀ {lam ω ς : ℝ}, 0 < lam → 0 < ω → 0 < ς →
      ‖((1 / (2 * π) : ℝ) : ℂ) *
          (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt lam τ *
            Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) -
        (((1 / √π) * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * ω) : ℝ) : ℂ)‖ ≤
        C_ref * ω ^ (-(2 : ℝ)) * ς ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C0, hC0_pos, hdiff⟩ := regSqrt_diff_cutoff_bound
  refine ⟨C0, hC0_pos, fun {lam ω ς} hlam hω hς => ?_⟩
  have hlim_R := regSqrt_cutoff_tendsto hlam hω
  have hlim_norm : Tendsto (fun R : ℝ =>
      ‖((1 / (2 * π) : ℝ) : ℂ) * (∫ τ : ℝ, ((smoothCutoff0 (τ / R) : ℝ) : ℂ) * regSqrt lam τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ))) -
        ((1 / (2 * π) : ℝ) : ℂ) * (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt lam τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)))‖)
      atTop (𝓝 ‖(((1 / √π) * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-lam * ω) : ℝ) : ℂ) -
        ((1 / (2 * π) : ℝ) : ℂ) * (∫ τ : ℝ, ((smoothCutoff0 (τ / ς) : ℝ) : ℂ) * regSqrt lam τ *
          Complex.exp (Complex.I * ((ω * τ : ℝ) : ℂ)))‖) :=
    (hlim_R.sub tendsto_const_nhds).norm
  have hle := le_of_tendsto hlim_norm (by
    filter_upwards [eventually_ge_atTop (2 * ς)] with R hR
    exact hdiff hlam hω hς hR)
  rwa [norm_sub_rev] at hle

/-- info: 'FormalResearch.SignUncertainty.uct_ce_band_global_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_ce_band_global_bound

/-- info: 'FormalResearch.SignUncertainty.regSqrt_cutoff_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regSqrt_cutoff_fourier

end FormalResearch.SignUncertainty
