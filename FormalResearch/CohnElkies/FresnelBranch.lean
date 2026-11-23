module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fresnel integral and the branch-point term `∫ φ(v) (i v)^{1/2} e^{iAv} dv`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1c:U3`(3), Step 1, Piece C, item 3
("the branch term"), used in `O.3(2)` (`u1co:O3`, `(e4)`): for `φ ∈ C²` supported in `[-1, 1]`,
`∫ φ(v) (iv)^{1/2} e^{iAv} dv = -√π φ(0) A^{-3/2} + O(A^{-2})`.

This module proves this real-variable statement with an explicit absolute constant, with no reference
to the Airy seeds (`fresnel_branch`: for `φ ∈ C²` with `φ = 0` off `[-1, 1]`, `|φ|, |φ'|, |φ''| ≤ M` and
`A ≥ 1`, `|∫ φ (iv)^{1/2} e^{iAv} dv + √π φ(0) A^{-3/2}| ≤ (12 D + 2) M A^{-2}`, `D = ∫₀^∞ t^{-1/2} e^{-t/2} dt`).
The ingredients:

* `ibp_half_line`: improper integration by parts of `f e^{iat}` on `(0, ∞)`;
* `integral_rpow_neg_half_exp`: `∫₀^∞ t^{-1/2} e^{-bt} dt = (π/b)^{1/2}` for `Re b > 0`
  (Gaussian integral and the substitution `t = x²`), the complex-rate Gamma integral at `1/2`;
* `norm_sqrtPiDiv_sub_le`: `|(π/(1 - ia))^{1/2} - (π/(-ia))^{1/2}| ≤ ½ √π |a|^{-3/2}`;
* `HalfLineData.half_line`: the one-sided statement `∫₀^∞ φ √t e^{iat} dt = (i/2a) φ(0) √(π/(-ia)) + O(M/a²)`,
  by one integration by parts (to `∫ φ t^{-1/2} e^{iat}`), the model `e^{-t}`, and a second one.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

/-! ### Improper integration by parts on `(0, ∞)` -/

/-- `∫₀^∞ f e^{iat} dt = -(ia)⁻¹ ∫₀^∞ f' e^{iat} dt` for `f` continuous at `0` with `f(0) = 0`,
`f → 0` at `∞`, and `f`, `f'` integrable. -/
theorem ibp_half_line {f f' : ℝ → ℂ} {a : ℝ} (ha : a ≠ 0) (hcont : ContinuousWithinAt f (Ici 0) 0) (hf0 : f 0 = 0)
    (hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t) (hint : IntegrableOn f' (Ioi 0)) (hint0 : IntegrableOn f (Ioi 0))
    (hlim : Tendsto f atTop (𝓝 0)) :
    ∫ t in Ioi (0 : ℝ), f t * Complex.exp (Complex.I * a * t) =
      -(Complex.I * a)⁻¹ * ∫ t in Ioi (0 : ℝ), f' t * Complex.exp (Complex.I * a * t) := by
  have hia : (Complex.I * (a : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ha)
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  set F : ℝ → ℂ := fun t => f t * Complex.exp (Complex.I * a * t) / (Complex.I * a) with hF
  have hFd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (f' t * Complex.exp (Complex.I * a * t) / (Complex.I * a) +
      f t * Complex.exp (Complex.I * a * t)) t := fun t ht => by
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * a * s)) (Complex.exp (Complex.I * a * t) * (Complex.I * a)) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * a)).cexp
      simpa [mul_comm] using this
    have := ((hd t ht).mul h1).div_const (Complex.I * a)
    convert this using 1
    field_simp
  have hnorm_exp : ∀ t : ℝ, ‖Complex.exp (Complex.I * a * t)‖ = 1 := fun t => by
    rw [show Complex.I * (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hmeas : Continuous fun t : ℝ => Complex.exp (Complex.I * a * t) := by fun_prop
  have hint1 : IntegrableOn (fun t : ℝ => f' t * Complex.exp (Complex.I * a * t)) (Ioi 0) :=
    hint.norm.mono' (hint.aestronglyMeasurable.mul hmeas.aestronglyMeasurable) (ae_of_all _ fun t => by rw [norm_mul, hnorm_exp, mul_one])
  have hint2 : IntegrableOn (fun t : ℝ => f t * Complex.exp (Complex.I * a * t)) (Ioi 0) :=
    hint0.norm.mono' (hint0.aestronglyMeasurable.mul hmeas.aestronglyMeasurable) (ae_of_all _ fun t => by rw [norm_mul, hnorm_exp, mul_one])
  have hlimF : Tendsto F atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => ‖F t‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => ‖f t‖ / ‖Complex.I * a‖) atTop (𝓝 0) := by
        simpa using (hlim.norm).div_const ‖Complex.I * (a : ℂ)‖
      refine h0.congr fun t => ?_
      simp [hF, hnorm_exp]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  have hFc : ContinuousWithinAt F (Ici 0) 0 := by
    have : ContinuousWithinAt (fun t : ℝ => Complex.exp (Complex.I * a * t)) (Ici 0) 0 := hmeas.continuousWithinAt
    exact (hcont.mul this).div_const _
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hFc hFd ((hint1.div_const (Complex.I * a)).add hint2) hlimF
  have hF0 : F 0 = 0 := by simp [hF, hf0]
  rw [hF0, sub_zero, integral_add (hint1.div_const _) hint2, integral_div] at key
  have : ∫ t in Ioi (0 : ℝ), f t * Complex.exp (Complex.I * a * t) =
      -((∫ t in Ioi (0 : ℝ), f' t * Complex.exp (Complex.I * a * t)) / (Complex.I * a)) := by
    linear_combination key
  rw [this]; field_simp

/-! ### The Gamma integral at `1/2` with complex rate -/

/-- `∫₀^∞ t^{-1/2} e^{-bt} dt = (π / b)^{1/2}` for `Re b > 0`. -/
theorem integral_rpow_neg_half_exp {b : ℂ} (hb : 0 < b.re) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(b * t)) = ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) := by
  have hsub := integral_comp_rpow_Ioi (fun t : ℝ => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(b * t))) (p := 2) (by norm_num)
  rw [← hsub]
  have h2 : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • (((((x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) *
      Complex.exp (-(b * ((x ^ (2 : ℝ) : ℝ) : ℂ)))) = ∫ x in Ioi (0 : ℝ), 2 * Complex.exp (-b * (x : ℂ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have e1 : (x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
      rw [Real.rpow_two, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx0.le]
    have e2 : x ^ ((2 : ℝ) - 1) = x := by norm_num
    rw [Complex.real_smul, e1, e2, Real.rpow_two]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    push_cast
    rw [show -(b * (x : ℂ) ^ 2) = -b * (x : ℂ) ^ 2 by ring]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    push_cast
    field_simp
  rw [h2, integral_const_mul, integral_gaussian_complex_Ioi hb]
  ring

/-! ### Comparison of the complex-rate Gamma values -/

/-- `√(π / b)` as a function of `b`. -/
noncomputable def sqrtPiDiv (b : ℂ) : ℂ := ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ)

/-- Derivative of `√(π / z)` off the real axis. -/
lemma hasDerivAt_sqrtPiDiv {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt sqrtPiDiv (-(1 / 2 : ℂ) * sqrtPiDiv z / z) z := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  have hslit : (Real.pi : ℂ) / z ∈ Complex.slitPlane := by
    refine Or.inr ?_
    have : ((Real.pi : ℂ) / z).im = -Real.pi * z.im / Complex.normSq z := by
      rw [Complex.div_im]; simp; ring
    rw [this]
    have hns : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    intro h
    have : -Real.pi * z.im = 0 := by
      have := (div_eq_zero_iff.mp h).resolve_right hns.ne'
      exact this
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Real.pi_pos.ne' (by linarith)
    · exact hz h1
  have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) / w) (-(Real.pi : ℂ) / z ^ 2) z := by
    have := (hasDerivAt_const z (Real.pi : ℂ)).div (hasDerivAt_id z) hz0
    exact this.congr_deriv (by simp)
  have h2 := h1.cpow_const (c := (1 / 2 : ℂ)) hslit
  unfold sqrtPiDiv
  convert h2 using 1
  have hq : ((Real.pi : ℂ) / z) ^ ((1 / 2 : ℂ) - 1) = ((Real.pi : ℂ) / z) ^ (1 / 2 : ℂ) / ((Real.pi : ℂ) / z) := by
    rw [Complex.cpow_sub _ _ (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hz0), Complex.cpow_one]
  rw [hq]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- `|√(π/(1 - ia)) - √(π/(-ia))| ≤ ½ √π |a|^{-3/2}` for real `a ≠ 0`. -/
theorem norm_sqrtPiDiv_sub_le {a : ℝ} (ha : a ≠ 0) :
    ‖sqrtPiDiv (1 - Complex.I * a) - sqrtPiDiv (-(Complex.I * a))‖ ≤ (1 / 2) * Real.sqrt Real.pi * |a| ^ (-(3 / 2 : ℝ)) := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  let s : Set ℂ := {z | z.im = -a ∧ 0 ≤ z.re ∧ z.re ≤ 1}
  have hconv : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, hx.1, hy.1]; linear_combination (-a) * hpq
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; nlinarith [hx.2.1, hy.2.1]
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]; nlinarith [hx.2.2, hy.2.2]
  have hz0 : (-(Complex.I * a) : ℂ) ∈ s := ⟨by simp, by simp, by simp⟩
  have hz1 : (1 - Complex.I * a : ℂ) ∈ s := ⟨by simp, by simp, by simp⟩
  have hd : ∀ z ∈ s, HasDerivWithinAt sqrtPiDiv (-(1 / 2 : ℂ) * sqrtPiDiv z / z) s z := fun z hz =>
    (hasDerivAt_sqrtPiDiv (by rw [hz.1]; simpa using ha)).hasDerivWithinAt
  have hb : ∀ z ∈ s, ‖-(1 / 2 : ℂ) * sqrtPiDiv z / z‖ ≤ (1 / 2) * Real.sqrt Real.pi * |a| ^ (-(3 / 2 : ℝ)) := fun z hz => by
    have hz_ge : |a| ≤ ‖z‖ := by
      have := Complex.abs_im_le_norm z
      rwa [hz.1, abs_neg] at this
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hapos hz_ge
    have hnorm : ‖sqrtPiDiv z‖ = Real.sqrt Real.pi * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
      unfold sqrtPiDiv
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_real, norm_div, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Real.div_rpow Real.pi_pos.le hzpos.le, ← Real.sqrt_eq_rpow,
        Real.rpow_neg hzpos.le, div_eq_mul_inv]
    rw [norm_div, norm_mul, hnorm]
    have : ‖z‖ ^ (-(1 / 2 : ℝ)) / ‖z‖ = ‖z‖ ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_iff hzpos.ne', ← Real.rpow_add_one hzpos.ne']; norm_num
    have hle : ‖z‖ ^ (-(3 / 2 : ℝ)) ≤ |a| ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hapos hz_ge (by norm_num)
    calc ‖(-(1 / 2 : ℂ))‖ * (Real.sqrt Real.pi * ‖z‖ ^ (-(1 / 2 : ℝ))) / ‖z‖ =
        (1 / 2) * Real.sqrt Real.pi * (‖z‖ ^ (-(1 / 2 : ℝ)) / ‖z‖) := by
          rw [norm_neg]; simp; ring
      _ = (1 / 2) * Real.sqrt Real.pi * ‖z‖ ^ (-(3 / 2 : ℝ)) := by rw [this]
      _ ≤ _ := by gcongr
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hconv hz0 hz1
  have hdist : ‖(1 - Complex.I * a : ℂ) - (-(Complex.I * a))‖ = 1 := by simp
  rw [hdist, mul_one] at this
  exact this


/-! ### Dominating function and elementary derivatives on `(0, ∞)` -/

/-- `d(t) = t^{-1/2} e^{-t/2}`, integrable on `(0, ∞)`. -/
noncomputable def fresnelDom (t : ℝ) : ℝ := (Real.sqrt t)⁻¹ * Real.exp (-t / 2)

lemma integrableOn_fresnelDom : IntegrableOn fresnelDom (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ)) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  simp only [fresnelDom, Real.rpow_one]
  rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
  congr 2; ring

lemma fresnelDom_nonneg (t : ℝ) : 0 ≤ fresnelDom t := by unfold fresnelDom; positivity

/-- A function dominated by `K · d` on `(0, ∞)` has a half-line oscillatory integral bounded by `K · ∫ d`. -/
lemma norm_integral_exp_le_of_dom {g : ℝ → ℂ} {K : ℝ} {a : ℝ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hdom : ∀ t ∈ Ioi (0 : ℝ), ‖g t‖ ≤ K * fresnelDom t) :
    IntegrableOn g (Ioi 0) ∧ ‖∫ t in Ioi (0 : ℝ), g t * Complex.exp (Complex.I * a * t)‖ ≤ K * ∫ t in Ioi (0 : ℝ), fresnelDom t := by
  have hint : IntegrableOn g (Ioi 0) :=
    (integrableOn_fresnelDom.const_mul K).mono' hg ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hdom))
  refine ⟨hint, ?_⟩
  have hnorm_exp : ∀ t : ℝ, ‖Complex.exp (Complex.I * a * t)‖ = 1 := fun t => by
    rw [show Complex.I * (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  calc ‖∫ t in Ioi (0 : ℝ), g t * Complex.exp (Complex.I * a * t)‖ ≤ ∫ t in Ioi (0 : ℝ), K * fresnelDom t := by
        refine norm_integral_le_of_norm_le (integrableOn_fresnelDom.const_mul K) ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
        rw [norm_mul, hnorm_exp, mul_one]; exact hdom t ht
    _ = _ := integral_const_mul _ _


/-! ### Half-line branch integral -/

/-- Hypotheses on the amplitude of a half-line branch integral: `C²`, supported in `(-∞, 1]` on the right,
with `‖φ‖, ‖φ'‖, ‖φ''‖ ≤ M` on `[0, ∞)`. -/
structure HalfLineData (φ : ℝ → ℂ) (M : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  supp : ∀ t : ℝ, 1 < t → φ t = 0
  b0 : ∀ t : ℝ, 0 ≤ t → ‖φ t‖ ≤ M
  b1 : ∀ t : ℝ, 0 ≤ t → ‖deriv φ t‖ ≤ M
  b2 : ∀ t : ℝ, 0 ≤ t → ‖deriv (deriv φ) t‖ ≤ M

namespace HalfLineData

variable {φ : ℝ → ℂ} {M : ℝ}

lemma hasDeriv (h : HalfLineData φ M) (t : ℝ) : HasDerivAt φ (deriv φ t) t :=
  ((h.contDiff.differentiable (by norm_num)) t).hasDerivAt

lemma hasDeriv2 (h : HalfLineData φ M) (t : ℝ) : HasDerivAt (deriv φ) (deriv (deriv φ) t) t :=
  ((h.contDiff.differentiable_deriv_two) t).hasDerivAt

lemma continuous_deriv (h : HalfLineData φ M) : Continuous (deriv φ) :=
  continuous_iff_continuousAt.mpr fun t => (h.hasDeriv2 t).continuousAt

lemma continuous_deriv2 (h : HalfLineData φ M) : Continuous (deriv (deriv φ)) := by
  have := h.contDiff.iterate_deriv' 0 2
  simpa using this.continuous

lemma deriv_zero (h : HalfLineData φ M) {t : ℝ} (ht : 1 < t) : deriv φ t = 0 := by
  have : φ =ᶠ[𝓝 t] fun _ => (0 : ℂ) := Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => h.supp s hs
  rw [this.deriv_eq, deriv_const]

lemma deriv2_zero (h : HalfLineData φ M) {t : ℝ} (ht : 1 < t) : deriv (deriv φ) t = 0 := by
  have : deriv φ =ᶠ[𝓝 t] fun _ => (0 : ℂ) := Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => h.deriv_zero hs
  rw [this.deriv_eq, deriv_const]

lemma M_nonneg (h : HalfLineData φ M) : 0 ≤ M := (norm_nonneg _).trans (h.b0 0 le_rfl)

end HalfLineData

lemma exp_neg_half_ge {t : ℝ} (ht : t ≤ 1) : 1 / 2 ≤ Real.exp (-t / 2) := by
  have := Real.add_one_le_exp (-t / 2)
  linarith

lemma sqrt_le_inv_sqrt {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1) : Real.sqrt t ≤ (Real.sqrt t)⁻¹ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have h1 : Real.sqrt t * Real.sqrt t ≤ 1 := by rw [Real.mul_self_sqrt ht0.le]; exact ht
  calc Real.sqrt t = Real.sqrt t * Real.sqrt t * (Real.sqrt t)⁻¹ := by field_simp
    _ ≤ 1 * (Real.sqrt t)⁻¹ := by gcongr
    _ = _ := one_mul _

lemma hasDerivAt_ofReal_sqrt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (Real.sqrt s : ℂ)) ((1 / (2 * Real.sqrt t) : ℝ) : ℂ) t :=
  (Real.hasDerivAt_sqrt ht.ne').ofReal_comp

/-- First integration by parts: `∫₀^∞ φ' √t e^{iat} dt` is `O(M/|a|)`. -/
lemma HalfLineData.term1 {φ : ℝ → ℂ} {M : ℝ} (h : HalfLineData φ M) {a : ℝ} (ha : a ≠ 0) :
    ‖∫ t in Ioi (0 : ℝ), deriv φ t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * a * t)‖ ≤
      (3 * M * ∫ t in Ioi (0 : ℝ), fresnelDom t) / |a| := by
  set f : ℝ → ℂ := fun t => deriv φ t * (Real.sqrt t : ℂ) with hf
  set f' : ℝ → ℂ := fun t => deriv (deriv φ) t * (Real.sqrt t : ℂ) + deriv φ t * ((1 / (2 * Real.sqrt t) : ℝ) : ℂ) with hf'
  have hfc : Continuous f := h.continuous_deriv.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)
  have m1 := h.continuous_deriv.measurable
  have m2 := h.continuous_deriv2.measurable
  have hf'm : AEStronglyMeasurable f' (volume.restrict (Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.add (Measurable.mul m2 (by fun_prop)) (Measurable.mul m1 (by fun_prop))
  have hM := h.M_nonneg
  have hdom : ∀ t ∈ Ioi (0 : ℝ), ‖f' t‖ ≤ (3 * M) * fresnelDom t := fun t ht => by
    have ht0 : 0 < t := ht
    rcases le_or_gt t 1 with ht1 | ht1
    · have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have hu1 := sqrt_le_inv_sqrt ht0 ht1
      have hb1 := h.b1 t ht0.le
      have hb2 := h.b2 t ht0.le
      have hexp := exp_neg_half_ge ht1
      have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
      calc ‖f' t‖ ≤ ‖deriv (deriv φ) t‖ * Real.sqrt t + ‖deriv φ t‖ * (1 / (2 * Real.sqrt t)) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hu.le,
              Real.norm_of_nonneg (by positivity)]
        _ ≤ M * (Real.sqrt t)⁻¹ + M * ((Real.sqrt t)⁻¹ / 2) := by
            have : 1 / (2 * Real.sqrt t) = (Real.sqrt t)⁻¹ / 2 := by field_simp
            rw [this]
            gcongr
        _ ≤ (3 * M) * fresnelDom t := by
            unfold fresnelDom
            nlinarith [mul_nonneg hM hinv.le, mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le)]
    · simp only [hf', h.deriv_zero ht1, h.deriv2_zero ht1, zero_mul, add_zero, norm_zero]
      exact mul_nonneg (by positivity) (fresnelDom_nonneg t)
  have hint := (norm_integral_exp_le_of_dom (a := a) hf'm hdom).1
  have hbound := (norm_integral_exp_le_of_dom (a := a) hf'm hdom).2
  have hint0 : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_fresnelDom.const_mul (2 * M)).mono' hfc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht0 : 0 < t := ht
    rcases le_or_gt t 1 with ht1 | ht1
    · have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have hexp := exp_neg_half_ge ht1
      have hu1 := sqrt_le_inv_sqrt ht0 ht1
      have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
      calc ‖f t‖ = ‖deriv φ t‖ * Real.sqrt t := by
            rw [hf]; dsimp only; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le]
        _ ≤ M * (Real.sqrt t)⁻¹ := mul_le_mul (h.b1 t ht0.le) hu1 hu.le hM
        _ ≤ 2 * M * fresnelDom t := by
            unfold fresnelDom
            nlinarith [mul_nonneg hM hinv.le, mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le)]
    · simp only [hf, h.deriv_zero ht1, zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (fresnelDom_nonneg t)
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := fun t ht =>
    (h.hasDeriv2 t).mul (hasDerivAt_ofReal_sqrt ht) |>.congr_deriv (by simp [hf'])
  have hlim : Tendsto f atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((Filter.eventually_gt_atTop 1).mono fun t ht => by simp [hf, h.deriv_zero ht])
  have key := ibp_half_line ha hfc.continuousWithinAt (by simp [hf]) hd hint hint0 hlim
  show ‖∫ t in Ioi (0 : ℝ), f t * Complex.exp (Complex.I * a * t)‖ ≤ _
  rw [key, norm_mul]
  have hinv : ‖-(Complex.I * (a : ℂ))⁻¹‖ = 1 / |a| := by
    simp [norm_inv, Real.norm_eq_abs]
  rw [hinv]
  calc 1 / |a| * ‖∫ t in Ioi (0 : ℝ), f' t * Complex.exp (Complex.I * a * t)‖ ≤ 1 / |a| * (3 * M * ∫ t in Ioi (0 : ℝ), fresnelDom t) := by
        gcongr
    _ = _ := by ring


lemma integrableOn_mul_expI {g : ℝ → ℂ} {a : ℝ} (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun t : ℝ => g t * Complex.exp (Complex.I * a * t)) (Ioi 0) := by
  have hnorm_exp : ∀ t : ℝ, ‖Complex.exp (Complex.I * a * t)‖ = 1 := fun t => by
    rw [show Complex.I * (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  exact hg.norm.mono' (hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ => Complex.exp (Complex.I * a * t)).aestronglyMeasurable)
    (ae_of_all _ fun t => by rw [norm_mul, hnorm_exp, mul_one])

/-- The model integral: `∫₀^∞ t^{-1/2} e^{-t} e^{iat} dt = √(π/(1 - ia))`. -/
lemma integral_inv_sqrt_exp (a : ℝ) :
    ∫ t in Ioi (0 : ℝ), (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (Complex.exp (-(t : ℂ)) * Complex.exp (Complex.I * a * t)) =
      sqrtPiDiv (1 - Complex.I * a) := by
  have hb : 0 < (1 - Complex.I * (a : ℂ)).re := by simp
  rw [sqrtPiDiv, ← integral_rpow_neg_half_exp hb]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow, ← Complex.exp_add]
  congr 2
  ring_nf


lemma norm_cexp_neg_real (t : ℝ) : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
  rw [Complex.norm_exp]; simp

lemma alg_aux (M t : ℝ) (ht : 0 < t) :
    2 * M * t * (1 / (2 * Real.sqrt t) / (Real.sqrt t) ^ 2) = M * (Real.sqrt t)⁻¹ ∧
      2 * M * t * (Real.sqrt t)⁻¹ = 2 * M * Real.sqrt t := by
  have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  generalize Real.sqrt t = u at hu h2 ⊢
  subst h2
  constructor <;> field_simp

/-- Second integration by parts and the model integral:
`∫₀^∞ φ t^{-1/2} e^{iat} dt = φ(0) √(π/(1 - ia)) + O(M/|a|)`. -/
lemma HalfLineData.termK {φ : ℝ → ℂ} {M : ℝ} (h : HalfLineData φ M) {a : ℝ} (ha : a ≠ 0) :
    IntegrableOn (fun t : ℝ => φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) (Ioi 0) ∧
    ‖(∫ t in Ioi (0 : ℝ), φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * a * t)) -
        φ 0 * sqrtPiDiv (1 - Complex.I * a)‖ ≤ (6 * M * ∫ t in Ioi (0 : ℝ), fresnelDom t) / |a| := by
  have hM := h.M_nonneg
  set ψ : ℝ → ℂ := fun t => φ t - φ 0 * Complex.exp (-(t : ℂ)) with hψ
  set ψ' : ℝ → ℂ := fun t => deriv φ t + φ 0 * Complex.exp (-(t : ℂ)) with hψ'
  set f : ℝ → ℂ := fun t => ψ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) with hf
  set f' : ℝ → ℂ := fun t => ψ' t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) +
    ψ t * ((-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2 : ℝ) : ℂ) with hf'
  have hψd : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ))) (Complex.exp (-(t : ℂ)) * (-1)) t := by
      have := (hasDerivAt_id t).ofReal_comp.neg.cexp
      simpa using this
    exact ((h.hasDeriv t).sub (h1.const_mul (φ 0))).congr_deriv (by simp [hψ'])
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hexp1 : ∀ t : ℝ, 0 ≤ t → ‖Complex.exp (-(t : ℂ))‖ ≤ 1 := fun t ht => by
    rw [norm_cexp_neg_real]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hψ'b : ∀ t : ℝ, 0 ≤ t → ‖ψ' t‖ ≤ 2 * M := fun t ht => by
    refine (norm_add_le _ _).trans ?_
    have h1 := h.b1 t ht
    have h2 : ‖φ 0 * Complex.exp (-(t : ℂ))‖ ≤ M := by
      rw [norm_mul]; calc _ ≤ M * 1 := mul_le_mul (h.b0 0 le_rfl) (hexp1 t ht) (norm_nonneg _) hM
        _ = M := mul_one M
    linarith
  have hψb : ∀ t : ℝ, 0 ≤ t → ‖ψ t‖ ≤ 2 * M * t := fun t ht => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ψ) (f' := ψ') (s := Ici (0 : ℝ))
      (fun x _ => (hψd x).hasDerivWithinAt) (fun x hx => hψ'b x hx) (convex_Ici 0) (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht)
    simpa [hψ0, Real.norm_of_nonneg ht] using this
  have hψtail : ∀ t : ℝ, 1 < t → ‖ψ t‖ ≤ M * Real.exp (-t) ∧ ‖ψ' t‖ ≤ M * Real.exp (-t) := fun t ht => by
    have h1 : ‖φ 0 * Complex.exp (-(t : ℂ))‖ ≤ M * Real.exp (-t) := by
      rw [norm_mul, norm_cexp_neg_real]; exact mul_le_mul_of_nonneg_right (h.b0 0 le_rfl) (Real.exp_pos _).le
    refine ⟨?_, ?_⟩
    · simpa [hψ, h.supp t ht] using h1
    · simpa [hψ', h.deriv_zero ht] using h1
  have hnorm_inv : ∀ t : ℝ, ‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt t)⁻¹ := fun t => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hnorm_dinv : ∀ t : ℝ, ‖((-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2 : ℝ) : ℂ)‖ = 1 / (2 * Real.sqrt t) / (Real.sqrt t) ^ 2 := fun t => by
    rw [Complex.norm_real, Real.norm_eq_abs, neg_div, abs_neg, abs_of_nonneg (by positivity)]
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun t => (hψd t).continuousAt
  have hfm : Measurable f := by
    refine Measurable.mul hψc.measurable ?_
    fun_prop
  have hf'm : Measurable f' := by
    refine Measurable.add (Measurable.mul (by simp only [hψ']; exact h.continuous_deriv.measurable.add (by fun_prop)) (by fun_prop))
      (Measurable.mul hψc.measurable (by fun_prop))
  -- domination of `f'`
  have hdom' : ∀ t ∈ Ioi (0 : ℝ), ‖f' t‖ ≤ (6 * M) * fresnelDom t := fun t ht => by
    have ht0 : 0 < t := ht
    have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have ht2 : t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht0.le).symm
    have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
    have hnn : ‖f' t‖ ≤ ‖ψ' t‖ * (Real.sqrt t)⁻¹ + ‖ψ t‖ * (1 / (2 * Real.sqrt t) / (Real.sqrt t) ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, hnorm_inv, hnorm_dinv]
    rcases le_or_gt t 1 with ht1 | ht1
    · have hexp := exp_neg_half_ge ht1
      have h1 := (alg_aux M t ht0).1
      have h2 := mul_le_mul (hψ'b t ht0.le) le_rfl hinv.le (by positivity : (0 : ℝ) ≤ 2 * M)
      have h3 := mul_le_mul_of_nonneg_right (hψb t ht0.le) (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.sqrt t) / (Real.sqrt t) ^ 2)
      unfold fresnelDom
      nlinarith [mul_nonneg hM hinv.le, mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le)]
    · have hu1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht1.le
      obtain ⟨hb1, hb2⟩ := hψtail t ht1
      have hexpt : Real.exp (-t) ≤ Real.exp (-t / 2) := Real.exp_le_exp.mpr (by linarith)
      have hq : 1 / (2 * Real.sqrt t) / (Real.sqrt t) ^ 2 ≤ (Real.sqrt t)⁻¹ := by
        rw [div_div, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hu1)]
      have h2 := mul_le_mul hb2 le_rfl hinv.le (by positivity : 0 ≤ M * Real.exp (-t))
      have h3 := mul_le_mul hb1 hq (by positivity) (by positivity : 0 ≤ M * Real.exp (-t))
      unfold fresnelDom
      have : M * Real.exp (-t) * (Real.sqrt t)⁻¹ ≤ M * Real.exp (-t / 2) * (Real.sqrt t)⁻¹ := by gcongr
      nlinarith [mul_nonneg hM hinv.le, mul_nonneg (mul_nonneg hM hinv.le) (Real.exp_pos (-t / 2)).le]
  -- domination of `f`
  have hdom0 : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ (4 * M) * fresnelDom t := fun t ht => by
    have ht0 : 0 < t := ht
    have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have ht2 : t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht0.le).symm
    have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
    have hn : ‖f t‖ = ‖ψ t‖ * (Real.sqrt t)⁻¹ := by rw [hf]; dsimp only; rw [norm_mul, hnorm_inv]
    rw [hn]
    rcases le_or_gt t 1 with ht1 | ht1
    · have hexp := exp_neg_half_ge ht1
      have hu1 := sqrt_le_inv_sqrt ht0 ht1
      have h1 := (alg_aux M t ht0).2
      have h2 := mul_le_mul_of_nonneg_right (hψb t ht0.le) hinv.le
      unfold fresnelDom
      nlinarith [mul_nonneg hM hinv.le, mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le), mul_le_mul_of_nonneg_left hu1 hM]
    · obtain ⟨hb1, _⟩ := hψtail t ht1
      have hexpt : Real.exp (-t) ≤ Real.exp (-t / 2) := Real.exp_le_exp.mpr (by linarith)
      have h2 := mul_le_mul_of_nonneg_right hb1 hinv.le
      unfold fresnelDom
      have : M * Real.exp (-t) * (Real.sqrt t)⁻¹ ≤ M * Real.exp (-t / 2) * (Real.sqrt t)⁻¹ := by gcongr
      nlinarith [mul_nonneg hM hinv.le, mul_nonneg (mul_nonneg hM hinv.le) (Real.exp_pos (-t / 2)).le]
  have hint' := (norm_integral_exp_le_of_dom (a := a) hf'm.aestronglyMeasurable hdom')
  have hint0 : IntegrableOn f (Ioi 0) :=
    (integrableOn_fresnelDom.const_mul (4 * M)).mono' hfm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hdom0))
  -- boundary behaviour of `f`
  have hf0 : f 0 = 0 := by simp [hf, hψ0]
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have hb : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ 2 * M * Real.sqrt t := fun t ht => by
      rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with h0 | ht0
      · subst h0; simp [hf0]
      · have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
        have ht2 : t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht0.le).symm
        have hn : ‖f t‖ = ‖ψ t‖ * (Real.sqrt t)⁻¹ := by rw [hf]; dsimp only; rw [norm_mul, hnorm_inv]
        rw [hn]
        calc ‖ψ t‖ * (Real.sqrt t)⁻¹ ≤ 2 * M * t * (Real.sqrt t)⁻¹ := mul_le_mul_of_nonneg_right (hψb t ht0.le) (inv_pos.mpr hu).le
          _ = 2 * M * Real.sqrt t := (alg_aux M t ht0).2
    have hlim0 : Tendsto (fun t : ℝ => 2 * M * Real.sqrt t) (𝓝[Ici 0] 0) (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto (0 : ℝ)).const_mul (2 * M)).mono_left (nhdsWithin_le_nhds (s := Ici (0 : ℝ)))
    have : Tendsto f (𝓝[Ici 0] 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) (eventually_nhdsWithin_of_forall hb) hlim0)
    rw [ContinuousWithinAt, hf0]; exact this
  have hlim : Tendsto f atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hb : ∀ᶠ t : ℝ in atTop, ‖f t‖ ≤ M * Real.exp (-t) := (Filter.eventually_gt_atTop 1).mono fun t ht => by
      have hu1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht.le
      have hinv : (Real.sqrt t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
      have hn : ‖f t‖ = ‖ψ t‖ * (Real.sqrt t)⁻¹ := by rw [hf]; dsimp only; rw [norm_mul, hnorm_inv]
      rw [hn]
      calc ‖ψ t‖ * (Real.sqrt t)⁻¹ ≤ M * Real.exp (-t) * 1 :=
            mul_le_mul (hψtail t ht).1 hinv (inv_pos.mpr (lt_of_lt_of_le one_pos hu1)).le (by positivity)
        _ = _ := mul_one _
    have h0 : Tendsto (fun t : ℝ => M * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul M)
    exact squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) hb h0
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := fun t ht => by
    have ht0 : 0 < t := ht
    have hu : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have h1 : HasDerivAt (fun s : ℝ => (((Real.sqrt s)⁻¹ : ℝ) : ℂ)) ((-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2 : ℝ) : ℂ) t :=
      ((Real.hasDerivAt_sqrt ht0.ne').inv hu).ofReal_comp
    exact (hψd t).mul h1
  have key := ibp_half_line ha hcont hf0 hd hint'.1 hint0 hlim
  have hnorm_exp : ∀ t : ℝ, ‖Complex.exp (Complex.I * a * t)‖ = 1 := fun t => by
    rw [show Complex.I * (a : ℂ) * (t : ℂ) = ((a * t : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hmodel : IntegrableOn (fun t : ℝ => (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (Complex.exp (-(t : ℂ)) * Complex.exp (Complex.I * a * t))) (Ioi 0) := by
    refine (integrableOn_fresnelDom.const_mul 1).mono' (Measurable.aestronglyMeasurable (by fun_prop))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht0 : 0 < t := ht
    rw [norm_mul, norm_mul, hnorm_inv, hnorm_exp, norm_cexp_neg_real, mul_one, one_mul]
    unfold fresnelDom
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (inv_nonneg.mpr (Real.sqrt_nonneg t))
  have hphi : IntegrableOn (fun t : ℝ => φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ)) (Ioi 0) := by
    refine (integrableOn_fresnelDom.const_mul (2 * M)).mono'
      (Measurable.aestronglyMeasurable (Measurable.mul h.contDiff.continuous.measurable (by fun_prop)))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht0 : 0 < t := ht
    have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
    rw [norm_mul, hnorm_inv]
    rcases le_or_gt t 1 with ht1 | ht1
    · have hexp := exp_neg_half_ge ht1
      unfold fresnelDom
      nlinarith [mul_le_mul_of_nonneg_right (h.b0 t ht0.le) hinv.le, mul_nonneg hM hinv.le,
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le)]
    · simp only [h.supp t ht1, norm_zero, zero_mul]
      exact mul_nonneg (by positivity) (fresnelDom_nonneg t)
  refine ⟨hphi, ?_⟩
  have hsplit : ∀ t : ℝ, φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * a * t) =
      f t * Complex.exp (Complex.I * a * t) +
        φ 0 * ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (Complex.exp (-(t : ℂ)) * Complex.exp (Complex.I * a * t))) := fun t => by
    simp only [hf, hψ]; ring
  have hsum : ∫ t in Ioi (0 : ℝ), φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * a * t) =
      (∫ t in Ioi (0 : ℝ), f t * Complex.exp (Complex.I * a * t)) + φ 0 * sqrtPiDiv (1 - Complex.I * a) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hsplit t), integral_add (integrableOn_mul_expI hint0) (hmodel.const_mul (φ 0)),
      integral_const_mul, integral_inv_sqrt_exp]
  rw [hsum, add_sub_cancel_right, key, norm_mul]
  have hinv' : ‖-(Complex.I * (a : ℂ))⁻¹‖ = 1 / |a| := by
    simp [norm_inv, Real.norm_eq_abs]
  rw [hinv']
  calc 1 / |a| * ‖∫ t in Ioi (0 : ℝ), f' t * Complex.exp (Complex.I * a * t)‖ ≤ 1 / |a| * (6 * M * ∫ t in Ioi (0 : ℝ), fresnelDom t) := by
        gcongr; exact hint'.2
    _ = _ := by ring


lemma HalfLineData.integrableOn_deriv_sqrt {φ : ℝ → ℂ} {M : ℝ} (h : HalfLineData φ M) :
    IntegrableOn (fun t : ℝ => deriv φ t * (Real.sqrt t : ℂ)) (Ioi 0) := by
  have hM := h.M_nonneg
  refine (integrableOn_fresnelDom.const_mul (2 * M)).mono'
    (h.continuous_deriv.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  have ht0 : 0 < t := ht
  have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le]
  rcases le_or_gt t 1 with ht1 | ht1
  · have hexp := exp_neg_half_ge ht1
    have hu1 := sqrt_le_inv_sqrt ht0 ht1
    unfold fresnelDom
    nlinarith [mul_le_mul (h.b1 t ht0.le) hu1 hu.le hM, mul_nonneg hM hinv.le,
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le)]
  · simp only [h.deriv_zero ht1, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (fresnelDom_nonneg t)

lemma HalfLineData.integrableOn_sqrt {φ : ℝ → ℂ} {M : ℝ} (h : HalfLineData φ M) :
    IntegrableOn (fun t : ℝ => φ t * (Real.sqrt t : ℂ)) (Ioi 0) := by
  have hM := h.M_nonneg
  refine (integrableOn_fresnelDom.const_mul (2 * M)).mono'
    (h.contDiff.continuous.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  have ht0 : 0 < t := ht
  have hu : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hinv : 0 < (Real.sqrt t)⁻¹ := inv_pos.mpr hu
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le]
  rcases le_or_gt t 1 with ht1 | ht1
  · have hexp := exp_neg_half_ge ht1
    have hu1 := sqrt_le_inv_sqrt ht0 ht1
    unfold fresnelDom
    nlinarith [mul_le_mul (h.b0 t ht0.le) hu1 hu.le hM, mul_nonneg hM hinv.le,
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hM hinv.le)]
  · simp only [h.supp t ht1, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (fresnelDom_nonneg t)

/-- **Half-line branch integral**: for `|a| ≥ 1`,
`∫₀^∞ φ(t) √t e^{iat} dt = (i / 2a) φ(0) √(π / (-ia)) + O((6D + 1) M / a²)`, `D = ∫₀^∞ t^{-1/2} e^{-t/2} dt`. -/
theorem HalfLineData.half_line {φ : ℝ → ℂ} {M : ℝ} (h : HalfLineData φ M) {a : ℝ} (ha : 1 ≤ |a|) :
    ‖(∫ t in Ioi (0 : ℝ), φ t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * a * t)) -
        (Complex.I / (2 * a)) * φ 0 * sqrtPiDiv (-(Complex.I * a))‖ ≤
      (6 * (∫ t in Ioi (0 : ℝ), fresnelDom t) + 1) * M / a ^ 2 := by
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha; linarith
  have hM := h.M_nonneg
  set D : ℝ := ∫ t in Ioi (0 : ℝ), fresnelDom t with hD
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_Ioi fun t _ => fresnelDom_nonneg t
  obtain ⟨hphi, hK⟩ := h.termK ha0
  have hT1 := h.term1 ha0
  set f : ℝ → ℂ := fun t => φ t * (Real.sqrt t : ℂ) with hf
  set f' : ℝ → ℂ := fun t => deriv φ t * (Real.sqrt t : ℂ) + φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (1 / 2 : ℂ) with hf'
  have hfc : Continuous f := h.contDiff.continuous.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := fun t ht => by
    have ht0 : 0 < t := ht
    have hu : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    refine ((h.hasDeriv t).mul (hasDerivAt_ofReal_sqrt ht0)).congr_deriv ?_
    simp only [hf']
    push_cast
    field_simp
  have hint1 := h.integrableOn_deriv_sqrt
  have hint' : IntegrableOn f' (Ioi 0) := hint1.add (hphi.mul_const (1 / 2 : ℂ))
  have hlim : Tendsto f atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((Filter.eventually_gt_atTop 1).mono fun t ht => by simp [hf, h.supp t ht])
  have key := ibp_half_line ha0 hfc.continuousWithinAt (by simp [hf]) hd hint' h.integrableOn_sqrt hlim
  have hsplit : ∫ t in Ioi (0 : ℝ), f' t * Complex.exp (Complex.I * a * t) =
      (∫ t in Ioi (0 : ℝ), deriv φ t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * a * t)) +
        (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * a * t) := by
    rw [← integral_const_mul, ← integral_add (integrableOn_mul_expI hint1) ((integrableOn_mul_expI hphi).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf']; ring
  show ‖(∫ t in Ioi (0 : ℝ), f t * Complex.exp (Complex.I * a * t)) - _‖ ≤ _
  rw [key, hsplit]
  set P1 := ∫ t in Ioi (0 : ℝ), deriv φ t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * a * t)
  set K := ∫ t in Ioi (0 : ℝ), φ t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * a * t)
  set S1 := sqrtPiDiv (1 - Complex.I * a)
  set S0 := sqrtPiDiv (-(Complex.I * a))
  have hia : (Complex.I * (a : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ha0)
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0
  have hid : -(Complex.I * (a : ℂ))⁻¹ * (P1 + 1 / 2 * K) - Complex.I / (2 * a) * φ 0 * S0 =
      (Complex.I / a) * P1 + (Complex.I / (2 * a)) * ((K - φ 0 * S1) + φ 0 * (S1 - S0)) := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hid]
  have hS := norm_sqrtPiDiv_sub_le ha0
  have hnI : ‖Complex.I / (a : ℂ)‖ = 1 / |a| := by simp [Real.norm_eq_abs]
  have hnI2 : ‖Complex.I / (2 * (a : ℂ))‖ = 1 / (2 * |a|) := by simp [Real.norm_eq_abs]
  have hapos : 0 < |a| := abs_pos.mpr ha0
  have hsq : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have hpi : Real.sqrt Real.pi ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hφ0 : ‖φ 0‖ ≤ M := h.b0 0 le_rfl
  have hpow : |a| ^ (-(3 / 2 : ℝ)) ≤ 1 / |a| := by
    calc |a| ^ (-(3 / 2 : ℝ)) ≤ |a| ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
      _ = 1 / |a| := by rw [Real.rpow_neg_one, one_div]
  have hY : ‖S1 - S0‖ ≤ 1 / |a| := by
    refine hS.trans ?_
    calc (1 / 2) * Real.sqrt Real.pi * |a| ^ (-(3 / 2 : ℝ)) ≤ (1 / 2) * 2 * (1 / |a|) := by
          gcongr
      _ = 1 / |a| := by ring
  have hZ : ‖φ 0 * (S1 - S0)‖ ≤ M * (1 / |a|) := by
    rw [norm_mul]; exact mul_le_mul hφ0 hY (norm_nonneg _) hM
  have hP1 : ‖P1‖ ≤ 3 * M * D / |a| := hT1
  have hX : ‖K - φ 0 * S1‖ ≤ 6 * M * D / |a| := hK
  calc ‖Complex.I / (a : ℂ) * P1 + Complex.I / (2 * a) * ((K - φ 0 * S1) + φ 0 * (S1 - S0))‖
      ≤ ‖Complex.I / (a : ℂ)‖ * ‖P1‖ + ‖Complex.I / (2 * (a : ℂ))‖ * (‖K - φ 0 * S1‖ + ‖φ 0 * (S1 - S0)‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / |a| * (3 * M * D / |a|) + 1 / (2 * |a|) * (6 * M * D / |a| + M * (1 / |a|)) := by
        rw [hnI, hnI2]
        gcongr
    _ = (6 * M * D + M / 2) / |a| ^ 2 := by field_simp; ring
    _ ≤ (6 * D + 1) * M / a ^ 2 := by
        rw [hsq]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith


/-! ### The two sides of the branch point -/

/-- `(i t)^{1/2} = e^{iπ/4} √t` for `t > 0` (principal branch). -/
lemma cpow_I_mul_pos {t : ℝ} (ht : 0 < t) :
    (Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) = Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Real.sqrt t : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero Complex.I_ne_zero htc), mul_comm Complex.I, Complex.log_ofReal_mul ht Complex.I_ne_zero,
    Complex.log_I]
  have : (((Real.log t : ℝ) : ℂ) + ↑Real.pi / 2 * Complex.I) * (1 / 2) =
      ((Real.log t / 2 : ℝ) : ℂ) + Complex.I * (Real.pi / 4 : ℝ) := by push_cast; ring
  rw [this, Complex.exp_add, mul_comm, ← Complex.ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
  congr 3; ring

/-- `(-i t)^{1/2} = e^{-iπ/4} √t` for `t > 0` (principal branch). -/
lemma cpow_I_mul_neg {t : ℝ} (ht : 0 < t) :
    (Complex.I * ((-t : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Real.sqrt t : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hI : Complex.I * ((-t : ℝ) : ℂ) = (t : ℂ) * (-Complex.I) := by push_cast; ring
  rw [hI, Complex.cpow_def_of_ne_zero (mul_ne_zero htc (neg_ne_zero.mpr Complex.I_ne_zero)),
    Complex.log_ofReal_mul ht (neg_ne_zero.mpr Complex.I_ne_zero), Complex.log_neg_I]
  have : (((Real.log t : ℝ) : ℂ) + (-(↑Real.pi / 2) * Complex.I)) * (1 / 2) =
      ((Real.log t / 2 : ℝ) : ℂ) + -(Complex.I * (Real.pi / 4 : ℝ)) := by push_cast; ring
  rw [this, Complex.exp_add, mul_comm, ← Complex.ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
  congr 3; ring


lemma sqrtPiDiv_pos {A : ℝ} (hA : 0 < A) :
    sqrtPiDiv (-(Complex.I * (A : ℂ))) = Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Real.sqrt (Real.pi / A) : ℂ) := by
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have : (Real.pi : ℂ) / (-(Complex.I * (A : ℂ))) = Complex.I * ((Real.pi / A : ℝ) : ℂ) := by
    push_cast; field_simp; simp [Complex.I_sq]
  unfold sqrtPiDiv
  rw [this]
  exact cpow_I_mul_pos (div_pos Real.pi_pos hA)

lemma sqrtPiDiv_neg {A : ℝ} (hA : 0 < A) :
    sqrtPiDiv (-(Complex.I * ((-A : ℝ) : ℂ))) = Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Real.sqrt (Real.pi / A) : ℂ) := by
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have : (Real.pi : ℂ) / (-(Complex.I * ((-A : ℝ) : ℂ))) = Complex.I * ((-(Real.pi / A) : ℝ) : ℂ) := by
    push_cast; field_simp; simp [Complex.I_sq]
  unfold sqrtPiDiv
  rw [this]
  exact cpow_I_mul_neg (div_pos Real.pi_pos hA)

lemma exp_quarter_sq : Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) = Complex.I := by
  rw [← Complex.exp_add, show Complex.I * ((Real.pi / 4 : ℝ) : ℂ) + Complex.I * ((Real.pi / 4 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

lemma exp_neg_quarter_sq : Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) = -Complex.I := by
  rw [← Complex.exp_add, show -(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) + -(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) = -((Real.pi : ℂ) / 2 * Complex.I) by
    push_cast; ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp

lemma main_terms {A : ℝ} (hA : 0 < A) (z : ℂ) :
    Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * ((Complex.I / (2 * (A : ℂ))) * z *
        (Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Real.sqrt (Real.pi / A) : ℂ))) +
      Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * ((Complex.I / (2 * ((-A : ℝ) : ℂ))) * z *
        (Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Real.sqrt (Real.pi / A) : ℂ))) =
      -(((Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * z) := by
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have e1 := exp_quarter_sq
  have e2 := exp_neg_quarter_sq
  have hs : Real.sqrt (Real.pi / A) = Real.sqrt Real.pi * A ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_eq_rpow A, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hA32 : A ^ (-(3 / 2 : ℝ)) = A⁻¹ * A ^ (-(1 / 2 : ℝ)) := by
    rw [show -(3 / 2 : ℝ) = -1 + -(1 / 2) by norm_num, Real.rpow_add hA, Real.rpow_neg_one]
  rw [hs, hA32]
  push_cast at e1 e2 ⊢
  generalize ((Real.sqrt Real.pi : ℝ) : ℂ) = p
  generalize ((A ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = q
  generalize Complex.exp (Complex.I * ((Real.pi : ℂ) / 4)) = x at e1 ⊢
  generalize Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 4))) = y at e2 ⊢
  have : x * (Complex.I / (2 * A) * z * (x * (p * q))) + y * (Complex.I / (2 * -A) * z * (y * (p * q))) =
      (Complex.I / (2 * A) * z * p * q) * (x * x) - (Complex.I / (2 * A) * z * p * q) * (y * y) := by
    field_simp
    ring
  rw [this, e1, e2]
  field_simp
  simp [Complex.I_sq]
  ring


lemma norm_cpow_I_mul_le_one {v : ℝ} (hv : |v| ≤ 1) : ‖(Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ)‖ ≤ 1 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_real, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact Real.rpow_le_one (abs_nonneg v) hv (by norm_num)

/-- **Branch-point term** (`u1c:U3`(3), Piece C, item 3): for `φ ∈ C²` supported in `[-1, 1]` with
`‖φ‖, ‖φ'‖, ‖φ''‖ ≤ M` and `A ≥ 1`,
`∫_ℝ φ(v) (i v)^{1/2} e^{iAv} dv = -√π φ(0) A^{-3/2} + O((12 D + 2) M A^{-2})`,
`D = ∫₀^∞ t^{-1/2} e^{-t/2} dt` (an absolute constant). -/
theorem fresnel_branch {φ : ℝ → ℂ} {M : ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ v : ℝ, 1 < |v| → φ v = 0)
    (b0 : ∀ v, ‖φ v‖ ≤ M) (b1 : ∀ v, ‖deriv φ v‖ ≤ M) (b2 : ∀ v, ‖deriv (deriv φ) v‖ ≤ M) {A : ℝ} (hA : 1 ≤ A) :
    ‖(∫ v : ℝ, φ v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * A * v)) +
        ((Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * φ 0‖ ≤
      (12 * (∫ t in Ioi (0 : ℝ), fresnelDom t) + 2) * M / A ^ 2 := by
  have hAp : 0 < A := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (b0 0)
  set D : ℝ := ∫ t in Ioi (0 : ℝ), fresnelDom t with hD
  set F : ℝ → ℂ := fun v => φ v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * A * v) with hF
  have hdp : HalfLineData φ M := ⟨hφ, fun t ht => hsupp t (by rwa [abs_of_pos (by linarith)]), fun t _ => b0 t, fun t _ => b1 t, fun t _ => b2 t⟩
  set φ' : ℝ → ℂ := fun t => φ (-t) with hφ'
  have hd1 : ∀ t, deriv φ' t = -deriv φ (-t) := fun t => deriv_comp_neg φ t
  have hd2 : ∀ t, deriv (deriv φ') t = deriv (deriv φ) (-t) := fun t => by
    have : deriv φ' = fun t => -deriv φ (-t) := funext hd1
    rw [this, deriv.fun_neg, deriv_comp_neg (deriv φ) t, neg_neg]
  have hdn : HalfLineData φ' M := ⟨hφ.comp contDiff_neg, fun t ht => hsupp (-t) (by rw [abs_neg, abs_of_pos (by linarith)]; exact ht),
    fun t _ => b0 (-t), fun t _ => by rw [hd1, norm_neg]; exact b1 _, fun t _ => by rw [hd2]; exact b2 _⟩
  -- integrability of `F`
  have hFmeas : Measurable F := by
    have := hφ.continuous.measurable
    simp only [hF]
    fun_prop
  have hFint : Integrable F := by
    refine ((integrableOn_const (μ := volume) (s := Icc (-1 : ℝ) 1) (C := M) (by simp) ).integrable_indicator measurableSet_Icc).mono'
      hFmeas.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    by_cases hv : |v| ≤ 1
    · have hvI : v ∈ Icc (-1 : ℝ) 1 := abs_le.mp hv |> fun h => ⟨h.1, h.2⟩
      rw [Set.indicator_of_mem hvI]
      have hn : ‖Complex.exp (Complex.I * A * v)‖ = 1 := by
        rw [show Complex.I * (A : ℂ) * (v : ℂ) = ((A * v : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
      simp only [hF, norm_mul, hn, mul_one]
      calc ‖φ v‖ * ‖(Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ)‖ ≤ M * 1 :=
            mul_le_mul (b0 v) (norm_cpow_I_mul_le_one hv) (norm_nonneg _) hM
        _ = M := mul_one M
    · rw [Set.indicator_of_notMem (fun hh => hv (abs_le.mpr ⟨hh.1, hh.2⟩))]
      simp [hF, hsupp v (not_le.mp hv)]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi hFint.integrableOn hFint.integrableOn (b := (0 : ℝ))
  have hpos : ∫ v in Ioi (0 : ℝ), F v =
      Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * ∫ t in Ioi (0 : ℝ), φ t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * A * t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hF]
    rw [cpow_I_mul_pos ht]; ring
  have hneg : ∫ v in Iic (0 : ℝ), F v =
      Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * ∫ t in Ioi (0 : ℝ), φ' t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * ((-A : ℝ) : ℂ) * t) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) F
    rw [neg_zero] at h
    rw [← h, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hF, hφ']
    rw [cpow_I_mul_neg ht]
    push_cast
    ring_nf
  have hHp := hdp.half_line (a := A) (by rwa [abs_of_pos hAp])
  have hHm := hdn.half_line (a := -A) (by rw [abs_neg, abs_of_pos hAp]; exact hA)
  rw [sqrtPiDiv_pos hAp] at hHp
  rw [sqrtPiDiv_neg hAp] at hHm
  have hmain := main_terms hAp (φ 0)
  have hφ'0 : φ' 0 = φ 0 := by simp [hφ']
  rw [hφ'0] at hHm
  set Hp := ∫ t in Ioi (0 : ℝ), φ t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * A * t)
  set Hm := ∫ t in Ioi (0 : ℝ), φ' t * (Real.sqrt t : ℂ) * Complex.exp (Complex.I * ((-A : ℝ) : ℂ) * t)
  have hJ : ∫ v : ℝ, F v = Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * Hm + Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * Hp := by
    rw [← hsplit, hpos, hneg]
  have hu1 : ‖Complex.exp (Complex.I * (Real.pi / 4 : ℝ))‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hu2 : ‖Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ)))‖ = 1 := by
    rw [show -(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  show ‖(∫ v : ℝ, F v) + _‖ ≤ _
  rw [hJ]
  have hid : Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * Hm + Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * Hp +
      ((Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * φ 0 =
      Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Hp - Complex.I / (2 * (A : ℂ)) * φ 0 *
        (Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Real.sqrt (Real.pi / A) : ℂ))) +
      Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Hm - Complex.I / (2 * ((-A : ℝ) : ℂ)) * φ 0 *
        (Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Real.sqrt (Real.pi / A) : ℂ))) := by
    linear_combination hmain
  rw [hid]
  have hA2 : (-A) ^ 2 = A ^ 2 := by ring
  rw [hA2] at hHm
  calc _ ≤ ‖Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Hp - Complex.I / (2 * (A : ℂ)) * φ 0 *
        (Complex.exp (Complex.I * (Real.pi / 4 : ℝ)) * (Real.sqrt (Real.pi / A) : ℂ)))‖ +
      ‖Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Hm - Complex.I / (2 * ((-A : ℝ) : ℂ)) * φ 0 *
        (Complex.exp (-(Complex.I * (Real.pi / 4 : ℝ))) * (Real.sqrt (Real.pi / A) : ℂ)))‖ := norm_add_le _ _
    _ ≤ (6 * D + 1) * M / A ^ 2 + (6 * D + 1) * M / A ^ 2 := by
        rw [norm_mul, norm_mul, hu1, hu2, one_mul, one_mul]
        exact add_le_add hHp hHm
    _ = _ := by ring

/-- info: 'FormalResearch.CohnElkies.ibp_half_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ibp_half_line
/-- info: 'FormalResearch.CohnElkies.integral_rpow_neg_half_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.integral_rpow_neg_half_exp
/-- info: 'FormalResearch.CohnElkies.norm_sqrtPiDiv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.norm_sqrtPiDiv_sub_le
/-- info: 'FormalResearch.CohnElkies.HalfLineData.term1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HalfLineData.term1
/-- info: 'FormalResearch.CohnElkies.HalfLineData.termK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HalfLineData.termK
/-- info: 'FormalResearch.CohnElkies.HalfLineData.half_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.HalfLineData.half_line
/-- info: 'FormalResearch.CohnElkies.fresnel_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fresnel_branch

end FormalResearch.CohnElkies
