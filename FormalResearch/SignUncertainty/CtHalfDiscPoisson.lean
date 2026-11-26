module

public import Mathlib
public import FormalResearch.Complex.HalfDiscPoisson

/-!
# `ct:dyadic` Part (2): the explicit half-disc Poisson kernel and its bounds

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` Part (2), equations `ct:Pdiam`, `ct:Parc`.
**Proved** (kernel algebra only).  With `A > 0`, `z ∈ D_+ = {|z| < A, Im z > 0}`, `y = Im z`:

* `pDiam A z t = (y/π)(A²-|z|²)(A²-t²) / (|z-t|²|A²-tz|²)` (the density on the diameter, `|t| < A`);
  `pDiam_eq`: `= (y/π)(|z-t|⁻² - A²|A²-tz|⁻²)`; `pDiam_le`: `0 ≤ pDiam ≤ y/(π|z-t|²) ≤ 1/(π|z-t|)`.
* `pArc A z θ = (2/π) A y (A²-|z|²) sin θ / (|z-Ae^{iθ}|²|z-Ae^{-iθ}|²)` (`A · P` on the arc);
  `pArc_le`: for `|z| ≤ A/4`, `0 ≤ pArc ≤ 3 (y/A) sin θ` (`512/(81π) ≤ 3`).

The Poisson representation of a function continuous on `closure D_+` and holomorphic in `D_+` by these kernels is
`ct_halfDisc_poisson` (from `Complex/HalfDiscPoisson`); the area integral `r_*⁻¹ ∫_{N_+} P(z,t) dA ≤ 6` and the Lipschitz
bound `|P(z,t) - P(z,0)| ≤ 123 r_*⁻²|t|` are NOT formalised here.
-/

@[expose] public section

open Complex Set intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty.CtHalfDiscPoisson

/-- Poisson density of `D_+` on the diameter. -/
noncomputable def pDiam (A : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  z.im / π * ((A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2)) /
    (Complex.normSq (z - t) * Complex.normSq (((A : ℂ) ^ 2) - t * z))

/-- `A ·` Poisson density of `D_+` on the arc `A e^{iθ}`. -/
noncomputable def pArc (A : ℝ) (z : ℂ) (θ : ℝ) : ℝ :=
  2 / π * (A * z.im * (A ^ 2 - Complex.normSq z) * Real.sin θ) /
    (Complex.normSq (z - A * Complex.exp (θ * Complex.I)) *
      Complex.normSq (z - A * Complex.exp (-(θ : ℂ) * Complex.I)))

lemma normSq_identity (A : ℝ) (z : ℂ) (t : ℝ) :
    Complex.normSq (((A : ℂ) ^ 2) - t * z) =
      A ^ 2 * Complex.normSq (z - t) + (A ^ 2 - t ^ 2) * (A ^ 2 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_two]
  ring

lemma pDiam_eq {A : ℝ} {z : ℂ} {t : ℝ} (hz : z ≠ t) (hden : ((A : ℂ) ^ 2) - t * z ≠ 0) :
    pDiam A z t = z.im / π * (1 / Complex.normSq (z - t) - A ^ 2 / Complex.normSq (((A : ℂ) ^ 2) - t * z)) := by
  have h1 : Complex.normSq (z - t) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact sub_ne_zero.mpr hz
  have h2 : Complex.normSq (((A : ℂ) ^ 2) - t * z) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact hden
  have hid := normSq_identity A z t
  have hX : (A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2) =
      Complex.normSq (((A : ℂ) ^ 2) - t * z) - A ^ 2 * Complex.normSq (z - t) := by linarith
  unfold pDiam
  rw [hX]
  generalize Complex.normSq (((A : ℂ) ^ 2) - t * z) = N at *
  generalize Complex.normSq (z - t) = M at *
  field_simp

lemma pDiam_le {A : ℝ} {z : ℂ} {t : ℝ} (hy : 0 < z.im) (hzA : Complex.normSq z < A ^ 2)
    (htA : |t| < A) :
    0 ≤ pDiam A z t ∧ pDiam A z t ≤ z.im / (π * Complex.normSq (z - t)) ∧
      pDiam A z t ≤ 1 / (π * ‖z - t‖) := by
  have hpi := Real.pi_pos
  have hA2 : t ^ 2 < A ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_lt.mp htA]) (abs_lt.mp htA).2
    nlinarith [sq_abs t, abs_nonneg t]
  have hz0 : 0 < Complex.normSq (z - t) := by
    rw [Complex.normSq_pos, Ne, sub_eq_zero]
    intro h; rw [h] at hy; simp at hy
  have hid := normSq_identity A z t
  have hP : 0 < (A ^ 2 - t ^ 2) * (A ^ 2 - Complex.normSq z) := mul_pos (by linarith) (by linarith)
  have hd : 0 < Complex.normSq (((A : ℂ) ^ 2) - t * z) := by
    rw [hid]; have : 0 ≤ A ^ 2 * Complex.normSq (z - t) := by positivity
    linarith
  have hnum : 0 ≤ z.im / π * ((A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2)) := by
    have : 0 ≤ (A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2) := by nlinarith
    positivity
  have h0 : 0 ≤ pDiam A z t := by unfold pDiam; positivity
  have hle : pDiam A z t ≤ z.im / (π * Complex.normSq (z - t)) := by
    unfold pDiam
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2) ≤ Complex.normSq (((A : ℂ) ^ 2) - t * z) := by
      rw [hid]; have : 0 ≤ A ^ 2 * Complex.normSq (z - t) := by positivity
      nlinarith
    have hy' : 0 ≤ z.im / π := by positivity
    calc z.im / π * ((A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2)) * (π * Complex.normSq (z - t))
        = z.im * ((A ^ 2 - Complex.normSq z) * (A ^ 2 - t ^ 2)) * Complex.normSq (z - t) := by
          field_simp
      _ ≤ z.im * Complex.normSq (((A : ℂ) ^ 2) - t * z) * Complex.normSq (z - t) := by gcongr
      _ = _ := by ring
  refine ⟨h0, hle, hle.trans ?_⟩
  have hn : 0 < ‖z - t‖ := by
    rw [norm_pos_iff, sub_ne_zero]; intro h; rw [h] at hy; simp at hy
  have hyle : z.im ≤ ‖z - t‖ := by
    have := Complex.abs_im_le_norm (z - t)
    simpa using (le_abs_self _).trans this
  have hsq : Complex.normSq (z - t) = ‖z - t‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
  rw [hsq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hpi hn]

lemma normSq_sub_arc_ge {A : ℝ} (hA : 0 < A) {z : ℂ} (hz : ‖z‖ ≤ A / 4) (w : ℂ) (hw : ‖w‖ = A) :
    (3 * A / 4) ^ 2 ≤ Complex.normSq (z - w) := by
  rw [Complex.normSq_eq_norm_sq]
  have h : A - A / 4 ≤ ‖z - w‖ := by
    have := norm_sub_norm_le w z
    rw [norm_sub_rev] at this
    linarith
  nlinarith

/-- `A · P_{D_+}(z, A e^{iθ}) ≤ 3 (y/A) sin θ` for `|z| ≤ A/4`, `θ ∈ [0, π]`. -/
lemma pArc_le {A : ℝ} (hA : 0 < A) {z : ℂ} (hy : 0 < z.im) (hz : ‖z‖ ≤ A / 4) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθπ : θ ≤ π) :
    0 ≤ pArc A z θ ∧ pArc A z θ ≤ 3 * (z.im / A) * Real.sin θ := by
  have hpi := Real.pi_pos
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ hθπ
  have hw1 : ‖(A : ℂ) * Complex.exp (θ * Complex.I)‖ = A := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, mul_one]
  have hw2 : ‖(A : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ = A := by
    have : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, mul_one]
  have hD1 := normSq_sub_arc_ge hA hz _ hw1
  have hD2 := normSq_sub_arc_ge hA hz _ hw2
  have hzA : Complex.normSq z ≤ (A / 4) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hAz : 0 ≤ A ^ 2 - Complex.normSq z := by nlinarith
  have hAz' : A ^ 2 - Complex.normSq z ≤ A ^ 2 := by linarith [Complex.normSq_nonneg z]
  have hpos : 0 < (3 * A / 4) ^ 2 := by positivity
  have hDD : (3 * A / 4) ^ 2 * (3 * A / 4) ^ 2 ≤ Complex.normSq (z - A * Complex.exp (θ * Complex.I)) *
      Complex.normSq (z - A * Complex.exp (-(θ : ℂ) * Complex.I)) := mul_le_mul hD1 hD2 hpos.le
        (lt_of_lt_of_le hpos hD1).le
  have hDDpos : 0 < Complex.normSq (z - A * Complex.exp (θ * Complex.I)) *
      Complex.normSq (z - A * Complex.exp (-(θ : ℂ) * Complex.I)) := lt_of_lt_of_le (by positivity) hDD
  have hnum : 0 ≤ 2 / π * (A * z.im * (A ^ 2 - Complex.normSq z) * Real.sin θ) := by positivity
  refine ⟨by unfold pArc; positivity, ?_⟩
  unfold pArc
  rw [div_le_iff₀ hDDpos]
  have h1 : 2 / π * (A * z.im * (A ^ 2 - Complex.normSq z) * Real.sin θ) ≤
      2 / π * (A * z.im * A ^ 2 * Real.sin θ) := by
    gcongr
  have h2 : 3 * (z.im / A) * Real.sin θ * ((3 * A / 4) ^ 2 * (3 * A / 4) ^ 2) ≤
      3 * (z.im / A) * Real.sin θ * (Complex.normSq (z - A * Complex.exp (θ * Complex.I)) *
      Complex.normSq (z - A * Complex.exp (-(θ : ℂ) * Complex.I))) := by
    gcongr
  refine h1.trans (le_trans ?_ h2)
  have hz0 : 0 ≤ z.im * Real.sin θ := mul_nonneg hy.le hsin
  have e : 3 * (z.im / A) * Real.sin θ * ((3 * A / 4) ^ 2 * (3 * A / 4) ^ 2) =
      (243 / 256) * A ^ 3 * (z.im * Real.sin θ) := by field_simp; ring
  rw [e]
  have e2 : 2 / π * (A * z.im * A ^ 2 * Real.sin θ) = (2 / π) * A ^ 3 * (z.im * Real.sin θ) := by ring
  rw [e2]
  have : 2 / π ≤ 243 / 256 := by
    rw [div_le_div_iff₀ hpi (by norm_num)]; nlinarith [Real.pi_gt_three]
  have hA3 : 0 ≤ A ^ 3 * (z.im * Real.sin θ) := by positivity
  nlinarith

/-- info: 'FormalResearch.SignUncertainty.CtHalfDiscPoisson.pDiam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pDiam_le

/-- info: 'FormalResearch.SignUncertainty.CtHalfDiscPoisson.pArc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pArc_le

lemma pDiam_eq_hdDiam (A : ℝ) (z : ℂ) (t : ℝ) : pDiam A z t = FormalResearch.HalfDiscCauchy.hdDiam A z t := rfl

lemma pArc_eq_hdArc (A : ℝ) (z : ℂ) (θ : ℝ) : pArc A z θ = FormalResearch.HalfDiscCauchy.hdArc A z θ := rfl

/-- **`ct:dyadic` Part (2), the Poisson representation on `D_+`** (`G` continuous on `closure D_+`, holomorphic in `D_+`):
`G(z) = ∫_{-A}^{A} P(z,t) G(t) dt + ∫_0^π (A P)(z,θ) G(A e^{iθ}) dθ` with the kernels `pDiam`, `pArc`
(`ct:Pdiam`, `ct:Parc`). -/
theorem ct_halfDisc_poisson {A : ℝ} (hA : 0 < A) {G : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ FormalResearch.HalfDiscCauchy.openHalfDisc A)
    (hc : ContinuousOn G (FormalResearch.HalfDiscCauchy.closedHalfDisc A))
    (hd : DifferentiableOn ℂ G (FormalResearch.HalfDiscCauchy.openHalfDisc A)) :
    G z = (∫ t in (-A)..A, (pDiam A z t : ℂ) * G (t : ℂ)) +
      ∫ θ in (0 : ℝ)..π, (pArc A z θ : ℂ) * G (A * Complex.exp (θ * I)) :=
  FormalResearch.HalfDiscCauchy.halfDisc_poisson hA hz hc hd

end FormalResearch.SignUncertainty.CtHalfDiscPoisson
