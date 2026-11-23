module

public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.CohnElkies.SaddleGeometry
public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The holomorphic edge phase on `D(0, 1)` (`mellin_airy_toolkit.tex` Lemma T.4(b); `u1co:O4`)

`Φ_L(τ) = L τ + ∫₀^τ log(tanh(π u / 2) / (π u / 2)) du` extends holomorphically to `|τ| < 1`:
in the variable `ζ = i τ`, `g(ζ) = log(tan(π ζ / 2) / (π ζ / 2))` is holomorphic on `|Re ζ| < 1`
because `q(ζ) = tan(π ζ / 2) / (π ζ / 2)` (with `q(0) = 1`) has `Re q > 0` there
(`tan_div_self_re_pos_halfStrip` on `0 ≤ Re ζ < 1`, evenness for `Re ζ < 0`).

Main declarations (all unconditional):
* `stripQ`, `differentiableOn_stripG`: `q` and holomorphy of `stripG` on the strip `|Re ζ| < 1`;
* `edgePrim`: the primitive of `stripG` on `D(0, 1)` with `edgePrim 0 = 0`; `stripS0Tilde_eq_edgePrim`;
* `edgePhiC L τ = L τ - i P(i τ)`: `hasDerivAt_edgePhiC`, `edgePhiC_ofReal` (agrees with the real
  `edgePhi`), `edgePhiC_neg` (odd), `edgePhiC_zero`, and the real-axis derivative
  `edgePhiC_deriv_ofReal` (`= edgePhiDeriv`).
-/

@[expose] public section

open Metric Set Filter Topology Complex
open scoped Real

namespace FormalResearch.CohnElkies

/-- `q(ζ) = tan(π ζ / 2) / (π ζ / 2)`, with `q(0) = 1`, as a holomorphic expression
(`dslope` of `ζ ↦ tan(π ζ / 2)` at `0`, divided by `π/2`). -/
noncomputable def stripQ (ζ : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2)) 0 ζ * (2 / (π : ℂ))

private lemma pi_ne_zero_c : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

lemma stripQ_of_ne {ζ : ℂ} (hζ : ζ ≠ 0) :
    stripQ ζ = Complex.tan ((π : ℂ) * ζ / 2) / ((π : ℂ) * ζ / 2) := by
  unfold stripQ
  rw [dslope_of_ne _ hζ, slope_def_field]
  simp only [mul_zero, zero_div, Complex.tan_zero, sub_zero, sub_zero]
  field_simp

lemma stripQ_zero : stripQ 0 = 1 := by
  unfold stripQ
  rw [dslope_same]
  have h : HasDerivAt (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2)) ((π : ℂ) / 2) 0 := by
    have harg : HasDerivAt (fun w : ℂ => (π : ℂ) * w / 2) ((π : ℂ) / 2) 0 :=
      (((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).div_const 2).congr_deriv (by simp)
    have := (Complex.hasDerivAt_tan (by simp : Complex.cos ((π : ℂ) * 0 / 2) ≠ 0)).comp (0 : ℂ) harg
    change HasDerivAt (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2)) _ 0 at this
    exact this.congr_deriv (by simp)
  rw [h.deriv]
  field_simp

lemma stripQ_even (ζ : ℂ) : stripQ (-ζ) = stripQ ζ := by
  by_cases hζ : ζ = 0
  · subst hζ; simp
  · rw [stripQ_of_ne hζ, stripQ_of_ne (neg_ne_zero.mpr hζ)]
    have : (π : ℂ) * -ζ / 2 = -((π : ℂ) * ζ / 2) := by ring
    rw [this, Complex.tan_neg, neg_div_neg_eq]

lemma stripG_eq_log_stripQ (ζ : ℂ) : stripG ζ = Complex.log (stripQ ζ) := by
  by_cases hζ : ζ = 0
  · subst hζ; simp [stripG, stripQ_zero]
  · simp [stripG, hζ, stripQ_of_ne hζ]

lemma stripG_even (ζ : ℂ) : stripG (-ζ) = stripG ζ := by
  rw [stripG_eq_log_stripQ, stripG_eq_log_stripQ, stripQ_even]

/-- `Re q > 0` on the strip `|Re ζ| < 1`. -/
lemma stripQ_re_pos {ζ : ℂ} (h : |ζ.re| < 1) : 0 < (stripQ ζ).re := by
  by_cases hζ : ζ = 0
  · subst hζ; simp [stripQ_zero]
  · rcases le_or_gt 0 ζ.re with h0 | h0
    · rw [stripQ_of_ne hζ]
      exact tan_div_self_re_pos_halfStrip h0 (by rwa [abs_of_nonneg h0] at h) hζ
    · rw [← stripQ_even]
      have hn : -ζ ≠ 0 := neg_ne_zero.mpr hζ
      rw [stripQ_of_ne hn]
      exact tan_div_self_re_pos_halfStrip (by simp; linarith) (by rw [abs_of_neg h0] at h; simpa using h) hn

lemma cos_pi_div_two_ne_zero {ζ : ℂ} (h : |ζ.re| < 1) : Complex.cos ((π : ℂ) * ζ / 2) ≠ 0 := by
  intro hc
  rw [Complex.cos_eq_zero_iff] at hc
  obtain ⟨k, hk⟩ := hc
  have hζ : ζ = 2 * k + 1 := by
    have : (π : ℂ) * ζ = (π : ℂ) * (2 * k + 1) := by
      have h2 : (π : ℂ) * ζ / 2 = (2 * k + 1) * π / 2 := hk
      linear_combination 2 * h2
    have := mul_left_cancel₀ pi_ne_zero_c this
    exact this
  have hre : ζ.re = 2 * k + 1 := by rw [hζ]; simp
  rw [hre] at h
  have h1 : (-1 : ℝ) < 2 * k + 1 ∧ (2 * k + 1 : ℝ) < 1 := abs_lt.mp h
  have hk0 : (k : ℝ) < 0 := by linarith [h1.2]
  have hk1 : (-1 : ℝ) < k := by linarith [h1.1]
  have : (k : ℤ) < 0 := by exact_mod_cast hk0
  have : (-1 : ℤ) < k := by exact_mod_cast hk1
  omega

/-- The open strip `|Re ζ| < 1`. -/
def edgeStrip : Set ℂ := {ζ : ℂ | |ζ.re| < 1}

lemma isOpen_edgeStrip : IsOpen edgeStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

lemma ball_subset_edgeStrip : ball (0 : ℂ) 1 ⊆ edgeStrip := fun ζ hζ => by
  rw [mem_ball_zero_iff] at hζ
  exact lt_of_le_of_lt (Complex.abs_re_le_norm ζ) hζ

lemma differentiableOn_stripQ : DifferentiableOn ℂ stripQ edgeStrip := by
  have hT : DifferentiableOn ℂ (fun w : ℂ => Complex.tan ((π : ℂ) * w / 2)) edgeStrip := fun ζ hζ => by
    have hcos := cos_pi_div_two_ne_zero hζ
    have harg : HasDerivAt (fun w : ℂ => (π : ℂ) * w / 2) ((π : ℂ) / 2) ζ :=
      (((hasDerivAt_id ζ).const_mul (π : ℂ)).div_const 2).congr_deriv (by simp)
    exact (((Complex.hasDerivAt_tan hcos).comp ζ harg).differentiableAt).differentiableWithinAt
  have h0 : (0 : ℂ) ∈ edgeStrip := by simp [edgeStrip]
  have := (differentiableOn_dslope (isOpen_edgeStrip.mem_nhds h0)).mpr hT
  exact this.mul_const _

/-- `g = stripG` is holomorphic on the strip `|Re ζ| < 1`. -/
lemma differentiableOn_stripG : DifferentiableOn ℂ stripG edgeStrip := by
  have : stripG = fun ζ => Complex.log (stripQ ζ) := funext stripG_eq_log_stripQ
  rw [this]
  intro ζ hζ
  exact (((differentiableOn_stripQ ζ hζ).differentiableAt (isOpen_edgeStrip.mem_nhds hζ)).clog
    (Complex.mem_slitPlane_iff.mpr (Or.inl (stripQ_re_pos hζ)))).differentiableWithinAt


/-! ### The primitive of `g` on `D(0, 1)` -/

lemma exists_edgePrim : ∃ P : ℂ → ℂ, P 0 = 0 ∧ ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt P (stripG z) z := by
  have h := (differentiableOn_stripG.mono ball_subset_edgeStrip).isExactOn_ball
  obtain ⟨g, hg0, hg⟩ := h.with_val_at 0 0
  exact ⟨g, hg0, hg⟩

/-- A primitive of `stripG` on `D(0, 1)` vanishing at `0`. -/
noncomputable def edgePrim : ℂ → ℂ := Classical.choose exists_edgePrim

lemma edgePrim_zero : edgePrim 0 = 0 := (Classical.choose_spec exists_edgePrim).1

lemma hasDerivAt_edgePrim {z : ℂ} (hz : ‖z‖ < 1) : HasDerivAt edgePrim (stripG z) z :=
  (Classical.choose_spec exists_edgePrim).2 z (by simpa using hz)

lemma continuousOn_stripG : ContinuousOn stripG edgeStrip := differentiableOn_stripG.continuousOn

/-- `S̃₀ = edgePrim` on `D(0, 1)`. -/
lemma stripS0Tilde_eq_edgePrim {ζ : ℂ} (hζ : ‖ζ‖ < 1) : stripS0Tilde ζ = edgePrim ζ := by
  unfold stripS0Tilde
  have hmem : ∀ s ∈ uIcc (0 : ℝ) 1, ‖(s : ℂ) * ζ‖ < 1 := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖ζ‖ ≤ 1 * ‖ζ‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ < 1 := by linarith
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => edgePrim ((s : ℂ) * ζ)) (stripG ((s : ℂ) * ζ) * ζ) s := fun s hs => by
    have h1 : HasDerivAt (fun w : ℂ => w * ζ) ζ (s : ℂ) := by
      simpa using (hasDerivAt_id (s : ℂ)).mul_const ζ
    have h2 := (hasDerivAt_edgePrim (hmem s hs)).comp (s : ℂ) h1
    exact (h2.comp_ofReal : HasDerivAt (fun y : ℝ => edgePrim ((y : ℂ) * ζ)) _ s)
  have hcont : ContinuousOn (fun s : ℝ => stripG ((s : ℂ) * ζ) * ζ) (uIcc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    refine continuousOn_stripG.comp (by fun_prop) fun s hs => ?_
    have := hmem s hs
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  rw [this]
  simp [edgePrim_zero]

lemma stripS0Tilde_neg (ζ : ℂ) : stripS0Tilde (-ζ) = -stripS0Tilde ζ := by
  unfold stripS0Tilde
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [mul_neg, stripG_even]

lemma edgePrim_neg {ζ : ℂ} (hζ : ‖ζ‖ < 1) : edgePrim (-ζ) = -edgePrim ζ := by
  rw [← stripS0Tilde_eq_edgePrim (by simpa using hζ), ← stripS0Tilde_eq_edgePrim hζ, stripS0Tilde_neg]

/-! ### The complex edge phase -/

/-- Holomorphic edge phase `Φ_L(τ) = L τ - i P(i τ)` on `D(0, 1)`. -/
noncomputable def edgePhiC (L : ℝ) (τ : ℂ) : ℂ := (L : ℂ) * τ - Complex.I * edgePrim (Complex.I * τ)

lemma edgePhiC_zero (L : ℝ) : edgePhiC L 0 = 0 := by simp [edgePhiC, edgePrim_zero]

lemma hasDerivAt_edgePhiC (L : ℝ) {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasDerivAt (edgePhiC L) ((L : ℂ) + stripG (Complex.I * τ)) τ := by
  have hI : ‖Complex.I * τ‖ < 1 := by simpa using hτ
  have h1 : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I τ := by
    simpa using (hasDerivAt_id τ).const_mul Complex.I
  have h2 := (hasDerivAt_edgePrim hI).comp τ h1
  have h3 := (((hasDerivAt_id τ).const_mul (L : ℂ)).sub (h2.const_mul Complex.I))
  refine h3.congr_deriv ?_
  have : Complex.I * (stripG (Complex.I * τ) * Complex.I) = -stripG (Complex.I * τ) := by
    rw [mul_comm, mul_assoc, Complex.I_mul_I]; ring
  rw [this]; ring

lemma edgePhiC_neg (L : ℝ) {τ : ℂ} (hτ : ‖τ‖ < 1) : edgePhiC L (-τ) = -edgePhiC L τ := by
  unfold edgePhiC
  have hI : ‖Complex.I * τ‖ < 1 := by simpa using hτ
  rw [show Complex.I * -τ = -(Complex.I * τ) by ring, edgePrim_neg hI]
  ring

lemma edgePhiC_ofReal (L : ℝ) {τ : ℝ} (hτ : |τ| < 1) : edgePhiC L (τ : ℂ) = (edgePhi L τ : ℂ) := by
  have hI : ‖(τ : ℂ) * Complex.I‖ < 1 := by simpa [Complex.norm_real] using hτ
  unfold edgePhiC edgePhi
  rw [mul_comm Complex.I (τ : ℂ), ← stripS0Tilde_eq_edgePrim hI, stripS0Tilde_imag]
  push_cast
  rw [← mul_assoc, mul_comm Complex.I (Complex.I), Complex.I_mul_I]
  ring

/-- Derivative of `Φ_L` on the real axis equals the real `edgePhiDeriv`. -/
lemma edgePhiC_deriv_ofReal (L : ℝ) {τ : ℝ} (hτ : |τ| < 1) :
    (L : ℂ) + stripG (Complex.I * (τ : ℂ)) = (edgePhiDeriv L τ : ℂ) := by
  have hτ' : ‖(τ : ℂ)‖ < 1 := by simpa [Complex.norm_real] using hτ
  have h1 : HasDerivAt (fun y : ℝ => edgePhiC L (y : ℂ)) ((L : ℂ) + stripG (Complex.I * (τ : ℂ))) τ :=
    (hasDerivAt_edgePhiC L hτ').comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => ((edgePhi L y : ℝ) : ℂ)) (edgePhiDeriv L τ : ℂ) τ :=
    (hasDerivAt_edgePhi L τ).ofReal_comp
  have hev : (fun y : ℝ => edgePhiC L (y : ℂ)) =ᶠ[𝓝 τ] fun y : ℝ => ((edgePhi L y : ℝ) : ℂ) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hτ] with y hy
    exact edgePhiC_ofReal L hy
  exact (h1.congr_of_eventuallyEq hev.symm).unique h2

/-- `Φ_L'` is even on `D(0, 1)`. -/
lemma stripG_I_mul_neg (τ : ℂ) : stripG (Complex.I * -τ) = stripG (Complex.I * τ) := by
  rw [show Complex.I * -τ = -(Complex.I * τ) by ring, stripG_even]

/-- info: 'FormalResearch.CohnElkies.differentiableOn_stripG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differentiableOn_stripG

/-- info: 'FormalResearch.CohnElkies.stripS0Tilde_eq_edgePrim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stripS0Tilde_eq_edgePrim

/-- info: 'FormalResearch.CohnElkies.hasDerivAt_edgePhiC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_edgePhiC

/-- info: 'FormalResearch.CohnElkies.edgePhiC_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgePhiC_neg

/-- info: 'FormalResearch.CohnElkies.edgePhiC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgePhiC_ofReal

/-- info: 'FormalResearch.CohnElkies.edgePhiC_deriv_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edgePhiC_deriv_ofReal

end FormalResearch.CohnElkies
