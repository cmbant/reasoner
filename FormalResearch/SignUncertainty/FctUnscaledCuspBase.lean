/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCuspEdgeIbp

/-!
# `fct:unscaled-cusp`, hypotheses and the absolute estimate (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`.

Setting.  `CuspPhase 𝔪 κ₁ κ₂ C₂ C₀` records the hypotheses on the phase derivative `𝔪`: even, `C²`, `𝔪(0) = 0`,
`κ₁ m' ≤ 𝔪' ≤ κ₂ m'` on `(0, ∞)` (with `m = hankelEdgeM`, `m' = hankelEdgeM'`), `|𝔪''| ≤ C₂`, `|𝔪 - m| ≤ C₀`.
`CuspAmp η Ca M a` records the symbol bounds of the amplitude `a_c`; `CuspAmpPos` is its restriction to `τ > 0`.
`cuspInt 𝔪 c u a = ∫_ℝ e^{i c φ(τ;u)} a(τ) dτ`, `φ(τ;u) = u τ - ∫_0^τ 𝔪`.

Contents: the reflection `cuspInt = cuspIntPos a + conj (cuspIntPos ã)` (`ã(s) = conj a(-s)`), and the first estimate
`‖cuspInt‖ ≤ C M` for every `u` (`cuspInt_abs_le`).

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- The phase `φ(τ; u) = u τ - ∫_0^τ 𝔪`. -/
noncomputable def cuspPhase (𝔪 : ℝ → ℝ) (u τ : ℝ) : ℝ := u * τ - ∫ t in (0 : ℝ)..τ, 𝔪 t

/-- The oscillatory integral over `ℝ`. -/
noncomputable def cuspInt (𝔪 : ℝ → ℝ) (c u : ℝ) (a : ℝ → ℂ) : ℂ :=
  ∫ τ : ℝ, Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) * a τ

/-- The oscillatory integral over `(0, ∞)`. -/
noncomputable def cuspIntPos (𝔪 : ℝ → ℝ) (c u : ℝ) (a : ℝ → ℂ) : ℂ :=
  ∫ τ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) * a τ

/-- Hypotheses on the phase derivative `𝔪` of `fct:unscaled-cusp`: `𝔪` even, `C²`, `𝔪(0) = 0`, `𝔪' ≍ m'` on `(0, ∞)`,
`|𝔪''| ≤ C₂`, `𝔪 - m = O(1)`. -/
structure CuspPhase (𝔪 : ℝ → ℝ) (κ₁ κ₂ C₂ C₀ : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 𝔪
  even : ∀ t, 𝔪 (-t) = 𝔪 t
  zero : 𝔪 0 = 0
  κ₁_pos : 0 < κ₁
  deriv_lower : ∀ t, 0 < t → κ₁ * hankelEdgeM' t ≤ deriv 𝔪 t
  deriv_upper : ∀ t, 0 < t → deriv 𝔪 t ≤ κ₂ * hankelEdgeM' t
  deriv2_bound : ∀ t, |iteratedDeriv 2 𝔪 t| ≤ C₂
  diff_bound : ∀ t, |𝔪 t - hankelEdgeM t| ≤ C₀

/-- The symbol bounds of the amplitude `a_c` on `τ > 0`: `|a^{(j)}| ≤ C_a M τ^{1/2-j}` on `(0,1]`, `≤ C_a M e^{-ητ}` on
`[1, ∞)`, for `j ≤ 2`. -/
structure CuspAmpPos (η Ca M : ℝ) (a : ℝ → ℂ) : Prop where
  contDiffOn : ContDiffOn ℝ 2 a (Ioi 0)
  small : ∀ j ≤ 2, ∀ τ ∈ Ioc (0 : ℝ) 1, ‖iteratedDeriv j a τ‖ ≤ Ca * M * τ ^ ((1 : ℝ) / 2 - j)
  large : ∀ j ≤ 2, ∀ τ : ℝ, 1 ≤ τ → ‖iteratedDeriv j a τ‖ ≤ Ca * M * Real.exp (-η * τ)

/-- The symbol bounds of the amplitude `a_c` on `ℝ` (continuous, `C²` away from zero). -/
structure CuspAmp (η Ca M : ℝ) (a : ℝ → ℂ) : Prop where
  continuous : Continuous a
  pos : CuspAmpPos η Ca M a
  neg : CuspAmpPos η Ca M (fun τ => star (a (-τ)))

lemma CuspPhase.κ₂_pos {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ} (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : 0 < κ₂ := by
  have h1 := h.deriv_lower 1 one_pos
  have h2 := h.deriv_upper 1 one_pos
  have h3 := (hankelEdgeM'_bounds (τ := 1) one_pos).1
  have : 0 < hankelEdgeM' 1 := lt_of_lt_of_le (by norm_num) h3
  have := h.κ₁_pos
  nlinarith

/-! ### Reflection -/

lemma cuspPhase_neg {𝔪 : ℝ → ℝ} (he : ∀ t, 𝔪 (-t) = 𝔪 t) (u s : ℝ) : cuspPhase 𝔪 u (-s) = -cuspPhase 𝔪 u s := by
  unfold cuspPhase
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := s) (fun x => 𝔪 x)
  simp only [he, neg_zero] at h
  have h2 : ∫ x in (-s)..0, 𝔪 x = -∫ x in (0 : ℝ)..(-s), 𝔪 x := intervalIntegral.integral_symm _ _
  rw [h2] at h
  have : ∫ x in (0 : ℝ)..(-s), 𝔪 x = -∫ x in (0 : ℝ)..s, 𝔪 x := by linarith
  rw [this]; ring

lemma conj_neg_amp {η Ca M : ℝ} {a : ℝ → ℂ} (h : CuspAmp η Ca M a) :
    CuspAmpPos η Ca M (fun τ => star (a (-τ))) := h.neg

/-! ### The absolute estimate -/

/-- The universal dominating function `e^η τ^{1/2} e^{-ητ}` of an amplitude with the symbol bounds. -/
noncomputable def dom (η τ : ℝ) : ℝ := Real.exp η * (τ ^ ((1 : ℝ) / 2) * Real.exp (-η * τ))

/-- The constant `∫_0^∞ e^η τ^{1/2} e^{-ητ} dτ`. -/
noncomputable def domInt (η : ℝ) : ℝ := ∫ τ in Ioi (0 : ℝ), dom η τ

lemma dom_integrableOn {η : ℝ} (hη : 0 < η) : IntegrableOn (dom η) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (1 : ℝ) / 2) (b := η) (by norm_num) one_pos hη
  have h' : IntegrableOn (fun x : ℝ => x ^ ((1 : ℝ) / 2) * Real.exp (-η * x)) (Ioi 0) := by
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp
  exact h'.const_mul _

lemma dom_nonneg (η : ℝ) {τ : ℝ} (_hτ : 0 ≤ τ) : 0 ≤ dom η τ := by
  unfold dom; positivity

lemma domInt_nonneg (η : ℝ) : 0 ≤ domInt η :=
  setIntegral_nonneg measurableSet_Ioi fun _ hτ => dom_nonneg η (le_of_lt hτ)

/-- Pointwise bound of the amplitude on `τ > 0`. -/
lemma CuspAmpPos.norm_le {η Ca M : ℝ} {a : ℝ → ℂ} (h : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M)
    {τ : ℝ} (hτ : 0 < τ) : ‖a τ‖ ≤ Ca * M * dom η τ := by
  have hCM : 0 ≤ Ca * M := mul_nonneg hCa hM
  by_cases h1 : τ ≤ 1
  · have := h.small 0 (by norm_num) τ ⟨hτ, h1⟩
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at this
    refine this.trans ?_
    unfold dom
    refine mul_le_mul_of_nonneg_left ?_ hCM
    have h2 : (1 : ℝ) ≤ Real.exp η * Real.exp (-η * τ) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
    have h3 : 0 ≤ τ ^ ((1 : ℝ) / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  · push Not at h1
    have := h.large 0 (by norm_num) τ h1.le
    simp only [iteratedDeriv_zero] at this
    refine this.trans ?_
    unfold dom
    refine mul_le_mul_of_nonneg_left ?_ hCM
    have h2 : (1 : ℝ) ≤ τ ^ ((1 : ℝ) / 2) := Real.one_le_rpow h1.le (by norm_num)
    have h3 : 1 ≤ Real.exp η := Real.one_le_exp hη.le
    have h4 : 0 < Real.exp (-η * τ) := Real.exp_pos _
    calc Real.exp (-η * τ) = 1 * (1 * Real.exp (-η * τ)) := by ring
      _ ≤ Real.exp η * (τ ^ ((1 : ℝ) / 2) * Real.exp (-η * τ)) := by gcongr

lemma cuspPhase_continuous {𝔪 : ℝ → ℝ} (h : Continuous 𝔪) (u : ℝ) : Continuous (cuspPhase 𝔪 u) := by
  unfold cuspPhase
  exact (continuous_const.mul continuous_id).sub
    (intervalIntegral.continuous_primitive (fun a b => h.intervalIntegrable a b) 0)

lemma CuspAmpPos.continuousOn {η Ca M : ℝ} {a : ℝ → ℂ} (h : CuspAmpPos η Ca M a) : ContinuousOn a (Ioi 0) :=
  h.contDiffOn.continuousOn

lemma cuspF_integrableOn {𝔪 : ℝ → ℝ} (h𝔪 : Continuous 𝔪) {η Ca M : ℝ} {a : ℝ → ℂ} (ha : CuspAmpPos η Ca M a)
    (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) (c u : ℝ) :
    IntegrableOn (fun τ => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) * a τ) (Ioi 0) := by
  have hcont : ContinuousOn (fun τ => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) * a τ) (Ioi 0) := by
    have h1 : Continuous fun τ => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.mul (cuspPhase_continuous h𝔪 u))))
    exact h1.continuousOn.mul ha.continuousOn
  refine Integrable.mono' ((dom_integrableOn hη).const_mul (Ca * M)) (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact ha.norm_le hη hCa hM hτ

/-- The absolute bound for the half-line integral. -/
lemma cuspIntPos_norm_le {𝔪 : ℝ → ℝ} {η Ca M : ℝ} {a : ℝ → ℂ} (ha : CuspAmpPos η Ca M a)
    (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) (c u : ℝ) : ‖cuspIntPos 𝔪 c u a‖ ≤ Ca * M * domInt η := by
  unfold cuspIntPos domInt
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((dom_integrableOn hη).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact ha.norm_le hη hCa hM hτ

/-- Reflection: `∫_ℝ = ∫_0^∞ + conj ∫_0^∞ (reflected amplitude)`. -/
theorem cuspInt_eq {𝔪 : ℝ → ℝ} (h𝔪 : Continuous 𝔪) (he : ∀ t, 𝔪 (-t) = 𝔪 t) {η Ca M : ℝ} {a : ℝ → ℂ}
    (ha : CuspAmp η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) (c u : ℝ) :
    cuspInt 𝔪 c u a = cuspIntPos 𝔪 c u a + star (cuspIntPos 𝔪 c u (fun τ => star (a (-τ)))) := by
  set F : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) * a τ with hF
  set F' : ℝ → ℂ := fun τ => Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u τ : ℝ) : ℂ)) * star (a (-τ)) with hF'
  have key : ∀ r : ℝ, star (Complex.exp (Complex.I * (r : ℂ))) = Complex.exp (Complex.I * ((-r : ℝ) : ℂ)) := by
    intro r
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_mul, Complex.conj_ofReal]
  have hneg : ∀ x : ℝ, F (-x) = star (F' x) := by
    intro x
    simp only [hF, hF', cuspPhase_neg he, star_mul', star_star, mul_neg, key]
  have hint' : IntegrableOn F' (Ioi 0) := cuspF_integrableOn h𝔪 ha.neg hη hCa hM c u
  have hintF' : IntegrableOn (fun x => F (-x)) (Ioi 0) := by
    have : (fun x => F (-x)) = fun x => star (F' x) := funext hneg
    rw [this]
    refine Integrable.mono' hint'.norm ?_ (ae_of_all _ fun x => by simp)
    exact Complex.continuous_conj.comp_aestronglyMeasurable hint'.1
  have hIio : IntegrableOn F (Iio 0) := by
    have := IntegrableOn.comp_neg_Iio (c := 0) (f := fun x => F (-x)) (by simpa using hintF')
    simpa using this
  have hIic : IntegrableOn F (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio).mpr hIio
  have hIoi : IntegrableOn F (Ioi 0) := cuspF_integrableOn h𝔪 ha.pos hη hCa hM c u
  unfold cuspInt cuspIntPos
  rw [← intervalIntegral.integral_Iic_add_Ioi hIic hIoi]
  have h1 : ∫ x in Iic (0 : ℝ), F x = ∫ x in Ioi (0 : ℝ), F (-x) := by
    simp
  rw [h1, add_comm]
  congr 1
  have : (fun x => F (-x)) = fun x => star (F' x) := funext hneg
  rw [this]
  exact integral_conj

/-- **The absolute estimate** (first line of `fct:unscaled-cusp`): `|∫_ℝ e^{icφ} a| ≤ C M` for every `u`. -/
theorem cuspInt_abs_le {𝔪 : ℝ → ℝ} (h𝔪 : Continuous 𝔪) (he : ∀ t, 𝔪 (-t) = 𝔪 t) {η Ca M : ℝ} {a : ℝ → ℂ}
    (ha : CuspAmp η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) (c u : ℝ) :
    ‖cuspInt 𝔪 c u a‖ ≤ 2 * Ca * domInt η * M := by
  rw [cuspInt_eq h𝔪 he ha hη hCa hM]
  refine (norm_add_le _ _).trans ?_
  rw [norm_star]
  have h1 := cuspIntPos_norm_le (𝔪 := 𝔪) ha.pos hη hCa hM c u
  have h2 := cuspIntPos_norm_le (𝔪 := 𝔪) ha.neg hη hCa hM c u
  linarith

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_eq

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cuspInt_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cuspInt_abs_le

end FormalResearch.SignUncertainty.FctUnscaledCusp
