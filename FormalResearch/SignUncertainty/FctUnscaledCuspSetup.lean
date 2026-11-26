/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspIbp
public import FormalResearch.SignUncertainty.FctUnscaledCuspPhase
public import FormalResearch.SignUncertainty.FctCuspEdgeSmall

/-!
# `fct:unscaled-cusp`, interval bounds specialised to the cusp phase (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`.

* `CuspAmpPos.jet_le`: the amplitude jets satisfy the single bound `‖a^{(j)} x‖ ≤ K x^{1/2-j} e^{-η x/2}` on `x > 0`
  (`j ≤ 2`, `K = C_a M (e^η + 8/η²)`).
* `cusp_ibp_one`, `cusp_ibp_two`: the one- and two-step integration-by-parts majorants for
  `∫_α^β e^{i c φ(x;u)} a(x) dx` with explicit pointwise majorants (`ibp_one_bound`, `ibp_two_bound`).
* `norm_Ioi_le`, `norm_Ioc_le`: passage to the half-line from finite intervals.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- The amplitude majorant `K x^{1/2-j} e^{-e x}`. -/
noncomputable def ampB (K e : ℝ) (j : ℕ) (x : ℝ) : ℝ := K * (x ^ ((1 : ℝ) / 2 - j) * Real.exp (-e * x))

/-- The constant `e^η + 8/η²`. -/
noncomputable def ampC (η : ℝ) : ℝ := Real.exp η + 8 / η ^ 2

lemma ampC_pos {η : ℝ} (hη : 0 < η) : 0 < ampC η := by unfold ampC; positivity

section Amp

variable {η Ca M : ℝ} {a : ℝ → ℂ}

lemma CuspAmpPos.hasDerivAt_a (h : CuspAmpPos η Ca M a) {x : ℝ} (hx : 0 < x) : HasDerivAt a (deriv a x) x :=
  ((h.contDiffOn.differentiableOn (by norm_num)) x hx |>.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt

lemma CuspAmpPos.contDiffOn_deriv (h : CuspAmpPos η Ca M a) : ContDiffOn ℝ 1 (deriv a) (Ioi 0) :=
  h.contDiffOn.deriv_of_isOpen isOpen_Ioi (by norm_num)

lemma CuspAmpPos.hasDerivAt_a1 (h : CuspAmpPos η Ca M a) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv a) (deriv (deriv a) x) x :=
  ((h.contDiffOn_deriv.differentiableOn (by norm_num)) x hx |>.differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt

lemma CuspAmpPos.continuousOn_a1 (h : CuspAmpPos η Ca M a) : ContinuousOn (deriv a) (Ioi 0) :=
  h.contDiffOn_deriv.continuousOn

lemma CuspAmpPos.continuousOn_a2 (h : CuspAmpPos η Ca M a) : ContinuousOn (deriv (deriv a)) (Ioi 0) := by
  have := h.contDiffOn_deriv.deriv_of_isOpen isOpen_Ioi (m := 0) (by norm_num)
  exact this.continuousOn

lemma iteratedDeriv_two_eq (f : ℝ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- Unified jet bound. -/
lemma CuspAmpPos.jet_le (h : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) {j : ℕ} (hj : j ≤ 2)
    {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j a x‖ ≤ ampB (Ca * M * ampC η) (η / 2) j x := by
  have hCM : 0 ≤ Ca * M := mul_nonneg hCa hM
  have hAC := ampC_pos hη
  unfold ampB
  have hxj : 0 < x ^ ((1 : ℝ) / 2 - j) := Real.rpow_pos_of_pos hx _
  by_cases h1 : x ≤ 1
  · have := h.small j hj x ⟨hx, h1⟩
    refine this.trans ?_
    have h2 : (1 : ℝ) ≤ ampC η * Real.exp (-(η / 2) * x) := by
      have : Real.exp (η / 2 * x) ≤ Real.exp η := Real.exp_le_exp.mpr (by nlinarith)
      have h3 : Real.exp (-(η / 2) * x) * Real.exp (η / 2 * x) = 1 := by
        rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (-(η / 2) * x) := Real.exp_pos _
      unfold ampC
      nlinarith [Real.exp_pos (η / 2 * x), show 0 ≤ 8 / η ^ 2 by positivity]
    calc Ca * M * x ^ ((1 : ℝ) / 2 - j) = Ca * M * (x ^ ((1 : ℝ) / 2 - j) * 1) := by ring
      _ ≤ Ca * M * (x ^ ((1 : ℝ) / 2 - j) * (ampC η * Real.exp (-(η / 2) * x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hxj.le) hCM
      _ = Ca * M * ampC η * (x ^ ((1 : ℝ) / 2 - j) * Real.exp (-(η / 2) * x)) := by ring
  · push Not at h1
    have := h.large j hj x h1.le
    refine this.trans ?_
    -- `x^(j - 1/2) e^{-η x/2} ≤ ampC`
    have hxe : x ^ ((j : ℝ) - 1 / 2) ≤ x ^ (2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le h1.le ?_
      have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      linarith
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ η / 2 * x by positivity)
    have hexp_pos := Real.exp_pos (η / 2 * x)
    have hx2 : x ^ (2 : ℝ) = x ^ 2 := by norm_cast
    have h5 : x ^ 2 * Real.exp (-(η / 2) * x) ≤ 8 / η ^ 2 := by
      have h3 : Real.exp (-(η / 2) * x) * Real.exp (η / 2 * x) = 1 := by
        rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (-(η / 2) * x) := Real.exp_pos _
      rw [le_div_iff₀ (by positivity)]
      have : (η / 2 * x) ^ 2 / 2 ≤ Real.exp (η / 2 * x) := by nlinarith [sq_nonneg (η / 2 * x)]
      nlinarith [mul_le_mul_of_nonneg_left this h4.le]
    have h6 : x ^ ((j : ℝ) - 1 / 2) * Real.exp (-(η / 2) * x) ≤ ampC η := by
      calc x ^ ((j : ℝ) - 1 / 2) * Real.exp (-(η / 2) * x) ≤ x ^ 2 * Real.exp (-(η / 2) * x) := by
            rw [← hx2]; exact mul_le_mul_of_nonneg_right hxe (Real.exp_pos _).le
        _ ≤ 8 / η ^ 2 := h5
        _ ≤ ampC η := by unfold ampC; linarith [Real.exp_pos η]
    have h7 : Real.exp (-η * x) = Real.exp (-(η / 2) * x) * Real.exp (-(η / 2) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h8 : x ^ ((1 : ℝ) / 2 - j) * x ^ ((j : ℝ) - 1 / 2) = 1 := by
      rw [← Real.rpow_add hx]; simp
    have h9 : Real.exp (-(η / 2) * x) ≤ ampC η * x ^ ((1 : ℝ) / 2 - j) := by
      have := mul_le_mul_of_nonneg_left h6 hxj.le
      have h10 : x ^ ((1 : ℝ) / 2 - j) * (x ^ ((j : ℝ) - 1 / 2) * Real.exp (-(η / 2) * x)) =
          Real.exp (-(η / 2) * x) := by rw [← mul_assoc, h8, one_mul]
      rw [h10] at this
      linarith
    calc Ca * M * Real.exp (-η * x) = Ca * M * (Real.exp (-(η / 2) * x) * Real.exp (-(η / 2) * x)) := by rw [h7]
      _ ≤ Ca * M * ((ampC η * x ^ ((1 : ℝ) / 2 - j)) * Real.exp (-(η / 2) * x)) := by
          gcongr
      _ = Ca * M * ampC η * (x ^ ((1 : ℝ) / 2 - j) * Real.exp (-(η / 2) * x)) := by ring

end Amp

/-! ### Interval integration by parts for the cusp phase -/

section IbpCusp

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ} {η Ca M : ℝ} {a : ℝ → ℂ}

private lemma hasDerivAt_D1 (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (c u x : ℝ) :
    HasDerivAt (fun x => c * (u - 𝔪 x)) (-c * deriv 𝔪 x) x :=
  (((hasDerivAt_const x u).sub (h.hasDerivAt x)).const_mul c).congr_deriv (by ring)

private lemma hasDerivAt_D2 (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (c x : ℝ) :
    HasDerivAt (fun x => -c * deriv 𝔪 x) (-c * iteratedDeriv 2 𝔪 x) x :=
  ((h.hasDerivAt₂ x).const_mul (-c))

/-- One integration by parts for `∫_α^β e^{icφ(x;u)} a(x)`. -/
theorem cusp_ibp_one (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) {c u α β : ℝ} (hc : 0 < c)
    (hα : 0 < α) (hαβ : α ≤ β) {B0 B1 P1 P2 : ℝ → ℝ}
    (hB0 : ∀ x ∈ Icc α β, ‖a x‖ ≤ B0 x) (hB1 : ∀ x ∈ Icc α β, ‖deriv a x‖ ≤ B1 x)
    (hP1 : ∀ x ∈ Icc α β, 0 < P1 x ∧ P1 x ≤ c * |u - 𝔪 x|) (hP2 : ∀ x ∈ Icc α β, c * deriv 𝔪 x ≤ P2 x)
    (hint : IntervalIntegrable (fun x => B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) volume α β) :
    ‖∫ x in α..β, Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      B0 β / P1 β + B0 α / P1 α + ∫ x in α..β, (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) := by
  have hpos : ∀ x ∈ Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα hx.1
  have hD1c : ∀ x ∈ Icc α β, |c * (u - 𝔪 x)| = c * |u - 𝔪 x| := fun x _ => by
    rw [abs_mul, abs_of_pos hc]
  refine ibp_one_bound hαβ (Φ := fun x => c * cuspPhase 𝔪 u x) (D1 := fun x => c * (u - 𝔪 x))
    (D2 := fun x => -c * deriv 𝔪 x) (h := a) (h1 := deriv a) (B0 := B0) (B1 := B1) (P1 := P1) (P2 := P2)
    (fun x _ => (h.hasDerivAt_phase u x).const_mul c) (fun x _ => hasDerivAt_D1 h c u x) ?_
    (fun x hx => ha.hasDerivAt_a (hpos x hx)) (ha.continuousOn_a1.mono fun x hx => hpos x hx)
    (by exact (continuous_const.mul h.continuous_deriv).continuousOn) hB0 hB1 ?_ ?_ hint
  · intro x hx
    have := hP1 x hx
    have h2 : 0 < c * |u - 𝔪 x| := lt_of_lt_of_le this.1 this.2
    have : u - 𝔪 x ≠ 0 := fun h0 => by simp [h0] at h2
    exact mul_ne_zero hc.ne' this
  · intro x hx
    refine ⟨(hP1 x hx).1, ?_⟩
    rw [hD1c x hx]; exact (hP1 x hx).2
  · intro x hx
    have := h.deriv_nonneg (hpos x hx)
    rw [show -c * deriv 𝔪 x = -(c * deriv 𝔪 x) by ring, abs_neg, abs_of_pos (mul_pos hc this)]
    exact hP2 x hx

/-- Two integrations by parts for `∫_α^β e^{icφ(x;u)} a(x)`. -/
theorem cusp_ibp_two (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) {c u α β : ℝ} (hc : 0 < c)
    (hα : 0 < α) (hαβ : α ≤ β) {B0 B1 B2 P1 P2 P3 : ℝ → ℝ}
    (hB0 : ∀ x ∈ Icc α β, ‖a x‖ ≤ B0 x) (hB1 : ∀ x ∈ Icc α β, ‖deriv a x‖ ≤ B1 x)
    (hB2 : ∀ x ∈ Icc α β, ‖deriv (deriv a) x‖ ≤ B2 x)
    (hP1 : ∀ x ∈ Icc α β, 0 < P1 x ∧ P1 x ≤ c * |u - 𝔪 x|) (hP2 : ∀ x ∈ Icc α β, c * deriv 𝔪 x ≤ P2 x)
    (hP3 : ∀ x ∈ Icc α β, c * C₂ ≤ P3 x)
    (hint : IntervalIntegrable (fun x => (B2 x / P1 x + 2 * B1 x * P2 x / P1 x ^ 2 + B0 x * P3 x / P1 x ^ 2 +
        2 * B0 x * P2 x ^ 2 / P1 x ^ 3) / P1 x +
      (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) * P2 x / P1 x ^ 2) volume α β) :
    ‖∫ x in α..β, Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      B0 β / P1 β + B0 α / P1 α + (B1 β / P1 β + B0 β * P2 β / P1 β ^ 2) / P1 β +
        (B1 α / P1 α + B0 α * P2 α / P1 α ^ 2) / P1 α +
      ∫ x in α..β, ((B2 x / P1 x + 2 * B1 x * P2 x / P1 x ^ 2 + B0 x * P3 x / P1 x ^ 2 +
        2 * B0 x * P2 x ^ 2 / P1 x ^ 3) / P1 x +
      (B1 x / P1 x + B0 x * P2 x / P1 x ^ 2) * P2 x / P1 x ^ 2) := by
  have hpos : ∀ x ∈ Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα hx.1
  have hD1c : ∀ x ∈ Icc α β, |c * (u - 𝔪 x)| = c * |u - 𝔪 x| := fun x _ => by
    rw [abs_mul, abs_of_pos hc]
  refine ibp_two_bound hαβ (Φ := fun x => c * cuspPhase 𝔪 u x) (D1 := fun x => c * (u - 𝔪 x))
    (D2 := fun x => -c * deriv 𝔪 x) (D3 := fun x => -c * iteratedDeriv 2 𝔪 x) (h := a) (h1 := deriv a)
    (h2 := deriv (deriv a)) (B0 := B0) (B1 := B1) (B2 := B2) (P1 := P1) (P2 := P2) (P3 := P3)
    (fun x _ => (h.hasDerivAt_phase u x).const_mul c) (fun x _ => hasDerivAt_D1 h c u x)
    (fun x _ => hasDerivAt_D2 h c x) ?_
    (fun x hx => ha.hasDerivAt_a (hpos x hx)) (fun x hx => ha.hasDerivAt_a1 (hpos x hx))
    (ha.continuousOn_a2.mono fun x hx => hpos x hx)
    (by exact (continuous_const.mul h.continuous_deriv₂).continuousOn) hB0 hB1 hB2 ?_ ?_ ?_ hint
  · intro x hx
    have := hP1 x hx
    have h2 : 0 < c * |u - 𝔪 x| := lt_of_lt_of_le this.1 this.2
    have : u - 𝔪 x ≠ 0 := fun h0 => by simp [h0] at h2
    exact mul_ne_zero hc.ne' this
  · intro x hx
    refine ⟨(hP1 x hx).1, ?_⟩
    rw [hD1c x hx]; exact (hP1 x hx).2
  · intro x hx
    have := h.deriv_nonneg (hpos x hx)
    rw [show -c * deriv 𝔪 x = -(c * deriv 𝔪 x) by ring, abs_neg, abs_of_pos (mul_pos hc this)]
    exact hP2 x hx
  · intro x hx
    rw [show -c * iteratedDeriv 2 𝔪 x = -(c * iteratedDeriv 2 𝔪 x) by ring, abs_neg, abs_mul, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (h.deriv2_bound x) hc.le).trans (hP3 x hx)

end IbpCusp

/-! ### Passage to the half-line -/

/-- If `∫_β^N f` is bounded by `A + R N` with `R → 0`, then `‖∫_{Ioi β} f‖ ≤ A`. -/
lemma norm_Ioi_le {f : ℝ → ℂ} {β A : ℝ} (hf : IntegrableOn f (Ioi β)) {R : ℝ → ℝ} (hR : Tendsto R atTop (𝓝 0))
    (h : ∀ N, β ≤ N → ‖∫ x in β..N, f x‖ ≤ A + R N) : ‖∫ x in Ioi β, f x‖ ≤ A := by
  have h1 := intervalIntegral_tendsto_integral_Ioi β hf tendsto_id
  have h2 : Tendsto (fun N => ‖∫ x in β..N, f x‖) atTop (𝓝 ‖∫ x in Ioi β, f x‖) := h1.norm
  have h3 : Tendsto (fun N => A + R N) atTop (𝓝 (A + 0)) := hR.const_add A
  rw [add_zero] at h3
  exact le_of_tendsto_of_tendsto h2 h3 (by
    filter_upwards [eventually_ge_atTop β] with N hN using h N hN)

/-- Cut at `0`: if `‖f x‖ ≤ K √x` on `(0, β]` and `‖∫_s^β f‖ ≤ A + c₁ √s` for all `s ∈ (0, β]`, then
`‖∫_0^β f‖ ≤ A`. -/
lemma norm_zero_le {f : ℝ → ℂ} {β A c₁ K : ℝ} (hβ : 0 < β) (hf : IntervalIntegrable f volume 0 β) (hc₁ : 0 ≤ c₁)
    (hK : 0 ≤ K) (hfK : ∀ x ∈ Ioc (0 : ℝ) β, ‖f x‖ ≤ K * Real.sqrt x)
    (h : ∀ s ∈ Ioc (0 : ℝ) β, ‖∫ x in s..β, f x‖ ≤ A + c₁ * Real.sqrt s) : ‖∫ x in (0 : ℝ)..β, f x‖ ≤ A := by
  have key : ∀ s ∈ Ioc (0 : ℝ) β, ‖∫ x in (0 : ℝ)..β, f x‖ ≤ A + (c₁ + K * β) * Real.sqrt s := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsβ : s ≤ β := hs.2
    have h1 : IntervalIntegrable f volume 0 s := hf.mono_set (by
      rw [uIcc_of_le hs0.le, uIcc_of_le hβ.le]; exact Icc_subset_Icc le_rfl hsβ)
    have h2 : IntervalIntegrable f volume s β := hf.mono_set (by
      rw [uIcc_of_le hsβ, uIcc_of_le hβ.le]; exact Icc_subset_Icc hs0.le le_rfl)
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have h3 : ‖∫ x in (0 : ℝ)..s, f x‖ ≤ K * Real.sqrt s * |s - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
      rw [uIoc_of_le hs0.le] at hx
      refine (hfK x ⟨hx.1, hx.2.trans hsβ⟩).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx.2) hK
    rw [sub_zero, abs_of_pos hs0] at h3
    have h4 := h s hs
    have h5 : K * Real.sqrt s * s ≤ K * β * Real.sqrt s := by
      nlinarith [Real.sqrt_nonneg s, mul_nonneg hK (Real.sqrt_nonneg s)]
    calc _ ≤ ‖∫ x in (0 : ℝ)..s, f x‖ + ‖∫ x in s..β, f x‖ := norm_add_le _ _
      _ ≤ K * Real.sqrt s * s + (A + c₁ * Real.sqrt s) := add_le_add h3 h4
      _ ≤ _ := by nlinarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 < c₁ + K * β + 1 := by positivity
  set s : ℝ := min β ((ε / (c₁ + K * β + 1)) ^ 2) with hs
  have hs0 : 0 < s := lt_min hβ (by positivity)
  have hsq : Real.sqrt s ≤ ε / (c₁ + K * β + 1) := by
    calc Real.sqrt s ≤ Real.sqrt ((ε / (c₁ + K * β + 1)) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = ε / (c₁ + K * β + 1) := Real.sqrt_sq (by positivity)
  have := key s ⟨hs0, min_le_left _ _⟩
  have h6 : (c₁ + K * β) * Real.sqrt s ≤ ε := by
    calc (c₁ + K * β) * Real.sqrt s ≤ (c₁ + K * β + 1) * (ε / (c₁ + K * β + 1)) :=
          mul_le_mul (by linarith) hsq (Real.sqrt_nonneg _) hc.le
      _ = ε := by field_simp
  linarith

/-- Splitting `∫_{Ioi a} f = ∫_a^b f + ∫_{Ioi b} f`. -/
lemma integral_Ioi_split {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : IntegrableOn f (Ioi a)) :
    ∫ x in Ioi a, f x = (∫ x in a..b, f x) + ∫ x in Ioi b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← Ioc_union_Ioi_eq_Ioi hab]
  refine setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.out)) measurableSet_Ioi
    (hf.mono_set (by rw [← Ioc_union_Ioi_eq_Ioi hab]; exact subset_union_left)) 
    (hf.mono_set (by rw [← Ioc_union_Ioi_eq_Ioi hab]; exact subset_union_right))

/-- Second-derivative van der Corput for the cusp phase on `[α, β] ⊂ (0, ∞)`. -/
theorem cusp_vdc {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ : ℝ} (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) {η Ca M : ℝ} {a : ℝ → ℂ}
    (ha : CuspAmpPos η Ca M a) {c u α β lam M1 M2 : ℝ} (hc : 0 < c) (hα : 0 < α) (hαβ : α ≤ β) (hlam : 0 < lam)
    (hlb : ∀ x ∈ Icc α β, lam ≤ deriv 𝔪 x) (hM1 : ∀ x ∈ Icc α β, ‖a x‖ ≤ M1)
    (hM2 : ∀ x ∈ Icc α β, ‖deriv a x‖ ≤ M2) (hM2nn : 0 ≤ M2) :
    ‖∫ x in α..β, Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      8 * (M1 + M2 * (β - α)) / Real.sqrt (c * lam) := by
  have hpos : ∀ x ∈ Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα hx.1
  obtain ⟨hbv, hev⟩ := FormalResearch.SignUncertainty.FctCuspEdge.eVariationOn_le_of_deriv_bound hαβ hM2nn isOpen_Ioi
    (fun x hx => hpos x hx) (ha.contDiffOn.of_le (by norm_num)) hM2
  have hM1nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 α (left_mem_Icc.mpr hαβ))
  have hv := FormalResearch.Analysis.van_der_corput_second hαβ hc hlam (φ := cuspPhase 𝔪 u)
    (φ' := fun x => u - 𝔪 x) (φ'' := fun x => -deriv 𝔪 x) (h := a) (M := M1)
    (fun x _ => h.hasDerivAt_phase u x)
    (fun x _ => (((hasDerivAt_const x u).sub (h.hasDerivAt x)).congr_deriv (by ring)))
    (Or.inr (fun x hx y hy hxy => by
      have := h.mono (hpos x hx).le hxy
      simp only; linarith))
    (fun x hx => by
      rw [abs_neg, abs_of_pos (h.deriv_nonneg (hpos x hx))]; exact hlb x hx)
    (ha.contDiffOn.continuousOn.mono fun x hx => hpos x hx) hbv hM1
  have hsq : 0 < Real.sqrt (c * lam) := Real.sqrt_pos.mpr (mul_pos hc hlam)
  have h1 : ∫ x in α..β, Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x =
      ∫ x in α..β, a x * Complex.exp (Complex.I * (c : ℂ) * (cuspPhase 𝔪 u x : ℂ)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [mul_comm]; push_cast; ring_nf
  rw [h1]
  refine hv.trans ?_
  gcongr

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.CuspAmpPos.jet_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CuspAmpPos.jet_le

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cusp_ibp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cusp_ibp_one

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cusp_ibp_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cusp_ibp_two

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.cusp_vdc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cusp_vdc

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.norm_Ioi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_Ioi_le

/-- info: 'FormalResearch.SignUncertainty.FctUnscaledCusp.norm_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_zero_le

end FormalResearch.SignUncertainty.FctUnscaledCusp
