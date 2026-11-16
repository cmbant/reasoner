module

public import FormalResearch.Special.AiryEnvelope
public import FormalResearch.Special.AiryRotation

/-!
# An entire primitive of `Ai`, and its behaviour on the rays `arg z = ±π/3`

`Ai` is entire, so it has an entire primitive `P` with `P(0) = 0` (Mathlib's Morera theorem for `ℂ`,
`Differentiable.isExactOn_univ`).  This file proves, for `P = airyAiPrim`:

* `airyAiPrim_rotation`: `P(z) + P(ωz) + P(ω²z) = 0` (integrate the three-fold rotation identity),
* `airyAiPrim_real`: `P(T) = ∫_0^T Ai` for real `T`,
* `norm_airyAiPrim_ray_sub_le`: `‖P(ρ e^{±iπ/3}) - P(ρ)‖ ≤ 3π/(2√ρ)`: the integral of `Ai` over the arc
  `{ρ e^{±iθ} : 0 ≤ θ ≤ π/3}` is `O(ρ^{-1/2})`.  It uses only the complex envelope
  `|Ai(z)| ≤ 3 exp(-(2/3) Re z^{3/2})` (`airyAiC_envelope`), the identity
  `Re (ρ e^{iφ})^{3/2} = ρ^{3/2} cos(3φ/2)` and Jordan's inequality `cos φ ≥ 1 - 2φ/π`
  (`φ ∈ [0, π/2]`): the exponential gain `exp(-(2/3) ρ^{3/2} cos(3θ/2))` degenerates to `1` only at the
  end point `θ = π/3`, on a `θ`-set of size `O(ρ^{-3/2})`.
(The identity `P(-y) = -P(y e^{iπ/3}) - P(y e^{-iπ/3})` is `airyAiPrim_neg_eq` in `AiryIntegral`.)

These are the inputs of `AiryIntegral` (`∫_0^∞ Ai = 1/3`, `∫_{-∞}^0 Ai = 2/3`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma airyInt_exists_prim : ∃ P : ℂ → ℂ, P 0 = 0 ∧ ∀ z, HasDerivAt P (airyAiC z) z := by
  obtain ⟨g, hg0, hg⟩ := (Differentiable.isExactOn_univ differentiable_airyAiC).with_val_at 0 0
  exact ⟨g, hg0, fun z => hg z trivial⟩

/-- The entire primitive of `Ai` vanishing at `0` (`P(z) = ∫_0^z Ai`). -/
noncomputable def airyAiPrim : ℂ → ℂ := airyInt_exists_prim.choose

lemma airyAiPrim_zero : airyAiPrim 0 = 0 := airyInt_exists_prim.choose_spec.1

lemma hasDerivAt_airyAiPrim (z : ℂ) : HasDerivAt airyAiPrim (airyAiC z) z :=
  airyInt_exists_prim.choose_spec.2 z

lemma continuous_airyAiPrim : Continuous airyAiPrim :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_airyAiPrim z).continuousAt

/-- `P(z) + P(ωz) + P(ω²z) = 0`. -/
theorem airyAiPrim_rotation (z : ℂ) :
    airyAiPrim z + airyAiPrim (airyOmega * z) + airyAiPrim (airyOmega ^ 2 * z) = 0 := by
  have hQ : ∀ w : ℂ, HasDerivAt (fun w => airyAiPrim w + airyAiPrim (airyOmega * w) +
      airyAiPrim (airyOmega ^ 2 * w)) 0 w := by
    intro w
    have h1 := hasDerivAt_airyAiPrim w
    have h2 : HasDerivAt (fun w => airyAiPrim (airyOmega * w)) (airyAiC (airyOmega * w) * airyOmega) w := by
      have := (hasDerivAt_airyAiPrim (airyOmega * w)).comp w ((hasDerivAt_id w).const_mul airyOmega)
      exact this.congr_deriv (by ring)
    have h3 : HasDerivAt (fun w => airyAiPrim (airyOmega ^ 2 * w))
        (airyAiC (airyOmega ^ 2 * w) * airyOmega ^ 2) w := by
      have := (hasDerivAt_airyAiPrim (airyOmega ^ 2 * w)).comp w
        ((hasDerivAt_id w).const_mul (airyOmega ^ 2))
      exact this.congr_deriv (by ring)
    have := (h1.add h2).add h3
    convert this using 1
    have := airyAiC_rotation w
    linear_combination -this
  have hconst := is_const_of_deriv_eq_zero (f := fun w => airyAiPrim w + airyAiPrim (airyOmega * w) +
      airyAiPrim (airyOmega ^ 2 * w)) (fun w => (hQ w).differentiableAt) (fun w => (hQ w).deriv) z 0
  simpa [airyAiPrim_zero] using hconst

/-- For real `T`, `P(T) = ∫_0^T Ai`. -/
lemma airyAiPrim_real (T : ℝ) : airyAiPrim (T : ℂ) = ((∫ x in (0 : ℝ)..T, airyAi x : ℝ) : ℂ) := by
  have h : ∀ x ∈ Set.uIcc (0 : ℝ) T, HasDerivAt (fun x : ℝ => airyAiPrim (x : ℂ)) (airyAi x : ℂ) x := by
    intro x _
    have := (hasDerivAt_airyAiPrim (x : ℂ)).comp_ofReal
    rwa [airyAiC_ofReal] at this
  have hi : IntervalIntegrable (fun x : ℝ => (airyAi x : ℂ)) volume 0 T :=
    (Complex.continuous_ofReal.comp differentiable_airyAi.continuous).intervalIntegrable _ _
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt h hi
  rw [intervalIntegral.integral_ofReal] at this
  simpa [airyAiPrim_zero] using this.symm

/-! ### The arc estimate -/

lemma airyInt_re_cpow {ρ φ : ℝ} (hρ : 0 < ρ) (h1 : -π < φ) (h2 : φ ≤ π) :
    (((ρ : ℂ) * cexp ((φ : ℂ) * I)) ^ (3 / 2 : ℂ)).re = ρ ^ (3 / 2 : ℝ) * Real.cos (3 * φ / 2) := by
  have e : (ρ : ℂ) * cexp ((φ : ℂ) * I) = cexp (((Real.log ρ : ℝ) : ℂ) + (φ : ℂ) * I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ]
  rw [e, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  rw [Complex.log_exp (by simpa using h1) (by simpa using h2)]
  rw [Complex.exp_re, Real.rpow_def_of_pos hρ]
  congr 1
  · congr 1; simp
  · congr 1; simp; ring

lemma airyInt_cos_ge {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 3) :
    1 - 3 * θ / π ≤ Real.cos (3 * θ / 2) := by
  have hπ := Real.pi_pos
  have hx : 0 ≤ π / 2 - 3 * θ / 2 := by linarith
  have hx' : π / 2 - 3 * θ / 2 ≤ π / 2 := by linarith
  have := Real.mul_le_sin hx hx'
  rw [show Real.cos (3 * θ / 2) = Real.sin (π / 2 - 3 * θ / 2) by rw [Real.sin_pi_div_two_sub]]
  refine le_trans (le_of_eq ?_) this
  field_simp

lemma airyInt_exp_integral_le {a : ℝ} (ha : 0 < a) :
    ∫ θ in (0 : ℝ)..π / 3, Real.exp (-(a * (1 - 3 * θ / π))) ≤ π / (3 * a) := by
  have hπ := Real.pi_pos
  have h : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 3), HasDerivAt
      (fun θ : ℝ => π / (3 * a) * Real.exp (-(a * (1 - 3 * θ / π))))
      (Real.exp (-(a * (1 - 3 * θ / π)))) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ : ℝ => -(a * (1 - 3 * θ / π))) (3 * a / π) θ := by
      have := ((((hasDerivAt_id θ).const_mul 3).div_const π).const_sub 1).const_mul a |>.neg
      exact this.congr_deriv (by simp; ring)
    have := (h1.exp).const_mul (π / (3 * a))
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by apply Continuous.intervalIntegrable; fun_prop)]
  have e : -(a * (1 - 3 * (π / 3) / π)) = 0 := by field_simp; ring
  simp only [e, Real.exp_zero, mul_zero, zero_div, sub_zero, mul_one]
  have : 0 < π / (3 * a) * Real.exp (-a) := by positivity
  simp
  linarith

/-- The arc integral: `‖P(ρ e^{±iπ/3}) - P(ρ)‖ ≤ 3π/(2√ρ)`. -/
theorem norm_airyAiPrim_ray_sub_le {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ = 1 ∨ σ = -1) :
    ‖airyAiPrim ((ρ : ℂ) * cexp (((σ * (π / 3) : ℝ) : ℂ) * I)) - airyAiPrim ρ‖ ≤ 3 * π / (2 * √ρ) := by
  have hπ := Real.pi_pos
  set a : ℝ := (2 / 3) * ρ ^ (3 / 2 : ℝ) with ha_def
  have hρ32 : 0 < ρ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have ha : 0 < a := by positivity
  set γ : ℝ → ℂ := fun θ => (ρ : ℂ) * cexp (((σ * θ : ℝ) : ℂ) * I) with hγ
  set G : ℝ → ℂ := fun θ => ((ρ : ℂ) * (cexp (((σ * θ : ℝ) : ℂ) * I) * ((σ : ℂ) * I))) *
    airyAiC (γ θ) with hG
  have hγd : ∀ θ : ℝ, HasDerivAt γ ((ρ : ℂ) * (cexp (((σ * θ : ℝ) : ℂ) * I) * ((σ : ℂ) * I))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => (((σ * θ : ℝ)) : ℂ)) (σ : ℂ) θ := by
      have := ((hasDerivAt_id θ).const_mul σ).ofReal_comp
      simpa using this
    exact ((h1.mul_const I).cexp.const_mul (ρ : ℂ)).congr_deriv (by ring)
  have hgd : ∀ θ : ℝ, HasDerivAt (fun θ => airyAiPrim (γ θ)) (G θ) θ := by
    intro θ
    exact ((hasDerivAt_airyAiPrim (γ θ)).scomp θ (hγd θ)).congr_deriv (by simp [hG])
  have hGc : Continuous G := by
    have := differentiable_airyAiC.continuous
    have hγc : Continuous γ := by simp only [hγ]; fun_prop
    simp only [hG]
    exact (by fun_prop : Continuous fun θ : ℝ =>
      (ρ : ℂ) * (cexp (((σ * θ : ℝ) : ℂ) * I) * ((σ : ℂ) * I))).mul (this.comp hγc)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π / 3) (fun θ _ => hgd θ)
    (hGc.intervalIntegrable _ _)
  have hγ0 : γ 0 = ρ := by simp [hγ]
  have hπ3 : (0 : ℝ) ≤ π / 3 := by positivity
  rw [show airyAiPrim ((ρ : ℂ) * cexp (((σ * (π / 3) : ℝ) : ℂ) * I)) - airyAiPrim ρ =
    airyAiPrim (γ (π / 3)) - airyAiPrim (γ 0) by rw [hγ0]]
  rw [← hftc]
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) (π / 3), ‖G θ‖ ≤ 3 * ρ * Real.exp (-(a * (1 - 3 * θ / π))) := by
    intro θ hθ
    have hnorm : ‖(ρ : ℂ) * (cexp (((σ * θ : ℝ) : ℂ) * I) * ((σ : ℂ) * I))‖ = ρ := by
      rcases hσ with rfl | rfl <;> simp [abs_of_pos hρ, Complex.norm_exp]
    have hre : ((γ θ) ^ (3 / 2 : ℂ)).re = ρ ^ (3 / 2 : ℝ) * Real.cos (3 * θ / 2) := by
      have := airyInt_re_cpow (ρ := ρ) (φ := σ * θ) hρ
        (by rcases hσ with rfl | rfl <;> nlinarith [hθ.1, hθ.2]) (by rcases hσ with rfl | rfl <;> nlinarith [hθ.1, hθ.2])
      simp only [hγ]
      rw [this]
      rcases hσ with rfl | rfl
      · simp
      · rw [show 3 * (-1 * θ) / 2 = -(3 * θ / 2) by ring, Real.cos_neg]
    have hcos := airyInt_cos_ge hθ.1 hθ.2
    have hAi := airyAiC_envelope (γ θ)
    have h1 := rpow_neg_quarter_le_one (γ θ)
    have hexp : Real.exp (-(2 / 3) * ((γ θ) ^ (3 / 2 : ℂ)).re) ≤ Real.exp (-(a * (1 - 3 * θ / π))) := by
      apply Real.exp_le_exp.mpr
      rw [hre, ha_def]
      nlinarith [mul_le_mul_of_nonneg_left hcos hρ32.le]
    have hAi' : ‖airyAiC (γ θ)‖ ≤ 3 * Real.exp (-(a * (1 - 3 * θ / π))) := by
      refine hAi.trans ?_
      have h3 := Real.exp_pos (-(2 / 3) * ((γ θ) ^ (3 / 2 : ℂ)).re)
      calc 3 * (1 + ‖γ θ‖) ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * ((γ θ) ^ (3 / 2 : ℂ)).re)
          ≤ 3 * 1 * Real.exp (-(2 / 3) * ((γ θ) ^ (3 / 2 : ℂ)).re) := by gcongr
        _ ≤ 3 * Real.exp (-(a * (1 - 3 * θ / π))) := by linarith
    have hGn : ‖G θ‖ = ρ * ‖airyAiC (γ θ)‖ := by
      show ‖((ρ : ℂ) * (cexp (((σ * θ : ℝ) : ℂ) * I) * ((σ : ℂ) * I))) * airyAiC (γ θ)‖ = _
      rw [norm_mul, hnorm]
    rw [hGn]
    calc ρ * ‖airyAiC (γ θ)‖ ≤ ρ * (3 * Real.exp (-(a * (1 - 3 * θ / π)))) := by gcongr
      _ = _ := by ring
  have hint : ‖∫ θ in (0 : ℝ)..π / 3, G θ‖ ≤ ∫ θ in (0 : ℝ)..π / 3, ‖G θ‖ :=
    intervalIntegral.norm_integral_le_integral_norm hπ3
  have hmono : ∫ θ in (0 : ℝ)..π / 3, ‖G θ‖ ≤
      ∫ θ in (0 : ℝ)..π / 3, 3 * ρ * Real.exp (-(a * (1 - 3 * θ / π))) := by
    refine intervalIntegral.integral_mono_on hπ3 ?_ ?_ hpt
    · exact (hGc.norm).intervalIntegrable _ _
    · apply Continuous.intervalIntegrable; fun_prop
  have hI := airyInt_exp_integral_le ha
  rw [intervalIntegral.integral_const_mul] at hmono
  refine hint.trans (hmono.trans ?_)
  have hsq : √ρ * √ρ = ρ := Real.mul_self_sqrt hρ.le
  have hsqpos : 0 < √ρ := Real.sqrt_pos.mpr hρ
  have hr : ρ ^ (3 / 2 : ℝ) = ρ * √ρ := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hρ, Real.rpow_one, ← Real.sqrt_eq_rpow]
  calc 3 * ρ * ∫ θ in (0 : ℝ)..π / 3, Real.exp (-(a * (1 - 3 * θ / π)))
      ≤ 3 * ρ * (π / (3 * a)) := by gcongr
    _ = 3 * π / (2 * √ρ) := by
      rw [ha_def, hr]
      field_simp

/-- info: 'FormalResearch.Special.airyAiPrim_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAiPrim_rotation

/-- info: 'FormalResearch.Special.norm_airyAiPrim_ray_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.norm_airyAiPrim_ray_sub_le

end FormalResearch.Special
