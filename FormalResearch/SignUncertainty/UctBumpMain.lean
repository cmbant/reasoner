module

public import FormalResearch.SignUncertainty.UctBumpSymbolAdmiss
public import FormalResearch.SignUncertainty.DeepLobeKernel
public import FormalResearch.SignUncertainty.StripAdmissLift
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# `uct:bump-symbol`: the main-density bound for `L ≤ bδ/2` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:bump-symbol`: "for `L ≤ bδ/2` the main density is bounded by
`C M (cδ)^{-1} Λ_α(δ) e^{-κ c δ^{3/2}}`".

`bumpDW c B ζ = c^{-1/3} B̂(cζ)` (`ΔW_c`) and `bumpHmain c B ξ = (c^{1/3}/2π) ∫ K₀(iτ,ξ) ΔW_c(iτ) dτ` (`Δh_main`, `ξ = e^L/π²`).
`kernel_line_shift`: for `StripM1 W`, `∫ K₀(σ+iτ,ξ) W(σ+iτ) dτ` does not depend on `σ ∈ [0,1)` (`admiss_vert_rep`).
`bump_main_density`: shift to `σ = k√δ` with `k = min(1/8, b)`, bound `K₀` by `norm_mellinK0_vert_le` and `B̂` by `bump_laplace_decay` (`r = 2`);
the total exponent is `≤ -(kb/4) c δ^{3/2}`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `ΔW_c(ζ) = c^{-1/3} B̂(cζ)`. -/
noncomputable def bumpDW (c : ℝ) (B : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)

/-- `Δh_main(L) = (c^{1/3}/2π) ∫ K₀(iτ,ξ) ΔW_c(iτ) dτ`. -/
noncomputable def bumpHmain (c : ℝ) (B : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ((c ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I)

theorem kernel_line_shift {c : ℝ} (hc : 1 ≤ c) {W : ℂ → ℂ} (hW : StripM1 W) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I) =
      ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) := by
  have h1 := admiss_vert_rep hc hW hσ0 hσ1 hξ
  have h0 := admiss_vert_rep hc hW (le_refl (0 : ℝ)) zero_lt_one hξ
  rw [h0] at h1
  have hne : (((1 / (2 * Real.pi * ξ) : ℝ)) : ℂ) ≠ 0 := by
    have : (1 / (2 * Real.pi * ξ) : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have := mul_left_cancel₀ hne h1
  simpa using this.symm

lemma integrable_inv_sq_one_add_abs : Integrable (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (ae_of_all _ fun x => ?_)
  show (1 + ‖x‖) ^ (-(2 : ℝ)) = ((1 + |x|) ^ 2)⁻¹
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
  norm_cast

/-- `∫ (1 + a|τ|)^{-2} dτ = I₂ / a`, `I₂ = ∫ (1+|x|)^{-2}`. -/
lemma integral_inv_sq_scaled {a : ℝ} (ha : 0 < a) :
    Integrable (fun τ : ℝ => ((1 + a * |τ|) ^ 2)⁻¹) ∧
      ∫ τ : ℝ, ((1 + a * |τ|) ^ 2)⁻¹ = (∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) / a := by
  have heq : (fun τ : ℝ => ((1 + a * |τ|) ^ 2)⁻¹) = fun τ => (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) (a * τ) := by
    funext τ; simp [abs_mul, abs_of_pos ha]
  refine ⟨?_, ?_⟩
  · rw [heq]; exact integrable_inv_sq_one_add_abs.comp_mul_left' ha.ne'
  · rw [heq, Measure.integral_comp_mul_left (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) a, abs_of_pos (inv_pos.mpr ha)]
    simp [div_eq_inv_mul]

set_option maxHeartbeats 800000 in
theorem bump_main_density {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c ξ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 1 ≤ c → 0 < ξ →
      Real.log (Real.pi ^ 2 * ξ) ≤ b * δ / 2 → BumpProfile b δ M α β K B →
        ‖bumpHmain c B ξ‖ ≤ C * M * (c * δ)⁻¹ * bumpLambda α δ * Real.exp (-(κ * c * δ ^ (3 / 2 : ℝ))) := by
  obtain ⟨C2, hC2, hdecay⟩ := bump_laplace_decay (α := α) hb hβ K 2
  set k : ℝ := min (1 / 8) b with hk
  have hk0 : 0 < k := lt_min (by norm_num) hb
  have hk8 : k ≤ 1 / 8 := min_le_left _ _
  have hkb : k ≤ b := min_le_right _ _
  set I2 : ℝ := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ with hI2
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  refine ⟨k * b / 4, Real.exp (1 / 4) * C2 * I2 / Real.pi, by positivity, by positivity,
    fun B δ M c ξ hδ0 hδ1 hbδ hM hc hξ hL h => ?_⟩
  have hc0 : 0 < c := by linarith
  set σ : ℝ := k * Real.sqrt δ with hσ
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  have hσ0 : 0 < σ := mul_pos hk0 hsq
  have hsq1 : Real.sqrt δ ≤ 1 := by rw [Real.sqrt_le_one]; exact hδ1
  have hσ12 : σ ≤ 1 / 2 := by nlinarith
  have hW := bump_stripM1 (α := α) hb hβ K hδ0 hδ1 hbδ hM hc0 h
  have hshift : ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * bumpDW c B ((σ : ℂ) + (τ : ℂ) * Complex.I) =
      ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * bumpDW c B ((τ : ℂ) * Complex.I) :=
    kernel_line_shift hc hW hσ0.le (by linarith) hξ
  unfold bumpHmain
  rw [← hshift]
  -- pointwise bound
  set a : ℝ := c * δ with ha
  have ha0 : 0 < a := mul_pos hc0 hδ0
  set E : ℝ := Real.exp (-(k * b / 4 * c * δ ^ (3 / 2 : ℝ))) with hE
  have hδ32 : δ ^ (3 / 2 : ℝ) = δ * Real.sqrt δ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hδ0.le (by norm_num)]; norm_num
  have hexp : c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ)) - b * c * σ * δ ≤ -(k * b / 4 * c * δ ^ (3 / 2 : ℝ)) := by
    have h1 : σ * Real.log (Real.pi ^ 2 * ξ) ≤ σ * (b * δ / 2) := mul_le_mul_of_nonneg_left hL hσ0.le
    have hs2 : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
    have hk2 : (4 / 9 : ℝ) * k ^ 2 ≤ b / 4 := by
      have : k * k ≤ k * b := mul_le_mul_of_nonneg_left hkb hk0.le
      nlinarith
    have h3 : (4 / 9 : ℝ) * σ ^ 3 = (4 / 9) * k ^ 3 * Real.sqrt δ * δ := by
      rw [hσ]; have : Real.sqrt δ ^ 3 = Real.sqrt δ * δ := by rw [pow_succ, hs2]; ring
      calc (4 / 9 : ℝ) * (k * Real.sqrt δ) ^ 3 = (4 / 9) * k ^ 3 * Real.sqrt δ ^ 3 := by ring
        _ = _ := by rw [this]; ring
    rw [hδ32]
    have h4 : (4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ) - b * σ * δ ≤ -(k * b / 4 * (δ * Real.sqrt δ)) := by
      have : σ * (b * δ / 2) = k * Real.sqrt δ * (b * δ / 2) := by rw [hσ]
      rw [h3] at *
      have h5 : (4 / 9 : ℝ) * k ^ 3 * Real.sqrt δ * δ ≤ k * (b / 4) * Real.sqrt δ * δ := by
        have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hk0.le (mul_nonneg hsq.le hδ0.le))
        nlinarith
      rw [hσ] at h1 ⊢
      nlinarith [mul_nonneg hk0.le (mul_nonneg hsq.le hδ0.le), mul_nonneg hb.le (mul_nonneg hk0.le (mul_nonneg hsq.le hδ0.le))]
    nlinarith [mul_le_mul_of_nonneg_left h4 hc0.le]
  have hpt : ∀ τ : ℝ, ‖mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * bumpDW c B ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ * E) * ((1 + a * |τ|) ^ 2)⁻¹ := by
    intro τ
    have hK := norm_mellinK0_vert_le (c := c) (ξ := ξ) (s := σ) (τ := τ) hc0 hξ hσ0 hσ12
    have hD := hdecay B δ M c σ τ hδ0 hδ1 hbδ hM hc0 hσ0.le h
    have hlob := lobeU_nonneg τ
    have hc3 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc0 _
    have hK2 : ‖mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ‖ ≤
        2 * Real.exp (1 / 4) * Real.exp (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ))) := by
      refine hK.trans ?_
      have e1 : Real.exp (-(c * (2 * (3 / 56 : ℝ) * σ * lobeU τ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc0.le (mul_nonneg hσ0.le hlob)])
      have e2 : Real.exp (1 / (4 * c)) ≤ Real.exp (1 / 4) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have e3 := Real.exp_pos (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ)))
      calc 2 * Real.exp (1 / (4 * c)) * Real.exp (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ))) *
            Real.exp (-(c * (2 * (3 / 56 : ℝ) * σ * lobeU τ)))
          ≤ 2 * Real.exp (1 / 4) * Real.exp (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ))) * 1 := by gcongr
        _ = _ := by ring
    rw [norm_mul]
    have hDW : ‖bumpDW c B ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        c ^ (-(1 / 3 : ℝ)) * (C2 * M * bumpLambda α δ * Real.exp (-(b * c * σ * δ)) / (1 + c * δ * |τ|) ^ 2) := by
      unfold bumpDW
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc3]
      exact mul_le_mul_of_nonneg_left hD hc3.le
    have hΛ := one_le_bumpLambda (α := α) hδ0 hδ1
    calc ‖mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ‖ * ‖bumpDW c B ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ (2 * Real.exp (1 / 4) * Real.exp (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ)))) *
          (c ^ (-(1 / 3 : ℝ)) * (C2 * M * bumpLambda α δ * Real.exp (-(b * c * σ * δ)) / (1 + c * δ * |τ|) ^ 2)) :=
          mul_le_mul hK2 hDW (norm_nonneg _) (by positivity)
      _ = (Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ) *
          (Real.exp (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ))) * Real.exp (-(b * c * σ * δ))) *
          ((1 + a * |τ|) ^ 2)⁻¹ := by rw [ha]; ring
      _ ≤ (Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ * E) * ((1 + a * |τ|) ^ 2)⁻¹ := by
          have : Real.exp (c * ((4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ))) * Real.exp (-(b * c * σ * δ)) ≤ E := by
            rw [← Real.exp_add, hE]
            apply Real.exp_le_exp.mpr
            linarith
          have hpos : 0 ≤ Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ := by
            have : 0 ≤ bumpLambda α δ := by linarith
            positivity
          have hinv : 0 ≤ ((1 + a * |τ|) ^ 2)⁻¹ := by positivity
          calc _ ≤ (Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ) * E * ((1 + a * |τ|) ^ 2)⁻¹ := by
                gcongr
            _ = _ := by ring
  obtain ⟨hint, hval⟩ := integral_inv_sq_scaled ha0
  have hmaj := (hint.const_mul (Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ * E))
  have hI := norm_integral_le_of_norm_le hmaj (ae_of_all _ hpt)
  rw [integral_const_mul, hval] at hI
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hprod : c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
  rw [abs_of_pos (by positivity)]
  calc c ^ (1 / 3 : ℝ) / (2 * Real.pi) * ‖∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * bumpDW c B ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
      ≤ c ^ (1 / 3 : ℝ) / (2 * Real.pi) * ((Real.exp (1 / 4) * 2 * C2 * c ^ (-(1 / 3 : ℝ)) * M * bumpLambda α δ * E) * (I2 / a)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (Real.exp (1 / 4) * 2 * C2 * I2 / (2 * Real.pi)) * (M * a⁻¹ * bumpLambda α δ * E) * (c ^ (1 / 3 : ℝ) * c ^ (-(1 / 3 : ℝ))) := by
        ring
    _ = _ := by
        rw [hprod, ha]
        ring

/-- info: 'FormalResearch.SignUncertainty.kernel_line_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_line_shift

/-- info: 'FormalResearch.SignUncertainty.bump_main_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_main_density

end FormalResearch.SignUncertainty
