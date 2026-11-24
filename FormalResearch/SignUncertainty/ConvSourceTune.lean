module

public import FormalResearch.SignUncertainty.ConvSourceTail
public import FormalResearch.SignUncertainty.LiftSymbolOriginEdge

/-!
# The tuning of `η_c` in `thm:ce-hb-lift` (M6, step (2))

The pair of `thm:ce-hb-lift` requires `f₋(0) = 0`, where `f₋` is the `σ = -1` lift of the seed `Y = Y₀ + η g₁`:
`f₋(0) = W_Y(c^{1/3}) - W_Y(0)` (`exists_hankelEigenfn_lift_general`).  `W_Y(0) = k ∫ Y` and `W_{g₁}(0) = k` (as `∫ g₁ = 1`).
`exists_eta_tune`: if `|W_{g₁}(x)| ≤ k/2` at `x = c^{1/3}`, there is a real `η` with
`W_Y(x) - W_Y(0) = 0` and `|η| ≤ (2/k) |W_{Y₀}(x) - W_{Y₀}(0)|` (the paper's `η_c = W_{Q₀}(ε⁻¹)/(k - W_{g₁}(ε⁻¹)) = O(ε^{5/2})`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The lift symbol of a real seed is real at real arguments. -/
lemma liftSymbol_im_eq_zero_of_real (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (x : ℝ) :
    (liftSymbol X δ₀ m (x : ℂ)).im = 0 := by
  have h := liftSymbol_conj X δ₀ m (x : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma liftSymbol_zero_g1 (δ₀ : ℝ) (m : ℕ) :
    liftSymbol (ceG1 (airyZero 1)) δ₀ m 0 = (ceK : ℂ) := by
  rw [liftSymbol_zero_eq hasU2_ceG1, ceG1_integral_eq_one]; simp

/-- **Tuning of `η_c`.** -/
theorem exists_eta_tune {Y₀ : ℝ → ℝ} (hY : HasU2 Y₀) {δ₀ : ℝ} (m : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hgx : |(liftSymbol (ceG1 (airyZero 1)) δ₀ m (x : ℂ)).re| ≤ ceK / 2) :
    ∃ η : ℝ, liftSymbol (fun u => Y₀ u + η * ceG1 (airyZero 1) u) δ₀ m (x : ℂ) -
        liftSymbol (fun u => Y₀ u + η * ceG1 (airyZero 1) u) δ₀ m 0 = 0 ∧
      |η| ≤ 2 / ceK * ‖liftSymbol Y₀ δ₀ m (x : ℂ) - liftSymbol Y₀ δ₀ m 0‖ := by
  have hk := ceK_pos
  have hg := hasU2_ceG1
  set Wg := liftSymbol (ceG1 (airyZero 1)) δ₀ m (x : ℂ) with hWg
  set Wy := liftSymbol Y₀ δ₀ m (x : ℂ) with hWy
  set Wy0 := liftSymbol Y₀ δ₀ m 0 with hWy0
  have hWg_im : Wg.im = 0 := liftSymbol_im_eq_zero_of_real _ _ _ _
  have hWy_im : Wy.im = 0 := liftSymbol_im_eq_zero_of_real _ _ _ _
  have hWy0_re : Wy0 = ((ceK * ∫ u : ℝ, Y₀ u : ℝ) : ℂ) := liftSymbol_zero_eq hY δ₀ m
  have hWg_re : Wg = (Wg.re : ℂ) := Complex.ext (by simp) (by simp [hWg_im])
  have hWy_re : Wy = (Wy.re : ℂ) := Complex.ext (by simp) (by simp [hWy_im])
  have hden : Wg.re - ceK ≤ -(ceK / 2) := by
    have := (abs_le.mp hgx).2; linarith
  have hden0 : Wg.re - ceK ≠ 0 := by intro h; linarith
  set N : ℝ := Wy.re - ceK * ∫ u : ℝ, Y₀ u with hN
  set η : ℝ := -N / (Wg.re - ceK) with hη
  have hlin : ∀ w : ℂ, 0 ≤ w.re → liftSymbol (fun u => Y₀ u + η * ceG1 (airyZero 1) u) δ₀ m w =
      liftSymbol Y₀ δ₀ m w + (η : ℂ) * liftSymbol (ceG1 (airyZero 1)) δ₀ m w := fun w hw => by
    rw [liftSymbol_add_seed hY (hg.smul η) δ₀ m hw, liftSymbol_const_mul_seed]
  have hx' : 0 ≤ ((x : ℝ) : ℂ).re := by simpa using hx
  refine ⟨η, ?_, ?_⟩
  · rw [hlin _ hx', hlin 0 (by simp), liftSymbol_zero_g1, ← hWg, ← hWy, ← hWy0, hWy0_re]
    have hηe : η * (Wg.re - ceK) = -N := by rw [hη]; field_simp
    have : Wy + (η : ℂ) * Wg - (((ceK * ∫ u : ℝ, Y₀ u : ℝ) : ℂ) + (η : ℂ) * (ceK : ℂ)) =
        ((N + η * (Wg.re - ceK) : ℝ) : ℂ) := by
      push_cast
      rw [hN]; push_cast
      linear_combination hWy_re + (η : ℂ) * hWg_re
    rw [this, hηe]; simp
  · have hnorm : ‖Wy - Wy0‖ = |N| := by
      rw [hWy0_re, hWy_re, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hη, abs_div, abs_neg]
    have hd : ceK / 2 ≤ |Wg.re - ceK| := by
      rw [abs_of_neg (by linarith)]; linarith
    calc |N| / |Wg.re - ceK| ≤ |N| / (ceK / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
      _ = 2 / ceK * |N| := by field_simp

/-- info: 'FormalResearch.SignUncertainty.exists_eta_tune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_eta_tune

end FormalResearch.SignUncertainty
