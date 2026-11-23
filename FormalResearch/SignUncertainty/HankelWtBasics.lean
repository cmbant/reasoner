module

public import FormalResearch.SignUncertainty.HankelStripInversion

/-!
# Basic properties of `W̃_c(ζ) = e^{-cℋ(ζ)} M̃_f(c(1-ζ))` (`gt:7.4`)

`hankelWt_norm_le`: `‖W̃_c(ζ)‖ ≤ M[f] ‖1+ζ‖^{1/2} e^{1/(6c)}` on `0 ≤ Re ζ < 1`;
`hankelWt_differentiableOn`: `W̃_c` is holomorphic on `0 < Re ζ < 1`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

lemma hankelWt_norm_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    ‖hankelWt c f ζ‖ ≤ hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) := by
  have h := norm_mellinStrip_le_majorant hc hf hε hζ0 hζ1
  unfold hankelWt
  rw [norm_mul, Complex.norm_exp]
  have hre2 : (-((c : ℂ) * hInt ζ)).re = -(c * (hInt ζ).re) := by simp
  rw [hre2]
  calc Real.exp (-(c * (hInt ζ).re)) * ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖
      ≤ Real.exp (-(c * (hInt ζ).re)) *
        (hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (c * (hInt ζ).re + 1 / (6 * c))) := by gcongr
    _ = hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) := by
        rw [Real.exp_add]
        have : Real.exp (-(c * (hInt ζ).re)) * Real.exp (c * (hInt ζ).re) = 1 := by
          rw [← Real.exp_add]; simp
        calc _ = (Real.exp (-(c * (hInt ζ).re)) * Real.exp (c * (hInt ζ).re)) *
            (hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c))) := by ring
          _ = _ := by rw [this, one_mul]

lemma hankelWt_differentiableOn {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (hankelWt c f) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
  have hH : DifferentiableOn ℂ hInt {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    differentiableOn_hInt.mono (fun ζ hζ => ⟨by linarith [hζ.1], by linarith [hζ.2]⟩)
  have hlin2 : DifferentiableOn ℂ (fun ζ : ℂ => (c : ℂ) * (1 - ζ)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
    fun_prop
  have hM : DifferentiableOn ℂ (fun ζ : ℂ => mellinStrip f ((c : ℂ) * (1 - ζ)))
      {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
    refine (differentiableOn_mellinStrip hc hf).comp hlin2 (fun ζ hζ => ?_)
    have hre : ((c : ℂ) * (1 - ζ)).re = c * (1 - ζ.re) := by simp
    refine ⟨?_, ?_⟩ <;> simp only [hre] <;> nlinarith [hζ.1, hζ.2]
  exact ((hH.const_mul (c : ℂ)).neg.cexp).mul hM

/-- info: 'FormalResearch.SignUncertainty.hankelWt_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWt_norm_le

/-- info: 'FormalResearch.SignUncertainty.hankelWt_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWt_differentiableOn

end FormalResearch.SignUncertainty
