module

public import Mathlib
public import FormalResearch.SignUncertainty.HankelModular

/-!
# `ct:boas` Step 1: the Gaussian-window convolution identity

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:boas` Step 1 (the identity
`ψ̃^(k) = conj F(k) - ∫ ŝ_near(ω) conj F(k-ω) dω`).  **Proved** (Fourier analysis only).

For `h ∈ L¹(ℝ)` (real; in the application `h = 1_{Δ>0} f ρ₀`), `Fh(z) = ∫ h(s) e^{2πizs} ds`, a window
`s_{D,W}(Δ) = ∫_{-D}^{D} G_W(Δ - x) dx` (`G_W` the centred Gaussian density of standard deviation `W`),
`windowFT D W ω = e^{-2π²W²ω²} ∫_{-D}^{D} e^{-2πiωx} dx`:

* `windowCoeff_eq`: `∫ s_{D,W}(Δ) h(Δ) e^{-2πiνΔ} dΔ = ∫ windowFT D W ω · Fh(ω - ν) dω`;
* `norm_windowFT_le`: `|windowFT D W ω| ≤ 2D e^{-2π²W²ω²}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtBoasWindow

/-- Centred Gaussian density of standard deviation `W`. -/
noncomputable def gaussK (W y : ℝ) : ℝ := Real.exp (-(1 / (2 * W ^ 2)) * y ^ 2) / (√(2 * π) * W)

/-- The window `s_{D,W}(Δ) = ∫_{-D}^{D} G_W(Δ - x) dx`. -/
noncomputable def sWin (D W Δ : ℝ) : ℝ := ∫ x in Icc (-D) D, gaussK W (Δ - x)

/-- The transform of the window. -/
noncomputable def windowFT (D W ω : ℝ) : ℂ :=
  (Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2) : ℂ) *
    ∫ x in Icc (-D) D, Complex.exp (-(2 * π * Complex.I * ω * x))

/-- The transform of `h`: `Fh(z) = ∫ h(s) e^{2πizs} ds`. -/
noncomputable def Fh (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ s, (h s : ℂ) * Complex.exp (2 * π * Complex.I * z * s)

lemma gauss_fourier {W : ℝ} (hW : 0 < W) (y : ℝ) :
    ∫ ω : ℝ, Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 + 2 * π * Complex.I * y * ω) =
      (gaussK W y : ℂ) := by
  have hpos : 0 < 2 * π ^ 2 * W ^ 2 := by positivity
  have hb : ((-(2 * π ^ 2 * W ^ 2) : ℝ) : ℂ).re < 0 := by
    simp only [Complex.ofReal_re]; linarith
  have key := integral_cexp_quadratic hb (2 * π * Complex.I * y) 0
  have e1 : ∀ ω : ℝ, Complex.exp (((-(2 * π ^ 2 * W ^ 2) : ℝ) : ℂ) * ω ^ 2 + 2 * π * Complex.I * y * ω + 0) =
      Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 + 2 * π * Complex.I * y * ω) := by
    intro ω; push_cast; ring_nf
  simp_rw [e1] at key
  rw [key]
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e2 : (π : ℂ) / -(((-(2 * π ^ 2 * W ^ 2) : ℝ) : ℂ)) = (((1 / (2 * π * W ^ 2)) : ℝ) : ℂ) := by
    push_cast; field_simp
  have hc := Complex.ofReal_cpow (show (0 : ℝ) ≤ 1 / (2 * π * W ^ 2) by positivity) (1 / 2)
  have h12 : (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [h12] at hc
  rw [e2, ← hc]
  have e3 : (1 / (2 * π * W ^ 2)) ^ (1 / 2 : ℝ) = 1 / (√(2 * π) * W) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hW.le]
  rw [e3]
  unfold gaussK
  have e4 : (0 : ℂ) - (2 * π * Complex.I * y) ^ 2 / (4 * ((-(2 * π ^ 2 * W ^ 2) : ℝ) : ℂ)) =
      ((-(1 / (2 * W ^ 2)) * y ^ 2 : ℝ) : ℂ) := by
    push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e4, ← Complex.ofReal_exp]
  push_cast; ring

lemma norm_windowFT_le {D : ℝ} (hD : 0 ≤ D) (W ω : ℝ) :
    ‖windowFT D W ω‖ ≤ 2 * D * Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2) := by
  unfold windowFT
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : ‖∫ x in Icc (-D) D, Complex.exp (-(2 * π * Complex.I * ω * x))‖ ≤ 2 * D := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-D) D) (C := 1)
      (f := fun x : ℝ => Complex.exp (-(2 * π * Complex.I * ω * x)))
      (by simp [Real.volume_Icc]) (fun x _ => by
        rw [Complex.norm_exp]; simp)
    have h' := by simpa [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ D - -D),
      show D - -D = 2 * D by ring] using h
    rcases h' with h' | h'
    · exact h'
    · rw [h']; simp; linarith
  calc Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2) *
        ‖∫ x in Icc (-D) D, Complex.exp (-(2 * π * Complex.I * ω * x))‖
      ≤ Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2) * (2 * D) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = _ := by ring

lemma sWin_repr {D : ℝ} {W : ℝ} (hW : 0 < W) (Δ : ℝ) :
    (sWin D W Δ : ℂ) = ∫ ω : ℝ, windowFT D W ω * Complex.exp (2 * π * Complex.I * ω * Δ) := by
  set μ : Measure ℝ := volume.restrict (Icc (-D) D) with hμ
  set E : ℝ → ℝ → ℂ := fun x ω => Complex.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2 +
      2 * π * Complex.I * ((Δ - x : ℝ) : ℂ) * ω) with hE
  have h1 : (sWin D W Δ : ℂ) = ∫ x, ∫ ω, E x ω ∂volume ∂μ := by
    unfold sWin
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (gauss_fourier hW (Δ - x)).symm
  have hint : Integrable (Function.uncurry E) (μ.prod volume) := by
    have hb : Integrable (fun ω : ℝ => Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2)) :=
      integrable_exp_neg_mul_sq (by positivity)
    have hg : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * Real.exp (-(2 * π ^ 2 * W ^ 2) * p.2 ^ 2))
        (μ.prod volume) := by
      have : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const _
      exact this.mul_prod hb
    refine Integrable.mono' hg ?_ (ae_of_all _ fun p => ?_)
    · exact (by simp only [hE, Function.uncurry]; fun_prop : Continuous (Function.uncurry E)).aestronglyMeasurable
    · have hre : (-(2 * (π : ℂ) ^ 2 * (W : ℂ) ^ 2) * (p.2 : ℂ) ^ 2 +
          2 * π * Complex.I * ((Δ - p.1 : ℝ) : ℂ) * (p.2 : ℂ)).re = -(2 * π ^ 2 * W ^ 2) * p.2 ^ 2 := by
        have : (-(2 * (π : ℂ) ^ 2 * (W : ℂ) ^ 2) * (p.2 : ℂ) ^ 2 +
            2 * π * Complex.I * ((Δ - p.1 : ℝ) : ℂ) * (p.2 : ℂ)) =
            ((-(2 * π ^ 2 * W ^ 2) * p.2 ^ 2 : ℝ) : ℂ) + ((2 * π * (Δ - p.1) * p.2 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
        ring
      simp only [hE, Function.uncurry]
      rw [Complex.norm_exp, hre, one_mul]
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have e : ∀ x : ℝ, E x ω = (Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2) : ℂ) *
      Complex.exp (2 * π * Complex.I * ω * Δ) * Complex.exp (-(2 * π * Complex.I * ω * x)) := by
    intro x
    simp only [hE]
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [e]
  rw [integral_const_mul]
  unfold windowFT
  ring

lemma stronglyMeasurable_windowFT (D W : ℝ) : StronglyMeasurable (windowFT D W) := by
  unfold windowFT
  refine (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun ω : ℝ =>
    Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2))).stronglyMeasurable.mul ?_
  have : StronglyMeasurable (Function.uncurry fun (ω x : ℝ) =>
      Complex.exp (-(2 * π * Complex.I * ω * x))) :=
    (by fun_prop : Continuous (Function.uncurry fun (ω x : ℝ) =>
      Complex.exp (-(2 * π * Complex.I * ω * x)))).stronglyMeasurable
  exact this.integral_prod_right (ν := volume.restrict (Icc (-D) D))

/-- **Window convolution identity.** For `h ∈ L¹(ℝ)`, `W > 0`, `D ≥ 0`, real `ν`:
`∫ s_{D,W}(Δ) h(Δ) e^{-2πiνΔ} dΔ = ∫ windowFT(ω) · Fh(ω - ν) dω`. -/
theorem windowCoeff_eq {h : ℝ → ℝ} (hh : Integrable h) {D W : ℝ} (hW : 0 < W) (hD : 0 ≤ D) (ν : ℝ) :
    ∫ Δ : ℝ, (sWin D W Δ : ℂ) * (h Δ : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * Δ)) =
      ∫ ω : ℝ, windowFT D W ω * Fh h ((ω - ν : ℝ) : ℂ) := by
  set Φ : ℝ → ℝ → ℂ := fun Δ ω => windowFT D W ω *
      ((h Δ : ℂ) * Complex.exp (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * Δ)) with hΦ
  have h1 : ∀ Δ : ℝ, (sWin D W Δ : ℂ) * (h Δ : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * Δ)) =
      ∫ ω, Φ Δ ω := by
    intro Δ
    rw [sWin_repr hW Δ, ← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [hΦ]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [show (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * Δ) =
      (2 * π * Complex.I * ω * Δ) + (-(2 * π * Complex.I * ν * Δ)) by push_cast; ring, Complex.exp_add]
    ring
  simp_rw [h1]
  have hint : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    have hb : Integrable (fun ω : ℝ => 2 * D * Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2)) :=
      (integrable_exp_neg_mul_sq (by positivity)).const_mul _
    have hg : Integrable (fun p : ℝ × ℝ => ‖h p.1‖ * (2 * D * Real.exp (-(2 * π ^ 2 * W ^ 2) * p.2 ^ 2)))
        (volume.prod volume) := hh.norm.mul_prod hb
    refine Integrable.mono' hg ?_ (ae_of_all _ fun p => ?_)
    · have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ => windowFT D W p.2) (volume.prod volume) :=
        ((stronglyMeasurable_windowFT D W).measurable.comp measurable_snd).aestronglyMeasurable
      have m2 : AEStronglyMeasurable (fun p : ℝ × ℝ => (h p.1 : ℂ)) (volume.prod volume) :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable).comp_fst
      have m3 : AEStronglyMeasurable (fun p : ℝ × ℝ => Complex.exp (2 * π * Complex.I * ((p.2 - ν : ℝ) : ℂ) * p.1))
          (volume.prod volume) :=
        (by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (2 * π * Complex.I * ((p.2 - ν : ℝ) : ℂ) * p.1)).aestronglyMeasurable
      exact m1.mul (m2.mul m3)
    · obtain ⟨Δ, ω⟩ := p
      simp only [hΦ, Function.uncurry]
      rw [norm_mul, norm_mul, Complex.norm_real]
      have he : ‖Complex.exp (2 * π * Complex.I * ((ω - ν : ℝ) : ℂ) * Δ)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [he, mul_one]
      calc ‖windowFT D W ω‖ * ‖h Δ‖ ≤ (2 * D * Real.exp (-(2 * π ^ 2 * W ^ 2) * ω ^ 2)) * ‖h Δ‖ :=
            mul_le_mul_of_nonneg_right (norm_windowFT_le hD W ω) (norm_nonneg _)
        _ = _ := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hΦ]
  rw [integral_const_mul]
  unfold Fh
  rfl

/-- **Window coefficient bound.** Under the hypotheses `‖Fh(x)‖ ≤ M` for all real `x` and
`‖Fh(ω - ν)‖ ≤ a` for `|ω| ≤ ρ` (`a, M ≥ 0`), with `b = 2π²W²`,
`‖∫ s_{D,W} h e^{-2πiνΔ}‖ ≤ 2D ( a √(π/b) + M e^{-bρ²/2} √(2π/b) )`. -/
theorem windowCoeff_bound {h : ℝ → ℝ} (hh : Integrable h) {D W : ℝ} (hW : 0 < W) (hD : 0 ≤ D)
    (ν ρ a M : ℝ) (hρ0 : 0 ≤ ρ) (ha : 0 ≤ a) (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, ‖Fh h (x : ℂ)‖ ≤ M)
    (hρ : ∀ ω : ℝ, |ω| ≤ ρ → ‖Fh h ((ω - ν : ℝ) : ℂ)‖ ≤ a) :
    ‖∫ Δ : ℝ, (sWin D W Δ : ℂ) * (h Δ : ℂ) * Complex.exp (-(2 * π * Complex.I * ν * Δ))‖ ≤
      2 * D * (a * √(π / (2 * π ^ 2 * W ^ 2)) +
        M * Real.exp (-(2 * π ^ 2 * W ^ 2) * ρ ^ 2 / 2) * √(2 * π / (2 * π ^ 2 * W ^ 2))) := by
  rw [windowCoeff_eq hh hW hD ν]
  set b : ℝ := 2 * π ^ 2 * W ^ 2 with hb
  have hb0 : 0 < b := by positivity
  have i1 : Integrable (fun ω : ℝ => Real.exp (-b * ω ^ 2)) := integrable_exp_neg_mul_sq hb0
  have i2 : Integrable (fun ω : ℝ => Real.exp (-(b / 2) * ω ^ 2)) := integrable_exp_neg_mul_sq (by positivity)
  have hG : Integrable (fun ω : ℝ => 2 * D * (a * Real.exp (-b * ω ^ 2) +
      M * Real.exp (-b * ρ ^ 2 / 2) * Real.exp (-(b / 2) * ω ^ 2))) :=
    (((i1.const_mul a).add (i2.const_mul (M * Real.exp (-b * ρ ^ 2 / 2)))).const_mul (2 * D))
  refine (norm_integral_le_of_norm_le hG (ae_of_all _ fun ω => ?_)).trans ?_
  · rw [norm_mul]
    have h1 := norm_windowFT_le hD W ω
    rw [← hb] at h1
    have hF0 : 0 ≤ ‖Fh h ((ω - ν : ℝ) : ℂ)‖ := norm_nonneg _
    have hE : 0 ≤ Real.exp (-b * ω ^ 2) := (Real.exp_pos _).le
    have hcase : ‖Fh h ((ω - ν : ℝ) : ℂ)‖ * Real.exp (-b * ω ^ 2) ≤
        a * Real.exp (-b * ω ^ 2) + M * Real.exp (-b * ρ ^ 2 / 2) * Real.exp (-(b / 2) * ω ^ 2) := by
      by_cases hw : |ω| ≤ ρ
      · have := mul_le_mul_of_nonneg_right (hρ ω hw) hE
        have hpos : 0 ≤ M * Real.exp (-b * ρ ^ 2 / 2) * Real.exp (-(b / 2) * ω ^ 2) := by positivity
        linarith
      · rw [not_le] at hw
        have hm := mul_le_mul_of_nonneg_right (hM (ω - ν)) hE
        have hsq : ρ ^ 2 ≤ ω ^ 2 := by
          have := pow_le_pow_left₀ hρ0 hw.le 2
          rwa [sq_abs] at this
        have hexp : Real.exp (-b * ω ^ 2) ≤ Real.exp (-b * ρ ^ 2 / 2) * Real.exp (-(b / 2) * ω ^ 2) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
        have : M * Real.exp (-b * ω ^ 2) ≤ M * (Real.exp (-b * ρ ^ 2 / 2) * Real.exp (-(b / 2) * ω ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp hM0
        have hpos : 0 ≤ a * Real.exp (-b * ω ^ 2) := by positivity
        linarith
    calc ‖windowFT D W ω‖ * ‖Fh h ((ω - ν : ℝ) : ℂ)‖
        ≤ (2 * D * Real.exp (-b * ω ^ 2)) * ‖Fh h ((ω - ν : ℝ) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right h1 hF0
      _ = 2 * D * (‖Fh h ((ω - ν : ℝ) : ℂ)‖ * Real.exp (-b * ω ^ 2)) := by ring
      _ ≤ 2 * D * (a * Real.exp (-b * ω ^ 2) + M * Real.exp (-b * ρ ^ 2 / 2) * Real.exp (-(b / 2) * ω ^ 2)) :=
          mul_le_mul_of_nonneg_left hcase (by linarith)
  · rw [integral_const_mul, integral_add (i1.const_mul a) (i2.const_mul _), integral_const_mul,
      integral_const_mul, integral_gaussian, integral_gaussian]
    have : √(π / (b / 2)) = √(2 * π / b) := by
      congr 1; field_simp
    rw [this]

/-- info: 'FormalResearch.SignUncertainty.CtBoasWindow.windowCoeff_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.CtBoasWindow.windowCoeff_bound

end FormalResearch.SignUncertainty.CtBoasWindow
