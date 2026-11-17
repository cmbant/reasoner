module

public import FormalResearch.Special.AiryFourier

/-!
# Abel-regularised orthogonality of the Airy transform

`Ai ∉ L²(ℝ)` (`|Ai(-y)|² ≍ y^{-1/2}`), so the orthogonality relation `∫_ℝ Ai(x) Ai(x+t) dx = δ(t)` of the
Airy transform (DLMF 9.11.15; unitarity of `f ↦ ∫ Ai(x+s) f(s) ds`) is a distributional/conditionally convergent
statement.  Its Abel-regularised form is an exact closed formula, proved here from the Fourier representation
of `e^{cx} Ai(x)` of `AiryFourier` by Mathlib's multiplication formula `∫ 𝓕f · g = ∫ f · 𝓕g`, Fourier inversion
and the Gaussian Fourier transform (the cubic terms of the two symbols cancel, `(c+is)³ + (c-is)³ = 2c³ - 6cs²`):

* `integral_airyAi_mul_airyAi_shift`: for `ε > 0`,
  `∫_ℝ Ai(x) Ai(x+t) e^{εx} dx = exp(ε³/12 - εt/2 - t²/(4ε)) / (2 √(πε))`;
* `integral_airyAi_sq_mul_exp`: `t = 0`: `∫ Ai(x)² e^{εx} dx = e^{ε³/12}/(2√(πε)) → ∞` (`ε → 0⁺`, as `Ai ∉ L²`);
* `tendsto_integral_airyAi_mul_airyAi_shift`: for `t ≠ 0` the Abel limit is `0` (orthogonality).

Numerical check (mpmath, 20 digits, `quad` on `[-60,30]`): `(ε,t) = (1,0.5), (0.8,-1.2), (1.5,2)` give
`0.2243206471606789…, 0.33916326456144…, 0.03495613307814…`, equal to the closed formula to `≥ 15` digits.

**Not formalised here:** the statement as a distribution identity `∫ Ai(x+s) Ai(x+t) dx = δ(s-t)` (test functions).  Unitarity on `L²` (via the Fourier side, `AiryTransformDef`: `airyTransform_norm`) and the projection property `K_Ai² = K_Ai` (`isStarProjection_airyKAi`, `AiryTransformProj`) are formalised in `AiryTransform*`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.Special


lemma airyGram_four_tilt {c : ℝ} (hc : 0 < c) (w : ℝ) : 𝓕 (airyTilt c) w = airyFourierH c (-w) := by
  have hH_cont : Continuous (airyFourierH c) := by
    unfold airyFourierH
    exact (continuous_airyFourierSymbol c).comp (by fun_prop)
  have hH_int : Integrable (airyFourierH c) := by
    unfold airyFourierH
    exact (integrable_airyFourierSymbol hc).comp_mul_left' (by positivity)
  have hF : 𝓕 (airyFourierH c) = airyTilt c := funext (fourier_airyFourierH hc)
  have hinv := hH_cont.fourierInv_fourier_eq hH_int (by rw [hF]; exact integrable_airyTilt hc)
  have h1 := congrFun hinv (-w)
  rw [hF, Real.fourierInv_eq_fourier_neg, neg_neg] at h1
  exact h1

lemma airyGram_trans (c t : ℝ) (w : ℝ) :
    𝓕 (fun x => airyTilt c (x + t)) w = Complex.exp (((2 * π * (t * w) : ℝ) : ℂ) * I) * 𝓕 (airyTilt c) w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := volume) (fun y : ℝ =>
    Complex.exp (((-2 * π * (y - t) * w : ℝ) : ℂ) * I) * airyTilt c y) t
  simp only [add_sub_cancel_right] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

lemma airyGram_fourier {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ x : ℝ, airyTilt c x * airyTilt c (x + t) =
      ∫ ξ : ℝ, airyFourierH c ξ * (Complex.exp (((2 * π * (t * ξ) : ℝ) : ℂ) * I) * airyFourierH c (-ξ)) := by
  have hH_int : Integrable (airyFourierH c) := by
    unfold airyFourierH
    exact (integrable_airyFourierSymbol hc).comp_mul_left' (by positivity)
  have hF : 𝓕 (airyFourierH c) = airyTilt c := funext (fourier_airyFourierH hc)
  have hφ : Integrable (fun x => airyTilt c (x + t)) :=
    (integrable_airyTilt hc).comp_add_right t
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (e := Real.fourierChar)
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner hH_int hφ
  simp only [smul_eq_mul] at h
  have hfl : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hfl] at h
  have h' : ∫ ξ, 𝓕 (airyFourierH c) ξ * airyTilt c (ξ + t) =
      ∫ x, airyFourierH c x * 𝓕 (fun x => airyTilt c (x + t)) x := h
  rw [hF] at h'
  rw [h']
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [airyGram_trans, airyGram_four_tilt hc]

lemma airyGram_H_mul_neg (c ξ : ℝ) :
    airyFourierH c ξ * airyFourierH c (-ξ) =
      Complex.exp (((2 * c ^ 3 / 3 : ℝ) : ℂ)) * Complex.exp (-(((8 * π ^ 2 * c : ℝ) : ℂ)) * (ξ : ℂ) ^ 2) := by
  unfold airyFourierH airyFourierSymbol airyLine
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (2 * (c : ℂ) * (2 * (π : ℂ) * ξ) ^ 2) * Complex.I_sq

lemma airyGram_tilt {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ x : ℝ, airyTilt c x * airyTilt c (x + t) =
      (((Real.exp (2 * c ^ 3 / 3) * (√(π / (8 * π ^ 2 * c)) * Real.exp (-(2 * π * t) ^ 2 / (4 * (8 * π ^ 2 * c)))) : ℝ)) : ℂ) := by
  rw [airyGram_fourier hc t]
  have e : ∀ ξ : ℝ, airyFourierH c ξ * (Complex.exp (((2 * π * (t * ξ) : ℝ) : ℂ) * I) * airyFourierH c (-ξ)) =
      Complex.exp (((2 * c ^ 3 / 3 : ℝ) : ℂ)) *
        (Complex.exp (I * ((2 * π * t : ℝ) : ℂ) * (ξ : ℂ)) * Complex.exp (-(((8 * π ^ 2 * c : ℝ) : ℂ)) * (ξ : ℂ) ^ 2)) := by
    intro ξ
    have := airyGram_H_mul_neg c ξ
    calc _ = Complex.exp (((2 * π * (t * ξ) : ℝ) : ℂ) * I) * (airyFourierH c ξ * airyFourierH c (-ξ)) := by ring
      _ = _ := by
        rw [this]
        have : Complex.exp (((2 * π * (t * ξ) : ℝ) : ℂ) * I) = Complex.exp (I * ((2 * π * t : ℝ) : ℂ) * (ξ : ℂ)) := by
          congr 1; push_cast; ring
        rw [this]; ring
  simp_rw [e]
  rw [integral_const_mul]
  have hb : 0 < (((8 * π ^ 2 * c : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  rw [fourierIntegral_gaussian hb]
  have hpos : 0 ≤ π / (8 * π ^ 2 * c) := by positivity
  have hsq : ((π : ℂ) / ((8 * π ^ 2 * c : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((√(π / (8 * π ^ 2 * c)) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos]
    push_cast; rfl
  rw [hsq]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 4
  push_cast
  ring

/-- **Abel-regularised orthogonality of Airy translates**: for `ε > 0`,
`∫_ℝ Ai(x) Ai(x+t) e^{εx} dx = exp(ε³/12 - εt/2 - t²/(4ε)) / (2 √(πε))`. -/
theorem integral_airyAi_mul_airyAi_shift {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ x : ℝ, airyAi x * airyAi (x + t) * Real.exp (ε * x) =
      Real.exp (ε ^ 3 / 12 - ε * t / 2 - t ^ 2 / (4 * ε)) / (2 * √(π * ε)) := by
  have hc : 0 < ε / 2 := by positivity
  have h := airyGram_tilt hc t
  have hL : ∀ x : ℝ, airyTilt (ε / 2) x * airyTilt (ε / 2) (x + t) =
      ((airyAi x * airyAi (x + t) * Real.exp (ε * x) * Real.exp (ε * t / 2) : ℝ) : ℂ) := by
    intro x
    unfold airyTilt
    push_cast
    have : cexp (↑ε / 2 * ↑x) * cexp (↑ε / 2 * (↑x + ↑t)) = cexp (↑ε * ↑x) * cexp (↑ε * ↑t / 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    calc _ = (↑(airyAi x) * ↑(airyAi (x + t))) * (cexp (↑ε / 2 * ↑x) * cexp (↑ε / 2 * (↑x + ↑t))) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [hL] at h
  rw [integral_complex_ofReal, integral_mul_const] at h
  have h' := Complex.ofReal_injective h
  have hs : 0 < √(π * ε) := Real.sqrt_pos.mpr (by positivity)
  have hexp : Real.exp (ε * t / 2) ≠ 0 := (Real.exp_pos _).ne'
  have e1 : √(π / (8 * π ^ 2 * (ε / 2))) = 1 / (2 * √(π * ε)) := by
    rw [show π / (8 * π ^ 2 * (ε / 2)) = (1 / (2 * √(π * ε))) ^ 2 by
      have := Real.sq_sqrt (show 0 ≤ π * ε by positivity)
      field_simp; nlinarith [this]]
    exact Real.sqrt_sq (by positivity)
  have e2 : Real.exp (2 * (ε / 2) ^ 3 / 3) * (1 / (2 * √(π * ε)) *
      Real.exp (-(2 * π * t) ^ 2 / (4 * (8 * π ^ 2 * (ε / 2))))) =
      Real.exp (ε ^ 3 / 12 - ε * t / 2 - t ^ 2 / (4 * ε)) / (2 * √(π * ε)) * Real.exp (ε * t / 2) := by
    rw [show ε ^ 3 / 12 - ε * t / 2 - t ^ 2 / (4 * ε) =
      2 * (ε / 2) ^ 3 / 3 + -(2 * π * t) ^ 2 / (4 * (8 * π ^ 2 * (ε / 2))) + (-(ε * t / 2)) by
        field_simp; ring, Real.exp_add, Real.exp_add, Real.exp_neg]
    field_simp
  rw [e1, e2] at h'
  exact mul_right_cancel₀ hexp h'

/-- `t = 0`: `∫ Ai(x)² e^{εx} dx = e^{ε³/12} / (2 √(πε))`. -/
theorem integral_airyAi_sq_mul_exp {ε : ℝ} (hε : 0 < ε) :
    ∫ x : ℝ, airyAi x ^ 2 * Real.exp (ε * x) = Real.exp (ε ^ 3 / 12) / (2 * √(π * ε)) := by
  have := integral_airyAi_mul_airyAi_shift hε 0
  simpa [sq] using this

/-- For `t ≠ 0` the regularised pairing tends to `0` as `ε → 0⁺`. -/
theorem tendsto_integral_airyAi_mul_airyAi_shift {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, airyAi x * airyAi (x + t) * Real.exp (ε * x)) (𝓝[>] 0) (𝓝 0) := by
  have hrw : ∀ᶠ ε : ℝ in 𝓝[>] 0, Real.exp (ε ^ 3 / 12 - ε * t / 2) / (2 * √π) *
      ((ε⁻¹) ^ (1 / 2 : ℝ) * Real.exp (-(t ^ 2 / 4) * ε⁻¹)) =
      ∫ x : ℝ, airyAi x * airyAi (x + t) * Real.exp (ε * x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    rw [integral_airyAi_mul_airyAi_shift hε' t, Real.sqrt_mul Real.pi_pos.le,
      Real.inv_rpow hε'.le, ← Real.sqrt_eq_rpow]
    have hsε : 0 < √ε := Real.sqrt_pos.mpr hε'
    have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    rw [show ε ^ 3 / 12 - ε * t / 2 - t ^ 2 / (4 * ε) = (ε ^ 3 / 12 - ε * t / 2) + (-(t ^ 2 / 4) * ε⁻¹) by
      field_simp; ring, Real.exp_add]
    field_simp
  refine Tendsto.congr' hrw ?_
  have h1 : Tendsto (fun ε : ℝ => Real.exp (ε ^ 3 / 12 - ε * t / 2) / (2 * √π)) (𝓝[>] 0)
      (𝓝 (1 / (2 * √π))) := by
    have hc : Continuous fun ε : ℝ => Real.exp (ε ^ 3 / 12 - ε * t / 2) / (2 * √π) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h2 : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (1 / 2 : ℝ) * Real.exp (-(t ^ 2 / 4) * ε⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have hb : 0 < t ^ 2 / 4 := by positivity
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2 : ℝ) (t ^ 2 / 4) hb
    refine (this.comp tendsto_inv_nhdsGT_zero).congr fun ε => ?_
    simp [neg_mul]
  simpa using h1.mul h2

/-- info: 'FormalResearch.Special.integral_airyAi_mul_airyAi_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyAi_mul_airyAi_shift

/-- info: 'FormalResearch.Special.tendsto_integral_airyAi_mul_airyAi_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_integral_airyAi_mul_airyAi_shift

/-- info: 'FormalResearch.Special.integral_airyAi_sq_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyAi_sq_mul_exp

end FormalResearch.Special
