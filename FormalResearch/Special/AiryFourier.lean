module

public import FormalResearch.Special.AiryBound
public import FormalResearch.Special.AiryReal

/-!
# The Fourier–Laplace side of the Airy function

`Ai(x) = (1/2π) ∫ exp((c+is)³/3 - x(c+is)) ds` says that `e^{cx} Ai(x)` is the (inverse) Fourier
transform of the Gaussian-decaying symbol `s ↦ exp((c+is)³/3)`.  `Ai` itself is not absolutely
integrable on `(-∞, 0)` (it oscillates with envelope `|x|^{-1/4}`), so the formal identity
`∫ Ai(x) e^{-iωx} dx = e^{iω³/3}` is proved here in its absolutely convergent, exponentially tilted form
(the Abel-regularised statement): by Fourier inversion (Mathlib's `Continuous.fourierInv_fourier_eq`),

* `integral_airyAi_mul_exp_complex`: for `Re a > 0`, `∫_ℝ Ai(x) e^{a x} dx = e^{a³/3}`;
  the integrand is integrable (`integrable_airyTilt`: `|e^{cx} Ai(x)| ≤ K e^{-(c/2)|x|}`, from the
  `c`-dependent contour bound);
* `integral_airyAi_mul_exp`: the real case `∫ Ai(x) e^{a x} dx = e^{a³/3}`, `a > 0`;
* `tendsto_integral_airyAi_fourier`: `∫ Ai(x) e^{εx - iωx} dx = e^{(ε-iω)³/3} → e^{iω³/3}` as `ε → 0⁺`.

The conditionally convergent improper integrals `∫_{-∞}^{∞} Ai = 1` and `∫_0^∞ Ai = 1/3` are in `AiryIntegral`.

**Not formalised:** the Fourier transform of `Ai` as an `L²` / tempered-distribution identity.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.Special

/-- The symbol `s ↦ exp((c + i s)³/3)`: the Fourier transform of the tilted function `e^{cx} Ai(x)`. -/
noncomputable def airyFourierSymbol (c s : ℝ) : ℂ := cexp (airyLine c s ^ 3 / 3)

lemma airyFourierSymbol_eq (c s : ℝ) : airyFourierSymbol c s = airyPoly 0 c 0 s := by
  simp [airyFourierSymbol, airyPoly, airyKernel]

lemma integrable_airyFourierSymbol {c : ℝ} (hc : 0 < c) : Integrable (airyFourierSymbol c) := by
  rw [show airyFourierSymbol c = airyPoly 0 c 0 from funext (airyFourierSymbol_eq c)]
  exact integrable_airyPoly hc 0 0

lemma continuous_airyFourierSymbol (c : ℝ) : Continuous (airyFourierSymbol c) := by
  rw [show airyFourierSymbol c = airyPoly 0 c 0 from funext (airyFourierSymbol_eq c)]
  exact continuous_airyPoly 0 c 0

/-- `e^{cx} Ai(x) = (1/2π) ∫ exp((c+is)³/3) e^{-isx} ds`. -/
lemma airyAi_mul_exp_eq {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (airyAi x : ℂ) * cexp (c * x) =
      (1 / (2 * (π : ℂ))) * ∫ s : ℝ, cexp (-((s * x : ℝ) : ℂ) * I) * airyFourierSymbol c s := by
  rw [← airyAiC_ofReal, airyAiC_eq_airyMom hc, airyMom, mul_assoc]
  congr 1
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [airyPoly, airyKernel, airyFourierSymbol, airyLine, pow_zero, one_mul]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The tilted function `ψ_c(x) = e^{cx} Ai(x)`. -/
noncomputable def airyTilt (c x : ℝ) : ℂ := (airyAi x : ℂ) * cexp (c * x)

lemma continuous_airyTilt (c : ℝ) : Continuous (airyTilt c) := by
  unfold airyTilt
  have := differentiable_airyAi.continuous
  fun_prop

/-- Exponential decay of `e^{cx} Ai(x)` in both directions (`c > 0`). -/
lemma norm_airyTilt_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ‖airyTilt c x‖ ≤ ((1 / (2 * π)) * (Real.exp ((2 * c) ^ 3 / 3) * √(π / (2 * c))) +
      (1 / (2 * π)) * (Real.exp ((c / 2) ^ 3 / 3) * √(π / (c / 2)))) * Real.exp (-(c / 2) * |x|) := by
  have hAi : ∀ c' : ℝ, 0 < c' → ‖(airyAi x : ℂ)‖ ≤ (1 / (2 * π)) *
      (Real.exp (c' ^ 3 / 3 - x * c') * √(π / c')) := by
    intro c' hc'
    have := norm_airyMom_zero_le c' x
    have e : airyMom 0 c' (x : ℂ) = (airyAi x : ℂ) := by
      rw [← airyAiC_eq_airyMom hc', airyAiC_ofReal]
    rwa [e] at this
  have hn : ‖airyTilt c x‖ = |airyAi x| * Real.exp (c * x) := by
    unfold airyTilt
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp
  have K1 : 0 ≤ (1 / (2 * π)) * (Real.exp ((2 * c) ^ 3 / 3) * √(π / (2 * c))) := by positivity
  have K2 : 0 ≤ (1 / (2 * π)) * (Real.exp ((c / 2) ^ 3 / 3) * √(π / (c / 2))) := by positivity
  rw [hn]
  rcases le_total 0 x with hx | hx
  · have h1 := hAi (2 * c) (by positivity)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    rw [abs_of_nonneg hx]
    calc |airyAi x| * Real.exp (c * x)
        ≤ ((1 / (2 * π)) * (Real.exp ((2 * c) ^ 3 / 3 - x * (2 * c)) * √(π / (2 * c)))) *
          Real.exp (c * x) := by gcongr
      _ = ((1 / (2 * π)) * (Real.exp ((2 * c) ^ 3 / 3) * √(π / (2 * c)))) * Real.exp (-(c * x)) := by
          have e : Real.exp ((2 * c) ^ 3 / 3 - x * (2 * c)) * Real.exp (c * x) =
              Real.exp ((2 * c) ^ 3 / 3) * Real.exp (-(c * x)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (1 / (2 * π) * √(π / (2 * c))) * e
      _ ≤ _ := by
          have : Real.exp (-(c * x)) ≤ Real.exp (-(c / 2) * x) :=
            Real.exp_le_exp.mpr (by nlinarith)
          nlinarith [Real.exp_pos (-(c * x)), Real.exp_pos (-(c / 2) * x),
            mul_le_mul_of_nonneg_left this K1,
            mul_nonneg K2 (Real.exp_pos (-(c / 2) * x)).le]
  · have h1 := hAi (c / 2) (by positivity)
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    rw [abs_of_nonpos hx]
    calc |airyAi x| * Real.exp (c * x)
        ≤ ((1 / (2 * π)) * (Real.exp ((c / 2) ^ 3 / 3 - x * (c / 2)) * √(π / (c / 2)))) *
          Real.exp (c * x) := by gcongr
      _ = ((1 / (2 * π)) * (Real.exp ((c / 2) ^ 3 / 3) * √(π / (c / 2)))) * Real.exp ((c / 2) * x) := by
          have e : Real.exp ((c / 2) ^ 3 / 3 - x * (c / 2)) * Real.exp (c * x) =
              Real.exp ((c / 2) ^ 3 / 3) * Real.exp ((c / 2) * x) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (1 / (2 * π) * √(π / (c / 2))) * e
      _ ≤ _ := by
          have : Real.exp ((c / 2) * x) = Real.exp (-(c / 2) * -x) := by ring_nf
          rw [this]
          nlinarith [Real.exp_pos (-(c / 2) * -x),
            mul_nonneg K1 (Real.exp_pos (-(c / 2) * -x)).le]

lemma integrable_airyTilt {c : ℝ} (hc : 0 < c) : Integrable (airyTilt c) := by
  set K := ((1 / (2 * π)) * (Real.exp ((2 * c) ^ 3 / 3) * √(π / (2 * c))) +
      (1 / (2 * π)) * (Real.exp ((c / 2) ^ 3 / 3) * √(π / (c / 2)))) with hK
  have hb : Integrable (fun x : ℝ => K * Real.exp (-(c / 2) * |x|)) := by
    have h1 : IntegrableOn (fun x : ℝ => K * Real.exp (-(c / 2) * |x|)) (Iic 0) := by
      have := ((integrableOn_exp_mul_Iic (a := c / 2) (by positivity) 0).const_mul K :
        IntegrableOn (fun x : ℝ => K * Real.exp (c / 2 * x)) (Iic 0) volume)
      refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Iic
      simp only [mem_Iic] at hx
      rw [abs_of_nonpos hx]; ring_nf
    have h2 : IntegrableOn (fun x : ℝ => K * Real.exp (-(c / 2) * |x|)) (Ioi 0) := by
      have := ((exp_neg_integrableOn_Ioi 0 (b := c / 2) (by positivity)).const_mul K :
        IntegrableOn (fun x : ℝ => K * Real.exp (-(c / 2) * x)) (Ioi 0) volume)
      refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioi
      simp only [mem_Ioi] at hx
      rw [abs_of_pos hx]
    have := h1.union h2
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  exact hb.mono' (continuous_airyTilt c).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_airyTilt_le hc x)

/-- `h_c(ξ) = exp((c + 2π i ξ)³/3)`, the symbol in Mathlib's `2π`-normalisation. -/
noncomputable def airyFourierH (c ξ : ℝ) : ℂ := airyFourierSymbol c (2 * π * ξ)

/-- `e^{cx} Ai(x)` is the Fourier transform (Mathlib's `𝓕`) of `h_c`. -/
lemma fourier_airyFourierH {c : ℝ} (hc : 0 < c) (x : ℝ) : 𝓕 (airyFourierH c) x = airyTilt c x := by
  rw [Real.fourier_real_eq_integral_exp_smul, airyTilt, airyAi_mul_exp_eq hc]
  simp only [smul_eq_mul]
  have h := Measure.integral_comp_mul_left
    (fun s : ℝ => cexp (-((s * x : ℝ) : ℂ) * I) * airyFourierSymbol c s) (2 * π)
  have e : ∀ ξ : ℝ, cexp (↑(-2 * π * ξ * x) * I) * airyFourierH c ξ =
      (fun s : ℝ => cexp (-((s * x : ℝ) : ℂ) * I) * airyFourierSymbol c s) (2 * π * ξ) := by
    intro ξ
    simp only [airyFourierH]
    congr 2
    push_cast; ring_nf
  simp_rw [e]
  rw [h, Complex.real_smul]
  have : |(2 * π)⁻¹| = (2 * π)⁻¹ := abs_of_pos (by positivity)
  rw [this]
  push_cast
  ring

/-- **Two-sided Laplace transform of `Ai`**: for `Re a > 0`,
`∫_ℝ Ai(x) e^{a x} dx = e^{a³/3}` (absolutely convergent).  For `a = ε - iω` this is the
Abel-regularised form of the Fourier transform `∫ Ai(x) e^{-iωx} dx = e^{iω³/3}`. -/
theorem integral_airyAi_mul_exp_complex {a : ℂ} (ha : 0 < a.re) :
    ∫ x : ℝ, (airyAi x : ℂ) * cexp (a * x) = cexp (a ^ 3 / 3) := by
  set c := a.re with hc
  set s := a.im with hs
  have hh_cont : Continuous (airyFourierH c) := by
    unfold airyFourierH
    exact (continuous_airyFourierSymbol c).comp (by fun_prop)
  have hh_int : Integrable (airyFourierH c) := by
    unfold airyFourierH
    exact (integrable_airyFourierSymbol ha).comp_mul_left' (by positivity)
  have hF : 𝓕 (airyFourierH c) = airyTilt c := funext (fourier_airyFourierH ha)
  have hinv := hh_cont.fourierInv_fourier_eq hh_int (by rw [hF]; exact integrable_airyTilt ha)
  have h1 := congrFun hinv (s / (2 * π))
  rw [hF, Real.fourierInv_eq'] at h1
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have e1 : airyFourierH c (s / (2 * π)) = cexp (a ^ 3 / 3) := by
    unfold airyFourierH airyFourierSymbol airyLine
    have : (2 * π * (s / (2 * π)) : ℝ) = s := by field_simp
    rw [this]
    congr 3
    exact (Complex.ext (by simp [hc]) (by simp [hs])).symm
  rw [e1] at h1
  rw [← h1]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [airyTilt, smul_eq_mul]
  have hin : inner ℝ x (s / (2 * π)) = x * (s / (2 * π)) := by
    simp [mul_comm]
  have : cexp (a * x) = cexp (↑(2 * π * inner ℝ x (s / (2 * π))) * I) * cexp (c * x) := by
    rw [← Complex.exp_add, hin]
    congr 1
    have : (a : ℂ) = (c : ℂ) + (s : ℂ) * I := (Complex.re_add_im a).symm
    rw [this]
    push_cast
    field_simp
    ring
  rw [this]
  ring

/-- `e^{ax} Ai(x)` is integrable for real `a > 0`. -/
theorem integrable_airyAi_mul_exp {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => airyAi x * Real.exp (a * x)) := by
  refine (integrable_airyTilt ha).re.congr (Eventually.of_forall fun x => ?_)
  have : airyTilt a x = ((airyAi x * Real.exp (a * x) : ℝ) : ℂ) := by
    unfold airyTilt; push_cast; rfl
  show (airyTilt a x).re = _
  rw [this]
  exact Complex.ofReal_re _

/-- **`∫_ℝ Ai(x) e^{a x} dx = e^{a³/3}` for real `a > 0`.** -/
theorem integral_airyAi_mul_exp {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, airyAi x * Real.exp (a * x) = Real.exp (a ^ 3 / 3) := by
  have h := integral_airyAi_mul_exp_complex (a := (a : ℂ)) (by simpa using ha)
  have e1 : ∀ x : ℝ, (airyAi x : ℂ) * cexp ((a : ℂ) * x) = ((airyAi x * Real.exp (a * x) : ℝ) : ℂ) := by
    intro x; push_cast; rfl
  simp_rw [e1] at h
  rw [integral_complex_ofReal] at h
  have e2 : cexp ((a : ℂ) ^ 3 / 3) = ((Real.exp (a ^ 3 / 3) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  rw [e2] at h
  exact_mod_cast h

/-- **Abel-regularised Fourier transform of `Ai`**: `∫_ℝ Ai(x) e^{-iωx} dx = e^{iω³/3}` in the sense
`lim_{ε → 0⁺} ∫ Ai(x) e^{εx - iωx} dx`. -/
theorem tendsto_integral_airyAi_fourier (ω : ℝ) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, (airyAi x : ℂ) * cexp (((ε : ℂ) - ω * I) * x)) (𝓝[>] 0)
      (𝓝 (cexp ((ω : ℂ) ^ 3 * I / 3))) := by
  have hcongr : ∀ᶠ ε : ℝ in 𝓝[>] 0, (∫ x : ℝ, (airyAi x : ℂ) * cexp (((ε : ℂ) - ω * I) * x)) =
      cexp (((ε : ℂ) - ω * I) ^ 3 / 3) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_airyAi_mul_exp_complex (a := (ε : ℂ) - ω * I) (by simpa using hε)
  refine Tendsto.congr' (EventuallyEq.symm hcongr) ?_
  have hc : Continuous fun ε : ℝ => cexp (((ε : ℂ) - ω * I) ^ 3 / 3) := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hI : (I : ℂ) ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  have e : cexp ((((0 : ℝ) : ℂ) - ω * I) ^ 3 / 3) = cexp ((ω : ℂ) ^ 3 * I / 3) := by
    congr 1
    simp only [Complex.ofReal_zero, zero_sub]
    linear_combination (-(ω : ℂ) ^ 3 / 3) * hI
  rw [e] at this
  exact this

/-- The Abelian limit `∫_ℝ Ai(x) e^{εx} dx → 1` (`ε → 0⁺`), the regularised `∫_ℝ Ai = 1`. -/
theorem tendsto_integral_airyAi_mul_exp :
    Tendsto (fun ε : ℝ => ∫ x : ℝ, airyAi x * Real.exp (ε * x)) (𝓝[>] 0) (𝓝 1) := by
  have hcongr : ∀ᶠ ε : ℝ in 𝓝[>] 0, Real.exp (ε ^ 3 / 3) = ∫ x : ℝ, airyAi x * Real.exp (ε * x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integral_airyAi_mul_exp hε).symm
  refine Tendsto.congr' hcongr ?_
  have hc : Continuous fun ε : ℝ => Real.exp (ε ^ 3 / 3) := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa using this

/-- info: 'FormalResearch.Special.integral_airyAi_mul_exp_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyAi_mul_exp_complex

/-- info: 'FormalResearch.Special.integral_airyAi_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyAi_mul_exp

/-- info: 'FormalResearch.Special.tendsto_integral_airyAi_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_integral_airyAi_fourier

end FormalResearch.Special
