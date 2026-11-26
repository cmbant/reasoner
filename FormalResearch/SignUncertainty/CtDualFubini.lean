module

public import FormalResearch.SignUncertainty.CtDualId
public import FormalResearch.SignUncertainty.CtSdReal

/-!
# `ct:dual-id` (2): the regularised Fubini identity

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (2), proof (Cauchy theorem for `G_ε M_δ W̃_c`
and Fubini, using `ct:Wc-rep`).  **Proved.**  For `δ > 0`, `c ≥ 2` and `f ∈ 𝒜_c^ε`:
`Re ∫_0^∞ g₀(ξ) J_δ(ξ) dξ = 0`, where `J_δ(ξ) = ∫_0^∞ A_ε(τ) e^{-δ τ(τ+i)} e^{-icΦ_Ph(τ;ξ)} dτ` and `g₀ = c (fρ₀)(cξ)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtDual

open CtOuter FormalResearch.Asymptotics FormalResearch.CohnElkies CtOsc

/-- The oscillatory kernel `e^{-icΦ_Ph(τ; ξ)}`, `Φ_Ph(τ;ξ) = τ log(π²ξ) - ∫_0^τ m`. -/
noncomputable def dualP (c ξ τ : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ)))

lemma dualP_eq (c ξ τ : ℝ) :
    dualP c ξ τ = Complex.exp (Complex.I * (c : ℂ) * (CtSd.phaseL (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ)) := by
  unfold dualP CtSd.phaseL
  rw [CtCfu.edgePhi_eq]
  congr 1
  push_cast
  ring

lemma norm_dualP (c ξ τ : ℝ) : ‖dualP c ξ τ‖ = 1 := by
  unfold dualP
  rw [show -(Complex.I * (c : ℂ) * (edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ)) =
    ((-(c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Edge representation of the regularised product, as a double-integral integrand. -/
theorem Fd_edge {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) (δ : ℝ)
    {y : ℝ} (hy : 0 < y) :
    Fd c ε f δ ((y : ℂ) * Complex.I) =
      ∫ ξ in Ioi (0 : ℝ), outerAmp ε c y * CtOsc.gcut δ y * (dualP c ξ y * ((hankelDmDens c f ξ : ℝ) : ℂ)) := by
  have hm : (y : ℂ) * Complex.I = Complex.I * (y : ℂ) := mul_comm _ _
  unfold Fd
  rw [gcutC_I_mul, ct_Wc_rep (by linarith) hf y, integral_const_mul]
  unfold dualP
  simp only [hm]
  have hG := phase_identity hε hy
  have key : outerAmp ε c y = outerGbar ε (Complex.I * (y : ℂ)) * (1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) *
      Complex.exp (-(binetDiff c (Complex.I * (y : ℂ)))) := by
    rw [outerAmp_eq hy, hG]
    ring
  rw [key]
  ring

lemma continuousOn_M : ContinuousOn (fun τ : ℝ => ∫ u in (0 : ℝ)..τ, hankelEdgeM u) (Ioi 0) := by
  have h : ContinuousOn (CtSd.phaseL 0) (Ioi 0) := fun τ hτ =>
    (CtSd.phaseL_deriv 0 hτ).continuousAt.continuousWithinAt
  refine h.congr (fun τ _ => ?_)
  simp [CtSd.phaseL]

lemma continuousOn_dualP (c : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => dualP c z.2 z.1) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
  have hlog : ContinuousOn (fun z : ℝ × ℝ => Real.log (Real.pi ^ 2 * z.2)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    refine Real.continuousOn_log.comp (by fun_prop : ContinuousOn (fun z : ℝ × ℝ => Real.pi ^ 2 * z.2) _) ?_
    intro z hz
    exact (mul_pos (by positivity) hz.2).ne'
  have hM' : ContinuousOn (fun z : ℝ × ℝ => ∫ u in (0 : ℝ)..z.1, hankelEdgeM u) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    continuousOn_M.comp continuousOn_fst (fun z (hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) => hz.1)
  have h1 : ContinuousOn (fun z : ℝ × ℝ => (∫ u in (0 : ℝ)..z.1, hankelEdgeM u) - Real.log (Real.pi ^ 2 * z.2) * z.1)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    hM'.sub (hlog.mul continuousOn_fst)
  have h2 := Complex.continuous_exp.comp_continuousOn
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1) :
      ContinuousOn (fun z : ℝ × ℝ => Complex.I * (c : ℂ) * (((∫ u in (0 : ℝ)..z.1, hankelEdgeM u) -
        Real.log (Real.pi ^ 2 * z.2) * z.1 : ℝ) : ℂ)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
  refine h2.congr (fun z hz => ?_)
  simp only [Function.comp]
  rw [dualP_eq]
  rfl

/-- Amplitude data: continuity on `(0,∞)` and a uniform bound. -/
lemma outer_amp_data {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ {c : ℝ}, 2 ≤ c → ContinuousOn (outerAmp ε c) (Ioi 0) ∧
      ∀ τ : ℝ, 0 < τ → ‖outerAmp ε c τ‖ ≤ CA := by
  obtain ⟨CA, hCA, H⟩ := outerAmp_ampBd (ε := ε) (by rcases hε with h | h <;> simp [h])
  refine ⟨CA, hCA, fun {c} hc => ?_⟩
  obtain ⟨A1, A2, hA⟩ := H c hc
  refine ⟨fun τ hτ => (hA.d1 τ hτ).continuousAt.continuousWithinAt, fun τ hτ => ?_⟩
  refine (hA.b0 τ hτ).trans ?_
  obtain ⟨r1, -, -, -, -⟩ := rp_all hτ
  rw [r1, div_le_iff₀ (by linarith)]
  have : Real.sqrt τ ≤ 1 + τ := by nlinarith [Real.sq_sqrt hτ.le, sq_nonneg (Real.sqrt τ - 1), Real.sqrt_nonneg τ]
  nlinarith [mul_le_mul_of_nonneg_left this hCA]

/-- The regularised inner integral `J_δ(ξ) = ∫_0^∞ A_ε(τ) e^{-δ τ(τ+i)} e^{-icΦ_Ph(τ;ξ)} dτ`. -/
noncomputable def Jd (c ε δ ξ : ℝ) : ℂ :=
  ∫ τ in Ioi (0 : ℝ), outerAmp ε c τ * CtOsc.gcut δ τ * dualP c ξ τ

lemma continuous_gcut (δ : ℝ) : Continuous (CtOsc.gcut δ) :=
  continuous_iff_continuousAt.2 fun τ => (CtOsc.hasDerivAt_gcut δ τ).continuousAt

lemma integrable_gauss_Ioi (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun τ : ℝ => K * Real.exp (-(δ * τ ^ 2))) (volume.restrict (Ioi (0 : ℝ))) := by
  have := (integrable_exp_neg_mul_sq hδ).const_mul K
  simpa [neg_mul] using this.restrict

/-- **The regularised Fubini identity**: `Re ∫_0^∞ g₀(ξ) J_δ(ξ) dξ = 0` for `δ > 0`, and the integrand is integrable. -/
theorem dual_fubini {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun ξ => ((hankelDmDens c f ξ : ℝ) : ℂ) * Jd c ε δ ξ) (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ ξ in Ioi (0 : ℝ), ((hankelDmDens c f ξ : ℝ) : ℂ) * Jd c ε δ ξ).re = 0 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨CA, hCA0, hCA⟩ := outer_amp_data hε
  obtain ⟨hcont, hbd⟩ := hCA hc
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F2 : ℝ × ℝ → ℂ := fun z => outerAmp ε c z.1 * CtOsc.gcut δ z.1 *
    (dualP c z.2 z.1 * ((hankelDmDens c f z.2 : ℝ) : ℂ)) with hF2
  have hprod : μ.prod μ = (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    rw [hμ, Measure.volume_eq_prod, Measure.prod_restrict]
  have hcontF2 : ContinuousOn F2 (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    have h1 : ContinuousOn (fun z : ℝ × ℝ => outerAmp ε c z.1) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      hcont.comp continuousOn_fst (fun z (hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) => hz.1)
    have h2 : ContinuousOn (fun z : ℝ × ℝ => CtOsc.gcut δ z.1) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      ((continuous_gcut δ).comp continuous_fst).continuousOn
    have h3 : ContinuousOn (fun z : ℝ × ℝ => ((hankelDmDens c f z.2 : ℝ) : ℂ)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((hankelDmDens_continuousOn hc0 hf).comp continuousOn_snd
          (fun z (hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) => hz.2))
    exact (h1.mul h2).mul ((continuousOn_dualP c).mul h3)
  have hmeas : AEStronglyMeasurable F2 (μ.prod μ) := by
    rw [hprod]
    exact hcontF2.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  have hmaj : Integrable (fun z : ℝ × ℝ => (CA * Real.exp (-(δ * z.1 ^ 2))) * ‖((hankelDmDens c f z.2 : ℝ) : ℂ)‖)
      (μ.prod μ) := by
    refine Integrable.mul_prod (f := fun τ : ℝ => CA * Real.exp (-(δ * τ ^ 2)))
      (g := fun ξ : ℝ => ‖((hankelDmDens c f ξ : ℝ) : ℂ)‖) (integrable_gauss_Ioi CA hδ) ?_
    have := (hankelDmDens_integrableOn hc0 hf).norm
    simpa [hμ] using this
  have hint2 : Integrable F2 (μ.prod μ) := by
    refine Integrable.mono' hmaj hmeas ?_
    rw [hprod, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    refine Eventually.of_forall fun z hz => ?_
    have hz1 : 0 < z.1 := hz.1
    simp only [hF2, norm_mul, norm_dualP, one_mul, CtOsc.norm_gcut]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbd z.1 hz1) (Real.exp_pos _).le) (norm_nonneg _)
  -- identification of the inner integral
  have hA : ∫ τ in Ioi (0 : ℝ), Fd c ε f δ ((τ : ℂ) * Complex.I) = ∫ τ in Ioi (0 : ℝ), ∫ ξ in Ioi (0 : ℝ), F2 (τ, ξ) :=
    setIntegral_congr_fun measurableSet_Ioi fun τ hτ => Fd_edge hc hf hε δ hτ
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun τ ξ => F2 (τ, ξ)) hint2
  have hinner : ∀ ξ : ℝ, ∫ τ, F2 (τ, ξ) ∂μ = ((hankelDmDens c f ξ : ℝ) : ℂ) * Jd c ε δ ξ := by
    intro ξ
    have : ∀ τ : ℝ, F2 (τ, ξ) = (outerAmp ε c τ * CtOsc.gcut δ τ * dualP c ξ τ) * ((hankelDmDens c f ξ : ℝ) : ℂ) :=
      fun τ => by simp only [hF2]; ring
    simp_rw [this]
    rw [integral_mul_const, mul_comm]
    rfl
  refine ⟨?_, ?_⟩
  · have := hint2.integral_prod_right
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    exact hinner ξ
  · have h0 := Fd_re_zero (by linarith : (3 / 2 : ℝ) < c) hf hε hδ
    rw [hA, hswap] at h0
    have e : (fun ξ => ∫ τ, F2 (τ, ξ) ∂μ) = fun ξ => ((hankelDmDens c f ξ : ℝ) : ℂ) * Jd c ε δ ξ := funext hinner
    rw [e] at h0
    exact h0

/-- info: 'FormalResearch.SignUncertainty.CtDual.dual_fubini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dual_fubini

end FormalResearch.SignUncertainty.CtDual
