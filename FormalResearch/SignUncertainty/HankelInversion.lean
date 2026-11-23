module

public import FormalResearch.SignUncertainty.EuclidRadialProjection

/-!
# Hankel inversion and the `±1` projections (`d = n + 1 ≥ 2`)

For `G` continuous on `[0,∞)` with `G ρ₀` and `(𝓗_c G) ρ₀` integrable and `𝓗_c G` continuous on `[0,∞)`,
`c = (n+1)/2`: `𝓗_c (𝓗_c G) = G` on `[0,∞)` (`besselHankel_involutive`), from the radial Fourier transform
(`fourier_radial_hankel`) and Fourier inversion on `ℝ^{n+1}`. Consequently `p = (G + 𝓗_c G)/2` is in `𝒜_c^{+1}`
and `q = (𝓗_c G - G)/2` is in `𝒜_c^{-1}` (`isHankelEigenfn_plus`, `isHankelEigenfn_minus`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

/-- The Hankel transform is real-linear on integrable profiles. -/
lemma besselHankelTransform_add {c : ℝ} (hc : 1 / 2 < c) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun s => f s * hankelRho0 c s) (Ioi 0))
    (hg : IntegrableOn (fun s => g s * hankelRho0 c s) (Ioi 0)) (Δ : ℝ) :
    besselHankelTransform c (fun s => f s + g s) Δ =
      besselHankelTransform c f Δ + besselHankelTransform c g Δ := by
  unfold besselHankelTransform
  rw [← integral_add (integrableOn_mul_hankelKernel hc hf Δ) (integrableOn_mul_hankelKernel hc hg Δ)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only
  ring

lemma besselHankelTransform_smul (c a : ℝ) (f : ℝ → ℝ) (Δ : ℝ) :
    besselHankelTransform c (fun s => a * f s) Δ = a * besselHankelTransform c f Δ := by
  unfold besselHankelTransform
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only
  ring

/-- **Hankel inversion** (`d = n + 1 ≥ 2`). -/
theorem besselHankel_involutive (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hGi : IntegrableOn (fun s => G s * hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0))
    (hĜ : ContinuousOn (besselHankelTransform (((n : ℝ) + 1) / 2) G) (Ici 0))
    (hĜi : IntegrableOn (fun s => besselHankelTransform (((n : ℝ) + 1) / 2) G s *
      hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0)) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    besselHankelTransform (((n : ℝ) + 1) / 2) (besselHankelTransform (((n : ℝ) + 1) / 2) G) Δ = G Δ := by
  set c : ℝ := ((n : ℝ) + 1) / 2 with hc
  set Ĝ : ℝ → ℝ := besselHankelTransform c G with hĜdef
  set g : EuclSp (n + 1) → ℂ := fun x => (G (‖x‖ ^ 2 / 2) : ℂ) with hg
  set ĝ : EuclSp (n + 1) → ℂ := fun x => (Ĝ (‖x‖ ^ 2 / 2) : ℂ) with hĝ
  have hgi : Integrable g := (integrable_radialLift_iff n hn G).2 hGi
  have hĝi : Integrable ĝ := (integrable_radialLift_iff n hn Ĝ).2 hĜi
  have hgc : Continuous g :=
    Complex.continuous_ofReal.comp (hG.comp_continuous ((continuous_norm.pow 2).div_const 2)
      fun v => mem_Ici.mpr (by positivity))
  have hF : 𝓕 g = ĝ := funext fun y => fourier_radial_hankel n hn hG hgi y
  have hinv := hgc.fourierInv_fourier_eq hgi (by rw [hF]; exact hĝi)
  rw [hF] at hinv
  set y : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) √(2 * Δ) with hy
  have hy2 : ‖y‖ ^ 2 / 2 = Δ := by
    rw [hy, PiLp.norm_single, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]; ring
  have h1 := congrFun hinv y
  rw [Real.fourierInv_eq_fourier_neg] at h1
  have h2 := fourier_radial_hankel n hn hĜ hĝi (-y)
  rw [norm_neg, hy2] at h2
  rw [h2] at h1
  simp only [hg, hy2] at h1
  exact Complex.ofReal_injective h1

/-- `p = (G + 𝓗_c G)/2 ∈ 𝒜_c^{+1}`. -/
theorem isHankelEigenfn_plus (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hGi : IntegrableOn (fun s => G s * hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0))
    (hĜ : ContinuousOn (besselHankelTransform (((n : ℝ) + 1) / 2) G) (Ici 0))
    (hĜi : IntegrableOn (fun s => besselHankelTransform (((n : ℝ) + 1) / 2) G s *
      hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0)) :
    IsHankelEigenfn (((n : ℝ) + 1) / 2) 1
      (fun s => (1 / 2 : ℝ) * (G s + besselHankelTransform (((n : ℝ) + 1) / 2) G s)) := by
  have hc : 1 / 2 < ((n : ℝ) + 1) / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨continuousOn_const.mul (hG.add hĜ), ?_, fun Δ hΔ => ?_⟩
  · have := (hGi.add hĜi).const_mul (1 / 2 : ℝ)
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    ring
  · rw [besselHankelTransform_smul, besselHankelTransform_add hc hGi hĜi,
      besselHankel_involutive n hn hG hGi hĜ hĜi hΔ]
    ring

/-- `q = (𝓗_c G - G)/2 ∈ 𝒜_c^{-1}`. -/
theorem isHankelEigenfn_minus (n : ℕ) (hn : 1 ≤ n) {G : ℝ → ℝ} (hG : ContinuousOn G (Ici 0))
    (hGi : IntegrableOn (fun s => G s * hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0))
    (hĜ : ContinuousOn (besselHankelTransform (((n : ℝ) + 1) / 2) G) (Ici 0))
    (hĜi : IntegrableOn (fun s => besselHankelTransform (((n : ℝ) + 1) / 2) G s *
      hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0)) :
    IsHankelEigenfn (((n : ℝ) + 1) / 2) (-1)
      (fun s => (1 / 2 : ℝ) * (besselHankelTransform (((n : ℝ) + 1) / 2) G s - G s)) := by
  have hc : 1 / 2 < ((n : ℝ) + 1) / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨continuousOn_const.mul (hĜ.sub hG), ?_, fun Δ hΔ => ?_⟩
  · have := (hĜi.sub hGi).const_mul (1 / 2 : ℝ)
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  · have e : (fun s => (1 / 2 : ℝ) * (besselHankelTransform (((n : ℝ) + 1) / 2) G s - G s)) =
        fun s => (1 / 2 : ℝ) * (besselHankelTransform (((n : ℝ) + 1) / 2) G s + (-1 : ℝ) * G s) := by
      funext s; ring
    have hneg : IntegrableOn (fun s => ((-1 : ℝ) * G s) * hankelRho0 (((n : ℝ) + 1) / 2) s) (Ioi 0) := by
      have := hGi.const_mul (-1 : ℝ)
      refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
      ring
    have hadd := besselHankelTransform_add hc hĜi hneg Δ
    rw [e, besselHankelTransform_smul, hadd, besselHankelTransform_smul,
      besselHankel_involutive n hn hG hGi hĜ hĜi hΔ]
    ring

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.besselHankel_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselHankel_involutive

/-- info: 'FormalResearch.SignUncertainty.isHankelEigenfn_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isHankelEigenfn_plus

/-- info: 'FormalResearch.SignUncertainty.isHankelEigenfn_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isHankelEigenfn_minus

end FormalResearch.SignUncertainty
