module

public import FormalResearch.SignUncertainty.HankelMellinKernel

/-!
# Integrability of the Mellin integrand of a Hankel transform

`mellin_hankel_fubini` (`HankelMellinKernel`) gives the value of `∫ Δ^{z-1} (𝓗_c g)(Δ) dΔ`; its proof contains the integrability of the
integrand (Tonelli on the double integral), stated here as `integrableOn_mellin_hankel`.  Used by the Hankel eigen-identity of the
Mellin lifts (`MellinLiftEigen`, `O.11ak`).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- The Mellin integrand `Δ^{z-1} (𝓗_c g)(Δ)` is integrable on `(0, ∞)` for `0 < Re z < c/2 - 1/4`. -/
theorem integrableOn_mellin_hankel {c : ℝ} (hc : 3 / 2 < c) {z : ℂ} (hz0 : 0 < z.re)
    (hz1 : z.re < c / 2 - 1 / 4) {g : ℝ → ℝ} (hgc : ContinuousOn g (Ioi 0))
    (hg : IntegrableOn (fun s : ℝ => |g s| * s ^ (c - 1 - z.re)) (Ioi 0)) :
    IntegrableOn (fun Δ : ℝ => (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c g Δ : ℂ)) (Ioi 0) := by
  have hc0 : 0 < c := by linarith
  set x := z.re with hx
  set a : ℝ := (2 * π) ^ c / Real.Gamma c with ha
  have hρ : ∀ s : ℝ, hankelRho0 c s = a * s ^ (c - 1) := fun s => rfl
  have hA := integrableOn_abs_phi_mellin hc hz0 hz1
  set A : ℝ := ∫ w in Ioi (0 : ℝ), |hankelPhi c w| * w ^ (x - 1) with hAdef
  let Fd : ℝ → ℝ → ℂ := fun Δ s =>
    (Δ : ℂ) ^ (z - 1) * ((g s * hankelRho0 c s * hankelPhi c (Δ * s) : ℝ) : ℂ)
  -- inner integrability and norm integral
  have hinner : ∀ s ∈ Ioi (0 : ℝ), IntegrableOn (fun Δ => Fd Δ s) (Ioi 0) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hI := integrableOn_phi_mellin hc hz0 hz1
    have hI' : IntegrableOn (fun Δ : ℝ => (hankelPhi c (s * Δ) : ℂ) * ((s * Δ : ℝ) : ℂ) ^ (z - 1))
        (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff (fun w : ℝ => (hankelPhi c w : ℂ) * (w : ℂ) ^ (z - 1))
        0 hs0, mul_zero]
      exact hI
    have hI'' : IntegrableOn (fun Δ : ℝ => (((g s * hankelRho0 c s : ℝ)) : ℂ) *
        (((s : ℂ) ^ (z - 1))⁻¹ * ((hankelPhi c (s * Δ) : ℂ) * ((s * Δ : ℝ) : ℂ) ^ (z - 1))))
        (Ioi 0) := (hI'.const_mul (((s : ℂ) ^ (z - 1))⁻¹)).const_mul (((g s * hankelRho0 c s : ℝ)) : ℂ)
    refine hI''.congr_fun (fun Δ hΔ => ?_) measurableSet_Ioi
    have hΔ0 : 0 < Δ := hΔ
    simp only [Fd]
    have hmulc : ((s * Δ : ℝ) : ℂ) ^ (z - 1) = (s : ℂ) ^ (z - 1) * (Δ : ℂ) ^ (z - 1) := by
      rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hs0.le hΔ0.le _
    rw [hmulc, mul_comm Δ s]
    have : (s : ℂ) ^ (z - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hs0.ne']
    push_cast
    field_simp
  have hnorm : ∀ s ∈ Ioi (0 : ℝ), ∫ Δ in Ioi (0 : ℝ), ‖Fd Δ s‖ =
      |g s| * hankelRho0 c s * (s ^ (-x) * A) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hρ0 : 0 ≤ hankelRho0 c s := hankelRho0_nonneg hc0 hs0.le
    have hpt : ∀ Δ ∈ Ioi (0 : ℝ), ‖Fd Δ s‖ =
        |g s| * hankelRho0 c s * (|hankelPhi c (Δ * s)| * Δ ^ (x - 1)) := by
      intro Δ hΔ
      have hΔ0 : 0 < Δ := hΔ
      simp only [Fd]
      rw [norm_mul, norm_cpow_sub_one hΔ0, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hρ0]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_scale_real (fun w => |hankelPhi c w|) hs0 x]
  have hmeas : AEStronglyMeasurable (Function.uncurry Fd)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (z - 1)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      ContinuousOn.cpow_const (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        fun p hp => Or.inl (by simpa using (mem_Ioi.mp hp.1))
    have h2 : ContinuousOn (fun p : ℝ × ℝ => g p.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      hgc.comp continuous_snd.continuousOn fun p hp => hp.2
    have h3 : ContinuousOn (fun p : ℝ × ℝ => hankelRho0 c p.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      (continuousOn_hankelRho0 c).comp continuous_snd.continuousOn fun p hp => hp.2
    have h4 : Continuous fun p : ℝ × ℝ => hankelPhi c (p.1 * p.2) :=
      (hankelPhi_continuous c).comp (continuous_fst.mul continuous_snd)
    exact h1.mul (Complex.continuous_ofReal.comp_continuousOn ((h2.mul h3).mul h4.continuousOn))
  have hF : Integrable (Function.uncurry Fd)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hinner s hs
    · have hdom : IntegrableOn (fun s : ℝ => (A * a) * (|g s| * s ^ (c - 1 - x))) (Ioi 0) :=
        hg.const_mul _
      refine hdom.congr_fun (fun s hs => ?_) measurableSet_Ioi
      have hs0 : 0 < s := hs
      simp only [Function.uncurry_apply_pair]
      rw [hnorm s hs, hρ, show c - 1 - x = (c - 1) + -x by ring, Real.rpow_add hs0]
      ring
  have hL : ∀ Δ : ℝ, ∫ s in Ioi (0 : ℝ), Fd Δ s =
      (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c g Δ : ℂ) := by
    intro Δ
    simp only [Fd]
    rw [integral_const_mul]
    unfold besselHankelTransform hankelKernel
    rw [integral_complex_ofReal]
  have h1 := hF.integral_prod_left
  simp only [Function.uncurry_apply_pair] at h1
  refine h1.congr (Eventually.of_forall fun Δ => ?_)
  exact hL Δ

/-- info: 'FormalResearch.SignUncertainty.integrableOn_mellin_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.integrableOn_mellin_hankel

end FormalResearch.SignUncertainty
