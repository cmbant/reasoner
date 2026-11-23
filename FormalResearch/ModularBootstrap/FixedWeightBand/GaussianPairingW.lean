module

public import FormalResearch.ModularBootstrap.Crossing.Setup

/-!
# Gaussian Pairing on `ℝ^{2w}` and the Laplace Reflection `Φ(1/λ) = -λ^w Φ(λ)` (`vlo:S1`, `vlo:R3`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S1 (`vlo:S1`), proof of the
reflection ("Reflection by Gaussian pairing"), with the Gaussian Hankel transform `vlo:R3`.

For `w ≥ 1` and `g : ℝ → ℝ` whose radial lift `x ↦ g(‖x‖²/2)` on `EuclideanSpace ℝ (Fin (2 w))` is
integrable and Fourier-odd (`𝓕 (radialLift w g) = -radialLift w g`, the `fourier_odd` field of
`TestClass`), put `Φ(λ) = ∫₀^∞ g(t) t^{w-1} e^{-2π λ t} dt`.

* `fourier_radial_exp_W`: public copy of the Gaussian Fourier transform on `ℝ^{2w}`,
  `𝓕 (e^{-2π β ‖x‖²/2}) = β^{-w} e^{-2π ‖x‖²/(2β)}` (the private `fourier_radial_exp` of `Crossing.Setup`);
* `laplacePairW_inv`: `Φ(1/λ) = -λ^w Φ(λ)` for `λ > 0` (paper's `vlo:eGaussRefl`, written as
  `Φ(λ) = -λ^{-w} Φ(1/λ)` there).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing

/-- Gaussian Fourier transform on `ℝ^{2w}` (`vlo:R3`): the radial lift of `e^{-2π β t}` is
integrable and `𝓕 (radialLift w e^{-2π β ·}) = β^{-w} • radialLift w e^{-2π · / β}`.
Public copy of the private `Crossing.fourier_radial_exp`. -/
lemma fourier_radial_exp_W (w : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (radialLift w (fun t => Real.exp (-2 * π * β * t))) ∧
      𝓕 (radialLift w (fun t => Real.exp (-2 * π * β * t))) =
        ((β ^ (-(w : ℝ)) : ℝ) : ℂ) • radialLift w (fun t => Real.exp (-2 * π * t / β)) := by
  have hb : 0 < ((π * β : ℝ) : ℂ).re := by simp [Real.pi_pos, hβ]
  have hlift : radialLift w (fun t => Real.exp (-2 * π * β * t)) =
      fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
        Complex.exp (-((π * β : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    ext x
    simp only [radialLift]
    rw [Complex.ofReal_exp]
    congr 1; push_cast; ring
  have hint : Integrable (radialLift w (fun t => Real.exp (-2 * π * β * t))) := by
    rw [hlift]
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0
      (0 : EuclideanSpace ℝ (Fin (2 * w)))
  refine ⟨hint, ?_⟩
  ext ξ
  rw [hlift, fourier_gaussian_innerProductSpace hb ξ]
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) / 2 : ℂ) = (w : ℂ) := by
    rw [finrank_euclideanSpace_fin]
    push_cast; ring
  rw [hdim]
  have hpi : ((π : ℝ) : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hbc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
    push_cast; field_simp
  rw [hpi, show (w : ℂ) = ((w : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (by positivity : 0 ≤ β⁻¹), Real.inv_rpow hβ.le,
    ← Real.rpow_neg hβ.le]
  simp only [Pi.smul_apply, smul_eq_mul, radialLift]
  rw [Complex.ofReal_exp]
  congr 2; push_cast
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hb_ne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  field_simp

/-- The Laplace pairing `Φ(λ) = ∫₀^∞ g(t) t^{w-1} e^{-2π λ t} dt` (`vlo:S1` proof). -/
noncomputable def laplacePairW (w : ℕ) (g : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), g t * t ^ (w - 1) * Real.exp (-2 * π * lam * t)

/-- Radial constant `(2π)^w / (w-1)!` of `integral_radialLiftReal`. -/
noncomputable def radialConstW (w : ℕ) : ℝ := (2 * π) ^ w / ((w - 1).factorial : ℝ)

lemma radialConstW_pos (w : ℕ) : 0 < radialConstW w := by
  unfold radialConstW; positivity

/-- Radial integral of the pairing of `g` with a Gaussian:
`∫_{ℝ^{2w}} g(‖x‖²/2) e^{-2π β ‖x‖²/2} dx = c_w Φ(β)`. -/
lemma integral_radial_pair_W {w : ℕ} (hw : 1 ≤ w) {g : ℝ → ℝ}
    (hint : Integrable (radialLift w g)) {β : ℝ} (hβ : 0 < β) :
    ∫ x : EuclideanSpace ℝ (Fin (2 * w)),
        radialLift w g x * radialLift w (fun t => Real.exp (-2 * π * β * t)) x =
      ((radialConstW w * laplacePairW w g β : ℝ) : ℂ) := by
  have hreal : Integrable (radialLiftReal w g) := (integrable_radialLift_iff_real w g).1 hint
  have hbd : Integrable (fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
      g (‖x‖ ^ 2 / 2) * Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2))) := by
    refine hreal.norm.mono' ?_ ?_
    · have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
          Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2))) := by fun_prop
      exact hreal.aestronglyMeasurable.mul hcont.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp_le : Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have harg_nn : 0 ≤ 2 * π * β * (‖x‖ ^ 2 / 2) := by positivity
        linarith
      calc |g (‖x‖ ^ 2 / 2)| * Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2))
          ≤ |g (‖x‖ ^ 2 / 2)| * 1 := by gcongr
        _ = ‖radialLiftReal w g x‖ := by simp [radialLiftReal]
  have hfn : (fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
      radialLift w g x * radialLift w (fun t => Real.exp (-2 * π * β * t)) x) =
      fun x => ((g (‖x‖ ^ 2 / 2) * Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2)) : ℝ) : ℂ) := by
    ext x
    simp only [radialLift, Complex.ofReal_mul]
  have hcomm := Complex.ofRealCLM.integral_comp_comm hbd
  change (∫ x : EuclideanSpace ℝ (Fin (2 * w)),
      ((g (‖x‖ ^ 2 / 2) * Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2)) : ℝ) : ℂ)) =
    ((∫ x : EuclideanSpace ℝ (Fin (2 * w)),
      g (‖x‖ ^ 2 / 2) * Real.exp (-2 * π * β * (‖x‖ ^ 2 / 2)) : ℝ) : ℂ) at hcomm
  rw [hfn, hcomm]
  congr 1
  have hrad := integral_radialLiftReal hw (fun t => g t * Real.exp (-2 * π * β * t))
  rw [hrad]
  unfold radialConstW laplacePairW
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-- **Gaussian-pairing reflection** (`vlo:eGaussRefl`): for `w ≥ 1` and `g` with integrable
Fourier-odd radial lift on `ℝ^{2w}`, `Φ(1/λ) = -λ^w Φ(λ)` for every `λ > 0`
(equivalently `Φ(λ) = -λ^{-w} Φ(1/λ)`). -/
theorem laplacePairW_inv {w : ℕ} (hw : 1 ≤ w) {g : ℝ → ℝ}
    (hint : Integrable (radialLift w g))
    (hodd : 𝓕 (radialLift w g) = -(radialLift w g)) {lam : ℝ} (hlam : 0 < lam) :
    laplacePairW w g lam⁻¹ = -(lam ^ w * laplacePairW w g lam) := by
  obtain ⟨hG_int, hG_four⟩ := fourier_radial_exp_W w hlam
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (2 * w)))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin (2 * w)))))
    (L := innerₗ (EuclideanSpace ℝ (Fin (2 * w)))) Real.continuous_fourierChar continuous_inner
    hint hG_int
  have hflip : (innerₗ (EuclideanSpace ℝ (Fin (2 * w)))).flip =
      innerₗ (EuclideanSpace ℝ (Fin (2 * w))) := by
    ext x y; exact real_inner_comm x y
  rw [hflip] at hswap
  change ∫ ξ : EuclideanSpace ℝ (Fin (2 * w)),
      (𝓕 (radialLift w g) ξ) • radialLift w (fun t => Real.exp (-2 * π * lam * t)) ξ =
    ∫ x : EuclideanSpace ℝ (Fin (2 * w)),
      (radialLift w g x) • 𝓕 (radialLift w (fun t => Real.exp (-2 * π * lam * t))) x at hswap
  rw [hodd, hG_four] at hswap
  have hexp : (fun t : ℝ => Real.exp (-2 * π * t / lam)) =
      fun t => Real.exp (-2 * π * lam⁻¹ * t) := by
    ext t; congr 1; ring
  have hlhs : ∫ ξ : EuclideanSpace ℝ (Fin (2 * w)),
      (-(radialLift w g)) ξ • radialLift w (fun t => Real.exp (-2 * π * lam * t)) ξ =
      -((radialConstW w * laplacePairW w g lam : ℝ) : ℂ) := by
    rw [← integral_radial_pair_W hw hint hlam, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.neg_apply, smul_eq_mul, neg_mul]
  have hrhs : ∫ x : EuclideanSpace ℝ (Fin (2 * w)),
      (radialLift w g x) • (((lam ^ (-(w : ℝ)) : ℝ) : ℂ) •
        radialLift w (fun t => Real.exp (-2 * π * t / lam)) x) =
      ((lam ^ (-(w : ℝ)) * (radialConstW w * laplacePairW w g lam⁻¹) : ℝ) : ℂ) := by
    rw [hexp, Complex.ofReal_mul, ← integral_radial_pair_W hw hint (inv_pos.mpr hlam),
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    ring
  simp only [Pi.smul_apply] at hswap
  rw [hlhs, hrhs] at hswap
  have hreal : -(radialConstW w * laplacePairW w g lam) =
      lam ^ (-(w : ℝ)) * (radialConstW w * laplacePairW w g lam⁻¹) := by
    apply Complex.ofReal_injective
    simpa [Complex.ofReal_neg, Complex.ofReal_mul] using hswap
  have hc_ne : radialConstW w ≠ 0 := (radialConstW_pos w).ne'
  have hlw : lam ^ (-(w : ℝ)) * lam ^ w = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlam]
    simp
  have hlw_pos : (lam ^ (-(w : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hlam _).ne'
  have h2 : laplacePairW w g lam⁻¹ = -(lam ^ w * laplacePairW w g lam) := by
    have h3 : radialConstW w * laplacePairW w g lam⁻¹ =
        -(lam ^ w * (radialConstW w * laplacePairW w g lam)) := by
      calc radialConstW w * laplacePairW w g lam⁻¹
          = (lam ^ (-(w : ℝ)) * lam ^ w) * (radialConstW w * laplacePairW w g lam⁻¹) := by
            rw [hlw, one_mul]
        _ = lam ^ w * (lam ^ (-(w : ℝ)) * (radialConstW w * laplacePairW w g lam⁻¹)) := by ring
        _ = lam ^ w * (-(radialConstW w * laplacePairW w g lam)) := by rw [← hreal]
        _ = -(lam ^ w * (radialConstW w * laplacePairW w g lam)) := by ring
    have h5 : radialConstW w * (laplacePairW w g lam⁻¹ + lam ^ w * laplacePairW w g lam) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h hc_ne
    · linarith
  exact h2

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.laplacePairW_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeightBand.laplacePairW_inv

end FormalResearch.ModularBootstrap.FixedWeightBand
