module

public import FormalResearch.ModularBootstrap.Mellin.MellinConvergence

/-!
# Hankel–Mellin Antisymmetry and Entire Extension (Lemma S1, `vlo:S1`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S1 (`vlo:S1`, lines 344–353).

Proves Lemma S1 directly from `TestClass.fourier_odd` (`𝓕 (radialLift 1 g) = -(radialLift 1 g)`)
via the Gaussian-mixture representation:
1. For every `λ > 0`, applying `VectorFourier.integral_fourierIntegral_smul_eq_flip` to
   `f = radialLift 1 g` and the Gaussian `x ↦ exp(-π λ ‖x‖²)` gives
   `Φ(λ) = -λ⁻¹ Φ(λ⁻¹)`, where `Φ(λ) = 2π ∫₀^∞ g(t) e^{-2π λ t} dt`
   (`laplacePairG_inv_symmetry`).
2. For `0 < z.re < 1`, taking the Mellin transform `∫₀^∞ λ^{-z} Φ(λ) dλ` and swapping integrals
   by absolute Fubini (`mellin_laplacePairG_eq`) yields `(2π)^z Γ(1 - z) Mg(z)` directly on the
   full strip `0 < Re z < 1`, while `λ ↦ λ⁻¹` sends it to `-(2π)^{1-z} Γ(z) Mg(1 - z)`.
3. Dividing by `Γ(z) Γ(1 - z)` yields the reflection identity `m_g(1 - z) = -m_g(z)` on
   `0 < Re z < 1` (`mellinMG_reflection`, `mellinTransformG_reflection`).
4. Gluing `m_g(z)` on `Re z > 0` with `-m_g(1 - z)` on `Re z < 1` gives an entire function
   `mellinMGEntire g` satisfying `mellinMGEntire g (1 - z) = -mellinMGEntire g z` everywhere on `ℂ`
   (`lemma_S1`, `lemma_S1_of_ge_two`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Mellin

open Crossing Integration ComplexBessel

/-! ### Section 1: Gaussian-mixture Laplace duality `Φ(λ) = -λ⁻¹ Φ(λ⁻¹)` -/

/-- The Laplace pairing `Φ(λ) = 2π ∫₀^∞ g(t) e^{-2π λ t} dt` (`λ > 0`). -/
noncomputable def laplacePairG (g : ℝ → ℝ) (lam : ℝ) : ℝ :=
  2 * Real.pi * ∫ t in Ioi (0 : ℝ), g t * Real.exp (-2 * Real.pi * lam * t)

private lemma integrable_radialLift_mul_exp {a : ℝ} {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 2) =>
      g (‖x‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam * (‖x‖ ^ 2 / 2))) := by
  have hreal : Integrable (radialLiftReal 1 g) := (integrable_radialLift_iff_real 1 g).1 hg.int_lift
  refine hreal.norm.mono' ?_ ?_
  · have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-2 * Real.pi * lam * (‖x‖ ^ 2 / 2))) := by fun_prop
    exact hreal.aestronglyMeasurable.mul hcont.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_le : Real.exp (-2 * Real.pi * lam * (‖x‖ ^ 2 / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have harg_nn : 0 ≤ 2 * Real.pi * lam * (‖x‖ ^ 2 / 2) := by positivity
      linarith
    calc |g (‖x‖ ^ 2 / 2)| * Real.exp (-2 * Real.pi * lam * (‖x‖ ^ 2 / 2))
        ≤ |g (‖x‖ ^ 2 / 2)| * 1 := by gcongr
      _ = ‖radialLiftReal 1 g x‖ := by simp [radialLiftReal]

/-- **Gaussian-mixture Laplace symmetry**: for `g ∈ TestClass virasoroProblem a` and `λ > 0`,
`Φ(λ) = -λ⁻¹ Φ(λ⁻¹)` where `Φ(λ) = 2π ∫₀^∞ g(t) e^{-2π λ t} dt`. -/
theorem laplacePairG_inv_symmetry {a : ℝ} {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {lam : ℝ} (hlam : 0 < lam) :
    laplacePairG g lam = -lam⁻¹ * laplacePairG g lam⁻¹ := by
  let G : ℝ → EuclideanSpace ℝ (Fin 2) → ℂ := fun l x =>
    Complex.exp (-((Real.pi * l : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2)
  have hG_int : Integrable (G lam) := by
    have hb : 0 < ((Real.pi * lam : ℝ) : ℂ).re := by simp [Real.pi_pos, hlam]
    simpa [G] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0
      (0 : EuclideanSpace ℝ (Fin 2))
  have hG_four : 𝓕 (G lam) = fun ξ : EuclideanSpace ℝ (Fin 2) => (lam : ℂ)⁻¹ * G lam⁻¹ ξ := by
    ext ξ
    have hb : 0 < ((Real.pi * lam : ℝ) : ℂ).re := by simp [Real.pi_pos, hlam]
    dsimp [G]
    rw [fourier_gaussian_innerProductSpace hb ξ]
    have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) / 2 : ℂ) = 1 := by
      rw [finrank_euclideanSpace_fin]; norm_num
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hlam_ne : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    rw [hdim, Complex.cpow_one]
    congr 1
    · push_cast; field_simp [hpi_ne, hlam_ne]
    · congr 1; push_cast; field_simp [hpi_ne, hlam_ne]
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (L := innerₗ (EuclideanSpace ℝ (Fin 2))) Real.continuous_fourierChar continuous_inner
    hg.int_lift hG_int
  have hflip : (innerₗ (EuclideanSpace ℝ (Fin 2))).flip = innerₗ (EuclideanSpace ℝ (Fin 2)) := by
    ext x y; exact real_inner_comm x y
  rw [hflip] at hswap
  change ∫ ξ : EuclideanSpace ℝ (Fin 2), (𝓕 (radialLift 1 g) ξ) • G lam ξ =
      ∫ x : EuclideanSpace ℝ (Fin 2), (radialLift 1 g x) • 𝓕 (G lam) x at hswap
  have hodd : 𝓕 (radialLift 1 g) = -(radialLift 1 g) := hg.fourier_odd
  rw [hodd, hG_four] at hswap
  have hlhs : ∫ ξ : EuclideanSpace ℝ (Fin 2), (-(radialLift 1 g)) ξ • G lam ξ =
      -(laplacePairG g lam : ℂ) := by
    have hneg : (fun ξ : EuclideanSpace ℝ (Fin 2) => (-(radialLift 1 g)) ξ • G lam ξ) =
        fun ξ => -(((g (‖ξ‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam * (‖ξ‖ ^ 2 / 2)) : ℝ) : ℂ)) := by
      ext ξ
      simp only [Pi.neg_apply, smul_eq_mul, neg_mul]
      unfold radialLift
      dsimp [G]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast; ring_nf
    have hcomm := Complex.ofRealCLM.integral_comp_comm (integrable_radialLift_mul_exp hg hlam)
    change (∫ ξ : EuclideanSpace ℝ (Fin 2),
        ((g (‖ξ‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam * (‖ξ‖ ^ 2 / 2)) : ℝ) : ℂ)) =
      ((∫ ξ : EuclideanSpace ℝ (Fin 2),
        g (‖ξ‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam * (‖ξ‖ ^ 2 / 2)) : ℝ) : ℂ) at hcomm
    have hrad := integral_radialLiftReal (w := 1) le_rfl
      (fun t => g t * Real.exp (-2 * Real.pi * lam * t))
    simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
      one_mul] at hrad
    rw [hneg, integral_neg, hcomm, hrad]
    rfl
  have hrhs : ∫ x : EuclideanSpace ℝ (Fin 2), (radialLift 1 g x) • ((lam : ℂ)⁻¹ * G lam⁻¹ x) =
      (lam : ℂ)⁻¹ * (laplacePairG g lam⁻¹ : ℂ) := by
    have hmul : (fun x : EuclideanSpace ℝ (Fin 2) =>
          (radialLift 1 g x) • ((lam : ℂ)⁻¹ * G lam⁻¹ x)) =
        fun x => (lam : ℂ)⁻¹ *
          ((g (‖x‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam⁻¹ * (‖x‖ ^ 2 / 2)) : ℝ) : ℂ) := by
      ext x
      simp only [smul_eq_mul]
      unfold radialLift
      dsimp [G]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast; ring_nf
    have hcomm := Complex.ofRealCLM.integral_comp_comm
      (integrable_radialLift_mul_exp hg (inv_pos.mpr hlam))
    change (∫ x : EuclideanSpace ℝ (Fin 2),
        ((g (‖x‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam⁻¹ * (‖x‖ ^ 2 / 2)) : ℝ) : ℂ)) =
      ((∫ x : EuclideanSpace ℝ (Fin 2),
        g (‖x‖ ^ 2 / 2) * Real.exp (-2 * Real.pi * lam⁻¹ * (‖x‖ ^ 2 / 2)) : ℝ) : ℂ) at hcomm
    have hrad := integral_radialLiftReal (w := 1) le_rfl
      (fun t => g t * Real.exp (-2 * Real.pi * lam⁻¹ * t))
    simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
      one_mul] at hrad
    rw [hmul, integral_const_mul, hcomm, hrad]
    rfl
  rw [hlhs, hrhs] at hswap
  have hinj : (-laplacePairG g lam : ℝ) = lam⁻¹ * laplacePairG g lam⁻¹ := by
    apply Complex.ofReal_inj.mp
    simpa [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_inv] using hswap
  linarith

/-! ### Section 2: Scaled Gamma integral and Fubini identity on `0 < Re z < 1` -/

private lemma gamma_integral_scaled_complex {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ))) (Ioi 0) ∧
      ∫ lam in Ioi (0 : ℝ), (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ)) =
        Complex.Gamma s * (r : ℂ) ^ (-s) := by
  have hint0 : IntegrableOn (fun u : ℝ => ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1)) (Ioi 0) :=
    Complex.GammaIntegral_convergent hs
  have hint_comp : IntegrableOn (fun lam : ℝ => (((-(r * lam)).exp : ℝ) : ℂ) *
      ((r * lam : ℝ) : ℂ) ^ (s - 1)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1)) 0 hr).mpr
      (by simpa using hint0)
  have hfac_ne : (r : ℂ) ^ (s - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
  have hint : IntegrableOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ)))
      (Ioi 0) := by
    have hmul_int : IntegrableOn (fun lam : ℝ => ((r : ℂ) ^ (s - 1))⁻¹ *
        ((((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1))) (Ioi 0) :=
      hint_comp.const_mul _
    refine hmul_int.congr_fun (fun lam hlam => ?_) measurableSet_Ioi
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (mem_Ioi.mp hlam).le,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    have hmul : (-(lam : ℂ) * (r : ℂ)) = -((r : ℂ) * (lam : ℂ)) := by ring
    rw [hmul]
    calc ((r : ℂ) ^ (s - 1))⁻¹ * (Complex.exp (-((r : ℂ) * (lam : ℂ))) *
            ((r : ℂ) ^ (s - 1) * (lam : ℂ) ^ (s - 1)))
        = (((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ) ^ (s - 1)) *
            ((lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ)))) := by ring
      _ = (lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ))) := by
          rw [inv_mul_cancel₀ hfac_ne, one_mul]
  refine ⟨hint, ?_⟩
  have hcomp_val : ∫ lam in Ioi (0 : ℝ),
      (((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1) =
      (r : ℂ)⁻¹ * Complex.Gamma s := by
    have h1 := integral_comp_mul_left_Ioi (fun u : ℝ => ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1)) 0 hr
    rw [mul_zero] at h1
    change ∫ lam in Ioi (0 : ℝ), (((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1) =
      r⁻¹ • ∫ u in Ioi (0 : ℝ), ((-u).exp : ℂ) * (u : ℂ) ^ (s - 1) at h1
    rw [h1, Complex.real_smul, Complex.ofReal_inv, ← Complex.GammaIntegral,
      ← Complex.Gamma_eq_integral hs]
  have heq : EqOn (fun lam : ℝ => (lam : ℂ) ^ (s - 1) * Complex.exp (-(lam : ℂ) * (r : ℂ)))
      (fun lam : ℝ => ((r : ℂ) ^ (s - 1))⁻¹ *
        ((((-(r * lam)).exp : ℝ) : ℂ) * ((r * lam : ℝ) : ℂ) ^ (s - 1))) (Ioi 0) := by
    intro lam hlam
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (mem_Ioi.mp hlam).le,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    have hmul : (-(lam : ℂ) * (r : ℂ)) = -((r : ℂ) * (lam : ℂ)) := by ring
    rw [hmul]
    calc (lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ)))
        = (((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ) ^ (s - 1)) *
            ((lam : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * (lam : ℂ)))) := by
          rw [inv_mul_cancel₀ hfac_ne, one_mul]
      _ = ((r : ℂ) ^ (s - 1))⁻¹ * (Complex.exp (-((r : ℂ) * (lam : ℂ))) *
            ((r : ℂ) ^ (s - 1) * (lam : ℂ) ^ (s - 1))) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hcomp_val]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hpow_neg : ((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ)⁻¹ = (r : ℂ) ^ (-s) := by
    rw [← Complex.cpow_neg, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hrc]
    congr 1; ring
  calc ((r : ℂ) ^ (s - 1))⁻¹ * ((r : ℂ)⁻¹ * Complex.Gamma s)
      = Complex.Gamma s * (((r : ℂ) ^ (s - 1))⁻¹ * (r : ℂ)⁻¹) := by ring
    _ = Complex.Gamma s * (r : ℂ) ^ (-s) := by rw [hpow_neg]

private lemma gamma_integral_scaled_real {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun lam : ℝ => lam ^ (s - 1) * Real.exp (-lam * r)) (Ioi 0) ∧
      ∫ lam in Ioi (0 : ℝ), lam ^ (s - 1) * Real.exp (-lam * r) =
        Real.Gamma s * r ^ (-s) := by
  have heq : (fun lam : ℝ => lam ^ (s - 1) * Real.exp (-lam * r)) =
      fun lam : ℝ => lam ^ (s - 1) * Real.exp (-(r * lam)) := by
    ext lam; ring_nf
  rw [heq]
  have hint0 : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (s - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hs
  have hint_comp : IntegrableOn (fun lam : ℝ => Real.exp (-(r * lam)) * (r * lam) ^ (s - 1))
      (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u) * u ^ (s - 1)) 0 hr).mpr
      (by simpa using hint0)
  have hint : IntegrableOn (fun lam : ℝ => lam ^ (s - 1) * Real.exp (-(r * lam))) (Ioi 0) := by
    have hmul_int : IntegrableOn (fun lam : ℝ => (r ^ (s - 1))⁻¹ *
        (Real.exp (-(r * lam)) * (r * lam) ^ (s - 1))) (Ioi 0) :=
      hint_comp.const_mul _
    refine hmul_int.congr_fun (fun lam hlam => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.mul_rpow hr.le (mem_Ioi.mp hlam).le]
    have hne : r ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp [hne]
  refine ⟨hint, ?_⟩
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, Real.rpow_neg hr.le, one_div,
    ← Real.inv_rpow hr.le, mul_comm]

private lemma mellin_laplace_integrand_eq (g : ℝ → ℝ) (z : ℂ) (lam t : ℝ) :
    (lam : ℂ) ^ (-z) * ((g t : ℂ) * (Real.exp (-2 * Real.pi * lam * t) : ℝ)) =
      (g t : ℂ) * ((lam : ℂ) ^ ((1 - z) - 1) *
        Complex.exp (-(lam : ℂ) * ((2 * Real.pi * t : ℝ) : ℂ))) := by
  rw [Complex.ofReal_exp]
  have hsub : (1 - z) - 1 = -z := by ring
  have hexp : (-2 * Real.pi * lam * t : ℝ) = -(lam * (2 * Real.pi * t)) := by ring
  rw [hsub, hexp]
  push_cast; ring_nf

/-- **Mellin–Laplace Fubini identity**: for `2 ≤ a`, `g ∈ TestClass virasoroProblem a`, and
`0 < z.re < 1`, `λ ↦ λ^{-z} Φ(λ)` is integrable on `(0, ∞)` and its integral equals
`(2π)^z Γ(1 - z) Mg(z)`. -/
theorem mellin_laplacePairG_eq {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    IntegrableOn (fun lam : ℝ => (lam : ℂ) ^ (-z) * (laplacePairG g lam : ℂ)) (Ioi 0) ∧
      ∫ lam in Ioi (0 : ℝ), (lam : ℂ) ^ (-z) * (laplacePairG g lam : ℂ) =
        (2 * (Real.pi : ℂ)) ^ z * Complex.Gamma (1 - z) * mellinTransformG g z := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let H : ℝ × ℝ → ℂ := fun p =>
    (p.1 : ℂ) ^ (-z) * ((g p.2 : ℂ) * (Real.exp (-2 * Real.pi * p.1 * p.2) : ℝ))
  have hH_meas : AEStronglyMeasurable H (μ.prod μ) := by
    rw [show μ.prod μ = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) by
      dsimp [μ]; rw [Measure.prod_restrict, ← Measure.volume_eq_prod]]
    have hcont_pow : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (-z)) (Ioi 0 ×ˢ Ioi 0) := by
      intro p hp
      have hp1 : (p.1 : ℂ) ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hp.1))
      exact ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.cpow
        continuousAt_const hp1).continuousWithinAt
    have hcont_g : ContinuousOn (fun p : ℝ × ℝ => (g p.2 : ℂ)) (Ioi 0 ×ˢ Ioi 0) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact hg.cont.comp continuous_snd.continuousOn fun p hp => (mem_Ioi.mp hp.2).le
    have hcont_exp : ContinuousOn
        (fun p : ℝ × ℝ => ((Real.exp (-2 * Real.pi * p.1 * p.2) : ℝ) : ℂ)) (Ioi 0 ×ˢ Ioi 0) := by
      fun_prop
    exact (hcont_pow.mul (hcont_g.mul hcont_exp)).aestronglyMeasurable
      (isOpen_Ioi.prod isOpen_Ioi).measurableSet
  have hz1_re : 0 < (1 - z).re := by simp [hz1]
  have hinner_int : ∀ t ∈ Ioi (0 : ℝ),
      Integrable (fun lam : ℝ => H (lam, t)) μ := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have h2pit : 0 < 2 * Real.pi * t := by positivity
    have hgam : IntegrableOn (fun lam : ℝ => (g t : ℂ) *
        ((lam : ℂ) ^ ((1 - z) - 1) * Complex.exp (-(lam : ℂ) * ((2 * Real.pi * t : ℝ) : ℂ))))
        (Ioi 0) :=
      (gamma_integral_scaled_complex hz1_re h2pit).1.const_mul (g t : ℂ)
    have heq : EqOn (fun lam : ℝ => (g t : ℂ) * ((lam : ℂ) ^ ((1 - z) - 1) *
          Complex.exp (-(lam : ℂ) * ((2 * Real.pi * t : ℝ) : ℂ))))
        (fun lam : ℝ => H (lam, t)) (Ioi 0) :=
      fun lam _ => (mellin_laplace_integrand_eq g z lam t).symm
    exact hgam.congr_fun heq measurableSet_Ioi
  have houter_int : Integrable (fun t : ℝ => ∫ lam : ℝ, ‖H (lam, t)‖ ∂μ) μ := by
    have hnorm_eq : EqOn (fun t : ℝ => ∫ lam : ℝ, ‖H (lam, t)‖ ∂μ)
        (fun t : ℝ => (Real.Gamma (1 - z.re) * (2 * Real.pi) ^ (z.re - 1)) *
          (|g t| * t ^ (z.re - 1))) (Ioi 0) := by
      intro t ht
      have ht0 : 0 < t := mem_Ioi.mp ht
      have h2pit : 0 < 2 * Real.pi * t := by positivity
      have hlam_eq : EqOn (fun lam : ℝ => ‖H (lam, t)‖)
          (fun lam : ℝ => |g t| * (lam ^ ((1 - z.re) - 1) * Real.exp (-lam * (2 * Real.pi * t))))
          (Ioi 0) := by
        intro lam hlam
        have hlam0 : 0 < lam := mem_Ioi.mp hlam
        dsimp [H]
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hlam0,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, Complex.neg_re]
        have he1 : (1 - z.re) - 1 = -z.re := by ring
        have he2 : -2 * Real.pi * lam * t = -lam * (2 * Real.pi * t) := by ring
        rw [he1, he2]; ring
      change ∫ lam in Ioi (0 : ℝ), ‖H (lam, t)‖ = _
      have hgam_r := (gamma_integral_scaled_real hz1_re h2pit).2
      rw [show (1 - z).re = 1 - z.re by simp] at hgam_r
      rw [setIntegral_congr_fun measurableSet_Ioi hlam_eq, integral_const_mul, hgam_r]
      have hmul_rpow : (2 * Real.pi * t) ^ (-(1 - z.re)) =
          (2 * Real.pi) ^ (z.re - 1) * t ^ (z.re - 1) := by
        rw [Real.mul_rpow (by positivity) ht0.le]
        have he : -(1 - z.re) = z.re - 1 := by ring
        rw [he]
      rw [hmul_rpow]; ring
    have hmg : IntegrableOn (fun t : ℝ =>
        (Real.Gamma (1 - z.re) * (2 * Real.pi) ^ (z.re - 1)) * (|g t| * t ^ (z.re - 1))) (Ioi 0) :=
      (integrableOn_abs_mellinTransformG ha hg hz0).const_mul _
    exact hmg.congr_fun hnorm_eq.symm measurableSet_Ioi
  have hH_prod : Integrable H (μ.prod μ) := by
    rw [integrable_prod_iff' hH_meas]
    refine ⟨?_, houter_int⟩
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall hinner_int
  have hleft_int : IntegrableOn (fun lam : ℝ => (2 * (Real.pi : ℂ)) * ∫ t : ℝ, H (lam, t) ∂μ)
      (Ioi 0) :=
    hH_prod.integral_prod_left.const_mul (2 * (Real.pi : ℂ))
  have hleft_eq : EqOn (fun lam : ℝ => (lam : ℂ) ^ (-z) * (laplacePairG g lam : ℂ))
      (fun lam : ℝ => (2 * (Real.pi : ℂ)) * ∫ t : ℝ, H (lam, t) ∂μ) (Ioi 0) := by
    intro lam hlam
    have hlam0 : 0 < lam := mem_Ioi.mp hlam
    have hint_t : IntegrableOn (fun t : ℝ => g t * Real.exp (-2 * Real.pi * lam * t)) (Ioi 0) := by
      refine (testClass_integrableOn_abs hg).mono' ?_ ?_
      · have hcont_g : ContinuousOn (fun t : ℝ => g t) (Ioi 0) := hg.cont.mono Ioi_subset_Ici_self
        have hcont_e : Continuous (fun t : ℝ => Real.exp (-2 * Real.pi * lam * t)) := by fun_prop
        exact (hcont_g.mul hcont_e.continuousOn).aestronglyMeasurable measurableSet_Ioi
      · rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun t ht => ?_
        have ht0 : 0 < t := mem_Ioi.mp ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hexp1 : Real.exp (-2 * Real.pi * lam * t) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have harg_nn : 0 ≤ 2 * Real.pi * lam * t := by positivity
          linarith
        calc |g t| * Real.exp (-2 * Real.pi * lam * t) ≤ |g t| * 1 := by gcongr
          _ = |g t| := mul_one _
    have hcast : ((∫ t in Ioi (0 : ℝ), g t * Real.exp (-2 * Real.pi * lam * t) : ℝ) : ℂ) =
        ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (Real.exp (-2 * Real.pi * lam * t) : ℝ) := by
      simpa using (Complex.ofRealCLM.integral_comp_comm hint_t).symm
    dsimp [H, laplacePairG, μ]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, hcast]
    change (lam : ℂ) ^ (-z) * (2 * (Real.pi : ℂ) *
        ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (Real.exp (-2 * Real.pi * lam * t) : ℝ)) =
      2 * (Real.pi : ℂ) *
        ∫ t in Ioi (0 : ℝ), (lam : ℂ) ^ (-z) * ((g t : ℂ) * (Real.exp (-2 * Real.pi * lam * t) : ℝ))
    rw [mul_left_comm, ← integral_const_mul ((lam : ℂ) ^ (-z))]
  refine ⟨hleft_int.congr_fun hleft_eq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hleft_eq, integral_const_mul,
    integral_integral_swap hH_prod]
  have hinner_val : EqOn (fun t : ℝ => ∫ lam : ℝ, H (lam, t) ∂μ)
      (fun t : ℝ => (2 * (Real.pi : ℂ)) ^ (z - 1) * Complex.Gamma (1 - z) *
        ((g t : ℂ) * (t : ℂ) ^ (z - 1))) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have h2pit : 0 < 2 * Real.pi * t := by positivity
    have heq : EqOn (fun lam : ℝ => H (lam, t))
        (fun lam : ℝ => (g t : ℂ) * ((lam : ℂ) ^ ((1 - z) - 1) *
          Complex.exp (-(lam : ℂ) * ((2 * Real.pi * t : ℝ) : ℂ)))) (Ioi 0) :=
      fun lam _ => mellin_laplace_integrand_eq g z lam t
    change ∫ lam in Ioi (0 : ℝ), H (lam, t) = _
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
      (gamma_integral_scaled_complex hz1_re h2pit).2]
    have hcpow_split : ((2 * Real.pi * t : ℝ) : ℂ) ^ (-(1 - z)) =
        (2 * (Real.pi : ℂ)) ^ (z - 1) * (t : ℂ) ^ (z - 1) := by
      have hneg : -(1 - z) = z - 1 := by ring
      rw [hneg, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) ht0.le]
      push_cast; rfl
    rw [hcpow_split]; ring
  change (2 * (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ), (∫ lam : ℝ, H (lam, t) ∂μ) = _
  rw [setIntegral_congr_fun measurableSet_Ioi hinner_val, integral_const_mul]
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h2pi_pow : (2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (z - 1) =
      (2 * (Real.pi : ℂ)) ^ z := by
    conv_lhs => lhs; rw [← Complex.cpow_one (2 * (Real.pi : ℂ))]
    rw [← Complex.cpow_add _ _ h2pi_ne]
    congr 1; ring
  unfold mellinTransformG
  calc (2 * (Real.pi : ℂ)) * ((2 * (Real.pi : ℂ)) ^ (z - 1) * Complex.Gamma (1 - z) *
          ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1))
      = ((2 * (Real.pi : ℂ)) * (2 * (Real.pi : ℂ)) ^ (z - 1)) * Complex.Gamma (1 - z) *
          ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1) := by ring
    _ = (2 * (Real.pi : ℂ)) ^ z * Complex.Gamma (1 - z) *
          ∫ t in Ioi (0 : ℝ), (g t : ℂ) * (t : ℂ) ^ (z - 1) := by rw [h2pi_pow]

/-! ### Section 3: Strip reflection and entire extension `mellinMGEntire` (`vlo:S1`) -/

/-- **Reflection identity for `m_g` on `0 < Re z < 1`** (`vlo:S1`). -/
theorem mellinMG_reflection {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    mellinMG g (1 - z) = -mellinMG g z := by
  have hz1_re0 : 0 < (1 - z).re := by simp [hz1]
  have hz1_re1 : (1 - z).re < 1 := by simp [hz0]
  have hz_lhs := (mellin_laplacePairG_eq ha hg hz0 hz1).2
  have hz_rhs := (mellin_laplacePairG_eq ha hg hz1_re0 hz1_re1).2
  rw [sub_sub_cancel] at hz_rhs
  have himg : (fun u : ℝ => u⁻¹) '' Ioi 0 = Ioi 0 := by
    ext lam; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact inv_pos.mpr hu
    · intro hlam; exact ⟨lam⁻¹, inv_pos.mpr hlam, inv_inv lam⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul (f := fun u : ℝ => u⁻¹)
    (f' := fun u : ℝ => -(u ^ 2)⁻¹) measurableSet_Ioi
    (fun u hu => (hasDerivAt_inv (mem_Ioi.mp hu).ne').hasDerivWithinAt)
    (fun u₁ _ u₂ _ h => inv_injective h)
    (fun lam : ℝ => (lam : ℂ) ^ (-z) * (laplacePairG g lam : ℂ))
  rw [himg] at hcov
  have hcov_eq : ∫ lam in Ioi (0 : ℝ), (lam : ℂ) ^ (-z) * (laplacePairG g lam : ℂ) =
      -∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (-(1 - z)) * (laplacePairG g u : ℂ) := by
    rw [hcov, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := mem_Ioi.mp hu
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
    rw [abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu0)), Complex.real_smul,
      laplacePairG_inv_symmetry hg (inv_pos.mpr hu0), inv_inv, Complex.ofReal_mul,
      Complex.ofReal_neg]
    have hpow1 : ((u⁻¹ : ℝ) : ℂ) ^ (-z) = (u : ℂ) ^ z := by
      have harg : (u : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hu0.le]
        exact Real.pi_pos.ne
      rw [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow (u : ℂ) z harg, inv_inv]
    have hpow2 : (((u ^ 2)⁻¹ : ℝ) : ℂ) * (u : ℂ) ^ z * (-(u : ℂ)) =
        -((u : ℂ) ^ (-(1 - z))) := by
      have hu2 : (((u ^ 2)⁻¹ : ℝ) : ℂ) = (u : ℂ) ^ (-2 : ℂ) := by
        rw [Complex.ofReal_inv, Complex.ofReal_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg]
        norm_num
      have hu1 : (u : ℂ) = (u : ℂ) ^ (1 : ℂ) := (Complex.cpow_one _).symm
      have hmul_c : (u : ℂ) ^ (-2 : ℂ) * (u : ℂ) ^ z * (u : ℂ) =
          (u : ℂ) ^ (-2 : ℂ) * (u : ℂ) ^ z * (u : ℂ) ^ (1 : ℂ) := by
        rw [← hu1]
      calc (((u ^ 2)⁻¹ : ℝ) : ℂ) * (u : ℂ) ^ z * (-(u : ℂ))
          = -((u : ℂ) ^ (-2 : ℂ) * (u : ℂ) ^ z * (u : ℂ)) := by rw [hu2]; ring
        _ = -((u : ℂ) ^ (-2 : ℂ) * (u : ℂ) ^ z * (u : ℂ) ^ (1 : ℂ)) := by rw [hmul_c]
        _ = -((u : ℂ) ^ (-2 + z + 1)) := by
            rw [← Complex.cpow_add _ _ huc, ← Complex.cpow_add _ _ huc]
        _ = -((u : ℂ) ^ (-(1 - z))) := by congr 2; ring
    calc (((u ^ 2)⁻¹ : ℝ) : ℂ) * (((u⁻¹ : ℝ) : ℂ) ^ (-z) * (-((u : ℂ)) * (laplacePairG g u : ℂ)))
        = (((u ^ 2)⁻¹ : ℝ) : ℂ) * ((u⁻¹ : ℝ) : ℂ) ^ (-z) * (-(u : ℂ)) * (laplacePairG g u : ℂ) := by
          ring
      _ = (((u ^ 2)⁻¹ : ℝ) : ℂ) * (u : ℂ) ^ z * (-(u : ℂ)) * (laplacePairG g u : ℂ) := by
          rw [hpow1]
      _ = -((u : ℂ) ^ (-(1 - z)) * (laplacePairG g u : ℂ)) := by
          rw [hpow2]; ring
  have hid : (2 * (Real.pi : ℂ)) ^ z * Complex.Gamma (1 - z) * mellinTransformG g z =
      -((2 * (Real.pi : ℂ)) ^ (1 - z) * Complex.Gamma z * mellinTransformG g (1 - z)) := by
    rw [← hz_lhs, ← hz_rhs, hcov_eq]
  have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hg1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz1_re0
  unfold mellinMG
  rw [eq_neg_iff_add_eq_zero]
  field_simp [hgz, hg1z]
  linear_combination hid

/-- **Reflection identity for `Mg` on `0 < Re z < 1`** (`vlo:S1`):
`-Mg(z) = (2π)^{1 - 2z} (Γ(z) / Γ(1 - z)) Mg(1 - z)`. -/
theorem mellinTransformG_reflection {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    -mellinTransformG g z =
      (2 * (Real.pi : ℂ)) ^ (1 - 2 * z) * (Complex.Gamma z / Complex.Gamma (1 - z)) *
        mellinTransformG g (1 - z) := by
  have hz1_re0 : 0 < (1 - z).re := by simp [hz1]
  have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hg1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz1_re0
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h2piz_ne : (2 * (Real.pi : ℂ)) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl h2pi_ne)
  have hpow : (2 * (Real.pi : ℂ)) ^ (1 - z) / (2 * (Real.pi : ℂ)) ^ z =
      (2 * (Real.pi : ℂ)) ^ (1 - 2 * z) := by
    rw [← Complex.cpow_sub _ _ h2pi_ne]
    congr 1; ring
  have hm := mellinMG_reflection ha hg hz0 hz1
  unfold mellinMG at hm
  rw [← hpow]
  have hm' : (2 * (Real.pi : ℂ)) ^ z * mellinTransformG g z / Complex.Gamma z +
      (2 * (Real.pi : ℂ)) ^ (1 - z) * mellinTransformG g (1 - z) / Complex.Gamma (1 - z) = 0 := by
    linear_combination hm
  rw [eq_comm, ← sub_eq_zero]
  field_simp [hgz, hg1z, h2piz_ne] at hm' ⊢
  linear_combination hm'

/-- Glued entire extension of `m_g(z) = (2π)^z Mg(z) / Γ(z)` to all of `ℂ` (`vlo:S1`). -/
noncomputable def mellinMGEntire (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  if 0 < z.re then mellinMG g z else -mellinMG g (1 - z)

theorem mellinMGEntire_of_re_pos (g : ℝ → ℝ) {z : ℂ} (hz : 0 < z.re) :
    mellinMGEntire g z = mellinMG g z := by
  simp [mellinMGEntire, hz]

theorem mellinMGEntire_one_sub {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) (z : ℂ) :
    mellinMGEntire g (1 - z) = -mellinMGEntire g z := by
  unfold mellinMGEntire
  by_cases hz0 : 0 < z.re
  · by_cases hz1 : 0 < (1 - z).re
    · simp only [hz0, hz1, ↓reduceIte]
      exact mellinMG_reflection ha hg hz0 (by simpa using hz1)
    · simp only [hz0, hz1, ↓reduceIte, sub_sub_cancel]
  · have hz1 : 0 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    simp only [hz0, hz1, ↓reduceIte, neg_neg]

theorem differentiable_mellinMGEntire {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    Differentiable ℂ (mellinMGEntire g) := by
  have hdiff_pos : DifferentiableOn ℂ (mellinMG g) {z : ℂ | 0 < z.re} :=
    differentiableOn_mellinMG ha hg
  intro z
  by_cases hz0 : 0 < z.re
  · have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hda : DifferentiableAt ℂ (mellinMG g) z :=
      (hdiff_pos z hz0).differentiableAt (hopen.mem_nhds hz0)
    refine hda.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hz0] with w hw
    exact mellinMGEntire_of_re_pos g hw
  · have hz1 : z.re < 1 := by linarith
    have hopen : IsOpen {w : ℂ | w.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have h1z_pos : 0 < (1 - z).re := by simp [hz1]
    have hopen_pos : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hda : DifferentiableAt ℂ (fun w : ℂ => -mellinMG g (1 - w)) z := by
      have h1 : DifferentiableAt ℂ (mellinMG g) (1 - z) :=
        (hdiff_pos (1 - z) h1z_pos).differentiableAt (hopen_pos.mem_nhds h1z_pos)
      exact (h1.comp z ((differentiableAt_const 1).sub differentiableAt_id)).neg
    refine hda.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hz1] with w hw
    by_cases hw0 : 0 < w.re
    · rw [mellinMGEntire_of_re_pos g hw0, mellinMG_reflection ha hg hw0 hw, neg_neg]
    · unfold mellinMGEntire
      simp only [hw0, ↓reduceIte]

/-- **Lemma S1 (general `a ≥ 2` form)** (`lower_o1_two_edge.tex`, §J2, `vlo:S1`):
for `2 ≤ a` and `g ∈ TestClass virasoroProblem a`, `m_g(z) = (2π)^z Mg(z) / Γ(z)` extends to an
entire function `F : ℂ → ℂ` satisfying `F (1 - z) = - F z` for all `z : ℂ`. -/
theorem lemma_S1_of_ge_two {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem a g) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, 0 < z.re →
        F z = (2 * (Real.pi : ℂ)) ^ z * mellinTransformG g z / Complex.Gamma z) ∧
      ∀ z : ℂ, F (1 - z) = -F z :=
  ⟨mellinMGEntire g, differentiable_mellinMGEntire ha hg,
    fun _ hz => mellinMGEntire_of_re_pos g hz, mellinMGEntire_one_sub ha hg⟩

/-- **Lemma S1 (entire, source-free antisymmetry)** (`lower_o1_two_edge.tex`, §J2, `vlo:S1`):
for `24 ≤ c'` and `g ∈ TestClass virasoroProblem (c' / 12)`, `m_g(z) = (2π)^z Mg(z) / Γ(z)`
extends to an entire function `F : ℂ → ℂ` satisfying `F (1 - z) = - F z` for all `z : ℂ`. -/
theorem lemma_S1 {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, 0 < z.re →
        F z = (2 * (Real.pi : ℂ)) ^ z * mellinTransformG g z / Complex.Gamma z) ∧
      ∀ z : ℂ, F (1 - z) = -F z :=
  lemma_S1_of_ge_two (by linarith) hg

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Mellin.laplacePairG_inv_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.laplacePairG_inv_symmetry

/-- info: 'FormalResearch.ModularBootstrap.Mellin.mellinMG_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.mellinMG_reflection

/-- info: 'FormalResearch.ModularBootstrap.Mellin.mellinTransformG_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.mellinTransformG_reflection

/-- info: 'FormalResearch.ModularBootstrap.Mellin.lemma_S1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mellin.lemma_S1

end FormalResearch.ModularBootstrap.Mellin
