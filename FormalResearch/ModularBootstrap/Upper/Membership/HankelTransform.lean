module

public import FormalResearch.ModularBootstrap.Upper.Membership.Vacuum
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeRepresentation
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The Hankel transform `𝓗_w` as the radial Fourier transform

`hankelTransform w u` is the real radial profile of the Fourier transform of `radialLift w u`
(radial symmetry and reality of `𝓕 (radialLift w u)` are proved here from linear-isometry
invariance, Mathlib's `fourier_comp_linearIsometry`), so that
`𝓕 (radialLift w u) = radialLift w (hankelTransform w u)` (`fourier_radialLift_eq_hankelTransform`).
At `w = 1` it is the order-zero Hankel transform `2π ∫₀^∞ u(s) J₀(4π √(s t)) ds` used by the
edge lemmas (`hankelTransform_one_eq_edgeHankel`: `edgeHankel c' h₀ t = ĥ(t)` for the comb profile
`u(s) = h₀(√(3s/c'))`), which connects Lemma `SD_H`/`SD_G`/`SD_V` to the membership statement.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Upper.Hankel

section Symmetry

variable {w : ℕ}

/-- The first coordinate vector of `ℝ^{2w}` (`w ≥ 1`). -/
def e0 (hw : 1 ≤ w) : Fin (2 * w) := ⟨0, by omega⟩

/-- `𝓕 (radialLift w u)` is radial. -/
theorem fourier_radialLift_radial (hw : 1 ≤ w) (u : ℝ → ℝ) (ξ : EuclideanSpace ℝ (Fin (2 * w))) :
    𝓕 (radialLift w u) ξ = 𝓕 (radialLift w u) (EuclideanSpace.single (e0 hw) ‖ξ‖) := by
  set v : EuclideanSpace ℝ (Fin (2 * w)) := EuclideanSpace.single (e0 hw) ‖ξ‖ with hv
  have hnorm : ‖v‖ = ‖ξ‖ := by
    have := PiLp.norm_single 2 (fun _ : Fin (2 * w) => ℝ) (e0 hw) ‖ξ‖
    rw [hv, this, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  set A : EuclideanSpace ℝ (Fin (2 * w)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * w)) :=
    (Submodule.span ℝ {v - ξ})ᗮ.reflection with hA
  have hAv : A v = ξ := Submodule.reflection_sub hnorm
  have hcomp : (radialLift w u) ∘ A = radialLift w u := by
    ext x; simp [radialLift, Function.comp]
  have := Real.fourier_comp_linearIsometry A (radialLift w u) v
  rw [hcomp, hAv] at this
  exact this.symm

/-- `𝓕 (radialLift w u)` is real-valued for real `u`. -/
theorem fourier_radialLift_conj (hw : 1 ≤ w) (u : ℝ → ℝ) (ξ : EuclideanSpace ℝ (Fin (2 * w))) :
    (starRingEnd ℂ) (𝓕 (radialLift w u) ξ) = 𝓕 (radialLift w u) ξ := by
  have h1 : (starRingEnd ℂ) (𝓕 (radialLift w u) ξ) = 𝓕 (radialLift w u) (-ξ) := by
    simp only [Real.fourier_eq', smul_eq_mul]
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hr : (starRingEnd ℂ) (radialLift w u v) = radialLift w u v := by
      simp [radialLift, Complex.conj_ofReal]
    have he : (starRingEnd ℂ) (Complex.exp (((-2 * π * ⟪v, ξ⟫ : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (((-2 * π * ⟪v, -ξ⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      congr 1
      rw [inner_neg_right]
      push_cast; ring
    show (starRingEnd ℂ) (_ * _) = _ * _
    rw [map_mul, hr, he]
  rw [h1, fourier_radialLift_radial hw u (-ξ), fourier_radialLift_radial hw u ξ, norm_neg]

/-- The Hankel transform `ĥ = 𝓗_w u`: the real radial profile of `𝓕 (radialLift w u)`
(`t = ‖ξ‖² / 2`). -/
noncomputable def hankelTransform (w : ℕ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  if hw : 1 ≤ w then
    (𝓕 (radialLift w u) (EuclideanSpace.single (e0 hw) (Real.sqrt (2 * t)))).re
  else 0

/-- `𝓕 (radialLift w u) = radialLift w (hankelTransform w u)`. -/
theorem fourier_radialLift_eq_hankelTransform (hw : 1 ≤ w) (u : ℝ → ℝ) :
    𝓕 (radialLift w u) = radialLift w (hankelTransform w u) := by
  ext ξ
  have hnn : 0 ≤ ‖ξ‖ ^ 2 / 2 := by positivity
  have hsq : Real.sqrt (2 * (‖ξ‖ ^ 2 / 2)) = ‖ξ‖ := by
    rw [show 2 * (‖ξ‖ ^ 2 / 2) = ‖ξ‖ ^ 2 by ring]; exact Real.sqrt_sq (norm_nonneg _)
  simp only [radialLift, hankelTransform, dif_pos hw, hsq]
  rw [← fourier_radialLift_radial hw u ξ]
  have hre := fourier_radialLift_conj hw u ξ
  exact (Complex.conj_eq_iff_re.mp hre).symm

/-- `hankelTransform w u` is continuous on `[0, ∞)` when the radial lift of `u` is integrable. -/
theorem continuousOn_hankelTransform (hw : 1 ≤ w) {u : ℝ → ℝ}
    (hint : Integrable (radialLift w u)) : ContinuousOn (hankelTransform w u) (Ici 0) := by
  have hF : Continuous (𝓕 (radialLift w u)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ (EuclideanSpace ℝ (Fin (2 * w)))) continuous_inner hint
  have hsingle : Continuous (fun r : ℝ =>
      (EuclideanSpace.single (e0 hw) r : EuclideanSpace ℝ (Fin (2 * w)))) := by
    unfold EuclideanSpace.single PiLp.single
    have h : Continuous (fun r : ℝ => (Pi.single (e0 hw) r : Fin (2 * w) → ℝ)) :=
      continuous_pi fun j => by
        by_cases hj : j = e0 hw
        · subst hj; simp only [Pi.single_eq_same]; exact continuous_id
        · simp only [Pi.single_eq_of_ne hj]; exact continuous_const
    exact (PiLp.continuous_toLp 2 (fun _ : Fin (2 * w) => ℝ)).comp h
  have : Continuous fun t : ℝ =>
      (𝓕 (radialLift w u) (EuclideanSpace.single (e0 hw) (Real.sqrt (2 * t)))).re :=
    Complex.continuous_re.comp (hF.comp (hsingle.comp
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))))
  refine this.continuousOn.congr fun t _ => ?_
  simp [hankelTransform, hw]

/-- A profile with continuous integrable lift and a continuous integrable Hankel transform is a
`RadialFourierPair`. -/
theorem radialFourierPair_hankelTransform (hw : 1 ≤ w) {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Ici 0)) (hint : Integrable (radialLift w u))
    (hint' : Integrable (radialLift w (hankelTransform w u))) :
    RadialFourierPair w u (hankelTransform w u) :=
  ⟨hcont, continuousOn_hankelTransform hw hint, hint, hint',
    fourier_radialLift_eq_hankelTransform hw u⟩

/-- Hankel formula in terms of `hankelTransform`: for real `b`,
`hankelContinuationW w c' u b = -ĥ(c' b² / 3)`. -/
theorem hankelContinuationW_eq_neg_hankelTransform (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c')
    {u : ℝ → ℝ} (hcont : ContinuousOn u (Ici 0)) (hint : Integrable (radialLift w u)) (b : ℝ) :
    hankelContinuationW w c' u (b : ℂ) = -(hankelTransform w u (c' * b ^ 2 / 3) : ℂ) := by
  have := fourier_radialLift_apply_eq hw hc' hcont hint b
  rw [fourier_radialLift_eq_hankelTransform hw u, radialLift_single hw hc'] at this
  rw [this]; ring

end Symmetry

/-! ### Order zero: `hankelTransform 1` is `edgeHankel` -/

lemma integration_besselI0C_neg (z : ℂ) : Integration.besselI0C (-z) = Integration.besselI0C z := by
  unfold Integration.besselI0C
  congr 1
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => Complex.exp (z * (Real.cos θ : ℝ))) Real.pi (a := 0) (b := Real.pi)
  simp only [sub_zero, sub_self] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Real.cos_pi_sub, Complex.ofReal_neg, mul_neg, neg_mul]

lemma besselJ_zero_eq_besselI0C (y : ℝ) :
    Complex.besselJ 0 (y : ℂ) = Integration.besselI0C (Complex.I * y) := by
  have h1 := ComplexBessel.integration_besselI0C_eq_blowup (-Complex.I * (y : ℂ))
  have h2 : ModularBootstrap.besselI0C (-Complex.I * (y : ℂ)) = Complex.besselJ 0 (y : ℂ) := by
    unfold ModularBootstrap.besselI0C
    congr 1
    rw [← mul_assoc, show Complex.I * -Complex.I = 1 by simp, one_mul]
  rw [← h2, ← h1, ← integration_besselI0C_neg]
  congr 1; ring

/-- **Order-zero link**: if `h₀(√(3s/c')) = u(s)` for `s > 0` with `u` real, continuous on `[0, ∞)`
with integrable radial lift on `ℝ²`, then `edgeHankel c' h₀ t = ĥ(t)` for `t > 0`,
where `ĥ = hankelTransform 1 u` (`edgeHankel` is the `J₀` form `2π ∫₀^∞ h₀ J₀(4π√(st)) ds`). -/
theorem hankelTransform_one_eq_edgeHankel {c' : ℝ} (hc' : 0 < c') {h₀ : ℂ → ℂ} {u : ℝ → ℝ}
    (hu : ∀ s : ℝ, 0 < s → h₀ ((Real.sqrt (3 * s / c') : ℝ) : ℂ) = (u s : ℂ))
    (hcont : ContinuousOn u (Ici 0)) (hint : Integrable (radialLift 1 u)) {t : ℝ} (ht : 0 < t) :
    edgeHankel c' h₀ t = (hankelTransform 1 u t : ℂ) := by
  set x : ℝ := Real.sqrt (3 * t / c') with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have htx : t = c' * x ^ 2 / 3 := by
    rw [hx, Real.sq_sqrt (by positivity)]; field_simp
  have key := hankelContinuationW_eq_neg_hankelTransform le_rfl hc' hcont hint x
  rw [← htx] at key
  rw [hankelContinuationW_one_eq hc'.le] at key
  unfold Integration.hankelContinuation at key
  unfold edgeHankel
  have hmul : ∀ s ∈ Ioi (0 : ℝ),
      h₀ ((Real.sqrt (3 * s / c') : ℝ) : ℂ) * Complex.besselJ 0 ((4 * π * Real.sqrt (s * t) : ℝ) : ℂ) =
        (u s : ℂ) * Integration.besselI0C (4 * (π : ℂ) * Complex.I * (x : ℂ) *
          (Real.sqrt (c' * s / 3) : ℝ)) := by
    intro s hs
    rw [hu s hs, besselJ_zero_eq_besselI0C]
    congr 2
    have hst : Real.sqrt (s * t) = x * Real.sqrt (c' * s / 3) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      rw [htx]; ring_nf
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    rw [hst]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hmul]
  have : -2 * (π : ℂ) * ∫ s in Ioi (0 : ℝ), (u s : ℂ) *
      Integration.besselI0C (4 * (π : ℂ) * Complex.I * (x : ℂ) * (Real.sqrt (c' * s / 3) : ℝ)) =
      -(hankelTransform 1 u t : ℂ) := key.symm ▸ rfl
  linear_combination (-1 : ℂ) * this

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fourier_radialLift_eq_hankelTransform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radialLift_eq_hankelTransform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.hankelTransform_one_eq_edgeHankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelTransform_one_eq_edgeHankel

end FormalResearch.ModularBootstrap.Upper.Membership
