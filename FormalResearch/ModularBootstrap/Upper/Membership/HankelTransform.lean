module

public import FormalResearch.ModularBootstrap.Upper.Membership.Vacuum
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeRepresentationP
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The Hankel transform `𝓗_w` as the radial Fourier transform

`hankelTransform w u` is the real radial profile of the Fourier transform of `radialLift w u`
(radial symmetry and reality of `𝓕 (radialLift w u)` are proved here from linear-isometry
invariance, Mathlib's `fourier_comp_linearIsometry`), so that
`𝓕 (radialLift w u) = radialLift w (hankelTransform w u)` (`fourier_radialLift_eq_hankelTransform`).
At weight `w = p + 1` it is the order-`p` Hankel transform `2π ∫₀^∞ u(s) (s/t)^{p/2} J_p(4π √(s t)) ds`
(`hankelTransformOrd_eq_hankelTransform`, the link of `fw:s1`), and for the comb profile `u(s) = h₀(√(3s/c'))`
it is `edgeHankelP p c' h₀` (`hankelTransform_eq_edgeHankelP`), which connects Lemma `SD_H`/`SD_G`/`SD_V`
and `FW-SD` to the membership statement; `w = 1` is `hankelTransform_one_eq_edgeHankel` (`edgeHankel`).

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

/-! ### Order `p`: `hankelTransform (p+1)` is the order-`p` Hankel transform `𝓗_{p+1}` -/

/-- **Link lemma**: for `u` continuous on `[0, ∞)` with integrable radial lift on `ℝ^{2(p+1)}`, the Fourier
profile `hankelTransform (p+1) u` is the order-`p` Bessel transform `hankelTransformOrd p u`
(`(𝓗_{p+1} u)(t) = 2π ∫₀^∞ u(s) (s/t)^{p/2} J_p(4π√(s t)) ds`, `fw:s1`), for `t > 0`.  Both are the Hankel
formula `fourier_radialLift_apply_eq` with the kernel `kernelKC (p+1)` identified with `besselKern p`. -/
theorem hankelTransformOrd_eq_hankelTransform (p : ℕ) {u : ℝ → ℝ} (hcont : ContinuousOn u (Ici 0))
    (hint : Integrable (radialLift (p + 1) u)) {t : ℝ} (ht : 0 < t) :
    hankelTransformOrd p (fun s => (u s : ℂ)) t = (hankelTransform (p + 1) u t : ℂ) := by
  have key := hankelContinuationW_eq_neg_hankelTransform (w := p + 1) (by omega) (c' := 3)
    (by norm_num) hcont hint (Real.sqrt t)
  have hb : (3 : ℝ) * Real.sqrt t ^ 2 / 3 = t := by rw [Real.sq_sqrt ht.le]; ring
  rw [hb] at key
  unfold hankelContinuationW at key
  have hker : ∀ s ∈ Ioi (0 : ℝ),
      (u s : ℂ) * kernelKC (p + 1) (-((3 : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) ^ 2 / 3) (s : ℂ) =
        (u s : ℂ) * besselKern p s t := by
    intro s _
    congr 1
    unfold kernelKC besselKern
    have hsq : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by
      exact_mod_cast Real.sq_sqrt ht.le
    simp only [Nat.add_sub_cancel]
    congr 2
    rw [hsq]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hker] at key
  rw [hankelTransformOrd_eq_kern p _ ht]
  linear_combination (-1 : ℂ) * key

/-- **Order-`p` link**: if `h₀(√(3s/c')) = u(s)` for `s > 0` with `u` real, continuous on `[0, ∞)` with
integrable radial lift on `ℝ^{2(p+1)}`, then `edgeHankelP p c' h₀ t = ĥ(t)` for `t > 0`, where
`ĥ = hankelTransform (p+1) u`. -/
theorem hankelTransform_eq_edgeHankelP (p : ℕ) {c' : ℝ} {h₀ : ℂ → ℂ} {u : ℝ → ℝ}
    (hu : ∀ s : ℝ, 0 < s → h₀ ((Real.sqrt (3 * s / c') : ℝ) : ℂ) = (u s : ℂ))
    (hcont : ContinuousOn u (Ici 0)) (hint : Integrable (radialLift (p + 1) u)) {t : ℝ} (ht : 0 < t) :
    edgeHankelP p c' h₀ t = (hankelTransform (p + 1) u t : ℂ) := by
  rw [← hankelTransformOrd_eq_hankelTransform p hcont hint ht]
  unfold edgeHankelP hankelTransformOrd
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  simp only [hu s hs]

/-- **Order-zero link**: if `h₀(√(3s/c')) = u(s)` for `s > 0` with `u` real, continuous on `[0, ∞)`
with integrable radial lift on `ℝ²`, then `edgeHankel c' h₀ t = ĥ(t)` for `t > 0`,
where `ĥ = hankelTransform 1 u` (`edgeHankel` is the `J₀` form `2π ∫₀^∞ h₀ J₀(4π√(st)) ds`). -/
theorem hankelTransform_one_eq_edgeHankel {c' : ℝ} (_hc' : 0 < c') {h₀ : ℂ → ℂ} {u : ℝ → ℝ}
    (hu : ∀ s : ℝ, 0 < s → h₀ ((Real.sqrt (3 * s / c') : ℝ) : ℂ) = (u s : ℂ))
    (hcont : ContinuousOn u (Ici 0)) (hint : Integrable (radialLift 1 u)) {t : ℝ} (ht : 0 < t) :
    edgeHankel c' h₀ t = (hankelTransform 1 u t : ℂ) := by
  rw [← edgeHankelP_zero]
  exact hankelTransform_eq_edgeHankelP 0 hu hcont hint ht

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fourier_radialLift_eq_hankelTransform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radialLift_eq_hankelTransform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.hankelTransform_one_eq_edgeHankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelTransform_one_eq_edgeHankel

end FormalResearch.ModularBootstrap.Upper.Membership
