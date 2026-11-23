module

public import FormalResearch.ModularBootstrap.Crossing.Setup
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Radial Fourier inversion and Fourier-odd membership

Formalises the "Involution" step of `FW-M` (`fw:FWM`, item 2, `upper_transfer.tex`) and of
Lemma `K7` (`cmb:K7`, `comb_estimates.tex`, "Membership"): a real profile `h` whose radial lift
`x ↦ h (‖x‖² / 2)` is continuous and integrable on `ℝ^{2w}` and has Fourier transform equal to
the radial lift of a real profile `ĥ` with integrable lift satisfies

`𝓕 (radialLift w ĥ) = radialLift w h`   (`fourier_radialLift_involutive`),

and `g = ½ (h - ĥ)` is Fourier-odd (`pairOdd_fourier_odd`), so it lies in the Hankel-odd test
class once the Cardy-weighted integrability holds (`pairOdd_testClass`).

Radial Fourier inversion on `ℝ^{2w}` is Mathlib's `Continuous.fourierInv_fourier_eq` together with
the evenness of a radial function; no unproved input remains.

Everything is proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing

/-! ### Radial lifts are continuous and even -/

lemma continuous_radialLift {w : ℕ} {h : ℝ → ℝ} (hcont : ContinuousOn h (Ici 0)) :
    Continuous (radialLift w h) :=
  Complex.continuous_ofReal.comp
    (hcont.comp_continuous ((continuous_norm.pow 2).div_const 2) fun v =>
      mem_Ici.mpr (by positivity))

lemma radialLift_neg {w : ℕ} (h : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin (2 * w))) :
    radialLift w h (-x) = radialLift w h x := by
  simp [radialLift]

/-! ### Linearity of the Fourier transform on integrable functions -/

lemma fourier_sub_fn {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f₁ f₂ : V → ℂ} (h₁ : Integrable f₁) (h₂ : Integrable f₂) :
    𝓕 (fun x => f₁ x - f₂ x) = 𝓕 f₁ - 𝓕 f₂ := by
  ext w
  simp only [Real.fourier_eq, Pi.sub_apply]
  have hi1 : Integrable (fun v : V => 𝐞 (-⟪v, w⟫) • f₁ v) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner w).2 h₁
  have hi2 : Integrable (fun v : V => 𝐞 (-⟪v, w⟫) • f₂ v) :=
    (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner w).2 h₂
  simp_rw [smul_sub]
  exact integral_sub hi1 hi2

lemma fourier_smul_fn' {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (c : ℂ) (f : V → ℂ) :
    𝓕 (fun x => c • f x) = c • 𝓕 f := by
  ext w
  simp only [Real.fourier_eq, Pi.smul_apply]
  simp_rw [smul_comm _ c]
  exact integral_smul c _

/-! ### The pair `(h, ĥ)` and radial Fourier inversion -/

/-- A Fourier pair of radial profiles at weight `w` (`ℝ^{2w}`, `t = ‖x‖² / 2`): `h`, `ĥ` are real
profiles with continuous integrable radial lifts and `𝓕 (radialLift w h) = radialLift w ĥ`.
Here `ĥ` is the order-`(w - 1)` Hankel transform `𝓗_w h` of the bootstrap
(`fw:FWM`, `cmb:K7`) in the normalisation of `Crossing.TestClass`. -/
structure RadialFourierPair (w : ℕ) (h ĥ : ℝ → ℝ) : Prop where
  cont : ContinuousOn h (Ici 0)
  cont' : ContinuousOn ĥ (Ici 0)
  int : Integrable (radialLift w h)
  int' : Integrable (radialLift w ĥ)
  transform : 𝓕 (radialLift w h) = radialLift w ĥ

/-- **Radial Fourier inversion on `ℝ^{2w}`** (`fw:FWM` item 2, `cmb:K7` "Membership"): for a
Fourier pair, `𝓗_w (𝓗_w h) = h`, i.e. `𝓕 (radialLift w ĥ) = radialLift w h`. -/
theorem fourier_radialLift_involutive {w : ℕ} {h ĥ : ℝ → ℝ} (hp : RadialFourierPair w h ĥ) :
    𝓕 (radialLift w ĥ) = radialLift w h := by
  have hcont := continuous_radialLift (w := w) hp.cont
  have hinv := hcont.fourierInv_fourier_eq hp.int (by rw [hp.transform]; exact hp.int')
  rw [hp.transform] at hinv
  ext x
  have hx := congrFun hinv (-x)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at hx
  rw [hx, radialLift_neg]

/-- The pair is symmetric: `(ĥ, h)` is again a Fourier pair. -/
theorem RadialFourierPair.symm {w : ℕ} {h ĥ : ℝ → ℝ} (hp : RadialFourierPair w h ĥ) :
    RadialFourierPair w ĥ h where
  cont := hp.cont'
  cont' := hp.cont
  int := hp.int'
  int' := hp.int
  transform := fourier_radialLift_involutive hp

/-! ### `g = ½ (h - ĥ)` is Fourier-odd -/

/-- The odd combination `g = ½ (h - ĥ)` of `K7` / `FW-M`. -/
noncomputable def pairOdd (h ĥ : ℝ → ℝ) (t : ℝ) : ℝ := (h t - ĥ t) / 2

lemma radialLift_pairOdd (w : ℕ) (h ĥ : ℝ → ℝ) :
    radialLift w (pairOdd h ĥ) =
      fun x => (1 / 2 : ℂ) • (radialLift w h x - radialLift w ĥ x) := by
  ext x; simp [radialLift, pairOdd]; ring

theorem pairOdd_cont {w : ℕ} {h ĥ : ℝ → ℝ} (hp : RadialFourierPair w h ĥ) :
    ContinuousOn (pairOdd h ĥ) (Ici 0) :=
  (hp.cont.sub hp.cont').div_const 2

theorem pairOdd_int_lift {w : ℕ} {h ĥ : ℝ → ℝ} (hp : RadialFourierPair w h ĥ) :
    Integrable (radialLift w (pairOdd h ĥ)) := by
  rw [radialLift_pairOdd]
  exact (hp.int.sub hp.int').smul (1 / 2 : ℂ)

/-- `𝓗_w g = -g` for `g = ½ (h - ĥ)`: Fourier-oddness of the radial lift. -/
theorem pairOdd_fourier_odd {w : ℕ} {h ĥ : ℝ → ℝ} (hp : RadialFourierPair w h ĥ) :
    𝓕 (radialLift w (pairOdd h ĥ)) = -(radialLift w (pairOdd h ĥ)) := by
  rw [radialLift_pairOdd, fourier_smul_fn', fourier_sub_fn hp.int hp.int', hp.transform,
    fourier_radialLift_involutive hp]
  ext x
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Membership of `g = ½ (h - ĥ)` in the Hankel-odd test class `Ā`, given Cardy-weighted
integrability of `h` and `ĥ` (`fw:FWM` items 1-2, `cmb:K7` "Membership"). -/
theorem pairOdd_testClass {prob : FixedWeightProblem} {a : ℝ} {h ĥ : ℝ → ℝ}
    (hp : RadialFourierPair prob.w h ĥ)
    (hV : IntegrableOn (fun t => |h t| * prob.cardyV a t) (Ioi 0))
    (hV' : IntegrableOn (fun t => |ĥ t| * prob.cardyV a t) (Ioi 0))
    (hV0 : ∀ t, 0 ≤ t → 0 ≤ prob.cardyV a t) :
    TestClass prob a (pairOdd h ĥ) where
  cont := pairOdd_cont hp
  int_lift := pairOdd_int_lift hp
  fourier_odd := pairOdd_fourier_odd hp
  int_cardy := by
    have hmeas : AEStronglyMeasurable (fun t => |pairOdd h ĥ t| * prob.cardyV a t)
        (volume.restrict (Ioi 0)) :=
      (((pairOdd_cont hp).abs.mono Ioi_subset_Ici_self).mul
        (continuous_cardyV prob a).continuousOn).aestronglyMeasurable measurableSet_Ioi
    refine ((hV.add hV').const_mul (1 / 2 : ℝ)).mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    have hv := hV0 t (mem_Ioi.mp ht).le
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hv)]
    have habs : |pairOdd h ĥ t| ≤ (|h t| + |ĥ t|) / 2 := by
      unfold pairOdd
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
    calc |pairOdd h ĥ t| * prob.cardyV a t ≤ (|h t| + |ĥ t|) / 2 * prob.cardyV a t :=
          mul_le_mul_of_nonneg_right habs hv
      _ = 1 / 2 * (|h t| * prob.cardyV a t + |ĥ t| * prob.cardyV a t) := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fourier_radialLift_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_radialLift_involutive

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.pairOdd_testClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairOdd_testClass

end FormalResearch.ModularBootstrap.Upper.Membership
