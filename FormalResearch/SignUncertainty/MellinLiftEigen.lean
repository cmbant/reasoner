module

public import FormalResearch.SignUncertainty.MellinLiftInverse
public import FormalResearch.SignUncertainty.HankelMellinIntegrable

/-!
# `O.11ak`, Hankel side: the inverse Mellin lift is a Hankel eigenfunction

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Theorem `O.11ak` (`ceo:O11ak`), `(ceo:O11ak.3)`.  For `c > 3/2`, a Mellin multiplier
`Φ` as in `MellinLiftData` whose normalised version `(2π)^z Γ(z)^{-1} Φ(z)` has the reflection `𝓜(c - z) = σ 𝓜(z)` and whose lift
`f = liftFun Φ x₀` has finite mass `∫ f ρ₀ < ∞`, the lift (with its origin value) lies in `𝒜_c^σ`.  The proof: the Mellin transform of
`𝓗_c f` on `0 < Re z < c/2 - 1/4` is `σ Φ(z)` (`mellin_hankel_fubini`, Weber's integral `hankelMellin_mul_gamma`, the Mellin transform
of `f` at `c - z` from `mellinRaw_liftFun`), equal to that of `σ f`, and the difference vanishes by Mellin uniqueness
(`mellinInv_mellin_eq`).  The origin value is `σ 𝓗_c f(0)` (continuity of `𝓗_c f`).

Status: proved, unconditional.  Not formalised here: the finiteness of the mass (the tail estimate, `MellinLiftTail`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- `(2π)^z Γ(z)^{-1} Φ(z)`, the normalised multiplier. -/
noncomputable def mellinMult (Φ : ℂ → ℂ) (z : ℂ) : ℂ := ((2 * Real.pi : ℝ) : ℂ) ^ z / Complex.Gamma z * Φ z

lemma mellinConvergent_of_re {f : ℝ → ℂ} {s s' : ℂ} (hre : s.re = s'.re) (hc : ContinuousOn f (Ioi 0))
    (hf : MellinConvergent f s) : MellinConvergent f s' := by
  unfold MellinConvergent at hf ⊢
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s' - 1) • f t) (Ioi 0) := by
    have hc1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s' - 1)) (Ioi 0) :=
      ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun t ht =>
        Complex.ofReal_mem_slitPlane.mpr ht
    exact hc1.smul hc
  refine hf.norm.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := ht
  rw [norm_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp [hre]


section

variable {c : ℝ} {Φ : ℂ → ℂ}

lemma integrableOn_abs_liftFun (h : MellinLiftData c Φ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < c) :
    IntegrableOn (fun s : ℝ => |liftFun Φ x₀ s| * s ^ (x - 1)) (Ioi 0) := by
  have hc := h.mellinConvergent hx0 hx1
  have : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((x : ℂ) - 1) • mellinInv x Φ t‖) (Ioi 0) := Integrable.norm hc
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht' : 0 < t := ht
  simp only
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', ← ofReal_liftFun h hx₀ hx₀' hx0 hx1 ht',
    Complex.norm_real, Real.norm_eq_abs]
  simp [mul_comm]

/-- The Mellin transform of `𝓗_c f` on `0 < Re z < c/2 - 1/4` is `σ Φ(z)`. -/
theorem mellin_hankel_liftFun (h : MellinLiftData c Φ) (hc : 3 / 2 < c) {σ : ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hx₀' : x₀ < c) (hsym : ∀ z : ℂ, 0 < z.re → z.re < c → mellinMult Φ ((c : ℂ) - z) = (σ : ℂ) * mellinMult Φ z)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c / 2 - 1 / 4) :
    ∫ Δ in Ioi (0 : ℝ), (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c (liftFun Φ x₀) Δ : ℂ) = (σ : ℂ) * Φ z := by
  have hc0 : 0 < c := by linarith
  have hzc : z.re < c := by linarith
  have hgc := continuousOn_liftFun h hx₀ hx₀'
  have hg : IntegrableOn (fun s : ℝ => |liftFun Φ x₀ s| * s ^ (c - 1 - z.re)) (Ioi 0) := by
    have := integrableOn_abs_liftFun h hx₀ hx₀' (x := c - z.re) (by linarith) (by linarith)
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only
    rw [show c - z.re - 1 = c - 1 - z.re by ring]
  have F := mellin_hankel_fubini hc hz0 hz1 hgc hg
  have W := hankelMellin_mul_gamma hc hz0 hz1
  have hR : ∫ s in Ioi (0 : ℝ), (liftFun Φ x₀ s : ℂ) * (s : ℂ) ^ ((c : ℂ) - 1 - z) = Φ ((c : ℂ) - z) := by
    rw [← mellinRaw_liftFun h hx₀ hx₀' (z := (c : ℂ) - z) (by simpa using (by linarith : z.re < c))
      (by simpa using hz0)]
    unfold mellinRaw
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [show (c : ℂ) - z - 1 = (c : ℂ) - 1 - z by ring]
  rw [F, hR]
  have hr : (0 : ℝ) < 2 * π := by positivity
  have hinv : ∀ w : ℂ, (1 / ((2 * π : ℝ) : ℂ)) ^ w = (((2 * π : ℝ) : ℂ) ^ w)⁻¹ := fun w => by
    rw [one_div, Complex.inv_cpow]
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  rw [hinv, hinv] at W
  have hz : (((2 * π : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hX : ((2 * π : ℝ) : ℂ) ^ z ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp [hz]
  have hY : ((2 * π : ℝ) : ℂ) ^ ((c : ℂ) - z) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp [hz]
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hGc : Complex.Gamma ((c : ℂ) - z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using hzc)
  have hs := hsym z hz0 hzc
  unfold mellinMult at hs
  set Ph := hankelMellin c z
  set a : ℂ := (((2 * π) ^ c / Real.Gamma c : ℝ) : ℂ)
  set X := ((2 * π : ℝ) : ℂ) ^ z
  set Y := ((2 * π : ℝ) : ℂ) ^ ((c : ℂ) - z)
  have hΦ : Ph * a = X⁻¹ * Complex.Gamma z * Y / Complex.Gamma ((c : ℂ) - z) := by
    rw [eq_div_iff hGc]
    calc Ph * a * Complex.Gamma ((c : ℂ) - z) = Ph * a * (Y⁻¹ * Complex.Gamma ((c : ℂ) - z)) * Y := by
          field_simp
      _ = _ := by rw [W]
  rw [hΦ]
  calc X⁻¹ * Complex.Gamma z * Y / Complex.Gamma ((c : ℂ) - z) * Φ ((c : ℂ) - z)
      = X⁻¹ * Complex.Gamma z * (Y / Complex.Gamma ((c : ℂ) - z) * Φ ((c : ℂ) - z)) := by ring
    _ = X⁻¹ * Complex.Gamma z * ((σ : ℂ) * (X / Complex.Gamma z * Φ z)) := by rw [hs]
    _ = _ := by field_simp

end


section

variable {c : ℝ} {Φ : ℂ → ℂ}

lemma mellin_liftFun_eq (h : MellinLiftData c Φ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z.re < c) :
    mellin (fun Δ : ℝ => (liftFun Φ x₀ Δ : ℂ)) z = Φ z := by
  rw [← mellinRaw_liftFun h hx₀ hx₀' hz0 hz1]
  unfold mellin mellinRaw
  refine setIntegral_congr_fun measurableSet_Ioi fun Δ _ => ?_
  simp only [smul_eq_mul]; ring

lemma mellinConvergent_liftFun (h : MellinLiftData c Φ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < c) : MellinConvergent (fun Δ : ℝ => (liftFun Φ x₀ Δ : ℂ)) s := by
  have h1 := h.mellinConvergent hs0 hs1
  have h2 : MellinConvergent (fun Δ : ℝ => (liftFun Φ x₀ Δ : ℂ)) (s.re : ℂ) := by
    unfold MellinConvergent at h1 ⊢
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [ofReal_liftFun h hx₀ hx₀' hs0 hs1 ht]
  refine mellinConvergent_of_re (by simp) ?_ h2
  exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_liftFun h hx₀ hx₀')

/-- **The Hankel transform of the lift is `σ` times the lift** on `(0, ∞)`. -/
theorem besselHankelTransform_liftFun (h : MellinLiftData c Φ) (hc : 3 / 2 < c) {σ : ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hx₀' : x₀ < c) (hsym : ∀ z : ℂ, 0 < z.re → z.re < c → mellinMult Φ ((c : ℂ) - z) = (σ : ℂ) * mellinMult Φ z)
    (hint : IntegrableOn (fun Δ => liftFun Φ x₀ Δ * hankelRho0 c Δ) (Ioi 0)) {Δ : ℝ} (hΔ : 0 < Δ) :
    besselHankelTransform c (liftFun Φ x₀) Δ = σ * liftFun Φ x₀ Δ := by
  have hc0 : 0 < c := by linarith
  set f₀ := liftFun Φ x₀ with hf₀
  set Ĝ := besselHankelTransform c f₀ with hĜ
  have hĜc : Continuous Ĝ := besselHankelTransform_continuous (by linarith) hint
  set x : ℝ := (c / 2 - 1 / 4) / 2 with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hx1 : x < c / 2 - 1 / 4 := by rw [hx]; linarith
  have hxc : x < c := by linarith
  set hC : ℝ → ℂ := fun t => (Ĝ t : ℂ) - (σ : ℂ) * (f₀ t : ℂ) with hhC
  have hgc := continuousOn_liftFun h hx₀ hx₀'
  have hintG : ∀ y : ℝ, MellinConvergent (fun t : ℝ => (Ĝ t : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I) := fun y => by
    have hz0 : 0 < (((x : ℂ) + (y : ℂ) * Complex.I)).re := by simpa using hx0
    have hz1 : (((x : ℂ) + (y : ℂ) * Complex.I)).re < c / 2 - 1 / 4 := by simpa using hx1
    have hg : IntegrableOn (fun s : ℝ => |f₀ s| * s ^ (c - 1 - (((x : ℂ) + (y : ℂ) * Complex.I)).re)) (Ioi 0) := by
      have := integrableOn_abs_liftFun h hx₀ hx₀' (x := c - x) (by linarith) (by linarith)
      refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [show c - x - 1 = c - 1 - x by ring]
    have := integrableOn_mellin_hankel_outer hc hz0 hz1 hgc hg
    unfold MellinConvergent
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]; rfl
  have hmG : ∀ y : ℝ, mellin (fun t : ℝ => (Ĝ t : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I) =
      (σ : ℂ) * Φ ((x : ℂ) + (y : ℂ) * Complex.I) := fun y => by
    have hz0 : 0 < (((x : ℂ) + (y : ℂ) * Complex.I)).re := by simpa using hx0
    have hz1 : (((x : ℂ) + (y : ℂ) * Complex.I)).re < c / 2 - 1 / 4 := by simpa using hx1
    rw [← mellin_hankel_liftFun h hc hx₀ hx₀' hsym hz0 hz1]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]; rfl
  have hmh : ∀ y : ℝ, mellin hC ((x : ℂ) + (y : ℂ) * Complex.I) = 0 := fun y => by
    have hz0 : 0 < (((x : ℂ) + (y : ℂ) * Complex.I)).re := by simpa using hx0
    have hz1 : (((x : ℂ) + (y : ℂ) * Complex.I)).re < c := by simpa using hxc
    have hmf := mellin_liftFun_eq h hx₀ hx₀' hz0 hz1
    have hcf := mellinConvergent_liftFun h hx₀ hx₀' hz0 hz1
    have hcG := hintG y
    have e : mellin hC ((x : ℂ) + (y : ℂ) * Complex.I) =
        mellin (fun t : ℝ => (Ĝ t : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I) -
          (σ : ℂ) * mellin (fun t : ℝ => (f₀ t : ℂ)) ((x : ℂ) + (y : ℂ) * Complex.I) := by
      unfold mellin
      have hcf' : IntegrableOn (fun t : ℝ => (σ : ℂ) * ((t : ℂ) ^ ((x : ℂ) + (y : ℂ) * Complex.I - 1) • (f₀ t : ℂ))) (Ioi 0) :=
        Integrable.const_mul hcf (σ : ℂ)
      rw [← integral_const_mul, ← integral_sub hcG hcf']
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hhC, smul_eq_mul]; ring
    rw [e, hmG y, hmf]; ring
  have hconv : MellinConvergent hC (x : ℂ) := by
    have h1 := hintG 0
    have h2 := mellinConvergent_liftFun h hx₀ hx₀' (s := (x : ℂ)) (by simpa using hx0) (by simpa using hxc)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h1
    have := h1.sub (h2.const_smul (σ : ℂ))
    unfold MellinConvergent at this ⊢
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hhC, smul_eq_mul, Pi.sub_apply]; ring
  have hvert : Complex.VerticalIntegrable (mellin hC) x := by
    unfold Complex.VerticalIntegrable
    simp only [hmh]
    exact integrable_zero _ _ _
  have hcts : ContinuousAt hC Δ := by
    have h1 : ContinuousAt (fun t : ℝ => (Ĝ t : ℂ)) Δ := Complex.continuous_ofReal.continuousAt.comp hĜc.continuousAt
    have h2 : ContinuousAt (fun t : ℝ => (f₀ t : ℂ)) Δ :=
      Complex.continuous_ofReal.continuousAt.comp (hgc.continuousAt (Ioi_mem_nhds hΔ))
    exact h1.sub (continuousAt_const.mul h2)
  have := mellinInv_mellin_eq x hC hΔ hconv hvert hcts
  have hz : mellinInv x (mellin hC) Δ = 0 := by
    unfold mellinInv
    simp [hmh]
  rw [hz] at this
  have h3 : (Ĝ Δ : ℂ) - (σ : ℂ) * (f₀ Δ : ℂ) = 0 := this.symm
  have h4 : Ĝ Δ - σ * f₀ Δ = 0 := by exact_mod_cast h3
  linarith

end


section

variable {c : ℝ} {Φ : ℂ → ℂ}

/-- **The Mellin lift is a Hankel eigenfunction** (`ceo:O11ak`, `(ceo:O11ak.3)`, first two claims), given the reflection symmetry
of the normalised multiplier and the finiteness of the mass `∫ f ρ₀`.  The function is the lift on `(0, ∞)`; its value at `0` is
`σ ∫ f ρ₀` (`= σ 𝓗_c f(0)`). -/
theorem exists_isHankelEigenfn_of_lift (h : MellinLiftData c Φ) (hc : 3 / 2 < c) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c)
    (hsym : ∀ z : ℂ, 0 < z.re → z.re < c → mellinMult Φ ((c : ℂ) - z) = (σ : ℂ) * mellinMult Φ z)
    (hint : IntegrableOn (fun Δ => liftFun Φ x₀ Δ * hankelRho0 c Δ) (Ioi 0)) :
    ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧ (∀ Δ : ℝ, 0 < Δ → f Δ = liftFun Φ x₀ Δ) ∧
      f 0 = σ * ∫ Δ in Ioi (0 : ℝ), liftFun Φ x₀ Δ * hankelRho0 c Δ := by
  have hc0 : 0 < c := by linarith
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set f₀ := liftFun Φ x₀ with hf₀
  set Ĝ := besselHankelTransform c f₀ with hĜ
  have hĜc : Continuous Ĝ := besselHankelTransform_continuous (by linarith) hint
  have hĜ0 : Ĝ 0 = ∫ Δ in Ioi (0 : ℝ), f₀ Δ * hankelRho0 c Δ := besselHankelTransform_zero hc0 f₀
  have hG : ∀ Δ : ℝ, 0 < Δ → Ĝ Δ = σ * f₀ Δ := fun Δ hΔ =>
    besselHankelTransform_liftFun h hc hx₀ hx₀' hsym hint hΔ
  let f : ℝ → ℝ := fun Δ => if 0 < Δ then f₀ Δ else σ * Ĝ 0
  have hfG : ∀ Δ : ℝ, 0 ≤ Δ → f Δ = σ * Ĝ Δ := by
    intro Δ hΔ
    rcases hΔ.eq_or_lt with rfl | hpos
    · simp [f]
    · simp only [f, if_pos hpos, hG Δ hpos]
      linear_combination (-f₀ Δ) * hσσ
  have hfΔ : ∀ Δ : ℝ, 0 < Δ → f Δ = f₀ Δ := fun Δ hΔ => by simp [f, hΔ]
  refine ⟨f, ⟨?_, ?_, ?_⟩, hfΔ, ?_⟩
  · exact (continuousOn_const.mul hĜc.continuousOn).congr fun Δ hΔ => hfG Δ hΔ
  · exact hint.congr_fun (fun Δ hΔ => by rw [hfΔ Δ hΔ]) measurableSet_Ioi
  · intro Δ hΔ
    have hEq : besselHankelTransform c f = Ĝ := by
      funext Δ'
      unfold besselHankelTransform
      refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
      rw [hfΔ s hs]
    rw [hEq]
    rcases hΔ.eq_or_lt with rfl | hpos
    · have := hfG 0 le_rfl
      have h0 : f 0 = σ * Ĝ 0 := this
      rw [h0]; linear_combination (-Ĝ 0) * hσσ
    · rw [hfΔ Δ hpos, hG Δ hpos]
  · have := hfG 0 le_rfl
    rw [this, hĜ0]

end


/-- info: 'FormalResearch.SignUncertainty.mellin_hankel_liftFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.mellin_hankel_liftFun

/-- info: 'FormalResearch.SignUncertainty.besselHankelTransform_liftFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.besselHankelTransform_liftFun

/-- info: 'FormalResearch.SignUncertainty.exists_isHankelEigenfn_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.exists_isHankelEigenfn_of_lift

end FormalResearch.SignUncertainty
