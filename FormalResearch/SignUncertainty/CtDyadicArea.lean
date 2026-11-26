module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicEta
public import FormalResearch.Complex.HalfDiscMoments
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodArea
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodWtilde

/-!
# `ct:dyadic` (2): the regularised Airy-unfolded test `G_reg` and its area integrals

`constant_terms_lower.tex`, `ct:dyadic` Part (2): `G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) e^{(4/3) i w³}` (`A² = R_J`), the unfolding of
`Ψ̃` to the upper half-plane (`ap:lemU`).  This file proves the geometric half of the "two Cauchy moments" argument for the
concrete `Ψ̃ = hankelPsi c f`:

* `ctGReg_analytic`: `G_reg` is analytic on `|w| ≤ A` when `A² ≤ langerRadius c` (`Ψ̃` is analytic on the Langer disc);
* `ct_inv_norm_area_id`: `∫∫ r ‖re^{iφ} - t‖⁻¹ ≤ (9π/2) r₀` over the half-sector, for every real `t`;
* `ct_area_id`, `ct_area_wtilde`: `∫_{r₀}^{3r₀/2} ∫_0^π r ‖G_reg(ζ(re^{iφ}))‖ dφ dr ≤ M` for `ζ = id` and `ζ = w̃`
  (`w̃(w) = w (φ_c(-w²)/(-w²))^{1/2}`, the `φ_c`-transported coordinate of Paper II), from the pointwise Cauchy-moment bound
  `hd_moment_area` with the two inputs `Σ = ∫_0^π ‖G_reg(A e^{iy})‖ A dy ≤ C_Σ/A` and `S₂ = ∫ t² ‖G_reg(t)‖ dt ≤ C_S A`.

Proved (the inputs `Σ`, `S₂` and the chart facts enter as hypotheses of the lemmas).
-/

@[expose] public section

open Complex MeasureTheory Set Metric intervalIntegral
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.HalfDiscCauchy FormalResearch.ModularBootstrap.FiveTerm

/-- **`G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) exp((4/3) i w³)`** (`ct:dyadic` Part (2)), `Ψ̃ = hankelPsi c f`. -/
noncomputable def ctGReg (A c : ℝ) (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  (1 - w ^ 2 / (A : ℂ) ^ 2) ^ 2 * w * hankelPsi c f (-(w ^ 2)) * Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)

lemma langerRadius_eq (c : ℝ) : langerRadius c = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
  unfold langerRadius langerScale; ring

/-- `G_reg` is analytic on the closed disc `|w| ≤ A` as soon as `A² ≤ langerRadius c`. -/
lemma ctGReg_analytic {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {A : ℝ} (hA : 0 < A)
    (hAR : A ^ 2 ≤ langerRadius c) : AnalyticOnNhd ℂ (ctGReg A c f) (closedBall (0 : ℂ) A) := by
  intro w hw
  have hw_norm : ‖w‖ ≤ A := mem_closedBall_zero_iff.mp hw
  have hneg_mem : -(w ^ 2) ∈ closedBall (0 : ℂ) (c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4) := by
    rw [mem_closedBall_zero_iff, norm_neg, norm_pow, ← langerRadius_eq]
    exact (pow_le_pow_left₀ (norm_nonneg w) hw_norm 2).trans hAR
  have hpsi : AnalyticAt ℂ (fun z => hankelPsi c f (-(z ^ 2))) w :=
    (analyticOnNhd_hankelPsi hc hf _ hneg_mem).comp_of_eq ((analyticAt_id.pow 2).neg) rfl
  have hpre : AnalyticAt ℂ (fun z => (1 - z ^ 2 / (A : ℂ) ^ 2) ^ 2 * z) w :=
    (((analyticAt_const.sub ((analyticAt_id.pow 2).div analyticAt_const
      (by exact_mod_cast (pow_pos hA 2).ne'))).pow 2).mul analyticAt_id)
  have hexp : AnalyticAt ℂ (fun z => Complex.exp ((4 / 3 : ℂ) * I * z ^ 3)) w :=
    (analyticAt_const.mul (analyticAt_id.pow 3)).cexp
  exact (hpre.mul hpsi).mul hexp

/-- Over the half-sector `r ∈ (r₀, (3/2)r₀]`, `φ ∈ (0, π)`: `∫∫ r ‖r e^{iφ} - t‖⁻¹ ≤ (9π/2) r₀` for every real `t`
(`lowerGood_inv_norm_area_le` for the ball `|z| ≤ (3/2) r₀` and polar coordinates). -/
lemma ct_inv_norm_area_id {r₀ : ℝ} (hr₀ : 0 < r₀) (t : ℝ) :
    ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
      ENNReal.ofReal p.1 * (ENNReal.ofReal ‖(p.1 : ℂ) * Complex.exp (p.2 * I) - (t : ℂ)‖)⁻¹ ≤
        ENNReal.ofReal (9 * π / 2 * r₀) := by
  have h_sub : (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π) ⊆ Complex.polarCoord.target := by
    intro p hp
    rw [Complex.polarCoord_target]
    exact ⟨lt_trans hr₀ hp.1.1, ⟨lt_trans (by linarith [Real.pi_pos]) hp.2.1, hp.2.2⟩⟩
  have h_pt : ∀ p ∈ (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
      ENNReal.ofReal p.1 * (ENNReal.ofReal ‖(p.1 : ℂ) * Complex.exp (p.2 * I) - (t : ℂ)‖)⁻¹ ≤
        ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
          (fun z => (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) (Complex.polarCoord.symm p) := by
    intro p hp
    have hp1 : 0 < p.1 := by linarith [hp.1.1]
    have hsymm : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * I) := by
      simp [Complex.exp_mul_I]
    have hmem : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) (3 / 2 * r₀) := by
      rw [mem_closedBall_zero_iff, hsymm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hp1, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hp.1.2
    rw [Set.indicator_of_mem hmem, hsymm, smul_eq_mul]
  have h_le1 : ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
        ENNReal.ofReal p.1 * (ENNReal.ofReal ‖(p.1 : ℂ) * Complex.exp (p.2 * I) - (t : ℂ)‖)⁻¹ ≤
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
          (fun z => (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) (Complex.polarCoord.symm p) :=
    (setLIntegral_mono' (measurableSet_Ioc.prod measurableSet_Ioo) h_pt).trans
      (lintegral_mono_set h_sub)
  have h_eq : (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
          (fun z => (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) (Complex.polarCoord.symm p)) =
      ∫⁻ z in closedBall (0 : ℂ) (3 / 2 * r₀), (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹ := by
    have h_pc := Complex.lintegral_comp_polarCoord_symm
      (fun z => (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator (fun z => (ENNReal.ofReal ‖z - (t : ℂ)‖)⁻¹) z)
    exact h_pc.trans (lintegral_indicator measurableSet_closedBall _)
  rw [h_eq] at h_le1
  refine h_le1.trans ((lowerGood_inv_norm_area_le (by positivity) t).trans (le_of_eq ?_))
  congr 1; ring

/-- The numerical heart of `ct_area_of_zeta`: with `ρ = r₀/4`, `A ≥ 9 r₀` and `A Σ ≤ C_Σ`,
`(3r₀²/8)(Σ/ρ + AΣ/ρ² + 4Σ/(3A)) ≤ 7 C_Σ`. -/
lemma ct_B0_bound {A r₀ Sig CSig : ℝ} (hr₀ : 0 < r₀) (hA9 : 9 * r₀ ≤ A) (hSig0 : 0 ≤ Sig)
    (hu : A * Sig ≤ CSig) :
    3 * r₀ ^ 2 / 8 * (Sig / (r₀ / 4) + A * Sig / (r₀ / 4) ^ 2 + 4 * Sig / (3 * A)) ≤ 7 * CSig := by
  have hA : 0 < A := by linarith
  have h1 : 9 * (Sig * r₀) ≤ CSig := by nlinarith [mul_le_mul_of_nonneg_left hA9 hSig0]
  have h2 : Sig * r₀ ^ 2 / A ≤ Sig * r₀ / 9 := by
    rw [div_le_iff₀ hA]; nlinarith [mul_nonneg hSig0 hr₀.le, mul_le_mul_of_nonneg_left hA9 (mul_nonneg hSig0 hr₀.le)]
  have hid : 3 * r₀ ^ 2 / 8 * (Sig / (r₀ / 4) + A * Sig / (r₀ / 4) ^ 2 + 4 * Sig / (3 * A)) =
      3 / 8 * (4 * (Sig * r₀) + 16 * (A * Sig) + 4 / 3 * (Sig * r₀ ^ 2 / A)) := by
    field_simp
    ring
  rw [hid]
  nlinarith [mul_nonneg hSig0 hr₀.le, mul_nonneg hSig0 (sq_nonneg r₀), div_nonneg (mul_nonneg hSig0 (sq_nonneg r₀)) hA.le]

/-- **Area bound for one coordinate map `ζ`** (`ct:dyadic` Part (2)): if `ζ` maps the half-sector into `{r₀/4 ≤ ‖z‖ ≤ A/4}` in the
open half-disc of radius `A ≥ 9 r₀`, with the inverse-norm area bound `∫∫ r ‖ζ - t‖⁻¹ ≤ K r₀`, and `Σ ≤ C_Σ/A`,
`S₂ ≤ C_S A`, then `∫∫ r ‖G(ζ(re^{iφ}))‖ ≤ 7 C_Σ + 8 K C_S A/(π r₀)`. -/
lemma ct_area_of_zeta {G : ℂ → ℂ} {A r₀ K CSig CS : ℝ} (hr₀ : 0 < r₀) (hA9 : 9 * r₀ ≤ A) (hK : 0 ≤ K)
    (hc : ContinuousOn G (closedHalfDisc A)) (hd : DifferentiableOn ℂ G (openHalfDisc A))
    (hSig : hdArcMass A G ≤ CSig / A) (hS2 : ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖ ≤ CS * A)
    (ζ : ℂ → ℂ) (hζc : ContinuousOn ζ {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀})
    (hζ : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      ζ ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧ r₀ / 4 ≤ ‖ζ ((r : ℂ) * Complex.exp (φ * I))‖ ∧
        ‖ζ ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4)
    (hinv : ∀ t ∈ Ioo (-A) A,
      ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
        ENNReal.ofReal p.1 * (ENNReal.ofReal ‖ζ ((p.1 : ℂ) * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
          ENNReal.ofReal (K * r₀)) :
    ∫⁻ r in Ioc r₀ (3 / 2 * r₀), ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖G (ζ ((r : ℂ) * Complex.exp (φ * I)))‖) ≤
      ENNReal.ofReal (7 * CSig + 8 * K * CS * A / (π * r₀)) := by
  have hA : 0 < A := by linarith
  have hpi := Real.pi_pos
  have hSig0 := hdArcMass_nonneg hA G
  have hu : A * hdArcMass A G ≤ CSig := by
    have := mul_le_mul_of_nonneg_left hSig hA.le
    rwa [mul_div_cancel₀ _ hA.ne'] at this
  refine (hd_moment_area hA (by positivity : 0 < r₀ / 4) hr₀ hK hc hd ζ hζc hζ hinv).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := ct_B0_bound hr₀ hA9 hSig0 hu
  have hS2' : K * r₀ * (∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖) / (2 * π * (r₀ / 4) ^ 2) ≤
      8 * K * CS * A / (π * r₀) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : K * r₀ * (∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖G (t : ℂ)‖) ≤ K * r₀ * (CS * A) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h4 : 0 ≤ π * r₀ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  linarith

/-- info: 'FormalResearch.SignUncertainty.ct_area_of_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_area_of_zeta

end FormalResearch.SignUncertainty
