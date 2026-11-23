module

public import FormalResearch.SignUncertainty.HermiteBiehlerUniq
public import FormalResearch.Analysis.Scheffe
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Hankel Threshold Rigidity, Hardy–Mellin Intertwiner, Active Origin Constraint, and Sign Separation

Formalizes `CFT/sign_uncertainty/paper/general_theorems.tex` (PR 240, commit `c3d8c90fe`):

* **Section 1:** Shared Hankel constants (`hankelBeta1`, `hankelRho0`, `hankelMass`,
  `hankelWindowProfile`) and linear change-of-variables lemmas.
* **Section 2 (Theorem 7.5 / `gt:7.5`):** All-level Hermite–Biehler Airy-scale lower bound
  (`radial_rigidity_liminf`), locally uniform & `L¹` profile rigidity (`radial_rigidity_profile`),
  and origin vanishing (`radial_rigidity_origin`), reusing `HermiteBiehlerUniq` and `Analysis.Scheffe`,
  with a concrete non-vacuity witness (`radialRigidityPackage_nonvacuous`).
* **Section 3 (Proposition 7.9a / `gt:7.9a`):** Hardy–Mellin intertwiner `(ℐ_c f)(Δ)` mapping
  `𝒜_c^{-1}` injectively into `𝒜_c^{+1}`, preserving feasibility (`T_c^{+1} ≤ T_c^{-1}`,
  `A_+(d) ≤ A_-(d)` for `d ≥ 4`), with an exact `c = 5 / 2` Bessel `J_{3/2}` non-vacuity witness.
* **Section 4 (Proposition 7.9b / `gt:7.9b`):** Explicit odd Laguerre mode `oddLaguerreMode`,
  `active_origin_constraint`, and constrained/unconstrained infimum equality for `T_c^{-1} > c / (4π)`.
* **Section 5 (Theorem 7.9c / `gt:7.9c`):** `integral_linear_exp_tail_lower`, Langer `C¹` transport
  reduction, `sign_separation_liminf` (`limsup (T_c^{+1} - T_c^{-1}) ≤ -2 / π²`), integer
  `A_+(d) - A_-(d)` and `κ_{+1} - κ_{-1}` corollaries, plus `sign_separation_nonvacuous`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis

/-! ### Section 1: Shared Hankel Constants, Density, and Airy Window Profile -/

/-- Hankel Airy scaling constant `β₁ = (π² √3)^{2/3}`. -/
noncomputable def hankelBeta1 : ℝ := (π ^ 2 * √3) ^ (2 / 3 : ℝ)

lemma hankelBeta1_pos : 0 < hankelBeta1 := by
  unfold hankelBeta1; positivity

lemma hankelBeta1_rpow_three_halves : hankelBeta1 ^ (3 / 2 : ℝ) = π ^ 2 * √3 := by
  unfold hankelBeta1
  rw [← Real.rpow_mul (by positivity)]
  norm_num

/-- Hankel radial weight `ρ₀(c, Δ) = (2π)^c / Γ(c) · Δ^{c - 1}`. -/
noncomputable def hankelRho0 (c Δ : ℝ) : ℝ :=
  (2 * π) ^ c / Real.Gamma c * Δ ^ (c - 1)

lemma hankelRho0_pos {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) : 0 < hankelRho0 c Δ := by
  unfold hankelRho0
  have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hpow1 : 0 < (2 * π) ^ c := Real.rpow_pos_of_pos (by positivity) c
  have hpow2 : 0 < Δ ^ (c - 1) := Real.rpow_pos_of_pos hΔ (c - 1)
  positivity

lemma hankelRho0_nonneg {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 ≤ Δ) : 0 ≤ hankelRho0 c Δ := by
  unfold hankelRho0
  have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  exact mul_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) c) hG.le)
    (Real.rpow_nonneg hΔ (c - 1))

lemma continuousOn_hankelRho0 (c : ℝ) : ContinuousOn (hankelRho0 c) (Ioi 0) := by
  intro Δ hΔ
  unfold hankelRho0
  exact ((continuousAt_id.rpow_const (Or.inl (ne_of_gt (mem_Ioi.mp hΔ)))).const_mul
    _).continuousWithinAt

/-- Hankel `L¹` mass `M[f] = ∫_{0}^∞ |f(Δ)| ρ₀(c, Δ) dΔ`. -/
noncomputable def hankelMass (c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ Δ in Ioi (0 : ℝ), |f Δ| * hankelRho0 c Δ

lemma hankelMass_nonneg {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) : 0 ≤ hankelMass c f :=
  setIntegral_nonneg measurableSet_Ioi fun _ hΔ =>
    mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc (le_of_lt hΔ))

lemma abs_mul_rho0_integrableOn {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0)) :
    IntegrableOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioi 0) := by
  refine hint.norm.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ => ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc (le_of_lt hΔ))]

/-- Rescaled Airy window profile `Ψ_{f,c}(u) = (c^{1/3}/β₁) (f ρ₀)(c/π² - u c^{1/3}/β₁)`
extended by `0` outside `{Δ > 0}`. -/
noncomputable def hankelWindowProfile (c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  let Δ := c / π ^ 2 - u / hankelBeta1 * c ^ (1 / 3 : ℝ)
  if 0 < Δ then (c ^ (1 / 3 : ℝ) / hankelBeta1) * (f Δ * hankelRho0 c Δ) else 0

private lemma hankelWindowProfile_eq_indicator (c : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    hankelWindowProfile c f u =
      (c ^ (1 / 3 : ℝ) / hankelBeta1) *
        (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * hankelRho0 c Δ)
          (c / π ^ 2 - (c ^ (1 / 3 : ℝ) / hankelBeta1) * u) := by
  have hsub : c / π ^ 2 - u / hankelBeta1 * c ^ (1 / 3 : ℝ) =
      c / π ^ 2 - (c ^ (1 / 3 : ℝ) / hankelBeta1) * u := by ring
  unfold hankelWindowProfile
  dsimp only
  rw [hsub]
  by_cases h : 0 < c / π ^ 2 - (c ^ (1 / 3 : ℝ) / hankelBeta1) * u
  · rw [indicator_of_mem (mem_Ioi.mpr h)]
    split_ifs; rfl
  · rw [indicator_of_notMem (mem_Ioi.not.mpr h), mul_zero]
    split_ifs; rfl

lemma integrable_hankelWindowProfile_iff {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    Integrable (hankelWindowProfile c f) ↔
      IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0) := by
  let a := c ^ (1 / 3 : ℝ) / hankelBeta1
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc _) hankelBeta1_pos
  have heq : hankelWindowProfile c f = fun u =>
      a * (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * hankelRho0 c Δ) (c / π ^ 2 - a * u) :=
    funext (hankelWindowProfile_eq_indicator c f)
  rw [heq, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr ha.ne')]
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * hankelRho0 c Δ)
  have h1 : Integrable (fun u : ℝ => g (c / π ^ 2 - a * u)) ↔ Integrable (fun u : ℝ => g ((-a) * u)) := by
    have hshift : ∀ u : ℝ, g (c / π ^ 2 - a * u) = g ((-a) * (u - c / (a * π ^ 2))) := fun u => by
      congr 1; field_simp [ha.ne', Real.pi_ne_zero]; ring
    simp_rw [hshift]
    refine ⟨fun h => (h.comp_add_right (c / (a * π ^ 2))).congr (Eventually.of_forall fun u =>
        congr_arg g (by ring)),
      fun h => (h.comp_add_right (-(c / (a * π ^ 2)))).congr (Eventually.of_forall fun u =>
        congr_arg g (by ring))⟩
  rw [h1, integrable_comp_mul_left_iff g (neg_ne_zero.mpr ha.ne'),
    integrable_indicator_iff measurableSet_Ioi]

lemma integral_hankelWindowProfile {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ u : ℝ, hankelWindowProfile c f u = ∫ Δ in Ioi (0 : ℝ), f Δ * hankelRho0 c Δ := by
  let a := c ^ (1 / 3 : ℝ) / hankelBeta1
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc _) hankelBeta1_pos
  have heq : hankelWindowProfile c f = fun u =>
      a * (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * hankelRho0 c Δ) (c / π ^ 2 - a * u) :=
    funext (hankelWindowProfile_eq_indicator c f)
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left (fun t =>
      (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * hankelRho0 c Δ) (c / π ^ 2 - t)) a,
    integral_sub_left_eq_self (fun Δ => (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * hankelRho0 c Δ) Δ)
      volume (c / π ^ 2),
    integral_indicator measurableSet_Ioi, smul_eq_mul, abs_inv, abs_of_pos ha,
    ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma integral_abs_hankelWindowProfile {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ u : ℝ, |hankelWindowProfile c f u| = hankelMass c f := by
  have ha_nn : 0 ≤ c ^ (1 / 3 : ℝ) / hankelBeta1 :=
    div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le
  have habs : (fun u => |hankelWindowProfile c f u|) = hankelWindowProfile c (fun Δ => |f Δ|) := by
    ext u; unfold hankelWindowProfile; dsimp only
    split_ifs with h
    · rw [abs_mul, abs_of_nonneg ha_nn, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc h.le)]
    · simp
  rw [habs, integral_hankelWindowProfile hc (fun Δ => |f Δ|), hankelMass]

lemma integral_tail_abs_hankelWindowProfile {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (R : ℝ) :
    ∫ u in Ioi (R * hankelBeta1), |hankelWindowProfile c f u| =
      ∫ Δ in Ioo (0 : ℝ) (c / π ^ 2 - R * c ^ (1 / 3 : ℝ)), |f Δ| * hankelRho0 c Δ := by
  let a := c ^ (1 / 3 : ℝ) / hankelBeta1
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc _) hankelBeta1_pos
  let b := c / π ^ 2 - R * c ^ (1 / 3 : ℝ)
  have h1 : ∀ u : ℝ, (Ioi (R * hankelBeta1)).indicator (fun v => |hankelWindowProfile c f v|) u =
      a * (Ioo (0 : ℝ) b).indicator (fun Δ => |f Δ| * hankelRho0 c Δ) (c / π ^ 2 - a * u) := by
    intro u
    have hlin : c / π ^ 2 - a * u < b ↔ R * hankelBeta1 < u := by
      have hb_eq : b = c / π ^ 2 - a * (R * hankelBeta1) := by
        dsimp [b, a]; field_simp [hankelBeta1_pos.ne']
      rw [hb_eq, sub_lt_sub_iff_left, mul_lt_mul_iff_right₀ ha]
    by_cases hu : u ∈ Ioi (R * hankelBeta1)
    · rw [indicator_of_mem hu]
      have hlt : c / π ^ 2 - a * u < b := hlin.mpr hu
      rw [hankelWindowProfile_eq_indicator]
      by_cases h0 : 0 < c / π ^ 2 - a * u
      · rw [indicator_of_mem (mem_Ioo.mpr ⟨h0, hlt⟩), indicator_of_mem (mem_Ioi.mpr h0),
          abs_mul, abs_of_pos ha, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc h0.le)]
      · rw [indicator_of_notMem (fun hm => h0 (mem_Ioo.mp hm).1)]
        dsimp only [a] at h0 ⊢
        rw [indicator_of_notMem (mem_Ioi.not.mpr h0), mul_zero, abs_zero]
    · rw [indicator_of_notMem hu]
      have hge : ¬ c / π ^ 2 - a * u < b := fun h => hu (hlin.mp h)
      rw [indicator_of_notMem (fun hm => hge (mem_Ioo.mp hm).2), mul_zero]
  rw [← integral_indicator measurableSet_Ioi]
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun t =>
      (Ioo (0 : ℝ) b).indicator (fun Δ => |f Δ| * hankelRho0 c Δ) (c / π ^ 2 - t)) a,
    integral_sub_left_eq_self (fun Δ => (Ioo (0 : ℝ) b).indicator (fun Δ => |f Δ| * hankelRho0 c Δ) Δ)
      volume (c / π ^ 2),
    integral_indicator measurableSet_Ioo, smul_eq_mul, abs_inv, abs_of_pos ha,
    ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma hankelMass_pos_of_continuousOn {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ici 0)) (hint : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0))
    (hne : ∃ Δ : ℝ, 0 ≤ Δ ∧ f Δ ≠ 0) :
    0 < hankelMass c f := by
  obtain ⟨Δ₀, hΔ₀_nn, hΔ₀_ne⟩ := hne
  have hΔ₁ : ∃ Δ₁ : ℝ, 0 < Δ₁ ∧ f Δ₁ ≠ 0 := by
    rcases hΔ₀_nn.eq_or_lt with rfl | hpos
    · obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 (mem_Ici.mpr le_rfl))
        (|f 0| / 2) (by positivity)
      refine ⟨δ / 2, half_pos hδ, fun h0 => ?_⟩
      have hdist := hball (half_pos hδ).le (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
      rw [h0, Real.dist_eq, zero_sub, abs_neg] at hdist
      linarith [abs_pos.mpr hΔ₀_ne]
    · exact ⟨Δ₀, hpos, hΔ₀_ne⟩
  obtain ⟨Δ₁, hΔ₁_pos, hΔ₁_ne⟩ := hΔ₁
  have hint_abs := abs_mul_rho0_integrableOn hc hint
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ =>
      mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc (le_of_lt hΔ)))
    hint_abs).mpr ?_
  have hcont_g : ContinuousOn (fun Δ => |f Δ| * hankelRho0 c Δ) (Ioi 0) :=
    (hcont.mono Ioi_subset_Ici_self).abs.mul (continuousOn_hankelRho0 c)
  have hopen : IsOpen {Δ ∈ Ioi (0 : ℝ) | 0 < |f Δ| * hankelRho0 c Δ} :=
    hcont_g.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
  have hmem : Δ₁ ∈ {Δ ∈ Ioi (0 : ℝ) | 0 < |f Δ| * hankelRho0 c Δ} :=
    ⟨hΔ₁_pos, mul_pos (abs_pos.mpr hΔ₁_ne) (hankelRho0_pos hc hΔ₁_pos)⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨Δ₁, hmem⟩)
    (measure_mono fun Δ h => ⟨Function.mem_support.mpr h.2.ne', h.1⟩)

/-! ### Section 2: Theorem 7.5 (`gt:7.5` / `thm:radial-rigidity`) — All-Level Rigidity -/

/-- Unified Hermite–Biehler extremal and uniqueness package covering `(P, Q) = (1, 0)` (`m = 1`,
`G_Ai = airyExtremal`) as well as all `AiryPQHB P Q` with `Q ≠ 0` (`hbExtremal`). -/
structure HermiteBiehlerData where
  P : ℝ[X]
  Q : ℝ[X]
  hHB : AiryPQHB P Q
  S : Finset ℝ
  tm : ℝ
  G : ℂ → ℂ
  S_nonempty : S.Nonempty
  tm_mem : tm ∈ S
  tm_min : ∀ t ∈ S, tm ≤ t
  G_diff : Differentiable ℂ G
  G_int : Integrable (fun x : ℝ => G (x : ℂ))
  G_env : ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖G u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u
  G_real : ∀ x : ℝ, (G (x : ℂ)).im = 0
  G_integral_zero : (∫ x : ℝ, G (x : ℂ)) = 0
  G_l1_pos : 0 < ∫ x : ℝ, ‖G (x : ℂ)‖
  G_nonneg_left : ∀ x : ℝ, x ≤ tm → 0 ≤ (G (x : ℂ)).re
  G_eq_zero_on_S : ∀ t ∈ S, G (t : ℂ) = 0
  G_deriv_ne_zero : ∀ t ∈ S, deriv G (t : ℂ) ≠ 0
  uniqueness : ∀ {H : ℂ → ℂ} {C ν : ℝ},
    Differentiable ℂ H → Integrable (fun x : ℝ => H (x : ℂ)) →
    0 ≤ C → (∀ u : ℂ, ‖H u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) →
    (∀ x : ℝ, (H (x : ℂ)).im = 0) →
    0 ≤ (∫ x : ℝ, H (x : ℂ)).re →
    (∀ t ∈ S, t ≠ tm → (H (t : ℂ)).re ≤ 0) →
    (∀ x : ℝ, x ≤ tm → (H (x : ℂ)).re ≤ 0) →
    ∃ b : ℝ, 0 ≤ b ∧ (∀ z : ℂ, H z = -((b : ℂ) * G z)) ∧
      ((∃ z : ℂ, H z ≠ 0) →
        0 < b ∧
        b = (∫ x : ℝ, ‖H (x : ℂ)‖) / (∫ x : ℝ, ‖G (x : ℂ)‖) ∧
        ∀ t ∈ S, deriv H (t : ℂ) ≠ 0)

/-- Unit-`L¹` normalized extremal profile `G_N / ‖G_N‖₁` on `ℝ`. -/
noncomputable def HermiteBiehlerData.normG (D : HermiteBiehlerData) (u : ℝ) : ℝ :=
  (D.G (u : ℂ)).re / ∫ x : ℝ, ‖D.G (x : ℂ)‖

lemma HermiteBiehlerData.normG_continuous (D : HermiteBiehlerData) : Continuous D.normG :=
  ((Complex.continuous_re.comp (D.G_diff.continuous.comp Complex.continuous_ofReal)).div_const _)

lemma HermiteBiehlerData.normG_integrable (D : HermiteBiehlerData) : Integrable D.normG :=
  D.G_int.re.div_const _

lemma HermiteBiehlerData.normG_integral (D : HermiteBiehlerData) : ∫ u : ℝ, D.normG u = 0 := by
  unfold HermiteBiehlerData.normG
  have hre : ∫ u : ℝ, (D.G (u : ℂ)).re = (∫ u : ℝ, D.G (u : ℂ)).re := integral_re D.G_int
  rw [integral_div, hre, D.G_integral_zero, Complex.zero_re, zero_div]

lemma HermiteBiehlerData.normG_abs_integral (D : HermiteBiehlerData) :
    ∫ u : ℝ, |D.normG u| = 1 := by
  have hnorm : (fun u : ℝ => |D.normG u|) =
      fun u : ℝ => ‖D.G (u : ℂ)‖ / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
    ext u
    unfold HermiteBiehlerData.normG
    have hG_cast : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
    rw [abs_div, abs_of_pos D.G_l1_pos]
    congr 1
    conv_rhs => rw [hG_cast, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, integral_div, div_self D.G_l1_pos.ne']

lemma airyExtremal_deriv_airyZero_one :
    deriv airyExtremal (airyZero 1 : ℂ) = -(deriv airyAiC (airyZero 1 : ℂ)) ^ 2 := by
  have hd_ds : Differentiable ℂ (dslope airyAiC (airyZero 1 : ℂ)) :=
    EntireDiv.differentiable_dslope_entire differentiable_airyAiC _
  have hd_mul := ((differentiable_airyAiC (airyZero 1 : ℂ)).hasDerivAt.mul
    (hd_ds (airyZero 1 : ℂ)).hasDerivAt).neg
  change HasDerivAt airyExtremal _ (airyZero 1 : ℂ) at hd_mul
  rw [hd_mul.deriv, airyAiC_airyZero, dslope_same, zero_mul, add_zero, sq]

/-- One-level Hermite–Biehler data `(P, Q) = (1, 0)` (`N = Ai`, `G_Ai = airyExtremal`, `t₁ = a₁`). -/
noncomputable def HermiteBiehlerData.airy : HermiteBiehlerData where
  P := 1
  Q := 0
  hHB := by simpa using airyPQHB_C 1 0 (Or.inl one_ne_zero)
  S := {airyZero 1}
  tm := airyZero 1
  G := airyExtremal
  S_nonempty := Finset.singleton_nonempty _
  tm_mem := Finset.mem_singleton_self _
  tm_min := fun t ht => by rw [Finset.mem_singleton.mp ht]
  G_diff := differentiable_airyExtremal
  G_int := airyExtremal_integrable
  G_env := airyExtremal_attains.2.2.1
  G_real := fun x => airyExtremal_attains.2.2.2.1 x
  G_integral_zero := airyExtremal_integral
  G_l1_pos := by
    have h0 := airyExtremal_attains
    obtain ⟨C, ν, hC, hb⟩ := h0.2.2.1
    have hre : (∫ x : ℝ, (-airyExtremal (x : ℂ))).re = 0 := by
      rw [integral_neg, Complex.neg_re, airyExtremal_integral, Complex.zero_re, neg_zero]
    obtain ⟨_, _, _, _, hnz⟩ := airy_m1_uniqueness (H := fun z => -airyExtremal z)
      differentiable_airyExtremal.neg airyExtremal_integrable.neg hC
      (fun u => by simpa using hb u) (fun x => neg_eq_zero.mpr (h0.2.2.2.1 x))
      hre.ge (fun x hx => by rw [Complex.neg_re]; linarith [h0.2.2.2.2.1 x hx])
    obtain ⟨z, hz⟩ := h0.2.2.2.2.2.2
    exact (hnz ⟨z, neg_ne_zero.mpr hz⟩).2.1
  G_nonneg_left := fun x hx => airyExtremal_nonneg hx
  G_eq_zero_on_S := fun t ht => by
    rw [Finset.mem_singleton.mp ht]; unfold airyExtremal; rw [airyAiC_airyZero, zero_mul, neg_zero]
  G_deriv_ne_zero := fun t ht => by
    rw [Finset.mem_singleton.mp ht, airyExtremal_deriv_airyZero_one]
    exact neg_ne_zero.mpr (pow_ne_zero 2 (airyZero_deriv_ne_zero 1))
  uniqueness := fun hHd hHi hC hHb hHreal hHint _ hHneg => by
    obtain ⟨b, hb_nn, hH_eq, _, hnz⟩ := airy_m1_uniqueness hHd hHi hC hHb hHreal hHint hHneg
    refine ⟨b, hb_nn, hH_eq, fun h => ?_⟩
    obtain ⟨hb_pos, _, hb_ratio, hd⟩ := hnz h
    exact ⟨hb_pos, hb_ratio, fun t ht => by rwa [Finset.mem_singleton.mp ht]⟩

lemma HermiteBiehlerData.normG_airy_deriv_neg :
    deriv HermiteBiehlerData.airy.normG (airyZero 1) < 0 := by
  have hdC : HasDerivAt (fun u : ℝ => airyExtremal (u : ℂ))
      (deriv airyExtremal (airyZero 1 : ℂ)) (airyZero 1) := by
    simpa only [mul_one] using (differentiable_airyExtremal (airyZero 1 : ℂ)).hasDerivAt.comp_ofReal
  have hdNorm : HasDerivAt HermiteBiehlerData.airy.normG
      ((deriv airyExtremal (airyZero 1 : ℂ)).re / ∫ x : ℝ, ‖airyExtremal (x : ℂ)‖) (airyZero 1) :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (airyZero 1) hdC).div_const _
  rw [hdNorm.deriv, airyExtremal_deriv_airyZero_one, deriv_airyAiC_ofReal,
    ← Complex.ofReal_pow, ← Complex.ofReal_neg, Complex.ofReal_re]
  have hne : airyAi' (airyZero 1) ≠ 0 := by
    have h := airyZero_deriv_ne_zero 1
    rw [deriv_airyAiC_ofReal] at h
    exact_mod_cast h
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_ne_zero hne)) HermiteBiehlerData.airy.G_l1_pos

/-- General Hermite–Biehler data for `(P, Q)` with `AiryPQHB P Q` and `Q ≠ 0`. -/
noncomputable def HermiteBiehlerData.ofQNeZero {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    HermiteBiehlerData where
  P := P
  Q := Q
  hHB := hHB
  S := hbTopZeros hHB hQ
  tm := hbMinZero hHB hQ
  G := hbExtremal hHB hQ
  S_nonempty := ⟨hbMinZero hHB hQ, (hbTopZeros_spec hHB hQ).2.2.2.1⟩
  tm_mem := (hbTopZeros_spec hHB hQ).2.2.2.1
  tm_min := (hbTopZeros_spec hHB hQ).2.2.2.2
  G_diff := (hbExtremal_spec hHB hQ).1
  G_int := (hbExtremal_spec hHB hQ).2.2.1
  G_env := (hbExtremal_spec hHB hQ).2.2.2.1
  G_real := (hbExtremal_spec hHB hQ).2.2.2.2.1
  G_integral_zero := (hbExtremal_spec hHB hQ).2.2.2.2.2.2.2.1
  G_l1_pos := by
    have hsp := hbExtremal_spec hHB hQ
    obtain ⟨C, ν, hC, hb⟩ := hsp.2.2.2.1
    obtain ⟨x₀, hx₀⟩ := hsp.2.2.2.2.2.2.2.2
    have hre : (∫ x : ℝ, (-hbExtremal hHB hQ (x : ℂ))).re = 0 := by
      rw [integral_neg, Complex.neg_re, hsp.2.2.2.2.2.2.2.1, Complex.zero_re, neg_zero]
    obtain ⟨_, _, _, hnz⟩ := hbExtremal_uniqueness hHB hQ hsp.1.neg hsp.2.2.1.neg hC
      (fun u => by simpa using hb u) (fun x => neg_eq_zero.mpr (hsp.2.2.2.2.1 x))
      hre.ge (fun t ht _ => by rw [Pi.neg_apply, Complex.neg_re, hsp.2.2.2.2.2.2.1 t ht]; simp)
      (fun x hx => by rw [Pi.neg_apply, Complex.neg_re]; linarith [hsp.2.2.2.2.2.1 x hx])
    exact (hnz ⟨(x₀ : ℂ), neg_ne_zero.mpr hx₀⟩).2.1
  G_nonneg_left := (hbExtremal_spec hHB hQ).2.2.2.2.2.1
  G_eq_zero_on_S := (hbExtremal_spec hHB hQ).2.2.2.2.2.2.1
  G_deriv_ne_zero := by
    have hsp := hbExtremal_spec hHB hQ
    obtain ⟨C, ν, hC, hb⟩ := hsp.2.2.2.1
    obtain ⟨x₀, hx₀⟩ := hsp.2.2.2.2.2.2.2.2
    have hre : (∫ x : ℝ, (-hbExtremal hHB hQ (x : ℂ))).re = 0 := by
      rw [integral_neg, Complex.neg_re, hsp.2.2.2.2.2.2.2.1, Complex.zero_re, neg_zero]
    obtain ⟨_, _, _, hnz⟩ := hbExtremal_uniqueness hHB hQ hsp.1.neg hsp.2.2.1.neg hC
      (fun u => by simpa using hb u) (fun x => neg_eq_zero.mpr (hsp.2.2.2.2.1 x))
      hre.ge (fun t ht _ => by rw [Pi.neg_apply, Complex.neg_re, hsp.2.2.2.2.2.2.1 t ht]; simp)
      (fun x hx => by rw [Pi.neg_apply, Complex.neg_re]; linarith [hsp.2.2.2.2.2.1 x hx])
    have hd := (hnz ⟨(x₀ : ℂ), neg_ne_zero.mpr hx₀⟩).2.2.2
    intro t ht h0'
    apply hd t ht
    rw [((hsp.1 (t : ℂ)).hasDerivAt.neg).deriv, h0', neg_zero]
  uniqueness := fun hHd hHi hC hHb hHreal hHint hHS hHneg => by
    obtain ⟨b, hb_nn, hH_eq, hnz⟩ := hbExtremal_uniqueness hHB hQ hHd hHi hC hHb hHreal hHint hHS hHneg
    exact ⟨b, hb_nn, hH_eq, fun h => let r := hnz h; ⟨r.1, r.2.2.1, r.2.2.2⟩⟩

/-- General Hermite–Biehler data for ANY `AiryPQHB P Q` (splitting on `Q = 0` vs `Q ≠ 0`). -/
noncomputable def HermiteBiehlerData.ofAiryPQHB {P Q : ℝ[X]} (hHB : AiryPQHB P Q) :
    HermiteBiehlerData :=
  if hQ : Q = 0 then HermiteBiehlerData.airy else HermiteBiehlerData.ofQNeZero hHB hQ

/-- Clark two-node Hermite–Biehler data `(P, Q) = (cos α, -sin α)` for `sin α ≠ 0`. -/
noncomputable def HermiteBiehlerData.clark {α : ℝ} (hα : Real.sin α ≠ 0) : HermiteBiehlerData :=
  HermiteBiehlerData.ofQNeZero
    (airyPQHB_C (Real.cos α) (-Real.sin α) (Or.inr (neg_ne_zero.mpr hα)))
    (by simpa using neg_ne_zero.mpr hα)

/-- Packaged hypotheses for Theorem 7.5 (`gt:7.5` / `thm:radial-rigidity`), incorporating the
radial-compactness and deep-lobe bounds of `lem:radial-compactness`. -/
structure RadialRigidityPackage (ι : Type*) (p : Filter ι) (D : HermiteBiehlerData) where
  c : ι → ℝ
  eps : ℝ
  eps_sign : eps = 1 ∨ eps = -1
  f : ι → ℝ → ℝ
  T : ι → ℝ
  Tsite : D.S → ι → ℝ
  c_tendsto : Tendsto c p atTop
  f_cont : ∀ᶠ n in p, ContinuousOn (f n) (Ici 0)
  f_int : ∀ᶠ n in p, IntegrableOn (fun Δ => f n Δ * hankelRho0 (c n) Δ) (Ioi 0)
  f_ne : ∀ᶠ n in p, ∃ Δ : ℝ, 0 ≤ Δ ∧ f n Δ ≠ 0
  f_origin_eq : ∀ᶠ n in p, eps * f n 0 = ∫ Δ in Ioi 0, f n Δ * hankelRho0 (c n) Δ
  f_origin_le : ∀ᶠ n in p, eps * f n 0 ≤ 0
  f_tail_nonneg : ∀ᶠ n in p, ∀ Δ : ℝ, T n ≤ Δ → 0 ≤ f n Δ
  f_site_nonneg : ∀ t : D.S, (t : ℝ) ≠ D.tm → ∀ᶠ n in p, 0 ≤ f n (Tsite t n)
  Tsite_asymp : ∀ t : D.S, (t : ℝ) ≠ D.tm →
    Tendsto (fun n => (c n) ^ (-(1 / 3 : ℝ)) * (Tsite t n - c n / π ^ 2)) p
      (𝓝 (-(t : ℝ) / hankelBeta1))
  deep_lobe_mass : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
    ∀ R : ℝ, 1 ≤ R → ∀ᶠ n in p, R * (c n) ^ (1 / 3 : ℝ) < c n / π ^ 2 →
      ∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - R * (c n) ^ (1 / 3 : ℝ)),
        |f n Δ| * hankelRho0 (c n) Δ ≤
          C * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ * c n))
  compactness_subseq : ∀ (ns : ℕ → ι), Tendsto ns atTop p →
    (∃ B : ℝ, ∀ k : ℕ, (c (ns k)) ^ (-(1 / 3 : ℝ)) * (T (ns k) - c (ns k) / π ^ 2) ≤ B) →
    ∃ (ms : ℕ → ℕ) (sLim : ℝ) (F : ℂ → ℂ) (C ν : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => (c (ns (ms k))) ^ (-(1 / 3 : ℝ)) *
        (T (ns (ms k)) - c (ns (ms k)) / π ^ 2)) atTop (𝓝 sLim) ∧
      TendstoLocallyUniformlyOn (fun k u =>
          hankelWindowProfile (c (ns (ms k))) (f (ns (ms k))) u /
            hankelMass (c (ns (ms k))) (f (ns (ms k))))
        (fun u : ℝ => (F (u : ℂ)).re) atTop univ ∧
      Differentiable ℂ F ∧
      Integrable (fun u : ℝ => F (u : ℂ)) ∧
      0 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z) ∧
      (∀ u : ℝ, (F (u : ℂ)).im = 0)

private lemma rpow_neg_one_third_mul_add {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 3 : ℝ)) * x ^ (1 / 3 : ℝ) = 1 := by
  rw [← Real.rpow_add hx]; norm_num

private lemma psi_neg_mass_ge_half {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0))
    (hmass : 0 < hankelMass c f) (horigin : (∫ Δ in Ioi 0, f Δ * hankelRho0 c Δ) ≤ 0) :
    (1 / 2 : ℝ) ≤ ∫ u : ℝ, max 0 (-(hankelWindowProfile c f u / hankelMass c f)) := by
  let ψ : ℝ → ℝ := fun u => hankelWindowProfile c f u / hankelMass c f
  have hψ_int : Integrable ψ := ((integrable_hankelWindowProfile_iff hc f).mpr hint).div_const _
  have hψ_abs : ∫ u : ℝ, |ψ u| = 1 := by
    have heq : (fun u => |ψ u|) = fun u => |hankelWindowProfile c f u| / hankelMass c f := by
      ext u; simp [ψ, abs_div, abs_of_pos hmass]
    rw [heq, integral_div, integral_abs_hankelWindowProfile hc f, div_self hmass.ne']
  have hψ_le : ∫ u : ℝ, ψ u ≤ 0 := by
    rw [integral_div, integral_hankelWindowProfile hc f]
    exact div_nonpos_of_nonpos_of_nonneg horigin hmass.le
  have hsplit : (fun u => |ψ u| - ψ u) = fun u => 2 * max 0 (-ψ u) := by
    ext u
    rcases le_total 0 (ψ u) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith), sub_self, mul_zero]
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
  have h1 : (∫ u, |ψ u|) - ∫ u, ψ u = 2 * ∫ u, max 0 (-ψ u) := by
    have hsub := integral_sub hψ_int.abs hψ_int
    rw [hsplit, integral_const_mul] at hsub
    exact hsub.symm
  linarith

private lemma neg_part_integrable {ψ : ℝ → ℝ} (hψ : Integrable ψ) :
    Integrable (fun u : ℝ => max 0 (-ψ u)) := by
  refine Integrable.mono' hψ.abs
    ((continuous_const.max continuous_id).comp_aestronglyMeasurable hψ.neg.aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact max_le (abs_nonneg _) (neg_le_abs _)

private lemma psi_nonneg_of_le_thresh {c T u : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (htail : ∀ Δ : ℝ, T ≤ Δ → 0 ≤ f Δ) (hmass : 0 < hankelMass c f)
    (hu : u ≤ -hankelBeta1 * (c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2))) :
    0 ≤ hankelWindowProfile c f u / hankelMass c f := by
  unfold hankelWindowProfile; dsimp only
  split_ifs with hΔ
  · refine div_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hc.le _) hankelBeta1_pos.le)
      (mul_nonneg (htail _ ?_) (hankelRho0_nonneg hc hΔ.le))) hmass.le
    have h1 : (-c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2)) * c ^ (1 / 3 : ℝ) = -(T - c / π ^ 2) := by
      rw [show (-c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2)) * c ^ (1 / 3 : ℝ) =
        -(c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) * (T - c / π ^ 2) by ring,
        rpow_neg_one_third_mul_add hc]; ring
    have h' : u / hankelBeta1 ≤ -(c ^ (-(1 / 3 : ℝ)) * (T - c / π ^ 2)) :=
      (div_le_iff₀ hankelBeta1_pos).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_right h' (Real.rpow_nonneg hc.le (1 / 3 : ℝ))
    linarith [h1]
  · simp

private lemma integral_Icc_tendsto {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun R : ℝ => ∫ u in Icc (-R) R, g u) atTop (𝓝 (∫ u : ℝ, g u)) := by
  have heq : ∀ R : ℝ, ∫ u in Icc (-R) R, g u = ∫ u : ℝ, (Icc (-R) R).indicator g u := fun R =>
    (integral_indicator measurableSet_Icc).symm
  simp_rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖g u‖)
    (Eventually.of_forall fun R => (hg.indicator measurableSet_Icc).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun u => by
      simp only [Set.indicator]; split_ifs <;> simp)
    hg.norm (Eventually.of_forall fun u => ?_)
  exact tendsto_const_nhds.congr'
    ((eventually_ge_atTop |u|).mono fun R hR => (Set.indicator_of_mem (mem_Icc.mpr (abs_le.mp hR)) g).symm)

private lemma setIntegral_Icc_tendsto_of_tendstoUniformlyOn
    {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hunif : TendstoUniformlyOn g G atTop (Icc a b))
    (hg_int : ∀ᶠ k in atTop, IntegrableOn (g k) (Icc a b))
    (hG_int : IntegrableOn G (Icc a b)) :
    Tendsto (fun k => ∫ u in Icc a b, g k u) atTop (𝓝 (∫ u in Icc a b, G u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (b - a + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hunif' := Metric.tendstoUniformlyOn_iff.mp hunif δ hδ
  filter_upwards [hg_int, hunif'] with k hki hku
  rw [Real.dist_eq, ← integral_sub hki hG_int]
  have h1 : |∫ u in Icc a b, (g k u - G u)| ≤ ∫ u in Icc a b, |g k u - G u| :=
    by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => g k u - G u)
  have h2 : ∫ u in Icc a b, |g k u - G u| ≤ ∫ _u in Icc a b, δ := by
    refine setIntegral_mono_on (hki.sub hG_int).abs continuousOn_const.integrableOn_Icc
      measurableSet_Icc fun u hu => ?_
    simpa [Real.dist_eq, abs_sub_comm] using (hku u hu).le
  have h3 : ∫ _u in Icc a b, δ = (b - a) * δ := by
    rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
  have h4 : (b - a) * δ < ε := by
    dsimp [δ]; rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

/-- Lower bound on the rescaled threshold from the deep-lobe mass bound, on raw data. -/
theorem scaled_threshold_bddBelow_raw {ι : Type*} {p : Filter ι}
    (c : ι → ℝ) (eps : ℝ) (f : ι → ℝ → ℝ) (T : ι → ℝ)
    (h_c_tendsto : Tendsto c p atTop)
    (h_f_cont : ∀ᶠ n in p, ContinuousOn (f n) (Ici 0))
    (h_f_int : ∀ᶠ n in p, IntegrableOn (fun Δ => f n Δ * hankelRho0 (c n) Δ) (Ioi 0))
    (h_f_ne : ∀ᶠ n in p, ∃ Δ : ℝ, 0 ≤ Δ ∧ f n Δ ≠ 0)
    (h_f_origin_eq : ∀ᶠ n in p, eps * f n 0 = ∫ Δ in Ioi 0, f n Δ * hankelRho0 (c n) Δ)
    (h_f_origin_le : ∀ᶠ n in p, eps * f n 0 ≤ 0)
    (h_f_tail_nonneg : ∀ᶠ n in p, ∀ Δ : ℝ, T n ≤ Δ → 0 ≤ f n Δ)
    (hdeep : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ R : ℝ, 1 ≤ R → ∀ᶠ n in p, R * (c n) ^ (1 / 3 : ℝ) < c n / π ^ 2 →
        ∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - R * (c n) ^ (1 / 3 : ℝ)),
          |f n Δ| * hankelRho0 (c n) Δ ≤
            C * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ * c n))) :
    ∃ B₀ : ℝ, ∀ᶠ n in p, B₀ ≤ (c n) ^ (-(1 / 3 : ℝ)) * (T n - c n / π ^ 2) := by
  obtain ⟨C, κ, hC, hκ, hlobe⟩ := hdeep
  have htR : Tendsto (fun r : ℝ => C * Real.exp (-5 * r ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop
      (neg_lt_zero.mpr (by norm_num : (0 : ℝ) < 5))
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)))).const_mul C)
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (htR.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  let r₀ := max R₀ 1
  have hr₀1 : 1 ≤ r₀ := le_max_right _ _
  have hr₀_lt : C * Real.exp (-5 * r₀ ^ (3 / 2 : ℝ)) < 1 / 4 := hR₀ r₀ (le_max_left _ _)
  have hexp_c : ∀ᶠ n in p, C * Real.exp (-κ * c n) < 1 / 4 := by
    have ht : Tendsto (fun n => C * Real.exp (-κ * c n)) p (𝓝 0) := by
      simpa using ((Real.tendsto_exp_atBot.comp
        (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hκ) h_c_tendsto)).const_mul C)
    exact ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hc_dom : ∀ᶠ n in p, 1 ≤ c n ∧ r₀ * (c n) ^ (1 / 3 : ℝ) < c n / π ^ 2 := by
    have hq : Tendsto (fun n => (c n) ^ (2 / 3 : ℝ)) p atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp h_c_tendsto
    filter_upwards [h_c_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
      hq.eventually (eventually_gt_atTop (r₀ * π ^ 2))] with n hc1 hqgt
    refine ⟨hc1, ?_⟩
    have hc0 : 0 < c n := by linarith
    have hmul := mul_lt_mul_of_pos_right hqgt (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ))
    rw [← Real.rpow_add hc0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one] at hmul
    rw [lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)]
    linarith
  refine ⟨-r₀, ?_⟩
  filter_upwards [hc_dom, hexp_c, hlobe r₀ hr₀1, h_f_cont, h_f_int, h_f_ne,
    h_f_origin_eq, h_f_origin_le, h_f_tail_nonneg] with
    n ⟨hc1, hRlt⟩ hexp_lt hlobe_n hcont hint hne horg horg_le htail
  have hc0 : 0 < c n := by linarith
  have hmass : 0 < hankelMass (c n) (f n) := hankelMass_pos_of_continuousOn hc0 hcont hint hne
  by_contra hbad
  push Not at hbad
  let ψ : ℝ → ℝ := fun u => hankelWindowProfile (c n) (f n) u / hankelMass (c n) (f n)
  have hψ_int : Integrable ψ := ((integrable_hankelWindowProfile_iff hc0 _).mpr hint).div_const _
  have hm_int := neg_part_integrable hψ_int
  have hhalf := psi_neg_mass_ge_half hc0 hint hmass (by rw [← horg]; exact horg_le)
  have hzero_left : ∀ u : ℝ, u ≤ r₀ * hankelBeta1 → max 0 (-ψ u) = 0 := fun u hu => by
    have hnn : 0 ≤ ψ u := psi_nonneg_of_le_thresh hc0 htail hmass
      (hu.trans (by nlinarith [hankelBeta1_pos]))
    exact max_eq_left (by linarith)
  have hsplit := integral_add_compl (s := Ioi (r₀ * hankelBeta1)) measurableSet_Ioi hm_int
  have hcompl : ∫ u in (Ioi (r₀ * hankelBeta1))ᶜ, max 0 (-ψ u) = 0 := by
    rw [compl_Ioi]
    exact setIntegral_eq_zero_of_forall_eq_zero fun u hu => hzero_left u hu
  rw [hcompl, add_zero] at hsplit
  have hle_abs : ∫ u in Ioi (r₀ * hankelBeta1), max 0 (-ψ u) ≤
      ∫ u in Ioi (r₀ * hankelBeta1), |ψ u| :=
    setIntegral_mono_on hm_int.integrableOn hψ_int.abs.integrableOn measurableSet_Ioi fun u _ =>
      max_le (abs_nonneg _) (neg_le_abs _)
  have habs_tail : ∫ u in Ioi (r₀ * hankelBeta1), |ψ u| =
      (∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - r₀ * (c n) ^ (1 / 3 : ℝ)),
        |f n Δ| * hankelRho0 (c n) Δ) / hankelMass (c n) (f n) := by
    have heq : (fun u => |ψ u|) = fun u => |hankelWindowProfile (c n) (f n) u| / hankelMass (c n) (f n) := by
      ext u; simp [ψ, abs_div, abs_of_pos hmass]
    rw [heq, integral_div, integral_tail_abs_hankelWindowProfile hc0 (f n) r₀]
  have hbd : (∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - r₀ * (c n) ^ (1 / 3 : ℝ)),
        |f n Δ| * hankelRho0 (c n) Δ) / hankelMass (c n) (f n) ≤
      C * (Real.exp (-5 * r₀ ^ (3 / 2 : ℝ)) + Real.exp (-κ * c n)) := by
    rw [div_le_iff₀ hmass]; linarith [hlobe_n hRlt]
  linarith

private lemma RadialRigidityPackage.scaled_threshold_bddBelow {ι : Type*} {p : Filter ι}
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D) :
    ∃ B₀ : ℝ, ∀ᶠ n in p, B₀ ≤ (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) :=
  scaled_threshold_bddBelow_raw R.c R.eps R.f R.T R.c_tendsto R.f_cont R.f_int R.f_ne R.f_origin_eq
    R.f_origin_le R.f_tail_nonneg R.deep_lobe_mass

private lemma RadialRigidityPackage.subseq_extremal {ι : Type*} {p : Filter ι}
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D)
    (ns : ℕ → ι) (hns : Tendsto ns atTop p)
    (hB : ∃ B : ℝ, ∀ k : ℕ, (R.c (ns k)) ^ (-(1 / 3 : ℝ)) * (R.T (ns k) - R.c (ns k) / π ^ 2) ≤ B)
    (hUpper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (R.c (ns k)) ^ (-(1 / 3 : ℝ)) * (R.T (ns k) - R.c (ns k) / π ^ 2) ≤ -(D.tm / hankelBeta1) + ε) :
    ∃ (ms : ℕ → ℕ) (sLim : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => (R.c (ns (ms k))) ^ (-(1 / 3 : ℝ)) *
        (R.T (ns (ms k)) - R.c (ns (ms k)) / π ^ 2)) atTop (𝓝 sLim) ∧
      TendstoLocallyUniformlyOn (fun k u =>
          hankelWindowProfile (R.c (ns (ms k))) (R.f (ns (ms k))) u /
            hankelMass (R.c (ns (ms k))) (R.f (ns (ms k))))
        D.normG atTop univ ∧
      sLim = -(D.tm / hankelBeta1) := by
  obtain ⟨ms, sLim, F, C, ν, hms, hs_lim, hΨ_lim, hFd, hFi, hC, hFb, hFreal⟩ :=
    R.compactness_subseq ns hns hB
  let c' : ℕ → ℝ := fun k => R.c (ns (ms k))
  let T' : ℕ → ℝ := fun k => R.T (ns (ms k))
  let f' : ℕ → ℝ → ℝ := fun k => R.f (ns (ms k))
  let s' : ℕ → ℝ := fun k => (c' k) ^ (-(1 / 3 : ℝ)) * (T' k - c' k / π ^ 2)
  let ψ' : ℕ → ℝ → ℝ := fun k u => hankelWindowProfile (c' k) (f' k) u / hankelMass (c' k) (f' k)
  have hsLim_le : sLim ≤ -(D.tm / hankelBeta1) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact le_of_tendsto hs_lim (hms.tendsto_atTop.eventually (hUpper ε hε))
  have htm_le_band : D.tm ≤ -hankelBeta1 * sLim := by
    have := mul_le_mul_of_nonpos_left hsLim_le (neg_nonpos.mpr hankelBeta1_pos.le)
    rwa [show -hankelBeta1 * -(D.tm / hankelBeta1) = D.tm by field_simp [hankelBeta1_pos.ne']] at this
  have hsub : Tendsto (fun k => ns (ms k)) atTop p := hns.comp hms.tendsto_atTop
  have hc'_tend : Tendsto c' atTop atTop := R.c_tendsto.comp hsub
  obtain ⟨C_l, κ_l, hCl, hκl, hlobe⟩ := R.deep_lobe_mass
  have hc_pos : ∀ᶠ k in atTop, 0 < c' k := hc'_tend.eventually (eventually_gt_atTop 0)
  have hf_cont : ∀ᶠ k in atTop, ContinuousOn (f' k) (Ici 0) := hsub.eventually R.f_cont
  have hf_int : ∀ᶠ k in atTop, IntegrableOn (fun Δ => f' k Δ * hankelRho0 (c' k) Δ) (Ioi 0) :=
    hsub.eventually R.f_int
  have hf_ne : ∀ᶠ k in atTop, ∃ Δ : ℝ, 0 ≤ Δ ∧ f' k Δ ≠ 0 := hsub.eventually R.f_ne
  have hf_org : ∀ᶠ k in atTop, R.eps * f' k 0 = ∫ Δ in Ioi 0, f' k Δ * hankelRho0 (c' k) Δ :=
    hsub.eventually R.f_origin_eq
  have hf_org_le : ∀ᶠ k in atTop, R.eps * f' k 0 ≤ 0 := hsub.eventually R.f_origin_le
  have hf_tail : ∀ᶠ k in atTop, ∀ Δ : ℝ, T' k ≤ Δ → 0 ≤ f' k Δ := hsub.eventually R.f_tail_nonneg
  have hF_cont : Continuous (fun u : ℝ => (F (u : ℂ)).re) :=
    Complex.continuous_re.comp (hFd.continuous.comp Complex.continuous_ofReal)
  have hψ_int : ∀ᶠ k in atTop, Integrable (ψ' k) := by
    filter_upwards [hc_pos, hf_int] with k hc0 hink
    exact ((integrable_hankelWindowProfile_iff hc0 _).mpr hink).div_const _
  have hF_nonneg_band : ∀ u : ℝ, u ≤ -hankelBeta1 * sLim → 0 ≤ (F (u : ℂ)).re := by
    have hlt_case : ∀ u : ℝ, u < -hankelBeta1 * sLim → 0 ≤ (F (u : ℂ)).re := fun u hu => by
      have hev_le : ∀ᶠ k in atTop, u ≤ -hankelBeta1 * s' k :=
        ((tendsto_const_nhds.mul hs_lim).eventually (Ioi_mem_nhds hu)).mono fun _ h => h.le
      refine ge_of_tendsto (hΨ_lim.tendsto_at (mem_univ u)) ?_
      filter_upwards [hc_pos, hf_cont, hf_int, hf_ne, hf_tail, hev_le] with k hc0 hck hink hnek htk hlek
      exact psi_nonneg_of_le_thresh hc0 htk (hankelMass_pos_of_continuousOn hc0 hck hink hnek) hlek
    intro u hu
    rcases hu.eq_or_lt with rfl | hlt
    · have hseq : Tendsto (fun j : ℕ => -hankelBeta1 * sLim - ((j : ℝ) + 1)⁻¹) atTop
          (𝓝 (-hankelBeta1 * sLim)) := by
        simpa using (tendsto_const_nhds (x := -hankelBeta1 * sLim)).sub
          (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      exact ge_of_tendsto (hF_cont.continuousAt.tendsto.comp hseq)
        (Eventually.of_forall fun j => hlt_case _ (by linarith [show (0 : ℝ) < ((j : ℝ) + 1)⁻¹ by positivity]))
    · exact hlt_case u hlt
  have hF_sites : ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ (F (t : ℂ)).re := by
    intro t htS htne
    let ts : D.S := ⟨t, htS⟩
    let u' : ℕ → ℝ := fun k =>
      hankelBeta1 * ((c' k) ^ (-(1 / 3 : ℝ)) * (c' k / π ^ 2 - R.Tsite ts (ns (ms k))))
    have hasymp : Tendsto u' atTop (𝓝 t) := by
      have h1 := ((R.Tsite_asymp ts htne).comp hsub).neg.const_mul hankelBeta1
      have hlim : hankelBeta1 * -(-(t : ℝ) / hankelBeta1) = t := by field_simp [hankelBeta1_pos.ne']
      rw [hlim] at h1
      exact h1.congr' (Eventually.of_forall fun k => by dsimp [u']; ring)
    have hsite_pos : ∀ᶠ k in atTop, 0 < R.Tsite ts (ns (ms k)) := by
      have hc23 : Tendsto (fun k => (c' k) ^ (2 / 3 : ℝ) / π ^ 2) atTop atTop :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_tend).atTop_div_const
          (sq_pos_of_pos Real.pi_pos)
      have hsub_t : Tendsto (fun k => (c' k) ^ (2 / 3 : ℝ) / π ^ 2 - u' k / hankelBeta1) atTop atTop := by
        have hbd : ∀ᶠ k in atTop, u' k / hankelBeta1 ≤ t / hankelBeta1 + 1 :=
          (hasymp.div_const hankelBeta1).eventually (eventually_le_nhds (by linarith))
        exact tendsto_atTop_mono' atTop (hbd.mono fun _ hk => sub_le_sub_left hk _)
          (hc23.atTop_add tendsto_const_nhds)
      have hdom : Tendsto (fun k => (c' k) ^ (1 / 3 : ℝ) * ((c' k) ^ (2 / 3 : ℝ) / π ^ 2 - u' k / hankelBeta1))
          atTop atTop :=
        Tendsto.atTop_mul_atTop₀ ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc'_tend) hsub_t
      filter_upwards [hdom.eventually (eventually_gt_atTop 0), hc_pos] with k hpos hc0
      have heq : R.Tsite ts (ns (ms k)) =
          (c' k) ^ (1 / 3 : ℝ) * ((c' k) ^ (2 / 3 : ℝ) / π ^ 2 - u' k / hankelBeta1) := by
        have hmul : (c' k) ^ (1 / 3 : ℝ) * ((c' k) ^ (2 / 3 : ℝ) / π ^ 2) = c' k / π ^ 2 := by
          rw [mul_div_assoc', ← Real.rpow_add hc0, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]
        rw [mul_sub, hmul]; dsimp [u']
        have hr := rpow_neg_one_third_mul_add hc0
        have hb : hankelBeta1 ≠ 0 := hankelBeta1_pos.ne'
        calc R.Tsite ts (ns (ms k))
            = c' k / π ^ 2 - (c' k ^ (-(1 / 3 : ℝ)) * c' k ^ (1 / 3 : ℝ)) *
                (c' k / π ^ 2 - R.Tsite ts (ns (ms k))) := by rw [hr]; ring
          _ = _ := by field_simp [hb]
      rwa [heq]
    have hψ_at_u' : ∀ᶠ k in atTop, 0 ≤ ψ' k (u' k) := by
      filter_upwards [hc_pos, hf_cont, hf_int, hf_ne, hsub.eventually (R.f_site_nonneg ts htne), hsite_pos] with
        k hc0 hck hink hnek hsk hpos
      have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
      have hΔ : c' k / π ^ 2 - u' k / hankelBeta1 * (c' k) ^ (1 / 3 : ℝ) = R.Tsite ts (ns (ms k)) := by
        dsimp [u']
        have hr := rpow_neg_one_third_mul_add hc0
        have hb : hankelBeta1 ≠ 0 := hankelBeta1_pos.ne'
        calc c' k / π ^ 2 - hankelBeta1 * (c' k ^ (-(1 / 3 : ℝ)) * (c' k / π ^ 2 - R.Tsite ts (ns (ms k)))) /
              hankelBeta1 * c' k ^ (1 / 3 : ℝ)
            = c' k / π ^ 2 - (c' k ^ (-(1 / 3 : ℝ)) * c' k ^ (1 / 3 : ℝ)) *
                (c' k / π ^ 2 - R.Tsite ts (ns (ms k))) := by field_simp [hb]
          _ = R.Tsite ts (ns (ms k)) := by rw [hr]; ring
      dsimp [ψ']; unfold hankelWindowProfile; dsimp only; rw [hΔ]
      split_ifs
      exact div_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg hc0.le _) hankelBeta1_pos.le)
        (mul_nonneg hsk (hankelRho0_nonneg hc0 hpos.le))) hmass.le
    have hlim_u' : Tendsto (fun k => ψ' k (u' k)) atTop (𝓝 ((F (t : ℂ)).re)) := by
      have hdiff : Tendsto (fun k => ψ' k (u' k) - (F (u' k : ℂ)).re) atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]; intro ε hε
        have hunif := Metric.tendstoUniformlyOn_iff.mp
          ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
            (Icc (t - 1) (t + 1)) (subset_univ _) isCompact_Icc) ε hε
        filter_upwards [hunif, hasymp.eventually (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))] with k h1 h2
        rw [Real.dist_eq, sub_zero]
        simpa [Real.dist_eq, abs_sub_comm] using h1 (u' k) h2
      simpa using hdiff.add (hF_cont.continuousAt.tendsto.comp hasymp)
    exact ge_of_tendsto hlim_u' hψ_at_u'
  have hlobe_tail : ∀ r₀ : ℝ, 1 ≤ r₀ → ∀ᶠ k in atTop,
      ∫ u in Ioi (r₀ * hankelBeta1), |ψ' k u| ≤
        C_l * (Real.exp (-5 * r₀ ^ (3 / 2 : ℝ)) + Real.exp (-κ_l * c' k)) := by
    intro r₀ hr₀1
    have hq : Tendsto (fun k => (c' k) ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_tend
    have hc_dom : ∀ᶠ k in atTop, r₀ * (c' k) ^ (1 / 3 : ℝ) < c' k / π ^ 2 := by
      filter_upwards [hc_pos, hq.eventually (eventually_gt_atTop (r₀ * π ^ 2))] with k hc0 hqgt
      have hmul := mul_lt_mul_of_pos_right hqgt (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ))
      rw [← Real.rpow_add hc0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one] at hmul
      rw [lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)]; linarith
    filter_upwards [hc_pos, hf_cont, hf_int, hf_ne, hc_dom, hsub.eventually (hlobe r₀ hr₀1)] with
      k hc0 hck hink hnek hRlt hlobe_k
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    have heq : ∫ u in Ioi (r₀ * hankelBeta1), |ψ' k u| =
        (∫ Δ in Ioo (0 : ℝ) (c' k / π ^ 2 - r₀ * (c' k) ^ (1 / 3 : ℝ)),
          |f' k Δ| * hankelRho0 (c' k) Δ) / hankelMass (c' k) (f' k) := by
      have hp : (fun u => |ψ' k u|) = fun u => |hankelWindowProfile (c' k) (f' k) u| / hankelMass (c' k) (f' k) := by
        ext u; simp [ψ', abs_div, abs_of_pos hmass]
      rw [hp, integral_div, integral_tail_abs_hankelWindowProfile hc0 (f' k) r₀]
    rw [heq, div_le_iff₀ hmass]
    linarith [hlobe_k hRlt]
  let R0 := max (|hankelBeta1 * sLim| + 1) hankelBeta1
  have hR0_tend : Tendsto (fun R' : ℝ => C_l * Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun R' : ℝ => R' / hankelBeta1) atTop atTop :=
      tendsto_id.atTop_div_const hankelBeta1_pos
    simpa using ((Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop
      (neg_lt_zero.mpr (by norm_num : (0 : ℝ) < 5))
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp ht1))).const_mul C_l)
  have hF_abs_int : Integrable (fun u : ℝ => |(F (u : ℂ)).re|) := hFi.re.abs
  have hF_norm_le : ∫ u : ℝ, ‖F (u : ℂ)‖ ≤ 1 := by
    have hnorm_eq : (fun u : ℝ => ‖F (u : ℂ)‖) = fun u : ℝ => |(F (u : ℂ)).re| := by
      ext u
      have hcast : F (u : ℂ) = ((F (u : ℂ)).re : ℂ) := Complex.ext rfl (hFreal u)
      conv_lhs => rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm_eq]
    refine le_of_tendsto (integral_Icc_tendsto hF_abs_int)
      ((eventually_ge_atTop (0 : ℝ)).mono fun R' hR' => ?_)
    have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
      (Icc (-R') R') (subset_univ _) isCompact_Icc)
    have hunif_abs : TendstoUniformlyOn (fun k u => |ψ' k u|) (fun u => |(F (u : ℂ)).re|)
        atTop (Icc (-R') R') := by
      rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
      intro ε hε
      exact (hunif ε hε).mono fun k hk u hu =>
        lt_of_le_of_lt (by simpa [Real.dist_eq] using abs_abs_sub_abs_le (F (u : ℂ)).re (ψ' k u)) (hk u hu)
    have hlim := setIntegral_Icc_tendsto_of_tendstoUniformlyOn (by linarith : -R' ≤ R') hunif_abs
      (hψ_int.mono fun k hk => hk.abs.integrableOn) hF_abs_int.integrableOn
    refine le_of_tendsto hlim ?_
    filter_upwards [hc_pos, hf_cont, hf_int, hf_ne, hψ_int] with k hc0 hck hink hnek hψk
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    have hle := setIntegral_le_integral (s := Icc (-R') R') hψk.abs (Eventually.of_forall fun _ => abs_nonneg _)
    have htot : ∫ u : ℝ, |ψ' k u| = 1 := by
      have heq : (fun u => |ψ' k u|) = fun u => |hankelWindowProfile (c' k) (f' k) u| / hankelMass (c' k) (f' k) := by
        ext u; simp [ψ', abs_div, abs_of_pos hmass]
      rw [heq, integral_div, integral_abs_hankelWindowProfile hc0 (f' k), div_self hmass.ne']
    linarith
  have hF_int_le : (∫ u : ℝ, (F (u : ℂ)).re) ≤ 0 := by
    refine le_of_tendsto_of_tendsto (integral_Icc_tendsto hFi.re) hR0_tend ?_
    filter_upwards [eventually_ge_atTop R0] with R' hR'
    have hR'pos : 0 < R' := lt_of_lt_of_le (by positivity) hR'
    have hr1 : 1 ≤ R' / hankelBeta1 := (one_le_div hankelBeta1_pos).mpr ((le_max_right _ _).trans hR')
    have hs_lt : ∀ᶠ k in atTop, -R' ≤ -hankelBeta1 * s' k := by
      have h1 : -R' < -hankelBeta1 * sLim := by
        have := le_abs_self (hankelBeta1 * sLim); have := neg_abs_le (hankelBeta1 * sLim)
        linarith [le_max_left (|hankelBeta1 * sLim| + 1) hankelBeta1]
      exact ((tendsto_const_nhds.mul hs_lim).eventually (Ioi_mem_nhds h1)).mono fun _ h => h.le
    have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
      (Icc (-R') R') (subset_univ _) isCompact_Icc)
    have hlim := setIntegral_Icc_tendsto_of_tendstoUniformlyOn (by linarith : -R' ≤ R') hunif
      (hψ_int.mono fun k hk => hk.integrableOn) hFi.re.integrableOn
    have hexp_lim : Tendsto (fun k => C_l * (Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)) +
        Real.exp (-κ_l * c' k))) atTop
        (𝓝 (C_l * Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)))) := by
      have ht : Tendsto (fun k => Real.exp (-κ_l * c' k)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hκl) hc'_tend)
      simpa using (tendsto_const_nhds.add ht).const_mul C_l
    refine le_of_tendsto_of_tendsto hlim hexp_lim ?_
    have htl := hlobe_tail (R' / hankelBeta1) hr1
    rw [div_mul_cancel₀ _ hankelBeta1_pos.ne'] at htl
    filter_upwards [hc_pos, hf_cont, hf_int, hf_ne, hf_org, hf_org_le, hf_tail, hψ_int, hs_lt, htl] with
      k hc0 hck hink hnek horgk horglek htk hψk hsle htailk
    have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
    have htot_le : ∫ u : ℝ, ψ' k u ≤ 0 := by
      rw [integral_div, integral_hankelWindowProfile hc0 (f' k), ← horgk]
      exact div_nonpos_of_nonpos_of_nonneg horglek hmass.le
    have hleft_nn : 0 ≤ ∫ u in Iio (-R'), ψ' k u :=
      setIntegral_nonneg measurableSet_Iio fun u hu =>
        psi_nonneg_of_le_thresh hc0 htk hmass (le_trans (le_of_lt hu) hsle)
    have hright_bd : -∫ u in Ioi R', ψ' k u ≤ ∫ u in Ioi R', |ψ' k u| := by
      rw [← integral_neg]
      exact setIntegral_mono_on hψk.neg.integrableOn hψk.abs.integrableOn measurableSet_Ioi fun u _ =>
        neg_le_abs _
    have hdecomp : (∫ u in Iio (-R'), ψ' k u) + (∫ u in Icc (-R') R', ψ' k u) +
        (∫ u in Ioi R', ψ' k u) = ∫ u : ℝ, ψ' k u := by
      have h12 : (∫ u in Iio (-R'), ψ' k u) + ∫ u in Icc (-R') R', ψ' k u =
          ∫ u in Iic R', ψ' k u := by
        rw [← setIntegral_union (Set.disjoint_left.mpr fun _ hx1 hx2 => not_le.mpr (mem_Iio.mp hx1) (mem_Icc.mp hx2).1)
          measurableSet_Icc hψk.integrableOn hψk.integrableOn, Iio_union_Icc_eq_Iic (by linarith)]
      rw [h12, ← compl_Iic]
      exact integral_add_compl measurableSet_Iic hψk
    linarith
  have hF_neg_half : (1 / 2 : ℝ) ≤ ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) := by
    have hm_int := neg_part_integrable hFi.re
    have hle_R : ∀ R' : ℝ, R0 ≤ R' →
        (1 / 2 : ℝ) ≤ (∫ u in Icc (-R') R', max 0 (-(F (u : ℂ)).re)) +
          C_l * Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)) := by
      intro R' hR'
      have hR'pos : 0 < R' := lt_of_lt_of_le (by positivity) hR'
      have hr1 : 1 ≤ R' / hankelBeta1 := (one_le_div hankelBeta1_pos).mpr ((le_max_right _ _).trans hR')
      have hs_lt : ∀ᶠ k in atTop, -R' ≤ -hankelBeta1 * s' k := by
        have h1 : -R' < -hankelBeta1 * sLim := by
          have := le_abs_self (hankelBeta1 * sLim); have := neg_abs_le (hankelBeta1 * sLim)
          linarith [le_max_left (|hankelBeta1 * sLim| + 1) hankelBeta1]
        exact ((tendsto_const_nhds.mul hs_lim).eventually (Ioi_mem_nhds h1)).mono fun _ h => h.le
      have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
        (Icc (-R') R') (subset_univ _) isCompact_Icc)
      have hunif_m : TendstoUniformlyOn (fun k u => max 0 (-ψ' k u))
          (fun u => max 0 (-(F (u : ℂ)).re)) atTop (Icc (-R') R') := by
        rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
        intro ε hε
        exact (hunif ε hε).mono fun k hk u hu => by
          have h1 := hk u hu
          rw [Real.dist_eq] at h1 ⊢
          have hlip : |max 0 (-(F (u : ℂ)).re) - max 0 (-ψ' k u)| ≤ |(F (u : ℂ)).re - ψ' k u| := by
            rcases le_total 0 (-(F (u : ℂ)).re) with a | a <;>
              rcases le_total 0 (-ψ' k u) with b | b
            · rw [max_eq_right a, max_eq_right b,
                show -(F (u : ℂ)).re - -ψ' k u = -((F (u : ℂ)).re - ψ' k u) by ring, abs_neg]
            · rw [max_eq_right a, max_eq_left b, sub_zero, abs_of_nonneg a]
              linarith [neg_abs_le ((F (u : ℂ)).re - ψ' k u)]
            · rw [max_eq_left a, max_eq_right b, zero_sub, abs_neg, abs_of_nonneg b]
              linarith [le_abs_self ((F (u : ℂ)).re - ψ' k u)]
            · rw [max_eq_left a, max_eq_left b, sub_self, abs_zero]; exact abs_nonneg _
          exact lt_of_le_of_lt hlip h1
      have hlim := setIntegral_Icc_tendsto_of_tendstoUniformlyOn (by linarith : -R' ≤ R') hunif_m
        (hψ_int.mono fun k hk => (neg_part_integrable hk).integrableOn) hm_int.integrableOn
      have hexp_lim : Tendsto (fun k => C_l * (Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)) +
          Real.exp (-κ_l * c' k))) atTop
          (𝓝 (C_l * Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)))) := by
        have ht : Tendsto (fun k => Real.exp (-κ_l * c' k)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hκl) hc'_tend)
        simpa using (tendsto_const_nhds.add ht).const_mul C_l
      refine ge_of_tendsto (hlim.add hexp_lim) ?_
      have htl := hlobe_tail (R' / hankelBeta1) hr1
      rw [div_mul_cancel₀ _ hankelBeta1_pos.ne'] at htl
      filter_upwards [hc_pos, hf_cont, hf_int, hf_ne, hf_org, hf_org_le, hf_tail, hψ_int, hs_lt, htl] with
        k hc0 hck hink hnek horgk horglek htk hψk hsle htailk
      have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
      have hhalf := psi_neg_mass_ge_half hc0 hink hmass (by rw [← horgk]; exact horglek)
      have hmk := neg_part_integrable hψk
      have hleft0 : ∫ u in Iio (-R'), max 0 (-ψ' k u) = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun u hu => by
          have hnn := psi_nonneg_of_le_thresh hc0 htk hmass (le_trans (le_of_lt hu) hsle)
          exact max_eq_left (by linarith)
      have hright_le : ∫ u in Ioi R', max 0 (-ψ' k u) ≤ ∫ u in Ioi R', |ψ' k u| :=
        setIntegral_mono_on hmk.integrableOn hψk.abs.integrableOn measurableSet_Ioi fun u _ =>
          max_le (abs_nonneg _) (neg_le_abs _)
      have hdecomp : (∫ u in Iio (-R'), max 0 (-ψ' k u)) + (∫ u in Icc (-R') R', max 0 (-ψ' k u)) +
          (∫ u in Ioi R', max 0 (-ψ' k u)) = ∫ u : ℝ, max 0 (-ψ' k u) := by
        have h12 : (∫ u in Iio (-R'), max 0 (-ψ' k u)) + ∫ u in Icc (-R') R', max 0 (-ψ' k u) =
            ∫ u in Iic R', max 0 (-ψ' k u) := by
          rw [← setIntegral_union (Set.disjoint_left.mpr fun _ hx1 hx2 => not_le.mpr (mem_Iio.mp hx1) (mem_Icc.mp hx2).1)
            measurableSet_Icc hmk.integrableOn hmk.integrableOn, Iio_union_Icc_eq_Iic (by linarith)]
        rw [h12, ← compl_Iic]
        exact integral_add_compl measurableSet_Iic hmk
      linarith
    have htend : Tendsto (fun R' : ℝ => (∫ u in Icc (-R') R', max 0 (-(F (u : ℂ)).re)) +
        C_l * Real.exp (-5 * (R' / hankelBeta1) ^ (3 / 2 : ℝ)))
        atTop (𝓝 ((∫ u : ℝ, max 0 (-(F (u : ℂ)).re)) + 0)) :=
      (integral_Icc_tendsto hm_int).add hR0_tend
    rw [add_zero] at htend
    exact ge_of_tendsto htend ((eventually_ge_atTop R0).mono hle_R)
  have hF_ne : ∃ z : ℂ, -F z ≠ 0 := by
    by_contra h0; push Not at h0
    have hFz : ∀ u : ℝ, max 0 (-(F (u : ℂ)).re) = 0 := fun u => by
      have hz := neg_eq_zero.mp (h0 (u : ℂ))
      rw [hz]; simp
    simp_rw [hFz, integral_zero] at hF_neg_half
    linarith
  obtain ⟨b, _, hH_eq, hnz⟩ := D.uniqueness (H := fun z => -F z) hFd.neg hFi.neg hC
    (fun z => by simpa using hFb z) (fun u => neg_eq_zero.mpr (hFreal u))
    (by rw [integral_neg, Complex.neg_re, neg_nonneg]; exact le_of_eq_of_le (integral_re hFi).symm hF_int_le)
    (fun t ht _ => by rw [Complex.neg_re]; linarith [hF_sites t ht ‹_›])
    (fun u hu => by rw [Complex.neg_re]; linarith [hF_nonneg_band u (hu.trans htm_le_band)])
  obtain ⟨hb_pos, hb_ratio, hH_deriv⟩ := hnz hF_ne
  have hF_eq : ∀ z : ℂ, F z = (b : ℂ) * D.G z := fun z => by
    have hz := hH_eq z; linear_combination -hz
  have hsLim_eq : sLim = -(D.tm / hankelBeta1) := by
    by_contra hne
    have hlt : D.tm < -hankelBeta1 * sLim := lt_of_le_of_ne htm_le_band fun heq => hne <| by
      field_simp [hankelBeta1_pos.ne'] at heq ⊢; linarith
    have hF_tm : (F (D.tm : ℂ)).re = 0 := by
      rw [hF_eq, D.G_eq_zero_on_S D.tm D.tm_mem, mul_zero, Complex.zero_re]
    have hloc_min : IsLocalMin (fun u : ℝ => (F (u : ℂ)).re) D.tm := by
      filter_upwards [Iio_mem_nhds hlt] with u hu
      rw [hF_tm]; exact hF_nonneg_band u (le_of_lt hu)
    have hd_re : HasDerivAt (fun u : ℝ => (F (u : ℂ)).re) (deriv F (D.tm : ℂ)).re D.tm :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm
        (by simpa using (hFd (D.tm : ℂ)).hasDerivAt.comp_ofReal)
    have hd_im : HasDerivAt (fun u : ℝ => (F (u : ℂ)).im) (deriv F (D.tm : ℂ)).im D.tm :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt D.tm
        (by simpa using (hFd (D.tm : ℂ)).hasDerivAt.comp_ofReal)
    have him0 : (deriv F (D.tm : ℂ)).im = 0 := by
      have e : (fun u : ℝ => (F (u : ℂ)).im) = fun _ => 0 := funext hFreal
      rw [e] at hd_im
      exact hd_im.unique (hasDerivAt_const D.tm 0)
    have hre0 : (deriv F (D.tm : ℂ)).re = 0 := by
      rw [← hd_re.deriv]
      exact hloc_min.deriv_eq_zero
    have hdH0 : deriv (fun z => -F z) (D.tm : ℂ) = 0 := by
      have hdH : HasDerivAt (fun z => -F z) (-deriv F (D.tm : ℂ)) (D.tm : ℂ) :=
        (hFd (D.tm : ℂ)).hasDerivAt.neg
      rw [hdH.deriv, show deriv F (D.tm : ℂ) = 0 from Complex.ext hre0 him0, neg_zero]
    exact hH_deriv D.tm D.tm_mem hdH0
  have hF_zero : ∫ u : ℝ, (F (u : ℂ)).re = 0 := by
    have heq : (fun u : ℝ => (F (u : ℂ)).re) = fun u : ℝ => b * (D.G (u : ℂ)).re := by
      ext u; rw [hF_eq (u : ℂ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [heq, integral_const_mul]
    exact mul_eq_zero_of_right b ((integral_re D.G_int).trans (by rw [D.G_integral_zero]; rfl))
  have hF_l1_eq : ∫ u : ℝ, ‖F (u : ℂ)‖ = 2 * ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) := by
    have hre_int : Integrable (fun u : ℝ => (F (u : ℂ)).re) := hFi.re
    have hre_neg : Integrable (fun u : ℝ => -(F (u : ℂ)).re) := hre_int.neg
    have hp_int : Integrable (fun u : ℝ => max 0 (F (u : ℂ)).re) :=
      (neg_part_integrable hre_neg).congr (Eventually.of_forall fun u => by simp)
    have hm_int : Integrable (fun u : ℝ => max 0 (-(F (u : ℂ)).re)) :=
      neg_part_integrable hre_int
    have hsp1 : (fun u : ℝ => (F (u : ℂ)).re) = fun u : ℝ => max 0 (F (u : ℂ)).re - max 0 (-(F (u : ℂ)).re) := by
      ext u; rcases le_total 0 (F (u : ℂ)).re with h | h <;> simp [h]
    have hsp2 : (fun u : ℝ => ‖F (u : ℂ)‖) = fun u : ℝ => max 0 (F (u : ℂ)).re + max 0 (-(F (u : ℂ)).re) := by
      ext u
      have hcast : F (u : ℂ) = ((F (u : ℂ)).re : ℂ) := Complex.ext rfl (hFreal u)
      conv_lhs => rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      rcases le_total 0 (F (u : ℂ)).re with h | h <;> simp [abs_of_nonneg, abs_of_nonpos, h]
    have hp_eq : ∫ u : ℝ, max 0 (F (u : ℂ)).re = ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) := by
      have h0 : ∫ u : ℝ, (max 0 (F (u : ℂ)).re - max 0 (-(F (u : ℂ)).re)) = 0 := by
        calc ∫ u : ℝ, (max 0 (F (u : ℂ)).re - max 0 (-(F (u : ℂ)).re))
            = ∫ u : ℝ, (F (u : ℂ)).re := by
              refine integral_congr_ae (Eventually.of_forall fun u => ?_)
              rcases le_total 0 (F (u : ℂ)).re with h | h <;> simp [h]
          _ = 0 := hF_zero
      rw [integral_sub hp_int hm_int] at h0; linarith
    rw [hsp2, integral_add hp_int hm_int, hp_eq]; ring
  have hF_l1_one : ∫ u : ℝ, ‖F (u : ℂ)‖ = 1 := by linarith
  have hb_val : b = (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ := by
    have hnorm : (fun u : ℝ => ‖-F (u : ℂ)‖) = fun u : ℝ => ‖F (u : ℂ)‖ := funext fun _ => norm_neg _
    rw [hb_ratio, hnorm, hF_l1_one, one_div]
  have hF_normG : (fun u : ℝ => (F (u : ℂ)).re) = D.normG := by
    ext u
    rw [hF_eq (u : ℂ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hb_val, HermiteBiehlerData.normG, inv_mul_eq_div]
  rw [hF_normG] at hΨ_lim
  exact ⟨ms, sLim, hms, hs_lim, hΨ_lim, hsLim_eq⟩

/-- **Theorem 7.5 (`gt:7.5` / `thm:radial-rigidity`), Part 1 (`EReal` `liminf`)**:
`liminf_{c → ∞} c^{-1/3} (T_c - c / π²) ≥ -t_m / β₁` for every fixed Hermite–Biehler level. -/
theorem radial_rigidity_liminf_ereal {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D) :
    (-(D.tm / hankelBeta1) : EReal) ≤
      Filter.liminf (fun n => (((R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) : ℝ) : EReal)) p := by
  have hev : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in p, -(D.tm / hankelBeta1) - ε ≤ (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) := by
    intro ε hε
    by_contra hnot
    rw [Filter.not_eventually] at hnot
    simp only [not_le] at hnot
    obtain ⟨ns, hns, hlt⟩ := exists_seq_forall_of_frequently hnot
    obtain ⟨ms, sLim, _, hs_lim, _, hs_eq⟩ := R.subseq_extremal ns hns
      ⟨-(D.tm / hankelBeta1) - ε, fun k => (hlt k).le⟩
      (fun δ hδ => Eventually.of_forall fun k => (hlt k).le.trans (by linarith))
    have hs_le : sLim ≤ -(D.tm / hankelBeta1) - ε :=
      le_of_tendsto hs_lim (Eventually.of_forall fun k => (hlt (ms k)).le)
    linarith
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hxL, hxA⟩ := EReal.exists_between_coe_real hlt
  have h1 := hev (-(D.tm / hankelBeta1) - x) (sub_pos.mpr (EReal.coe_lt_coe_iff.mp hxA))
  have h1' : ∀ᶠ n in p, x ≤ (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) :=
    h1.mono fun _ hn => by linarith
  have hle : (x : EReal) ≤ _ := le_liminf_of_le (by isBoundedDefault)
    (h1'.mono fun _ hn => EReal.coe_le_coe_iff.mpr hn)
  exact absurd (hle.trans_lt hxL) (lt_irrefl _)

/-- **Theorem 7.5 (`gt:7.5` / `thm:radial-rigidity`), Part 1 (`ℝ`-valued `liminf`)**:
`-(t_m / β₁) ≤ liminf c^{-1/3} (T_c - c / π²)` when the rescaled threshold is cobounded above. -/
theorem radial_rigidity_liminf {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D)
    (hbdd : p.IsCoboundedUnder (· ≥ ·)
      (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2))) :
    -(D.tm / hankelBeta1) ≤
      Filter.liminf (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) p := by
  by_contra hlt
  push Not at hlt
  set L := Filter.liminf (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) p
  have hfreq : ∃ᶠ n in p, (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2) <
      (-(D.tm / hankelBeta1) + L) / 2 := by
    by_contra hnot
    rw [Filter.not_frequently] at hnot
    have hle := le_liminf_of_le hbdd (hnot.mono fun _ hn => not_lt.mp hn)
    linarith
  obtain ⟨ns, hns, hlt_s⟩ := exists_seq_forall_of_frequently hfreq
  obtain ⟨ms, sLim, _, hs_lim, _, hs_eq⟩ := R.subseq_extremal ns hns
    ⟨(-(D.tm / hankelBeta1) + L) / 2, fun k => (hlt_s k).le⟩
    (fun δ hδ => Eventually.of_forall fun k => (hlt_s k).le.trans (by linarith))
  have hs_le := le_of_tendsto hs_lim (Eventually.of_forall fun k => (hlt_s (ms k)).le)
  linarith

/-- **Theorem 7.5 (`gt:7.5` / `thm:radial-rigidity`), Part 2 (profile rigidity)**:
when `c^{-1/3} (T_c - c / π²) → -t_m / β₁`, `Ψ_{f_c, c} / M[f_c]` converges locally uniformly
on `ℝ` and in `L¹(ℝ)` to `G_N / ‖G_N‖₁` (via `Analysis.Scheffe`). -/
theorem radial_rigidity_profile {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D)
    (hAtt : Tendsto (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) p
      (𝓝 (-(D.tm / hankelBeta1)))) :
    TendstoLocallyUniformlyOn (fun n u => hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n))
      D.normG p univ ∧
    Tendsto (fun n => ∫ u : ℝ,
      |hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n) - D.normG u|) p (𝓝 0) := by
  have hloc : TendstoLocallyUniformlyOn
      (fun n u => hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n))
      D.normG p univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    by_contra hnot
    have hfreq : ∃ᶠ n in p, ∃ u ∈ K,
        ε ≤ dist (D.normG u) (hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)) := by
      rw [Filter.not_eventually] at hnot
      exact hnot.mono fun _ hn => by push Not at hn; exact hn
    obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently hfreq
    have hlt1 := (hAtt.comp hns).eventually (eventually_lt_nhds (by linarith :
      -(D.tm / hankelBeta1) < -(D.tm / hankelBeta1) + 1))
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hlt1
    let ns' : ℕ → ι := fun k => ns (k + k₀)
    have hns' : Tendsto ns' atTop p := hns.comp (tendsto_add_atTop_nat k₀)
    obtain ⟨ms, _, _, _, hΨ_unif, -⟩ := R.subseq_extremal ns' hns'
      ⟨-(D.tm / hankelBeta1) + 1, fun k => (hk₀ (k + k₀) (by omega)).le⟩
      (fun δ hδ => (hAtt.comp hns').eventually (eventually_le_nhds (by linarith)))
    have hev := Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_unif K (subset_univ K) hK) ε hε
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
    obtain ⟨u, huK, hubad⟩ := hbad (ms j₀ + k₀)
    linarith [hj₀ j₀ le_rfl u huK]
  have hL1 : Tendsto (fun n => ∫ u : ℝ,
      |hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n) - D.normG u|) p (𝓝 0) := by
    let ψ : ι → ℝ → ℝ := fun n u => hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)
    have hf_int : ∀ᶠ n in p, Integrable (ψ n) := by
      filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_int] with n hc0 hint
      exact ((integrable_hankelWindowProfile_iff hc0 _).mpr hint).div_const _
    have hae : ∀ᵐ u ∂volume, Tendsto (fun n => ψ n u) p (𝓝 (D.normG u)) :=
      Eventually.of_forall fun u => hloc.tendsto_at (mem_univ u)
    have hnorm : Tendsto (fun n => ∫ u : ℝ, ‖ψ n u‖) p (𝓝 (∫ u : ℝ, ‖D.normG u‖)) := by
      have hG : ∫ u : ℝ, ‖D.normG u‖ = 1 := by
        simpa [Real.norm_eq_abs] using D.normG_abs_integral
      rw [hG]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_cont, R.f_int, R.f_ne] with
        n hc0 hck hink hnek
      have hmass := hankelMass_pos_of_continuousOn hc0 hck hink hnek
      have heq : (fun u => ‖ψ n u‖) = fun u => |hankelWindowProfile (R.c n) (R.f n) u| / hankelMass (R.c n) (R.f n) := by
        ext u; dsimp [ψ]; rw [abs_div, abs_of_pos hmass]
      rw [heq, integral_div, integral_abs_hankelWindowProfile hc0 (R.f n), div_self hmass.ne']
    simpa only [Real.norm_eq_abs] using
      tendsto_integral_norm_sub_of_tendsto_ae hf_int D.normG_integrable hae hnorm
  exact ⟨hloc, hL1⟩

/-- **Theorem 7.5 (`gt:7.5` / `thm:radial-rigidity`), Part 3 (origin vanishing)**:
when `c^{-1/3} (T_c - c / π²) → -t_m / β₁`, `f_c(0) / M[f_c] → 0`. -/
theorem radial_rigidity_origin {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (R : RadialRigidityPackage ι p D)
    (hAtt : Tendsto (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) p
      (𝓝 (-(D.tm / hankelBeta1)))) :
    Tendsto (fun n => R.f n 0 / hankelMass (R.c n) (R.f n)) p (𝓝 0) := by
  have hL1 := (radial_rigidity_profile R hAtt).2
  refine squeeze_zero_norm' ?_ hL1
  filter_upwards [R.c_tendsto.eventually (eventually_gt_atTop 0), R.f_cont, R.f_int, R.f_ne,
    R.f_origin_eq] with n hc0 hck hink hnek horg
  have hψ_int : Integrable (fun u => hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n)) :=
    ((integrable_hankelWindowProfile_iff hc0 _).mpr hink).div_const _
  have hval : R.eps * (R.f n 0 / hankelMass (R.c n) (R.f n)) =
      ∫ u : ℝ, (hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n) - D.normG u) := by
    rw [integral_sub hψ_int D.normG_integrable, D.normG_integral, sub_zero,
      integral_div, integral_hankelWindowProfile hc0 (R.f n), ← horg, mul_div_assoc']
  have hnorm : ‖R.f n 0 / hankelMass (R.c n) (R.f n)‖ =
      |R.eps * (R.f n 0 / hankelMass (R.c n) (R.f n))| := by
    rw [Real.norm_eq_abs, abs_mul]
    rcases R.eps_sign with h | h <;> simp [h]
  rw [hnorm, hval]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (fun u => hankelWindowProfile (R.c n) (R.f n) u / hankelMass (R.c n) (R.f n) - D.normG u)

private lemma normG_tail_bound (D : HermiteBiehlerData) :
    ∃ M : ℝ, 0 < M ∧ ∀ U : ℝ, 0 ≤ U →
      ∫ u in Ici U, |D.normG u| ≤ M * Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, ν, hC, hGb⟩ := D.G_env
  let C' := C / ∫ x : ℝ, ‖D.G (x : ℂ)‖
  have hC' : 0 ≤ C' := div_nonneg hC D.G_l1_pos.le
  have hint_tail : IntegrableOn (fun u : ℝ => C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) (Ici 0) := by
    have hpow : Tendsto (fun u : ℝ => (1 + u) ^ ν * Real.exp (-(1 / 2 : ℝ) * (1 + u))) atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν (1 / 2) (by norm_num)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_id)
      exact h1.congr' (Eventually.of_forall fun u => by simp [add_comm])
    obtain ⟨A, hA⟩ := eventually_atTop.mp (hpow.eventually (eventually_lt_nhds zero_lt_one))
    let A' := max A 1
    have h1 : IntegrableOn (fun u : ℝ => C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) (Icc 0 A') :=
      ((continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
        fun u hu => Or.inl (by linarith [(mem_Icc.mp hu).1] : 0 < 1 + u).ne')).mul
        ((continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2)).neg.rexp)).integrableOn_Icc
    have h2 : IntegrableOn (fun u : ℝ => C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) (Ioi A') := by
      have hdom : IntegrableOn (fun u : ℝ => (C' * Real.exp (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * u)) (Ioi A') :=
        (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) A').const_mul _
      refine hdom.mono' (ContinuousOn.aestronglyMeasurable (by
        refine (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
          fun u hu => Or.inl (by linarith [le_max_right A 1, mem_Ioi.mp hu] : 0 < 1 + u).ne')).mul
          ((continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2)).neg.rexp))
        measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
      have huA : A ≤ u := (le_max_left A 1).trans (le_of_lt hu)
      have hu1 : 1 ≤ u := (le_max_right A 1).trans (le_of_lt hu)
      have hu32 : u ≤ u ^ (3 / 2 : ℝ) := by
        calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
          _ ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      have hexp : Real.exp (-u ^ (3 / 2 : ℝ)) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
      have hexp2 : Real.exp (-u) = Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * (1 + u)) *
          Real.exp (-(1 / 2 : ℝ) * u) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      have hnn : 0 ≤ (1 + u) ^ ν := Real.rpow_nonneg (by linarith) _
      rw [Real.norm_of_nonneg (by positivity)]
      calc C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))
          ≤ C' * (1 + u) ^ ν * (Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * (1 + u)) *
              Real.exp (-(1 / 2 : ℝ) * u)) := by
            gcongr; exact hexp.trans_eq hexp2
        _ = (C' * Real.exp (1 / 2 : ℝ)) * ((1 + u) ^ ν * Real.exp (-(1 / 2 : ℝ) * (1 + u))) *
              Real.exp (-(1 / 2 : ℝ) * u) := by ring
        _ ≤ (C' * Real.exp (1 / 2 : ℝ)) * 1 * Real.exp (-(1 / 2 : ℝ) * u) := by
            gcongr; exact (hA u huA).le
        _ = (C' * Real.exp (1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ) * u) := by ring
    rw [← Set.Icc_union_Ioi_eq_Ici (by linarith [le_max_right A 1] : (0 : ℝ) ≤ A')]
    exact h1.union h2
  let M := (∫ u in Ici (0 : ℝ), C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) + 1
  have hM : 0 < M := by
    have hM_nonneg : 0 ≤ ∫ u in Ici (0 : ℝ), C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ)) :=
      setIntegral_nonneg measurableSet_Ici fun u (hu : (0 : ℝ) ≤ u) =>
        mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le
    dsimp [M]; linarith
  refine ⟨M, hM, fun U hU => ?_⟩
  have hpt : ∀ u ∈ Ici U, |D.normG u| ≤
      Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) * (C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 ≤ u := hU.trans hu
    have hnorm : |D.normG u| = ‖D.G (u : ℂ)‖ / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
      unfold HermiteBiehlerData.normG
      have hc : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
      rw [abs_div, abs_of_pos D.G_l1_pos]
      congr 1; conv_rhs => rw [hc, Complex.norm_real, Real.norm_eq_abs]
    have henv : airyEnv (u : ℂ) = Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
      unfold airyEnv
      have : ((u : ℂ) ^ (3 / 2 : ℂ)).re = u ^ (3 / 2 : ℝ) := by
        have := Complex.ofReal_cpow hu0 (3 / 2 : ℝ)
        rw [show (((3 / 2 : ℝ) : ℝ) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
        rw [← this, Complex.ofReal_re]
      rw [this]
    have hGb_u := hGb (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, henv] at hGb_u
    have hpow_le : U ^ (3 / 2 : ℝ) ≤ u ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hU hu (by norm_num)
    have hexp : Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) ≤
        Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) * Real.exp (-u ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    rw [hnorm, div_eq_mul_inv]
    calc ‖D.G (u : ℂ)‖ * (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹
        ≤ (C * (1 + u) ^ ν * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) * (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ :=
          mul_le_mul_of_nonneg_right hGb_u (inv_nonneg.mpr D.G_l1_pos.le)
      _ = C' * (1 + u) ^ ν * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by dsimp [C']; ring
      _ ≤ C' * (1 + u) ^ ν * (Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) * Real.exp (-u ^ (3 / 2 : ℝ))) := by
          gcongr
      _ = Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) * (C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) := by ring
  have h1 : ∫ u in Ici U, |D.normG u| ≤
      ∫ u in Ici U, Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) * (C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ))) :=
    setIntegral_mono_on D.normG_integrable.abs.integrableOn
      ((hint_tail.mono_set (Ici_subset_Ici.mpr hU)).const_mul _) measurableSet_Ici hpt
  have h2 : ∫ u in Ici U, C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ)) ≤ M := by
    have hsub := setIntegral_mono_set hint_tail (ae_restrict_of_forall_mem measurableSet_Ici fun u (hu : 0 ≤ u) =>
      mul_nonneg (mul_nonneg hC' (Real.rpow_nonneg (by linarith) _)) (Real.exp_pos _).le)
      (Eventually.of_forall fun _ (hu : _ ∈ Ici U) => hU.trans hu)
    dsimp [M]; linarith
  rw [integral_const_mul] at h1
  calc ∫ u in Ici U, |D.normG u| ≤ Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) *
        ∫ u in Ici U, C' * (1 + u) ^ ν * Real.exp (-u ^ (3 / 2 : ℝ)) := h1
    _ ≤ Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) * M :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = M * Real.exp (-(1 / 3 : ℝ) * U ^ (3 / 2 : ℝ)) := by ring

/-- **Non-vacuity of Theorem 7.5** for every Hermite–Biehler configuration `D`:
constructing a family `f_n` matching `D.normG` on `[2, ∞)` with a compact `[1, 2]` zero-mean
correction, attaining `c^{-1/3} (T_c - c / π²) = -t_m / β₁`. -/
theorem radialRigidityPackage_nonvacuous (D : HermiteBiehlerData) :
    ∃ R : RadialRigidityPackage ℕ atTop D,
      Tendsto (fun n => (R.c n) ^ (-(1 / 3 : ℝ)) * (R.T n - R.c n / π ^ 2)) atTop
        (𝓝 (-(D.tm / hankelBeta1))) := by
  let c : ℕ → ℝ := fun n => (n : ℝ) + 100
  let T : ℕ → ℝ := fun n => c n / π ^ 2 - (D.tm / hankelBeta1) * (c n) ^ (1 / 3 : ℝ)
  let Tsite : D.S → ℕ → ℝ := fun t n => c n / π ^ 2 - ((t : ℝ) / hankelBeta1) * (c n) ^ (1 / 3 : ℝ)
  let uMap : ℕ → ℝ → ℝ := fun n Δ => hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - Δ)
  let χ : ℝ → ℝ := fun Δ => max 0 (min 1 (Δ - 1))
  let bump : ℝ → ℝ := fun Δ => max 0 (1 - |2 * Δ - 3|)
  let gBase : ℕ → ℝ → ℝ := fun n Δ =>
    if 1 ≤ Δ then χ Δ * (hankelBeta1 / (c n) ^ (1 / 3 : ℝ)) * D.normG (uMap n Δ) / hankelRho0 (c n) Δ
    else 0
  let W : ℕ → ℝ := fun n => ∫ Δ in Ioi (0 : ℝ), bump Δ * hankelRho0 (c n) Δ
  let I_tail : ℕ → ℝ := fun n => ∫ Δ in Ioi (0 : ℝ), gBase n Δ * hankelRho0 (c n) Δ
  let f : ℕ → ℝ → ℝ := fun n Δ => gBase n Δ - (I_tail n / W n) * bump Δ
  have hc_pos : ∀ n : ℕ, 0 < c n := fun n => by dsimp [c]; positivity
  have hc_tend : Tendsto c atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hχ_cont : Continuous χ := continuous_const.max (continuous_const.min (continuous_id.sub continuous_const))
  have hχ_bounds : ∀ Δ : ℝ, 0 ≤ χ Δ ∧ χ Δ ≤ 1 := fun Δ =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hbump_cont : Continuous bump := continuous_const.max (continuous_const.sub (continuous_abs.comp
    ((continuous_const.mul continuous_id).sub continuous_const)))
  have hbump_supp : ∀ Δ : ℝ, Δ ∉ Ioo (1 : ℝ) 2 → bump Δ = 0 := fun Δ hΔ => by
    dsimp [bump]; rw [max_eq_left]; rw [mem_Ioo, not_and_or, not_lt, not_lt] at hΔ
    rcases hΔ with h | h <;> [rw [abs_of_nonpos (by linarith)]; rw [abs_of_nonneg (by linarith)]] <;> linarith
  have hbump_nn : ∀ Δ : ℝ, 0 ≤ bump Δ := fun Δ => le_max_left _ _
  have hW_int : ∀ n : ℕ, IntegrableOn (fun Δ => bump Δ * hankelRho0 (c n) Δ) (Ioi 0) := fun n => by
    have hIcc : IntegrableOn (fun Δ => bump Δ * hankelRho0 (c n) Δ) (Icc 1 2) :=
      (hbump_cont.continuousOn.mul ((continuousOn_hankelRho0 (c n)).mono
        fun _ hx => mem_Ioi.mpr (by linarith [(mem_Icc.mp hx).1]))).integrableOn_Icc
    have hind : Integrable (fun Δ => (Icc (1 : ℝ) 2).indicator (fun Δ => bump Δ * hankelRho0 (c n) Δ) Δ) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hIcc
    refine hind.integrableOn.congr_fun (fun Δ _ => ?_) measurableSet_Ioi
    dsimp only
    by_cases h : Δ ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h, hbump_supp Δ (fun hm => h (Ioo_subset_Icc_self hm)), zero_mul]
  have hW_pos : ∀ n : ℕ, 0 < W n := fun n => by
    have hcont : ContinuousOn (fun Δ => bump Δ * hankelRho0 (c n) Δ) (Ioi 0) :=
      hbump_cont.continuousOn.mul (continuousOn_hankelRho0 (c n))
    have hopen : IsOpen {Δ ∈ Ioi (0 : ℝ) | 0 < bump Δ * hankelRho0 (c n) Δ} :=
      hcont.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
    have hmem : (3 / 2 : ℝ) ∈ {Δ ∈ Ioi (0 : ℝ) | 0 < bump Δ * hankelRho0 (c n) Δ} := by
      refine ⟨by norm_num, mul_pos ?_ (hankelRho0_pos (hc_pos n) (by norm_num))⟩
      dsimp [bump]; norm_num
    exact (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ =>
        mul_nonneg (hbump_nn Δ) (hankelRho0_nonneg (hc_pos n) (le_of_lt hΔ)))
      (hW_int n)).mpr (lt_of_lt_of_le (hopen.measure_pos volume ⟨3 / 2, hmem⟩)
        (measure_mono fun Δ h => ⟨Function.mem_support.mpr h.2.ne', h.1⟩))
  have hg_cont : ∀ n : ℕ, ContinuousOn (gBase n) (Ici 0) := fun n => by
    have hpos : ContinuousOn (fun Δ => χ Δ * (hankelBeta1 / (c n) ^ (1 / 3 : ℝ)) *
        D.normG (uMap n Δ) / hankelRho0 (c n) Δ) (Ioi (1 / 2 : ℝ)) := by
      refine (((hχ_cont.continuousOn.mul continuousOn_const).mul
        (D.normG_continuous.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn).div
        ((continuousOn_hankelRho0 (c n)).mono fun _ hx => mem_Ioi.mpr (by linarith [mem_Ioi.mp hx]))
        fun _ hx => (hankelRho0_pos (hc_pos n) (by linarith [mem_Ioi.mp hx])).ne')
    have hIio : ContinuousOn (gBase n) (Iio (1 : ℝ)) :=
      (continuousOn_const : ContinuousOn (fun _ => (0 : ℝ)) (Iio (1 : ℝ))).congr fun (Δ : ℝ) hΔ =>
        show gBase n Δ = 0 from by
          dsimp [gBase]; simp [not_le.mpr (mem_Iio.mp hΔ)]
    have hIoi : ContinuousOn (gBase n) (Ioi (1 / 2 : ℝ)) :=
      hpos.congr fun Δ hΔ => by
        by_cases h1 : 1 ≤ Δ <;> simp only [gBase, h1, ↓reduceIte]
        have hχ0 : χ Δ = 0 := by
          dsimp [χ]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
        rw [hχ0, zero_mul, zero_mul, zero_div]
    intro Δ _
    by_cases h : Δ < 1
    · exact (hIio.continuousAt (isOpen_Iio.mem_nhds h)).continuousWithinAt
    · exact (hIoi.continuousAt (isOpen_Ioi.mem_nhds (by linarith : (1 / 2 : ℝ) < Δ))).continuousWithinAt
  have hf_cont : ∀ n : ℕ, ContinuousOn (f n) (Ici 0) := fun n =>
    (hg_cont n).sub (continuousOn_const.mul hbump_cont.continuousOn)
  have hg_rho : ∀ n : ℕ, ∀ Δ ∈ Ioi (0 : ℝ),
      gBase n Δ * hankelRho0 (c n) Δ =
        (Ici (1 : ℝ)).indicator (fun d => χ d * (hankelBeta1 / (c n) ^ (1 / 3 : ℝ)) * D.normG (uMap n d)) Δ := by
    intro n Δ _
    dsimp [gBase]
    by_cases h1 : 1 ≤ Δ
    · split_ifs
      rw [indicator_of_mem (mem_Ici.mpr h1), div_mul_cancel₀ _ (hankelRho0_pos (hc_pos n) (by linarith)).ne']
    · split_ifs
      rw [indicator_of_notMem (mem_Ici.not.mpr h1), zero_mul]
  have hg_int : ∀ n : ℕ, IntegrableOn (fun Δ => gBase n Δ * hankelRho0 (c n) Δ) (Ioi 0) := fun n => by
    have hc0 := hc_pos n
    let a := (c n) ^ (1 / 3 : ℝ) / hankelBeta1
    have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc0 _) hankelBeta1_pos
    have hD_cov : Integrable (fun Δ : ℝ => (hankelBeta1 / (c n) ^ (1 / 3 : ℝ)) * D.normG (uMap n Δ)) := by
      have h1 := ((D.normG_integrable.comp_add_right (a⁻¹ * (c n / π ^ 2))).comp_mul_left'
        (neg_ne_zero.mpr (inv_ne_zero ha.ne'))).const_mul a⁻¹
      refine h1.congr (Eventually.of_forall fun Δ => ?_)
      have hinv : a⁻¹ = hankelBeta1 / (c n) ^ (1 / 3 : ℝ) := by dsimp [a]; rw [inv_div]
      dsimp only
      rw [hinv]
      congr 2
      dsimp [uMap]
      rw [Real.rpow_neg hc0.le (1 / 3 : ℝ), inv_eq_one_div]
      ring
    have hdom : IntegrableOn (fun Δ => (hankelBeta1 / (c n) ^ (1 / 3 : ℝ)) * |D.normG (uMap n Δ)|) (Ioi 0) :=
      hD_cov.norm.integrableOn.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ _ => by
        dsimp only
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hankelBeta1_pos (Real.rpow_pos_of_pos hc0 _))])
    refine hdom.mono' (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ => ?_)
    · exact ((hg_cont n).mono Ioi_subset_Ici_self).mul (continuousOn_hankelRho0 (c n))
    · rw [hg_rho n Δ hΔ]
      by_cases h1 : 1 ≤ Δ
      · rw [indicator_of_mem (mem_Ici.mpr h1), Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (hχ_bounds Δ).1,
          abs_of_pos (div_pos hankelBeta1_pos (Real.rpow_pos_of_pos hc0 _)), mul_assoc]
        exact mul_le_of_le_one_left (mul_nonneg (div_pos hankelBeta1_pos
          (Real.rpow_pos_of_pos hc0 _)).le (abs_nonneg _)) (hχ_bounds Δ).2
      · rw [indicator_of_notMem (mem_Ici.not.mpr h1), norm_zero]
        exact mul_nonneg (div_pos hankelBeta1_pos (Real.rpow_pos_of_pos hc0 _)).le (abs_nonneg _)
  have hf_int : ∀ n : ℕ, IntegrableOn (fun Δ => f n Δ * hankelRho0 (c n) Δ) (Ioi 0) := fun n => by
    have heq : (fun Δ => f n Δ * hankelRho0 (c n) Δ) =
        fun Δ => gBase n Δ * hankelRho0 (c n) Δ - (I_tail n / W n) * (bump Δ * hankelRho0 (c n) Δ) := by
      ext Δ; dsimp [f]; ring
    rw [heq]
    exact (hg_int n).sub ((hW_int n).const_mul _)
  have hprof_g : ∀ n : ℕ, ∀ u : ℝ,
      hankelWindowProfile (c n) (gBase n) u =
        if 1 ≤ c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) then
          χ (c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)) * D.normG u
        else 0 := by
    intro n u
    unfold hankelWindowProfile; dsimp only
    set Δ := c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)
    by_cases h1 : 1 ≤ Δ
    · have h0 : 0 < Δ := by linarith
      have hc0 := hc_pos n
      have hu_eq : uMap n Δ = u := by
        dsimp [uMap, Δ]
        rw [Real.rpow_neg hc0.le (1 / 3 : ℝ)]
        field_simp [hankelBeta1_pos.ne', (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)).ne']; ring
      split_ifs
      rw [hg_rho n Δ h0, indicator_of_mem (mem_Ici.mpr h1), hu_eq]
      calc (c n ^ (1 / 3 : ℝ) / hankelBeta1) * (χ Δ * (hankelBeta1 / c n ^ (1 / 3 : ℝ)) * D.normG u)
          = (c n ^ (1 / 3 : ℝ) / c n ^ (1 / 3 : ℝ)) * (hankelBeta1 / hankelBeta1) * (χ Δ * D.normG u) := by ring
        _ = χ Δ * D.normG u := by
            rw [div_self (Real.rpow_pos_of_pos hc0 _).ne', div_self hankelBeta1_pos.ne']; ring
    · by_cases h0 : 0 < Δ
      · split_ifs
        rw [hg_rho n Δ h0, indicator_of_notMem (mem_Ici.not.mpr h1), mul_zero]
      · split_ifs; rfl
  obtain ⟨M_g, hMg, htail_g⟩ := normG_tail_bound D
  let κ₀ : ℝ := (1 / 3 : ℝ) * (hankelBeta1 / (2 * π ^ 2)) ^ (3 / 2 : ℝ)
  have hκ₀ : 0 < κ₀ := mul_pos (by norm_num) (Real.rpow_pos_of_pos (div_pos hankelBeta1_pos (by positivity)) _)
  let U : ℕ → ℝ := fun n => hankelBeta1 / (2 * π ^ 2) * (c n) ^ (2 / 3 : ℝ)
  have hu2_ge : ∀ᶠ n in atTop, U n ≤ uMap n 2 := by
    filter_upwards [hc_tend.eventually (eventually_ge_atTop (4 * π ^ 2))] with n hcn
    have hc0 := hc_pos n
    have h1 : c n / (2 * π ^ 2) ≤ c n / π ^ 2 - 2 := by
      have h4pi : 4 ≤ c n / π ^ 2 := (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr hcn
      rw [show c n / (2 * π ^ 2) = (c n / π ^ 2) / 2 by ring]
      linarith
    have h2 : (c n) ^ (-(1 / 3 : ℝ)) * (c n / (2 * π ^ 2)) = (c n) ^ (2 / 3 : ℝ) / (2 * π ^ 2) := by
      have h2_0 : (c n) ^ (-(1 / 3 : ℝ)) * c n = (c n) ^ (2 / 3 : ℝ) := by
        calc (c n) ^ (-(1 / 3 : ℝ)) * c n = (c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (c n) ^ (-(1 / 3 : ℝ) + 1) := (Real.rpow_add hc0 _ _).symm
          _ = (c n) ^ (2 / 3 : ℝ) := by norm_num
      rw [show (c n) ^ (-(1 / 3 : ℝ)) * (c n / (2 * π ^ 2)) =
        ((c n) ^ (-(1 / 3 : ℝ)) * c n) / (2 * π ^ 2) by ring, h2_0]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hc0.le (-(1 / 3 : ℝ)))
    have h4 := mul_le_mul_of_nonneg_left (h2.symm ▸ h3) hankelBeta1_pos.le
    calc U n = hankelBeta1 * ((c n) ^ (2 / 3 : ℝ) / (2 * π ^ 2)) := by dsimp [U]; ring
      _ ≤ hankelBeta1 * ((c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - 2)) := h4
      _ = uMap n 2 := by dsimp [uMap]; ring
  have hL1_g : ∀ᶠ n in atTop,
      ∫ u : ℝ, |hankelWindowProfile (c n) (gBase n) u - D.normG u| ≤ M_g * Real.exp (-κ₀ * c n) := by
    filter_upwards [hu2_ge] with n hu2
    have hc0 := hc_pos n
    have hU0 : 0 ≤ U n := mul_nonneg (div_nonneg hankelBeta1_pos.le (by positivity)) (Real.rpow_nonneg hc0.le _)
    have hprof_g_int : Integrable (hankelWindowProfile (c n) (gBase n)) :=
      (integrable_hankelWindowProfile_iff hc0 _).mpr (hg_int n)
    have hpt_le : ∀ u : ℝ,
        |hankelWindowProfile (c n) (gBase n) u - D.normG u| ≤
          (Ici (U n)).indicator (fun x => |D.normG x|) u := by
      intro u
      by_cases hu : u ∈ Ici (U n)
      · rw [indicator_of_mem hu, hprof_g n u]
        split_ifs with h1
        · let d := c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)
          have hdiff : |χ d - 1| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ_bounds d).1], by linarith [(hχ_bounds d).2]⟩
          calc |χ d * D.normG u - D.normG u| = |χ d - 1| * |D.normG u| := by
                rw [← abs_mul]; congr 1; ring
            _ ≤ 1 * |D.normG u| := mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
            _ = |D.normG u| := one_mul _
        · simp
      · rw [indicator_of_notMem hu, hprof_g n u]
        have hu_le : u ≤ uMap n 2 := le_trans (le_of_not_ge fun h => hu (mem_Ici.mpr h)) hu2
        have hΔ2 : 2 ≤ c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) := by
          have hr := rpow_neg_one_third_mul_add hc0
          have hmul : u * (c n) ^ (1 / 3 : ℝ) / hankelBeta1 ≤ uMap n 2 * (c n) ^ (1 / 3 : ℝ) / hankelBeta1 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu_le (Real.rpow_nonneg hc0.le _)) hankelBeta1_pos.le
          have heq : uMap n 2 * (c n) ^ (1 / 3 : ℝ) / hankelBeta1 = c n / π ^ 2 - 2 := by
            dsimp [uMap]
            calc hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - 2) * (c n) ^ (1 / 3 : ℝ) / hankelBeta1
                = (hankelBeta1 / hankelBeta1) * ((c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ)) * (c n / π ^ 2 - 2) := by ring
              _ = c n / π ^ 2 - 2 := by rw [div_self hankelBeta1_pos.ne', hr]; ring
          linarith [show u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) = u * (c n) ^ (1 / 3 : ℝ) / hankelBeta1 by ring]
        have h1 : 1 ≤ c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) := by linarith
        have hχ1 : χ (c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)) = 1 := by
          dsimp [χ]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
        split_ifs
        rw [hχ1, one_mul, sub_self, abs_zero]
    have hint_ind : Integrable ((Ici (U n)).indicator (fun x => |D.normG x|)) :=
      D.normG_integrable.abs.indicator measurableSet_Ici
    have hint_diff : Integrable (fun u => |hankelWindowProfile (c n) (gBase n) u - D.normG u|) :=
      (hprof_g_int.sub D.normG_integrable).abs
    have hexp_eq : -(1 / 3 : ℝ) * (U n) ^ (3 / 2 : ℝ) = -κ₀ * c n := by
      dsimp [U, κ₀]
      rw [Real.mul_rpow (div_nonneg hankelBeta1_pos.le (by positivity)) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul hc0.le]
      norm_num; ring
    calc ∫ u : ℝ, |hankelWindowProfile (c n) (gBase n) u - D.normG u|
        ≤ ∫ u : ℝ, (Ici (U n)).indicator (fun x => |D.normG x|) u :=
          integral_mono hint_diff hint_ind hpt_le
      _ = ∫ u in Ici (U n), |D.normG u| := integral_indicator measurableSet_Ici
      _ ≤ M_g * Real.exp (-(1 / 3 : ℝ) * (U n) ^ (3 / 2 : ℝ)) := htail_g (U n) hU0
      _ = M_g * Real.exp (-κ₀ * c n) := by rw [hexp_eq]
  have hI_tail_bound : ∀ᶠ n in atTop, |I_tail n| ≤ M_g * Real.exp (-κ₀ * c n) := by
    filter_upwards [hL1_g] with n hL1
    have hc0 := hc_pos n
    have hprof_g_int : Integrable (hankelWindowProfile (c n) (gBase n)) :=
      (integrable_hankelWindowProfile_iff hc0 _).mpr (hg_int n)
    have hIt_eq : I_tail n = ∫ u : ℝ, (hankelWindowProfile (c n) (gBase n) u - D.normG u) := by
      rw [integral_sub hprof_g_int D.normG_integrable, D.normG_integral, sub_zero,
        integral_hankelWindowProfile hc0 (gBase n)]
    rw [hIt_eq]
    exact abs_integral_le_integral_abs.trans hL1
  have hmass_diff : ∀ n : ℕ, |hankelMass (c n) (f n) - hankelMass (c n) (gBase n)| ≤ |I_tail n| := by
    intro n
    have hc0 := hc_pos n
    have hm_f := abs_mul_rho0_integrableOn hc0 (hf_int n)
    have hm_g := abs_mul_rho0_integrableOn hc0 (hg_int n)
    have hdiff_eq : hankelMass (c n) (f n) - hankelMass (c n) (gBase n) =
        ∫ Δ in Ioi (0 : ℝ), (|f n Δ| * hankelRho0 (c n) Δ - |gBase n Δ| * hankelRho0 (c n) Δ) := by
      unfold hankelMass; exact (integral_sub hm_f hm_g).symm
    have hpt : ∀ Δ ∈ Ioi (0 : ℝ),
        |(|f n Δ| * hankelRho0 (c n) Δ - |gBase n Δ| * hankelRho0 (c n) Δ)| ≤
          (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) := by
      intro Δ hΔ
      have hr : 0 ≤ hankelRho0 (c n) Δ := hankelRho0_nonneg hc0 hΔ.le
      calc |(|f n Δ| * hankelRho0 (c n) Δ - |gBase n Δ| * hankelRho0 (c n) Δ)|
          = |(|f n Δ| - |gBase n Δ|)| * hankelRho0 (c n) Δ := by
            rw [← sub_mul, abs_mul, abs_of_nonneg hr]
        _ ≤ |f n Δ - gBase n Δ| * hankelRho0 (c n) Δ :=
            mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le _ _) hr
        _ = (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) := by
            have hd : f n Δ - gBase n Δ = -((I_tail n / W n) * bump Δ) := by dsimp [f]; ring
            rw [hd, abs_neg, abs_mul, abs_div, abs_of_pos (hW_pos n), abs_of_nonneg (hbump_nn Δ)]
            ring
    rw [hdiff_eq]
    calc |∫ Δ in Ioi (0 : ℝ), (|f n Δ| * hankelRho0 (c n) Δ - |gBase n Δ| * hankelRho0 (c n) Δ)|
        ≤ ∫ Δ in Ioi (0 : ℝ), |(|f n Δ| * hankelRho0 (c n) Δ - |gBase n Δ| * hankelRho0 (c n) Δ)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ Δ in Ioi (0 : ℝ), (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) :=
          setIntegral_mono_on (hm_f.sub hm_g).abs ((hW_int n).const_mul _) measurableSet_Ioi hpt
      _ = (|I_tail n| / W n) * W n := integral_const_mul _ _
      _ = |I_tail n| := div_mul_cancel₀ _ (hW_pos n).ne'
  have hmass_bound : ∀ᶠ n in atTop, |hankelMass (c n) (f n) - 1| ≤ 2 * M_g * Real.exp (-κ₀ * c n) := by
    filter_upwards [hI_tail_bound, hL1_g] with n hIt hL1
    have hc0 := hc_pos n
    have hprof_g_int : Integrable (hankelWindowProfile (c n) (gBase n)) :=
      (integrable_hankelWindowProfile_iff hc0 _).mpr (hg_int n)
    have hmg_1 : |hankelMass (c n) (gBase n) - 1| ≤ M_g * Real.exp (-κ₀ * c n) := by
      have heq : hankelMass (c n) (gBase n) - 1 =
          ∫ u : ℝ, (|hankelWindowProfile (c n) (gBase n) u| - |D.normG u|) := by
        rw [← integral_abs_hankelWindowProfile hc0 (gBase n), ← D.normG_abs_integral,
          ← integral_sub hprof_g_int.abs D.normG_integrable.abs]
      rw [heq]
      calc |∫ u : ℝ, (|hankelWindowProfile (c n) (gBase n) u| - |D.normG u|)|
          ≤ ∫ u : ℝ, |(|hankelWindowProfile (c n) (gBase n) u| - |D.normG u|)| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ u : ℝ, |hankelWindowProfile (c n) (gBase n) u - D.normG u| :=
            integral_mono (hprof_g_int.abs.sub D.normG_integrable.abs).abs
              (hprof_g_int.sub D.normG_integrable).abs (fun u => abs_abs_sub_abs_le _ _)
        _ ≤ M_g * Real.exp (-κ₀ * c n) := hL1
    calc |hankelMass (c n) (f n) - 1|
        ≤ |hankelMass (c n) (f n) - hankelMass (c n) (gBase n)| + |hankelMass (c n) (gBase n) - 1| :=
          abs_sub_le _ _ _
      _ ≤ M_g * Real.exp (-κ₀ * c n) + M_g * Real.exp (-κ₀ * c n) := add_le_add ((hmass_diff n).trans hIt) hmg_1
      _ = 2 * M_g * Real.exp (-κ₀ * c n) := by ring
  have hmass_tend : Tendsto (fun n => hankelMass (c n) (f n)) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hmass_bound.mono fun n hn => by simpa [Real.norm_eq_abs] using hn) ?_
    have hexp : Tendsto (fun n => Real.exp (-κ₀ * c n)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hκ₀) hc_tend)
    simpa using hexp.const_mul (2 * M_g)
  have hmass_half : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ hankelMass (c n) (f n) :=
    hmass_tend.eventually (eventually_ge_nhds (by norm_num))
  have hT_ge2 : ∀ᶠ n in atTop, 2 ≤ T n := by
    have hdiv : Tendsto (fun n => T n / (c n) ^ (1 / 3 : ℝ)) atTop atTop := by
      have hc23 : Tendsto (fun n => (c n) ^ (2 / 3 : ℝ) / π ^ 2) atTop atTop :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).atTop_div_const
          (sq_pos_of_pos Real.pi_pos)
      refine (hc23.atTop_add (tendsto_const_nhds (x := -(D.tm / hankelBeta1)))).congr'
        (Eventually.of_forall fun n => ?_)
      have hc0 := hc_pos n
      dsimp [T]
      have hsub : c n / (c n) ^ (1 / 3 : ℝ) = (c n) ^ (2 / 3 : ℝ) :=
        div_eq_of_eq_mul (Real.rpow_pos_of_pos hc0 _).ne' (by
          rw [← Real.rpow_add hc0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one])
      calc (c n) ^ (2 / 3 : ℝ) / π ^ 2 + -(D.tm / hankelBeta1)
          = (c n / (c n) ^ (1 / 3 : ℝ)) / π ^ 2 - D.tm / hankelBeta1 := by rw [hsub]; ring
        _ = (c n / π ^ 2 - D.tm / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)) / (c n) ^ (1 / 3 : ℝ) := by
            field_simp [(Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)).ne']
    have hr1 : ∀ᶠ n in atTop, 1 ≤ (c n) ^ (1 / 3 : ℝ) :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).eventually (eventually_ge_atTop 1)
    filter_upwards [hdiv.eventually (eventually_ge_atTop 2), hr1] with n h2 h1
    have hc0 := hc_pos n
    nlinarith [(le_div_iff₀ (Real.rpow_pos_of_pos hc0 _)).mp h2]
  have hTsite_ge2 : ∀ t : D.S, ∀ᶠ n in atTop, 2 ≤ Tsite t n := by
    intro t
    have hdiv : Tendsto (fun n => Tsite t n / (c n) ^ (1 / 3 : ℝ)) atTop atTop := by
      have hc23 : Tendsto (fun n => (c n) ^ (2 / 3 : ℝ) / π ^ 2) atTop atTop :=
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend).atTop_div_const
          (sq_pos_of_pos Real.pi_pos)
      refine (hc23.atTop_add (tendsto_const_nhds (x := -((t : ℝ) / hankelBeta1)))).congr'
        (Eventually.of_forall fun n => ?_)
      have hc0 := hc_pos n
      dsimp [Tsite]
      have hsub : c n / (c n) ^ (1 / 3 : ℝ) = (c n) ^ (2 / 3 : ℝ) :=
        div_eq_of_eq_mul (Real.rpow_pos_of_pos hc0 _).ne' (by
          rw [← Real.rpow_add hc0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one])
      calc (c n) ^ (2 / 3 : ℝ) / π ^ 2 + -((t : ℝ) / hankelBeta1)
          = (c n / (c n) ^ (1 / 3 : ℝ)) / π ^ 2 - (t : ℝ) / hankelBeta1 := by rw [hsub]; ring
        _ = (c n / π ^ 2 - (t : ℝ) / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)) / (c n) ^ (1 / 3 : ℝ) := by
            field_simp [(Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)).ne']
    have hr1 : ∀ᶠ n in atTop, 1 ≤ (c n) ^ (1 / 3 : ℝ) :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).eventually (eventually_ge_atTop 1)
    filter_upwards [hdiv.eventually (eventually_ge_atTop 2), hr1] with n h2 h1
    have hc0 := hc_pos n
    nlinarith [(le_div_iff₀ (Real.rpow_pos_of_pos hc0 _)).mp h2]
  have horigin_eq : ∀ n : ℕ, (-1 : ℝ) * f n 0 = ∫ Δ in Ioi (0 : ℝ), f n Δ * hankelRho0 (c n) Δ := fun n => by
    have hf0 : f n 0 = 0 := by
      dsimp [f, gBase]; split_ifs with h01
      · norm_num at h01
      · rw [hbump_supp 0 (by simp), mul_zero, sub_zero]
    have hint : ∫ Δ in Ioi (0 : ℝ), f n Δ * hankelRho0 (c n) Δ = 0 := by
      have heq : (fun Δ => f n Δ * hankelRho0 (c n) Δ) =
          fun Δ => gBase n Δ * hankelRho0 (c n) Δ - (I_tail n / W n) * (bump Δ * hankelRho0 (c n) Δ) := by
        ext Δ; dsimp [f]; ring
      rw [heq, integral_sub (hg_int n) ((hW_int n).const_mul _), integral_const_mul,
        div_mul_cancel₀ _ (hW_pos n).ne', sub_self]
    rw [hf0, mul_zero, hint]
  have hdeep : ∀ R : ℝ, 1 ≤ R → ∀ᶠ n in atTop, R * (c n) ^ (1 / 3 : ℝ) < c n / π ^ 2 →
      ∫ Δ in Ioo (0 : ℝ) (c n / π ^ 2 - R * (c n) ^ (1 / 3 : ℝ)), |f n Δ| * hankelRho0 (c n) Δ ≤
        (2 * M_g) * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ₀ * c n)) := by
    intro R hR
    have hR0 : 0 ≤ R := by linarith
    filter_upwards [hI_tail_bound, hmass_half] with n hIt hhalf _
    have hc0 := hc_pos n
    set b := c n / π ^ 2 - R * (c n) ^ (1 / 3 : ℝ)
    have hpt : ∀ Δ ∈ Ioo (0 : ℝ) b, |f n Δ| * hankelRho0 (c n) Δ ≤
        |gBase n Δ| * hankelRho0 (c n) Δ + (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) := fun Δ hΔ => by
      have hr := hankelRho0_nonneg hc0 hΔ.1.le
      calc |f n Δ| * hankelRho0 (c n) Δ
          ≤ (|gBase n Δ| + |I_tail n / W n * bump Δ|) * hankelRho0 (c n) Δ :=
            mul_le_mul_of_nonneg_right (abs_sub _ _) hr
        _ = |gBase n Δ| * hankelRho0 (c n) Δ + (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) := by
            rw [abs_mul, abs_div, abs_of_pos (hW_pos n), abs_of_nonneg (hbump_nn Δ)]; ring
    have h1 : ∫ Δ in Ioo (0 : ℝ) b, |f n Δ| * hankelRho0 (c n) Δ ≤
        (∫ Δ in Ioo (0 : ℝ) b, |gBase n Δ| * hankelRho0 (c n) Δ) +
          ∫ Δ in Ioo (0 : ℝ) b, (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) := by
      have hg_sub : IntegrableOn (fun Δ => |gBase n Δ| * hankelRho0 (c n) Δ) (Ioo (0 : ℝ) b) :=
        (abs_mul_rho0_integrableOn hc0 (hg_int n)).mono_set Ioo_subset_Ioi_self
      have hw_sub : IntegrableOn (fun Δ => (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ))
          (Ioo (0 : ℝ) b) :=
        ((hW_int n).mono_set Ioo_subset_Ioi_self).const_mul (|I_tail n| / W n)
      rw [← integral_add hg_sub hw_sub]
      exact setIntegral_mono_on ((abs_mul_rho0_integrableOn hc0 (hf_int n)).mono_set Ioo_subset_Ioi_self)
        (hg_sub.add hw_sub) measurableSet_Ioo hpt
    have hfirst : ∫ Δ in Ioo (0 : ℝ) b, |gBase n Δ| * hankelRho0 (c n) Δ ≤
        M_g * Real.exp (-5 * R ^ (3 / 2 : ℝ)) := by
      rw [← integral_tail_abs_hankelWindowProfile hc0 (gBase n) R]
      have hprof_abs : IntegrableOn (fun u => |hankelWindowProfile (c n) (gBase n) u|) (Ioi (R * hankelBeta1)) :=
        ((integrable_hankelWindowProfile_iff hc0 _).mpr (hg_int n)).abs.integrableOn
      have hnorm_sub : IntegrableOn (fun u => |D.normG u|) (Ioi (R * hankelBeta1)) :=
        D.normG_integrable.abs.integrableOn
      have hpt2 : ∀ u ∈ Ioi (R * hankelBeta1), |hankelWindowProfile (c n) (gBase n) u| ≤ |D.normG u| := fun u _ => by
        rw [hprof_g n u]
        split_ifs
        · let d := c n / π ^ 2 - u / hankelBeta1 * (c n) ^ (1 / 3 : ℝ)
          rw [abs_mul, abs_of_nonneg (hχ_bounds d).1]
          exact mul_le_of_le_one_left (abs_nonneg _) (hχ_bounds d).2
        · rw [abs_zero]; exact abs_nonneg _
      have h5 : 5 * R ^ (3 / 2 : ℝ) ≤ (1 / 3 : ℝ) * (R * hankelBeta1) ^ (3 / 2 : ℝ) := by
        have h15 : (15 : ℝ) ≤ hankelBeta1 ^ (3 / 2 : ℝ) := by
          rw [hankelBeta1_rpow_three_halves]
          have h9 : (9 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
          have h81 : (81 : ℝ) < (π ^ 2) ^ 2 := by nlinarith
          have hsq : (15 : ℝ) ^ 2 ≤ (π ^ 2 * √3) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; nlinarith
          nlinarith [mul_nonneg (sq_nonneg π) (Real.sqrt_nonneg 3)]
        rw [Real.mul_rpow hR0 hankelBeta1_pos.le]
        nlinarith [Real.rpow_nonneg hR0 (3 / 2 : ℝ)]
      calc ∫ u in Ioi (R * hankelBeta1), |hankelWindowProfile (c n) (gBase n) u|
          ≤ ∫ u in Ioi (R * hankelBeta1), |D.normG u| :=
            setIntegral_mono_on hprof_abs hnorm_sub measurableSet_Ioi hpt2
        _ ≤ ∫ u in Ici (R * hankelBeta1), |D.normG u| :=
            setIntegral_mono_set D.normG_integrable.abs.integrableOn
              (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ hu => le_of_lt (mem_Ioi.mp hu))
        _ ≤ M_g * Real.exp (-(1 / 3 : ℝ) * (R * hankelBeta1) ^ (3 / 2 : ℝ)) :=
            htail_g (R * hankelBeta1) (mul_nonneg hR0 hankelBeta1_pos.le)
        _ ≤ M_g * Real.exp (-5 * R ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hMg.le
    have hsecond : ∫ Δ in Ioo (0 : ℝ) b, (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) ≤
        M_g * Real.exp (-κ₀ * c n) := by
      have h_eq : ∫ Δ in Ioi (0 : ℝ), (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) = |I_tail n| := by
        rw [integral_const_mul]; exact div_mul_cancel₀ _ (hW_pos n).ne'
      have hsub' : ∫ Δ in Ioo (0 : ℝ) b, (|I_tail n| / W n) * (bump Δ * hankelRho0 (c n) Δ) ≤ |I_tail n| := by
        refine (setIntegral_mono_set ((hW_int n).const_mul (|I_tail n| / W n))
          (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ =>
            mul_nonneg (div_nonneg (abs_nonneg _) (hW_pos n).le)
              (mul_nonneg (hbump_nn Δ) (hankelRho0_nonneg hc0 (le_of_lt hΔ))))
          (Eventually.of_forall fun Δ (h : Δ ∈ Ioo (0 : ℝ) b) => mem_Ioi.mpr h.1)).trans_eq h_eq
      exact hsub'.trans hIt
    have hadd_pos : 0 ≤ Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ₀ * c n) :=
      add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    calc ∫ Δ in Ioo (0 : ℝ) b, |f n Δ| * hankelRho0 (c n) Δ
        ≤ M_g * Real.exp (-5 * R ^ (3 / 2 : ℝ)) + M_g * Real.exp (-κ₀ * c n) := by linarith
      _ = (2 * M_g) * (1 / 2 : ℝ) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ₀ * c n)) := by ring
      _ ≤ (2 * M_g) * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-κ₀ * c n)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hhalf (by linarith)) le_rfl hadd_pos (by positivity)
  obtain ⟨CG, νG, hCG, hGenv⟩ := D.G_env
  let L : ℝ := ∫ x : ℝ, ‖D.G (x : ℂ)‖
  let C' : ℝ := CG / L
  let F : ℂ → ℂ := fun z => ((L⁻¹ : ℝ) : ℂ) * D.G z
  refine ⟨⟨c, -1, Or.inr rfl, f, T, Tsite, hc_tend, Eventually.of_forall hf_cont,
    Eventually.of_forall hf_int, ?_, Eventually.of_forall horigin_eq, ?_, ?_, ?_, ?_,
    ⟨2 * M_g, κ₀, by linarith, hκ₀, hdeep⟩, ?_⟩, ?_⟩
  · filter_upwards [hmass_half] with n hhalf
    by_contra h0; push Not at h0
    have hm0 : hankelMass (c n) (f n) = 0 := by
      unfold hankelMass
      refine setIntegral_eq_zero_of_forall_eq_zero fun Δ hΔ => ?_
      rw [h0 Δ (le_of_lt hΔ), abs_zero, zero_mul]
    linarith
  · exact Eventually.of_forall fun n => by
      have hf0 : f n 0 = 0 := by
        dsimp [f, gBase]; split_ifs with h01
        · norm_num at h01
        · rw [hbump_supp 0 (by simp), mul_zero, sub_zero]
      rw [hf0, mul_zero]
  · filter_upwards [hT_ge2] with n hT2 Δ hΔ
    have hc0 := hc_pos n
    have hΔ2 : 2 ≤ Δ := hT2.trans hΔ
    have hΔ1 : 1 ≤ Δ := by linarith
    have hb0 : bump Δ = 0 := hbump_supp Δ (fun hm => by linarith [hm.1, hm.2])
    have hχ1 : χ Δ = 1 := by dsimp [χ]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    have hu_le : uMap n Δ ≤ D.tm := by
      dsimp [uMap, T] at hΔ ⊢
      have hmul : hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - Δ) ≤
          hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * ((D.tm / hankelBeta1) * (c n) ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hankelBeta1_pos.le (Real.rpow_nonneg hc0.le _))
      have heq : hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * ((D.tm / hankelBeta1) * (c n) ^ (1 / 3 : ℝ)) = D.tm := by
        rw [show hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * ((D.tm / hankelBeta1) * (c n) ^ (1 / 3 : ℝ)) =
          (hankelBeta1 / hankelBeta1) * ((c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ)) * D.tm by ring,
          div_self hankelBeta1_pos.ne', rpow_neg_one_third_mul_add hc0]; ring
      exact hmul.trans_eq heq
    have hGn : 0 ≤ D.normG (uMap n Δ) :=
      div_nonneg (D.G_nonneg_left _ hu_le) D.G_l1_pos.le
    dsimp [f, gBase]
    split_ifs
    rw [hb0, mul_zero, sub_zero, hχ1, one_mul]
    exact div_nonneg (mul_nonneg (div_nonneg hankelBeta1_pos.le (Real.rpow_nonneg hc0.le _)) hGn)
      (hankelRho0_pos hc0 (by linarith)).le
  · intro t _
    filter_upwards [hTsite_ge2 t] with n ht2
    have hc0 := hc_pos n
    have hb0 : bump (Tsite t n) = 0 := hbump_supp _ (fun hm => by linarith [hm.1, hm.2])
    have hu_eq : uMap n (Tsite t n) = t := by
      dsimp [uMap, Tsite]
      rw [show hankelBeta1 * (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - (c n / π ^ 2 - (t : ℝ) / hankelBeta1 * (c n) ^ (1 / 3 : ℝ))) =
        (hankelBeta1 / hankelBeta1) * ((c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ)) * t by ring,
        div_self hankelBeta1_pos.ne', rpow_neg_one_third_mul_add hc0]; ring
    have hG0 : D.normG t = 0 := by
      unfold HermiteBiehlerData.normG; rw [D.G_eq_zero_on_S (t : ℝ) t.2, Complex.zero_re, zero_div]
    dsimp [f, gBase]
    split_ifs with h1
    · rw [hb0, mul_zero, sub_zero, hu_eq, hG0, mul_zero, zero_div]
    · exfalso; exact h1 (by linarith)
  · intro t _
    refine (tendsto_const_nhds (x := -(t : ℝ) / hankelBeta1)).congr' (Eventually.of_forall fun n => ?_)
    have hc0 := hc_pos n
    dsimp [Tsite]
    calc -(t : ℝ) / hankelBeta1
        = -(t : ℝ) / hankelBeta1 * 1 := (mul_one _).symm
      _ = -(t : ℝ) / hankelBeta1 * ((c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ)) := by
          rw [rpow_neg_one_third_mul_add hc0]
      _ = (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - (t : ℝ) / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) - c n / π ^ 2) := by
          ring
  · intro ns hns _
    refine ⟨id, -(D.tm / hankelBeta1), F, C', νG, strictMono_id, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
      have hc0 := hc_pos (ns k)
      dsimp [T]
      symm
      calc (c (ns k)) ^ (-(1 / 3 : ℝ)) * (c (ns k) / π ^ 2 - D.tm / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ) - c (ns k) / π ^ 2)
          = -(D.tm / hankelBeta1) * ((c (ns k)) ^ (-(1 / 3 : ℝ)) * (c (ns k)) ^ (1 / 3 : ℝ)) := by ring
        _ = -(D.tm / hankelBeta1) := by rw [rpow_neg_one_third_mul_add hc0, mul_one]
    · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
      intro K _ hK
      have hF_re : (fun u : ℝ => (F (u : ℂ)).re) = D.normG := by
        ext u; dsimp [F, L, HermiteBiehlerData.normG]
        rw [Complex.re_ofReal_mul, inv_mul_eq_div]
      rw [hF_re, Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨R, hRK⟩ := hK.bddAbove
      have hK_bd : ∃ M_K : ℝ, 0 < M_K ∧ ∀ u ∈ K, |D.normG u| ≤ M_K := by
        rcases K.eq_empty_or_nonempty with rfl | hKne
        · exact ⟨1, zero_lt_one, fun _ h => absurd h (notMem_empty _)⟩
        · obtain ⟨u₀, _, hu₀⟩ := hK.exists_isMaxOn hKne D.normG_continuous.abs.continuousOn
          exact ⟨|D.normG u₀| + 1, by positivity, fun u hu => (hu₀ hu).trans (by linarith)⟩
      obtain ⟨M_K, hMK, hnormK⟩ := hK_bd
      have hR_large : ∀ᶠ k in atTop, 2 ≤ c (ns k) / π ^ 2 - R / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ) := by
        have hc_ns := hc_tend.comp hns
        have hdiv : Tendsto (fun k => (c (ns k) / π ^ 2 - R / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ)) /
            (c (ns k)) ^ (1 / 3 : ℝ)) atTop atTop := by
          have hc23 : Tendsto (fun k => (c (ns k)) ^ (2 / 3 : ℝ) / π ^ 2) atTop atTop :=
            ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_ns).atTop_div_const
              (sq_pos_of_pos Real.pi_pos)
          refine (hc23.atTop_add (tendsto_const_nhds (x := -(R / hankelBeta1)))).congr'
            (Eventually.of_forall fun k => ?_)
          have hc0 := hc_pos (ns k)
          have hsub : c (ns k) / (c (ns k)) ^ (1 / 3 : ℝ) = (c (ns k)) ^ (2 / 3 : ℝ) :=
            div_eq_of_eq_mul (Real.rpow_pos_of_pos hc0 _).ne' (by
              rw [← Real.rpow_add hc0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one])
          calc (c (ns k)) ^ (2 / 3 : ℝ) / π ^ 2 + -(R / hankelBeta1)
              = (c (ns k) / (c (ns k)) ^ (1 / 3 : ℝ)) / π ^ 2 - R / hankelBeta1 := by rw [hsub]; ring
            _ = (c (ns k) / π ^ 2 - R / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ)) / (c (ns k)) ^ (1 / 3 : ℝ) := by
                field_simp [(Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)).ne']
        have hr1 : ∀ᶠ k in atTop, 1 ≤ (c (ns k)) ^ (1 / 3 : ℝ) :=
          ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_ns).eventually (eventually_ge_atTop 1)
        filter_upwards [hdiv.eventually (eventually_ge_atTop 2), hr1] with k h2 h1
        have hc0 := hc_pos (ns k)
        nlinarith [(le_div_iff₀ (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ))).mp h2]
      have hinv_ns : Tendsto (fun k => (hankelMass (c (ns k)) (f (ns k)))⁻¹ - 1) atTop (𝓝 0) := by
        simpa using ((hmass_tend.comp hns).inv₀ one_ne_zero).sub (tendsto_const_nhds (x := (1 : ℝ)))
      filter_upwards [hR_large, hinv_ns.eventually (Metric.ball_mem_nhds 0 (div_pos hε hMK))] with
        k hkR hinvk
      intro u hu
      have hc0 := hc_pos (ns k)
      have huR : u ≤ R := hRK hu
      have hΔ2 : 2 ≤ c (ns k) / π ^ 2 - u / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ) := by
        have hmul : u / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ) ≤ R / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right huR hankelBeta1_pos.le) (Real.rpow_nonneg hc0.le _)
        linarith
      have hprof_eq : hankelWindowProfile (c (ns k)) (f (ns k)) u = D.normG u := by
        unfold hankelWindowProfile; dsimp only
        set Δ := c (ns k) / π ^ 2 - u / hankelBeta1 * (c (ns k)) ^ (1 / 3 : ℝ)
        have h0 : 0 < Δ := by linarith
        have hb0 : bump Δ = 0 := hbump_supp Δ (fun hm => by linarith [hm.1, hm.2])
        have hχ1 : χ Δ = 1 := by dsimp [χ]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
        have hu_eq : uMap (ns k) Δ = u := by
          dsimp [uMap, Δ]; rw [Real.rpow_neg hc0.le (1 / 3 : ℝ)]
          field_simp [hankelBeta1_pos.ne', (Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)).ne']; ring
        have hf_eq : f (ns k) Δ = (hankelBeta1 / (c (ns k)) ^ (1 / 3 : ℝ)) * D.normG u / hankelRho0 (c (ns k)) Δ := by
          dsimp [f, gBase]; split_ifs with h1
          · rw [hb0, mul_zero, sub_zero, hχ1, one_mul, hu_eq]
          · exfalso; exact h1 (by linarith)
        split_ifs
        rw [hf_eq, div_mul_cancel₀ _ (hankelRho0_pos hc0 h0).ne']
        calc (c (ns k) ^ (1 / 3 : ℝ) / hankelBeta1) * (hankelBeta1 / c (ns k) ^ (1 / 3 : ℝ) * D.normG u)
            = (c (ns k) ^ (1 / 3 : ℝ) / c (ns k) ^ (1 / 3 : ℝ)) * (hankelBeta1 / hankelBeta1) * D.normG u := by ring
          _ = D.normG u := by
              rw [div_self (Real.rpow_pos_of_pos hc0 _).ne', div_self hankelBeta1_pos.ne']; ring
      dsimp only [id]
      rw [hprof_eq, Real.dist_eq, abs_sub_comm]
      rw [Real.dist_eq, sub_zero] at hinvk
      calc |D.normG u / hankelMass (c (ns k)) (f (ns k)) - D.normG u|
          = |D.normG u| * |(hankelMass (c (ns k)) (f (ns k)))⁻¹ - 1| := by
            rw [← abs_mul]; congr 1; ring
        _ ≤ M_K * |(hankelMass (c (ns k)) (f (ns k)))⁻¹ - 1| :=
            mul_le_mul_of_nonneg_right (hnormK u hu) (abs_nonneg _)
        _ < M_K * (ε / M_K) := mul_lt_mul_of_pos_left hinvk hMK
        _ = ε := mul_div_cancel₀ _ hMK.ne'
    · exact D.G_diff.const_mul _
    · exact D.G_int.const_mul _
    · exact div_nonneg hCG D.G_l1_pos.le
    · intro z; dsimp [F, L]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr D.G_l1_pos)]
      calc (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ * ‖D.G z‖
          ≤ (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ * (CG * (1 + ‖z‖) ^ νG * airyEnv z) :=
            mul_le_mul_of_nonneg_left (hGenv z) (inv_nonneg.mpr D.G_l1_pos.le)
        _ = C' * (1 + ‖z‖) ^ νG * airyEnv z := by dsimp [C', L]; ring
    · intro u; dsimp [F]; rw [Complex.im_ofReal_mul, D.G_real u, mul_zero]
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    have hc0 := hc_pos n
    dsimp [T]
    symm
    calc (c n) ^ (-(1 / 3 : ℝ)) * (c n / π ^ 2 - D.tm / hankelBeta1 * (c n) ^ (1 / 3 : ℝ) - c n / π ^ 2)
        = -(D.tm / hankelBeta1) * ((c n) ^ (-(1 / 3 : ℝ)) * (c n) ^ (1 / 3 : ℝ)) := by ring
      _ = -(D.tm / hankelBeta1) := by rw [rpow_neg_one_third_mul_add hc0, mul_one]


end FormalResearch.SignUncertainty

/-! ### Axiom Checks (`#guard_msgs`) -/

/-- info: 'FormalResearch.SignUncertainty.radial_rigidity_liminf_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.radial_rigidity_liminf_ereal

/-- info: 'FormalResearch.SignUncertainty.radial_rigidity_liminf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.radial_rigidity_liminf

/-- info: 'FormalResearch.SignUncertainty.radial_rigidity_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.radial_rigidity_profile

/-- info: 'FormalResearch.SignUncertainty.radial_rigidity_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.radial_rigidity_origin

/-- info: 'FormalResearch.SignUncertainty.radialRigidityPackage_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.radialRigidityPackage_nonvacuous
