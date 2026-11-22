module

public import FormalResearch.SignUncertainty.HermiteBiehlerUniq
public import FormalResearch.Analysis.Scheffe
public import FormalResearch.Complex.Montel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.Order

/-!
# Airy–Laplace Transform, Even-`m` Sign, and One-Profile LP (`ce_shells.tex` §1–2, Prop H.14')

Source: `CFT/sign_uncertainty/paper/ce_shells.tex` (PR 240, commit `58dd780c8`).

* **Section 1:** Airy Laplace transform `airyLaplace`, Airy class `InAiryClass`, `ShellHBData`,
  Laplace calculus under the integral sign, shared tail-positivity lemma, factored Laplace ODE
  (`eq:ce-laplace-ode`), and the unconditional even-`m` Laplace sign theorem (`even_m_laplace_sign`).
* **Section 2 (Proposition H.14' / `par:ce-one-profile`):** equivalence between two-profile
  and one-profile feasibility (`one_profile_feasible_iff`), `u_* ≤ t_m` and `t_m` feasibility iff
  `∀ y > 0, 0 ≤ airyLaplace (-G_N) y` (`one_profile_threshold_le_and_endpoint_iff`), and
  attainment of `u_LP` (`one_profile_maximizer_exists` with `airyCompactnessModel_nonvacuous`).

(Companion modules `ShellGap`, `ShellGapWitness`, and `ShellLaplaceZeros` treat the conditional
Mellin origin-floor / subsequential core of Theorem `H.14` and Corollary `H.14b`.)
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis
open FormalResearch.Montel

/-! ### Section 1: Airy Class, `airyLaplace`, `ShellHBData`, and Even-`m` Sign Theorem -/

/-- Hankel Airy scaling constant `β₁ = (π² √3)^{2/3}`. -/
noncomputable def shellBeta1 : ℝ := (π ^ 2 * √3) ^ (2 / 3 : ℝ)

lemma shellBeta1_pos : 0 < shellBeta1 := by unfold shellBeta1; positivity

lemma shellBeta1_rpow_three_halves : shellBeta1 ^ (3 / 2 : ℝ) = π ^ 2 * √3 := by
  unfold shellBeta1
  rw [← Real.rpow_mul (by positivity)]
  norm_num

/-- Mellin rescaling constant `c_s = (π² / 3)^{1/3}`. -/
noncomputable def shellCs : ℝ := (π ^ 2 / 3) ^ (1 / 3 : ℝ)

lemma shellCs_pos : 0 < shellCs := by unfold shellCs; positivity

/-- Hankel radial weight `ρ₀(c, Δ) = (2π)^c / Γ(c) · Δ^{c - 1}`. -/
noncomputable def shellRho0 (c Δ : ℝ) : ℝ :=
  (2 * π) ^ c / Real.Gamma c * Δ ^ (c - 1)

lemma shellRho0_pos {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) : 0 < shellRho0 c Δ := by
  unfold shellRho0
  have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hp1 : 0 < (2 * π) ^ c := Real.rpow_pos_of_pos (by positivity) c
  have hp2 : 0 < Δ ^ (c - 1) := Real.rpow_pos_of_pos hΔ (c - 1)
  positivity

lemma shellRho0_nonneg {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 ≤ Δ) : 0 ≤ shellRho0 c Δ := by
  unfold shellRho0
  exact mul_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) c) (Real.Gamma_pos_of_pos hc).le)
    (Real.rpow_nonneg hΔ (c - 1))

lemma continuousOn_shellRho0 (c : ℝ) : ContinuousOn (shellRho0 c) (Ioi 0) := by
  intro Δ hΔ
  unfold shellRho0
  exact ((continuousAt_id.rpow_const (Or.inl (ne_of_gt (mem_Ioi.mp hΔ)))).const_mul
    _).continuousWithinAt

/-- Hankel `L¹` mass `M[f] = ∫_0^∞ |f(Δ)| ρ₀(c, Δ) dΔ`. -/
noncomputable def shellMass (c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ Δ in Ioi (0 : ℝ), |f Δ| * shellRho0 c Δ

lemma shellMass_nonneg {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) : 0 ≤ shellMass c f :=
  setIntegral_nonneg measurableSet_Ioi fun _ hΔ =>
    mul_nonneg (abs_nonneg _) (shellRho0_nonneg hc (le_of_lt hΔ))

lemma abs_mul_shellRho0_integrableOn {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hint : IntegrableOn (fun Δ => f Δ * shellRho0 c Δ) (Ioi 0)) :
    IntegrableOn (fun Δ => |f Δ| * shellRho0 c Δ) (Ioi 0) := by
  refine hint.norm.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ => ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (shellRho0_nonneg hc (le_of_lt hΔ))]

/-- Rescaled Airy window profile `Ψ_{f,c}(u)` extended by `0` outside `{Δ > 0}`. -/
noncomputable def shellWindowProfile (c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  let Δ := c / π ^ 2 - u / shellBeta1 * c ^ (1 / 3 : ℝ)
  if 0 < Δ then (c ^ (1 / 3 : ℝ) / shellBeta1) * (f Δ * shellRho0 c Δ) else 0

private lemma shellWindowProfile_eq_indicator (c : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    shellWindowProfile c f u =
      (c ^ (1 / 3 : ℝ) / shellBeta1) *
        (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * shellRho0 c Δ)
          (c / π ^ 2 - (c ^ (1 / 3 : ℝ) / shellBeta1) * u) := by
  have hsub : c / π ^ 2 - u / shellBeta1 * c ^ (1 / 3 : ℝ) =
      c / π ^ 2 - (c ^ (1 / 3 : ℝ) / shellBeta1) * u := by ring
  unfold shellWindowProfile; dsimp only; rw [hsub]
  by_cases h : 0 < c / π ^ 2 - (c ^ (1 / 3 : ℝ) / shellBeta1) * u
  · rw [indicator_of_mem (mem_Ioi.mpr h)]; split_ifs; rfl
  · rw [indicator_of_notMem (mem_Ioi.not.mpr h), mul_zero]; split_ifs; rfl

lemma integrable_shellWindowProfile_iff {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    Integrable (shellWindowProfile c f) ↔
      IntegrableOn (fun Δ => f Δ * shellRho0 c Δ) (Ioi 0) := by
  let a := c ^ (1 / 3 : ℝ) / shellBeta1
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc _) shellBeta1_pos
  have heq : shellWindowProfile c f = fun u =>
      a * (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * shellRho0 c Δ) (c / π ^ 2 - a * u) :=
    funext (shellWindowProfile_eq_indicator c f)
  rw [heq, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr ha.ne')]
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * shellRho0 c Δ)
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

lemma integral_shellWindowProfile {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ u : ℝ, shellWindowProfile c f u = ∫ Δ in Ioi (0 : ℝ), f Δ * shellRho0 c Δ := by
  let a := c ^ (1 / 3 : ℝ) / shellBeta1
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc _) shellBeta1_pos
  have heq : shellWindowProfile c f = fun u =>
      a * (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * shellRho0 c Δ) (c / π ^ 2 - a * u) :=
    funext (shellWindowProfile_eq_indicator c f)
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left (fun t =>
      (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * shellRho0 c Δ) (c / π ^ 2 - t)) a,
    integral_sub_left_eq_self (fun Δ => (Ioi (0 : ℝ)).indicator (fun Δ => f Δ * shellRho0 c Δ) Δ)
      volume (c / π ^ 2),
    integral_indicator measurableSet_Ioi, smul_eq_mul, abs_inv, abs_of_pos ha,
    ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma integral_abs_shellWindowProfile {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    ∫ u : ℝ, |shellWindowProfile c f u| = shellMass c f := by
  have ha_nn : 0 ≤ c ^ (1 / 3 : ℝ) / shellBeta1 :=
    div_nonneg (Real.rpow_nonneg hc.le _) shellBeta1_pos.le
  have habs : (fun u => |shellWindowProfile c f u|) = shellWindowProfile c (fun Δ => |f Δ|) := by
    ext u; unfold shellWindowProfile; dsimp only
    split_ifs with h
    · rw [abs_mul, abs_of_nonneg ha_nn, abs_mul, abs_of_nonneg (shellRho0_nonneg hc h.le)]
    · simp
  rw [habs, integral_shellWindowProfile hc (fun Δ => |f Δ|), shellMass]

lemma integral_tail_abs_shellWindowProfile {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) (R : ℝ) :
    ∫ u in Ioi (R * shellBeta1), |shellWindowProfile c f u| =
      ∫ Δ in Ioo (0 : ℝ) (c / π ^ 2 - R * c ^ (1 / 3 : ℝ)), |f Δ| * shellRho0 c Δ := by
  let a := c ^ (1 / 3 : ℝ) / shellBeta1
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hc _) shellBeta1_pos
  let b := c / π ^ 2 - R * c ^ (1 / 3 : ℝ)
  have h1 : ∀ u : ℝ, (Ioi (R * shellBeta1)).indicator (fun v => |shellWindowProfile c f v|) u =
      a * (Ioo (0 : ℝ) b).indicator (fun Δ => |f Δ| * shellRho0 c Δ) (c / π ^ 2 - a * u) := by
    intro u
    have hlin : c / π ^ 2 - a * u < b ↔ R * shellBeta1 < u := by
      have hb_eq : b = c / π ^ 2 - a * (R * shellBeta1) := by
        dsimp [b, a]; field_simp [shellBeta1_pos.ne']
      rw [hb_eq, sub_lt_sub_iff_left, mul_lt_mul_iff_right₀ ha]
    by_cases hu : u ∈ Ioi (R * shellBeta1)
    · rw [indicator_of_mem hu]
      have hlt : c / π ^ 2 - a * u < b := hlin.mpr hu
      rw [shellWindowProfile_eq_indicator]
      by_cases h0 : 0 < c / π ^ 2 - a * u
      · rw [indicator_of_mem (mem_Ioo.mpr ⟨h0, hlt⟩), indicator_of_mem (mem_Ioi.mpr h0),
          abs_mul, abs_of_pos ha, abs_mul, abs_of_nonneg (shellRho0_nonneg hc h0.le)]
      · rw [indicator_of_notMem (fun hm => h0 (mem_Ioo.mp hm).1)]
        dsimp only [a] at h0 ⊢
        rw [indicator_of_notMem (mem_Ioi.not.mpr h0), mul_zero, abs_zero]
    · rw [indicator_of_notMem hu]
      have hge : ¬ c / π ^ 2 - a * u < b := fun h => hu (hlin.mp h)
      rw [indicator_of_notMem (fun hm => hge (mem_Ioo.mp hm).2), mul_zero]
  rw [← integral_indicator measurableSet_Ioi]
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun t =>
      (Ioo (0 : ℝ) b).indicator (fun Δ => |f Δ| * shellRho0 c Δ) (c / π ^ 2 - t)) a,
    integral_sub_left_eq_self (fun Δ => (Ioo (0 : ℝ) b).indicator (fun Δ => |f Δ| * shellRho0 c Δ) Δ)
      volume (c / π ^ 2),
    integral_indicator measurableSet_Ioo, smul_eq_mul, abs_inv, abs_of_pos ha,
    ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma shellMass_pos_of_continuousOn {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ici 0)) (hint : IntegrableOn (fun Δ => f Δ * shellRho0 c Δ) (Ioi 0))
    (hne : ∃ Δ : ℝ, 0 ≤ Δ ∧ f Δ ≠ 0) :
    0 < shellMass c f := by
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
  have hint_abs := abs_mul_shellRho0_integrableOn hc hint
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun Δ hΔ =>
      mul_nonneg (abs_nonneg _) (shellRho0_nonneg hc (le_of_lt hΔ))) hint_abs).mpr ?_
  have hcont_g : ContinuousOn (fun Δ => |f Δ| * shellRho0 c Δ) (Ioi 0) :=
    (hcont.mono Ioi_subset_Ici_self).abs.mul (continuousOn_shellRho0 c)
  have hopen : IsOpen {Δ ∈ Ioi (0 : ℝ) | 0 < |f Δ| * shellRho0 c Δ} :=
    hcont_g.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
  have hmem : Δ₁ ∈ {Δ ∈ Ioi (0 : ℝ) | 0 < |f Δ| * shellRho0 c Δ} :=
    ⟨hΔ₁_pos, mul_pos (abs_pos.mpr hΔ₁_ne) (shellRho0_pos hc hΔ₁_pos)⟩
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨Δ₁, hmem⟩)
    (measure_mono fun Δ h => ⟨Function.mem_support.mpr h.2.ne', h.1⟩)

/-- The Airy Laplace transform `\mathscr L_y(F) = e^{-y³ / 12} ∫_ℝ F(u) e^{y u} du`. -/
noncomputable def airyLaplace (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, F u * Real.exp (y * u)

/-- Membership in the Airy class `𝒢` (`eq:airy-class`): entire, integrable on `ℝ`,
`‖F(u)‖ ≤ C (1 + ‖u‖)^ν e(u)`, and real-valued on `ℝ`. -/
def InAiryClass (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
  Integrable (fun x : ℝ => F (x : ℂ)) ∧
  (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖F u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
  (∀ x : ℝ, (F (x : ℂ)).im = 0)

/-- Real-axis growth class: continuous, polynomial growth on `(-∞, 0]`, Airy decay on `[0, ∞)`. -/
def HasPolyLeftAiryRightBound (g : ℝ → ℝ) : Prop :=
  Continuous g ∧
  (∃ (C₁ : ℝ) (k : ℕ), 0 ≤ C₁ ∧ ∀ u : ℝ, u ≤ 0 → |g u| ≤ C₁ * (1 + |u|) ^ k) ∧
  (∃ (C₂ ν : ℝ), 0 ≤ C₂ ∧ ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₂ * (1 + u) ^ ν * airyEnv (u : ℂ))

lemma InAiryClass.neg {F : ℂ → ℂ} (h : InAiryClass F) : InAiryClass (fun z => -F z) :=
  ⟨h.1.neg, h.2.1.neg, by
    obtain ⟨C, ν, hC, hb⟩ := h.2.2.1
    exact ⟨C, ν, hC, fun u => by simpa using hb u⟩,
    fun x => by simp [h.2.2.2 x]⟩

lemma InAiryClass.smul {F : ℂ → ℂ} (h : InAiryClass F) (c : ℝ) :
    InAiryClass (fun z => (c : ℂ) * F z) :=
  ⟨h.1.const_mul _, h.2.1.const_mul _, by
    obtain ⟨C, ν, hC, hb⟩ := h.2.2.1
    refine ⟨|c| * C, ν, by positivity, fun u => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |c| * ‖F u‖ ≤ |c| * (C * (1 + ‖u‖) ^ ν * airyEnv u) :=
          mul_le_mul_of_nonneg_left (hb u) (abs_nonneg _)
      _ = (|c| * C) * (1 + ‖u‖) ^ ν * airyEnv u := by ring,
    fun x => by simp [h.2.2.2 x]⟩

lemma InAiryClass.add {F G : ℂ → ℂ} (hF : InAiryClass F) (hG : InAiryClass G) :
    InAiryClass (fun z => F z + G z) := by
  refine ⟨hF.1.add hG.1, hF.2.1.add hG.2.1, ?_, fun x => by simp [hF.2.2.2 x, hG.2.2.2 x]⟩
  obtain ⟨CF, νF, hCF, hbF⟩ := hF.2.2.1
  obtain ⟨CG, νG, hCG, hbG⟩ := hG.2.2.1
  refine ⟨CF + CG, max νF νG, add_nonneg hCF hCG, fun u => ?_⟩
  have h1 : 1 ≤ 1 + ‖u‖ := by linarith [norm_nonneg u]
  have hF' := hbF u
  have hG' := hbG u
  have hpF : (1 + ‖u‖) ^ νF ≤ (1 + ‖u‖) ^ max νF νG :=
    Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
  have hpG : (1 + ‖u‖) ^ νG ≤ (1 + ‖u‖) ^ max νF νG :=
    Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)
  have he := (airyEnv_pos u).le
  calc ‖F u + G u‖ ≤ ‖F u‖ + ‖G u‖ := norm_add_le _ _
    _ ≤ CF * (1 + ‖u‖) ^ max νF νG * airyEnv u + CG * (1 + ‖u‖) ^ max νF νG * airyEnv u :=
        add_le_add
          (hF'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpF hCF) he))
          (hG'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpG hCG) he))
    _ = (CF + CG) * (1 + ‖u‖) ^ max νF νG * airyEnv u := by ring

lemma InAiryClass.sub {F G : ℂ → ℂ} (hF : InAiryClass F) (hG : InAiryClass G) :
    InAiryClass (fun z => F z - G z) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma InAiryClass.zero : InAiryClass (fun _ => (0 : ℂ)) :=
  ⟨differentiable_const _, integrable_zero _ _ _,
    ⟨0, 0, le_rfl, fun u => by simp⟩, fun _ => rfl⟩

lemma InAiryClass.to_polyLeftAiryRightBound {F : ℂ → ℂ} (hF : InAiryClass F) :
    HasPolyLeftAiryRightBound (fun x : ℝ => (F (x : ℂ)).re) := by
  obtain ⟨C, ν, hC, hb⟩ := hF.2.2.1
  refine ⟨Complex.continuous_re.comp (hF.1.continuous.comp Complex.continuous_ofReal), ?_, ?_⟩
  · refine ⟨C, ⌈max ν 0⌉₊, hC, fun u hu => ?_⟩
    have hbu := hb (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hbu
    have he : airyEnv (u : ℂ) = 1 := by
      rcases hu.eq_or_lt with rfl | hlt
      · have h0 := at47_env_ofReal_nonneg (le_rfl : (0 : ℝ) ≤ 0)
        simpa using h0
      · exact airyEnv_ofReal_neg hlt
    have hre : |(F (u : ℂ)).re| ≤ ‖F (u : ℂ)‖ := Complex.abs_re_le_norm _
    have h1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
    have hp : (1 + |u|) ^ ν ≤ (1 + |u|) ^ ⌈max ν 0⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 ((le_max_left ν 0).trans (Nat.le_ceil _))
    calc |(F (u : ℂ)).re| ≤ ‖F (u : ℂ)‖ := hre
      _ ≤ C * (1 + |u|) ^ ν * 1 := by rwa [he] at hbu
      _ = C * (1 + |u|) ^ ν := mul_one _
      _ ≤ C * (1 + |u|) ^ ⌈max ν 0⌉₊ := by gcongr
  · refine ⟨C, ν, hC, fun u hu => ?_⟩
    have hbu := hb (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at hbu
    exact (Complex.abs_re_le_norm _).trans hbu

lemma HasPolyLeftAiryRightBound.mul_id_sub {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g) (t : ℝ) :
    HasPolyLeftAiryRightBound (fun u => (u - t) * g u) := by
  obtain ⟨hc, ⟨C₁, k, hC₁, hb₁⟩, ⟨C₂, ν, hC₂, hb₂⟩⟩ := hg
  refine ⟨(continuous_id.sub continuous_const).mul hc, ?_, ?_⟩
  · refine ⟨C₁ * (1 + |t|), k + 1, by positivity, fun u hu => ?_⟩
    have hut : |u - t| ≤ (1 + |t|) * (1 + |u|) := by
      calc |u - t| ≤ |u| + |t| := abs_sub _ _
        _ ≤ (1 + |t|) * (1 + |u|) := by nlinarith [abs_nonneg u, abs_nonneg t]
    rw [abs_mul]
    calc |u - t| * |g u| ≤ ((1 + |t|) * (1 + |u|)) * (C₁ * (1 + |u|) ^ k) :=
          mul_le_mul hut (hb₁ u hu) (abs_nonneg _) (by positivity)
      _ = (C₁ * (1 + |t|)) * (1 + |u|) ^ (k + 1) := by rw [pow_succ']; ring
  · refine ⟨C₂ * (1 + |t|), ν + 1, by positivity, fun u hu => ?_⟩
    have hut : |u - t| ≤ (1 + |t|) * (1 + u) := by
      calc |u - t| ≤ |u| + |t| := abs_sub _ _
        _ = u + |t| := by rw [abs_of_nonneg hu]
        _ ≤ (1 + |t|) * (1 + u) := by nlinarith [abs_nonneg t]
    have hp : (1 + u) * (1 + u) ^ ν = (1 + u) ^ (ν + 1) := by
      conv_lhs => lhs; rw [← Real.rpow_one (1 + u)]
      rw [← Real.rpow_add (by linarith)]
      ring_nf
    rw [abs_mul]
    calc |u - t| * |g u| ≤ ((1 + |t|) * (1 + u)) * (C₂ * (1 + u) ^ ν * airyEnv (u : ℂ)) :=
          mul_le_mul hut (hb₂ u hu) (abs_nonneg _) (by positivity)
      _ = (C₂ * (1 + |t|)) * ((1 + u) * (1 + u) ^ ν) * airyEnv (u : ℂ) := by ring
      _ = (C₂ * (1 + |t|)) * (1 + u) ^ (ν + 1) * airyEnv (u : ℂ) := by rw [hp]

lemma HasPolyLeftAiryRightBound.mul_id {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g) :
    HasPolyLeftAiryRightBound (fun u => u * g u) := by
  simpa using hg.mul_id_sub 0

lemma HasPolyLeftAiryRightBound.const_mul {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g) (c : ℝ) :
    HasPolyLeftAiryRightBound (fun u => c * g u) := by
  obtain ⟨hc, ⟨C₁, k, hC₁, hb₁⟩, ⟨C₂, ν, hC₂, hb₂⟩⟩ := hg
  refine ⟨continuous_const.mul hc,
    ⟨|c| * C₁, k, by positivity, fun u hu => by
      rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hb₁ u hu) (abs_nonneg _)⟩,
    ⟨|c| * C₂, ν, by positivity, fun u hu => by
      rw [abs_mul]
      calc |c| * |g u| ≤ |c| * (C₂ * (1 + u) ^ ν * airyEnv (u : ℂ)) :=
            mul_le_mul_of_nonneg_left (hb₂ u hu) (abs_nonneg _)
        _ = (|c| * C₂) * (1 + u) ^ ν * airyEnv (u : ℂ) := by ring⟩⟩

lemma HasPolyLeftAiryRightBound.neg {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g) :
    HasPolyLeftAiryRightBound (fun u => -g u) := by
  simpa using hg.const_mul (-1)

private lemma integrableOn_poly_exp_Iic {C₁ : ℝ} {k : ℕ} {a : ℝ} (hC₁ : 0 ≤ C₁) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => C₁ * (1 + |u|) ^ k * Real.exp (a * u)) (Iic 0) := by
  have hlim : Tendsto (fun v : ℝ => (1 + v) ^ (k : ℝ) * Real.exp (-(a / 2) * v)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (a / 2) (by positivity)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h2 : Tendsto (fun v : ℝ => (1 + v) ^ (k : ℝ) * Real.exp (-(a / 2) * (1 + v))) atTop (𝓝 0) :=
      h1.congr' (Eventually.of_forall fun v => by simp [add_comm])
    have h3 := h2.const_mul (Real.exp (a / 2))
    rw [mul_zero] at h3
    refine h3.congr' (Eventually.of_forall fun v => ?_)
    rw [← mul_assoc, mul_comm (Real.exp (a / 2)), mul_assoc, ← Real.exp_add]
    congr 2; ring
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds zero_lt_one))
  let A' := max A 0
  have hcont : Continuous (fun u : ℝ => C₁ * (1 + |u|) ^ k * Real.exp (a * u)) := by fun_prop
  have h1 : IntegrableOn (fun u : ℝ => C₁ * (1 + |u|) ^ k * Real.exp (a * u)) (Icc (-A') 0) :=
    hcont.continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (fun u : ℝ => C₁ * (1 + |u|) ^ k * Real.exp (a * u)) (Iio (-A')) := by
    have hexp : IntegrableOn (fun v : ℝ => C₁ * Real.exp (-(a / 2) * v)) (Ioi A') :=
      (integrableOn_exp_mul_Ioi (by linarith : -(a / 2) < 0) A').const_mul C₁
    have hmeas : AEStronglyMeasurable (fun u : ℝ => C₁ * (1 + |u|) ^ k * Real.exp (a * u))
        (volume.restrict (Iio (-A'))) := hcont.aestronglyMeasurable.restrict
    have hdom_neg : IntegrableOn (fun u : ℝ => C₁ * Real.exp ((a / 2) * u)) (Iio (-A')) := by
      have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (MeasurableEquiv.neg ℝ).measurableEmbedding (f := fun v : ℝ => C₁ * Real.exp (-(a / 2) * v))
        (s := Ioi A')
      have e : (fun u : ℝ => -u) ⁻¹' (Ioi A') = Iio (-A') := by ext u; simp
      rw [e] at hmp
      simpa [Function.comp_def, mul_neg, neg_mul] using hmp.mpr hexp
    refine hdom_neg.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Iio fun u (hu : u < -A') => ?_)
    have huA : A ≤ -u := (le_max_left A 0).trans (by linarith)
    have hu0 : u ≤ 0 := by linarith [le_max_right A 0]
    have hbd := (hA (-u) huA).le
    rw [Real.norm_of_nonneg (by positivity), abs_of_nonpos hu0]
    have hexp_eq : Real.exp (a * u) = Real.exp (-(a / 2) * (-u)) * Real.exp ((a / 2) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hrpow : (1 + -u) ^ k = (1 + -u) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
    rw [hrpow, hexp_eq]
    calc C₁ * (1 + -u) ^ (k : ℝ) * (Real.exp (-(a / 2) * -u) * Real.exp (a / 2 * u))
        = C₁ * ((1 + -u) ^ (k : ℝ) * Real.exp (-(a / 2) * -u)) * Real.exp (a / 2 * u) := by ring
      _ ≤ C₁ * 1 * Real.exp (a / 2 * u) := by gcongr
      _ = C₁ * Real.exp (a / 2 * u) := by ring
  rw [← Set.Iio_union_Icc_eq_Iic (by linarith [le_max_right A 0] : -A' ≤ 0)]
  exact h2.union h1

lemma integrableOn_airy_exp_Ioi {C₂ ν b : ℝ} (hC₂ : 0 ≤ C₂) :
    IntegrableOn (fun u : ℝ => C₂ * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp (b * u)) (Ioi 0) := by
  let b' := max b 0
  have hb' : 0 ≤ b' := le_max_right _ _
  have hlim : Tendsto (fun u : ℝ => (1 + u) ^ ν * Real.exp (-(1 / 3 : ℝ) * u)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν (1 / 3) (by norm_num)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have h2 : Tendsto (fun u : ℝ => (1 + u) ^ ν * Real.exp (-(1 / 3 : ℝ) * (1 + u))) atTop (𝓝 0) :=
      h1.congr' (Eventually.of_forall fun u => by simp [add_comm])
    have h3 := h2.const_mul (Real.exp (1 / 3 : ℝ))
    rw [mul_zero] at h3
    refine h3.congr' (Eventually.of_forall fun u => ?_)
    rw [← mul_assoc, mul_comm (Real.exp (1 / 3 : ℝ)), mul_assoc, ← Real.exp_add]
    congr 2; ring
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds zero_lt_one))
  let A' := max A ((b' + 1) ^ 2)
  have hA'pos : 0 < A' := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hcont : ContinuousOn (fun u : ℝ => C₂ * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp (b * u)) (Ici 0) := by
    refine ((continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
      fun u hu => Or.inl (by linarith [mem_Ici.mp hu] : 0 < 1 + u).ne')).mul ?_).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    refine (ContinuousOn.congr (f := fun u : ℝ => Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) ?_
      fun u hu => at47_env_ofReal_nonneg (mem_Ici.mp hu))
    exact (continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ =>
      Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).rexp
  have h1 : IntegrableOn (fun u : ℝ => C₂ * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp (b * u)) (Ioc 0 A') :=
    (hcont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun u : ℝ => C₂ * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp (b * u)) (Ioi A') := by
    have hdom : IntegrableOn (fun u : ℝ => C₂ * Real.exp (-u)) (Ioi A') :=
      ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) A').const_mul C₂).congr
        (Eventually.of_forall fun u => by simp)
    refine hdom.mono' ((hcont.mono (Ioi_subset_Ici hA'pos.le)).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : A' < u) => ?_)
    have hu0 : 0 ≤ u := (hA'pos.trans hu).le
    have hu_pos : 0 < u := hA'pos.trans hu
    have huA : A ≤ u := (le_max_left _ _).trans hu.le
    have huB : (b' + 1) ^ 2 ≤ u := (le_max_right _ _).trans hu.le
    have hsqrt : b' + 1 ≤ √u := Real.le_sqrt_of_sq_le huB
    have hu32 : (b' + 1) * u ≤ u ^ (3 / 2 : ℝ) := by
      have heq : u ^ (3 / 2 : ℝ) = √u * u := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hu_pos.ne']; norm_num
      rw [heq]; exact mul_le_mul_of_nonneg_right hsqrt hu0
    have hexp_le : airyEnv (u : ℂ) * Real.exp (b * u) ≤ Real.exp (-(1 / 3 : ℝ) * u) * Real.exp (-u) := by
      rw [at47_env_ofReal_nonneg hu0, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hb_le : b * u ≤ b' * u := mul_le_mul_of_nonneg_right (le_max_left b 0) hu0
      nlinarith [mul_nonneg hb' hu0]
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₂ (Real.rpow_nonneg (by linarith) _))
      (airyEnv_pos _).le) (Real.exp_pos _).le)]
    calc C₂ * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp (b * u)
        = (C₂ * (1 + u) ^ ν) * (airyEnv (u : ℂ) * Real.exp (b * u)) := by ring
      _ ≤ (C₂ * (1 + u) ^ ν) * (Real.exp (-(1 / 3 : ℝ) * u) * Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hC₂ (Real.rpow_nonneg (by linarith) _))
      _ = C₂ * ((1 + u) ^ ν * Real.exp (-(1 / 3 : ℝ) * u)) * Real.exp (-u) := by ring
      _ ≤ C₂ * 1 * Real.exp (-u) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA u huA).le hC₂) (Real.exp_pos _).le
      _ = C₂ * Real.exp (-u) := by ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi hA'pos.le]
  exact h1.union h2

lemma HasPolyLeftAiryRightBound.majorant_integrable {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g)
    {a b : ℝ} (ha : 0 < a) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧
      ∀ y ∈ Icc a b, ∀ u : ℝ, |g u * Real.exp (y * u)| ≤ bound u := by
  obtain ⟨_, ⟨C₁, k, hC₁, hb₁⟩, ⟨C₂, ν, hC₂, hb₂⟩⟩ := hg
  let bound : ℝ → ℝ := fun u =>
    if u ≤ 0 then C₁ * (1 + |u|) ^ k * Real.exp (a * u)
    else C₂ * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp (b * u)
  have hi1 := integrableOn_poly_exp_Iic (k := k) hC₁ ha
  have hi2 := integrableOn_airy_exp_Ioi (ν := ν) (b := b) hC₂
  have hfull : Integrable bound := by
    have hleft : IntegrableOn bound (Iic 0) :=
      hi1.congr_fun (fun u hu => by simp [bound, mem_Iic.mp hu]) measurableSet_Iic
    have hright : IntegrableOn bound (Ioi 0) :=
      hi2.congr_fun (fun u hu => by simp [bound, not_le.mpr (mem_Ioi.mp hu)]) measurableSet_Ioi
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hleft.union hright
  refine ⟨bound, hfull, fun y hy u => ?_⟩
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  dsimp [bound]
  split_ifs with hu
  · exact (mul_le_mul (hb₁ u hu) (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hy.1 hu))
      (Real.exp_pos _).le (by positivity)).trans_eq (by ring)
  · have hu0 : 0 ≤ u := (not_le.mp hu).le
    calc |g u| * Real.exp (y * u) ≤ (C₂ * (1 + u) ^ ν * airyEnv (u : ℂ)) * Real.exp (b * u) :=
        mul_le_mul (hb₂ u hu0) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy.2 hu0))
          (Real.exp_pos _).le (mul_nonneg (mul_nonneg hC₂ (Real.rpow_nonneg (by linarith) _))
            (airyEnv_pos _).le)
      _ = _ := by ring

lemma HasPolyLeftAiryRightBound.integrable_exp {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g)
    {y : ℝ} (hy : 0 < y) :
    Integrable (fun u : ℝ => g u * Real.exp (y * u)) := by
  obtain ⟨bound, hb_int, hb⟩ := hg.majorant_integrable (b := y) hy
  exact hb_int.mono' (hg.1.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb y ⟨le_rfl, le_rfl⟩ u)

lemma HasPolyLeftAiryRightBound.hasDerivAt_integral {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g)
    {y₀ : ℝ} (hy₀ : 0 < y₀) :
    HasDerivAt (fun y : ℝ => ∫ u : ℝ, g u * Real.exp (y * u))
      (∫ u : ℝ, (u * g u) * Real.exp (y₀ * u)) y₀ := by
  let a := y₀ / 2
  let b := 3 * y₀ / 2
  have ha : 0 < a := by positivity
  obtain ⟨bound, hb_int, hbd⟩ := hg.mul_id.majorant_integrable (b := b) ha
  have hs : Icc a b ∈ 𝓝 y₀ := Icc_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)
  have hF_meas : ∀ᶠ y in 𝓝 y₀, AEStronglyMeasurable (fun u => g u * Real.exp (y * u)) volume :=
    Eventually.of_forall fun y =>
      (hg.1.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (fun u => (u * g u) * Real.exp (y₀ * u)) volume :=
    ((continuous_id.mul hg.1).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := fun y u => g u * Real.exp (y * u))
    (F' := fun y u => (u * g u) * Real.exp (y * u))
    hs hF_meas (hg.integrable_exp hy₀) hF'_meas ?_ hb_int ?_).2
  · refine Eventually.of_forall fun u y hy => ?_
    simpa [Real.norm_eq_abs] using hbd y hy u
  · refine Eventually.of_forall fun u y _ => ?_
    have hd : HasDerivAt (fun t : ℝ => g u * Real.exp (t * u)) (g u * (u * Real.exp (y * u))) y := by
      have h1 : HasDerivAt (fun t : ℝ => t * u) u y := by simpa using (hasDerivAt_id y).mul_const u
      exact (h1.exp.congr_deriv (by ring)).const_mul (g u)
    exact hd.congr_deriv (by ring)

lemma HasPolyLeftAiryRightBound.contDiffOn_nat {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g)
    (n : ℕ) : ContDiffOn ℝ n (fun y : ℝ => ∫ u : ℝ, g u * Real.exp (y * u)) (Ioi 0) := by
  induction n generalizing g with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun y hy => (hg.hasDerivAt_integral (mem_Ioi.mp hy)).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hg.hasDerivAt_integral (mem_Ioi.mp hy)).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih hg.mul_id).congr fun y hy => (hg.hasDerivAt_integral (mem_Ioi.mp hy)).deriv

lemma HasPolyLeftAiryRightBound.holomorphic_right {g : ℝ → ℝ} (hg : HasPolyLeftAiryRightBound g) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ u : ℝ, ((g u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ)))
      {w : ℂ | 0 < w.re} := by
  intro w₀ hw₀
  have hw₀pos : 0 < w₀.re := hw₀
  let r := w₀.re / 2
  have hr : 0 < r := by positivity
  let a := w₀.re / 2
  let b := 3 * w₀.re / 2
  have ha : 0 < a := by positivity
  obtain ⟨bound, hb_int, hbd⟩ := hg.mul_id.majorant_integrable (b := b) ha
  have hint0 : Integrable (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (w₀ * (u : ℂ))) := by
    obtain ⟨bd0, hbd0_int, hbd0⟩ := hg.majorant_integrable (b := w₀.re) hw₀pos
    refine hbd0_int.mono' ((Complex.continuous_ofReal.comp hg.1).mul
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have heq : ‖((g u : ℝ) : ℂ) * Complex.exp (w₀ * (u : ℂ))‖ = |g u * Real.exp (w₀.re * u)| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        show (w₀ * (u : ℂ)).re = w₀.re * u by simp, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [heq]
    exact hbd0 w₀.re ⟨le_rfl, le_rfl⟩ u
  have hs : closedBall w₀ r ∈ 𝓝 w₀ := closedBall_mem_nhds w₀ hr
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))) volume :=
    Eventually.of_forall fun w =>
      ((Complex.continuous_ofReal.comp hg.1).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => (((u * g u : ℝ) : ℂ) * Complex.exp (w₀ * (u : ℂ)))) volume :=
    ((Complex.continuous_ofReal.comp (continuous_id.mul hg.1)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have hres := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w (u : ℝ) => ((g u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ)))
    (F' := fun w (u : ℝ) => (((u * g u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))))
    hs hF_meas hint0 hF'_meas ?_ hb_int ?_).2
  · exact hres.differentiableAt.differentiableWithinAt
  · refine Eventually.of_forall fun u w hw => ?_
    have hre_bd : w.re ∈ Icc a b := by
      have h1 : |w.re - w₀.re| ≤ r := by
        calc |w.re - w₀.re| = |(w - w₀).re| := by simp
          _ ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
          _ ≤ r := mem_closedBall_iff_norm.mp hw
      have h2 := abs_le.mp h1
      dsimp [a, b, r] at h2 ⊢
      exact ⟨by linarith, by linarith⟩
    have heq : ‖(((u * g u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ)))‖ = |(u * g u) * Real.exp (w.re * u)| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        show (w * (u : ℂ)).re = w.re * u by simp, abs_mul (u * g u) (Real.exp (w.re * u)),
        abs_of_pos (Real.exp_pos _)]
    rw [heq]
    exact hbd w.re hre_bd u
  · refine Eventually.of_forall fun u w _ => ?_
    have hd : HasDerivAt (fun z : ℂ => ((g u : ℝ) : ℂ) * Complex.exp (z * (u : ℂ)))
        (((g u : ℝ) : ℂ) * ((u : ℂ) * Complex.exp (w * (u : ℂ)))) w := by
      have h1 : HasDerivAt (fun z : ℂ => z * (u : ℂ)) (u : ℂ) w := by
        simpa using (hasDerivAt_id w).mul_const (u : ℂ)
      exact (h1.cexp.congr_deriv (by ring)).const_mul _
    exact hd.congr_deriv (by push_cast; ring)

lemma InAiryClass.integrable_exp_nonneg {F : ℂ → ℂ} (hF : InAiryClass F) {y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u)) := by
  rcases hy.eq_or_lt with rfl | hpos
  · simpa using hF.2.1.re
  · exact hF.to_polyLeftAiryRightBound.integrable_exp hpos

lemma InAiryClass.laplace_continuousOn_Ici {F : ℂ → ℂ} (hF : InAiryClass F) :
    ContinuousOn (fun y : ℝ => ∫ u : ℝ, (F (u : ℂ)).re * Real.exp (y * u)) (Ici 0) := by
  intro y₀ hy₀
  obtain ⟨C, ν, hC, hb⟩ := hF.2.2.1
  let bound : ℝ → ℝ := fun u =>
    if u ≤ 0 then |(F (u : ℂ)).re| else C * (1 + u) ^ ν * airyEnv (u : ℂ) * Real.exp ((y₀ + 1) * u)
  have hbi1 : IntegrableOn bound (Iic 0) :=
    hF.2.1.re.abs.integrableOn.congr_fun
      (fun u hu => by simp [bound, mem_Iic.mp hu]) measurableSet_Iic
  have hbi2 : IntegrableOn bound (Ioi 0) :=
    (integrableOn_airy_exp_Ioi (ν := ν) (b := y₀ + 1) hC).congr_fun
      (fun u hu => by simp [bound, not_le.mpr (mem_Ioi.mp hu)]) measurableSet_Ioi
  have hbfull : Integrable bound := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hbi1.union hbi2
  have hmeas : ∀ᶠ (y : ℝ) in 𝓝[Ici 0] y₀,
      AEStronglyMeasurable (fun (u : ℝ) => (F (u : ℂ)).re * Real.exp (y * u)) volume :=
    Eventually.of_forall fun y => (hF.to_polyLeftAiryRightBound.1.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hmem : ∀ᶠ (y : ℝ) in 𝓝[Ici 0] y₀, y ∈ Icc (0 : ℝ) (y₀ + 1) := by
    have hlt : ∀ᶠ (y : ℝ) in 𝓝 y₀, y < y₀ + 1 := eventually_lt_nhds (by linarith)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hlt] with y hy1 hy2
    exact ⟨mem_Ici.mp hy1, hy2.le⟩
  have hbd : ∀ᶠ (y : ℝ) in 𝓝[Ici 0] y₀, ∀ᵐ (u : ℝ) ∂volume,
      ‖(F (u : ℂ)).re * Real.exp (y * u)‖ ≤ bound u := by
    filter_upwards [hmem] with y hy
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp [bound]
    split_ifs with hu
    · exact mul_le_of_le_one_right (abs_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy.1 hu))
    · have hu0 : 0 ≤ u := (not_le.mp hu).le
      have hbu := hb (u : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at hbu
      have hre : |(F (u : ℂ)).re| ≤ C * (1 + u) ^ ν * airyEnv (u : ℂ) :=
        (Complex.abs_re_le_norm _).trans hbu
      exact mul_le_mul hre (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy.2 hu0))
        (Real.exp_pos _).le (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
          (airyEnv_pos _).le)
  have hlim : ∀ᵐ (u : ℝ) ∂volume,
      Tendsto (fun (y : ℝ) => (F (u : ℂ)).re * Real.exp (y * u)) (𝓝[Ici 0] y₀)
        (𝓝 ((F (u : ℂ)).re * Real.exp (y₀ * u))) := by
    refine Eventually.of_forall fun (u : ℝ) => ?_
    have hc : Continuous (fun y : ℝ => (F (u : ℂ)).re * Real.exp (y * u)) := by fun_prop
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_integral_filter_of_dominated_convergence bound hmeas hbd hbfull hlim

/-- **Shared tail-positivity lemma**: if `g` is continuous and integrable on `ℝ`, `g ≥ 0` on `[U, ∞)`,
and `g x₀ > 0` for some `x₀ > U`, then `∫ g(u) e^{y u} du > 0` for all sufficiently large `y ≥ 0`
(used for even-`m` Laplace sign, odd-`m` large-`y` positivity, and right-tail positivity of `H`). -/
lemma laplace_pos_eventually_of_nonneg_tail {g : ℝ → ℝ} (hgc : Continuous g) (hgi : Integrable g)
    (hint : ∀ y : ℝ, 0 ≤ y → Integrable (fun u : ℝ => g u * Real.exp (y * u)))
    {U x₀ : ℝ} (hUx₀ : U < x₀) (hnn : ∀ u : ℝ, U ≤ u → 0 ≤ g u) (hpos : 0 < g x₀) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, Y ≤ y → 0 < ∫ u : ℝ, g u * Real.exp (y * u) := by
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hgc.continuousAt (g x₀ / 2) (by positivity)
  let δ' := min (δ / 2) ((x₀ - U) / 2)
  have hδ' : 0 < δ' := lt_min (half_pos hδ_pos) (by linarith)
  let a := x₀ - δ'
  let b := x₀ + δ'
  have hUa : U < a := by dsimp [a, δ']; linarith [min_le_right (δ / 2) ((x₀ - U) / 2)]
  have hab : a < b := by dsimp [a, b]; linarith
  have hlow : ∀ u ∈ Icc a b, g x₀ / 2 ≤ g u := by
    intro u hu
    have hdist : dist u x₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      have h1 : δ' ≤ δ / 2 := min_le_left _ _
      constructor <;> linarith [hu.1, hu.2]
    have hgdist := hδ hdist
    rw [Real.dist_eq, abs_lt] at hgdist
    linarith
  let M : ℝ := ∫ u : ℝ, |g u|
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  let c₀ : ℝ := (g x₀ / 2) * (b - a)
  have hc₀ : 0 < c₀ := mul_pos (by positivity) (sub_pos.mpr hab)
  let Y : ℝ := max 1 ((Real.log ((M + 1) / c₀) + 1) / (a - U))
  have hY_pos : 0 < Y := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨Y, hY_pos, fun y hy => ?_⟩
  have hy0 : 0 ≤ y := (hY_pos.trans_le hy).le
  have hgy := hint y hy0
  have hleft_bd : -M * Real.exp (y * U) ≤ ∫ u in Iic U, g u * Real.exp (y * u) := by
    have h1 : ∫ u in Iic U, -(g u * Real.exp (y * u)) ≤ ∫ u in Iic U, |g u| * Real.exp (y * U) := by
      refine setIntegral_mono_on hgy.neg.integrableOn (hgi.abs.mul_const _).integrableOn
        measurableSet_Iic fun u hu => ?_
      have hle : -(|g u| * Real.exp (y * U)) ≤ g u * Real.exp (y * u) := by
        have hexp : Real.exp (y * u) ≤ Real.exp (y * U) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hy0)
        calc -(|g u| * Real.exp (y * U)) ≤ -(|g u| * Real.exp (y * u)) := by gcongr
          _ ≤ g u * Real.exp (y * u) := by
              have := neg_abs_le (g u)
              nlinarith [Real.exp_pos (y * u)]
      linarith
    have h2 : ∫ u in Iic U, |g u| * Real.exp (y * U) ≤ M * Real.exp (y * U) := by
      rw [integral_mul_const]
      gcongr
      exact setIntegral_le_integral hgi.abs (Eventually.of_forall fun _ => abs_nonneg _)
    rw [integral_neg] at h1
    linarith
  have hright_lb : c₀ * Real.exp (y * a) ≤ ∫ u in Ioi U, g u * Real.exp (y * u) := by
    have hsub : Icc a b ⊆ Ioi U := fun u hu => lt_of_lt_of_le hUa hu.1
    have h1 : ∫ u in Icc a b, g u * Real.exp (y * u) ≤ ∫ u in Ioi U, g u * Real.exp (y * u) :=
      setIntegral_mono_set hgy.integrableOn
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
          mul_nonneg (hnn u hu.le) (Real.exp_pos _).le)
        (Eventually.of_forall hsub)
    have h2 : c₀ * Real.exp (y * a) ≤ ∫ u in Icc a b, g u * Real.exp (y * u) := by
      have hconst : ∫ _u in Icc a b, (g x₀ / 2) * Real.exp (y * a) = c₀ * Real.exp (y * a) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
        dsimp [c₀]; ring
      rw [← hconst]
      refine setIntegral_mono_on continuousOn_const.integrableOn_Icc hgy.integrableOn
        measurableSet_Icc fun u hu => ?_
      exact mul_le_mul (hlow u hu) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.1 hy0))
        (Real.exp_pos _).le (by linarith [hlow u hu, hpos])
    exact h2.trans h1
  have hsplit : (∫ u in Iic U, g u * Real.exp (y * u)) + ∫ u in Ioi U, g u * Real.exp (y * u) =
      ∫ u : ℝ, g u * Real.exp (y * u) := by
    rw [← compl_Iic]
    exact integral_add_compl measurableSet_Iic hgy
  have hdom : M * Real.exp (y * U) < c₀ * Real.exp (y * a) := by
    have hyY : (Real.log ((M + 1) / c₀) + 1) / (a - U) ≤ y := (le_max_right _ _).trans hy
    have h1 : Real.log ((M + 1) / c₀) < y * (a - U) := by
      have h2 := (div_le_iff₀ (sub_pos.mpr hUa)).mp hyY
      linarith
    have h2 : (M + 1) / c₀ < Real.exp (y * (a - U)) := (Real.log_lt_iff_lt_exp (by positivity)).mp h1
    have h3 : M + 1 < c₀ * Real.exp (y * (a - U)) := by
      simpa [mul_comm] using (div_lt_iff₀ hc₀).mp h2
    have h4 : M < c₀ * Real.exp (y * (a - U)) := by linarith
    have h5 := mul_lt_mul_of_pos_right h4 (Real.exp_pos (y * U))
    calc M * Real.exp (y * U) < c₀ * Real.exp (y * (a - U)) * Real.exp (y * U) := h5
      _ = c₀ * Real.exp (y * a) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  linarith

/-- Unified Hermite–Biehler extremal and quadrature package covering both `(P, Q) = (1, 0)`
(`m = 1`, `G_Ai = airyExtremal`) and all `AiryPQHB P Q` with `Q ≠ 0` (`hbExtremal`). -/
structure ShellHBData where
  P : ℝ[X]
  Q : ℝ[X]
  hHB : AiryPQHB P Q
  S : Finset ℝ
  tm : ℝ
  G : ℂ → ℂ
  S_nonempty : S.Nonempty
  tm_mem : tm ∈ S
  tm_min : ∀ t ∈ S, tm ≤ t
  S_top : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ S → ∀ t ∈ S, x < t
  G_prod_eq : ∀ z : ℂ, G z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2
  G_diff : Differentiable ℂ G
  G_int : Integrable (fun x : ℝ => G (x : ℂ))
  G_env : ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖G u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u
  G_real : ∀ x : ℝ, (G (x : ℂ)).im = 0
  G_integral_zero : (∫ x : ℝ, G (x : ℂ)) = 0
  G_l1_pos : 0 < ∫ x : ℝ, ‖G (x : ℂ)‖
  G_nonneg_left : ∀ x : ℝ, x ≤ tm → 0 ≤ (G (x : ℂ)).re
  G_eq_zero_on_S : ∀ t ∈ S, G (t : ℂ) = 0
  G_deriv_ne_zero : ∀ t ∈ S, deriv G (t : ℂ) ≠ 0
  m_eq : (Q = 0 ∧ S.card = 1) ∨ (Q ≠ 0 ∧ S.card = at47_m P Q)
  quadrature_zero_vanish : ∀ {H : ℂ → ℂ} {C ν : ℝ},
    Differentiable ℂ H → Integrable (fun x : ℝ => H (x : ℂ)) →
    0 ≤ C → (∀ u : ℂ, ‖H u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) →
    (∀ x : ℝ, (H (x : ℂ)).im = 0) →
    (∀ x : ℝ, 0 ≤ (H (x : ℂ)).re) →
    (∀ t ∈ S, (H (t : ℂ)).re = 0) →
    (∀ x : ℝ, x ≤ tm → (H (x : ℂ)).re = 0) →
    ∀ z : ℂ, H z = 0
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

lemma ShellHBData.G_inAiryClass (D : ShellHBData) : InAiryClass D.G :=
  ⟨D.G_diff, D.G_int, D.G_env, D.G_real⟩

/-- Unit-`L¹` normalized extremal profile `G_N / ‖G_N‖₁` on `ℝ`. -/
noncomputable def ShellHBData.normG (D : ShellHBData) (u : ℝ) : ℝ :=
  (D.G (u : ℂ)).re / ∫ x : ℝ, ‖D.G (x : ℂ)‖

lemma ShellHBData.normG_continuous (D : ShellHBData) : Continuous D.normG :=
  ((Complex.continuous_re.comp (D.G_diff.continuous.comp Complex.continuous_ofReal)).div_const _)

lemma ShellHBData.normG_integrable (D : ShellHBData) : Integrable D.normG :=
  D.G_int.re.div_const _

lemma ShellHBData.normG_integral (D : ShellHBData) : ∫ u : ℝ, D.normG u = 0 := by
  unfold ShellHBData.normG
  have hre : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
  rw [integral_div, hre, D.G_integral_zero, Complex.zero_re, zero_div]

lemma ShellHBData.normG_abs_integral (D : ShellHBData) : ∫ u : ℝ, |D.normG u| = 1 := by
  have hnorm : (fun u : ℝ => |D.normG u|) =
      fun u : ℝ => ‖D.G (u : ℂ)‖ / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
    ext u
    unfold ShellHBData.normG
    have hc : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
    rw [abs_div, abs_of_pos D.G_l1_pos]
    congr 1; conv_rhs => rw [hc, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, integral_div, div_self D.G_l1_pos.ne']

lemma ShellHBData.t1_mem (D : ShellHBData) : D.S.max' D.S_nonempty ∈ D.S :=
  Finset.max'_mem _ _

lemma ShellHBData.G_re_tail (D : ShellHBData) {x : ℝ} (hx : D.S.max' D.S_nonempty < x) :
    (D.G (x : ℂ)).re =
      (-1 : ℝ) ^ D.S.card * at47_Nf D.P D.Q x ^ 2 / ∏ t ∈ D.S, (x - t) ∧
    0 < at47_Nf D.P D.Q x ^ 2 ∧
    0 < ∏ t ∈ D.S, (x - t) := by
  have hxS : x ∉ D.S := fun h => not_le.mpr hx (Finset.le_max' D.S x h)
  have hden : 0 < ∏ t ∈ D.S, (x - t) :=
    Finset.prod_pos fun t ht => sub_pos.mpr (lt_of_le_of_lt (Finset.le_max' D.S t ht) hx)
  have hNne : airyPQN D.P D.Q (x : ℂ) ≠ 0 := by
    intro h0
    have := D.S_top x h0 hxS (D.S.max' D.S_nonempty) D.t1_mem
    linarith
  have hNrne : at47_Nf D.P D.Q x ≠ 0 := by
    intro h0; apply hNne; unfold at47_Nf at h0; rw [airyPQN_ofReal, h0]; simp
  have hGeq := at47_F_real_formula D.G_prod_eq hxS
  rw [hGeq, Complex.ofReal_re]
  exact ⟨rfl, sq_pos_of_ne_zero hNrne, hden⟩

/-- Helper turning a real entire nonnegative function on `ℝ` with zero integral into `0` everywhere. -/
private lemma eq_zero_of_nonneg_integral_zero {H : ℂ → ℂ} (hHd : Differentiable ℂ H)
    (hHi : Integrable (fun x : ℝ => H (x : ℂ))) (hHreal : ∀ x : ℝ, (H (x : ℂ)).im = 0)
    (hHnn : ∀ x : ℝ, 0 ≤ (H (x : ℂ)).re) (hHint : (∫ x : ℝ, H (x : ℂ)) = 0) :
    ∀ z : ℂ, H z = 0 := by
  have hre : ∫ x : ℝ, (H (x : ℂ)).re = 0 := by
    have h1 : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hHi
    rw [h1, hHint, Complex.zero_re]
  have hae : (fun x : ℝ => (H (x : ℂ)).re) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hHnn hHi.re).mp hre
  have hzero_real : ∀ x : ℝ, (H (x : ℂ)).re = 0 := by
    have hcont : Continuous (fun x : ℝ => (H (x : ℂ)).re) :=
      Complex.continuous_re.comp (hHd.continuous.comp Complex.continuous_ofReal)
    intro x
    exact congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) x
  exact airy_entire_eq_zero_of_real_interval hHd (by norm_num : (0 : ℝ) < 1)
    fun x _ _ => Complex.ext (hzero_real x) (hHreal x)

/-- One-level Hermite–Biehler data `(P, Q) = (1, 0)` (`N = Ai`, `G_Ai = airyExtremal`). -/
noncomputable def ShellHBData.airy : ShellHBData where
  P := 1
  Q := 0
  hHB := by simpa using airyPQHB_C 1 0 (Or.inl one_ne_zero)
  S := {airyZero 1}
  tm := airyZero 1
  G := airyExtremal
  S_nonempty := Finset.singleton_nonempty _
  tm_mem := Finset.mem_singleton_self _
  tm_min := fun t ht => by rw [Finset.mem_singleton.mp ht]
  S_top := fun x hx hxS t ht => by
    rw [Finset.mem_singleton.mp ht]
    have hx_le : x ≤ 0 := by
      by_contra hpos; push Not at hpos
      rw [airyPQN_ofReal] at hx
      simp only [Polynomial.eval_one, one_mul, Polynomial.eval_zero, zero_mul, add_zero,
        Complex.ofReal_eq_zero] at hx
      exact (airyAi_pos hpos.le).ne' hx
    have hAi : airyAi x = 0 := by
      rw [airyPQN_ofReal] at hx
      simpa using hx
    obtain ⟨n, hn1, rfl⟩ := exists_airyZero_eq hAi hx_le
    have hn_ne : n ≠ 1 := fun h1 => hxS (by subst h1; exact Finset.mem_singleton_self _)
    exact airyZero_lt_of_lt le_rfl (by omega)
  G_prod_eq := fun z => by
    unfold at47_pr airyExtremal airyPQN airyPQc
    rw [Finset.prod_singleton, Finset.card_singleton, Polynomial.map_one, Polynomial.map_zero,
      Polynomial.eval_one, Polynomial.eval_zero, pow_one]
    have e := sub_smul_dslope airyAiC (airyZero 1 : ℂ) z
    rw [smul_eq_mul, airyAiC_airyZero, sub_zero] at e
    push_cast
    calc -(airyAiC z * dslope airyAiC (airyZero 1 : ℂ) z) * (z - (airyZero 1 : ℂ))
        = -(airyAiC z * ((z - (airyZero 1 : ℂ)) * dslope airyAiC (airyZero 1 : ℂ) z)) := by ring
      _ = -(airyAiC z * airyAiC z) := by rw [e]
      _ = (-1 : ℂ) * (1 * airyAiC z + 0 * deriv airyAiC z) ^ 2 := by ring
  G_diff := differentiable_airyExtremal
  G_int := airyExtremal_integrable
  G_env := airyExtremal_attains.2.2.1
  G_real := fun x => airyExtremal_attains.2.2.2.1 x
  G_integral_zero := airyExtremal_integral
  G_l1_pos := by
    have h0ne : airyExtremal 0 ≠ 0 := by
      have hp : airyExtremal 0 * ((0 : ℂ) - (airyZero 1 : ℂ)) = -airyAiC 0 ^ 2 := by
        unfold airyExtremal
        have e := sub_smul_dslope airyAiC (airyZero 1 : ℂ) 0
        rw [smul_eq_mul, airyAiC_airyZero, sub_zero] at e
        calc -(airyAiC 0 * dslope airyAiC (airyZero 1 : ℂ) 0) * ((0 : ℂ) - (airyZero 1 : ℂ))
            = -(airyAiC 0 * (((0 : ℂ) - (airyZero 1 : ℂ)) * dslope airyAiC (airyZero 1 : ℂ) 0)) := by ring
          _ = -airyAiC 0 ^ 2 := by rw [e, sq]
      intro h0
      rw [h0, zero_mul, eq_comm, neg_eq_zero, sq_eq_zero_iff] at hp
      have hn := congrArg norm hp
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, norm_airyAiC_ofReal, Complex.ofReal_zero,
        norm_zero, abs_of_pos (airyAi_pos le_rfl)] at hn
      exact (airyAi_pos le_rfl).ne' hn
    obtain ⟨C, ν, hC, hb⟩ := airyExtremal_attains.2.2.1
    have hre : (∫ x : ℝ, (-airyExtremal (x : ℂ))).re = 0 := by
      rw [integral_neg, Complex.neg_re, airyExtremal_integral, Complex.zero_re, neg_zero]
    obtain ⟨_, _, _, _, hnz⟩ := airy_m1_uniqueness (H := fun z => -airyExtremal z)
      differentiable_airyExtremal.neg airyExtremal_integrable.neg hC
      (fun u => by simpa using hb u) (fun x => neg_eq_zero.mpr (airyExtremal_attains.2.2.2.1 x))
      hre.ge (fun x hx => by rw [Complex.neg_re]; linarith [airyExtremal_nonneg hx])
    exact (hnz ⟨0, neg_ne_zero.mpr h0ne⟩).2.1
  G_nonneg_left := fun x hx => airyExtremal_nonneg hx
  G_eq_zero_on_S := fun t ht => by
    rw [Finset.mem_singleton.mp ht]; unfold airyExtremal; rw [airyAiC_airyZero, zero_mul, neg_zero]
  G_deriv_ne_zero := fun t ht => by
    rw [Finset.mem_singleton.mp ht]
    have h0ne : airyExtremal 0 ≠ 0 := by
      have hp : airyExtremal 0 * ((0 : ℂ) - (airyZero 1 : ℂ)) = -airyAiC 0 ^ 2 := by
        unfold airyExtremal
        have e := sub_smul_dslope airyAiC (airyZero 1 : ℂ) 0
        rw [smul_eq_mul, airyAiC_airyZero, sub_zero] at e
        calc -(airyAiC 0 * dslope airyAiC (airyZero 1 : ℂ) 0) * ((0 : ℂ) - (airyZero 1 : ℂ))
            = -(airyAiC 0 * (((0 : ℂ) - (airyZero 1 : ℂ)) * dslope airyAiC (airyZero 1 : ℂ) 0)) := by ring
          _ = -airyAiC 0 ^ 2 := by rw [e, sq]
      intro h0
      rw [h0, zero_mul, eq_comm, neg_eq_zero, sq_eq_zero_iff] at hp
      have hn := congrArg norm hp
      rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, norm_airyAiC_ofReal, Complex.ofReal_zero,
        norm_zero, abs_of_pos (airyAi_pos le_rfl)] at hn
      exact (airyAi_pos le_rfl).ne' hn
    obtain ⟨C, ν, hC, hb⟩ := airyExtremal_attains.2.2.1
    have hre : (∫ x : ℝ, (-airyExtremal (x : ℂ))).re = 0 := by
      rw [integral_neg, Complex.neg_re, airyExtremal_integral, Complex.zero_re, neg_zero]
    obtain ⟨_, _, _, _, hnz⟩ := airy_m1_uniqueness (H := fun z => -airyExtremal z)
      differentiable_airyExtremal.neg airyExtremal_integrable.neg hC
      (fun u => by simpa using hb u) (fun x => neg_eq_zero.mpr (airyExtremal_attains.2.2.2.1 x))
      hre.ge (fun x hx => by rw [Complex.neg_re]; linarith [airyExtremal_nonneg hx])
    have hd := (hnz ⟨0, neg_ne_zero.mpr h0ne⟩).2.2.2
    intro h0'
    apply hd
    have hderiv_neg : deriv (fun z => -airyExtremal z) (airyZero 1 : ℂ) = -deriv airyExtremal (airyZero 1 : ℂ) :=
      ((differentiable_airyExtremal (airyZero 1 : ℂ)).hasDerivAt.neg).deriv
    rw [hderiv_neg, h0', neg_zero]
  m_eq := Or.inl ⟨rfl, Finset.card_singleton _⟩
  quadrature_zero_vanish := fun {H _ _} hHd hHi hC hHb hHreal hHnn _ hHneg z => by
    have hsum := airyQ_hasSum_unc hHd hHi hC hHb
    have h0 : ∀ n : ℕ, H (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 = 0 := by
      intro n
      have hle : airyZero (n + 1) ≤ airyZero 1 := by
        rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)) with h1 | h1
        · rw [show n + 1 = 1 from h1.symm]
        · exact (airyZero_lt_of_lt le_rfl h1).le
      have hHre : (H (airyZero (n + 1) : ℂ)).re = 0 := hHneg _ hle
      have hHz : H (airyZero (n + 1) : ℂ) = 0 := Complex.ext hHre (hHreal _)
      rw [hHz, zero_div]
    simp_rw [h0] at hsum
    exact eq_zero_of_nonneg_integral_zero hHd hHi hHreal hHnn (hsum.unique hasSum_zero) z
  uniqueness := fun hHd hHi hC hHb hHreal hHint _ hHneg => by
    obtain ⟨b, hb_nn, hH_eq, _, hnz⟩ := airy_m1_uniqueness hHd hHi hC hHb hHreal hHint hHneg
    refine ⟨b, hb_nn, hH_eq, fun h => ?_⟩
    obtain ⟨hb_pos, _, hb_ratio, hd⟩ := hnz h
    exact ⟨hb_pos, hb_ratio, fun t ht => by rwa [Finset.mem_singleton.mp ht]⟩

/-- General Hermite–Biehler data for `(P, Q)` with `AiryPQHB P Q` and `Q ≠ 0`. -/
noncomputable def ShellHBData.ofQNeZero {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    ShellHBData where
  P := P
  Q := Q
  hHB := hHB
  S := hbTopZeros hHB hQ
  tm := hbMinZero hHB hQ
  G := hbExtremal hHB hQ
  S_nonempty := ⟨hbMinZero hHB hQ, (hbTopZeros_spec hHB hQ).2.2.2.1⟩
  tm_mem := (hbTopZeros_spec hHB hQ).2.2.2.1
  tm_min := (hbTopZeros_spec hHB hQ).2.2.2.2
  S_top := (hbTopZeros_spec hHB hQ).2.2.1
  G_prod_eq := (hbExtremal_spec hHB hQ).2.1
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
  m_eq := Or.inr ⟨hQ, (hbTopZeros_spec hHB hQ).1⟩
  quadrature_zero_vanish := fun {H _ _} hHd hHi hC hHb hHreal hHnn hHS hHneg z => by
    have hsum := airyPQ_hasSum_unc hHB hQ hHd hHi hC hHb
    have hs := hbTopZeros_spec hHB hQ
    have h0 : ∀ w : {w : ℂ // airyPQN P Q w = 0},
        H w.1 * (airyPQD P Q w.1 / airyPQN' P Q w.1 ^ 2) = 0 := by
      intro w
      have hwr := airyPQ_zero_eq_ofReal hHB w.2
      have hw_re : (H (w.1.re : ℂ)).re = 0 := by
        by_cases hwS : w.1.re ∈ hbTopZeros hHB hQ
        · exact hHS w.1.re hwS
        · have hw_lt : w.1.re < hbMinZero hHB hQ :=
            hs.2.2.1 w.1.re (by rw [← hwr]; exact w.2) hwS _ hs.2.2.2.1
          exact hHneg w.1.re hw_lt.le
      have hw0 : H w.1 = 0 := by rw [hwr]; exact Complex.ext hw_re (hHreal _)
      rw [hw0, zero_mul]
    simp_rw [h0] at hsum
    exact eq_zero_of_nonneg_integral_zero hHd hHi hHreal hHnn (hsum.unique hasSum_zero) z
  uniqueness := fun hHd hHi hC hHb hHreal hHint hHS hHneg => by
    obtain ⟨b, hb_nn, hH_eq, hnz⟩ := hbExtremal_uniqueness hHB hQ hHd hHi hC hHb hHreal hHint hHS hHneg
    exact ⟨b, hb_nn, hH_eq, fun h => let r := hnz h; ⟨r.1, r.2.2.1, r.2.2.2⟩⟩

/-- General Hermite–Biehler data for ANY `AiryPQHB P Q` (`Q = 0` or `Q ≠ 0`). -/
noncomputable def ShellHBData.ofAiryPQHB {P Q : ℝ[X]} (hHB : AiryPQHB P Q) : ShellHBData :=
  if hQ : Q = 0 then ShellHBData.airy else ShellHBData.ofQNeZero hHB hQ

/-- Clark two-node Hermite–Biehler data `(P, Q) = (cos α, -sin α)` (`m = 2` even). -/
noncomputable def ShellHBData.clark {α : ℝ} (hα : Real.sin α ≠ 0) : ShellHBData :=
  ShellHBData.ofQNeZero
    (airyPQHB_C (Real.cos α) (-Real.sin α) (Or.inr (neg_ne_zero.mpr hα)))
    (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr hα))

lemma ShellHBData.tm_le_airyZero_one (D : ShellHBData) : D.tm ≤ airyZero 1 := by
  have hre : ∫ x : ℝ, (D.G (x : ℂ)).re ≤ 0 := by
    have h1 : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
    rw [h1, D.G_integral_zero, Complex.zero_re]
  have hx : ∃ x₀ : ℝ, D.G (x₀ : ℂ) ≠ 0 := by
    by_contra h0; push Not at h0
    have hl : ∫ x : ℝ, ‖D.G (x : ℂ)‖ = 0 := by
      have hz : (fun x : ℝ => ‖D.G (x : ℂ)‖) = 0 := funext fun x => by simp [h0 x]
      simp [hz]
    linarith [D.G_l1_pos]
  obtain ⟨x₀, hx₀⟩ := hx
  exact airy_sign_uncertainty D.G_diff D.G_int D.G_env.choose_spec.choose_spec.1
    D.G_env.choose_spec.choose_spec.2 D.G_real D.G_nonneg_left hre ⟨(x₀ : ℂ), hx₀⟩

/-- **Theorem H.14 (even-`m` Laplace sign theorem)**: for every Hermite–Biehler configuration `D`
with even `m = D.S.card`, `∃ y > 0, airyLaplace (-G_N) y < 0` (`airyLaplace G_N y > 0`), without
numerical estimates. -/
theorem even_m_laplace_sign (D : ShellHBData) (heven : Even D.S.card) :
    ∃ y : ℝ, 0 < y ∧ airyLaplace (fun u => -(D.G (u : ℂ)).re) y < 0 := by
  let t₁ := D.S.max' D.S_nonempty
  have hG_tail : ∀ u : ℝ, t₁ ≤ u → 0 ≤ (D.G (u : ℂ)).re := by
    intro u hu
    rcases hu.eq_or_lt with rfl | hlt
    · rw [D.G_eq_zero_on_S t₁ D.t1_mem, Complex.zero_re]
    · obtain ⟨hform, hNsq, hden⟩ := D.G_re_tail hlt
      rw [hform, heven.neg_one_pow, one_mul]
      exact div_nonneg hNsq.le hden.le
  obtain ⟨hform, hNsq, hden⟩ := D.G_re_tail (lt_add_one t₁)
  have hG_pos : 0 < (D.G ((t₁ + 1 : ℝ) : ℂ)).re := by
    rw [hform, heven.neg_one_pow, one_mul]
    exact div_pos hNsq hden
  obtain ⟨Y, hY, hpos⟩ := laplace_pos_eventually_of_nonneg_tail
    D.G_inAiryClass.to_polyLeftAiryRightBound.1 D.G_int.re
    (fun y hy => D.G_inAiryClass.integrable_exp_nonneg hy)
    (lt_add_one t₁) hG_tail hG_pos
  refine ⟨Y, hY, ?_⟩
  have hneg : airyLaplace (fun u => -(D.G (u : ℂ)).re) Y =
      -airyLaplace (fun u => (D.G (u : ℂ)).re) Y := by
    unfold airyLaplace
    simp_rw [neg_mul]
    rw [integral_neg, mul_neg]
  rw [hneg, neg_lt_zero]
  unfold airyLaplace
  exact mul_pos (Real.exp_pos _) (hpos Y le_rfl)

lemma shell_clark_even (α : ℝ) (hα : Real.sin α ≠ 0) :
    Even (ShellHBData.clark hα).S.card := by
  have hm : (ShellHBData.clark hα).S.card = 2 := by
    have hsp := hbTopZeros_spec
      (airyPQHB_C (Real.cos α) (-Real.sin α) (Or.inr (neg_ne_zero.mpr hα)))
      (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr hα))
    change (hbTopZeros
      (airyPQHB_C (Real.cos α) (-Real.sin α) (Or.inr (neg_ne_zero.mpr hα)))
      (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr hα))).card = 2
    rw [hsp.1]
    unfold at47_m
    simp [Polynomial.natDegree_C]
  rw [hm]; exact even_two

/-! ### Section 1b: Factored Laplace Differential Operator (`eq:ce-laplace-ode`) and `m = 1` Sign -/

/-- Canonical Laplace integral `F_N(y) = ∫ (-G_N(u)) e^{yu} du`. -/
noncomputable def shellLaplaceF (D : ShellHBData) (y : ℝ) : ℝ :=
  ∫ u : ℝ, (-(D.G (u : ℂ)).re) * Real.exp (y * u)

lemma shellLaplaceF_zero (D : ShellHBData) : shellLaplaceF D 0 = 0 := by
  unfold shellLaplaceF
  simp_rw [zero_mul, Real.exp_zero, mul_one]
  have hre : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
  rw [integral_neg, hre, D.G_integral_zero, Complex.zero_re, neg_zero]

lemma shellLaplaceF_continuousOn (D : ShellHBData) : ContinuousOn (shellLaplaceF D) (Ici 0) := by
  have heq : shellLaplaceF D = fun y => -(∫ u : ℝ, (D.G (u : ℂ)).re * Real.exp (y * u)) := by
    ext y; unfold shellLaplaceF; simp_rw [neg_mul]; rw [integral_neg]
  rw [heq]
  exact D.G_inAiryClass.laplace_continuousOn_Ici.neg

lemma airyLaplace_negG_eq (D : ShellHBData) (y : ℝ) :
    airyLaplace (fun u => -(D.G (u : ℂ)).re) y = Real.exp (-(y ^ 3) / 12) * shellLaplaceF D y := rfl

/-- Iterative application of the first-order operators `(∂_y - t)` along a list of nodes. -/
noncomputable def laplaceApply : List ℝ → (ℝ → ℝ) → (ℝ → ℝ)
  | [], F => F
  | t :: ts, F => laplaceApply ts (fun y => deriv F y - t * F y)

lemma laplaceApply_eqOn_congr :
    ∀ (L : List ℝ) {f₁ f₂ : ℝ → ℝ}, EqOn f₁ f₂ (Ioi 0) →
      EqOn (laplaceApply L f₁) (laplaceApply L f₂) (Ioi 0)
  | [], _, _, h => h
  | t :: ts, f₁, f₂, h => by
    refine laplaceApply_eqOn_congr ts (fun y hy => ?_)
    have hev : f₁ =ᶠ[𝓝 y] f₂ :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioi 0, isOpen_Ioi.mem_nhds hy, h⟩
    rw [hev.deriv_eq, h hy]

lemma laplaceApply_eq_integral (g : ℝ → ℝ) (hg : HasPolyLeftAiryRightBound g) (L : List ℝ) :
    ∀ y : ℝ, 0 < y →
      laplaceApply L (fun s => ∫ u : ℝ, g u * Real.exp (s * u)) y =
        ∫ u : ℝ, (L.map (fun t => u - t)).prod * g u * Real.exp (y * u) := by
  induction L generalizing g with
  | nil => intro y _; simp [laplaceApply]
  | cons t ts ih =>
    intro y hy
    have hdiff_eq : EqOn (fun r => deriv (fun z => ∫ u : ℝ, g u * Real.exp (z * u)) r -
          t * ∫ u : ℝ, g u * Real.exp (r * u))
        (fun s => ∫ u : ℝ, ((u - t) * g u) * Real.exp (s * u)) (Ioi 0) := by
      intro s hs
      have hs0 : 0 < s := mem_Ioi.mp hs
      have hd : deriv (fun z => ∫ u : ℝ, g u * Real.exp (z * u)) s =
          ∫ u : ℝ, (u * g u) * Real.exp (s * u) :=
        (hg.hasDerivAt_integral hs0).deriv
      have hi1 := hg.mul_id.integrable_exp hs0
      have hi2 := (hg.integrable_exp hs0).const_mul t
      change deriv (fun z => ∫ u : ℝ, g u * Real.exp (z * u)) s -
          t * ∫ u : ℝ, g u * Real.exp (s * u) =
        ∫ u : ℝ, ((u - t) * g u) * Real.exp (s * u)
      rw [hd, ← integral_const_mul, ← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      ring
    calc laplaceApply (t :: ts) (fun s => ∫ u : ℝ, g u * Real.exp (s * u)) y
        = laplaceApply ts (fun s => ∫ u : ℝ, ((u - t) * g u) * Real.exp (s * u)) y :=
          laplaceApply_eqOn_congr ts hdiff_eq hy
      _ = ∫ u : ℝ, (ts.map (fun r => u - r)).prod * ((u - t) * g u) * Real.exp (y * u) :=
          ih (fun u => (u - t) * g u) (hg.mul_id_sub t) y hy
      _ = ∫ u : ℝ, ((t :: ts).map (fun r => u - r)).prod * g u * Real.exp (y * u) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only [List.map_cons, List.prod_cons]
          ring

lemma shellLaplaceF_contDiffOn (D : ShellHBData) (n : ℕ) :
    ContDiffOn ℝ n (shellLaplaceF D) (Ioi 0) :=
  D.G_inAiryClass.to_polyLeftAiryRightBound.neg.contDiffOn_nat n

private lemma list_prod_sub_eq_finset_prod (S : Finset ℝ) (L : List ℝ)
    (hnd : L.Nodup) (hmem : ∀ t : ℝ, t ∈ L ↔ t ∈ S) (u : ℝ) :
    (L.map (fun t => u - t)).prod = ∏ t ∈ S, (u - t) := by
  have hto : L.toFinset = S := by ext t; simp [hmem t]
  rw [← hto]
  clear hmem hto S
  induction L with
  | nil => simp
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.mp hnd).1
    have hal : a ∉ l.toFinset := by simpa using ha
    rw [List.map_cons, List.prod_cons, List.toFinset_cons, Finset.prod_insert hal,
      ih (List.nodup_cons.mp hnd).2]

lemma HasPolyLeftAiryRightBound.congr {f g : ℝ → ℝ} (hf : HasPolyLeftAiryRightBound f)
    (h : f = g) : HasPolyLeftAiryRightBound g := h ▸ hf

private lemma HasPolyLeftAiryRightBound.mul_list_sub :
    ∀ (L : List ℝ) {f : ℝ → ℝ}, HasPolyLeftAiryRightBound f →
      HasPolyLeftAiryRightBound (fun u => (L.map (fun t => u - t)).prod * f u)
  | [], _, hf => by simpa using hf
  | t :: ts, f, hf =>
    ((HasPolyLeftAiryRightBound.mul_list_sub ts (hf.mul_id_sub t)).congr (by
      ext u; simp only [List.map_cons, List.prod_cons]; ring))

/-- **Factored Laplace ODE (`eq:ce-laplace-ode`)**: applying `∏_{t ∈ S} (∂_y - t)` to `F_N(y)`
produces `(-1)^{m + 1} ∫ N(u)² e^{y u} du`, which has strict sign `(-1)^{m + 1}` for all `y > 0`. -/
theorem laplace_ode_identity (D : ShellHBData) {L : List ℝ} (hnd : L.Nodup)
    (hmem : ∀ t : ℝ, t ∈ L ↔ t ∈ D.S) {y : ℝ} (hy : 0 < y) :
    laplaceApply L (shellLaplaceF D) y =
      (-1 : ℝ) ^ (D.S.card + 1) * ∫ u : ℝ, at47_Nf D.P D.Q u ^ 2 * Real.exp (y * u) ∧
    0 < ∫ u : ℝ, at47_Nf D.P D.Q u ^ 2 * Real.exp (y * u) := by
  have hg : HasPolyLeftAiryRightBound (fun u => -(D.G (u : ℂ)).re) :=
    D.G_inAiryClass.to_polyLeftAiryRightBound.neg
  let h : ℝ → ℝ := fun u =>
    (-1 : ℝ) ^ (D.S.card + 1) * ((L.map (fun t => u - t)).prod * (-(D.G (u : ℂ)).re))
  have hh_bound : HasPolyLeftAiryRightBound h :=
    (HasPolyLeftAiryRightBound.mul_list_sub L hg).const_mul _
  have hae_not : ∀ᵐ u ∂volume, u ∉ D.S :=
    (Set.Finite.countable D.S.finite_toSet).ae_notMem volume
  have hpow_sq : ((-1 : ℝ) ^ (D.S.card + 1)) * (-1 : ℝ) ^ (D.S.card + 1) = 1 := by
    rw [← pow_add, ← two_mul]; exact Even.neg_one_pow (even_two_mul _)
  have hpow_m : (-1 : ℝ) ^ (D.S.card + 1) * (-1 : ℝ) ^ D.S.card = -1 := by
    rw [pow_succ]; nlinarith [show ((-1 : ℝ) ^ D.S.card) * (-1 : ℝ) ^ D.S.card = 1 from by
      rw [← pow_add, ← two_mul]; exact Even.neg_one_pow (even_two_mul _)]
  have hh_eq_ae : h =ᵐ[volume] fun u => at47_Nf D.P D.Q u ^ 2 := by
    filter_upwards [hae_not] with u hu
    have hprod := list_prod_sub_eq_finset_prod D.S L hnd hmem u
    have hG := at47_F_real_formula D.G_prod_eq hu
    have hden_ne : (∏ t ∈ D.S, (u - t)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun t ht => sub_ne_zero.mpr (fun he => hu (he ▸ ht))
    dsimp [h]
    rw [hprod, hG, Complex.ofReal_re]
    field_simp [hden_ne]
    calc _ = -(((-1 : ℝ) ^ (D.S.card + 1) * (-1 : ℝ) ^ D.S.card) * at47_Nf D.P D.Q u ^ 2) := by ring
      _ = -((-1 : ℝ) * at47_Nf D.P D.Q u ^ 2) := by rw [hpow_m]
      _ = at47_Nf D.P D.Q u ^ 2 := by ring
  have hint_h : Integrable (fun u => h u * Real.exp (y * u)) := hh_bound.integrable_exp hy
  have hint_eq : ∫ u : ℝ, h u * Real.exp (y * u) =
      ∫ u : ℝ, at47_Nf D.P D.Q u ^ 2 * Real.exp (y * u) :=
    integral_congr_ae (hh_eq_ae.mono fun u hu => by dsimp only; rw [hu])
  have hlhs : laplaceApply L (shellLaplaceF D) y =
      (-1 : ℝ) ^ (D.S.card + 1) * ∫ u : ℝ, h u * Real.exp (y * u) := by
    rw [show shellLaplaceF D = fun s => ∫ u : ℝ, (-(D.G (u : ℂ)).re) * Real.exp (s * u) from rfl,
      laplaceApply_eq_integral _ hg L y hy, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [h]
    calc (L.map (fun t => u - t)).prod * -(D.G (u : ℂ)).re * Real.exp (y * u)
        = 1 * ((L.map (fun t => u - t)).prod * -(D.G (u : ℂ)).re * Real.exp (y * u)) := by ring
      _ = ((-1 : ℝ) ^ (D.S.card + 1) * (-1 : ℝ) ^ (D.S.card + 1)) *
            ((L.map (fun t => u - t)).prod * -(D.G (u : ℂ)).re * Real.exp (y * u)) := by rw [hpow_sq]
      _ = _ := by ring
  have hh_nn_ae : ∀ᵐ u ∂volume, 0 ≤ h u * Real.exp (y * u) := by
    filter_upwards [hh_eq_ae] with u hu
    rw [hu]
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have x₀_pos : 0 < h (D.S.max' D.S_nonempty + 1) * Real.exp (y * (D.S.max' D.S_nonempty + 1)) := by
    have hxS : D.S.max' D.S_nonempty + 1 ∉ D.S :=
      fun hm => by linarith [Finset.le_max' D.S _ hm]
    have hprod := list_prod_sub_eq_finset_prod D.S L hnd hmem (D.S.max' D.S_nonempty + 1)
    obtain ⟨hform, hNsq, _⟩ := D.G_re_tail (lt_add_one (D.S.max' D.S_nonempty))
    have hden_ne : (∏ t ∈ D.S, (D.S.max' D.S_nonempty + 1 - t)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun t ht => sub_ne_zero.mpr (fun he => hxS (he ▸ ht))
    have hhx : h (D.S.max' D.S_nonempty + 1) = at47_Nf D.P D.Q (D.S.max' D.S_nonempty + 1) ^ 2 := by
      dsimp [h]
      rw [hprod, hform]
      field_simp [hden_ne]
      calc _ = -(((-1 : ℝ) ^ (D.S.card + 1) * (-1 : ℝ) ^ D.S.card) *
            at47_Nf D.P D.Q (D.S.max' D.S_nonempty + 1) ^ 2) := by ring
        _ = -((-1 : ℝ) * at47_Nf D.P D.Q (D.S.max' D.S_nonempty + 1) ^ 2) := by rw [hpow_m]
        _ = at47_Nf D.P D.Q (D.S.max' D.S_nonempty + 1) ^ 2 := by ring
    rw [hhx]
    exact mul_pos hNsq (Real.exp_pos _)
  have hpos_int : 0 < ∫ u : ℝ, h u * Real.exp (y * u) := by
    refine (integral_pos_iff_support_of_nonneg_ae hh_nn_ae hint_h).mpr ?_
    have hcont : Continuous (fun u : ℝ => h u * Real.exp (y * u)) :=
      hh_bound.1.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hopen : IsOpen {u : ℝ | 0 < h u * Real.exp (y * u)} := isOpen_lt continuous_const hcont
    exact lt_of_lt_of_le (hopen.measure_pos volume ⟨_, x₀_pos⟩)
      (measure_mono fun u hu => Function.mem_support.mpr hu.ne')
  exact ⟨hlhs.trans (by rw [hint_eq]), hint_eq ▸ hpos_int⟩

/-- For `m = 1` (`D.S.card = 1`), `shellLaplaceF D y > 0` for ALL `y > 0`
(immediately from `(e^{-t₁ y} F_N(y))' = e^{-t₁ y} ∫ N(u)² e^{yu} du > 0` and `F_N(0) = 0`). -/
lemma shellLaplaceF_m1_pos (D : ShellHBData) (hm1 : D.S.card = 1) {y : ℝ} (hy : 0 < y) :
    0 < shellLaplaceF D y := by
  have hS : D.S = {D.tm} := Finset.card_eq_one.mp hm1 |>.elim fun t ht => by
    have := ht ▸ D.tm_mem; rw [Finset.mem_singleton] at this; subst this; exact ht
  let φ : ℝ → ℝ := fun s => Real.exp (-D.tm * s) * shellLaplaceF D s
  have hcont : ContinuousOn φ (Icc 0 y) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((shellLaplaceF_continuousOn D).mono Icc_subset_Ici_self))
  have hderiv : ∀ s ∈ Ioo 0 y, HasDerivAt φ
      (Real.exp (-D.tm * s) * (deriv (shellLaplaceF D) s - D.tm * shellLaplaceF D s)) s := by
    intro s hs
    have hdF0 := D.G_inAiryClass.to_polyLeftAiryRightBound.neg.hasDerivAt_integral hs.1
    have hdF : HasDerivAt (shellLaplaceF D) (deriv (shellLaplaceF D) s) s :=
      hdF0.congr_deriv hdF0.deriv.symm
    have hdE : HasDerivAt (fun z => Real.exp (-D.tm * z)) (-D.tm * Real.exp (-D.tm * s)) s := by
      simpa [mul_comm] using ((hasDerivAt_id s).const_mul (-D.tm)).exp
    exact (hdE.mul hdF).congr_deriv (by ring)
  have hderiv' : ∀ s ∈ Ioo 0 y, 0 < Real.exp (-D.tm * s) *
      (deriv (shellLaplaceF D) s - D.tm * shellLaplaceF D s) := by
    intro s hs
    obtain ⟨hode, hint_pos⟩ := laplace_ode_identity D (L := [D.tm]) (List.nodup_singleton _)
      (fun t => by simp [hS]) hs.1
    rw [hm1, show (1 : ℕ) + 1 = 2 by rfl] at hode
    have : laplaceApply [D.tm] (shellLaplaceF D) s =
        deriv (shellLaplaceF D) s - D.tm * shellLaplaceF D s := rfl
    rw [← this, hode]
    norm_num
    exact mul_pos (Real.exp_pos _) hint_pos
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope φ
    (fun s => Real.exp (-D.tm * s) * (deriv (shellLaplaceF D) s - D.tm * shellLaplaceF D s))
    hy hcont hderiv
  have hφ0 : φ 0 = 0 := by simp [φ, shellLaplaceF_zero]
  rw [hφ0, sub_zero, sub_zero] at hslope
  have hdiv_pos : 0 < φ y / y := hslope ▸ hderiv' ξ hξ
  have hφy : 0 < φ y := by simpa [div_mul_cancel₀ _ hy.ne'] using mul_pos hdiv_pos hy
  exact (mul_pos_iff_of_pos_left (Real.exp_pos (-D.tm * y))).mp hφy

/-! ### Section 2: One-Profile LP Reduction, Threshold Bound `u_* ≤ t_m`, and Attainment (`H.14'`) -/

/-- Two-profile Airy LP feasibility (`eq:ce-laplace-constraint`): `P, Q ∈ 𝒢` with `S = P ≥ 0`,
`‖2 Q‖₁ ≤ 1`, `∫ 2 Q ≤ 0`, `∫_{u_*}^∞ (2 Q)_- ≥ 1/2`, and `H = S - 2 Q` satisfying the shell,
left-tail, and Laplace-nonnegativity constraints. -/
def TwoProfileFeasibleWitness (D : ShellHBData) (ustar : ℝ) (P Q : ℂ → ℂ) : Prop :=
  InAiryClass P ∧ InAiryClass Q ∧
  (∀ u : ℝ, 0 ≤ (P (u : ℂ)).re) ∧
  (∫ u : ℝ, ‖(2 : ℂ) * Q (u : ℂ)‖) ≤ 1 ∧
  (∫ u : ℝ, ((2 : ℂ) * Q (u : ℂ)).re) ≤ 0 ∧
  (1 / 2 : ℝ) ≤ ∫ u in Ioi ustar, max (-((2 : ℂ) * Q (u : ℂ)).re) 0 ∧
  (∀ t ∈ D.S, t ≠ D.tm → ((P (t : ℂ) - 2 * Q (t : ℂ)).re ≤ 0)) ∧
  (∀ u : ℝ, u ≤ ustar → (P (u : ℂ) - 2 * Q (u : ℂ)).re ≤ 0) ∧
  (∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u : ℝ, (P (u : ℂ) - 2 * Q (u : ℂ)).re * Real.exp (y * u))

def TwoProfileFeasible (D : ShellHBData) (ustar : ℝ) : Prop :=
  ∃ P Q : ℂ → ℂ, TwoProfileFeasibleWitness D ustar P Q

/-- Single-profile Airy feasibility: nonzero `H ∈ 𝒢` satisfying the second line of
`(eq:ce-laplace-constraint)`. -/
def OneProfileFeasibleWitness (D : ShellHBData) (ustar : ℝ) (H : ℂ → ℂ) : Prop :=
  InAiryClass H ∧
  (∃ z : ℂ, H z ≠ 0) ∧
  (∀ t ∈ D.S, t ≠ D.tm → (H (t : ℂ)).re ≤ 0) ∧
  (∀ u : ℝ, u ≤ ustar → (H (u : ℂ)).re ≤ 0) ∧
  (∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re * Real.exp (y * u))

def OneProfileFeasible (D : ShellHBData) (ustar : ℝ) : Prop :=
  ∃ H : ℂ → ℂ, OneProfileFeasibleWitness D ustar H

lemma OneProfileFeasible.mono {D : ShellHBData} {u v : ℝ} (huv : u ≤ v)
    (hv : OneProfileFeasible D v) : OneProfileFeasible D u := by
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := hv
  exact ⟨H, h1, h2, h3, fun x hx => h4 x (hx.trans huv), h5⟩

lemma posPart_eq_abs_add_div_two (x : ℝ) : max x 0 = (|x| + x) / 2 := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, abs_of_nonneg hx]; ring
  · rw [max_eq_right hx, abs_of_nonpos hx]; ring

private lemma l1_pos_of_inAiryClass_ne_zero {H : ℂ → ℂ} (hH : InAiryClass H) (hne : ∃ z : ℂ, H z ≠ 0) :
    0 < ∫ x : ℝ, ‖H (x : ℂ)‖ := by
  by_contra hle
  push Not at hle
  have h0 : ∫ x : ℝ, ‖H (x : ℂ)‖ = 0 := le_antisymm hle (integral_nonneg fun _ => norm_nonneg _)
  have hae : (fun x : ℝ => ‖H (x : ℂ)‖) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hH.2.1.norm).mp h0
  have hcont : Continuous (fun x : ℝ => ‖H (x : ℂ)‖) :=
    (hH.1.continuous.comp Complex.continuous_ofReal).norm
  have hzero : ∀ x : ℝ, H (x : ℂ) = 0 := fun x =>
    norm_eq_zero.mp (congrFun ((Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae) x)
  obtain ⟨z, hz⟩ := hne
  exact hz (airy_entire_eq_zero_of_real_interval hH.1 (by norm_num : (0 : ℝ) < 1) (fun x _ _ => hzero x) z)

/-- **Proposition H.14' (part 1 / `par:ce-one-profile`)**: two-profile Airy LP feasibility
`(eq:ce-laplace-constraint)` is equivalent to single-profile feasibility. -/
theorem one_profile_feasible_iff (D : ShellHBData) (ustar : ℝ) :
    TwoProfileFeasible D ustar ↔ OneProfileFeasible D ustar := by
  constructor
  · rintro ⟨P, Q, hP, hQ, hPnn, _, _, hQneg, hS, hleft, hL⟩
    let H : ℂ → ℂ := fun z => P z - 2 * Q z
    have hHin : InAiryClass H := hP.sub (hQ.smul 2)
    have hHne : ∃ z : ℂ, H z ≠ 0 := by
      by_contra h0
      push Not at h0
      have hall0 : ∀ u : ℝ, max (-((2 : ℂ) * Q (u : ℂ)).re) 0 = 0 := by
        intro u
        have hHu : P (u : ℂ) - 2 * Q (u : ℂ) = 0 := h0 (u : ℂ)
        have heq : ((2 : ℂ) * Q (u : ℂ)).re = (P (u : ℂ)).re := by
          have := congrArg Complex.re hHu
          simp only [Complex.sub_re, Complex.zero_re] at this
          have h2 : ((2 : ℂ) * Q (u : ℂ)).re = 2 * (Q (u : ℂ)).re := by simp
          linarith
        rw [heq]
        exact max_eq_right (neg_nonpos.mpr (hPnn u))
      have hint0 : ∫ u in Ioi ustar, max (-((2 : ℂ) * Q (u : ℂ)).re) 0 = 0 := by
        simp_rw [hall0, integral_zero]
      linarith
    exact ⟨H, hHin, hHne, hS, hleft, hL⟩
  · rintro ⟨H, hH, hHne, hS, hleft, hL⟩
    have hNpos : 0 < ∫ x : ℝ, ‖H (x : ℂ)‖ := l1_pos_of_inAiryClass_ne_zero hH hHne
    let N : ℝ := ∫ x : ℝ, ‖H (x : ℂ)‖
    let P : ℂ → ℂ := fun _ => 0
    let Q : ℂ → ℂ := fun z => (-(1 / (2 * N)) : ℝ) * H z
    refine ⟨P, Q, InAiryClass.zero, hH.smul _, fun _ => le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have heq : (fun u : ℝ => ‖(2 : ℂ) * Q (u : ℂ)‖) = fun (u : ℝ) => ‖H (u : ℂ)‖ / N := by
        ext u
        dsimp [Q]
        rw [show (2 : ℂ) * (((-(1 / (2 * N)) : ℝ) : ℂ) * H (u : ℂ)) =
            ((-(1 / N) : ℝ) : ℂ) * H (u : ℂ) by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
          abs_of_pos (one_div_pos.mpr hNpos), one_div, mul_comm, div_eq_mul_inv]
      rw [heq, integral_div, div_self hNpos.ne']
    · have heq : (fun u : ℝ => ((2 : ℂ) * Q (u : ℂ)).re) = fun (u : ℝ) => (-(1 / N)) * (H (u : ℂ)).re := by
        ext u; dsimp [Q]
        rw [show (2 : ℂ) * (((-(1 / (2 * N)) : ℝ) : ℂ) * H (u : ℂ)) =
            ((-(1 / N) : ℝ) : ℂ) * H (u : ℂ) by push_cast; ring,
          Complex.re_ofReal_mul]
      rw [heq, integral_const_mul]
      have hL0 : 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re := by simpa using hL 0 le_rfl
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (one_div_pos.mpr hNpos).le) hL0
    · have heq : (fun u : ℝ => max (-((2 : ℂ) * Q (u : ℂ)).re) 0) =
          fun (u : ℝ) => (1 / N) * max ((H (u : ℂ)).re) 0 := by
        ext u
        have hq : -((2 : ℂ) * Q (u : ℂ)).re = (1 / N) * (H (u : ℂ)).re := by
          dsimp [Q]
          rw [show (2 : ℂ) * (((-(1 / (2 * N)) : ℝ) : ℂ) * H (u : ℂ)) =
              ((-(1 / N) : ℝ) : ℂ) * H (u : ℂ) by push_cast; ring,
            Complex.re_ofReal_mul]
          ring
        have hmax_mul : max ((1 / N) * (H (u : ℂ)).re) 0 = (1 / N) * max ((H (u : ℂ)).re) 0 := by
          rcases le_total ((H (u : ℂ)).re) 0 with hx | hx
          · have hx' : (1 / N) * (H (u : ℂ)).re ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hNpos).le hx
            rw [max_eq_right hx', max_eq_right hx, mul_zero]
          · have hx' : 0 ≤ (1 / N) * (H (u : ℂ)).re :=
              mul_nonneg (one_div_pos.mpr hNpos).le hx
            rw [max_eq_left hx', max_eq_left hx]
        rw [hq, hmax_mul]
      have hpos_int_eq : (fun u : ℝ => max ((H (u : ℂ)).re) 0) =
          fun (u : ℝ) => (‖H (u : ℂ)‖ + (H (u : ℂ)).re) / 2 := by
        ext u
        have hnr : ‖H (u : ℂ)‖ = |(H (u : ℂ)).re| := by
          have hc : H (u : ℂ) = ((H (u : ℂ)).re : ℂ) := Complex.ext rfl (hH.2.2.2 u)
          conv_lhs => rw [hc, Complex.norm_real, Real.norm_eq_abs]
        rw [hnr, posPart_eq_abs_add_div_two]
      have hint_pos : Integrable (fun u : ℝ => max ((H (u : ℂ)).re) 0) := by
        rw [hpos_int_eq]; exact (hH.2.1.norm.add hH.2.1.re).div_const 2
      have hleft_zero : ∫ u in Iic ustar, max ((H (u : ℂ)).re) 0 = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        exact max_eq_right (hleft u (mem_Iic.mp hu))
      have hsplit : (∫ u in Iic ustar, max ((H (u : ℂ)).re) 0) +
          ∫ u in Ioi ustar, max ((H (u : ℂ)).re) 0 = ∫ u : ℝ, max ((H (u : ℂ)).re) 0 := by
        rw [← compl_Iic]; exact integral_add_compl measurableSet_Iic hint_pos
      have hL0 : 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re := by simpa using hL 0 le_rfl
      have hHre_int : Integrable (fun u : ℝ => (H (u : ℂ)).re) := by simpa using hH.2.1.re
      have hfull_lb : N / 2 ≤ ∫ u : ℝ, max ((H (u : ℂ)).re) 0 := by
        rw [hpos_int_eq, integral_div, integral_add hH.2.1.norm hHre_int]
        dsimp [N]; linarith
      rw [heq, integral_const_mul]
      have hIoi_lb : N / 2 ≤ ∫ u in Ioi ustar, max ((H (u : ℂ)).re) 0 := by linarith
      calc (1 / 2 : ℝ) = (1 / N) * (N / 2) := by field_simp; exact (div_self hNpos.ne').symm
        _ ≤ (1 / N) * ∫ u in Ioi ustar, max ((H (u : ℂ)).re) 0 := by gcongr
    · intro t ht htm
      have heq : (P (t : ℂ) - 2 * Q (t : ℂ)) = ((1 / N : ℝ) : ℂ) * H (t : ℂ) := by
        dsimp [P, Q]; push_cast; ring
      rw [heq, Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hNpos).le (hS t ht htm)
    · intro u hu
      have heq : (P (u : ℂ) - 2 * Q (u : ℂ)) = ((1 / N : ℝ) : ℂ) * H (u : ℂ) := by
        dsimp [P, Q]; push_cast; ring
      rw [heq, Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hNpos).le (hleft u hu)
    · intro y hy
      have heq : (fun u : ℝ => (P (u : ℂ) - 2 * Q (u : ℂ)).re * Real.exp (y * u)) =
          fun (u : ℝ) => (1 / N) * ((H (u : ℂ)).re * Real.exp (y * u)) := by
        ext u; dsimp [P, Q]
        have hre : (0 - (2 * (((-(1 / (2 * N)) : ℝ) : ℂ) * H (u : ℂ))).re) =
            (1 / N) * (H (u : ℂ)).re := by
          rw [← mul_assoc, show (2 : ℂ) * ((-(1 / (2 * N)) : ℝ) : ℂ) = ((-(1 / N) : ℝ) : ℂ) by
            push_cast; ring, Complex.re_ofReal_mul]
          ring
        rw [hre]; ring
      rw [heq, integral_const_mul]
      exact mul_nonneg (one_div_pos.mpr hNpos).le (hL y hy)

/-- **Proposition H.14' (parts 2 & 3 / `par:ce-one-profile`)**: every feasible threshold obeys
`u_* ≤ t_m`, and `u_* = t_m` is feasible iff `∀ y > 0, 0 ≤ airyLaplace (-G_N) y`. -/
theorem one_profile_threshold_le_and_endpoint_iff (D : ShellHBData) :
    (∀ ustar : ℝ, OneProfileFeasible D ustar → ustar ≤ D.tm) ∧
    (OneProfileFeasible D D.tm ↔ ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => -(D.G (u : ℂ)).re) y) := by
  refine ⟨fun ustar hfeas => ?_, ?_⟩
  · by_contra hgt
    push Not at hgt
    obtain ⟨H, hH, hHne, hS, hleft, hL⟩ := hfeas
    obtain ⟨C, ν, hC, hb⟩ := hH.2.2.1
    have hHint_re : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re := by
      have hre : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hH.2.1
      rw [← hre]
      simpa using hL 0 le_rfl
    obtain ⟨b, _, hH_eq, hnz⟩ := D.uniqueness hH.1 hH.2.1 hC hb hH.2.2.2 hHint_re hS
      fun x hx => hleft x (hx.trans hgt.le)
    obtain ⟨_, _, hderiv_ne⟩ := hnz hHne
    have hd_ne := hderiv_ne D.tm D.tm_mem
    have hH_tm : H (D.tm : ℂ) = 0 := by
      rw [hH_eq (D.tm : ℂ), D.G_eq_zero_on_S D.tm D.tm_mem, mul_zero, neg_zero]
    have hmax : IsLocalMax (fun u : ℝ => (H (u : ℂ)).re) D.tm := by
      have : Iio ustar ∈ 𝓝 D.tm := isOpen_Iio.mem_nhds hgt
      filter_upwards [this] with u hu
      rw [hH_tm, Complex.zero_re]
      exact hleft u hu.le
    have hder_re : HasDerivAt (fun u : ℝ => (H (u : ℂ)).re) (deriv H (D.tm : ℂ)).re D.tm := by
      have h1 : HasDerivAt (fun u : ℝ => H (u : ℂ)) (deriv H (D.tm : ℂ)) D.tm :=
        (hH.1 (D.tm : ℂ)).hasDerivAt.comp_ofReal
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm h1
    have hre0 : (deriv H (D.tm : ℂ)).re = 0 := (hmax.hasDerivAt_eq_zero hder_re)
    have hder_im : HasDerivAt (fun u : ℝ => (H (u : ℂ)).im) (deriv H (D.tm : ℂ)).im D.tm := by
      have h1 : HasDerivAt (fun u : ℝ => H (u : ℂ)) (deriv H (D.tm : ℂ)) D.tm :=
        (hH.1 (D.tm : ℂ)).hasDerivAt.comp_ofReal
      exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt D.tm h1
    have him0 : (deriv H (D.tm : ℂ)).im = 0 := by
      have hz : (fun u : ℝ => (H (u : ℂ)).im) = 0 := funext fun u => hH.2.2.2 u
      exact hder_im.unique (hz ▸ hasDerivAt_const D.tm (0 : ℝ))
    exact hd_ne (Complex.ext hre0 him0)
  · constructor
    · rintro ⟨H, hH, hHne, hS, hleft, hL⟩ y hy
      obtain ⟨C, ν, hC, hb⟩ := hH.2.2.1
      have hHint_re : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re := by
        have hre : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hH.2.1
        rw [← hre]
        simpa using hL 0 le_rfl
      obtain ⟨b, _, hH_eq, hnz⟩ := D.uniqueness hH.1 hH.2.1 hC hb hH.2.2.2 hHint_re hS hleft
      obtain ⟨hb_pos, _, _⟩ := hnz hHne
      have hLy := hL y hy.le
      have heq : (fun u : ℝ => (H (u : ℂ)).re * Real.exp (y * u)) =
          fun (u : ℝ) => b * (-(D.G (u : ℂ)).re * Real.exp (y * u)) := by
        ext u; rw [hH_eq (u : ℂ), Complex.neg_re, Complex.re_ofReal_mul]; ring
      rw [heq, integral_const_mul] at hLy
      have hint_nn : 0 ≤ ∫ u : ℝ, -(D.G (u : ℂ)).re * Real.exp (y * u) :=
        nonneg_of_mul_nonneg_right hLy hb_pos
      unfold airyLaplace
      exact mul_nonneg (Real.exp_pos _).le hint_nn
    · intro hL_nn
      refine ⟨fun z => -D.G z, D.G_inAiryClass.neg, ?_, ?_, ?_, ?_⟩
      · by_contra h0
        push Not at h0
        have hl : ∫ x : ℝ, ‖D.G (x : ℂ)‖ = 0 := by
          have : (fun x : ℝ => ‖D.G (x : ℂ)‖) = 0 := funext fun x => by
            simpa [neg_eq_zero] using h0 (x : ℂ)
          simp [this]
        linarith [D.G_l1_pos]
      · intro t ht _
        rw [Complex.neg_re, D.G_eq_zero_on_S t ht, Complex.zero_re, neg_zero]
      · intro u hu
        rw [Complex.neg_re]
        exact neg_nonpos.mpr (D.G_nonneg_left u hu)
      · intro y hy
        rcases hy.eq_or_lt with rfl | hypos
        · have hre : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
          simp_rw [zero_mul, Real.exp_zero, mul_one, Complex.neg_re, integral_neg, hre,
            D.G_integral_zero, Complex.zero_re, neg_zero, le_rfl]
        · have hyL := hL_nn y hypos
          unfold airyLaplace at hyL
          have hint_nn : 0 ≤ ∫ u : ℝ, -(D.G (u : ℂ)).re * Real.exp (y * u) :=
            nonneg_of_mul_nonneg_right hyL (Real.exp_pos _)
          have heq : (fun u : ℝ => (-D.G (u : ℂ)).re * Real.exp (y * u)) =
              fun (u : ℝ) => -(D.G (u : ℂ)).re * Real.exp (y * u) := by
            ext u; rw [Complex.neg_re]
          rw [heq]; exact hint_nn

/-- Compact/sequential-limit extraction package for unit-`L¹` profiles in `𝒢` near the optimal
threshold `u_LP = sup {u_* | OneProfileFeasible D u_*}`. -/
structure AiryCompactnessModel (D : ShellHBData) where
  u₀ : ℝ
  u₀_feasible : OneProfileFeasible D u₀
  C₀ : ℝ
  ν₀ : ℝ
  hC₀ : 0 ≤ C₀
  uniform_env : ∀ ⦃u : ℝ⦄ ⦃H : ℂ → ℂ⦄, u₀ ≤ u →
    OneProfileFeasibleWitness D u H → (∫ x : ℝ, ‖H (x : ℂ)‖) = 1 →
    ∀ z : ℂ, ‖H z‖ ≤ C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z

lemma integrableOn_airyEnv_Ici (C ν y b : ℝ) (hC : 0 ≤ C) :
    IntegrableOn (fun u : ℝ => C * (1 + |u|) ^ ν * airyEnv (u : ℂ) * Real.exp (y * u)) (Ici b) := by
  let a := min b 0
  have ha0 : a ≤ 0 := min_le_right _ _
  have hcont : ContinuousOn (fun u : ℝ => C * (1 + |u|) ^ ν * airyEnv (u : ℂ) * Real.exp (y * u)) (Icc a 0) := by
    refine ((continuousOn_const.mul ((continuousOn_const.add continuousOn_id.abs).rpow_const
      fun u _ => Or.inl (by linarith [abs_nonneg u] : 0 < 1 + |u|).ne')).mul ?_).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    refine ContinuousOn.congr (f := fun _ => (1 : ℝ)) continuousOn_const fun u hu => ?_
    rcases (mem_Icc.mp hu).2.eq_or_lt with h0 | hlt
    · simpa [h0] using at47_env_ofReal_nonneg (le_rfl : (0 : ℝ) ≤ 0)
    · exact airyEnv_ofReal_neg hlt
  have h1 : IntegrableOn (fun u : ℝ => C * (1 + |u|) ^ ν * airyEnv (u : ℂ) * Real.exp (y * u)) (Icc a 0) :=
    hcont.integrableOn_Icc
  have h2 : IntegrableOn (fun u : ℝ => C * (1 + |u|) ^ ν * airyEnv (u : ℂ) * Real.exp (y * u)) (Ioi 0) := by
    refine (integrableOn_airy_exp_Ioi (ν := ν) (b := y) hC).congr_fun (fun u hu => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hu)]
  have hunion : Icc a 0 ∪ Ioi 0 = Ici a := Icc_union_Ioi_eq_Ici ha0
  exact (h1.union h2).congr_set_ae (by rw [hunion]) |>.mono_set (Ici_subset_Ici.mpr (min_le_left b 0))

/-- **Proposition H.14' (part 4 / `par:ce-one-profile`)**: attainment of the one-profile LP supremum
`u_LP = max {u_* | OneProfileFeasible D u_*}` under `AiryCompactnessModel D`. -/
theorem one_profile_maximizer_exists (D : ShellHBData) (M : AiryCompactnessModel D) :
    ∃ uLP : ℝ, IsGreatest {u : ℝ | OneProfileFeasible D u} uLP := by
  let S : Set ℝ := {u : ℝ | OneProfileFeasible D u}
  have hS_ne : S.Nonempty := ⟨M.u₀, M.u₀_feasible⟩
  have hS_bdd : BddAbove S := ⟨D.tm, fun u hu => (one_profile_threshold_le_and_endpoint_iff D).1 u hu⟩
  let uLP : ℝ := sSup S
  refine ⟨uLP, ?_, fun u hu => le_csSup hS_bdd hu⟩
  have hmem_approx : ∀ n : ℕ, ∃ u ∈ S, uLP - 1 / ((n : ℝ) + 1) < u := by
    intro n
    exact (lt_csSup_iff hS_bdd hS_ne).mp (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
  choose u_raw hu_raw_mem hu_raw_gt using hmem_approx
  let u : ℕ → ℝ := fun n => max M.u₀ (u_raw n)
  have hu_mem : ∀ n, u n ∈ S := fun n => by
    rcases le_total M.u₀ (u_raw n) with h | h
    · simpa [u, max_eq_right h] using hu_raw_mem n
    · dsimp [u]; rw [max_eq_left h]; exact M.u₀_feasible
  have hu_ge : ∀ n, M.u₀ ≤ u n := fun n => le_max_left _ _
  have hu_le : ∀ n, u n ≤ uLP := fun n => le_csSup hS_bdd (hu_mem n)
  have hu_lim : Tendsto u atTop (𝓝 uLP) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
      (fun n => (hu_raw_gt n).le.trans (le_max_right _ _)) hu_le
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.sub h0
  have hex : ∀ n, ∃ H : ℂ → ℂ, OneProfileFeasibleWitness D (u n) H ∧ (∫ x : ℝ, ‖H (x : ℂ)‖) = 1 := by
    intro n
    obtain ⟨H₀, hH₀, hH₀ne, hS₀, hleft₀, hL₀⟩ := hu_mem n
    have hNpos : 0 < ∫ x : ℝ, ‖H₀ (x : ℂ)‖ := l1_pos_of_inAiryClass_ne_zero hH₀ hH₀ne
    let N := ∫ x : ℝ, ‖H₀ (x : ℂ)‖
    refine ⟨fun z => ((1 / N : ℝ) : ℂ) * H₀ z, ⟨hH₀.smul _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · obtain ⟨z, hz⟩ := hH₀ne
      exact ⟨z, mul_ne_zero (Complex.ofReal_ne_zero.mpr (one_div_pos.mpr hNpos).ne') hz⟩
    · intro t ht htm
      rw [Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hNpos).le (hS₀ t ht htm)
    · intro x hx
      rw [Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hNpos).le (hleft₀ x hx)
    · intro y hy
      have heq : (fun x : ℝ => (((1 / N : ℝ) : ℂ) * H₀ (x : ℂ)).re * Real.exp (y * x)) =
          fun (x : ℝ) => (1 / N) * ((H₀ (x : ℂ)).re * Real.exp (y * x)) := by
        ext x; rw [Complex.re_ofReal_mul]; ring
      rw [heq, integral_const_mul]
      exact mul_nonneg (one_div_pos.mpr hNpos).le (hL₀ y hy)
    · have heq : (fun x : ℝ => ‖((1 / N : ℝ) : ℂ) * H₀ (x : ℂ)‖) = fun (x : ℝ) => ‖H₀ (x : ℂ)‖ / N := by
        ext x
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hNpos),
          one_div, mul_comm, div_eq_mul_inv]
      rw [heq, integral_div, div_self hNpos.ne']
  choose H hH_wit hH_norm using hex
  have hloc : LocallyBounded H univ := by
    intro K _ hKc
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
    let R' := max R 0
    have hR' : 0 ≤ R' := le_max_right _ _
    refine ⟨M.C₀ * (1 + R') ^ (max M.ν₀ 0) * Real.exp ((4 / 3 : ℝ) * R' ^ (3 / 2 : ℝ)), fun n z hz => ?_⟩
    have hzn : ‖z‖ ≤ R' := (mem_closedBall_zero_iff.mp (hR hz)).trans (le_max_left _ _)
    have hpow : (1 + ‖z‖) ^ M.ν₀ ≤ (1 + R') ^ (max M.ν₀ 0) :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (le_max_left _ _)).trans
        (Real.rpow_le_rpow (by linarith [norm_nonneg z]) (by linarith) (le_max_right _ _))
    have henv : airyEnv z ≤ Real.exp ((4 / 3 : ℝ) * R' ^ (3 / 2 : ℝ)) := by
      unfold airyEnv
      refine Real.exp_le_exp.mpr ?_
      have hre_bd : -(z ^ (3 / 2 : ℂ)).re ≤ R' ^ (3 / 2 : ℝ) := by
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [Complex.zero_cpow (by norm_num), Complex.zero_re, neg_zero]
          exact Real.rpow_nonneg hR' _
        · calc -(z ^ (3 / 2 : ℂ)).re ≤ ‖z ^ (3 / 2 : ℂ)‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
            _ = ‖z ^ ((3 / 2 : ℝ) : ℂ)‖ := by norm_num
            _ = ‖z‖ ^ (3 / 2 : ℝ) := by
                rw [Complex.cpow_def_of_ne_zero hz0, Complex.norm_exp, Complex.mul_re,
                  Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
                  Real.rpow_def_of_pos (norm_pos_iff.mpr hz0), mul_comm]
            _ ≤ R' ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (norm_nonneg z) hzn (by norm_num)
      linarith
    exact (M.uniform_env (hu_ge n) (hH_wit n) (hH_norm n) z).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hpow M.hC₀) henv (airyEnv_pos z).le
        (mul_nonneg M.hC₀ (Real.rpow_nonneg (by linarith) _)))
  obtain ⟨φ, hφ, Hstar, hHstar_diff_on, hTLU⟩ :=
    montel isOpen_univ (fun n => (hH_wit n).1.1.differentiableOn) hloc
  have hHstar_diff : Differentiable ℂ Hstar := differentiableOn_univ.mp hHstar_diff_on
  have hpt : ∀ z : ℂ, Tendsto (fun k => H (φ k) z) atTop (𝓝 (Hstar z)) := fun z => by
    simpa using hTLU.tendsto_at (mem_univ z)
  have hHstar_env : ∀ z : ℂ, ‖Hstar z‖ ≤ M.C₀ * (1 + ‖z‖) ^ M.ν₀ * airyEnv z := fun z =>
    le_of_tendsto (hpt z).norm (Eventually.of_forall fun k =>
      M.uniform_env (hu_ge (φ k)) (hH_wit (φ k)) (hH_norm (φ k)) z)
  have hHstar_real : ∀ x : ℝ, (Hstar (x : ℂ)).im = 0 := fun x =>
    tendsto_nhds_unique ((Complex.continuous_im.continuousAt.tendsto).comp (hpt (x : ℂ)))
      (tendsto_const_nhds.congr fun k => ((hH_wit (φ k)).1.2.2.2 x).symm)
  have hHstar_int : Integrable (fun x : ℝ => Hstar (x : ℂ)) := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => Hstar (x : ℂ)) volume :=
      (hHstar_diff.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
    have hfatou : ∫⁻ x : ℝ, ‖Hstar (x : ℂ)‖ₑ ∂volume ≤ 1 := by
      have hlim_en : ∀ x : ℝ, ‖Hstar (x : ℂ)‖ₑ = Filter.liminf (fun k => ‖H (φ k) (x : ℂ)‖ₑ) atTop := by
        intro x
        have ht : Tendsto (fun k => ‖H (φ k) (x : ℂ)‖ₑ) atTop (𝓝 ‖Hstar (x : ℂ)‖ₑ) :=
          (hpt (x : ℂ)).enorm
        exact ht.liminf_eq.symm
      calc ∫⁻ x : ℝ, ‖Hstar (x : ℂ)‖ₑ ∂volume
          = ∫⁻ x : ℝ, Filter.liminf (fun k => ‖H (φ k) (x : ℂ)‖ₑ) atTop ∂volume := by
            simp_rw [hlim_en]
        _ ≤ Filter.liminf (fun k => ∫⁻ x : ℝ, ‖H (φ k) (x : ℂ)‖ₑ ∂volume) atTop :=
            lintegral_liminf_le fun k => ((hH_wit (φ k)).1.1.continuous.comp
              Complex.continuous_ofReal).measurable.enorm
        _ ≤ 1 := by
            have hk_eq : ∀ k, ∫⁻ x : ℝ, ‖H (φ k) (x : ℂ)‖ₑ ∂volume = 1 := fun k => by
              have hi := (hH_wit (φ k)).1.2.1
              rw [← ofReal_integral_norm_eq_lintegral_enorm hi, hH_norm (φ k), ENNReal.ofReal_one]
            simp_rw [hk_eq]
            simp
    exact ⟨hmeas, lt_of_le_of_lt hfatou ENNReal.one_lt_top⟩
  have hHstar_in : InAiryClass Hstar :=
    ⟨hHstar_diff, hHstar_int, ⟨M.C₀, M.ν₀, M.hC₀, hHstar_env⟩, hHstar_real⟩
  have hHstar_shell : ∀ t ∈ D.S, t ≠ D.tm → (Hstar (t : ℂ)).re ≤ 0 := fun t ht htm =>
    le_of_tendsto ((Complex.continuous_re.continuousAt.tendsto).comp (hpt (t : ℂ)))
      (Eventually.of_forall fun k => (hH_wit (φ k)).2.2.1 t ht htm)
  have hHstar_left : ∀ x : ℝ, x ≤ uLP → (Hstar (x : ℂ)).re ≤ 0 := by
    have hlt_left : ∀ x : ℝ, x < uLP → (Hstar (x : ℂ)).re ≤ 0 := by
      intro x hx
      have hev : ∀ᶠ k in atTop, x ≤ u (φ k) := by
        have := (hu_lim.comp hφ.tendsto_atTop).eventually (eventually_gt_nhds hx)
        exact this.mono fun k hk => hk.le
      exact le_of_tendsto ((Complex.continuous_re.continuousAt.tendsto).comp (hpt (x : ℂ)))
        (hev.mono fun k hk => (hH_wit (φ k)).2.2.2.1 x hk)
    intro x hx
    rcases hx.eq_or_lt with rfl | hxlt
    · have hc : Continuous (fun z : ℝ => (Hstar (z : ℂ)).re) :=
        Complex.continuous_re.comp (hHstar_diff.continuous.comp Complex.continuous_ofReal)
      have hseq : Tendsto (fun k : ℕ => uLP - 1 / ((k : ℝ) + 1)) atTop (𝓝 uLP) := by
        simpa only [sub_zero] using (tendsto_const_nhds (x := uLP)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      exact le_of_tendsto (hc.continuousAt.tendsto.comp hseq)
        (Eventually.of_forall fun k => hlt_left _ (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]))
    · exact hlt_left x hxlt
  have hdom0 := integrableOn_airyEnv_Ici M.C₀ M.ν₀ 0 M.u₀ M.hC₀
  have hHstar_ne : ∃ z : ℂ, Hstar z ≠ 0 := by
    have htail_lim : Tendsto (fun k => ∫ x in Ici M.u₀, max ((H (φ k) (x : ℂ)).re) 0) atTop
        (𝓝 (∫ x in Ici M.u₀, max ((Hstar (x : ℂ)).re) 0)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun x => M.C₀ * (1 + |x|) ^ M.ν₀ * airyEnv (x : ℂ) * Real.exp (0 * x))
        (fun k => (Continuous.max (Complex.continuous_re.comp
          ((hH_wit (φ k)).1.1.continuous.comp Complex.continuous_ofReal)) continuous_const).aestronglyMeasurable.restrict)
        hdom0 ?_ ?_
      · intro k
        refine ae_restrict_of_forall_mem measurableSet_Ici fun x _ => ?_
        have h1 := M.uniform_env (hu_ge (φ k)) (hH_wit (φ k)) (hH_norm (φ k)) (x : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        have hre : |(H (φ k) (x : ℂ)).re| ≤ ‖H (φ k) (x : ℂ)‖ := Complex.abs_re_le_norm _
        have hmax : ‖max ((H (φ k) (x : ℂ)).re) 0‖ ≤ |(H (φ k) (x : ℂ)).re| := by
          rw [Real.norm_of_nonneg (le_max_right _ _)]
          exact max_le (le_abs_self _) (abs_nonneg _)
        simpa using hmax.trans (hre.trans h1)
      · refine ae_restrict_of_forall_mem measurableSet_Ici fun x _ => ?_
        exact ((continuous_id.max continuous_const).continuousAt.tendsto.comp
          (Complex.continuous_re.continuousAt.tendsto.comp (hpt (x : ℂ))))
    have hk_ge : ∀ k, (1 / 2 : ℝ) ≤ ∫ x in Ici M.u₀, max ((H (φ k) (x : ℂ)).re) 0 := by
      intro k
      have hk := hH_wit (φ k)
      have hpos_eq : (fun x : ℝ => max ((H (φ k) (x : ℂ)).re) 0) =
          fun (x : ℝ) => (‖H (φ k) (x : ℂ)‖ + (H (φ k) (x : ℂ)).re) / 2 := by
        ext x
        have hnr : ‖H (φ k) (x : ℂ)‖ = |(H (φ k) (x : ℂ)).re| := by
          have hc : H (φ k) (x : ℂ) = ((H (φ k) (x : ℂ)).re : ℂ) := Complex.ext rfl (hk.1.2.2.2 x)
          conv_lhs => rw [hc, Complex.norm_real, Real.norm_eq_abs]
        rw [hnr, posPart_eq_abs_add_div_two]
      have hint_pos : Integrable (fun x : ℝ => max ((H (φ k) (x : ℂ)).re) 0) := by
        rw [hpos_eq]; exact (hk.1.2.1.norm.add hk.1.2.1.re).div_const 2
      have hleft_zero : ∫ x in Iio M.u₀, max ((H (φ k) (x : ℂ)).re) 0 = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
        exact max_eq_right (hk.2.2.2.1 x ((mem_Iio.mp hx).le.trans (hu_ge (φ k))))
      have hsplit : (∫ x in Iio M.u₀, max ((H (φ k) (x : ℂ)).re) 0) +
          ∫ x in Ici M.u₀, max ((H (φ k) (x : ℂ)).re) 0 = ∫ x : ℝ, max ((H (φ k) (x : ℂ)).re) 0 := by
        rw [← compl_Iio]; exact integral_add_compl measurableSet_Iio hint_pos
      have hL0 : 0 ≤ ∫ x : ℝ, (H (φ k) (x : ℂ)).re := by simpa using hk.2.2.2.2 0 le_rfl
      have hk_re_int : Integrable (fun x : ℝ => (H (φ k) (x : ℂ)).re) := by simpa using hk.1.2.1.re
      rw [hleft_zero, zero_add] at hsplit
      rw [hsplit, hpos_eq, integral_div, integral_add hk.1.2.1.norm hk_re_int,
        hH_norm (φ k)]
      linarith
    have hlim_ge : (1 / 2 : ℝ) ≤ ∫ x in Ici M.u₀, max ((Hstar (x : ℂ)).re) 0 :=
      ge_of_tendsto htail_lim (Eventually.of_forall hk_ge)
    by_contra hzero
    push Not at hzero
    have h0' : ∫ x in Ici M.u₀, max ((Hstar (x : ℂ)).re) 0 = 0 := by
      simp [hzero]
    linarith
  have hHstar_L : ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u : ℝ, (Hstar (u : ℂ)).re * Real.exp (y * u) := by
    intro y hy
    have hdomy := integrableOn_airyEnv_Ici M.C₀ M.ν₀ y M.u₀ M.hC₀
    have htail_lim : Tendsto (fun k => ∫ x in Ioi M.u₀, (H (φ k) (x : ℂ)).re * Real.exp (y * x)) atTop
        (𝓝 (∫ x in Ioi M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x))) := by
      refine tendsto_integral_of_dominated_convergence
        (fun x => M.C₀ * (1 + |x|) ^ M.ν₀ * airyEnv (x : ℂ) * Real.exp (y * x))
        (fun k => (hH_wit (φ k)).1.to_polyLeftAiryRightBound.1.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)) |>.aestronglyMeasurable.restrict)
        (hdomy.mono_set Ioi_subset_Ici_self) ?_ ?_
      · intro k
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_
        have h1 := M.uniform_env (hu_ge (φ k)) (hH_wit (φ k)) (hH_norm (φ k)) (x : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans h1) (Real.exp_pos _).le
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_
        exact ((Complex.continuous_re.continuousAt.tendsto.comp (hpt (x : ℂ))).mul tendsto_const_nhds)
    have hleft_nn : ∀ k, ∀ x ∈ Iic M.u₀, 0 ≤ -(H (φ k) (x : ℂ)).re * Real.exp (y * x) := fun k x hx =>
      mul_nonneg (neg_nonneg.mpr ((hH_wit (φ k)).2.2.2.1 x ((mem_Iic.mp hx).trans (hu_ge (φ k)))))
        (Real.exp_pos _).le
    have hstar_left_nn : ∀ x ∈ Iic M.u₀, 0 ≤ -(Hstar (x : ℂ)).re * Real.exp (y * x) := fun x hx =>
      mul_nonneg (neg_nonneg.mpr (hHstar_left x ((mem_Iic.mp hx).trans (le_csSup hS_bdd M.u₀_feasible))))
        (Real.exp_pos _).le
    have hstar_int : Integrable (fun x : ℝ => (Hstar (x : ℂ)).re * Real.exp (y * x)) :=
      hHstar_in.integrable_exp_nonneg hy
    have hfatou_le : ∫ x in Iic M.u₀, -(Hstar (x : ℂ)).re * Real.exp (y * x) ≤
        ∫ x in Ioi M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x) := by
      have hleft_le_right : ∀ k,
          ∫ x in Iic M.u₀, -(H (φ k) (x : ℂ)).re * Real.exp (y * x) ≤
          ∫ x in Ioi M.u₀, (H (φ k) (x : ℂ)).re * Real.exp (y * x) := by
        intro k
        have hi := (hH_wit (φ k)).1.integrable_exp_nonneg hy
        have hsp := integral_add_compl (measurableSet_Iic (a := M.u₀)) hi
        rw [compl_Iic] at hsp
        have hpos := (hH_wit (φ k)).2.2.2.2 y hy
        rw [← hsp] at hpos
        have hneg : ∫ x in Iic M.u₀, -(H (φ k) (x : ℂ)).re * Real.exp (y * x) =
            -(∫ x in Iic M.u₀, (H (φ k) (x : ℂ)).re * Real.exp (y * x)) := by
          simp_rw [neg_mul]; rw [integral_neg]
        linarith
      have hRHS_en_lim : Tendsto (fun k => ENNReal.ofReal (∫ x in Ioi M.u₀, (H (φ k) (x : ℂ)).re * Real.exp (y * x)))
          atTop (𝓝 (ENNReal.ofReal (∫ x in Ioi M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x)))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp htail_lim
      have hLHS_en_le : ∫⁻ x in Iic M.u₀, ENNReal.ofReal (-(Hstar (x : ℂ)).re * Real.exp (y * x)) ≤
          ENNReal.ofReal (∫ x in Ioi M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x)) := by
        have heq_lim : ∀ x : ℝ, ENNReal.ofReal (-(Hstar (x : ℂ)).re * Real.exp (y * x)) =
            Filter.liminf (fun k => ENNReal.ofReal (-(H (φ k) (x : ℂ)).re * Real.exp (y * x))) atTop := by
          intro x
          have htx : Tendsto (fun k => ENNReal.ofReal (-(H (φ k) (x : ℂ)).re * Real.exp (y * x)))
              atTop (𝓝 (ENNReal.ofReal (-(Hstar (x : ℂ)).re * Real.exp (y * x)))) :=
            ENNReal.continuous_ofReal.continuousAt.tendsto.comp
              (((Complex.continuous_re.continuousAt.tendsto.comp (hpt (x : ℂ))).neg).mul tendsto_const_nhds)
          exact htx.liminf_eq.symm
        calc ∫⁻ x in Iic M.u₀, ENNReal.ofReal (-(Hstar (x : ℂ)).re * Real.exp (y * x))
            = ∫⁻ x in Iic M.u₀, Filter.liminf (fun k => ENNReal.ofReal (-(H (φ k) (x : ℂ)).re * Real.exp (y * x))) atTop := by
              simp_rw [heq_lim]
          _ ≤ Filter.liminf (fun k => ∫⁻ x in Iic M.u₀, ENNReal.ofReal (-(H (φ k) (x : ℂ)).re * Real.exp (y * x))) atTop :=
              lintegral_liminf_le fun k => ENNReal.continuous_ofReal.measurable.comp
                ((((Complex.continuous_re.comp ((hH_wit (φ k)).1.1.continuous.comp
                  Complex.continuous_ofReal)).neg).mul
                  (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).measurable
          _ ≤ Filter.liminf (fun k => ENNReal.ofReal (∫ x in Ioi M.u₀, (H (φ k) (x : ℂ)).re * Real.exp (y * x))) atTop := by
              refine Filter.liminf_le_liminf (Eventually.of_forall fun k => ?_)
                (by isBoundedDefault) (by isBoundedDefault)
              have hik := ((hH_wit (φ k)).1.integrable_exp_nonneg hy).neg.integrableOn (s := Iic M.u₀)
              have hik' : IntegrableOn (fun (x : ℝ) => -(H (φ k) (x : ℂ)).re * Real.exp (y * x)) (Iic M.u₀) :=
                hik.congr_fun (fun x _ => by simp only [Pi.neg_apply]; ring) measurableSet_Iic
              rw [← ofReal_integral_eq_lintegral_ofReal hik'
                (ae_restrict_of_forall_mem measurableSet_Iic (hleft_nn k))]
              exact ENNReal.ofReal_le_ofReal (hleft_le_right k)
          _ = ENNReal.ofReal (∫ x in Ioi M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x)) := hRHS_en_lim.liminf_eq
      have histar_Iic : IntegrableOn (fun (x : ℝ) => -(Hstar (x : ℂ)).re * Real.exp (y * x)) (Iic M.u₀) :=
        (hstar_int.neg.integrableOn (s := Iic M.u₀)).congr_fun
          (fun x _ => by simp only [Pi.neg_apply]; ring) measurableSet_Iic
      rw [← ofReal_integral_eq_lintegral_ofReal histar_Iic
        (ae_restrict_of_forall_mem measurableSet_Iic hstar_left_nn)] at hLHS_en_le
      have hright_nn : 0 ≤ ∫ x in Ioi M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x) :=
        ge_of_tendsto htail_lim (Eventually.of_forall fun k => by
          have hk0 : 0 ≤ ∫ x in Iic M.u₀, -(H (φ k) (x : ℂ)).re * Real.exp (y * x) :=
            setIntegral_nonneg measurableSet_Iic (hleft_nn k)
          linarith [hleft_le_right k])
      exact (ENNReal.ofReal_le_ofReal_iff hright_nn).mp hLHS_en_le
    have hsp := integral_add_compl (measurableSet_Iic (a := M.u₀)) hstar_int
    rw [compl_Iic] at hsp
    have hneg : ∫ x in Iic M.u₀, -(Hstar (x : ℂ)).re * Real.exp (y * x) =
        -(∫ x in Iic M.u₀, (Hstar (x : ℂ)).re * Real.exp (y * x)) := by
      simp_rw [neg_mul]; rw [integral_neg]
    linarith
  exact ⟨Hstar, hHstar_in, hHstar_ne, hHstar_shell, hHstar_left, hHstar_L⟩

/-- Explicit non-vacuity witness for `AiryCompactnessModel` at `D = ShellHBData.airy` (`m = 1`). -/
noncomputable def airyCompactnessModel_nonvacuous : AiryCompactnessModel ShellHBData.airy where
  u₀ := ShellHBData.airy.tm
  u₀_feasible := (one_profile_threshold_le_and_endpoint_iff ShellHBData.airy).2.mpr fun y hy => by
    rw [airyLaplace_negG_eq]
    have hm1 : ShellHBData.airy.S.card = 1 :=
      ShellHBData.airy.m_eq.elim (fun h => h.2) (fun h => False.elim (h.1 rfl))
    exact mul_nonneg (Real.exp_pos _).le (shellLaplaceF_m1_pos ShellHBData.airy hm1 hy).le
  C₀ := ShellHBData.airy.G_env.choose / ∫ x : ℝ, ‖ShellHBData.airy.G (x : ℂ)‖
  ν₀ := ShellHBData.airy.G_env.choose_spec.choose
  hC₀ := div_nonneg ShellHBData.airy.G_env.choose_spec.choose_spec.1 ShellHBData.airy.G_l1_pos.le
  uniform_env := fun {u H} hu hH hnorm z => by
    have hu_le : u ≤ ShellHBData.airy.tm :=
      (one_profile_threshold_le_and_endpoint_iff ShellHBData.airy).1 u ⟨H, hH⟩
    have hueq : u = ShellHBData.airy.tm := le_antisymm hu_le hu
    subst hueq
    obtain ⟨hHin, hHne, hS, hleft, hL⟩ := hH
    obtain ⟨C, ν, hC, hb⟩ := hHin.2.2.1
    have hHint_re : 0 ≤ (∫ x : ℝ, H (x : ℂ)).re := by
      have hre : ∫ x : ℝ, (H (x : ℂ)).re = (∫ x : ℝ, H (x : ℂ)).re := integral_re hHin.2.1
      rw [← hre]
      simpa using hL 0 le_rfl
    obtain ⟨b, _, hH_eq, hnz⟩ := ShellHBData.airy.uniqueness hHin.1 hHin.2.1 hC hb hHin.2.2.2
      hHint_re hS hleft
    obtain ⟨_, hb_ratio, _⟩ := hnz hHne
    rw [hnorm, one_div] at hb_ratio
    have hGbd := ShellHBData.airy.G_env.choose_spec.choose_spec.2 z
    rw [hH_eq z, hb_ratio, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ShellHBData.airy.G_l1_pos)]
    calc (∫ x : ℝ, ‖ShellHBData.airy.G (x : ℂ)‖)⁻¹ * ‖ShellHBData.airy.G z‖
        ≤ (∫ x : ℝ, ‖ShellHBData.airy.G (x : ℂ)‖)⁻¹ *
          (ShellHBData.airy.G_env.choose * (1 + ‖z‖) ^ ShellHBData.airy.G_env.choose_spec.choose * airyEnv z) := by gcongr
      _ = (ShellHBData.airy.G_env.choose / ∫ x : ℝ, ‖ShellHBData.airy.G (x : ℂ)‖) *
          (1 + ‖z‖) ^ ShellHBData.airy.G_env.choose_spec.choose * airyEnv z := by
          rw [div_eq_mul_inv]; ring


/-- info: 'FormalResearch.SignUncertainty.even_m_laplace_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms even_m_laplace_sign

/-- info: 'FormalResearch.SignUncertainty.laplace_ode_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_ode_identity

/-- info: 'FormalResearch.SignUncertainty.shellLaplaceF_m1_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellLaplaceF_m1_pos

/-- info: 'FormalResearch.SignUncertainty.one_profile_feasible_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_profile_feasible_iff

/-- info: 'FormalResearch.SignUncertainty.one_profile_threshold_le_and_endpoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_profile_threshold_le_and_endpoint_iff

/-- info: 'FormalResearch.SignUncertainty.one_profile_maximizer_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_profile_maximizer_exists

/-- info: 'FormalResearch.SignUncertainty.airyCompactnessModel_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyCompactnessModel_nonvacuous

end FormalResearch.SignUncertainty
