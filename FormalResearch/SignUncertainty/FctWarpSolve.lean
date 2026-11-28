/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpInnerDerivs
public import FormalResearch.SignUncertainty.FctWarpFJClass
public import FormalResearch.SignUncertainty.FctWarpContraction
public import FormalResearch.SignUncertainty.FctWarpZero

/-!
# Unconditional zero solve `fct:warp-asymp` (1) (`FctWarpSolveStmt`)

Proves `fctWarpSolve_uncond {K4 : ℝ} (hK4 : 1 ≤ K4) : FctWarpSolveStmt K4` (Paper I,
Proposition `fct:warp-asymp` (1)) via:
* Total differentiability of `fctWarpI K4 ε c` from continuous partial derivatives
  (`hasDerivAt_fctWarpI_L`, `hasDerivAt_fctWarpI_alpha` + `continuousAt_of_dominated`).
* Local inverse derivative of the chart `Ψ = fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ)))` on
  `W.I ×ˢ W.J` (`FctWarpFJCenter`, `FctPhaseBox.fctChart_injOn`, `ContDiffAt.localInverse`).
* Constant invertible leading Jacobian `M` in `(Re, Im)` matching
  `(I * deriv fctG0 (airyZero 1), -I * warpC2Star * iteratedDeriv 2 fctG0 (airyZero 1))`,
  and contraction via `fctWarpI_zero_residual`, `fctWarpI_derivL_at_a1_err`,
  `fctWarpI_derivAlpha_at_a1_err`, and `fct_zero_of_chart`.
* Classification via `fctWarpClass_of_chart` and `fctWarpFJ_of_class`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real ContDiff Interval
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

/-! ### 1. Linear maps, complex-to-pair equivalence, and `C¹` from continuous partials -/

private noncomputable def toPairCLM : ℂ →L[ℝ] ℝ × ℝ := Complex.reCLM.prod Complex.imCLM

private lemma toPairCLM_apply (z : ℂ) : toPairCLM z = (z.re, z.im) := rfl

private lemma toPairCLM_eq_zero_iff (z : ℂ) : toPairCLM z = 0 ↔ z = 0 := by
  simp [toPairCLM, Complex.ext_iff, Prod.ext_iff]

private lemma toPairCLM_norm_le (z : ℂ) : ‖toPairCLM z‖ ≤ ‖z‖ := by
  change ‖(z.re, z.im)‖ ≤ ‖z‖
  rw [Prod.norm_def]
  exact max_le (by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z)
    (by simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm z)

private noncomputable def clmFromCols {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v₁ v₂ : E) : (ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v₁ + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v₂

private lemma clmFromCols_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v₁ v₂ : E) (h : ℝ × ℝ) : clmFromCols v₁ v₂ h = h.1 • v₁ + h.2 • v₂ := rfl

private lemma clmFromCols_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v₁ v₂ : E) : clmFromCols v₁ v₂ (1, 0) = v₁ := by simp [clmFromCols]

private lemma clmFromCols_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v₁ v₂ : E) : clmFromCols v₁ v₂ (0, 1) = v₂ := by simp [clmFromCols]

private lemma clmFromCols_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v₁ v₂ : E) : ‖clmFromCols v₁ v₂‖ ≤ ‖v₁‖ + ‖v₂‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [clmFromCols_apply]
  have h1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have h2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  calc ‖h.1 • v₁ + h.2 • v₂‖ ≤ ‖h.1 • v₁‖ + ‖h.2 • v₂‖ := norm_add_le _ _
    _ = ‖h.1‖ * ‖v₁‖ + ‖h.2‖ * ‖v₂‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖h‖ * ‖v₁‖ + ‖h‖ * ‖v₂‖ := add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = (‖v₁‖ + ‖v₂‖) * ‖h‖ := by ring

private lemma hasFDerivAt_of_continuousAt_partials {f : ℝ × ℝ → ℂ} {dL dA : ℝ × ℝ → ℂ} {p₀ : ℝ × ℝ}
    (hL : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => f (s, y)) (dL (x, y)) x)
    (hA : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => f (x, t)) (dA (x, y)) y)
    (hcL : ContinuousAt dL p₀) (hcA : ContinuousAt dA p₀) :
    HasFDerivAt f (clmFromCols (dL p₀) (dA p₀)) p₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δL, hδL0, hδL⟩ := Metric.continuousAt_iff.mp hcL (ε / 2) (half_pos hε)
  obtain ⟨δA, hδA0, hδA⟩ := Metric.continuousAt_iff.mp hcA (ε / 2) (half_pos hε)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) (lt_min hδL0 hδA0)] with h hh
  rw [mem_ball_zero_iff] at hh
  have hhL : ‖h‖ < δL := lt_of_lt_of_le hh (min_le_left _ _)
  have hhA : ‖h‖ < δA := lt_of_lt_of_le hh (min_le_right _ _)
  have hh1 : |h.1| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_fst_le h
  have hh2 : |h.2| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_snd_le h
  have h1 : ‖f (p₀.1 + h.1, p₀.2 + h.2) - f (p₀.1, p₀.2 + h.2) - h.1 • dL p₀‖ ≤
      (ε / 2) * |h.1| := by
    let g : ℝ → ℂ := (fun s => f (s, p₀.2 + h.2)) - (fun s => s • dL p₀)
    have hg : ∀ s ∈ uIcc p₀.1 (p₀.1 + h.1),
        HasDerivWithinAt g (dL (s, p₀.2 + h.2) - dL p₀) (uIcc p₀.1 (p₀.1 + h.1)) s := fun s _ =>
      (((hL s (p₀.2 + h.2)).sub ((hasDerivAt_id' s).smul_const (dL p₀))).congr_deriv
        (by simp)).hasDerivWithinAt
    have hbd : ∀ s ∈ uIcc p₀.1 (p₀.1 + h.1), ‖dL (s, p₀.2 + h.2) - dL p₀‖ ≤ ε / 2 := by
      intro s hsI
      have hdist : dist (s, p₀.2 + h.2) p₀ < δL := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        have hs1 : |s - p₀.1| ≤ |h.1| := by
          rw [mem_uIcc] at hsI
          rcases hsI with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [abs_le] <;> constructor <;>
            linarith [le_abs_self h.1, neg_abs_le h.1]
        have hs2 : |p₀.2 + h.2 - p₀.2| = |h.2| := by ring_nf
        rw [hs2]
        exact max_lt (lt_of_le_of_lt (hs1.trans hh1) hhL) (lt_of_le_of_lt hh2 hhL)
      exact le_of_lt (by simpa [dist_eq_norm] using hδL hdist)
    have hmv := (convex_uIcc p₀.1 (p₀.1 + h.1)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg hbd left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs, add_sub_cancel_left] at hmv
    have heqg : g (p₀.1 + h.1) - g p₀.1 =
        f (p₀.1 + h.1, p₀.2 + h.2) - f (p₀.1, p₀.2 + h.2) - h.1 • dL p₀ := by
      dsimp only [g, Pi.sub_apply]; rw [add_smul]; abel
    rwa [heqg] at hmv
  have h2 : ‖f (p₀.1, p₀.2 + h.2) - f (p₀.1, p₀.2) - h.2 • dA p₀‖ ≤ (ε / 2) * |h.2| := by
    let g : ℝ → ℂ := (fun t => f (p₀.1, t)) - (fun t => t • dA p₀)
    have hg : ∀ t ∈ uIcc p₀.2 (p₀.2 + h.2),
        HasDerivWithinAt g (dA (p₀.1, t) - dA p₀) (uIcc p₀.2 (p₀.2 + h.2)) t := fun t _ =>
      (((hA p₀.1 t).sub ((hasDerivAt_id' t).smul_const (dA p₀))).congr_deriv
        (by simp)).hasDerivWithinAt
    have hbd : ∀ t ∈ uIcc p₀.2 (p₀.2 + h.2), ‖dA (p₀.1, t) - dA p₀‖ ≤ ε / 2 := by
      intro t htI
      have hdist : dist (p₀.1, t) p₀ < δA := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        have ht2 : |t - p₀.2| ≤ |h.2| := by
          rw [mem_uIcc] at htI
          rcases htI with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [abs_le] <;> constructor <;>
            linarith [le_abs_self h.2, neg_abs_le h.2]
        rw [sub_self, abs_zero]
        exact max_lt (by positivity) (lt_of_le_of_lt (ht2.trans hh2) hhA)
      exact le_of_lt (by simpa [dist_eq_norm] using hδA hdist)
    have hmv := (convex_uIcc p₀.2 (p₀.2 + h.2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg hbd left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs, add_sub_cancel_left] at hmv
    have heqg : g (p₀.2 + h.2) - g p₀.2 =
        f (p₀.1, p₀.2 + h.2) - f (p₀.1, p₀.2) - h.2 • dA p₀ := by
      dsimp only [g, Pi.sub_apply]; rw [add_smul]; abel
    rwa [heqg] at hmv
  have hsplit : f (p₀ + h) - f p₀ - clmFromCols (dL p₀) (dA p₀) h =
      (f (p₀.1 + h.1, p₀.2 + h.2) - f (p₀.1, p₀.2 + h.2) - h.1 • dL p₀) +
      (f (p₀.1, p₀.2 + h.2) - f (p₀.1, p₀.2) - h.2 • dA p₀) := by
    rw [show p₀ + h = (p₀.1 + h.1, p₀.2 + h.2) from Prod.ext rfl rfl, clmFromCols_apply]; abel
  rw [hsplit]
  calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ ≤ (ε / 2) * |h.1| + (ε / 2) * |h.2| := add_le_add h1 h2
    _ ≤ (ε / 2) * ‖h‖ + (ε / 2) * ‖h‖ := add_le_add
        (mul_le_mul_of_nonneg_left hh1 (by positivity))
        (mul_le_mul_of_nonneg_left hh2 (by positivity))
    _ = ε * ‖h‖ := by ring

/-! ### 2. Continuity of `fctWarpI` partial derivatives and total `HasFDerivAt` -/

private lemma fctWarpIntegrand_continuous_param {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hc : 0 < c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    {τ : ℝ} (_hτ : 0 < τ) :
    Continuous (fun p : ℝ × ℝ => fctWarpIntegrand K4 ε c p.1 p.2 τ) := by
  have hm : Continuous (fun p : ℝ × ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 p.1)) := by
    set K_m : ℂ := (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
      Complex.exp (Complex.I * (c : ℂ) * ((-Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ))
    have heq : (fun p : ℝ × ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 p.1)) =
        fun p : ℝ × ℝ => K_m * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (p.1 : ℂ)) := by
      ext p
      have hξ : 0 < fctXi1 p.1 := by unfold fctXi1; positivity
      have hlog : Real.log (π ^ 2 * fctXi1 p.1) = p.1 := by
        unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
      rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 p.1) τ hξ, hlog]
      dsimp only [K_m]
      have hex : Complex.I * (c : ℂ) * ((p.1 * τ - Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
          Complex.I * (c : ℂ) * ((-Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) +
            Complex.I * ((c * τ : ℝ) : ℂ) * (p.1 : ℂ) := by push_cast; ring
      rw [hex, Complex.exp_add]; ring
    rw [heq]
    fun_prop
  have hD : Continuous (fun p : ℝ × ℝ => fctDcompAt K4 c p.2 ((τ : ℂ) * Complex.I)) := by
    have heq : (fun p : ℝ × ℝ => fctDcompAt K4 c p.2 ((τ : ℂ) * Complex.I)) =
        fun p : ℝ × ℝ => fctDcompAt K4 c 0 ((τ : ℂ) * Complex.I) *
          Complex.exp ((p.2 : ℂ) * ((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
            Complex.I * ((p.2 : ℂ) * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ))) := by
      ext p; exact fctDcompAt_alpha_decomp hK4 hc hτ₁ p.2 τ
    rw [heq]
    fun_prop
  unfold fctWarpIntegrand fctWarpA
  exact hm.mul (((continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).mul hD).mul
    continuous_const)

private lemma hasFDerivAt_fctWarpI {K4 ε c : ℝ} (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc1 : 1 ≤ c)
    (hτ₁ : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose) (p₀ : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => fctWarpI K4 ε c p.1 p.2)
      (clmFromCols
        (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c p₀.1 p₀.2 τ)
        (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c p₀.1 p₀.2 τ)) p₀ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨g, hg_int, _, hg_bd⟩ := fctWarpIntegrand_dom hK4 hε hc1 hτ₁
    (L_max := |p₀.1| + 1) (α_max := |p₀.2| + 1) (by positivity) (by positivity)
  have hmem_bd : ∀ p ∈ Metric.ball p₀ 1, ∀ τ ∈ Ioi (0 : ℝ),
      ‖fctWarpIntegrandDerivL K4 ε c p.1 p.2 τ‖ ≤ g τ ∧
      ‖fctWarpIntegrandDerivAlpha K4 ε c p.1 p.2 τ‖ ≤ g τ := by
    intro p hp τ hτ
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hp
    have hL : |p.1| ≤ |p₀.1| + 1 := by
      linarith [abs_sub_abs_le_abs_sub p.1 p₀.1, (max_lt_iff.mp hp).1]
    have hA : |p.2| ≤ |p₀.2| + 1 := by
      linarith [abs_sub_abs_le_abs_sub p.2 p₀.2, (max_lt_iff.mp hp).2]
    exact ⟨(hg_bd hL hA τ hτ).2.1, (hg_bd hL hA τ hτ).2.2⟩
  have hcL : ContinuousAt
      (fun p : ℝ × ℝ => Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c p.1 p.2 τ) p₀ := by
    refine continuousAt_const.mul (continuousAt_of_dominated (bound := g) ?_ ?_ hg_int ?_)
    · exact Eventually.of_forall fun p =>
        (fctWarpIntegrandDerivL_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Metric.ball_mem_nhds p₀ one_pos] with p hp
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => (hmem_bd p hp τ hτ).1
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => Continuous.continuousAt ?_
      have hW := fctWarpIntegrand_continuous_param (K4 := K4) (ε := ε) (c := c) hK4 hc0 hτ₁ hτ
      have hm : Continuous (fun p : ℝ × ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 p.1)) := by
        set K_m : ℂ := (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
          Complex.exp (Complex.I * (c : ℂ) * ((-Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ))
        have heq : (fun p : ℝ × ℝ => mellinK0 c ((τ : ℂ) * Complex.I) (fctXi1 p.1)) =
            fun p : ℝ × ℝ => K_m * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (p.1 : ℂ)) := by
          ext p
          have hξ : 0 < fctXi1 p.1 := by unfold fctXi1; positivity
          have hlog : Real.log (π ^ 2 * fctXi1 p.1) = p.1 := by
            unfold fctXi1; rw [mul_div_cancel₀ _ (pow_ne_zero 2 Real.pi_ne_zero), Real.log_exp]
          rw [FormalResearch.CohnElkies.mellinK0_imag_eq c (fctXi1 p.1) τ hξ, hlog]
          dsimp only [K_m]
          have hex : Complex.I * (c : ℂ) * ((p.1 * τ - Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) =
              Complex.I * (c : ℂ) * ((-Real.pi ^ 2 / 36 * τ ^ 3 + FormalResearch.CohnElkies.edgeR τ : ℝ) : ℂ) +
                Complex.I * ((c * τ : ℝ) : ℂ) * (p.1 : ℂ) := by push_cast; ring
          rw [hex, Complex.exp_add]; ring
        rw [heq]; fun_prop
      have hD : Continuous (fun p : ℝ × ℝ => fctDcompAt K4 c p.2 ((τ : ℂ) * Complex.I)) := by
        have heq : (fun p : ℝ × ℝ => fctDcompAt K4 c p.2 ((τ : ℂ) * Complex.I)) =
            fun p : ℝ × ℝ => fctDcompAt K4 c 0 ((τ : ℂ) * Complex.I) *
              Complex.exp ((p.2 : ℂ) * ((vAlpha 1 (c ^ (-(1 / 4 : ℝ))) τ : ℝ) : ℂ) +
                Complex.I * ((p.2 : ℂ) * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) τ : ℝ) : ℂ))) := by
          ext p; exact fctDcompAt_alpha_decomp hK4 hc0 hτ₁ p.2 τ
        rw [heq]; fun_prop
      unfold fctWarpIntegrandDerivL
      exact (continuous_const.mul hW).add
        (((hm.mul continuous_const).mul hD).mul continuous_const)
  have hcA : ContinuousAt
      (fun p : ℝ × ℝ => Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c p.1 p.2 τ) p₀ := by
    refine continuousAt_const.mul (continuousAt_of_dominated (bound := g) ?_ ?_ hg_int ?_)
    · exact Eventually.of_forall fun p =>
        (fctWarpIntegrandDerivAlpha_continuousOn hK4 hc0 hτ₁).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [Metric.ball_mem_nhds p₀ one_pos] with p hp
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => (hmem_bd p hp τ hτ).2
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => Continuous.continuousAt ?_
      have hW := fctWarpIntegrand_continuous_param (K4 := K4) (ε := ε) (c := c) hK4 hc0 hτ₁ hτ
      unfold fctWarpIntegrandDerivAlpha
      exact hW.mul continuous_const
  exact hasFDerivAt_of_continuousAt_partials
    (fun x y => hasDerivAt_fctWarpI_L hK4 hε hc1 hτ₁ x y)
    (fun x y => hasDerivAt_fctWarpI_alpha hK4 hε hc1 hτ₁ x y)
    hcL hcA

/-! ### 3. Leading Jacobian `M` at `(airyZero 1, 0)` and inverse chart derivative -/

private noncomputable def warpM1 : ℝ := -2 * Real.sqrt π

private noncomputable def warpW2 : ℂ :=
  -Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1)

private lemma warpM1_ne_zero : warpM1 ≠ 0 := by
  unfold warpM1
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  linarith only [hpi]

private lemma warpW2_im_ne_zero : warpW2.im ≠ 0 := by
  have hre : (iteratedDeriv 2 fctG0 (airyZero 1)).re =
      4 * π ^ (3 / 2 : ℝ) * (airyAi' (airyZero 1)) ^ 2 :=
    iteratedDeriv_two_fctG0_airyZero_re
  have hpi : 0 < π ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have hai : 0 < (airyAi' (airyZero 1)) ^ 2 := sq_pos_of_pos airyAi'_first_pos
  have hc2s : 0 < warpC2Star := by
    unfold warpC2Star
    have hts : (1.06 : ℝ) ≤ warpTauStar := warpTauStar_ge
    positivity
  have him : warpW2.im = -warpC2Star * (iteratedDeriv 2 fctG0 (airyZero 1)).re := by
    unfold warpW2
    simp [Complex.mul_im, Complex.mul_re]
  rw [him, hre]
  have hpos : 0 < warpC2Star * (4 * π ^ (3 / 2 : ℝ) * (airyAi' (airyZero 1)) ^ 2) := by positivity
  linarith only [hpos]

private noncomputable def warpMEquiv : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    (clmFromCols (warpM1, (0 : ℝ)) (warpW2.re, warpW2.im))
    (clmFromCols ((warpM1⁻¹ : ℝ), (0 : ℝ)) (-warpW2.re / (warpM1 * warpW2.im), warpW2.im⁻¹))
    (fun ⟨y₁, y₂⟩ => by
      simp only [clmFromCols_apply, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero]
      ext <;> dsimp only <;> field_simp [warpM1_ne_zero, warpW2_im_ne_zero] <;> ring)
    (fun ⟨z₁, z₂⟩ => by
      simp only [clmFromCols_apply, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero]
      ext <;> dsimp only <;> field_simp [warpM1_ne_zero, warpW2_im_ne_zero] <;> ring)

private lemma warpMEquiv_fst :
    warpMEquiv (1, 0) = toPairCLM (Complex.I * deriv fctG0 (airyZero 1)) := by
  have hd := deriv_fctG0_airyZero
  rw [hd]
  have hI : Complex.I * (Complex.I * ((2 * Real.sqrt π : ℝ) : ℂ)) = ((-2 * Real.sqrt π : ℝ) : ℂ) := by
    calc Complex.I * (Complex.I * ((2 * Real.sqrt π : ℝ) : ℂ))
        = Complex.I ^ 2 * ((2 * Real.sqrt π : ℝ) : ℂ) := by ring
      _ = (-1) * ((2 * Real.sqrt π : ℝ) : ℂ) := by rw [Complex.I_sq]
      _ = ((-2 * Real.sqrt π : ℝ) : ℂ) := by push_cast; ring
  rw [hI]
  ext <;> simp [warpMEquiv, clmFromCols_apply, warpM1, toPairCLM_apply]

private lemma warpMEquiv_snd : warpMEquiv (0, 1) = toPairCLM warpW2 := by
  ext <;> simp [warpMEquiv, clmFromCols_apply, toPairCLM_apply]

private noncomputable def invChartDerivEquiv (uL uA lam : ℝ) (huL : uL ≠ 0) (hlam : lam ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((uL • ContinuousLinearMap.fst ℝ ℝ ℝ + uA • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (lam • ContinuousLinearMap.snd ℝ ℝ ℝ))
    (clmFromCols (uL⁻¹, (0 : ℝ)) (-uA / (uL * lam), lam⁻¹))
    (fun ⟨v₁, v₂⟩ => by
      simp only [ContinuousLinearMap.prod_apply, add_apply,
        smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul, clmFromCols_apply, Prod.smul_mk, Prod.mk_add_mk, mul_zero]
      ext <;> dsimp only <;> field_simp [huL, hlam] <;> ring)
    (fun ⟨w₁, w₂⟩ => by
      simp only [ContinuousLinearMap.prod_apply, add_apply,
        smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul, clmFromCols_apply, Prod.smul_mk, Prod.mk_add_mk, mul_zero]
      ext <;> dsimp only <;> field_simp [huL, hlam] <;> ring)

private lemma fctChart_inv_hasFDerivAt {K4 ε c : ℝ} (W : FctWarpChartData K4 ε c)
    (hc0 : 0 < c) {y : ℝ × ℝ}
    (hy : (airyZero 1, (0 : ℝ)) + y ∈
      fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) ''
        (Ioo (W.L_ctr / 2) (2 * W.L_ctr) ×ˢ
          Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))))) :
    let I := Ioo (W.L_ctr / 2) (2 * W.L_ctr)
    let J := Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ)))
    let Ψ := fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)
    let q := (airyZero 1, (0 : ℝ)) + y
    let p := Function.invFunOn Ψ (I ×ˢ J) q
    let uL := FctPhaseBox.uL (fctKappa c) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p
    let uA := FctPhaseBox.uAlpha (fctKappa c) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p
    let lam := c ^ (-(2 / 3 : ℝ))
    p ∈ I ×ˢ J ∧ Ψ p = q ∧
      ∀ (huL : uL ≠ 0) (hlam : lam ≠ 0),
        HasFDerivAt (Function.invFunOn Ψ (I ×ˢ J))
          ((invChartDerivEquiv uL uA lam huL hlam).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) q := by
  intro I J Ψ q p uL uA lam
  obtain ⟨hp_mem, hΨp⟩ := Function.invFunOn_pos hy
  refine ⟨hp_mem, hΨp, fun huL hlam => ?_⟩
  have hpΩ : p ∈ concretePhaseDom W.ellMin ε c := W.h_rect_sub hp_mem
  have hΨ_cd : ContDiffAt ℝ ∞ Ψ p := by
    have h1 := ((contDiffAt_const (c := -fctKappa c)).mul (W.box.atil_contDiffAt hpΩ))
    have h2 := (contDiffAt_const (c := lam)).mul (contDiffAt_snd : ContDiffAt ℝ ∞ Prod.snd p)
    exact h1.prodMk h2
  have hΨ_fd : HasFDerivAt Ψ
      ((invChartDerivEquiv uL uA lam huL hlam : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    ((W.box.chain_rule hpΩ (fctKappa c) lam (Ξhat := id)
      (hasFDerivAt_id (fctChart (fctKappa c) lam (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p))
      (Eventually.of_forall fun _ => rfl)).1).congr_fderiv
      (ContinuousLinearMap.ext fun v => by simp [invChartDerivEquiv, uL, uA])
  have hΨp' : Ψ p = q := hΨp
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hΨ_cd.hasStrictFDerivAt hΨ_fd hn
  set g := hstrict.localInverse Ψ (invChartDerivEquiv uL uA lam huL hlam) p
  have hrinv : ∀ᶠ w in 𝓝 q, Ψ (g w) = w := by
    have := hstrict.eventually_right_inverse
    rwa [hΨp'] at this
  have hgp : g q = p := by
    have := hstrict.localInverse_apply_image
    rwa [hΨp'] at this
  have hgd : HasFDerivAt g
      ((invChartDerivEquiv uL uA lam huL hlam).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) q := by
    have := hstrict.to_localInverse.hasFDerivAt
    rwa [hΨp'] at this
  have hcont : ContinuousAt g q := hgd.continuousAt
  have hmem_nhd : ∀ᶠ w in 𝓝 q, g w ∈ I ×ˢ J := by
    have hopen : IsOpen (I ×ˢ J) := isOpen_Ioo.prod isOpen_Ioo
    exact hcont.eventually_mem (hopen.mem_nhds (by rwa [hgp]))
  have hinj : InjOn Ψ (I ×ˢ J) :=
    W.box.fctChart_injOn (fctKappa_pos hc0) hlam isOpen_Ioo ordConnected_Ioo W.h_rect_sub
  have hev_eq : Function.invFunOn Ψ (I ×ˢ J) =ᶠ[𝓝 q] g := by
    filter_upwards [hrinv, hmem_nhd] with w hw1 hw2
    conv_lhs => rw [← hw1]
    exact hinj.leftInvOn_invFunOn hw2
  exact hgd.congr_of_eventuallyEq hev_eq

/-! ### 4. Uniform `uAlpha` bound on admissible box -/

private lemma concrete_uAlpha_bound {K4 ε : ℝ} (hK4 : 1 ≤ K4) :
    ∃ C_uA : ℝ, 0 ≤ C_uA ∧
      ∀ {c : ℝ} {W : FctWarpChartData K4 ε c} {p : ℝ × ℝ},
        100 ≤ c →
        c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose →
        W.S = concreteBoxS K4 ε c →
        p ∈ concretePhaseDom W.ellMin ε c →
        |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p - airyZero 1| ≤
          c ^ (-(7 / 6 : ℝ)) →
        |c ^ (2 / 3 : ℝ) * FctPhaseBox.uAlpha (fctKappa c) (concretePhiTilde K4 ε c)
            (concreteTau0 ε c W.S) p| ≤ C_uA * c ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨_, _, _, Cα0, _, _, _, hCα0, hth_bd⟩ := thetaD_center_bounds
  let C_uA : ℝ := Cα0 * 3 ^ 11 / Real.sqrt 3
  refine ⟨C_uA, by positivity, fun {c W p} hc100 hτD hWS hp hadm => ?_⟩
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hτ₁ : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hã_pos : 0 < fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p := W.box.atil_pos hp
  have hã_sz := fctAtil_size hc100 rfl hadm airyZero_one hã_pos
  have hsqrt_lo : Real.sqrt 3 * c ^ (-(1 / 3 : ℝ)) ≤
      Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p) := by
    have hsq : (Real.sqrt 3 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 3 * c ^ (-(2 / 3 : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]; norm_num
    rw [Real.le_sqrt (by positivity) hã_pos.le, hsq]
    exact hã_sz.1
  have hsqrt_hi : Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p) ≤
      2 * c ^ (-(1 / 3 : ℝ)) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hsq : (2 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 4 * c ^ (-(2 / 3 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast (c ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
    rw [hsq]; exact hã_sz.2
  have hV_bd := W.h_S_V_bounds p hp
  have hτ0_eq := W.h_V_eq p hp
  have hτ0_pos : 0 < concreteTau0 ε c W.S p := by
    rw [hτ0_eq]; exact mul_pos (Real.sqrt_pos.mpr hã_pos) (by linarith [hV_bd.1])
  have hτ0_le3 : concreteTau0 ε c W.S p ≤ 3 * c ^ (-(1 / 3 : ℝ)) := by
    rw [hτ0_eq]
    calc Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p) *
          W.S.V ((concreteEll1 ε c p.1, 1, p.2), W.S.A (concreteEll1 ε c p.1, 1, p.2))
        ≤ (2 * c ^ (-(1 / 3 : ℝ))) * (100 / 92 : ℝ) :=
          mul_le_mul hsqrt_hi hV_bd.2 (by linarith [hV_bd.1]) (by positivity)
      _ ≤ 3 * c ^ (-(1 / 3 : ℝ)) := by
          have : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
          nlinarith only [this]
  have hτ0_le12 : |concreteTau0 ε c W.S p| ≤ 12 * c ^ (-(1 / 4 : ℝ)) := by
    rw [abs_of_pos hτ0_pos]
    have hle : c ^ (-(1 / 3 : ℝ)) ≤ c ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    linarith only [hτ0_le3, hle, Real.rpow_nonneg hc0.le (-(1 / 4 : ℝ))]
  have hth := ((hth_bd hK4 hc0 hτD).1 _ hτ0_le12).2.2.2
  rw [abs_of_pos hτ0_pos] at hth
  have hrat : concreteTau0 ε c W.S p / c ^ (-(1 / 4 : ℝ)) ≤ 3 * c ^ (-(1 / 12 : ℝ)) := by
    rw [div_le_iff₀ hτ₁]
    have hpow : c ^ (-(1 / 12 : ℝ)) * c ^ (-(1 / 4 : ℝ)) = c ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc concreteTau0 ε c W.S p ≤ 3 * c ^ (-(1 / 3 : ℝ)) := hτ0_le3
      _ = 3 * c ^ (-(1 / 12 : ℝ)) * c ^ (-(1 / 4 : ℝ)) := by rw [← hpow]; ring
  have hpow11 : (concreteTau0 ε c W.S p / c ^ (-(1 / 4 : ℝ))) ^ 11 ≤
      3 ^ 11 * c ^ (-(11 / 12 : ℝ)) := by
    have h1 := pow_le_pow_left₀ (by positivity) hrat 11
    have hp11 : (c ^ (-(1 / 12 : ℝ))) ^ (11 : ℕ) = c ^ (-(11 / 12 : ℝ)) := by
      rw [← Real.rpow_natCast _ 11, ← Real.rpow_mul hc0.le]; norm_num
    rwa [mul_pow, hp11] at h1
  have hdA_eq : fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) p (0, 1) =
      fctPhAlpha (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S p) p /
        Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p) := by
    have hf := W.box.hasFDerivAt_atil hp
    rw [hf.fderiv]
    simp
  have huA_eq : FctPhaseBox.uAlpha (fctKappa c) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p =
      -fctKappa c * fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) p (0, 1) := by
    rw [hdA_eq]; rfl
  have hdA_bd : |fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) p (0, 1)| ≤
      C_uA * c ^ (-(25 / 12 : ℝ)) := by
    rw [W.h_dA p hp, abs_div, abs_mul, abs_of_pos (inv_pos.mpr hc0),
      abs_of_pos (Real.sqrt_pos.mpr hã_pos)]
    have hnum : c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S p)| ≤
        Cα0 * 3 ^ 11 * c ^ (-(29 / 12 : ℝ)) := by
      have hτ12 : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := rpow_neg_quarter_sq hc0
      have hcexp : c⁻¹ * c ^ (-(1 / 2 : ℝ)) * c ^ (-(11 / 12 : ℝ)) = c ^ (-(29 / 12 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      calc c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S p)|
          ≤ c⁻¹ * (Cα0 * (c ^ (-(1 / 4 : ℝ))) ^ 2 *
              (concreteTau0 ε c W.S p / c ^ (-(1 / 4 : ℝ))) ^ 11) := by gcongr
        _ ≤ c⁻¹ * (Cα0 * c ^ (-(1 / 2 : ℝ)) * (3 ^ 11 * c ^ (-(11 / 12 : ℝ)))) := by
            rw [hτ12]; gcongr
        _ = Cα0 * 3 ^ 11 * (c⁻¹ * c ^ (-(1 / 2 : ℝ)) * c ^ (-(11 / 12 : ℝ))) := by ring
        _ = Cα0 * 3 ^ 11 * c ^ (-(29 / 12 : ℝ)) := by rw [hcexp]
    have hsqrt_pos : 0 < Real.sqrt 3 * c ^ (-(1 / 3 : ℝ)) := by positivity
    have hcexp2 : c ^ (-(29 / 12 : ℝ)) / c ^ (-(1 / 3 : ℝ)) = c ^ (-(25 / 12 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0]; norm_num
    calc c⁻¹ * |fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (concreteTau0 ε c W.S p)| /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p)
        ≤ (Cα0 * 3 ^ 11 * c ^ (-(29 / 12 : ℝ))) / (Real.sqrt 3 * c ^ (-(1 / 3 : ℝ))) :=
          div_le_div₀ (by positivity) hnum hsqrt_pos hsqrt_lo
      _ = (Cα0 * 3 ^ 11 / Real.sqrt 3) * (c ^ (-(29 / 12 : ℝ)) / c ^ (-(1 / 3 : ℝ))) := by ring
      _ = C_uA * c ^ (-(25 / 12 : ℝ)) := by rw [hcexp2]
  have hκ_le : fctKappa c ≤ c ^ (2 / 3 : ℝ) := by
    unfold fctKappa
    have hle : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    nlinarith only [hle, Real.rpow_pos_of_pos hc0 (2 / 3 : ℝ)]
  have hpow_tot : c ^ (2 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * c ^ (-(25 / 12 : ℝ))) = c ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
  rw [huA_eq, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.rpow_pos_of_pos hc0 _),
    abs_of_pos (fctKappa_pos hc0)]
  calc c ^ (2 / 3 : ℝ) * (fctKappa c * |fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)) p (0, 1)|)
      ≤ c ^ (2 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * (C_uA * c ^ (-(25 / 12 : ℝ)))) := by gcongr
    _ = C_uA * (c ^ (2 / 3 : ℝ) * (c ^ (2 / 3 : ℝ) * c ^ (-(25 / 12 : ℝ)))) := by ring
    _ = C_uA * c ^ (-(3 / 4 : ℝ)) := by rw [hpow_tot]

/-! ### 5. Derivative bound on the chart residual `N` and `fctWarpSolve_uncond` -/

private noncomputable def warpG (K4 ε c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  toPairCLM (((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c p.1 p.2)

private noncomputable def warpN (K4 ε c : ℝ) (W : FctWarpChartData K4 ε c) (y : ℝ × ℝ) : ℝ × ℝ :=
  warpG K4 ε c
    (Function.invFunOn
      (fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S))
      (Ioo (W.L_ctr / 2) (2 * W.L_ctr) ×ˢ
        Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ))))
      ((airyZero 1, (0 : ℝ)) + y)) -
  warpMEquiv y

private lemma warpN_deriv_bound {K4 ε c : ℝ} (C_DL C_DA C_uA : ℝ)
    (hK4 : 1 ≤ K4) (hε : ε = 1 ∨ ε = -1) (hc100 : 100 ≤ c)
    (hc_tauLim : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim)
    (hτD : c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose)
    (hK4t : K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1)
    (hCDL0 : 0 ≤ C_DL) (hCuA0 : 0 ≤ C_uA)
    (hdL_spec : ∀ {c' L1 α : ℝ}, (concreteInnerFamily K4 ε).adm c' L1 α → c' = c →
      ‖((warpN0 c / (-fctKappa c * (concreteBoxS K4 ε c).V
        ((concreteEll1 ε c L1, 1, α), (concreteBoxS K4 ε c).A (concreteEll1 ε c L1, 1, α))) : ℝ) : ℂ) *
        (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c L1 α τ) -
        Complex.I * deriv fctG0 (airyZero 1)‖ ≤ C_DL * c ^ (-(1 / 2 : ℝ)))
    (hdA_spec : ∀ {L1 α : ℝ}, (concreteInnerFamily K4 ε).adm c L1 α →
      ‖((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) *
        (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c L1 α τ) -
        (-Complex.I * ((warpC2Star : ℝ) : ℂ) * iteratedDeriv 2 fctG0 (airyZero 1))‖ ≤
        C_DA * c ^ (-(1 / 2 : ℝ)))
    (huA_spec : ∀ {W : FctWarpChartData K4 ε c} {p : ℝ × ℝ},
      W.S = concreteBoxS K4 ε c → p ∈ concretePhaseDom W.ellMin ε c →
      |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p - airyZero 1| ≤
        c ^ (-(7 / 6 : ℝ)) →
      |c ^ (2 / 3 : ℝ) * FctPhaseBox.uAlpha (fctKappa c) (concretePhiTilde K4 ε c)
          (concreteTau0 ε c W.S) p| ≤ C_uA * c ^ (-(3 / 4 : ℝ)))
    (W : FctWarpChartData K4 ε c) (hWS : W.S = concreteBoxS K4 ε c) (hWell : W.ellMin = pbellMin)
    {y : ℝ × ℝ} (hy : y ∈ closedBall (0 : ℝ × ℝ) (c ^ (-(7 / 6 : ℝ)))) :
    ∃ D_N : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      HasFDerivWithinAt (warpN K4 ε c W) D_N (closedBall (0 : ℝ × ℝ) (c ^ (-(7 / 6 : ℝ)))) y ∧
      ‖D_N‖ ≤ (C_DL + C_DA + C_uA * (‖Complex.I * deriv fctG0 (airyZero 1)‖ + C_DL)) * c ^ (-(1 / 2 : ℝ)) := by
  let I := Ioo (W.L_ctr / 2) (2 * W.L_ctr)
  let J := Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ)))
  let Ψ := fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)
  have hN_eq_fun : warpN K4 ε c W =
      fun z => warpG K4 ε c (Function.invFunOn Ψ (I ×ˢ J) ((airyZero 1, (0 : ℝ)) + z)) - warpMEquiv z := rfl
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  have hbox_cond : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧ K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧ 100 ≤ c :=
    ⟨hc_tauLim, hK4t, hc100⟩
  have hay_ball : (airyZero 1, (0 : ℝ)) + y ∈ closedBall (airyZero 1, (0 : ℝ)) (c ^ (-(7 / 6 : ℝ))) := by
    simpa [mem_closedBall, dist_eq_norm] using hy
  obtain ⟨hp_mem, hΨp, hinv_fd⟩ := fctChart_inv_hasFDerivAt W hc0 (W.h_surj hay_ball)
  set p := Function.invFunOn Ψ (I ×ˢ J) ((airyZero 1, (0 : ℝ)) + y)
  have hΨp' : Ψ p = (airyZero 1, (0 : ℝ)) + y := hΨp
  have hΨp_ball : Ψ p ∈ closedBall (airyZero 1, (0 : ℝ)) (c ^ (-(7 / 6 : ℝ))) := by
    rw [hΨp']; exact hay_ball
  have hadm : (concreteInnerFamily K4 ε).adm c p.1 p.2 :=
    fctWarpChart_mem_adm hK4 hε hbox_cond W hWS hWell hp_mem hΨp_ball
  have hpΩ : p ∈ concretePhaseDom W.ellMin ε c := W.h_rect_sub hp_mem
  let uLp := FctPhaseBox.uL (fctKappa c) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p
  let uAp := FctPhaseBox.uAlpha (fctKappa c) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p
  let lam : ℝ := c ^ (-(2 / 3 : ℝ))
  have huLp_eq : uLp = -fctKappa c *
      W.S.V ((concreteEll1 ε c p.1, 1, p.2), W.S.A (concreteEll1 ε c p.1, 1, p.2)) := by
    dsimp only [uLp, FctPhaseBox.uL]
    rw [W.h_V_eq p hpΩ, mul_div_cancel_left₀ _ (W.box.sqrt_atil_pos hpΩ).ne']
  have hVA_pos : 0 < W.S.V ((concreteEll1 ε c p.1, 1, p.2), W.S.A (concreteEll1 ε c p.1, 1, p.2)) := by
    linarith [(W.h_S_V_bounds p hpΩ).1]
  have huLp_ne : uLp ≠ 0 := by
    rw [huLp_eq]
    exact mul_ne_zero (neg_ne_zero.mpr (fctKappa_pos hc0).ne') hVA_pos.ne'
  have hlam_ne : lam ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
  have hinv_y := (hinv_fd huLp_ne hlam_ne).comp y ((hasFDerivAt_id y).const_add (airyZero 1, (0 : ℝ)))
  let dL := Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c p.1 p.2 τ
  let dA := Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivAlpha K4 ε c p.1 p.2 τ
  have hI_fd := hasFDerivAt_fctWarpI hK4 hε hc1 hτD p
  have hG_fd : HasFDerivAt (warpG K4 ε c) (toPairCLM.comp (((warpN0 c : ℝ) : ℂ) • clmFromCols dL dA)) p :=
    toPairCLM.hasFDerivAt.comp p (hI_fd.const_smul (((warpN0 c : ℝ) : ℂ)))
  have hcomp := hG_fd.comp y (by simpa only [← hΨp'] using hinv_y)
  have hN_fd : HasFDerivAt (warpN K4 ε c W)
      ((toPairCLM.comp (((warpN0 c : ℝ) : ℂ) • clmFromCols dL dA)).comp
        ((invChartDerivEquiv uLp uAp lam huLp_ne hlam_ne).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) -
        (warpMEquiv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) y := by
    rw [hN_eq_fun]
    exact hcomp.sub warpMEquiv.toContinuousLinearMap.hasFDerivAt
  set D_N := (toPairCLM.comp (((warpN0 c : ℝ) : ℂ) • clmFromCols dL dA)).comp
    ((invChartDerivEquiv uLp uAp lam huLp_ne hlam_ne).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) -
    (warpMEquiv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
  have hDN_eq : D_N = clmFromCols (D_N (1, 0)) (D_N (0, 1)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hv, map_add, map_smul, map_smul]
    simp [clmFromCols_apply]
  have hcol1_eq : D_N (1, 0) = toPairCLM
      (((warpN0 c / uLp : ℝ) : ℂ) * dL - Complex.I * deriv fctG0 (airyZero 1)) := by
    dsimp only [D_N]
    rw [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe]
    have hsym1 : (invChartDerivEquiv uLp uAp lam huLp_ne hlam_ne).symm (1, 0) = (uLp⁻¹, 0) := by
      simp [invChartDerivEquiv, clmFromCols_apply]
    rw [hsym1, warpMEquiv_fst, ← map_sub]
    congr 1
    simp only [smul_apply, clmFromCols_apply, smul_eq_mul,
      zero_smul, add_zero, Complex.real_smul]
    push_cast; ring
  have hc23_inv : lam⁻¹ = c ^ (2 / 3 : ℝ) := by
    dsimp only [lam]; rw [Real.rpow_neg hc0.le, inv_inv]
  have hcol2_eq : D_N (0, 1) = toPairCLM
      (((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * dA - warpW2 -
        ((c ^ (2 / 3 : ℝ) * uAp : ℝ) : ℂ) * (((warpN0 c / uLp : ℝ) : ℂ) * dL)) := by
    dsimp only [D_N]
    rw [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe]
    have hsym2 : (invChartDerivEquiv uLp uAp lam huLp_ne hlam_ne).symm (0, 1) =
        (-uAp / (uLp * lam), lam⁻¹) := by
      simp [invChartDerivEquiv, clmFromCols_apply]
    rw [hsym2, warpMEquiv_snd, ← map_sub]
    congr 1
    simp only [smul_apply, clmFromCols_apply, smul_eq_mul, Complex.real_smul]
    have hce : (-uAp / (uLp * lam) : ℝ) = -(c ^ (2 / 3 : ℝ) * uAp) / uLp := by
      rw [div_eq_mul_inv, mul_inv, ← hc23_inv]; ring
    rw [hce, hc23_inv]
    push_cast; ring
  have hdL_bd : ‖((warpN0 c / uLp : ℝ) : ℂ) * dL - Complex.I * deriv fctG0 (airyZero 1)‖ ≤
      C_DL * c ^ (-(1 / 2 : ℝ)) := by
    have h_eq : ((warpN0 c / uLp : ℝ) : ℂ) * dL =
        ((warpN0 c / (-fctKappa c * (concreteBoxS K4 ε c).V
          ((concreteEll1 ε c p.1, 1, p.2), (concreteBoxS K4 ε c).A (concreteEll1 ε c p.1, 1, p.2))) : ℝ) : ℂ) *
          (Complex.I * ∫ τ in Ioi (0 : ℝ), fctWarpIntegrandDerivL K4 ε c p.1 p.2 τ) := by
      rw [huLp_eq, hWS]
    rw [h_eq]
    exact hdL_spec hadm rfl
  have hdA_bd : ‖((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * dA - warpW2‖ ≤
      C_DA * c ^ (-(1 / 2 : ℝ)) := by
    dsimp only [warpW2, dA]
    exact hdA_spec hadm
  have huA_bd : |c ^ (2 / 3 : ℝ) * uAp| ≤ C_uA * c ^ (-(1 / 2 : ℝ)) := by
    have hadm_W : |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p - airyZero 1| ≤
        c ^ (-(7 / 6 : ℝ)) := by
      rw [hWS]; exact hadm.2.2.1
    have hc34 : c ^ (-(3 / 4 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    exact (huA_spec hWS hpΩ hadm_W).trans (mul_le_mul_of_nonneg_left hc34 hCuA0)
  let C_L1_bd : ℝ := ‖Complex.I * deriv fctG0 (airyZero 1)‖ + C_DL
  have hdL_tot : ‖((warpN0 c / uLp : ℝ) : ℂ) * dL‖ ≤ C_L1_bd := by
    have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    calc ‖((warpN0 c / uLp : ℝ) : ℂ) * dL‖
        = ‖(((warpN0 c / uLp : ℝ) : ℂ) * dL - Complex.I * deriv fctG0 (airyZero 1)) +
            Complex.I * deriv fctG0 (airyZero 1)‖ := by ring_nf
      _ ≤ ‖((warpN0 c / uLp : ℝ) : ℂ) * dL - Complex.I * deriv fctG0 (airyZero 1)‖ +
            ‖Complex.I * deriv fctG0 (airyZero 1)‖ := norm_add_le _ _
      _ ≤ C_DL * c ^ (-(1 / 2 : ℝ)) + ‖Complex.I * deriv fctG0 (airyZero 1)‖ :=
          add_le_add hdL_bd le_rfl
      _ ≤ C_DL * 1 + ‖Complex.I * deriv fctG0 (airyZero 1)‖ := by gcongr
      _ = C_L1_bd := by dsimp only [C_L1_bd]; ring
  have hDN1_bd : ‖D_N (1, 0)‖ ≤ C_DL * c ^ (-(1 / 2 : ℝ)) := by
    rw [hcol1_eq]; exact (toPairCLM_norm_le _).trans hdL_bd
  have hDN2_bd : ‖D_N (0, 1)‖ ≤ (C_DA + C_uA * C_L1_bd) * c ^ (-(1 / 2 : ℝ)) := by
    rw [hcol2_eq]
    refine (toPairCLM_norm_le _).trans ?_
    calc ‖(((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * dA - warpW2) -
          ((c ^ (2 / 3 : ℝ) * uAp : ℝ) : ℂ) * (((warpN0 c / uLp : ℝ) : ℂ) * dL)‖
        ≤ ‖((c ^ (2 / 3 : ℝ) * warpN0 c : ℝ) : ℂ) * dA - warpW2‖ +
          ‖((c ^ (2 / 3 : ℝ) * uAp : ℝ) : ℂ) * (((warpN0 c / uLp : ℝ) : ℂ) * dL)‖ := norm_sub_le _ _
      _ ≤ C_DA * c ^ (-(1 / 2 : ℝ)) + (C_uA * c ^ (-(1 / 2 : ℝ))) * C_L1_bd := by
          refine add_le_add hdA_bd ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul huA_bd hdL_tot (norm_nonneg _) (by positivity)
      _ = (C_DA + C_uA * C_L1_bd) * c ^ (-(1 / 2 : ℝ)) := by ring
  have hDN_norm : ‖D_N‖ ≤ (C_DL + C_DA + C_uA * C_L1_bd) * c ^ (-(1 / 2 : ℝ)) := by
    calc ‖D_N‖ = ‖clmFromCols (D_N (1, 0)) (D_N (0, 1))‖ := by rw [← hDN_eq]
      _ ≤ ‖D_N (1, 0)‖ + ‖D_N (0, 1)‖ := clmFromCols_norm_le _ _
      _ ≤ C_DL * c ^ (-(1 / 2 : ℝ)) + (C_DA + C_uA * C_L1_bd) * c ^ (-(1 / 2 : ℝ)) :=
          add_le_add hDN1_bd hDN2_bd
      _ = (C_DL + C_DA + C_uA * C_L1_bd) * c ^ (-(1 / 2 : ℝ)) := by ring
  exact ⟨D_N, hN_fd.hasFDerivWithinAt, hDN_norm⟩

/-- **Unconditional `fct:warp-asymp` (1)** (Paper I, Proposition `fct:warp-asymp` (1)). -/
theorem fctWarpSolve_uncond {K4 : ℝ} (hK4 : 1 ≤ K4) : FctWarpSolveStmt K4 := by
  obtain ⟨C_ctr, c_ctr, hCctr0, _, hcenter⟩ := fctWarpFJ_center hK4
  obtain ⟨C_R1, c_R1, hCR1, hcR1_b, hres1⟩ := fctWarpI_zero_residual (K4 := K4) (ε := 1) hK4
  obtain ⟨C_Rm1, c_Rm1, hCRm1, hcRm1_b, hresm1⟩ := fctWarpI_zero_residual (K4 := K4) (ε := -1) hK4
  obtain ⟨C_DL1, c_DL1, hCDL1, _, hdL1⟩ := fctWarpI_derivL_at_a1_err (K4 := K4) (ε := 1) hK4
  obtain ⟨C_DLm1, c_DLm1, hCDLm1, _, hdLm1⟩ := fctWarpI_derivL_at_a1_err (K4 := K4) (ε := -1) hK4
  obtain ⟨C_DA1, c_DA1, hCDA1, _, hdA1⟩ := fctWarpI_derivAlpha_at_a1_err (K4 := K4) (ε := 1) hK4
  obtain ⟨C_DAm1, c_DAm1, hCDAm1, _, hdAm1⟩ := fctWarpI_derivAlpha_at_a1_err (K4 := K4) (ε := -1) hK4
  obtain ⟨C_uA1, hCuA1, huA1⟩ := concrete_uAlpha_bound (K4 := K4) (ε := 1) hK4
  obtain ⟨C_uAm1, hCuAm1, huAm1⟩ := concrete_uAlpha_bound (K4 := K4) (ε := -1) hK4
  let C_R : ℝ := max C_R1 C_Rm1
  let c_R : ℝ := max c_R1 c_Rm1
  let C_DL : ℝ := max C_DL1 C_DLm1
  let c_DL : ℝ := max c_DL1 c_DLm1
  let C_DA : ℝ := max C_DA1 C_DAm1
  let c_DA : ℝ := max c_DA1 c_DAm1
  let C_uA : ℝ := max C_uA1 C_uAm1
  have hCR0 : 0 ≤ C_R := le_max_of_le_left hCR1
  have hCDL0 : 0 ≤ C_DL := le_max_of_le_left hCDL1
  have hCDA0 : 0 ≤ C_DA := le_max_of_le_left hCDA1
  have hCuA0 : 0 ≤ C_uA := le_max_of_le_left hCuA1
  let κ : ℝ := ‖(warpMEquiv.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ + 1
  have hκ_pos : 0 < κ := by positivity
  have hκ_M : ‖(warpMEquiv.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ κ := by linarith only
  let Cρ : ℝ := 2 * κ * C_R
  have hCρ0 : 0 ≤ Cρ := by positivity
  obtain ⟨C_cls, c_cls1, hCcls0, hc_cls1, hofChart⟩ := fctWarpClass_of_chart hK4 hCctr0 hCρ0
  obtain ⟨_, c_cls2, _, _, htoChart⟩ := fctWarpFJ_of_class hK4 C_cls
  let C_L1_bd : ℝ := ‖Complex.I * deriv fctG0 (airyZero 1)‖ + C_DL
  let C_Lip : ℝ := C_DL + C_DA + C_uA * C_L1_bd
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      c_ctr ≤ c ∧ c_R ≤ c ∧ c_DL ≤ c ∧ c_DA ≤ c ∧ c_cls1 ≤ c ∧ c_cls2 ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧
      max 100 ((30 * pbC0 + 1) ^ 2) ≤ c ∧
      c ^ (-(1 / 4 : ℝ)) ≤ (fct_comp_D_part1 StripKernelChoice.star).choose ∧
      K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧
      Cρ * c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(7 / 6 : ℝ)) ∧
      C_Lip * c ^ (-(1 / 2 : ℝ)) ≤ 1 / (2 * κ) ∧
      Real.pi ^ 2 * (|C_ctr| + |C_cls|) * c ^ (-(4 / 3 : ℝ)) < 1 / 2 := by
    refine Eventually.and (eventually_ge_atTop c_ctr)
      (Eventually.and (eventually_ge_atTop c_R)
        (Eventually.and (eventually_ge_atTop c_DL)
          (Eventually.and (eventually_ge_atTop c_DA)
            (Eventually.and (eventually_ge_atTop c_cls1)
              (Eventually.and (eventually_ge_atTop c_cls2)
                (Eventually.and ?_
                  (Eventually.and (eventually_ge_atTop _)
                    (Eventually.and ?_ (Eventually.and ?_ (Eventually.and ?_
                      (Eventually.and ?_ ?_)))))))))))
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds pbTauLim_pos)
    · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
        (Iic_mem_nhds (fct_comp_D_part1 StripKernelChoice.star).choose_spec.1)
    · have h0 : Tendsto (fun c : ℝ => K4 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul K4
      exact h0.eventually (Iic_mem_nhds zero_lt_one)
    · filter_upwards [eventually_gt_atTop 0,
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).eventually
          (Iic_mem_nhds (by positivity : (0 : ℝ) < 1 / (Cρ + 1)))] with c hc0 hlt
      have hexp : c ^ (-(4 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ)) := by
        rw [← Real.rpow_add hc0]; norm_num
      have h76 : 0 ≤ c ^ (-(7 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
      rw [hexp, ← mul_assoc]
      calc Cρ * c ^ (-(1 / 6 : ℝ)) * c ^ (-(7 / 6 : ℝ))
          ≤ (Cρ * (1 / (Cρ + 1))) * c ^ (-(7 / 6 : ℝ)) := by gcongr
        _ ≤ 1 * c ^ (-(7 / 6 : ℝ)) := by
            gcongr; rw [mul_div_assoc', div_le_one (by positivity)]; linarith only [hCρ0]
        _ = c ^ (-(7 / 6 : ℝ)) := one_mul _
    · have h0 : Tendsto (fun c : ℝ => C_Lip * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C_Lip
      exact h0.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * κ)))
    · have h0 : Tendsto (fun c : ℝ => Real.pi ^ 2 * (|C_ctr| + |C_cls|) * c ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 3)).const_mul
          (Real.pi ^ 2 * (|C_ctr| + |C_cls|))
      exact h0.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  refine ⟨C_cls, max 100 c₀, fun ε c hε hc => ?_⟩
  obtain ⟨hc_ctr, hc_R, hc_DL, hc_DA, hc_cls1, hc_cls2, hc_tauLim, hc_base, hτD, hK4t, hρ_le_r, hLip_le, hc_uniq⟩ :=
    hc₀ c ((le_max_right 100 c₀).trans hc)
  have hc100 : 100 ≤ c := (le_max_left 100 c₀).trans hc
  have hc0 : 0 < c := by linarith only [hc100]
  have hc1 : 1 ≤ c := by linarith only [hc100]
  obtain ⟨W, hWC, hWS, hWell⟩ := hcenter hε hc_ctr
  let I := Ioo (W.L_ctr / 2) (2 * W.L_ctr)
  let J := Ioo (-(3 / 2 * c ^ (-(1 / 2 : ℝ)))) (3 / 2 * c ^ (-(1 / 2 : ℝ)))
  let Ψ := fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S)
  let a : ℝ × ℝ := (airyZero 1, 0)
  let r : ℝ := c ^ (-(7 / 6 : ℝ))
  let ρ : ℝ := Cρ * c ^ (-(4 / 3 : ℝ))
  have hN0_pos : 0 < warpN0 c := by
    unfold warpN0
    have hts : (1.06 : ℝ) ≤ warpTauStar := warpTauStar_ge
    positivity
  have hG_iff : ∀ p : ℝ × ℝ, warpG K4 ε c p = 0 ↔ fctWarpI K4 ε c p.1 p.2 = 0 := fun p => by
    dsimp only [warpG]
    rw [toPairCLM_eq_zero_iff, mul_eq_zero]
    simp [hN0_pos.ne']
  have hinj : InjOn Ψ (I ×ˢ J) :=
    W.box.fctChart_injOn (fctKappa_pos hc0) (Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))).ne'
      isOpen_Ioo ordConnected_Ioo W.h_rect_sub
  have hsurj : closedBall a r ⊆ Ψ '' (I ×ˢ J) := W.h_surj
  have hbox_cond : c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧ K4 * c ^ (-(1 / 2 : ℝ)) ≤ 1 ∧ 100 ≤ c :=
    ⟨hc_tauLim, hK4t, hc100⟩
  -- Bound on `‖warpN K4 ε c W 0‖`
  have hN0_norm : κ * ‖warpN K4 ε c W 0‖ ≤ ρ / 2 := by
    have h0_mem : a + (0 : ℝ × ℝ) ∈ Ψ '' (I ×ˢ J) := hsurj (by rw [add_zero]; exact mem_closedBall_self (by positivity))
    obtain ⟨hp0_mem, hΨp0⟩ := Function.invFunOn_pos h0_mem
    let p₀ := Function.invFunOn Ψ (I ×ˢ J) (a + 0)
    have hΨp0_ball : Ψ p₀ ∈ closedBall a r := by
      dsimp only [p₀]; rw [hΨp0, add_zero]; exact mem_closedBall_self (by positivity)
    have hadm0 : (concreteInnerFamily K4 ε).adm c p₀.1 p₀.2 :=
      fctWarpChart_mem_adm hK4 hε hbox_cond W hWS hWell hp0_mem hΨp0_ball
    have hp0_2 : p₀.2 = 0 := by
      have h2 := congrArg Prod.snd hΨp0
      have h2' : c ^ (-(2 / 3 : ℝ)) * p₀.2 = c ^ (-(2 / 3 : ℝ)) * 0 := by
        simpa [p₀, Ψ, fctChart, a] using h2
      exact mul_left_cancel₀ (Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))).ne' h2'
    have hû0 : -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (p₀.1, 0) =
        airyZero 1 := by
      have h1 := congrArg Prod.fst hΨp0
      rw [← hp0_2]
      dsimp only [p₀]
      simpa [Ψ, fctChart, a, hWS] using h1
    have hres_bd : ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c p₀.1 p₀.2‖ ≤ C_R * c ^ (-(4 / 3 : ℝ)) := by
      rw [hp0_2] at hadm0 ⊢
      rcases hε with rfl | rfl
      · have h := hres1 (le_trans (le_max_left _ _) hc_R) hadm0
        dsimp only at h
        rw [hû0, fctG0_airyZero, mul_zero, sub_zero] at h
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · have h := hresm1 (le_trans (le_max_right _ _) hc_R) hadm0
        dsimp only at h
        rw [hû0, fctG0_airyZero, mul_zero, sub_zero] at h
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hN0_eq : warpN K4 ε c W 0 = warpG K4 ε c p₀ := by
      dsimp only [warpN, p₀, Ψ, I, J, a]; rw [map_zero, sub_zero]
    rw [hN0_eq]
    calc κ * ‖warpG K4 ε c p₀‖ ≤ κ * ‖((warpN0 c : ℝ) : ℂ) * fctWarpI K4 ε c p₀.1 p₀.2‖ :=
          mul_le_mul_of_nonneg_left (toPairCLM_norm_le _) hκ_pos.le
      _ ≤ κ * (C_R * c ^ (-(4 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hres_bd hκ_pos.le
      _ = ρ / 2 := by dsimp only [ρ, Cρ]; ring
  -- Lipschitz bound on `warpN K4 ε c W` on `closedBall 0 r`
  have hLip : ∀ y ∈ closedBall (0 : ℝ × ℝ) r, ∀ z ∈ closedBall (0 : ℝ × ℝ) r,
      ‖warpN K4 ε c W y - warpN K4 ε c W z‖ ≤ 1 / (2 * κ) * ‖y - z‖ := by
    have hderiv_bd : ∀ y ∈ closedBall (0 : ℝ × ℝ) r,
        ∃ D_N : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), HasFDerivWithinAt (warpN K4 ε c W) D_N (closedBall (0 : ℝ × ℝ) r) y ∧
          ‖D_N‖ ≤ 1 / (2 * κ) := by
      intro y hy
      obtain ⟨D_N, hN_fd, hN_bd⟩ := warpN_deriv_bound C_DL C_DA C_uA hK4 hε hc100 hc_tauLim hτD hK4t
        hCDL0 hCuA0
        (fun {c' L1 α} hadm hceq => by
          subst hceq
          rcases hε with rfl | rfl
          · exact (hdL1 (le_trans (le_max_left _ _) hc_DL) hadm).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          · exact (hdLm1 (le_trans (le_max_right _ _) hc_DL) hadm).trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
        (fun {L1 α} hadm => by
          rcases hε with rfl | rfl
          · exact (hdA1 (le_trans (le_max_left _ _) hc_DA) hadm).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          · exact (hdAm1 (le_trans (le_max_right _ _) hc_DA) hadm).trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
        (fun {W' p'} hW'S hp' hadm' => by
          rcases hε with rfl | rfl
          · exact (huA1 hc100 hτD hW'S hp' hadm').trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          · exact (huAm1 hc100 hτD hW'S hp' hadm').trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
        W hWS hWell hy
      exact ⟨D_N, hN_fd, hN_bd.trans hLip_le⟩
    classical
    choose D_N hD_fd hD_bd using hderiv_bd
    intro y hy z hz
    have hD_fd' : ∀ w ∈ closedBall (0 : ℝ × ℝ) r,
        HasFDerivWithinAt (warpN K4 ε c W)
          (if hw : w ∈ closedBall (0 : ℝ × ℝ) r then D_N w hw else 0)
          (closedBall (0 : ℝ × ℝ) r) w := fun w hw => by
      simp only [hw, ↓reduceDIte]; exact hD_fd w hw
    have hD_bd' : ∀ w ∈ closedBall (0 : ℝ × ℝ) r,
        ‖if hw : w ∈ closedBall (0 : ℝ × ℝ) r then D_N w hw else 0‖ ≤ 1 / (2 * κ) := fun w hw => by
      simp only [hw, ↓reduceDIte]; exact hD_bd w hw
    exact (convex_closedBall (0 : ℝ × ℝ) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hD_fd' hD_bd' hz hy
  -- Apply `fct_zero_of_chart`
  have hF_eq : ∀ y : ℝ × ℝ,
      warpG K4 ε c (Function.invFunOn Ψ (I ×ˢ J) (a + y)) = warpMEquiv y + warpN K4 ε c W y := by
    intro y; dsimp only [warpN, Ψ, I, J, a]; abel
  obtain ⟨p, hp_mem, hp_ball, hp_zero, hp_uniq⟩ :=
    fct_zero_of_chart Ψ (I ×ˢ J) (warpG K4 ε c) a (by positivity) hρ_le_r hinj hsurj
      warpMEquiv hκ_pos hκ_M hF_eq hLip hN0_norm
  have hcls_p : FctWarpClass C_cls ε c p.1 p.2 :=
    hofChart hε hc_cls1 W hWC hp_mem.1 hp_mem.2 hp_ball
  have hint_p : IntegrableOn (fctWarpIntegrand K4 ε c p.1 p.2) (Ioi (0 : ℝ)) :=
    integrableOn_fctWarpIntegrand hK4 hε hc1 hτD p.1 p.2
  have hzero_p : FctWarpZero K4 ε c p.1 p.2 := ⟨hint_p, (hG_iff p).mp hp_zero⟩
  refine ⟨p, ⟨hcls_p, hzero_p⟩, ?_⟩
  rintro p' ⟨hcls_p', hzero_p'⟩
  obtain ⟨W', _, hW'S, _, hof_p'⟩ := htoChart hε hc_cls2
  obtain ⟨_, hp'_J, hp'_ball⟩ := hof_p' hcls_p'
  have hp'_ball_W : Ψ p' ∈ closedBall a r := by
    change fctChart (fctKappa c) (c ^ (-(2 / 3 : ℝ))) (concretePhiTilde K4 ε c) (concreteTau0 ε c W.S) p' ∈
      closedBall a r
    rw [hWS, ← hW'S]
    exact hp'_ball
  have hL_pos : 0 < W.L_ctr := by linarith only [W.hL_scale.1, Real.rpow_pos_of_pos hc0 (-(2 / 3 : ℝ))]
  have hdiff_L : |p'.1 - W.L_ctr| ≤ Real.pi ^ 2 * (|C_ctr| + |C_cls|) * c ^ (-(2 : ℝ)) := by
    rw [add_comm |C_ctr| |C_cls|]
    refine l1_sub_ctr_of_exp_close (Δ5 := ctDelta5 ε c) hc100 hcls_p'.1 hL_pos ?_ ?_
    · exact hcls_p'.2.1
    · exact W.hT_ctr.trans (mul_le_mul_of_nonneg_right hWC (by positivity))
  have hdiff_lt : |p'.1 - W.L_ctr| < W.L_ctr / 2 := by
    have hpow2 : c ^ (-(2 : ℝ)) = c ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc |p'.1 - W.L_ctr|
        ≤ Real.pi ^ 2 * (|C_ctr| + |C_cls|) * c ^ (-(2 : ℝ)) := hdiff_L
      _ = (Real.pi ^ 2 * (|C_ctr| + |C_cls|) * c ^ (-(4 / 3 : ℝ))) * c ^ (-(2 / 3 : ℝ)) := by
          rw [hpow2]; ring
      _ < (1 / 2 : ℝ) * c ^ (-(2 / 3 : ℝ)) :=
          mul_lt_mul_of_pos_right hc_uniq (Real.rpow_pos_of_pos hc0 _)
      _ ≤ W.L_ctr / 2 := by linarith only [W.hL_scale.1]
  have hp'_I : p'.1 ∈ I := by
    have h := abs_lt.mp hdiff_lt
    exact ⟨by linarith only [h.1], by linarith only [h.2, hL_pos]⟩
  exact hp_uniq p' ⟨hp'_I, hp'_J⟩ hp'_ball_W ((hG_iff p').mpr hzero_p'.2)

/-- info: 'FormalResearch.SignUncertainty.fctWarpSolve_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarpSolve_uncond

end FormalResearch.SignUncertainty
