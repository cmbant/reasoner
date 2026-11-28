/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTotSplit
public import FormalResearch.SignUncertainty.UctSeedEdgeKW
public import FormalResearch.SignUncertainty.FctCuspEdge
public import FormalResearch.SignUncertainty.FctWarpOuterBase
public import FormalResearch.SignUncertainty.FctTau0Global

/-!
# Edge decomposition and macroscopic bound `(fct:hg1-mac)` for `ctWg1`

Decomposes `ctWg1 ε c = wg1PartA ε c + wg1PartB ε c` on the closed strip, expresses the normalized edge densities
of both parts as `(cuspEdgeJ c L A_A Y_A).re` and `(cuspEdgeJ c L A_B Y_B).re` (matching `FctCuspEdge`), proves
`CuspProfile (3/2)` for `Y_A(u) = ctTg1 (I * ceCs * u)` and `CuspProfile (1/2)` for `Y_B(u) = seedV 0 (ceCs * u)`,
and establishes `CuspAmplitude (π / 8)` bounds (with `O(c^{-2/3})` for `A_B`), yielding:

* `ctWg1_partB_bound`: `|normDensity (wg1PartB ε c) c ξ| ≤ C c^{-2/3}` everywhere and `≤ C c^{-5/3} L^{-3/2}` for `L > 0`.
* `ctWg1_partA_bound`: `|normDensity (wg1PartA ε c) c ξ| ≤ C` everywhere and `≤ C c^{-5/3} L^{-5/2}` for `L > 0`.
* `ctWg1_mac_bound` (`fct:hg1-mac`): `|normDensity (ctWg1 ε c) c ξ| ≤ C c^{-5/3} (L^{-5/2} + L^{-3/2})` for all `L > 0`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCuspEdge FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

/-- First summand `W_A` of `ctWg1 ε c`: `ctTg1` on the left edge, `seedT 0` on the right. -/
noncomputable def wg1PartA (ε c : ℝ) (ζ : ℂ) : ℂ :=
  (seedT 0 (seedScale c : ℂ))⁻¹ * (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) *
    (ctTg1 ((seedScale c : ℂ) * ζ) * seedT 0 ((seedScale c : ℂ) * (1 - ζ))))

/-- Second summand `W_B` of `ctWg1 ε c`: `seedT 0` on the left edge, `ctTg1` on the right. -/
noncomputable def wg1PartB (ε c : ℝ) (ζ : ℂ) : ℂ :=
  (seedT 0 (seedScale c : ℂ))⁻¹ * (uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) *
    (seedT 0 ((seedScale c : ℂ) * ζ) * ctTg1 ((seedScale c : ℂ) * (1 - ζ))))

lemma ctWg1_eq_add (ε c : ℝ) (ζ : ℂ) :
    ctWg1 ε c ζ = wg1PartA ε c ζ + wg1PartB ε c ζ := by
  unfold ctWg1 wg1PartA wg1PartB; ring

/-- Left-edge amplitude `A_A` for `wg1PartA`. -/
noncomputable def wg1AmpA (ε c τ : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * uctMc c 0 τ

/-- Left-edge amplitude `A_B` for `wg1PartB`. -/
noncomputable def wg1AmpB (ε c τ : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
    Complex.exp (binetDiff c ((τ : ℂ) * Complex.I)) *
    (1 - (τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ) *
    (ctTg1 ((seedScale c : ℂ) * (1 - (τ : ℂ) * Complex.I)) / seedT 0 (seedScale c : ℂ)) *
    (uctAstar τ : ℂ)

/-- Scaled `g̃₁` profile `Y_A(u) = ctTg1 (i c_s u)`. -/
noncomputable def wg1YA (u : ℝ) : ℂ := ctTg1 (((ceCs * u : ℝ) : ℂ) * Complex.I)

/-- Scaled `F̃_*` profile `Y_B(u) = seedV 0 (c_s u)`. -/
noncomputable def wg1YB (u : ℝ) : ℂ := seedV 0 (ceCs * u)

lemma wg1PartA_edge_eq {ε c ξ : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hξ : 0 < ξ) (τ : ℝ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        wg1AmpA ε c τ * wg1YA (c ^ (1 / 3 : ℝ) * τ) := by
  have hcore : (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
      (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * (uctAstar τ : ℂ) := by
    by_cases hτ : τ = 0
    · subst hτ; exact seedZ_edge_core_zero
    · exact seedZ_edge_core_all hε hτ
  have hK : ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) ≠ 0 := by
    have : c ^ (5 / 6 : ℝ) / uctCAi ≠ 0 := div_ne_zero (Real.rpow_pos_of_pos hc _).ne' uctCAi_ne
    exact_mod_cast this
  set K : ℂ := ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ)
  have hcomm : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
  have hY : wg1YA (c ^ (1 / 3 : ℝ) * τ) = ctTg1 ((seedScale c : ℂ) * (Complex.I * (τ : ℂ))) := by
    unfold wg1YA seedScale; congr 1; push_cast; ring
  rw [mellinK0_imag_outer c ξ τ hξ, ← outerK_eq, hY]
  unfold wg1PartA wg1AmpA uctMc
  rw [hcomm, uctPhi_one, uctPhi_eq_seedT]
  have hmd : K * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * seedT 0 ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ))) /
      (K * seedT 0 (seedScale c : ℂ)) =
      (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * seedT 0 ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ))) *
        (seedT 0 (seedScale c : ℂ))⁻¹ := by
    rw [mul_assoc K, mul_div_mul_left _ _ hK, div_eq_mul_inv]
  rw [hmd]
  set Bc := Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))
  set Ph := Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ))
  linear_combination (Bc * Ph * (seedT 0 (seedScale c : ℂ))⁻¹ *
    ctTg1 ((seedScale c : ℂ) * (Complex.I * (τ : ℂ))) *
    seedT 0 ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ)))) * hcore

lemma wg1PartB_edge_eq {ε c ξ : ℝ} (hε : ε = 1 ∨ ε = -1) (_hc : 0 < c) (hξ : 0 < ξ) (τ : ℝ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartB ε c ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        wg1AmpB ε c τ * wg1YB (c ^ (1 / 3 : ℝ) * τ) := by
  have hcore : (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
      (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * (uctAstar τ : ℂ) := by
    by_cases hτ : τ = 0
    · subst hτ; exact seedZ_edge_core_zero
    · exact seedZ_edge_core_all hε hτ
  have hcomm : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
  have hY : wg1YB (c ^ (1 / 3 : ℝ) * τ) = seedT 0 ((seedScale c : ℂ) * (Complex.I * (τ : ℂ))) := by
    unfold wg1YB seedV seedScale; congr 1; push_cast; ring
  rw [mellinK0_imag_outer c ξ τ hξ, ← outerK_eq, hY]
  unfold wg1PartB wg1AmpB
  rw [hcomm]
  set Bc := Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))
  set Ph := Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ))
  linear_combination (Bc * Ph * (seedT 0 (seedScale c : ℂ))⁻¹ *
    seedT 0 ((seedScale c : ℂ) * (Complex.I * (τ : ℂ))) *
    ctTg1 ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ)))) * hcore

/-! ### `CuspAmplitude (π / 8)` and `CuspProfile` helpers -/

private lemma cuspAmplitude_const_mul {η C_A : ℝ} {A : ℝ → ℂ} (k : ℂ) (hA : CuspAmplitude η C_A A) :
    CuspAmplitude η (‖k‖ * C_A) (fun τ => k * A τ) where
  contDiff := contDiff_const.mul hA.contDiff
  deriv_bound j hj τ := by
    rw [show (fun t => k * A t) = k • A from rfl, iteratedDeriv_const_smul_field, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hA.deriv_bound j hj τ) (norm_nonneg k)).trans_eq (mul_assoc _ _ _).symm

private lemma cuspAmplitude_mul_bdd {η C_A M : ℝ} {A f : ℝ → ℂ} (hCA : 0 ≤ C_A) (hM : 0 ≤ M)
    (hA : CuspAmplitude η C_A A) (hf_cd : ContDiff ℝ 3 f) (hf_bd : ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j f τ‖ ≤ M) :
    CuspAmplitude η (8 * C_A * M) (fun τ => A τ * f τ) where
  contDiff := hA.contDiff.mul hf_cd
  deriv_bound j hj τ := by
    have hAa : ContDiffAt ℝ j A τ := hA.contDiff.contDiffAt.of_le (by exact_mod_cast hj)
    have hfa : ContDiffAt ℝ j f τ := hf_cd.contDiffAt.of_le (by exact_mod_cast hj)
    rw [show (fun t => A t * f t) = A * f from rfl, iteratedDeriv_mul hAa hfa]
    have htri := norm_sum_le (Finset.range (j + 1)) fun i =>
      (Nat.choose j i : ℂ) * iteratedDeriv i A τ * iteratedDeriv (j - i) f τ
    refine htri.trans ?_
    have hexp0 : 0 ≤ Real.exp (-η * |τ|) := (Real.exp_pos _).le
    have hsum : ∑ i ∈ Finset.range (j + 1),
        ‖(Nat.choose j i : ℂ) * iteratedDeriv i A τ * iteratedDeriv (j - i) f τ‖ ≤
        (∑ i ∈ Finset.range (j + 1), (Nat.choose j i : ℝ)) * (C_A * M * Real.exp (-η * |τ|)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc (Nat.choose j i : ℝ) * ‖iteratedDeriv i A τ‖ * ‖iteratedDeriv (j - i) f τ‖
          ≤ (Nat.choose j i : ℝ) * (C_A * Real.exp (-η * |τ|)) * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hA.deriv_bound i (hij.trans hj) τ) (Nat.cast_nonneg _))
              (hf_bd (j - i) (by omega) τ) (norm_nonneg _) (by positivity)
        _ = (Nat.choose j i : ℝ) * (C_A * M * Real.exp (-η * |τ|)) := by ring
    refine hsum.trans ?_
    have hch : ∑ i ∈ Finset.range (j + 1), (Nat.choose j i : ℝ) = (2 : ℝ) ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    rw [hch]
    have hpow : (2 : ℝ) ^ j ≤ 8 := by
      calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj
        _ = 8 := by norm_num
    nlinarith [mul_nonneg (mul_nonneg hCA hM) hexp0]

private lemma cexp_deriv3_bdd {f : ℝ → ℂ} {M0 M1 M2 M3 : ℝ}
    (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hcd : ContDiff ℝ 3 f)
    (hb0 : ∀ t, ‖Complex.exp (f t)‖ ≤ M0) (hb1 : ∀ t, ‖deriv f t‖ ≤ M1)
    (hb2 : ∀ t, ‖iteratedDeriv 2 f t‖ ≤ M2) (hb3 : ∀ t, ‖iteratedDeriv 3 f t‖ ≤ M3) :
    ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun t => Complex.exp (f t)) τ‖ ≤
      max M0 (max (M0 * M1) (max (M0 * M1 ^ 2 + M0 * M2)
        (M0 * M1 ^ 3 + 3 * M0 * M1 * M2 + M0 * M3))) := by
  let g : ℝ → ℂ := fun t => Complex.exp (f t)
  have hcexp_cd : ContDiff ℝ 3 g := hcd.cexp
  have hd1 : ∀ t, deriv g t = g t * deriv f t := fun t =>
    (((hcd.differentiable (by norm_num)) t).hasDerivAt.cexp).deriv
  have hg1 : ∀ t, ‖deriv g t‖ ≤ M0 * M1 := fun t => by
    rw [hd1, norm_mul]; exact mul_le_mul (hb0 t) (hb1 t) (norm_nonneg _) hM0
  have hhd_f1 : ContDiff ℝ 2 (deriv f) := ((contDiff_succ_iff_deriv (n := 2)).mp hcd).2.2
  have hd2 : ∀ t, deriv (deriv g) t = deriv g t * deriv f t + g t * iteratedDeriv 2 f t := fun t => by
    have hev : deriv g = fun s => g s * deriv f s := funext hd1
    rw [hev]
    have hg' := ((hcd.differentiable (by norm_num)) t).hasDerivAt.cexp
    have hf' : HasDerivAt (deriv f) (iteratedDeriv 2 f t) t := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]; exact ((hhd_f1.differentiable (by norm_num)) t).hasDerivAt
    exact (hg'.mul hf').deriv
  have hg2 : ∀ t, ‖iteratedDeriv 2 g t‖ ≤ M0 * M1 ^ 2 + M0 * M2 := fun t => by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd2]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc ‖deriv g t‖ * ‖deriv f t‖ ≤ (M0 * M1) * M1 := mul_le_mul (hg1 t) (hb1 t) (norm_nonneg _) (by positivity)
        _ = M0 * M1 ^ 2 := by ring
    · rw [norm_mul]; exact mul_le_mul (hb0 t) (hb2 t) (norm_nonneg _) hM0
  have hhd_f2 : ContDiff ℝ 1 (deriv (deriv f)) := ((contDiff_succ_iff_deriv (n := 1)).mp hhd_f1).2.2
  have hhd_g1 : ContDiff ℝ 2 (deriv g) := ((contDiff_succ_iff_deriv (n := 2)).mp hcexp_cd).2.2
  have hg3 : ∀ t, ‖iteratedDeriv 3 g t‖ ≤ M0 * M1 ^ 3 + 3 * M0 * M1 * M2 + M0 * M3 := fun t => by
    have hev : deriv (deriv g) = fun s => deriv g s * deriv f s + g s * iteratedDeriv 2 f s := funext hd2
    have hg1' : HasDerivAt (deriv g) (iteratedDeriv 2 g t) t := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]; exact ((hhd_g1.differentiable (by norm_num)) t).hasDerivAt
    have hf1' : HasDerivAt (deriv f) (iteratedDeriv 2 f t) t := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]; exact ((hhd_f1.differentiable (by norm_num)) t).hasDerivAt
    have hf2' : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t := by
      have h3 : HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) t) t :=
        ((hhd_f2.differentiable (by norm_num)) t).hasDerivAt
      have heq2 : iteratedDeriv 2 f = deriv (deriv f) := by
        ext s; rw [iteratedDeriv_succ, iteratedDeriv_one]
      have heq3 : deriv (deriv (deriv f)) t = iteratedDeriv 3 f t := by
        rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [heq3] at h3
      rw [← heq2] at h3
      exact h3
    have hg0' := ((hcd.differentiable (by norm_num)) t).hasDerivAt.cexp
    have hsum : HasDerivAt (deriv (deriv g)) (iteratedDeriv 2 g t * deriv f t + deriv g t * iteratedDeriv 2 f t +
        (g t * deriv f t * iteratedDeriv 2 f t + g t * iteratedDeriv 3 f t)) t := by
      rw [hev]; exact (hg1'.mul hf1').add (hg0'.mul hf2')
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, hsum.deriv]
    have t1 : ‖iteratedDeriv 2 g t * deriv f t‖ ≤ M0 * M1 ^ 3 + M0 * M1 * M2 := by
      rw [norm_mul]
      calc ‖iteratedDeriv 2 g t‖ * ‖deriv f t‖ ≤ (M0 * M1 ^ 2 + M0 * M2) * M1 :=
            mul_le_mul (hg2 t) (hb1 t) (norm_nonneg _) (by positivity)
        _ = M0 * M1 ^ 3 + M0 * M1 * M2 := by ring
    have t2 : ‖deriv g t * iteratedDeriv 2 f t‖ ≤ M0 * M1 * M2 := by
      rw [norm_mul]; exact mul_le_mul (hg1 t) (hb2 t) (norm_nonneg _) (by positivity)
    have t3 : ‖g t * deriv f t * iteratedDeriv 2 f t‖ ≤ M0 * M1 * M2 := by
      rw [norm_mul]
      calc ‖g t * deriv f t‖ * ‖iteratedDeriv 2 f t‖ ≤ (M0 * M1) * M2 := by
            rw [norm_mul]; exact mul_le_mul (mul_le_mul (hb0 t) (hb1 t) (norm_nonneg _) hM0) (hb2 t) (norm_nonneg _) (by positivity)
        _ = M0 * M1 * M2 := by ring
    have t4 : ‖g t * iteratedDeriv 3 f t‖ ≤ M0 * M3 := by
      rw [norm_mul]; exact mul_le_mul (hb0 t) (hb3 t) (norm_nonneg _) hM0
    calc ‖iteratedDeriv 2 g t * deriv f t + deriv g t * iteratedDeriv 2 f t +
            (g t * deriv f t * iteratedDeriv 2 f t + g t * iteratedDeriv 3 f t)‖
        ≤ ‖iteratedDeriv 2 g t * deriv f t + deriv g t * iteratedDeriv 2 f t‖ +
            ‖g t * deriv f t * iteratedDeriv 2 f t + g t * iteratedDeriv 3 f t‖ := norm_add_le _ _
      _ ≤ (‖iteratedDeriv 2 g t * deriv f t‖ + ‖deriv g t * iteratedDeriv 2 f t‖) +
            (‖g t * deriv f t * iteratedDeriv 2 f t‖ + ‖g t * iteratedDeriv 3 f t‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ _ := by linarith
  intro j hj τ
  interval_cases j
  · rw [iteratedDeriv_zero]; exact (hb0 τ).trans (le_max_left _ _)
  · rw [iteratedDeriv_one]; exact (hg1 τ).trans (le_max_of_le_right (le_max_left _ _))
  · exact (hg2 τ).trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact (hg3 τ).trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

private lemma exp_phase_bdd (C_f : ℝ) {f : ℝ → ℝ} (hf_cd : ContDiff ℝ 3 f)
    (hf1 : ∀ τ, ‖deriv f τ‖ ≤ C_f) (hf2 : ∀ τ, ‖iteratedDeriv 2 f τ‖ ≤ C_f)
    (hf3 : ∀ τ, ‖iteratedDeriv 3 f τ‖ ≤ C_f) :
    ∃ M ≥ 0, ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun t : ℝ => Complex.exp (Complex.I * (f t : ℂ))) τ‖ ≤ M := by
  have hCf0 : 0 ≤ C_f := (norm_nonneg _).trans (hf1 0)
  let g : ℝ → ℂ := fun t => Complex.I * (f t : ℂ)
  have hcd : ContDiff ℝ 3 g := contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hf_cd)
  have hb0 : ∀ t, ‖Complex.exp (g t)‖ ≤ 1 := fun t => by simp [g, Complex.norm_exp_I_mul_ofReal]
  have hb1 : ∀ t, ‖deriv g t‖ ≤ C_f := fun t => by
    have hf' : HasDerivAt f (deriv f t) t := ((hf_cd.differentiable (by norm_num)) t).hasDerivAt
    have hd : HasDerivAt g (Complex.I * Complex.ofReal (deriv f t)) t := hf'.ofReal_comp.const_mul Complex.I
    rw [hd.deriv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]; exact hf1 t
  have hb2 : ∀ t, ‖iteratedDeriv 2 g t‖ ≤ C_f := fun t => by
    rw [show g = Complex.I • fun s : ℝ => (f s : ℂ) from rfl, iteratedDeriv_const_smul_field,
      norm_smul, Complex.norm_I, one_mul, iteratedDeriv_ofReal_eq', Complex.norm_real]
    exact hf2 t
  have hb3 : ∀ t, ‖iteratedDeriv 3 g t‖ ≤ C_f := fun t => by
    rw [show g = Complex.I • fun s : ℝ => (f s : ℂ) from rfl, iteratedDeriv_const_smul_field,
      norm_smul, Complex.norm_I, one_mul, iteratedDeriv_ofReal_eq', Complex.norm_real]
    exact hf3 t
  refine ⟨_, by positivity, cexp_deriv3_bdd zero_le_one hCf0 hCf0 hCf0 hcd hb0 hb1 hb2 hb3⟩

private lemma poly_exp_half_le (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, (1 + |τ|) ^ n * Real.exp (-(π / 8 * |τ|)) ≤ M := by
  obtain ⟨M, hM0, hM⟩ := poly_exp_le_n n
  refine ⟨M * 8 ^ n, by positivity, fun τ => ?_⟩
  have h1 : 1 + |τ| ≤ 8 * (1 + |τ| / 8) := by linarith [abs_nonneg τ]
  have hpow : (1 + |τ|) ^ n ≤ 8 ^ n * (1 + |τ| / 8) ^ n := by
    calc (1 + |τ|) ^ n ≤ (8 * (1 + |τ| / 8)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = 8 ^ n * (1 + |τ| / 8) ^ n := mul_pow _ _ n
  have hm := hM (|τ| / 8) (by positivity)
  have hex : -(π / 8 * |τ|) = -(π * (|τ| / 8)) := by ring
  rw [hex]
  calc (1 + |τ|) ^ n * Real.exp (-(π * (|τ| / 8)))
      ≤ (8 ^ n * (1 + |τ| / 8) ^ n) * Real.exp (-(π * (|τ| / 8))) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = 8 ^ n * ((1 + |τ| / 8) ^ n * Real.exp (-(π * (|τ| / 8)))) := by ring
    _ ≤ 8 ^ n * M := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = M * 8 ^ n := by ring

private lemma uctAstar_symW_Ici :
    ∃ K : ℕ → ℝ, FctSym.SymW (Ici (1 : ℝ)) (fun τ => Real.exp (-(π / 8 * τ))) K uctAstar := by
  have hm_sym : ∃ K, FctSym.SymW (Ici (1 : ℝ)) (fun τ => 1 + τ) K uctM := by
    obtain ⟨Am, hAm0, hAm⟩ := FctSym.uctM_deriv_symbol
    refine ⟨Nat.rec (π / 2) (fun j _ => Am j), ?_⟩
    refine
      { pos := fun _ hx => lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ _ from hx)
        smooth := ⟨Ioi 0, isOpen_Ioi, fun _ hx => lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ _ from hx), FctSym.contDiffOn_uctM⟩
        K_nonneg := fun r => by cases r with | zero => exact div_nonneg Real.pi_pos.le (by norm_num) | succ j => exact hAm0 j
        w_nonneg := fun τ hτ => by linarith [show (1 : ℝ) ≤ τ from hτ]
        bound := fun r τ hτ => ?_ }
    have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ τ from hτ)
    cases r with
    | zero =>
      simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one, abs_of_pos (uctM_pos hτ0)]
      have hrec : (Nat.rec (π / 2) (fun j _ => Am j) 0 : ℝ) = π / 2 := rfl
      rw [hrec]
      exact (FctSym.uctM_le_linear hτ0).trans (by nlinarith [Real.pi_pos])
    | succ j =>
      rw [iteratedDeriv_succ']
      have hbd := hAm j τ hτ0
      have h1t : 1 ≤ 1 + τ := by linarith [hτ0]
      calc |iteratedDeriv j (deriv uctM) τ| ≤ Am j * 1 * (τ ^ (j + 1))⁻¹ := hbd
        _ ≤ Am j * (1 + τ) * (τ ^ (j + 1))⁻¹ := by gcongr; exact hAm0 j
  have hθm12_sym : ∃ K, FctSym.SymW (Ici (1 : ℝ)) (fun _ => 1) K (fun τ => (τ * mPrime τ) ^ (-(1 / 2 : ℝ))) := by
    obtain ⟨Kth, hKth⟩ := FctSym.theta_symW_Ici
    obtain ⟨Kmp, hKmp⟩ := FctSym.mPrime_symW
    have hθ_ge : ∀ τ ∈ Ici (1 : ℝ), (π * (1 / 8)) ^ 2 / (6 + (π * (1 / 8)) ^ 2) ≤ τ * mPrime τ :=
      fun _ hx => FctSym.theta_ge_Ici (le_trans (by norm_num) (show (1 : ℝ) ≤ _ from hx))
    let θ0 : ℝ := (π * (1 / 8)) ^ 2 / (6 + (π * (1 / 8)) ^ 2)
    have hθ0_pos : 0 < θ0 := by positivity
    have hθ_le : ∀ τ ∈ Ici (1 : ℝ), τ * mPrime τ ≤ Kmp 0 + θ0 := fun τ hτ => by
      have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ τ from hτ)
      have hb := hKmp.bound 0 τ hτ0
      simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at hb
      have hdiv : τ / (1 + τ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      calc τ * mPrime τ ≤ τ * (Kmp 0 * (1 + τ)⁻¹) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hτ0.le
        _ = Kmp 0 * (τ / (1 + τ)) := by ring
        _ ≤ Kmp 0 * 1 := mul_le_mul_of_nonneg_left hdiv (hKmp.K_nonneg 0)
        _ ≤ Kmp 0 + θ0 := by linarith [hθ0_pos]
    have hΦ_cd : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Ioi 0) := fun y hy =>
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hy)).contDiffWithinAt
    have hbP : ∀ j : ℕ, ∃ P : ℝ, 0 ≤ P ∧ ∀ z ∈ Icc θ0 (Kmp 0 + θ0),
        |iteratedDeriv j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) z| ≤ P := fun j => by
      have hcdj := (FctSym.contDiffOn_iteratedDeriv_gen isOpen_Ioi hΦ_cd j).continuousOn
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hcdj.mono fun z hz => lt_of_lt_of_le hθ0_pos hz.1)
      exact ⟨max B 0, le_max_right _ _, fun z hz => (Real.norm_eq_abs _ ▸ hB z hz).trans (le_max_left _ _)⟩
    choose P hP0 hP using hbP
    refine ⟨_, (hKth.mono_set (fun _ hx => le_trans (by norm_num) (show (1 : ℝ) ≤ _ from hx))).comp_smooth
      (B := 1) (L := θ0 ^ (-(1 / 2 : ℝ))) isOpen_Ioi hΦ_cd
      (fun τ hτ => hθ0_pos.trans_le (hθ_ge τ hτ))
      (fun j τ hτ => hP j (τ * mPrime τ) ⟨hθ_ge τ hτ, hθ_le τ hτ⟩) hP0 (fun _ _ => le_rfl)
      (Real.rpow_pos_of_pos hθ0_pos _).le (fun τ hτ => by
        rw [mul_one, abs_of_pos (Real.rpow_pos_of_pos (hθ0_pos.trans_le (hθ_ge τ hτ)) _)]
        exact Real.rpow_le_rpow_of_nonpos hθ0_pos (hθ_ge τ hτ) (by norm_num))⟩
  obtain ⟨Kth, hth⟩ := hθm12_sym
  obtain ⟨Ks, hs⟩ := sinh_kernel_Ici_symW
  have hrp := FctSym.SymW.rpow_gen (S := Ici (1 : ℝ)) (fun _ hx => lt_of_lt_of_le zero_lt_one hx) 1 (3 : ℝ)
  let c0 : ℝ := π ^ 2 * Real.sqrt (π ^ 2 / 6)
  have hprod := (((hrp.smul c0).mul hth).mul (hs.mono_set (fun _ hx => le_trans (by norm_num) (show (1 : ℝ) ≤ _ from hx))))
  have hAstar_eq : ∀ {τ : ℝ}, 0 < τ →
      uctAstar τ = c0 * (1 * τ ^ (3 : ℝ)) * (τ * mPrime τ) ^ (-(1 / 2 : ℝ)) * (Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2) := by
    intro τ hτ
    have h1 := warpAmpScal_eq_Ici hτ
    have h2 : warpAmpScal τ = uctM τ * (τ ^ (-(5 / 2 : ℝ)) * uctAstar τ) := by
      unfold warpAmpScal; rw [uctAstar_eq_paper hτ, FctSym.uctMderiv_eq_mPrime hτ]
      have hsq : τ ^ (-(5 / 2 : ℝ)) * τ ^ (5 / 2 : ℝ) = 1 := by rw [← Real.rpow_add hτ]; simp
      calc uctM τ * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * mPrime τ)
          = uctM τ * (1 * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * mPrime τ)) := by ring
        _ = uctM τ * (τ ^ (-(5 / 2 : ℝ)) * (τ ^ (5 / 2 : ℝ) * ‖uctHstar (Complex.I * (τ : ℂ))‖ /
              Real.sqrt (6 / π ^ 2 * mPrime τ))) := by rw [← hsq]; ring
    have hm0 : 0 < uctM τ := uctM_pos hτ
    have hτ52 : τ ^ (5 / 2 : ℝ) * τ ^ (-(5 / 2 : ℝ)) = 1 := by rw [← Real.rpow_add hτ]; simp
    have hτ3 : τ ^ (5 / 2 : ℝ) * τ ^ (1 / 2 : ℝ) = τ ^ (3 : ℝ) := by rw [← Real.rpow_add hτ]; norm_num
    have heq' : uctM τ * (τ ^ (-(5 / 2 : ℝ)) * uctAstar τ) =
        uctM τ * (c0 * (τ ^ (1 / 2 : ℝ)) * (τ * mPrime τ) ^ (-(1 / 2 : ℝ)) *
          (Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2)) := by
      rw [← h2, h1]; dsimp only [c0]; ring
    have h3 := mul_left_cancel₀ hm0.ne' heq'
    calc uctAstar τ = τ ^ (5 / 2 : ℝ) * (τ ^ (-(5 / 2 : ℝ)) * uctAstar τ) := by rw [← mul_assoc, hτ52, one_mul]
      _ = τ ^ (5 / 2 : ℝ) * (c0 * τ ^ (1 / 2 : ℝ) * (τ * mPrime τ) ^ (-(1 / 2 : ℝ)) *
            (Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2)) := by rw [h3]
      _ = c0 * (1 * (τ ^ (5 / 2 : ℝ) * τ ^ (1 / 2 : ℝ))) * (τ * mPrime τ) ^ (-(1 / 2 : ℝ)) *
            (Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2) := by ring
      _ = _ := by rw [hτ3]
  have hcon := hprod.congr (U := Ioi 0) isOpen_Ioi
    (fun τ hτ => lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ _ from hτ))
    (g := uctAstar) fun τ hτ => (hAstar_eq hτ).symm
  obtain ⟨M3, hM30, hM3⟩ := poly_exp_half_le 3
  let C_e : ℝ := |c0| * M3 + 1
  have hCe0 : 0 ≤ C_e := by positivity
  have hw_le : ∀ τ ∈ Ici (1 : ℝ), (|c0| * (|1| * τ ^ (3 : ℝ))) * 1 * Real.exp (-(π / 2 * τ)) ≤
      C_e * Real.exp (-(π / 8 * τ)) := fun τ hτ => by
    have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ τ from hτ)
    have hexp_split : Real.exp (-(π / 2 * τ)) = Real.exp (-(π / 8 * τ)) * Real.exp (-(3 * π / 8 * τ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h38 : Real.exp (-(3 * π / 8 * τ)) ≤ Real.exp (-(π / 8 * |τ|)) := by
      rw [abs_of_pos hτ0]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hτ3_le : τ ^ (3 : ℝ) ≤ (1 + |τ|) ^ 3 := by
      rw [abs_of_pos hτ0, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ hτ0.le (by linarith) 3
    have hm3 := hM3 τ
    calc (|c0| * (|1| * τ ^ (3 : ℝ))) * 1 * Real.exp (-(π / 2 * τ))
        = |c0| * (τ ^ (3 : ℝ) * Real.exp (-(3 * π / 8 * τ))) * Real.exp (-(π / 8 * τ)) := by
          rw [abs_one, one_mul, mul_one, hexp_split]; ring
      _ ≤ |c0| * ((1 + |τ|) ^ 3 * Real.exp (-(π / 8 * |τ|))) * Real.exp (-(π / 8 * τ)) := by gcongr
      _ ≤ (|c0| * M3) * Real.exp (-(π / 8 * τ)) := by gcongr
      _ ≤ C_e * Real.exp (-(π / 8 * τ)) := by gcongr; linarith
  have hcon_w := hcon.of_le hw_le (fun _ => le_rfl)
  refine ⟨fun r => C_e * _,
    { pos := hcon_w.pos
      smooth := hcon_w.smooth
      K_nonneg := fun r => mul_nonneg hCe0 (hcon_w.K_nonneg r)
      w_nonneg := fun τ _ => (Real.exp_pos _).le
      bound := fun r τ hτ => by
        have hb := hcon_w.bound r τ hτ
        refine hb.trans_eq (by ring) }⟩

private lemma uctAstar_cuspAmplitude :
    ∃ C : ℝ, 0 ≤ C ∧ CuspAmplitude (π / 8) C (fun τ : ℝ => (uctAstar τ : ℂ)) := by
  obtain ⟨K_p, hsym⟩ := uctAstar_symW_Ici
  have hcd_R : ContDiff ℝ 3 uctAstar := contDiff_uctAstar.of_le le_top
  have hcd_C : ContDiff ℝ 3 (fun τ : ℝ => (uctAstar τ : ℂ)) := Complex.ofRealCLM.contDiff.comp hcd_R
  have hb_compact : ∀ j : ℕ, ∃ M ≥ 0, ∀ τ ∈ Icc (-1 : ℝ) 1, |iteratedDeriv j uctAstar τ| ≤ M := fun j => by
    have hc : Continuous (iteratedDeriv j uctAstar) := contDiff_uctAstar.continuous_iteratedDeriv j (by simp)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun τ hτ => (Real.norm_eq_abs _ ▸ hM τ hτ).trans (le_max_left _ _)⟩
  choose M_c hMc0 hMc using hb_compact
  let C_loc : ℝ := max (max (M_c 0) (M_c 1)) (max (M_c 2) (M_c 3)) * Real.exp (π / 8)
  let C_far : ℝ := max (max (K_p 0) (K_p 1)) (max (K_p 2) (K_p 3))
  have hCloc0 : 0 ≤ C_loc := mul_nonneg (le_max_of_le_left (le_max_of_le_left (hMc0 0))) (Real.exp_pos _).le
  have hCfar0 : 0 ≤ C_far := le_max_of_le_left (le_max_of_le_left (hsym.K_nonneg 0))
  refine ⟨max C_loc C_far, le_max_of_le_left hCloc0, hcd_C, fun j hj τ => ?_⟩
  have hid_eq : ‖iteratedDeriv j (fun t : ℝ => (uctAstar t : ℂ)) τ‖ = |iteratedDeriv j uctAstar τ| := by
    rw [iteratedDeriv_ofReal_eq', Complex.norm_real, Real.norm_eq_abs]
  rw [hid_eq]
  have hKc_le : M_c j ≤ max (max (M_c 0) (M_c 1)) (max (M_c 2) (M_c 3)) := by
    interval_cases j
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  have hKf_le : K_p j ≤ C_far := by
    dsimp only [C_far]
    interval_cases j
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_of_le_right (le_max_left _ _)
    · exact le_max_of_le_right (le_max_right _ _)
  have hpos_ge : ∀ t : ℝ, 1 ≤ t → |iteratedDeriv j uctAstar t| ≤ C_far * Real.exp (-(π / 8 * t)) := fun t ht => by
    have hbd := hsym.bound j t ht
    have hpow : (t ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht)
    calc |iteratedDeriv j uctAstar t|
        ≤ K_p j * Real.exp (-(π / 8 * t)) * (t ^ j)⁻¹ := hbd
      _ ≤ K_p j * Real.exp (-(π / 8 * t)) * 1 :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (hsym.K_nonneg j) (Real.exp_pos _).le)
      _ = K_p j * Real.exp (-(π / 8 * t)) := mul_one _
      _ ≤ C_far * Real.exp (-(π / 8 * t)) := mul_le_mul_of_nonneg_right hKf_le (Real.exp_pos _).le
  by_cases h1 : |τ| ≤ 1
  · have hmem : τ ∈ Icc (-1 : ℝ) 1 := abs_le.mp h1
    have hexp : Real.exp (-(π / 8)) ≤ Real.exp (-(π / 8 * |τ|)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc |iteratedDeriv j uctAstar τ| ≤ M_c j := hMc j τ hmem
      _ ≤ max (max (M_c 0) (M_c 1)) (max (M_c 2) (M_c 3)) := hKc_le
      _ = C_loc * Real.exp (-(π / 8)) := by dsimp only [C_loc]; rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ C_loc * Real.exp (-(π / 8 * |τ|)) := mul_le_mul_of_nonneg_left hexp hCloc0
      _ ≤ max C_loc C_far * Real.exp (-(π / 8 * |τ|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ = max C_loc C_far * Real.exp (-(π / 8) * |τ|) := by congr 2; ring
  · push Not at h1
    rcases le_or_gt 0 τ with hτ0 | hτ0
    · rw [abs_of_nonneg hτ0] at h1 ⊢
      exact (hpos_ge τ h1.le).trans
        ((mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le).trans_eq (by congr 2; ring))
    · have hneg : 1 ≤ -τ := by rw [abs_of_neg hτ0] at h1; exact h1.le
      have hcomp_id : (fun t : ℝ => uctAstar (-t)) = uctAstar := funext uctAstar_neg
      have hid_neg : iteratedDeriv j uctAstar τ = (-1 : ℝ) ^ j * iteratedDeriv j uctAstar (-τ) := by
        have h := iteratedDeriv_comp_neg (n := j) uctAstar (-τ)
        simp only [neg_neg, hcomp_id, smul_eq_mul] at h
        have hsq : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
        calc iteratedDeriv j uctAstar τ = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * iteratedDeriv j uctAstar τ := by rw [hsq, one_mul]
          _ = (-1 : ℝ) ^ j * ((-1 : ℝ) ^ j * iteratedDeriv j uctAstar τ) := by ring
          _ = (-1 : ℝ) ^ j * iteratedDeriv j uctAstar (-τ) := by rw [h]
      rw [hid_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_neg hτ0]
      exact (hpos_ge (-τ) hneg).trans
        ((mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le).trans_eq (by congr 2; ring))

private lemma outerTheta_exp_bdd_single {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ M ≥ 0, ContDiff ℝ 3 (fun t : ℝ => Complex.exp (-(Complex.I * (outerTheta ε t : ℂ)))) ∧
      ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun t : ℝ => Complex.exp (-(Complex.I * (outerTheta ε t : ℂ)))) τ‖ ≤ M := by
  obtain ⟨-, h3⟩ := ct_outer_part3
  have hε' : ε = -1 ∨ ε = 1 := hε.symm
  obtain ⟨-, C1, hC1⟩ := h3 ε hε' 1 le_rfl
  obtain ⟨-, C2, hC2⟩ := h3 ε hε' 2 (by norm_num)
  obtain ⟨-, C3, hC3⟩ := h3 ε hε' 3 (by norm_num)
  let C := max (max |C1| |C2|) |C3|
  have hbd_gen : ∀ (k : ℕ) (Ck : ℝ), (∀ τ, |iteratedDeriv k (outerTheta ε) τ| ≤ Ck / (1 + |τ|) ^ (k + 1)) →
      ∀ τ, ‖iteratedDeriv k (-outerTheta ε) τ‖ ≤ |Ck| := fun k Ck hCk τ => by
    rw [Real.norm_eq_abs, iteratedDeriv_neg, abs_neg]
    have hp : 1 ≤ (1 + |τ|) ^ (k + 1) := one_le_pow₀ (by linarith [abs_nonneg τ])
    calc |iteratedDeriv k (outerTheta ε) τ| ≤ Ck / (1 + |τ|) ^ (k + 1) := hCk τ
      _ ≤ |Ck| / (1 + |τ|) ^ (k + 1) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Ck| := div_le_self (abs_nonneg _) hp
  have hf_cd : ContDiff ℝ 3 (-outerTheta ε) := (contDiff_outerTheta ε).neg.of_le le_top
  obtain ⟨M, hM0, hM⟩ := exp_phase_bdd C hf_cd
    (fun τ => by rw [← iteratedDeriv_one]; exact (hbd_gen 1 C1 hC1 τ).trans (le_max_of_le_left (le_max_left _ _)))
    (fun τ => (hbd_gen 2 C2 hC2 τ).trans (le_max_of_le_left (le_max_right _ _)))
    (fun τ => (hbd_gen 3 C3 hC3 τ).trans (le_max_right _ _))
  have hcd_exp : ContDiff ℝ 3 (fun t : ℝ => Complex.exp (-(Complex.I * (outerTheta ε t : ℂ)))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ((contDiff_outerTheta ε).of_le le_top))).neg.cexp
  refine ⟨M, hM0, hcd_exp, fun j hj τ => ?_⟩
  have heq : (fun t : ℝ => Complex.exp (-(Complex.I * (outerTheta ε t : ℂ)))) =
      fun t : ℝ => Complex.exp (Complex.I * ((-outerTheta ε t : ℝ) : ℂ)) := by
    funext t; push_cast; ring_nf
  rw [heq]; exact hM j hj τ

private lemma outerTheta_exp_bdd :
    ∃ M ≥ 0, ∀ {ε : ℝ}, (ε = 1 ∨ ε = -1) →
      ContDiff ℝ 3 (fun t : ℝ => Complex.exp (-(Complex.I * (outerTheta ε t : ℂ)))) ∧
      ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun t : ℝ => Complex.exp (-(Complex.I * (outerTheta ε t : ℂ)))) τ‖ ≤ M := by
  obtain ⟨M1, hM1, h1cd, h1⟩ := outerTheta_exp_bdd_single (Or.inl rfl)
  obtain ⟨M2, hM2, h2cd, h2⟩ := outerTheta_exp_bdd_single (Or.inr rfl)
  refine ⟨max M1 M2, le_max_of_le_left hM1, fun {ε} hε => ?_⟩
  rcases hε with rfl | rfl
  · exact ⟨h1cd, fun j hj τ => (h1 j hj τ).trans (le_max_left _ _)⟩
  · exact ⟨h2cd, fun j hj τ => (h2 j hj τ).trans (le_max_right _ _)⟩

lemma imag_cauchy_bd {F : ℂ → ℂ} {p r K : ℝ} (_hr : 0 < r) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hF : DifferentiableOn ℂ F Complex.slitPlane) (hbd : ∀ w : ℂ, ‖w‖ ≤ 3 / 2 * r → ‖F w‖ ≤ K * ‖w‖ ^ p)
    (j : ℕ) {q : ℝ} (hq0 : q ≠ 0) (hqr : |q| ≤ r) :
    ‖iteratedDeriv j (fun t : ℝ => F (Complex.I * (t : ℂ))) q‖ ≤
      ((j.factorial : ℝ) * K * (3 / 2 : ℝ) ^ p * 2 ^ j) * |q| ^ (p - j) := by
  have hqpos : 0 < |q| := abs_pos.mpr hq0
  have hslit : ∀ z : ℂ, ‖z - Complex.I * (q : ℂ)‖ ≤ |q| / 2 → z ∈ Complex.slitPlane := fun z hz => by
    right; intro him
    have h1 : |z.im - q| ≤ |q| / 2 := by
      have := Complex.abs_im_le_norm (z - Complex.I * (q : ℂ))
      simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add] at this
      linarith
    rw [him, zero_sub, abs_neg] at h1; linarith
  have hsub : Metric.closedBall (Complex.I * (q : ℂ)) (|q| / 2) ⊆ Complex.slitPlane := fun z hz =>
    hslit z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  rw [iteratedDeriv_real_imag Complex.isOpen_slitPlane hF j q (hslit _ (by simp; positivity)),
    norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := Complex.I * (q : ℂ)) (R := |q| / 2)
    (C := K * (3 / 2 * |q|) ^ p) j (by positivity) (hF.diffContOnCl_ball hsub) (fun z hz => by
      have hz' : ‖z - Complex.I * (q : ℂ)‖ = |q| / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hzn : ‖z‖ ≤ 3 / 2 * |q| := by
        have := norm_le_norm_add_norm_sub' z (Complex.I * (q : ℂ))
        have h2 : ‖Complex.I * (q : ℂ)‖ = |q| := by simp
        linarith
      exact (hbd z (hzn.trans (by linarith))).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hzn hp) hK))
  refine hcauchy.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by norm_num) hqpos.le, div_pow, show (p - (j : ℝ)) = p + -(j : ℝ) by ring,
    Real.rpow_add hqpos, Real.rpow_neg hqpos.le, Real.rpow_natCast]
  field_simp

private lemma binet_exp_bdd :
    ∃ M ≥ 0, ∀ c : ℝ, 1 ≤ c → ContDiff ℝ 3 (fun τ : ℝ => Complex.exp (binetDiff c ((τ : ℂ) * Complex.I))) ∧
      (∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun τ : ℝ => Complex.exp (binetDiff c ((τ : ℂ) * Complex.I))) τ‖ ≤ M) := by
  have hb_exp : ∀ j, 1 ≤ j → j ≤ 3 → ∀ {c : ℝ}, 1 ≤ c →
      ContDiff ℝ 3 (fun τ : ℝ => binetDiff c ((τ : ℂ) * Complex.I)) ∧
      ∀ τ : ℝ, ‖iteratedDeriv j (fun τ : ℝ => binetDiff c ((τ : ℂ) * Complex.I)) τ‖ ≤ (j.factorial : ℝ) / 12 := fun j hj1 _ {c} hc => by
    have hc0 : 0 < c := by linarith
    have hopen : IsOpen {ζ : ℂ | ζ.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have hcd_C : ContDiffOn ℂ ⊤ (binetDiff c) {ζ : ℂ | ζ.re < 1} := by
      refine (DifferentiableOn.sub ?_ (differentiableOn_const _)).contDiffOn hopen
      refine binetRem_differentiableOn.comp
        (((differentiable_const (c : ℂ)).mul ((differentiable_const (1 : ℂ)).sub differentiable_id)).differentiableOn)
        fun ζ hζ => by
          change 0 < ((c : ℂ) * ((1 : ℂ) - ζ)).re
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
            zero_mul, sub_zero]
          exact mul_pos hc0 (sub_pos.mpr hζ)
    have hcd_R : ContDiff ℝ 3 (fun τ : ℝ => binetDiff c ((τ : ℂ) * Complex.I)) := by
      rw [contDiff_iff_contDiffAt]; intro τ
      have hat := (hcd_C.restrict_scalars ℝ).contDiffAt (hopen.mem_nhds (by simp : ((τ : ℂ) * Complex.I).re < 1))
      exact (hat.comp τ (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffAt).of_le le_top
    refine ⟨hcd_R, fun τ => ?_⟩
    have hid := iteratedDeriv_real_imag hopen (hcd_C.differentiableOn (by simp)) j τ (by simp : (Complex.I * (τ : ℂ)).re < 1)
    have hcomm : (fun t : ℝ => binetDiff c ((t : ℂ) * Complex.I)) = fun t : ℝ => binetDiff c (Complex.I * (t : ℂ)) := by
      funext t; rw [mul_comm]
    rw [hcomm, hid, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, mul_comm Complex.I]
    have hre : ((τ : ℂ) * Complex.I).re ≤ 0 := by simp
    calc ‖iteratedDeriv j (binetDiff c) ((τ : ℂ) * Complex.I)‖
        ≤ (j.factorial : ℝ) / (12 * c) := binetDiff_iteratedDeriv_norm_le hc0 hre hj1
      _ ≤ (j.factorial : ℝ) / 12 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
  let M0 : ℝ := Real.exp (1 / 6)
  refine ⟨max M0 (max (M0 * (1 / 12)) (max (M0 * (1 / 12) ^ 2 + M0 * (1 / 6))
      (M0 * (1 / 12) ^ 3 + 3 * M0 * (1 / 12) * (1 / 6) + M0 * (1 / 2)))),
    by positivity, fun c hc => ?_⟩
  have hcd := (hb_exp 1 le_rfl (by norm_num) hc).1
  have hb0 : ∀ t : ℝ, ‖Complex.exp (binetDiff c ((t : ℂ) * Complex.I))‖ ≤ M0 := fun t => by
    rw [Complex.norm_exp]
    have hbd := (binetDiff_norm_le_left (by linarith) (by simp : ((t : ℂ) * Complex.I).re ≤ 0)).trans
      (div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith : (6 : ℝ) ≤ 6 * c))
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hbd)
  refine ⟨hcd.cexp, cexp_deriv3_bdd (Real.exp_pos _).le (by norm_num) (by norm_num) (by norm_num) hcd hb0
    (fun t => by rw [← iteratedDeriv_one]; exact ((hb_exp 1 le_rfl (by norm_num) hc).2 t).trans_eq (by norm_num))
    (fun t => ((hb_exp 2 (by norm_num) (by norm_num) hc).2 t).trans_eq (by norm_num))
    (fun t => ((hb_exp 3 (by norm_num) le_rfl hc).2 t).trans_eq (by norm_num))⟩

private lemma right_cauchy_bdd {F : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re})
    (hbd : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖F z‖ ≤ M) :
    ContDiff ℝ 3 (fun τ : ℝ => F (1 - (τ : ℂ) * Complex.I)) ∧
      ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun τ : ℝ => F (1 - (τ : ℂ) * Complex.I)) τ‖ ≤ 48 * M := by
  have hopen : IsOpen {z : ℂ | (0 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF_cd : ContDiffOn ℂ ∞ F {z : ℂ | 0 < z.re} := (hF.contDiffOn hopen).of_le le_top
  have hcd : ContDiff ℝ 3 (fun τ : ℝ => F (1 - (τ : ℂ) * Complex.I)) := by
    rw [contDiff_iff_contDiffAt]; intro τ
    have hm : (1 - (τ : ℂ) * Complex.I) ∈ {z : ℂ | 0 < z.re} := by simp
    have hat := (hF_cd.restrict_scalars ℝ).contDiffAt (hopen.mem_nhds hm)
    have hlin : ContDiff ℝ ⊤ (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I) :=
      contDiff_const.sub (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact (hat.of_le (by simp : (3 : WithTop ℕ∞) ≤ ∞)).comp τ (hlin.contDiffAt.of_le (by simp))
  refine ⟨hcd, fun j hj τ => ?_⟩
  have hid_aux : ∀ (k : ℕ) (τ : ℝ), iteratedDeriv k (fun t : ℝ => F (1 + (-Complex.I) * (t : ℂ))) τ =
      (-Complex.I) ^ k * iteratedDeriv k F (1 + (-Complex.I) * (τ : ℂ)) := by
    intro k
    induction k with
    | zero => intro τ; simp
    | succ m ih =>
      intro τ
      have hf : iteratedDeriv m (fun t : ℝ => F (1 + (-Complex.I) * (t : ℂ))) =
          fun t : ℝ => (-Complex.I) ^ m * iteratedDeriv m F (1 + (-Complex.I) * (t : ℂ)) := funext ih
      rw [iteratedDeriv_succ, hf]
      have hm : (1 : ℂ) + (-Complex.I) * (τ : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
      have hcd_m : ContDiffOn ℂ ∞ (iteratedDeriv m F) {z : ℂ | 0 < z.re} :=
        FctSym.contDiffOn_iteratedDeriv_gen hopen hF_cd m
      have hda := ((hcd_m.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hm)).hasDerivAt
      have hdl : HasDerivAt (fun t : ℝ => (1 : ℂ) + (-Complex.I) * (t : ℂ)) (-Complex.I) τ :=
        ((hasDerivAt_const τ (1 : ℂ)).add ((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul (-Complex.I))).congr_deriv
          (by simp)
      have hd := (hda.scomp τ hdl).const_mul ((-Complex.I) ^ m)
      rw [show (fun t : ℝ => (-Complex.I) ^ m * iteratedDeriv m F (1 + (-Complex.I) * (t : ℂ))) =
          fun y : ℝ => (-Complex.I) ^ m * (iteratedDeriv m F ∘ fun t : ℝ => (1 : ℂ) + (-Complex.I) * (t : ℂ)) y from rfl]
      rw [hd.deriv, iteratedDeriv_succ, smul_eq_mul, pow_succ]; ring
  have hlin : (fun t : ℝ => F (1 - (t : ℂ) * Complex.I)) = fun t : ℝ => F (1 + (-Complex.I) * (t : ℂ)) := by
    funext t; congr 1; ring
  have hid : iteratedDeriv j (fun t : ℝ => F (1 - (t : ℂ) * Complex.I)) τ =
      (-Complex.I) ^ j * iteratedDeriv j F (1 - (τ : ℂ) * Complex.I) := by
    rw [hlin, hid_aux j τ]; congr 2; ring
  rw [hid, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  have hsub : Metric.closedBall (1 - (τ : ℂ) * Complex.I) (1 / 2) ⊆ {z : ℂ | 0 < z.re} := fun z hz => by
    have h1 : |z.re - 1| ≤ 1 / 2 := by
      have := Complex.abs_re_le_norm (z - (1 - (τ : ℂ) * Complex.I))
      have h2 : ‖z - (1 - (τ : ℂ) * Complex.I)‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero] at this
      linarith
    show (0 : ℝ) < z.re; linarith [(abs_le.mp h1).1]
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 1 - (τ : ℂ) * Complex.I)
    (R := 1 / 2) (C := M) j (by norm_num) (hF.diffContOnCl_ball hsub) fun z hz => by
    have h1 : |z.re - 1| ≤ 1 / 2 := by
      have := Complex.abs_re_le_norm (z - (1 - (τ : ℂ) * Complex.I))
      have h2 : ‖z - (1 - (τ : ℂ) * Complex.I)‖ = 1 / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero] at this
      linarith
    exact hbd z (by linarith [(abs_le.mp h1).1])
  refine hcauchy.trans ?_
  have hjf : (j.factorial : ℝ) ≤ 6 := by interval_cases j <;> norm_num
  have h2j : ((1 / 2 : ℝ) ^ j)⁻¹ ≤ 8 := by
    rw [← inv_pow, inv_div, div_one]; calc (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
      _ = 8 := by norm_num
  calc (j.factorial : ℝ) * M / (1 / 2 : ℝ) ^ j = (j.factorial : ℝ) * ((1 / 2 : ℝ) ^ j)⁻¹ * M := by ring
    _ ≤ 6 * 8 * M := by gcongr
    _ = 48 * M := by ring

private lemma uctPhi_rhp_bounds :
    ∃ c₁ : ℝ, 64 ≤ c₁ ∧ ∀ {c : ℝ}, c₁ ≤ c →
      (1 / 2 : ℝ) ≤ ‖uctPhi c 0 1‖ ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖uctPhi c 0 z‖ ≤ 3 := by
  obtain ⟨Cφ, hCφ0, hφ⟩ := uct_airy_trans_phi 0
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, 64 ≤ c₁ ∧ Cφ * c₁ ^ (-(2 / 3 : ℝ)) ≤ 1 / 2 := by
    obtain ⟨c₂, -, hc₂⟩ := exists_rpow_neg_le (p := (2 / 3 : ℝ)) (by norm_num) (ε := 1 / (2 * (Cφ + 1))) (by positivity)
    refine ⟨max 64 c₂, le_max_left _ _, ?_⟩
    have h1 := hc₂ (max 64 c₂) (le_max_right _ _)
    calc Cφ * (max 64 c₂) ^ (-(2 / 3 : ℝ)) ≤ Cφ * (1 / (2 * (Cφ + 1))) := mul_le_mul_of_nonneg_left h1 hCφ0
      _ ≤ 1 / 2 := by rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨c₁, hc₁.1, fun {c} hc => ?_⟩
  have hc64 : 64 ≤ c := hc₁.1.trans hc
  have hc0 : 0 < c := by linarith
  have hc₁0 : 0 < c₁ := by linarith [hc₁.1]
  have hcr : c ^ (-(2 / 3 : ℝ)) ≤ c₁ ^ (-(2 / 3 : ℝ)) := Real.rpow_le_rpow_of_nonpos hc₁0 hc (by norm_num)
  have h2c : 2 * c ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 := by
    have h1 : c ^ (-(1 / 3 : ℝ)) ≤ 64 ^ (-(1 / 3 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) hc64 (by norm_num)
    have h64 : (64 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / 4 := by
      rw [show (64 : ℝ) = 4 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  refine ⟨?_, fun z hz => ?_⟩
  · have hbd := hφ c 0 hc0 le_rfl zero_le_one 1 (by norm_num) (by simpa using h2c.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
    simp only [iteratedDerivWithin_zero, Nat.cast_zero, add_zero, norm_one, Real.one_rpow, mul_one] at hbd
    have hsub : ‖uctPhi c 0 1 - 1‖ ≤ 1 / 2 :=
      hbd.trans ((mul_le_mul_of_nonneg_left hcr hCφ0).trans hc₁.2)
    have htri : ‖(1 : ℂ)‖ - ‖uctPhi c 0 1‖ ≤ ‖(1 : ℂ) - uctPhi c 0 1‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev] at htri
    simp only [norm_one] at htri
    linarith
  · have hz_pos : 0 ≤ z.re := by linarith
    have hzn : 2 * c ^ (-(1 / 3 : ℝ)) ≤ ‖z‖ := h2c.trans (hz.trans (Complex.re_le_norm z))
    have hbd := hφ c 0 hc0 le_rfl zero_le_one z hz_pos hzn
    simp only [iteratedDerivWithin_zero, Nat.cast_zero, add_zero] at hbd
    have hzn2 : ‖z‖ ^ (-(2 : ℝ)) ≤ 4 := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z), Real.rpow_natCast]
      have : (1 / 4 : ℝ) ≤ ‖z‖ ^ 2 := by have : 1 / 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z); nlinarith
      exact (inv_anti₀ (by norm_num) this).trans_eq (by norm_num)
    have h1 := calc ‖uctPhi c 0 z - 1‖
        ≤ Cφ * c ^ (-(2 / 3 : ℝ)) * ‖z‖ ^ (-(2 : ℝ)) := hbd
      _ ≤ (1 / 2) * 4 := mul_le_mul ((mul_le_mul_of_nonneg_left hcr hCφ0).trans hc₁.2) hzn2 (by positivity) (by norm_num)
      _ = 2 := by norm_num
    calc ‖uctPhi c 0 z‖ = ‖1 + (uctPhi c 0 z - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖uctPhi c 0 z - 1‖ := norm_add_le _ _
      _ ≤ 1 + 2 := by simp; linarith
      _ = 3 := by norm_num

private lemma phiQuot_bdd :
    ∃ c₁ M : ℝ, 64 ≤ c₁ ∧ 0 ≤ M ∧ ∀ {c : ℝ}, c₁ ≤ c →
      ContDiff ℝ 3 (fun τ : ℝ => uctPhi c 0 (1 - (τ : ℂ) * Complex.I) / uctPhi c 0 1) ∧
      ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (fun τ : ℝ => uctPhi c 0 (1 - (τ : ℂ) * Complex.I) / uctPhi c 0 1) τ‖ ≤ M := by
  obtain ⟨c₁, hc₁64, hphi⟩ := uctPhi_rhp_bounds
  refine ⟨c₁, 48 * 6, hc₁64, by norm_num, fun {c} hc => ?_⟩
  have hc0 : 0 < c := by linarith
  have h1 : (1 / 2 : ℝ) ≤ ‖uctPhi c 0 1‖ := (hphi hc).1
  have hs0 : 0 < seedScale c := mul_pos ceCs_pos (Real.rpow_pos_of_pos hc0 _)
  have hdiff_phi : DifferentiableOn ℂ (fun z : ℂ => uctPhi c 0 z / uctPhi c 0 1) {z : ℂ | 0 < z.re} := by
    have heq : EqOn (fun z : ℂ => uctPhi c 0 z / uctPhi c 0 1)
        (fun z : ℂ => (((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * z ^ (5 / 2 : ℂ) *
          seedT 0 ((seedScale c : ℂ) * z)) / uctPhi c 0 1) {z : ℂ | 0 < z.re} := fun z _ => by
      dsimp only; rw [uctPhi_eq_seedT c 0 z]
    refine DifferentiableOn.congr (fun z hz => ?_) heq
    have hzre : 0 < z.re := hz
    have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ (5 / 2 : ℂ)) z :=
      differentiableAt_id.cpow_const (Or.inl hzre)
    have hre : 0 < ((seedScale c : ℂ) * z).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hs0 hzre
    have hT : DifferentiableAt ℂ (fun w : ℂ => seedT 0 ((seedScale c : ℂ) * w)) z :=
      ((seedT_differentiableOn 0).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)).comp z
        (differentiableAt_id.const_mul _)
    exact (((hpow.const_mul _).mul hT).div_const _).differentiableWithinAt
  refine right_cauchy_bdd (by norm_num) hdiff_phi fun z hz => ?_
  rw [norm_div]
  calc ‖uctPhi c 0 z‖ / ‖uctPhi c 0 1‖
      ≤ 3 / (1 / 2) := div_le_div₀ (by positivity) ((hphi hc).2 z hz) (by positivity) h1
    _ = 6 := by norm_num

private lemma ctTg1_right_bdd :
    ∃ c₁ M : ℝ, 64 ≤ c₁ ∧ 0 ≤ M ∧ ∀ {c : ℝ}, c₁ ≤ c →
      ContDiff ℝ 3 (fun τ : ℝ => (1 - (τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ) *
        (ctTg1 ((seedScale c : ℂ) * (1 - (τ : ℂ) * Complex.I)) / seedT 0 (seedScale c : ℂ))) ∧
      ∀ j ≤ 3, ∀ τ : ℝ,
        ‖iteratedDeriv j (fun τ : ℝ => (1 - (τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ) *
          (ctTg1 ((seedScale c : ℂ) * (1 - (τ : ℂ) * Complex.I)) / seedT 0 (seedScale c : ℂ))) τ‖ ≤
          M * c ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨c₁, hc₁64, hphi⟩ := uctPhi_rhp_bounds
  obtain ⟨CG, hCG0, hG⟩ := uctG1Ext_iteratedDeriv_bound 0
  refine ⟨c₁, 48 * (8 * CG / |uctCAi|), hc₁64, by positivity, fun {c} hc => ?_⟩
  have hc64 : 64 ≤ c := hc₁64.trans hc
  have hc0 : 0 < c := by linarith
  have h1 : (1 / 2 : ℝ) ≤ ‖uctPhi c 0 1‖ := (hphi hc).1
  rw [uctPhi_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (Real.rpow_pos_of_pos hc0 (5 / 6 : ℝ))] at h1
  have hCAi : 0 < |uctCAi| := abs_pos.mpr uctCAi_ne
  have hT_pos : 0 < ‖seedT 0 (seedScale c : ℂ)‖ := by
    by_contra hle
    push Not at hle
    have h0 : ‖seedT 0 (seedScale c : ℂ)‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0, mul_zero] at h1
    linarith
  have hT_inv : ‖seedT 0 (seedScale c : ℂ)‖⁻¹ ≤ 2 * c ^ (5 / 6 : ℝ) / |uctCAi| := by
    have hmul : (1 / 2 : ℝ) * ‖seedT 0 (seedScale c : ℂ)‖⁻¹ ≤
        c ^ (5 / 6 : ℝ) / |uctCAi| := by
      calc (1 / 2 : ℝ) * ‖seedT 0 (seedScale c : ℂ)‖⁻¹
          ≤ (c ^ (5 / 6 : ℝ) / |uctCAi| * ‖seedT 0 (seedScale c : ℂ)‖) * ‖seedT 0 (seedScale c : ℂ)‖⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (norm_nonneg _))
        _ = c ^ (5 / 6 : ℝ) / |uctCAi| := by rw [mul_assoc, mul_inv_cancel₀ hT_pos.ne', mul_one]
    calc ‖seedT 0 (seedScale c : ℂ)‖⁻¹ = 2 * ((1 / 2 : ℝ) * ‖seedT 0 (seedScale c : ℂ)‖⁻¹) := by ring
      _ ≤ 2 * (c ^ (5 / 6 : ℝ) / |uctCAi|) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 * c ^ (5 / 6 : ℝ) / |uctCAi| := by ring
  have hs0 : 0 < seedScale c := mul_pos ceCs_pos (Real.rpow_pos_of_pos hc0 _)
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => z ^ (5 / 2 : ℂ) *
      (ctTg1 ((seedScale c : ℂ) * z) / seedT 0 (seedScale c : ℂ))) {z : ℂ | 0 < z.re} := by
    have heq : EqOn (fun z : ℂ => z ^ (5 / 2 : ℂ) *
          (ctTg1 ((seedScale c : ℂ) * z) / seedT 0 (seedScale c : ℂ)))
        (fun z : ℂ => z ^ (5 / 2 : ℂ) *
          (uctG1Ext ((seedScale c : ℂ) * z) / seedT 0 (seedScale c : ℂ))) {z : ℂ | 0 < z.re} := fun z hz => by
      have hre : 0 ≤ ((seedScale c : ℂ) * z).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact (mul_pos hs0 hz).le
      dsimp only [ctTg1]; rw [uctG1Ext_eq hre]
    refine DifferentiableOn.congr (fun z hz => ?_) heq
    have hzre : 0 < z.re := hz
    have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ (5 / 2 : ℂ)) z :=
      differentiableAt_id.cpow_const (Or.inl hzre)
    have hre : 0 < ((seedScale c : ℂ) * z).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hs0 hzre
    have hG1 : DifferentiableAt ℂ (fun w : ℂ => uctG1Ext ((seedScale c : ℂ) * w)) z :=
      (differentiableOn_uctG1Ext.differentiableAt
        (Complex.isOpen_slitPlane.mem_nhds (Or.inl hre))).comp z (differentiableAt_id.const_mul _)
    exact (hpow.mul (hG1.div_const _)).differentiableWithinAt
  have hM : 0 ≤ (8 * CG / |uctCAi|) * c ^ (-(2 / 3 : ℝ)) := by positivity
  have hcauchy := right_cauchy_bdd hM hdiff fun z hz => by
    have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; linarith
    have hz_norm : 1 / 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
    have hc4 : 4 ≤ c ^ (1 / 3 : ℝ) := by
      calc (4 : ℝ) = (64 : ℝ) ^ (1 / 3 : ℝ) := by
            rw [show (64 : ℝ) = 4 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hc64 (by norm_num)
    have hs4 : 4 ≤ seedScale c := by
      unfold seedScale
      nlinarith [ceCs_gt_one]
    have hsz_re : 0 ≤ ((seedScale c : ℂ) * z).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg hs0.le (by linarith)
    have hsz_norm : 2 ≤ ‖(seedScale c : ℂ) * z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      nlinarith
    have hGb := hG _ hsz_re hsz_norm
    simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero] at hGb
    have hct : ‖ctTg1 ((seedScale c : ℂ) * z)‖ ≤ CG * (seedScale c * ‖z‖) ^ (-(9 / 2 : ℝ)) := by
      unfold ctTg1; rw [uctG1Ext_eq hsz_re]
      refine hGb.trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have hs_pow : (seedScale c) ^ (-(9 / 2 : ℝ)) ≤ c ^ (-(3 / 2 : ℝ)) := by
      unfold seedScale
      rw [Real.mul_rpow ceCs_pos.le (Real.rpow_nonneg hc0.le _), ← Real.rpow_mul hc0.le]
      have hce1 : ceCs ^ (-(9 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ceCs_gt_one.le (by norm_num)
      calc ceCs ^ (-(9 / 2 : ℝ)) * c ^ ((1 / 3 : ℝ) * -(9 / 2 : ℝ))
          ≤ 1 * c ^ (-(3 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right hce1 (Real.rpow_nonneg hc0.le _) |>.trans_eq ?_
            norm_num
        _ = c ^ (-(3 / 2 : ℝ)) := one_mul _
    have hz_m2 : ‖z‖ ^ (-(2 : ℝ)) ≤ 4 := by
      rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z), Real.rpow_natCast]
      have : (1 / 4 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
      exact (inv_anti₀ (by norm_num) this).trans_eq (by norm_num)
    have hprod : ‖z ^ (5 / 2 : ℂ)‖ * ‖ctTg1 ((seedScale c : ℂ) * z)‖ ≤ 4 * CG * c ^ (-(3 / 2 : ℝ)) := by
      rw [norm_cpow_five_half hz0]
      calc ‖z‖ ^ (5 / 2 : ℝ) * ‖ctTg1 ((seedScale c : ℂ) * z)‖
          ≤ ‖z‖ ^ (5 / 2 : ℝ) * (CG * (seedScale c * ‖z‖) ^ (-(9 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hct (by positivity)
        _ = CG * (seedScale c) ^ (-(9 / 2 : ℝ)) * (‖z‖ ^ (5 / 2 : ℝ) * ‖z‖ ^ (-(9 / 2 : ℝ))) := by
            rw [Real.mul_rpow hs0.le (norm_nonneg z)]; ring
        _ = CG * (seedScale c) ^ (-(9 / 2 : ℝ)) * ‖z‖ ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_add (norm_pos_iff.mpr hz0)]; norm_num
        _ ≤ CG * c ^ (-(3 / 2 : ℝ)) * 4 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hs_pow hCG0) hz_m2 (by positivity) (by positivity)
        _ = 4 * CG * c ^ (-(3 / 2 : ℝ)) := by ring
    rw [norm_mul, norm_div]
    calc ‖z ^ (5 / 2 : ℂ)‖ * (‖ctTg1 ((seedScale c : ℂ) * z)‖ / ‖seedT 0 (seedScale c : ℂ)‖)
        = (‖z ^ (5 / 2 : ℂ)‖ * ‖ctTg1 ((seedScale c : ℂ) * z)‖) * ‖seedT 0 (seedScale c : ℂ)‖⁻¹ := by ring
      _ ≤ (4 * CG * c ^ (-(3 / 2 : ℝ))) * (2 * c ^ (5 / 6 : ℝ) / |uctCAi|) :=
          mul_le_mul hprod hT_inv (by positivity) (by positivity)
      _ = (8 * CG / |uctCAi|) * (c ^ (-(3 / 2 : ℝ)) * c ^ (5 / 6 : ℝ)) := by ring
      _ = (8 * CG / |uctCAi|) * c ^ (-(2 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num
  refine ⟨hcauchy.1, fun j hj τ => ?_⟩
  refine (hcauchy.2 j hj τ).trans_eq ?_; ring

lemma wg1AmpA_cuspAmplitude :
    ∃ c₁ C_A : ℝ, 64 ≤ c₁ ∧ 0 ≤ C_A ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₁ ≤ c →
      CuspAmplitude (Real.pi / 8) C_A (wg1AmpA ε c) := by
  obtain ⟨CAstar, hCA0, hAstar⟩ := uctAstar_cuspAmplitude
  obtain ⟨Mt, hMt0, htheta⟩ := outerTheta_exp_bdd
  obtain ⟨Mb, hMb0, hbinet⟩ := binet_exp_bdd
  obtain ⟨cp, Mp, hcp64, hMp0, hphiq⟩ := phiQuot_bdd
  refine ⟨cp, 8 * (8 * (8 * CAstar * Mt) * Mb) * Mp, hcp64, by positivity,
    fun {ε c} hε hc => ?_⟩
  have hc1 : 1 ≤ c := le_trans (by linarith) hc
  have hcd_t := htheta hε
  have hcb_c := hbinet c hc1
  have hcp_c := hphiq hc
  have h1 := cuspAmplitude_mul_bdd hCA0 hMt0 hAstar hcd_t.1 hcd_t.2
  have h2 := cuspAmplitude_mul_bdd (by positivity) hMb0 h1 hcb_c.1 hcb_c.2
  have h3 := cuspAmplitude_mul_bdd (by positivity) hMp0 h2 hcp_c.1 hcp_c.2
  have heq : (fun τ : ℝ => (uctAstar τ : ℂ) * Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
      Complex.exp (binetDiff c ((τ : ℂ) * Complex.I)) *
      (uctPhi c 0 (1 - (τ : ℂ) * Complex.I) / uctPhi c 0 1)) = wg1AmpA ε c := by
    funext τ; unfold wg1AmpA uctMc; ring
  rwa [heq] at h3

lemma wg1AmpB_cuspAmplitude :
    ∃ c₁ C_B : ℝ, 64 ≤ c₁ ∧ 0 ≤ C_B ∧ ∀ {ε c : ℝ}, (ε = 1 ∨ ε = -1) → c₁ ≤ c →
      CuspAmplitude (Real.pi / 8) (C_B * c ^ (-(2 / 3 : ℝ))) (wg1AmpB ε c) := by
  obtain ⟨CAstar, hCA0, hAstar⟩ := uctAstar_cuspAmplitude
  obtain ⟨Mt, hMt0, htheta⟩ := outerTheta_exp_bdd
  obtain ⟨Mb, hMb0, hbinet⟩ := binet_exp_bdd
  obtain ⟨cg, Mg, hcg64, hMg0, hg1r⟩ := ctTg1_right_bdd
  refine ⟨cg, 8 * (8 * (8 * CAstar * Mt) * Mb) * Mg, hcg64, by positivity,
    fun {ε c} hε hc => ?_⟩
  have hc1 : 1 ≤ c := le_trans (by linarith) hc
  have hcd_t := htheta hε
  have hcb_c := hbinet c hc1
  have hcg_c := hg1r hc
  have h1 := cuspAmplitude_mul_bdd hCA0 hMt0 hAstar hcd_t.1 hcd_t.2
  have h2 := cuspAmplitude_mul_bdd (by positivity) hMb0 h1 hcb_c.1 hcb_c.2
  have h3 := cuspAmplitude_mul_bdd (by positivity) (by positivity) h2 hcg_c.1 hcg_c.2
  have heq : (fun τ : ℝ => (uctAstar τ : ℂ) * Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) *
      Complex.exp (binetDiff c ((τ : ℂ) * Complex.I)) *
      ((1 - (τ : ℂ) * Complex.I) ^ (5 / 2 : ℂ) *
        (ctTg1 ((seedScale c : ℂ) * (1 - (τ : ℂ) * Complex.I)) / seedT 0 (seedScale c : ℂ)))) = wg1AmpB ε c := by
    funext τ; unfold wg1AmpB; ring
  have hmul : 8 * (8 * (8 * CAstar * Mt) * Mb) * (Mg * c ^ (-(2 / 3 : ℝ))) =
      (8 * (8 * (8 * CAstar * Mt) * Mb) * Mg) * c ^ (-(2 / 3 : ℝ)) := by ring
  rw [heq, hmul] at h3
  exact h3

lemma wg1PartA_normDensity {ε c ξ : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hξ : 0 < ξ) :
    normDensity (wg1PartA ε c) c ξ = (cuspEdgeJ c (Real.log (Real.pi ^ 2 * ξ)) (wg1AmpA ε c) wg1YA).re := by
  unfold normDensity cuspEdgeJ
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        wg1AmpA ε c τ * wg1YA (c ^ (1 / 3 : ℝ) * τ) := funext (wg1PartA_edge_eq hε hc hξ)
  rw [hpt, Complex.re_ofReal_mul]

lemma wg1PartB_normDensity {ε c ξ : ℝ} (hε : ε = 1 ∨ ε = -1) (hc : 0 < c) (hξ : 0 < ξ) :
    normDensity (wg1PartB ε c) c ξ = (cuspEdgeJ c (Real.log (Real.pi ^ 2 * ξ)) (wg1AmpB ε c) wg1YB).re := by
  unfold normDensity cuspEdgeJ
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartB ε c ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        wg1AmpB ε c τ * wg1YB (c ^ (1 / 3 : ℝ) * τ) := funext (wg1PartB_edge_eq hε hc hξ)
  rw [hpt, Complex.re_ofReal_mul]

end FormalResearch.SignUncertainty
