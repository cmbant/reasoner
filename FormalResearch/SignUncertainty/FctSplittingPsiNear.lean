/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj
public import FormalResearch.SignUncertainty.FctSplittingCont
public import FormalResearch.SignUncertainty.FctSplittingLeftC2
public import FormalResearch.SignUncertainty.FctWarpAdmiss

/-!
# Near-corner left-edge graded bounds for `Ψ_c` and `Φ_c` (`fct:splitting` (3))

Paper I (`constant_terms_five.tex`), `fct:splitting` (3), `(fct:Psi-edge)` (`0 < τ ≤ 3/2`):
* `inv_edgeS_ej`: `τ ↦ (edgeS τ)⁻¹ = (iτ)^{5/2}` lies in `EJ · (5/2) 0 0 16`.
* `fctPhiC_near_ejOn`: along `(0, 3/2)`, `A_ε(iτ)` is in `EJOn (Ioo 0 (3/2)) · (-(1/2)) 0 0`,
  `Ψ_c(iτ)` is in `EJOn (Ioo 0 (3/2)) · (1/2) 0 0` (from `fctPsi_near_zero` and the ODE
  `fctPsi_hasDerivAt_pos`), and multiplying `c Ψ_c` by `(D_{τ₁}(iτ) · ctHG(iτ))⁻¹` yields
  `Φ_c(iτ)` in `EJOn (Ioo 0 (3/2)) · 3 0 0`.

Class: proved from `CompData` + `D_{τ₁}` hypotheses (`fctPhiC_near_ejOn`).
-/

@[expose] public section

open Set Filter Topology Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma inv_edgeS_ej : EJ (fun τ : ℝ => (edgeS τ)⁻¹) (5 / 2) 0 0 16 := by
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hz : ∀ τ ∈ {τ : ℝ | τ ≠ 0}, (0 : ℂ) + Complex.I * (τ : ℂ) ∈ Complex.slitPlane :=
    fun τ hτ => slit_I hτ
  have heq : (fun τ : ℝ => (edgeS τ)⁻¹) =
      fun τ : ℝ => ((0 : ℂ) + Complex.I * (τ : ℂ)) ^ (((5 / 2 : ℝ)) : ℂ) := by
    funext τ
    unfold edgeS
    rw [show (((-(5 / 2) : ℝ)) : ℂ) = -(((5 / 2 : ℝ)) : ℂ) by push_cast; ring, Complex.cpow_neg]
    simp
  rw [heq]
  refine ⟨by norm_num, cpow_line_contDiffOn _ _ _ hz, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · have h2 := ejW_ge_rpow (a := 5 / 2) (N := 0) 0 hτ
    rw [norm_cpow_line_I hτ]
    simp only [Nat.cast_zero, sub_zero] at h2
    have hp := Real.rpow_pos_of_pos (abs_pos.mpr hτ) (5 / 2 : ℝ)
    nlinarith
  · have hd := (cpow_line_deriv (0 : ℂ) Complex.I (((5 / 2 : ℝ)) : ℂ) hS hz hτ).1
    have h2 := ejW_ge_rpow (a := 5 / 2) (N := 0) 1 hτ
    have e : (((5 / 2 : ℝ) : ℂ) - 1) = (((3 / 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hd, e, norm_mul, norm_mul, norm_cpow_line_I hτ]
    have hn : ‖(((5 / 2 : ℝ)) : ℂ)‖ = 5 / 2 := by simp
    rw [hn, Complex.norm_I, mul_one]
    have e2 : (5 / 2 : ℝ) - ((1 : ℕ) : ℝ) = 3 / 2 := by norm_num
    rw [e2] at h2
    have hp := Real.rpow_pos_of_pos (abs_pos.mpr hτ) (3 / 2 : ℝ)
    nlinarith
  · have hd := (cpow_line_deriv (0 : ℂ) Complex.I (((5 / 2 : ℝ)) : ℂ) hS hz hτ).2
    have h2 := ejW_ge_rpow (a := 5 / 2) (N := 0) 2 hτ
    have e : (((5 / 2 : ℝ) : ℂ) - 1 - 1) = (((1 / 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hd, e, norm_mul, norm_mul, norm_mul, norm_cpow_line_I hτ]
    have hn : ‖(((5 / 2 : ℝ)) : ℂ)‖ = 5 / 2 := by simp
    have hn1 : ‖(((5 / 2 : ℝ)) : ℂ) - 1‖ = 3 / 2 := by
      have : (((5 / 2 : ℝ)) : ℂ) - 1 = (((3 / 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [this]; simp
    rw [hn, hn1, norm_pow, Complex.norm_I, one_pow, mul_one]
    have e2 : (5 / 2 : ℝ) - ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
    rw [e2] at h2
    have hp := Real.rpow_pos_of_pos (abs_pos.mpr hτ) (1 / 2 : ℝ)
    nlinarith

private lemma ejOn_of_contDiff {f : ℝ → ℂ} {S : Set ℝ} (hS : S ⊆ Icc (-(3 / 2 : ℝ)) (3 / 2))
    (hf : ContDiff ℝ 2 f) : ∃ M : ℝ, EJOn S f 0 0 0 M := by
  have hc0 : ContinuousOn f (Icc (-(3 / 2 : ℝ)) (3 / 2)) := hf.continuous.continuousOn
  have hd1 : ContDiff ℝ 1 (deriv f) := by
    have h2 : ContDiff ℝ ((1 : ℕ) + 1) f := by simpa [one_add_one_eq_two] using hf
    exact ((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2).2.2
  have hc1 : ContinuousOn (deriv f) (Icc (-(3 / 2 : ℝ)) (3 / 2)) := hd1.continuous.continuousOn
  have hc2 : ContinuousOn (deriv (deriv f)) (Icc (-(3 / 2 : ℝ)) (3 / 2)) :=
    (hd1.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hc0
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  set M : ℝ := max |M0| (max |M1| |M2|)
  have hMnn : 0 ≤ M := by positivity
  refine ⟨M, hMnn, hf.contDiffOn, fun τ hτS hτ => ?_, fun τ hτS hτ => ?_, fun τ hτS hτ => ?_⟩
  · have h1 : (1 : ℝ) ≤ ejW 0 0 0 0 τ := by simpa using ejW_ge (b := 0) (N := 0) 0 hτ
    calc ‖f τ‖ ≤ |M0| := (hM0 τ (hS hτS)).trans (le_abs_self _)
      _ ≤ M := le_max_left _ _
      _ ≤ M * ejW 0 0 0 0 τ := le_mul_of_one_le_right hMnn h1
  · have h1 : (1 : ℝ) ≤ ejW 0 0 0 1 τ := by simpa using ejW_ge (b := 0) (N := 0) 1 hτ
    calc ‖deriv f τ‖ ≤ |M1| := (hM1 τ (hS hτS)).trans (le_abs_self _)
      _ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
      _ ≤ M * ejW 0 0 0 1 τ := le_mul_of_one_le_right hMnn h1
  · have h1 : (1 : ℝ) ≤ ejW 0 0 0 2 τ := by simpa using ejW_ge (b := 0) (N := 0) 2 hτ
    calc ‖deriv (deriv f) τ‖ ≤ |M2| := (hM2 τ (hS hτS)).trans (le_abs_self _)
      _ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
      _ ≤ M * ejW 0 0 0 2 τ := le_mul_of_one_le_right hMnn h1

private lemma ejOn_quad_of_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hgd0 : deriv g 0 = 0) : ∃ M : ℝ, EJOn (Ioo (-(3 / 2 : ℝ)) (3 / 2)) g 2 0 0 M := by
  have hd0 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv g) := by
    have h2 : ContDiff ℝ ((1 : ℕ) + 1) g := by simpa [one_add_one_eq_two] using hg
    exact ((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2).2.2
  have hdd1 : Differentiable ℝ (deriv g) := hd1.differentiable (by norm_num)
  have hc2 : ContinuousOn (deriv (deriv g)) (Icc (-(3 / 2 : ℝ)) (3 / 2)) :=
    (hd1.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  set M : ℝ := |B|
  have hMnn : 0 ≤ M := abs_nonneg _
  have hb1 : ∀ τ ∈ Icc (-(3 / 2 : ℝ)) (3 / 2), ‖deriv g τ‖ ≤ M * |τ| := fun τ hτ => by
    have hm := (convex_Icc (-(3 / 2 : ℝ)) (3 / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => hdd1.differentiableAt)
      (fun t ht => (hB t ht).trans (le_abs_self _))
      (⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Icc (-(3 / 2 : ℝ)) (3 / 2)) hτ
    simpa [hgd0, Real.norm_eq_abs] using hm
  refine ⟨M, hMnn, hg.contDiffOn, fun τ hτS _ => ?_, fun τ hτS _ => ?_, fun τ hτS _ => ?_⟩
  · have hτabs : |τ| < 3 / 2 := abs_lt.mpr ⟨hτS.1, hτS.2⟩
    have hsub : Icc (-|τ|) |τ| ⊆ Icc (-(3 / 2 : ℝ)) (3 / 2) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hm := (convex_Icc (-|τ|) |τ|).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => hd0.differentiableAt)
      (fun t ht => (hb1 t (hsub ht)).trans (mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨ht.1, ht.2⟩) hMnn))
      (⟨by linarith [abs_nonneg τ], abs_nonneg τ⟩ : (0 : ℝ) ∈ Icc (-|τ|) |τ|)
      ⟨neg_abs_le τ, le_abs_self τ⟩
    rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs] at hm
    have hwe : ejW 2 0 0 0 τ = |τ| ^ 2 := by
      unfold ejW; simp
    rw [hwe]
    calc ‖g τ‖ ≤ M * |τ| * |τ| := hm
      _ = M * |τ| ^ 2 := by ring
  · have hτI : τ ∈ Icc (-(3 / 2 : ℝ)) (3 / 2) := ⟨hτS.1.le, hτS.2.le⟩
    have hwe : |τ| ≤ ejW 2 0 0 1 τ := by
      unfold ejW
      simp only [zero_add, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
      have h1 : (1 : ℝ) ≤ 1 + |τ| := by linarith [abs_nonneg τ]
      have h2 : |τ| ^ ((2 : ℝ) - ((1 : ℕ) : ℝ)) = |τ| := by norm_num
      rw [h2, pow_one]
      exact le_mul_of_one_le_right (abs_nonneg τ) h1
    exact (hb1 τ hτI).trans (mul_le_mul_of_nonneg_left hwe hMnn)
  · have hτI : τ ∈ Icc (-(3 / 2 : ℝ)) (3 / 2) := ⟨hτS.1.le, hτS.2.le⟩
    have hwe : (1 : ℝ) ≤ ejW 2 0 0 2 τ := by
      unfold ejW
      simp only [zero_add, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
      have h1 : (1 : ℝ) ≤ (1 + |τ|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg τ])
      have h2 : |τ| ^ ((2 : ℝ) - ((2 : ℕ) : ℝ)) = 1 := by simp
      rw [h2, one_mul]
      exact h1
    calc ‖deriv (deriv g) τ‖ ≤ M := (hB τ hτI).trans (le_abs_self _)
      _ ≤ M * ejW 2 0 0 2 τ := le_mul_of_one_le_right hMnn hwe

private lemma deriv_zero_of_sq_bound {f : ℝ → ℂ} {r C : ℝ} (hr : 0 < r)
    (hdf : DifferentiableAt ℝ f 0) (hf : ∀ t : ℝ, |t| ≤ r → ‖f t‖ ≤ C * |t| ^ 2) :
    f 0 = 0 ∧ deriv f 0 = 0 := by
  have hf0 : f 0 = 0 := norm_le_zero_iff.mp (by simpa using hf 0 (by simpa using hr.le))
  refine ⟨hf0, ?_⟩
  by_contra hne
  have hpos : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr hne
  have htend : Tendsto (fun t : ℝ => ‖((t : ℂ))⁻¹ * (f t - f 0)‖) (𝓝[≠] (0 : ℝ)) (𝓝 ‖deriv f 0‖) := by
    have hs := (hasDerivAt_iff_tendsto_slope.mp hdf.hasDerivAt).norm
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp [slope_def_module, Complex.real_smul]
  have hbd : ∀ᶠ (t : ℝ) in 𝓝[≠] (0 : ℝ), ‖((t : ℂ))⁻¹ * (f t - f 0)‖ ≤ ‖deriv f 0‖ / 2 := by
    set δ : ℝ := min r (‖deriv f 0‖ / (2 * (|C| + 1)))
    have hδ : 0 < δ := lt_min hr (by positivity)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ),
      self_mem_nhdsWithin] with t ht (ht0 : t ≠ 0)
    have htabs : |t| < δ := by simpa [Real.dist_eq] using ht
    have hle1 : ‖f t‖ ≤ C * |t| ^ 2 := hf t (htabs.le.trans (min_le_left _ _))
    rw [hf0, sub_zero, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |t|⁻¹ * ‖f t‖ ≤ |t|⁻¹ * (C * |t| ^ 2) :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = C * |t| := by
          have ha : |t| ≠ 0 := abs_ne_zero.mpr ht0
          field_simp
      _ ≤ |C| * |t| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg t)
      _ ≤ (|C| + 1) * |t| := by nlinarith [abs_nonneg t]
      _ ≤ (|C| + 1) * (‖deriv f 0‖ / (2 * (|C| + 1))) :=
          mul_le_mul_of_nonneg_left (htabs.le.trans (min_le_right _ _)) (by positivity)
      _ = ‖deriv f 0‖ / 2 := by
          have : (|C| + 1 : ℝ) ≠ 0 := by positivity
          field_simp
  have := le_of_tendsto htend hbd
  linarith

private lemma fctWarpA_near_ejOn {K4 ε c L1 α : ℝ} {P : ℝ → ℝ} (hc : 0 < c)
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) P) :
    ∃ M : ℝ, EJOn (Ioo (0 : ℝ) (3 / 2))
      (fun τ : ℝ => fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)) (-(1 / 2)) 0 0 M := by
  set S : Set ℝ := Ioo (-(3 / 2 : ℝ)) (3 / 2)
  set Spos : Set ℝ := Ioo (0 : ℝ) (3 / 2)
  have hSsub : S ⊆ Icc (-(3 / 2 : ℝ)) (3 / 2) := fun _ h => ⟨h.1.le, h.2.le⟩
  have hline : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  have hmemE : ∀ t : ℝ, (t : ℂ) * Complex.I ∈ edgeStrip := fun t => by
    show |((t : ℂ) * Complex.I).re| < 1; simp
  have hG_cd : ContDiff ℝ 2 (fun t : ℝ => stripG ((t : ℂ) * Complex.I)) := by
    rw [← contDiffOn_univ]
    exact (differentiableOn_stripG.contDiffOn isOpen_edgeStrip |>.restrict_scalars ℝ).comp
      hline.contDiffOn fun t _ => hmemE t
  have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hP_cd : ContDiff ℝ 2 (fun t : ℝ => FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)) :=
    (FctSym.contDiff_phiKill_imag ha).of_le (by norm_cast)
  set g : ℝ → ℂ := fun t => stripG ((t : ℂ) * Complex.I) + (L1 : ℂ) *
    FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) ((t : ℂ) * Complex.I)
  have hg_cd : ContDiff ℝ 2 g := hG_cd.add (contDiff_const.mul hP_cd)
  have hg_sq : ∃ r C : ℝ, 0 < r ∧ ∀ t : ℝ, |t| ≤ r → ‖g t‖ ≤ C * |t| ^ 2 := by
    obtain ⟨Cφ, hCφ0, hCφ⟩ := FctPhiKill.phiKill_near_zero
    set a := c ^ (-(1 / 12 : ℝ))
    refine ⟨min (1 / 4) (a / 2), (Real.pi ^ 2 / 12 + 10) + |L1| * ((Nat.choose 15 8 : ℝ) + Cφ) / a ^ 8,
      lt_min (by norm_num) (by positivity), fun t ht => ?_⟩
    have hn : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
    have ht14 : ‖(t : ℂ) * Complex.I‖ ≤ 1 / 4 := by rw [hn]; exact ht.trans (min_le_left _ _)
    have hta2 : ‖(t : ℂ) * Complex.I‖ ≤ a / 2 := by rw [hn]; exact ht.trans (min_le_right _ _)
    have hG1 : ‖stripG ((t : ℂ) * Complex.I)‖ ≤ (Real.pi ^ 2 / 12 + 10) * |t| ^ 2 := by
      have hs := stripG_sub_le ht14
      have ht4 : |t| ^ 4 ≤ |t| ^ 2 := by
        have : |t| ≤ 1 := by linarith [hn ▸ ht14]
        calc |t| ^ 4 = |t| ^ 2 * |t| ^ 2 := by ring
          _ ≤ |t| ^ 2 * 1 := by gcongr; exact pow_le_one₀ (abs_nonneg t) this
          _ = |t| ^ 2 := mul_one _
      have hsq : ‖((Real.pi : ℂ) ^ 2 / 12) * ((t : ℂ) * Complex.I) ^ 2‖ = (Real.pi ^ 2 / 12) * |t| ^ 2 := by
        rw [norm_mul, norm_pow, hn, show ((Real.pi : ℂ) ^ 2 / 12 : ℂ) = ((Real.pi ^ 2 / 12 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hnb := norm_sub_norm_le (stripG ((t : ℂ) * Complex.I)) (((Real.pi : ℂ) ^ 2 / 12) * ((t : ℂ) * Complex.I) ^ 2)
      rw [hsq] at hnb
      rw [hn] at hs
      nlinarith
    have hP1 : ‖FctPhiKill.phiKill a ((t : ℂ) * Complex.I)‖ ≤ ((Nat.choose 15 8 : ℝ) + Cφ) / a ^ 8 * |t| ^ 2 := by
      have hp := hCφ (a := a) (z := (t : ℂ) * Complex.I) ha hta2
      have hx0 : 0 ≤ |t| / a := by positivity
      have hx12 : |t| / a ≤ 1 / 2 := by rw [div_le_iff₀ ha]; linarith [hn ▸ hta2]
      have h9 : (|t| / a) ^ 9 ≤ (|t| / a) ^ 8 := by rw [pow_succ]; nlinarith [pow_nonneg hx0 8]
      have h8 : ‖(((Nat.choose 15 8 : ℕ) : ℝ) : ℂ) * (((t : ℂ) * Complex.I) / a) ^ 8‖ =
          (Nat.choose 15 8 : ℝ) * (|t| / a) ^ 8 := by
        rw [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          Complex.norm_real, Real.norm_of_nonneg ha.le, hn]
      have hnb := norm_sub_norm_le (FctPhiKill.phiKill a ((t : ℂ) * Complex.I))
        ((((Nat.choose 15 8 : ℕ) : ℝ) : ℂ) * (((t : ℂ) * Complex.I) / a) ^ 8)
      rw [h8] at hnb
      rw [hn] at hp
      have ht8 : (|t| / a) ^ 8 ≤ |t| ^ 2 / a ^ 8 := by
        rw [div_pow]; refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : |t| ≤ 1 := by linarith [hn ▸ ht14]
        calc |t| ^ 8 = |t| ^ 2 * |t| ^ 6 := by ring
          _ ≤ |t| ^ 2 * 1 := by gcongr; exact pow_le_one₀ (abs_nonneg t) this
          _ = |t| ^ 2 := mul_one _
      have hCφ9 : Cφ * (|t| / a) ^ 9 ≤ Cφ * (|t| / a) ^ 8 := mul_le_mul_of_nonneg_left h9 hCφ0
      have h12 : ‖FctPhiKill.phiKill a ((t : ℂ) * Complex.I)‖ ≤ ((Nat.choose 15 8 : ℝ) + Cφ) * (|t| / a) ^ 8 := by
        linarith [hp, hnb, hCφ9]
      calc _ ≤ ((Nat.choose 15 8 : ℝ) + Cφ) * (|t| ^ 2 / a ^ 8) :=
            h12.trans (mul_le_mul_of_nonneg_left ht8 (by positivity))
        _ = _ := by ring
    calc ‖g t‖ ≤ ‖stripG ((t : ℂ) * Complex.I)‖ + ‖(L1 : ℂ)‖ * ‖FctPhiKill.phiKill a ((t : ℂ) * Complex.I)‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ (Real.pi ^ 2 / 12 + 10) * |t| ^ 2 + |L1| * (((Nat.choose 15 8 : ℝ) + Cφ) / a ^ 8 * |t| ^ 2) := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add hG1 (mul_le_mul_of_nonneg_left hP1 (abs_nonneg L1))
      _ = _ := by ring
  obtain ⟨r0, C0, hr0, hgsq⟩ := hg_sq
  obtain ⟨hg0, hgd0⟩ := deriv_zero_of_sq_bound hr0 (hg_cd.differentiable (by norm_num) 0) hgsq
  obtain ⟨Mg, hgEJ⟩ := ejOn_quad_of_contDiff hg_cd hg0 hgd0
  obtain ⟨MD, hDEJ⟩ := ejOn_of_contDiff hSsub hEnv.1
  obtain ⟨MZ, hZE⟩ := ejZE ε
  have hHG_EJ : EJ (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) (-(5 / 2)) 10 1 (4 * (4 * MZ * 9) * 9) := by
    have hbase := ((hZE.mul edgeR_EJ).mul edgeS_EJ).cast (a' := -(5 / 2)) (b' := 1) (by norm_num) (by norm_num)
    have hEq : (fun τ : ℝ => ctHG ε ((τ : ℂ) * Complex.I)) =
        fun τ : ℝ => (uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) *
          edgeR τ * edgeS τ := funext fun τ => ctHG_edge ε τ
    rw [hEq]
    exact hbase
  have hmul : EJOn S (fun τ : ℝ => fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I))
      (-(1 / 2)) 10 1 (4 * (4 * Mg * MD) * (4 * (4 * MZ * 9) * 9)) :=
    ((hgEJ.mul hDEJ).mul (hHG_EJ.to_on (S := S))).cast (a' := -(1 / 2)) (b' := 1) (by norm_num) (by norm_num)
  set MA := 4 * (4 * Mg * MD) * (4 * (4 * MZ * 9) * 9)
  have hMA : 0 ≤ MA := hmul.hM
  have hstrip : ∀ (j : ℕ), j ≤ 2 → ∀ τ ∈ Spos, τ ≠ 0 →
      ejW (-(1 / 2)) 10 1 j τ ≤ (5 / 2 : ℝ) ^ 12 * ejW (-(1 / 2)) 0 0 j τ := fun j hj τ hτ _ => by
    unfold ejW
    have hτ0 : 0 < τ := hτ.1
    have hτ3 : τ < 3 / 2 := hτ.2
    have h1τ : 1 + |τ| ≤ 5 / 2 := by rw [abs_of_pos hτ0]; linarith
    have hexp : Real.exp (-(π * 1 * |τ|)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have hpow : (1 + |τ|) ^ (10 + j) ≤ (5 / 2 : ℝ) ^ 12 := by
      calc (1 + |τ|) ^ (10 + j) ≤ (5 / 2 : ℝ) ^ (10 + j) := pow_le_pow_left₀ (by positivity) h1τ _
        _ ≤ (5 / 2 : ℝ) ^ 12 := pow_le_pow_right₀ (by norm_num) (by omega)
    have he0 : 0 ≤ |τ| ^ (-(1 / 2 : ℝ) - (j : ℝ)) := by positivity
    have h10 : 1 ≤ (1 + |τ|) ^ (0 + j) := one_le_pow₀ (by linarith [abs_nonneg τ])
    calc |τ| ^ (-(1 / 2 : ℝ) - (j : ℝ)) * (1 + |τ|) ^ (10 + j) * Real.exp (-(π * 1 * |τ|))
        ≤ |τ| ^ (-(1 / 2 : ℝ) - (j : ℝ)) * (5 / 2 : ℝ) ^ 12 * 1 := by
          gcongr
      _ ≤ (5 / 2 : ℝ) ^ 12 * (|τ| ^ (-(1 / 2 : ℝ) - (j : ℝ)) * (1 + |τ|) ^ (0 + j) * Real.exp (-(π * 0 * |τ|))) := by
          simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
          nlinarith
  refine ⟨(5 / 2 : ℝ) ^ 12 * MA, by positivity, hmul.c2, ?_, ?_, ?_⟩
  · exact fun τ hS hτ => (hmul.b0 τ ⟨by linarith [hS.1], hS.2⟩ hτ).trans (by
      calc MA * ejW (-(1 / 2)) 10 1 0 τ ≤ MA * ((5 / 2 : ℝ) ^ 12 * ejW (-(1 / 2)) 0 0 0 τ) :=
            mul_le_mul_of_nonneg_left (hstrip 0 (by norm_num) τ hS hτ) hMA
        _ = _ := by ring)
  · exact fun τ hS hτ => (hmul.b1 τ ⟨by linarith [hS.1], hS.2⟩ hτ).trans (by
      calc MA * ejW (-(1 / 2)) 10 1 1 τ ≤ MA * ((5 / 2 : ℝ) ^ 12 * ejW (-(1 / 2)) 0 0 1 τ) :=
            mul_le_mul_of_nonneg_left (hstrip 1 (by norm_num) τ hS hτ) hMA
        _ = _ := by ring)
  · exact fun τ hS hτ => (hmul.b2 τ ⟨by linarith [hS.1], hS.2⟩ hτ).trans (by
      calc MA * ejW (-(1 / 2)) 10 1 2 τ ≤ MA * ((5 / 2 : ℝ) ^ 12 * ejW (-(1 / 2)) 0 0 2 τ) :=
            mul_le_mul_of_nonneg_left (hstrip 2 le_rfl τ hS hτ) hMA
        _ = _ := by ring)

private lemma fctPsi_near_ejOn {K4 ε c L1 α : ℝ} {P : ℝ → ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hDconj : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) P) :
    ∃ M : ℝ, EJOn (Ioo (0 : ℝ) (3 / 2))
      (fun τ : ℝ => fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)) (1 / 2) 0 0 M := by
  set Spos : Set ℝ := Ioo (0 : ℝ) (3 / 2)
  have hSpsub : Spos ⊆ Icc (-(3 / 2 : ℝ)) (3 / 2) := fun _ h => ⟨by linarith [h.1], h.2.le⟩
  obtain ⟨MA0, hA_on⟩ := fctWarpA_near_ejOn (K4 := K4) (ε := ε) (L1 := L1) hc hEnv
  set ψ : ℝ → ℂ := fun t => fctPsi K4 ε c L1 α ((t : ℂ) * Complex.I)
  have hPsi_c2 : ContDiffOn ℝ 2 ψ {τ : ℝ | τ ≠ 0} :=
    fctPsi_contDiffOn_left hc hDc hDb hDconj hEnv
  obtain ⟨rψ, Mψ, hrψ, hMψ, hψ_near⟩ := fctPsi_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb
  set r1 : ℝ := min rψ 1
  have hr1pos : 0 < r1 := lt_min hrψ zero_lt_one
  have hPsi_cont_mid : ContinuousOn ψ (Icc r1 (3 / 2)) := by
    refine (fctPsi_continuousOn (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc hDb).comp
      (by fun_prop) fun t ht => ⟨by simp, by simp, fun h => by
        have := congrArg Complex.im h; simp at this; linarith [ht.1, hr1pos]⟩
  obtain ⟨Mmid, hMmid⟩ := isCompact_Icc.exists_bound_of_continuousOn hPsi_cont_mid
  set MP0 : ℝ := max Mψ (|Mmid| / r1 ^ (1 / 2 : ℝ))
  have hMP0nn : 0 ≤ MP0 := le_trans hMψ (le_max_left _ _)
  have hbψ0 : ∀ τ ∈ Spos, ‖ψ τ‖ ≤ MP0 * τ ^ (1 / 2 : ℝ) := fun τ hτ => by
    have hτ0 : 0 < τ := hτ.1
    rcases le_or_gt τ r1 with hle | hgt
    · have hn : ‖(τ : ℂ) * Complex.I‖ = τ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le, Complex.norm_I, mul_one]
      have h1 := hψ_near ((τ : ℂ) * Complex.I) (by simp) (by simp)
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ0.ne') Complex.I_ne_zero)
        (by rw [hn]; exact hle.trans (min_le_left _ _))
      rw [hn] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have h1 := (hMmid τ ⟨hgt.le, hτ.2.le⟩).trans (le_abs_self _)
      have hrp : r1 ^ (1 / 2 : ℝ) ≤ τ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hr1pos.le hgt.le (by norm_num)
      have hrp_pos : 0 < r1 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr1pos _
      calc ‖ψ τ‖ ≤ |Mmid| := h1
        _ = (|Mmid| / r1 ^ (1 / 2 : ℝ)) * r1 ^ (1 / 2 : ℝ) := by field_simp
        _ ≤ MP0 * τ ^ (1 / 2 : ℝ) := mul_le_mul (le_max_right _ _) hrp hrp_pos.le hMP0nn
  have hline : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  have hmemE : ∀ t : ℝ, (t : ℂ) * Complex.I ∈ edgeStrip := fun t => by
    show |((t : ℂ) * Complex.I).re| < 1; simp
  set K0 : ℝ → ℂ := fun t => mellinK0 c ((t : ℂ) * Complex.I) (fctXi1 L1)
  have hK0_cd : ContDiff ℝ 2 K0 := by
    rw [← contDiffOn_univ]
    exact ((differentiableOn_mellinK0 hc (fctXi1 L1)).contDiffOn isOpen_edgeStrip |>.restrict_scalars ℝ).comp
      hline.contDiffOn fun t _ => hmemE t
  have hK0ne : ∀ t : ℝ, K0 t ≠ 0 := fun t => mellinK0_ne_zero c (by simp) _
  set Rk : ℝ → ℂ := fun t => deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1)) ((t : ℂ) * Complex.I) / K0 t
  have hK0_deriv_cd : ContDiff ℝ 2 (fun t : ℝ => deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1)) ((t : ℂ) * Complex.I)) := by
    rw [← contDiffOn_univ]
    have hdhol : DifferentiableOn ℂ (deriv (fun w : ℂ => mellinK0 c w (fctXi1 L1))) edgeStrip :=
      (differentiableOn_mellinK0 hc (fctXi1 L1)).deriv isOpen_edgeStrip
    exact (hdhol.contDiffOn isOpen_edgeStrip |>.restrict_scalars ℝ).comp
      hline.contDiffOn fun t _ => hmemE t
  have hRk_cd : ContDiff ℝ 2 Rk := hK0_deriv_cd.mul (hK0_cd.inv hK0ne)
  have hRk_cont0 : ContinuousOn Rk (Icc (-(3 / 2 : ℝ)) (3 / 2)) := hRk_cd.continuous.continuousOn
  have hRk_d1 : ContDiff ℝ 1 (deriv Rk) := by
    have h2 : ContDiff ℝ ((1 : ℕ) + 1) Rk := by simpa [one_add_one_eq_two] using hRk_cd
    exact ((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2).2.2
  have hRk_cont1 : ContinuousOn (deriv Rk) (Icc (-(3 / 2 : ℝ)) (3 / 2)) := hRk_d1.continuous.continuousOn
  obtain ⟨MR0, hMR0⟩ := isCompact_Icc.exists_bound_of_continuousOn hRk_cont0
  obtain ⟨MR1, hMR1⟩ := isCompact_Icc.exists_bound_of_continuousOn hRk_cont1
  set MR : ℝ := max |MR0| |MR1|
  have hMRnn : 0 ≤ MR := by positivity
  set MP1 : ℝ := MA0 + MR * (3 / 2) * MP0
  set MP2 : ℝ := (5 / 2) * MA0 + MR * (9 / 4) * MP0 + MR * (3 / 2) * MP1
  set MP := max MP0 (max MP1 MP2)
  have hMPnn : 0 ≤ MP := le_trans hMP0nn (le_max_left _ _)
  have hMAnn : 0 ≤ MA0 := hA_on.hM
  have hMP1nn : 0 ≤ MP1 := by positivity
  have hd_psi1 : ∀ τ : ℝ, 0 < τ → deriv ψ τ = Complex.I * (fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) - Rk τ * ψ τ) :=
    fun τ hτ => (fctPsi_hasDerivAt_pos hc hDc hDb hEnv hτ).deriv
  have hbψ1 : ∀ τ ∈ Spos, ‖deriv ψ τ‖ ≤ MP1 * τ ^ (-(1 / 2 : ℝ)) := fun τ hτ => by
    have hτ0 : 0 < τ := hτ.1
    have hτ3 : τ < 3 / 2 := hτ.2
    rw [hd_psi1 τ hτ0, norm_mul, Complex.norm_I, one_mul]
    have hA_b := hA_on.b0 τ hτ hτ0.ne'
    have hAw : ejW (-(1 / 2)) 0 0 0 τ = τ ^ (-(1 / 2 : ℝ)) := by unfold ejW; simp [abs_of_pos hτ0]
    rw [hAw] at hA_b
    have hRk_b : ‖Rk τ‖ ≤ MR := (hMR0 τ (hSpsub hτ)).trans ((le_abs_self _).trans (le_max_left _ _))
    have hpow : τ ^ (1 / 2 : ℝ) ≤ (3 / 2) * τ ^ (-(1 / 2 : ℝ)) := by
      have hsub : τ ^ (1 / 2 : ℝ) = τ * τ ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_one_add' hτ0.le (by norm_num)]
        congr 1; norm_num
      rw [hsub]
      exact mul_le_mul_of_nonneg_right hτ3.le (by positivity)
    calc ‖fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I) - Rk τ * ψ τ‖
        ≤ ‖fctWarpA K4 ε c L1 α ((τ : ℂ) * Complex.I)‖ + ‖Rk τ‖ * ‖ψ τ‖ :=
          (norm_sub_le _ _).trans (by rw [norm_mul])
      _ ≤ MA0 * τ ^ (-(1 / 2 : ℝ)) + MR * (MP0 * ((3 / 2) * τ ^ (-(1 / 2 : ℝ)))) :=
          add_le_add hA_b (mul_le_mul hRk_b ((hbψ0 τ hτ).trans (mul_le_mul_of_nonneg_left hpow hMP0nn))
            (norm_nonneg _) hMRnn)
      _ = _ := by ring
  refine ⟨MP, hMPnn, hPsi_c2, ?_, ?_, ?_⟩
  · intro τ hτ _
    have hτ0 : 0 < τ := hτ.1
    have hw : ejW (1 / 2) 0 0 0 τ = τ ^ (1 / 2 : ℝ) := by unfold ejW; simp [abs_of_pos hτ0]
    rw [hw]
    exact (hbψ0 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro τ hτ _
    have hτ0 : 0 < τ := hτ.1
    have h1 : τ ^ (-(1 / 2 : ℝ)) ≤ ejW (1 / 2) 0 0 1 τ := by
      have htmp := ejW_ge_rpow (a := 1 / 2) (N := 0) 1 hτ0.ne'
      rw [abs_of_pos hτ0, show (1 / 2 : ℝ) - ((1 : ℕ) : ℝ) = -(1 / 2) by norm_num] at htmp
      exact htmp
    exact (hbψ1 τ hτ).trans (calc MP1 * τ ^ (-(1 / 2 : ℝ)) ≤ MP * τ ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
      _ ≤ MP * ejW (1 / 2) 0 0 1 τ := mul_le_mul_of_nonneg_left h1 hMPnn)
  · intro τ hτ _
    have hτ0 : 0 < τ := hτ.1
    have hτ3 : τ < 3 / 2 := hτ.2
    have hev : deriv ψ =ᶠ[𝓝 τ] fun t => Complex.I * (fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I) - Rk t * ψ t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hτ0] with t ht using hd_psi1 t ht
    have hAd : DifferentiableAt ℝ (fun t : ℝ => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)) τ :=
      (hA_on.c2.differentiableOn (by norm_num) τ hτ0.ne').differentiableAt (isOpen_ne.mem_nhds hτ0.ne')
    have hRd : DifferentiableAt ℝ Rk τ := (hRk_cd.differentiable (by norm_num)) τ
    have hpd : DifferentiableAt ℝ ψ τ := (hPsi_c2.differentiableOn (by norm_num) τ hτ0.ne').differentiableAt (isOpen_ne.mem_nhds hτ0.ne')
    have hd2_eq : deriv (deriv ψ) τ = Complex.I * (deriv (fun t : ℝ => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)) τ -
        (deriv Rk τ * ψ τ + Rk τ * deriv ψ τ)) := by
      rw [hev.deriv_eq]
      exact ((hAd.hasDerivAt.sub (hRd.hasDerivAt.mul hpd.hasDerivAt)).const_mul Complex.I).deriv
    rw [hd2_eq, norm_mul, Complex.norm_I, one_mul]
    have hA1 := hA_on.b1 τ hτ hτ0.ne'
    have hAw1 : ejW (-(1 / 2)) 0 0 1 τ = τ ^ (-(3 / 2 : ℝ)) * (1 + τ) := by
      unfold ejW
      rw [abs_of_pos hτ0, show -(1 / 2 : ℝ) - ((1 : ℕ) : ℝ) = -(3 / 2) by norm_num]
      simp
    have hA1' : ‖deriv (fun t : ℝ => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)) τ‖ ≤
        ((5 / 2 : ℝ) * MA0) * τ ^ (-(3 / 2 : ℝ)) := by
      have : ejW (-(1 / 2)) 0 0 1 τ ≤ (5 / 2) * τ ^ (-(3 / 2 : ℝ)) := by
        rw [hAw1]
        nlinarith [show 1 + τ ≤ 5 / 2 by linarith, show (0 : ℝ) ≤ τ ^ (-(3 / 2 : ℝ)) by positivity]
      exact hA1.trans (by calc MA0 * ejW (-(1 / 2)) 0 0 1 τ ≤ MA0 * ((5 / 2) * τ ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left this hMAnn
        _ = _ := by ring)
    have hR0 : ‖Rk τ‖ ≤ MR := (hMR0 τ (hSpsub hτ)).trans ((le_abs_self _).trans (le_max_left _ _))
    have hR1 : ‖deriv Rk τ‖ ≤ MR := (hMR1 τ (hSpsub hτ)).trans ((le_abs_self _).trans (le_max_right _ _))
    have hpow0 : τ ^ (1 / 2 : ℝ) ≤ (9 / 4 : ℝ) * τ ^ (-(3 / 2 : ℝ)) := by
      have hs : τ ^ (1 / 2 : ℝ) = τ ^ (2 : ℝ) * τ ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hτ0]; congr 1; norm_num
      rw [hs, Real.rpow_two]
      nlinarith [show τ ^ 2 ≤ 9 / 4 by nlinarith, show (0 : ℝ) ≤ τ ^ (-(3 / 2 : ℝ)) by positivity]
    have hpow1 : τ ^ (-(1 / 2 : ℝ)) ≤ (3 / 2 : ℝ) * τ ^ (-(3 / 2 : ℝ)) := by
      have hs : τ ^ (-(1 / 2 : ℝ)) = τ * τ ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_one_add' hτ0.le (by norm_num)]
        congr 1; norm_num
      rw [hs]
      exact mul_le_mul_of_nonneg_right hτ3.le (by positivity)
    have h2 : τ ^ (-(3 / 2 : ℝ)) ≤ ejW (1 / 2) 0 0 2 τ := by
      have htmp := ejW_ge_rpow (a := 1 / 2) (N := 0) 2 hτ0.ne'
      rw [abs_of_pos hτ0, show (1 / 2 : ℝ) - ((2 : ℕ) : ℝ) = -(3 / 2) by norm_num] at htmp
      exact htmp
    have hb_all : ‖deriv (fun t : ℝ => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)) τ - (deriv Rk τ * ψ τ + Rk τ * deriv ψ τ)‖ ≤
        MP2 * τ ^ (-(3 / 2 : ℝ)) := by
      calc _ ≤ ‖deriv (fun t : ℝ => fctWarpA K4 ε c L1 α ((t : ℂ) * Complex.I)) τ‖ +
            (‖deriv Rk τ‖ * ‖ψ τ‖ + ‖Rk τ‖ * ‖deriv ψ τ‖) :=
            (norm_sub_le _ _).trans (add_le_add le_rfl
              ((norm_add_le _ _).trans (add_le_add (by rw [norm_mul]) (by rw [norm_mul]))))
        _ ≤ ((5 / 2 : ℝ) * MA0) * τ ^ (-(3 / 2 : ℝ)) +
            (MR * (MP0 * ((9 / 4 : ℝ) * τ ^ (-(3 / 2 : ℝ)))) + MR * (MP1 * ((3 / 2 : ℝ) * τ ^ (-(3 / 2 : ℝ))))) := by
            refine add_le_add hA1' (add_le_add ?_ ?_)
            · exact mul_le_mul hR1 ((hbψ0 τ hτ).trans (mul_le_mul_of_nonneg_left hpow0 hMP0nn)) (norm_nonneg _) hMRnn
            · exact mul_le_mul hR0 ((hbψ1 τ hτ).trans (mul_le_mul_of_nonneg_left hpow1 hMP1nn)) (norm_nonneg _) hMRnn
        _ = MP2 * τ ^ (-(3 / 2 : ℝ)) := by ring
    exact hb_all.trans (calc MP2 * τ ^ (-(3 / 2 : ℝ)) ≤ MP * τ ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
      _ ≤ MP * ejW (1 / 2) 0 0 2 τ := mul_le_mul_of_nonneg_left h2 hMPnn)

/-- **`Φ_c(iτ)` belongs to `EJOn (Ioo 0 (3/2)) · 3 0 0`** (`fct:splitting` (3), `(fct:Psi-edge)`). -/
theorem fctPhiC_near_ejOn {K4 ε c L1 α : ℝ} {P : ℝ → ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hDconj : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    (hEnv : Env2 (fun τ : ℝ => fctDcompAt K4 c α ((τ : ℂ) * Complex.I)) P) :
    ∃ M : ℝ, EJOn (Ioo (0 : ℝ) (3 / 2))
      (fun τ : ℝ => fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I)) 3 0 0 M := by
  set Spos : Set ℝ := Ioo (0 : ℝ) (3 / 2)
  have hSpsub : Spos ⊆ Icc (-(3 / 2 : ℝ)) (3 / 2) := fun _ h => ⟨by linarith [h.1], h.2.le⟩
  obtain ⟨MP, hPsi_ej⟩ := fctPsi_near_ejOn (K4 := K4) (ε := ε) (L1 := L1) hc hDc hDb hDconj hEnv
  have hDinv_cd : ContDiff ℝ 2 (fun τ : ℝ => (fctDcompAt K4 c α ((τ : ℂ) * Complex.I))⁻¹) :=
    hEnv.1.inv fun τ => fctDcompAt_ne_zero _
  obtain ⟨MDinv, hDinv_EJ⟩ := ejOn_of_contDiff hSpsub hDinv_cd
  obtain ⟨CZ, hZ0, hZ_env⟩ := env2_seedZi ε
  obtain ⟨aE, haE0, hE_env⟩ := env2_outerE
  have hZ_cd : ContDiff ℝ 2 (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I)) := by
    have heq : (fun τ : ℝ => uctSeedZ ε ((τ : ℂ) * Complex.I)) = fun τ : ℝ => uctSeedZ ε (0 + Complex.I * (τ : ℂ)) := by
      funext τ; congr 1; ring
    rw [heq]; exact hZ_env.1
  have hE_cd : ContDiff ℝ 2 (fun τ : ℝ => Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) := by
    have heq : (fun τ : ℝ => Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) =
        fun τ : ℝ => Complex.exp (-outerHbar (Complex.I * (τ : ℂ))) := by
      funext τ; rw [mul_comm]
    rw [heq]; exact hE_env.1
  have hZEinv_cd : ContDiff ℝ 2 (fun τ : ℝ => (uctSeedZ ε ((τ : ℂ) * Complex.I) *
      Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)))⁻¹) :=
    (hZ_cd.mul hE_cd).inv fun τ => uctSeedZ_mul_exp_ne_zero ε (by simp) (by simp)
  obtain ⟨MZEinv, hZEinv_EJ⟩ := ejOn_of_contDiff hSpsub hZEinv_cd
  have hRinv_eq : (fun τ : ℝ => (edgeR τ)⁻¹) = fun τ : ℝ => ((1 : ℂ) + (-Complex.I) * (τ : ℂ)) ^ (((5 / 2 : ℝ)) : ℂ) := by
    funext τ; unfold edgeR
    rw [show (((-(5 / 2) : ℝ)) : ℂ) = -(((5 / 2 : ℝ)) : ℂ) by push_cast; ring, Complex.cpow_neg]
    simp
  have hRinv_cd : ContDiff ℝ 2 (fun τ : ℝ => (edgeR τ)⁻¹) := by
    rw [hRinv_eq, ← contDiffOn_univ]
    exact cpow_line_contDiffOn _ _ _ (fun τ _ => slit_one_sub τ)
  obtain ⟨MRinv, hRinv_EJ⟩ := ejOn_of_contDiff hSpsub hRinv_cd
  have hSinv_EJ : EJOn Spos (fun τ : ℝ => (edgeS τ)⁻¹) (5 / 2) 0 0 16 := inv_edgeS_ej.to_on
  have hPhi_eq : (fun τ : ℝ => fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => (c : ℂ) * (fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) *
        ((fctDcompAt K4 c α ((τ : ℂ) * Complex.I))⁻¹ *
          ((uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I)))⁻¹ *
            ((edgeR τ)⁻¹ * (edgeS τ)⁻¹)))) := by
    funext τ
    have hH : ctHG ε ((τ : ℂ) * Complex.I) =
        (uctSeedZ ε ((τ : ℂ) * Complex.I) * Complex.exp (-outerHbar ((τ : ℂ) * Complex.I))) *
          edgeR τ * edgeS τ := ctHG_edge ε τ
    unfold fctPhiC
    rw [hH, div_eq_mul_inv]
    simp only [mul_inv_rev]
    ring
  have hprod := (hPsi_ej.mul (hDinv_EJ.mul (hZEinv_EJ.mul (hRinv_EJ.mul hSinv_EJ)))).const_mul (c : ℂ)
  have hcast := hprod.cast (a' := 3) (b' := 0) (by norm_num) (by norm_num)
  simp only [add_zero] at hcast
  refine ⟨‖(c : ℂ)‖ * (4 * MP * (4 * MDinv * (4 * MZEinv * (4 * MRinv * 16)))), ?_⟩
  rw [hPhi_eq]
  exact hcast

/-- info: 'FormalResearch.SignUncertainty.fctPhiC_near_ejOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiC_near_ejOn

end FormalResearch.SignUncertainty
