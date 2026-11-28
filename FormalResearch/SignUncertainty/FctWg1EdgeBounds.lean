/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWg1Edge

/-!
# Cusp profiles and macroscopic bound `(fct:hg1-mac)` for `ctWg1`

Proves `CuspProfile (3/2)` for `wg1YA` (`ctTg1 (i c_s u)`) and `CuspProfile (1/2)` for `wg1YB` (`seedV 0 (c_s u)`),
deduces the global and `L ≥ 0` edge bounds `ctWg1_partB_bound` and `ctWg1_partA_bound` from `FctCuspEdge.fct_cusp_edge`,
and concludes `(fct:hg1-mac)` (`ctWg1_mac_bound`) on `L = log(π² ξ) > 0`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCuspEdge FormalResearch.Asymptotics

namespace FormalResearch.SignUncertainty

noncomputable def lineC (u : ℝ) : ℂ := ((ceCs * u : ℝ) : ℂ) * Complex.I

private lemma lineC_mem_slit {u : ℝ} (hu : u ≠ 0) : lineC u ∈ Complex.slitPlane := by
  right; simp [lineC, mul_ne_zero ceCs_pos.ne' hu]

private lemma lineC_ne {u : ℝ} (hu : u ≠ 0) : lineC u ≠ 0 :=
  Complex.slitPlane_ne_zero (lineC_mem_slit hu)

private lemma lineC_norm (u : ℝ) : ‖lineC u‖ = ceCs * |u| := by
  simp [lineC, abs_of_pos ceCs_pos]

private lemma lineC_re (u : ℝ) : (lineC u).re = 0 := by simp [lineC]

private lemma cpow_line_iteratedDeriv (p : ℂ) (k : ℕ) :
    ∀ {u : ℝ}, u ≠ 0 →
      iteratedDeriv k (fun t : ℝ => (lineC t) ^ p) u =
        (∏ i ∈ Finset.range k, (p - (i : ℂ))) * ((ceCs : ℂ) * Complex.I) ^ k * (lineC u) ^ (p - (k : ℂ)) := by
  induction k with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    have hev : iteratedDeriv m (fun t : ℝ => (lineC t) ^ p) =ᶠ[𝓝 u]
        fun t : ℝ => (∏ i ∈ Finset.range m, (p - (i : ℂ))) * ((ceCs : ℂ) * Complex.I) ^ m *
          (lineC t) ^ (p - (m : ℂ)) := by
      filter_upwards [isOpen_ne.mem_nhds hu] with t ht
      exact ih ht
    have hline : HasDerivAt lineC ((ceCs : ℂ) * Complex.I) u := by
      have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
        funext t; unfold lineC; push_cast; ring
      rw [heq]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul ((ceCs : ℂ) * Complex.I)
    have hcp : HasDerivAt (fun z : ℂ => z ^ (p - (m : ℂ)))
        ((p - (m : ℂ)) * (lineC u) ^ (p - (m : ℂ) - 1)) (lineC u) := by
      have h := (hasDerivAt_id (lineC u)).cpow_const (lineC_mem_slit hu) (c := p - (m : ℂ))
      simpa using h
    have hd : HasDerivAt (fun t : ℝ =>
        (∏ i ∈ Finset.range m, (p - (i : ℂ))) * ((ceCs : ℂ) * Complex.I) ^ m * (lineC t) ^ (p - (m : ℂ)))
        ((∏ i ∈ Finset.range m, (p - (i : ℂ))) * ((ceCs : ℂ) * Complex.I) ^ m *
          ((p - (m : ℂ)) * (lineC u) ^ (p - (m : ℂ) - 1) * ((ceCs : ℂ) * Complex.I))) u :=
      ((hcp.scomp u hline).const_mul _).congr_deriv (by rw [smul_eq_mul]; ring)
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv, Finset.prod_range_succ, pow_succ]
    have hexp : p - (m : ℂ) - 1 = p - ((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hexp]; ring

private lemma cpow_line_iteratedDeriv_norm (α : ℝ) {k : ℕ} (hk : k ≤ 3) {u : ℝ} (hu : u ≠ 0) :
    ‖iteratedDeriv k (fun t : ℝ => (lineC t) ^ (α : ℂ)) u‖ ≤
      ((Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖(α : ℂ) - (i : ℂ)‖) *
        ceCs ^ α * |u| ^ (α - k) := by
  rw [cpow_line_iteratedDeriv (α : ℂ) k hu, norm_mul, norm_mul, norm_pow]
  have hexp : (α : ℂ) - (k : ℂ) = ((α - (k : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, norm_cpow_ofReal_exponent (lineC_ne hu) (α - (k : ℝ)), lineC_norm]
  have hcs_norm : ‖(ceCs : ℂ) * Complex.I‖ = ceCs := by simp [abs_of_pos ceCs_pos]
  rw [hcs_norm, Real.mul_rpow ceCs_pos.le (abs_nonneg u)]
  have hcs_pow : ceCs ^ k * ceCs ^ (α - (k : ℝ)) = ceCs ^ α := by
    rw [← Real.rpow_natCast ceCs k, ← Real.rpow_add ceCs_pos]; congr 1; ring
  have hprod_eq : ‖∏ i ∈ Finset.range k, ((α : ℂ) - (i : ℂ))‖ =
      ∏ i ∈ Finset.range k, ‖(α : ℂ) - (i : ℂ)‖ := norm_prod _ _
  rw [hprod_eq]
  have hsum : ∏ i ∈ Finset.range k, ‖(α : ℂ) - (i : ℂ)‖ ≤
      (Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖(α : ℂ) - (i : ℂ)‖ :=
    Finset.single_le_sum (f := fun m => ∏ i ∈ Finset.range m, ‖(α : ℂ) - (i : ℂ)‖)
      (fun m _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  calc (∏ i ∈ Finset.range k, ‖(α : ℂ) - (i : ℂ)‖) * ceCs ^ k * (ceCs ^ (α - (k : ℝ)) * |u| ^ (α - (k : ℝ)))
      = (∏ i ∈ Finset.range k, ‖(α : ℂ) - (i : ℂ)‖) * (ceCs ^ k * ceCs ^ (α - (k : ℝ))) * |u| ^ (α - (k : ℝ)) := by ring
    _ = (∏ i ∈ Finset.range k, ‖(α : ℂ) - (i : ℂ)‖) * ceCs ^ α * |u| ^ (α - (k : ℝ)) := by rw [hcs_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum (Real.rpow_pos_of_pos ceCs_pos _).le)
        (Real.rpow_pos_of_pos (abs_pos.mpr hu) _).le

private lemma cpow_line_mul_bound {α MH : ℝ} (hMH : 0 ≤ MH) {h : ℝ → ℂ} {u : ℝ} (hu : u ≠ 0)
    (hcd : ContDiffAt ℝ 3 h u)
    (hh : ∀ m ≤ 3, ‖iteratedDeriv m h u‖ ≤ MH * |u| ^ (-(m : ℝ))) :
    ∀ j ≤ 3, ‖iteratedDeriv j (fun t : ℝ => (lineC t) ^ (α : ℂ) * h t) u‖ ≤
      (8 * ((Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖(α : ℂ) - (i : ℂ)‖) *
        ceCs ^ α * MH) * |u| ^ (α - j) := by
  intro j hj
  have hup : ContDiffAt ℝ j (fun t : ℝ => (lineC t) ^ (α : ℂ)) u := by
    have hline_cd : ContDiff ℝ ⊤ lineC := by
      have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
        funext t; unfold lineC; push_cast; ring
      rw [heq]; exact contDiff_const.mul Complex.ofRealCLM.contDiff
    have hcp_cd : ContDiffOn ℂ ⊤ (fun z : ℂ => z ^ (α : ℂ)) Complex.slitPlane :=
      (differentiableOn_id.cpow_const fun _ hz => hz).contDiffOn Complex.isOpen_slitPlane
    have hat := (hcp_cd.restrict_scalars ℝ).contDiffAt (Complex.isOpen_slitPlane.mem_nhds (lineC_mem_slit hu))
    exact (hat.comp u hline_cd.contDiffAt).of_le le_top
  rw [show (fun t : ℝ => (lineC t) ^ (α : ℂ) * h t) = (fun t => (lineC t) ^ (α : ℂ)) * h from rfl,
    iteratedDeriv_mul hup (hcd.of_le (by exact_mod_cast hj))]
  let CP : ℝ := (Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖(α : ℂ) - (i : ℂ)‖
  have hCP : 0 ≤ CP := Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hq : 0 < |u| := abs_pos.mpr hu
  have htri := norm_sum_le (Finset.range (j + 1)) fun k =>
    (Nat.choose j k : ℂ) * iteratedDeriv k (fun t : ℝ => (lineC t) ^ (α : ℂ)) u * iteratedDeriv (j - k) h u
  refine htri.trans ?_
  have hsum : ∑ k ∈ Finset.range (j + 1),
      ‖(Nat.choose j k : ℂ) * iteratedDeriv k (fun t : ℝ => (lineC t) ^ (α : ℂ)) u * iteratedDeriv (j - k) h u‖ ≤
      (∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ)) * (CP * ceCs ^ α * MH * |u| ^ (α - j)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 : ‖iteratedDeriv k (fun t : ℝ => (lineC t) ^ (α : ℂ)) u‖ ≤ CP * ceCs ^ α * |u| ^ (α - k) :=
      cpow_line_iteratedDeriv_norm α (hkj.trans hj) hu
    have h2 := hh (j - k) (by omega)
    have hrp : |u| ^ (α - k) * |u| ^ (-((j - k : ℕ) : ℝ)) = |u| ^ (α - j) := by
      rw [← Real.rpow_add hq]; congr 1
      have : ((j - k : ℕ) : ℝ) = (j : ℝ) - k := by rw [Nat.cast_sub hkj]
      linarith
    have hce_nn : 0 ≤ CP * ceCs ^ α * |u| ^ (α - k) :=
      mul_nonneg (mul_nonneg hCP (Real.rpow_pos_of_pos ceCs_pos _).le) (Real.rpow_pos_of_pos hq _).le
    calc (Nat.choose j k : ℝ) * ‖iteratedDeriv k (fun t : ℝ => (lineC t) ^ (α : ℂ)) u‖ * ‖iteratedDeriv (j - k) h u‖
        ≤ (Nat.choose j k : ℝ) * (CP * ceCs ^ α * |u| ^ (α - k)) * (MH * |u| ^ (-((j - k : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hce_nn)
      _ = (Nat.choose j k : ℝ) * (CP * ceCs ^ α * MH * (|u| ^ (α - k) * |u| ^ (-((j - k : ℕ) : ℝ)))) := by ring
      _ = (Nat.choose j k : ℝ) * (CP * ceCs ^ α * MH * |u| ^ (α - j)) := by rw [hrp]
  refine hsum.trans ?_
  have hch : ∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ) = (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [hch]
  have h2j : (2 : ℝ) ^ j ≤ 8 := (pow_le_pow_right₀ (by norm_num) hj).trans_eq (by norm_num)
  have hnn : 0 ≤ CP * ceCs ^ α * MH * |u| ^ (α - j) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCP (Real.rpow_pos_of_pos ceCs_pos _).le) hMH)
      (Real.rpow_pos_of_pos hq _).le
  calc (2 : ℝ) ^ j * (CP * ceCs ^ α * MH * |u| ^ (α - j))
      ≤ 8 * (CP * ceCs ^ α * MH * |u| ^ (α - j)) := mul_le_mul_of_nonneg_right h2j hnn
    _ = (8 * CP * ceCs ^ α * MH) * |u| ^ (α - j) := by ring

private lemma lineC_slit_iteratedDeriv {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane)
    (k : ℕ) : ∀ {u : ℝ}, u ≠ 0 →
      iteratedDeriv k (fun t : ℝ => F (lineC t)) u =
        ((ceCs : ℂ) * Complex.I) ^ k * iteratedDeriv k F (lineC u) := by
  have hF_cd : ContDiffOn ℂ ∞ F Complex.slitPlane := (hF.contDiffOn Complex.isOpen_slitPlane).of_le le_top
  induction k with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    have hev : iteratedDeriv m (fun t : ℝ => F (lineC t)) =ᶠ[𝓝 u]
        fun t : ℝ => ((ceCs : ℂ) * Complex.I) ^ m * iteratedDeriv m F (lineC t) := by
      filter_upwards [isOpen_ne.mem_nhds hu] with t ht
      exact ih ht
    have hcd_m : ContDiffOn ℂ ∞ (iteratedDeriv m F) Complex.slitPlane :=
      FctSym.contDiffOn_iteratedDeriv_gen Complex.isOpen_slitPlane hF_cd m
    have hda := ((hcd_m.differentiableOn (by simp)).differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds (lineC_mem_slit hu))).hasDerivAt
    have hline : HasDerivAt lineC ((ceCs : ℂ) * Complex.I) u := by
      have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
        funext t; unfold lineC; push_cast; ring
      rw [heq]; simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul ((ceCs : ℂ) * Complex.I)
    have hd := (hda.scomp u hline).const_mul (((ceCs : ℂ) * Complex.I) ^ m)
    rw [iteratedDeriv_succ, hev.deriv_eq,
      show (fun t : ℝ => ((ceCs : ℂ) * Complex.I) ^ m * iteratedDeriv m F (lineC t)) =
        fun y : ℝ => ((ceCs : ℂ) * Complex.I) ^ m * (iteratedDeriv m F ∘ lineC) y from rfl,
      hd.deriv, iteratedDeriv_succ, smul_eq_mul, pow_succ]
    ring

private lemma compact_deriv3_bound {f : ℝ → ℂ} (hcd : ContDiff ℝ 3 f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m ≤ 3, ∀ u ∈ Icc (-2 : ℝ) 2, ‖iteratedDeriv m f u‖ ≤ B := by
  have hb0 := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hcd.continuous_iteratedDeriv 0 (by simp)).continuousOn
  have hb1 := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hcd.continuous_iteratedDeriv 1 (by norm_num)).continuousOn
  have hb2 := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hcd.continuous_iteratedDeriv 2 (by norm_num)).continuousOn
  have hb3 := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hcd.continuous_iteratedDeriv 3 le_rfl).continuousOn
  rcases hb0 with ⟨M0, hM0⟩; rcases hb1 with ⟨M1, hM1⟩; rcases hb2 with ⟨M2, hM2⟩; rcases hb3 with ⟨M3, hM3⟩
  refine ⟨max 0 (max (max M0 M1) (max M2 M3)), le_max_left _ _, fun m hm u hu => ?_⟩
  interval_cases m
  · exact (hM0 u hu).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
  · exact (hM1 u hu).trans (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))
  · exact (hM2 u hu).trans (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact (hM3 u hu).trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

private lemma one_le_eight_rpow_neg {m : ℕ} (hm : m ≤ 3) {u : ℝ} (hu0 : 0 < |u|) (hu2 : |u| < 2) :
    (1 : ℝ) ≤ 8 * |u| ^ (-(m : ℝ)) := by
  have hm_pow : |u| ^ m ≤ 2 ^ 3 := by
    calc |u| ^ m ≤ 2 ^ m := pow_le_pow_left₀ hu0.le hu2.le m
      _ ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hm
  rw [Real.rpow_neg hu0.le, Real.rpow_natCast]
  calc (1 : ℝ) = |u| ^ m * (|u| ^ m)⁻¹ := (mul_inv_cancel₀ (pow_pos hu0 m).ne').symm
    _ ≤ (2 ^ 3 : ℝ) * (|u| ^ m)⁻¹ := mul_le_mul_of_nonneg_right hm_pow (inv_nonneg.mpr (pow_nonneg hu0.le m))
    _ = 8 * (|u| ^ m)⁻¹ := by norm_num

private lemma lineC_slit_contDiffOn {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Complex.slitPlane) :
    ContDiffOn ℝ ∞ (fun u : ℝ => F (lineC u)) ({0}ᶜ) := by
  have hF_cd : ContDiffOn ℂ ∞ F Complex.slitPlane := (hF.contDiffOn Complex.isOpen_slitPlane).of_le le_top
  intro u hu
  have hmem : lineC u ∈ Complex.slitPlane := lineC_mem_slit hu
  have hat := (hF_cd.restrict_scalars ℝ).contDiffAt (Complex.isOpen_slitPlane.mem_nhds hmem)
  have hline : ContDiff ℝ ∞ lineC := by
    have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
      funext t; unfold lineC; push_cast; ring
    rw [heq]; exact contDiff_const.mul (Complex.ofRealCLM.contDiff.of_le le_top)
  exact (hat.comp u hline.contDiffAt).contDiffWithinAt

lemma wg1YA_cuspProfile :
    ∃ C_Y : ℝ, 0 ≤ C_Y ∧ CuspProfile (3 / 2) C_Y wg1YA
      (fun u => (ceK : ℂ) * uctE1 (lineC u))
      (fun u => ((ceK : ℂ) / (Real.sqrt π : ℂ)) * (lineC u) ^ (3 / 2 : ℂ) * uctE2 (lineC u)) := by
  have hy_eq : wg1YA = fun u : ℝ => uctG1Ext (lineC u) := by
    funext u; unfold wg1YA ctTg1 lineC; exact uctG1Ext_eq (by simp)
  have hcdY_inf : ContDiffOn ℝ ∞ wg1YA ({0}ᶜ) := by
    rw [hy_eq]; exact lineC_slit_contDiffOn differentiableOn_uctG1Ext
  have hcdY : ContDiffOn ℝ 3 wg1YA ({0}ᶜ) := hcdY_inf.of_le (by simp)
  have he1_cd : ContDiff ℝ 3 (fun u : ℝ => (ceK : ℂ) * uctE1 (lineC u)) := by
    have hline : ContDiff ℝ 3 lineC := by
      have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
        funext t; unfold lineC; push_cast; ring
      rw [heq]; exact contDiff_const.mul Complex.ofRealCLM.contDiff
    exact contDiff_const.mul (((uctE1_differentiable.contDiff (n := ⊤)).restrict_scalars ℝ).of_le le_top |>.comp hline)
  obtain ⟨B0, hB0_pos, hB0⟩ := compact_deriv3_bound he1_cd
  have he2_cd : ContDiff ℝ 3 (fun u : ℝ => ((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE2 (lineC u)) := by
    have hline : ContDiff ℝ 3 lineC := by
      have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
        funext t; unfold lineC; push_cast; ring
      rw [heq]; exact contDiff_const.mul Complex.ofRealCLM.contDiff
    exact contDiff_const.mul (((uctE2_differentiable.contDiff (n := ⊤)).restrict_scalars ℝ).of_le le_top |>.comp hline)
  obtain ⟨B2, hB2_pos, hB2⟩ := compact_deriv3_bound he2_cd
  have hG0 := uctG1Ext_iteratedDeriv_bound 0
  have hG1 := uctG1Ext_iteratedDeriv_bound 1
  have hG2 := uctG1Ext_iteratedDeriv_bound 2
  have hG3 := uctG1Ext_iteratedDeriv_bound 3
  rcases hG0 with ⟨CG0, hCG0_0, hCG0⟩; rcases hG1 with ⟨CG1, hCG1_0, hCG1⟩
  rcases hG2 with ⟨CG2, hCG2_0, hCG2⟩; rcases hG3 with ⟨CG3, hCG3_0, hCG3⟩
  let CG : ℝ := max (max CG0 CG1) (max CG2 CG3)
  have hCG0_le : 0 ≤ CG := le_max_of_le_left (le_max_of_le_left hCG0_0)
  have hK_mid : ∀ m : ℕ, ∃ M ≥ 0, ∀ u ∈ (Icc (1 : ℝ) 2 ∪ Icc (-2) (-1)), ‖iteratedDeriv m wg1YA u‖ ≤ M := fun m => by
    have hsub : (Icc (1 : ℝ) 2 ∪ Icc (-2 : ℝ) (-1)) ⊆ ({0}ᶜ : Set ℝ) := fun u hu h0 => by
      rw [Set.mem_singleton_iff] at h0
      rcases hu with hu | hu <;> linarith [hu.1, hu.2]
    have hc := (FctSym.contDiffOn_iteratedDeriv_gen isOpen_ne hcdY_inf m).continuousOn.mono hsub
    obtain ⟨M, hM⟩ := (isCompact_Icc.union isCompact_Icc).exists_bound_of_continuousOn hc
    exact ⟨max M 0, le_max_right _ _, fun u hu => (hM u hu).trans (le_max_left _ _)⟩
  choose M_f hMf0 hMf using hK_mid
  let CM : ℝ := max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 2 ^ (15 / 2 : ℝ)
  let CR : ℝ := 8 * ((Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖((3 / 2 : ℝ) : ℂ) - (i : ℂ)‖) *
    ceCs ^ (3 / 2 : ℝ) * (8 * B2)
  let CF : ℝ := CG * ceCs ^ (-(9 / 2 : ℝ))
  have hCR0 : 0 ≤ CR := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (Real.rpow_pos_of_pos ceCs_pos _).le) (by linarith)
  have hCM0 : 0 ≤ CM := mul_nonneg (le_max_of_le_left (le_max_of_le_left (hMf0 0))) (by positivity)
  have hCF0 : 0 ≤ CF := mul_nonneg hCG0_le (Real.rpow_pos_of_pos ceCs_pos _).le
  refine ⟨max (max B0 CR) (max CM CF), le_max_of_le_left (le_max_of_le_left hB0_pos), hcdY,
    fun j hj u hu => ?_, fun u _ => ?_,
    he1_cd.contDiffOn, fun j hj u hu => (hB0 j hj u (abs_le.mp hu.le)).trans (le_max_of_le_left (le_max_left _ _)),
    fun j hj u hu0 hu2 => ?_⟩
  · -- far_bound
    have heq_exp : -(2 * (3 / 2 : ℝ) + 3 / 2) - (j : ℝ) = -((9 / 2 : ℝ) + j) := by ring
    rw [heq_exp]
    by_cases hu2 : 2 ≤ |u|
    · have hu_ne : u ≠ 0 := by intro h0; rw [h0, abs_zero] at hu; linarith
      have hw_norm : 2 ≤ ‖lineC u‖ := by rw [lineC_norm]; nlinarith [ceCs_gt_one]
      have hid : iteratedDeriv j wg1YA u = ((ceCs : ℂ) * Complex.I) ^ j * iteratedDeriv j uctG1Ext (lineC u) := by
        rw [hy_eq]; exact lineC_slit_iteratedDeriv differentiableOn_uctG1Ext j hu_ne
      rw [hid, norm_mul, norm_pow, show ‖(ceCs : ℂ) * Complex.I‖ = ceCs by simp [abs_of_pos ceCs_pos]]
      have hGj : ‖iteratedDeriv j uctG1Ext (lineC u)‖ ≤ CG * ‖lineC u‖ ^ (-((9 / 2 : ℝ) + j)) := by
        interval_cases j
        · exact (hCG0 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (by positivity))
        · exact (hCG1 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (by positivity))
        · exact (hCG2 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by positivity))
        · exact (hCG3 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by positivity))
      rw [lineC_norm, Real.mul_rpow ceCs_pos.le (abs_nonneg u)] at hGj
      have hcs_pow : ceCs ^ j * ceCs ^ (-((9 / 2 : ℝ) + j)) = ceCs ^ (-(9 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast ceCs j, ← Real.rpow_add ceCs_pos]; congr 1; ring
      calc ceCs ^ j * ‖iteratedDeriv j uctG1Ext (lineC u)‖
          ≤ ceCs ^ j * (CG * (ceCs ^ (-((9 / 2 : ℝ) + j)) * |u| ^ (-((9 / 2 : ℝ) + j)))) :=
            mul_le_mul_of_nonneg_left hGj (pow_nonneg ceCs_pos.le j)
        _ = CG * (ceCs ^ j * ceCs ^ (-((9 / 2 : ℝ) + j))) * |u| ^ (-((9 / 2 : ℝ) + j)) := by ring
        _ = CF * |u| ^ (-((9 / 2 : ℝ) + j)) := by rw [hcs_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by positivity)
    · push Not at hu2
      have humem : u ∈ Icc (1 : ℝ) 2 ∪ Icc (-2) (-1) := by
        rcases le_or_gt 0 u with h0 | h0
        · left; rw [abs_of_nonneg h0] at hu hu2; exact ⟨hu, hu2.le⟩
        · right; rw [abs_of_neg h0] at hu hu2; exact ⟨by linarith, by linarith⟩
      have hMj : M_f j ≤ max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) := by
        interval_cases j
        · exact le_max_of_le_left (le_max_left _ _)
        · exact le_max_of_le_left (le_max_right _ _)
        · exact le_max_of_le_right (le_max_left _ _)
        · exact le_max_of_le_right (le_max_right _ _)
      have hupos : 0 < |u| := by linarith
      have hpow : (1 : ℝ) ≤ 2 ^ (15 / 2 : ℝ) * |u| ^ (-((9 / 2 : ℝ) + j)) := by
        have hjr : (j : ℝ) ≤ 3 := by exact_mod_cast hj
        have h1 : |u| ^ ((9 / 2 : ℝ) + j) ≤ 2 ^ (15 / 2 : ℝ) := by
          calc |u| ^ ((9 / 2 : ℝ) + j) ≤ 2 ^ ((9 / 2 : ℝ) + j) := Real.rpow_le_rpow hupos.le hu2.le (by positivity)
            _ ≤ 2 ^ (15 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [Real.rpow_neg hupos.le]
        calc (1 : ℝ) = |u| ^ ((9 / 2 : ℝ) + j) * (|u| ^ ((9 / 2 : ℝ) + j))⁻¹ := (mul_inv_cancel₀ (Real.rpow_pos_of_pos hupos _).ne').symm
          _ ≤ 2 ^ (15 / 2 : ℝ) * (|u| ^ ((9 / 2 : ℝ) + j))⁻¹ := by gcongr
      calc ‖iteratedDeriv j wg1YA u‖ ≤ M_f j := hMf j u humem
        _ ≤ max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 1 := by linarith
        _ ≤ CM * |u| ^ (-((9 / 2 : ℝ) + j)) := by
            dsimp only [CM]
            calc max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 1
                ≤ max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * (2 ^ (15 / 2 : ℝ) * |u| ^ (-((9 / 2 : ℝ) + j))) :=
                  mul_le_mul_of_nonneg_left hpow (le_max_of_le_left (le_max_of_le_left (hMf0 0)))
              _ = (max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 2 ^ (15 / 2 : ℝ)) * |u| ^ (-((9 / 2 : ℝ) + j)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by positivity)
  · -- decomp
    unfold wg1YA ctTg1
    have hrep := (uct_airy_trans_int_rep_g1 (w := lineC u) (by rw [lineC_re])).2
    change airyTwistedLaplaceC (ceG1 (Special.airyZero 1)) (lineC u) = _ at hrep
    rw [show ((ceCs * u : ℝ) : ℂ) * Complex.I = lineC u from rfl, hrep]
  · -- R_bound
    have hu_ne : u ≠ 0 := abs_pos.mp hu0
    have hfun : (fun t : ℝ => ((ceK : ℂ) / (Real.sqrt π : ℂ)) * (lineC t) ^ (3 / 2 : ℂ) * uctE2 (lineC t)) =
        fun t : ℝ => (lineC t) ^ ((3 / 2 : ℝ) : ℂ) * (((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE2 (lineC t)) := by
      funext t; norm_num [mul_comm, mul_left_comm, mul_assoc]
    rw [hfun]
    have hh : ∀ m ≤ 3, ‖iteratedDeriv m (fun t : ℝ => ((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE2 (lineC t)) u‖ ≤
        (8 * B2) * |u| ^ (-(m : ℝ)) := fun m hm => by
      have hm1 := hB2 m hm u (abs_le.mp hu2.le)
      have h8 := one_le_eight_rpow_neg hm hu0 hu2
      calc ‖iteratedDeriv m (fun t : ℝ => ((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE2 (lineC t)) u‖
          ≤ B2 * 1 := by linarith
        _ ≤ B2 * (8 * |u| ^ (-(m : ℝ))) := mul_le_mul_of_nonneg_left h8 hB2_pos
        _ = (8 * B2) * |u| ^ (-(m : ℝ)) := by ring
    exact (cpow_line_mul_bound (by positivity) hu_ne he2_cd.contDiffAt hh j hj).trans
      (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (by positivity))

lemma wg1YB_cuspProfile :
    ∃ C_Y : ℝ, 0 ≤ C_Y ∧ CuspProfile (1 / 2) C_Y wg1YB (fun _ => 0) wg1YB := by
  have hy_eq : wg1YB = fun u : ℝ => -uctF1Ext (lineC u) := by
    funext u; unfold wg1YB seedV lineC
    rw [seedT_eq_text 0 (by simp)]
    simp [seedText]
  have hdiff_F : DifferentiableOn ℂ (fun z => -uctF1Ext z) Complex.slitPlane :=
    differentiableOn_uctF1Ext.neg
  have hcdY_inf : ContDiffOn ℝ ∞ wg1YB ({0}ᶜ) := by
    rw [hy_eq]; exact lineC_slit_contDiffOn hdiff_F
  have hcdY : ContDiffOn ℝ 3 wg1YB ({0}ᶜ) := hcdY_inf.of_le (by simp)
  have he_cd : ContDiff ℝ 3 (fun u : ℝ => -((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE (lineC u)) := by
    have hline : ContDiff ℝ 3 lineC := by
      have heq : lineC = fun t : ℝ => ((ceCs : ℂ) * Complex.I) * (t : ℂ) := by
        funext t; unfold lineC; push_cast; ring
      rw [heq]; exact contDiff_const.mul Complex.ofRealCLM.contDiff
    exact contDiff_const.mul (((uctE_differentiable.contDiff (n := ⊤)).restrict_scalars ℝ).of_le le_top |>.comp hline)
  obtain ⟨Be, hBe_pos, hBe⟩ := compact_deriv3_bound he_cd
  have hZ0 := uctZ1_iteratedDeriv_bound 0
  have hZ1 := uctZ1_iteratedDeriv_bound 1
  have hZ2 := uctZ1_iteratedDeriv_bound 2
  have hZ3 := uctZ1_iteratedDeriv_bound 3
  rcases hZ0 with ⟨CZ0, hCZ0_0, hCZ0⟩; rcases hZ1 with ⟨CZ1, hCZ1_0, hCZ1⟩
  rcases hZ2 with ⟨CZ2, hCZ2_0, hCZ2⟩; rcases hZ3 with ⟨CZ3, hCZ3_0, hCZ3⟩
  let CZ : ℝ := max (max CZ0 CZ1) (max CZ2 CZ3)
  have hCZ_0 : 0 ≤ CZ := le_max_of_le_left (le_max_of_le_left hCZ0_0)
  have hK_mid : ∀ m : ℕ, ∃ M ≥ 0, ∀ u ∈ (Icc (1 : ℝ) 2 ∪ Icc (-2) (-1)), ‖iteratedDeriv m wg1YB u‖ ≤ M := fun m => by
    have hsub : (Icc (1 : ℝ) 2 ∪ Icc (-2 : ℝ) (-1)) ⊆ ({0}ᶜ : Set ℝ) := fun u hu h0 => by
      rw [Set.mem_singleton_iff] at h0
      rcases hu with hu | hu <;> linarith [hu.1, hu.2]
    have hc := (FctSym.contDiffOn_iteratedDeriv_gen isOpen_ne hcdY_inf m).continuousOn.mono hsub
    obtain ⟨M, hM⟩ := (isCompact_Icc.union isCompact_Icc).exists_bound_of_continuousOn hc
    exact ⟨max M 0, le_max_right _ _, fun u hu => (hM u hu).trans (le_max_left _ _)⟩
  choose M_f hMf0 hMf using hK_mid
  let CM : ℝ := max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 2 ^ (11 / 2 : ℝ)
  let CR : ℝ := 8 * ((Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖((1 / 2 : ℝ) : ℂ) - (i : ℂ)‖) *
    ceCs ^ (1 / 2 : ℝ) * (8 * Be)
  let MHZ : ℝ := ‖2 * uctC‖ + CZ * ceCs ^ (-(2 : ℝ))
  let m52 : ℝ := -(5 / 2 : ℝ)
  let CF : ℝ := 8 * ((Finset.range 4).sum fun m => ∏ i ∈ Finset.range m, ‖(m52 : ℂ) - (i : ℂ)‖) *
    ceCs ^ m52 * MHZ
  have hCR0 : 0 ≤ CR := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _))
    (Real.rpow_pos_of_pos ceCs_pos _).le) (by linarith)
  have hMHZ0 : 0 ≤ MHZ := add_nonneg (norm_nonneg _) (mul_nonneg hCZ_0 (Real.rpow_pos_of_pos ceCs_pos _).le)
  have hCF0 : 0 ≤ CF := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _))
    (Real.rpow_pos_of_pos ceCs_pos _).le) hMHZ0
  refine ⟨max (max CR CM) CF, le_max_of_le_left (le_max_of_le_left hCR0), hcdY,
    fun j hj u hu => ?_, fun _ _ => (zero_add _).symm,
    contDiffOn_const, fun j _ u _ => by
      have hid0 : iteratedDeriv j (fun _ : ℝ => (0 : ℂ)) u = 0 := by cases j <;> simp
      rw [hid0, norm_zero]
      exact le_max_of_le_left (le_max_of_le_left hCR0),
    fun j hj u hu0 hu2 => ?_⟩
  · -- far_bound
    have heq_exp : -(2 * (1 / 2 : ℝ) + 3 / 2) - (j : ℝ) = m52 - j := by dsimp only [m52]; ring
    rw [heq_exp]
    by_cases hu2 : 2 ≤ |u|
    · have hu_ne : u ≠ 0 := by intro h0; rw [h0, abs_zero] at hu; linarith
      have hev_y : wg1YB =ᶠ[𝓝 u] fun t : ℝ =>
          (lineC t) ^ (m52 : ℂ) * (-(2 * uctC + uctZ1 (lineC t))) := by
        filter_upwards [isOpen_ne.mem_nhds hu_ne] with t ht
        have hwt : lineC t ≠ 0 := lineC_ne ht
        have hzdef : 2 * uctC + uctZ1 (lineC t) = (lineC t) ^ (5 / 2 : ℂ) * uctF1Ext (lineC t) := by
          unfold uctZ1; rw [← mul_assoc ((lineC t) ^ 2), ← cpow_five_half]; ring
        have hmul : (lineC t) ^ (m52 : ℂ) * (lineC t) ^ (5 / 2 : ℂ) = 1 := by
          rw [show (m52 : ℂ) = -(5 / 2 : ℂ) by dsimp only [m52]; push_cast; ring, ← Complex.cpow_add _ _ hwt]; simp
        have hyt : wg1YB t = -uctF1Ext (lineC t) := congrFun hy_eq t
        calc wg1YB t = -(1 * uctF1Ext (lineC t)) := by rw [hyt]; ring
          _ = -(((lineC t) ^ (m52 : ℂ) * (lineC t) ^ (5 / 2 : ℂ)) * uctF1Ext (lineC t)) := by rw [hmul]
          _ = (lineC t) ^ (m52 : ℂ) * -((lineC t) ^ (5 / 2 : ℂ) * uctF1Ext (lineC t)) := by ring
          _ = (lineC t) ^ (m52 : ℂ) * -(2 * uctC + uctZ1 (lineC t)) := by rw [hzdef]
      have hh_cd : ContDiffAt ℝ 3 (fun t : ℝ => -(2 * uctC + uctZ1 (lineC t))) u :=
        (contDiffAt_const.add (((lineC_slit_contDiffOn differentiableOn_uctZ1).contDiffAt
          (isOpen_ne.mem_nhds hu_ne)).of_le (by simp))).neg
      have hh_bd : ∀ m ≤ 3, ‖iteratedDeriv m (fun t : ℝ => -(2 * uctC + uctZ1 (lineC t))) u‖ ≤ MHZ * |u| ^ (-(m : ℝ)) := by
        intro m hm
        have hZ_cd : iteratedDeriv m (fun t : ℝ => -(2 * uctC + uctZ1 (lineC t))) u =
            -(iteratedDeriv m (fun t : ℝ => 2 * uctC + uctZ1 (lineC t)) u) := by
          rw [show (fun t : ℝ => -(2 * uctC + uctZ1 (lineC t))) = -fun t : ℝ => 2 * uctC + uctZ1 (lineC t) from rfl,
            iteratedDeriv_neg]
        rw [hZ_cd, norm_neg]
        have hw_norm : 2 ≤ ‖lineC u‖ := by rw [lineC_norm]; nlinarith [ceCs_gt_one]
        have hu1 : 1 ≤ |u| := hu
        rcases m with _ | k
        · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
          have h0 := hCZ0 _ (by rw [lineC_re]) hw_norm
          simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero, lineC_norm] at h0
          have hcs_m2 : (ceCs * |u|) ^ (-(2 : ℝ)) ≤ ceCs ^ (-(2 : ℝ)) := by
            rw [Real.mul_rpow ceCs_pos.le (abs_nonneg u)]
            exact mul_le_of_le_one_right (Real.rpow_pos_of_pos ceCs_pos _).le
              (Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num))
          have hCZ0_le : CZ0 ≤ CZ := le_max_of_le_left (le_max_left _ _)
          have hb0' : ‖uctZ1 (lineC u)‖ ≤ CZ * ceCs ^ (-(2 : ℝ)) :=
            h0.trans (mul_le_mul hCZ0_le hcs_m2
              (Real.rpow_pos_of_pos (mul_pos ceCs_pos (abs_pos.mpr hu_ne)) _).le hCZ_0)
          calc ‖2 * uctC + uctZ1 (lineC u)‖ ≤ ‖2 * uctC‖ + ‖uctZ1 (lineC u)‖ := norm_add_le _ _
            _ ≤ ‖2 * uctC‖ + CZ * ceCs ^ (-(2 : ℝ)) := add_le_add le_rfl hb0'
        · have h1 : ContDiffAt ℝ (k + 1) (fun _ : ℝ => 2 * uctC) u := contDiff_const.contDiffAt
          have h2 : ContDiffAt ℝ (k + 1) (fun t : ℝ => uctZ1 (lineC t)) u :=
            ((lineC_slit_contDiffOn differentiableOn_uctZ1).contDiffAt (isOpen_ne.mem_nhds hu_ne)).of_le
              (by simp)
          rw [show (fun t : ℝ => 2 * uctC + uctZ1 (lineC t)) = (fun _ : ℝ => 2 * uctC) + fun t : ℝ => uctZ1 (lineC t) from rfl,
            iteratedDeriv_add h1 h2, show iteratedDeriv (k + 1) (fun _ : ℝ => 2 * uctC) u = 0 from by simp [iteratedDeriv_const], zero_add,
            lineC_slit_iteratedDeriv differentiableOn_uctZ1 (k + 1) hu_ne, norm_mul, norm_pow,
            show ‖(ceCs : ℂ) * Complex.I‖ = ceCs by simp [abs_of_pos ceCs_pos]]
          have hk2 : k ≤ 2 := by omega
          have hZk : ‖iteratedDeriv (k + 1) uctZ1 (lineC u)‖ ≤ CZ * ‖lineC u‖ ^ (-((2 : ℝ) + (k + 1 : ℕ))) := by
            interval_cases k
            · exact (hCZ1 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (by positivity))
            · exact (hCZ2 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (by positivity))
            · exact (hCZ3 _ (by rw [lineC_re]) hw_norm).trans (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by positivity))
          rw [lineC_norm, Real.mul_rpow ceCs_pos.le (abs_nonneg u)] at hZk
          have hcs_p : ceCs ^ (k + 1) * ceCs ^ (-((2 : ℝ) + ((k + 1 : ℕ) : ℝ))) = ceCs ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_natCast ceCs (k + 1), ← Real.rpow_add ceCs_pos]; congr 1; ring
          have hu_p : |u| ^ (-((2 : ℝ) + ((k + 1 : ℕ) : ℝ))) ≤ |u| ^ (-((k + 1 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
          have hcs_nn : 0 ≤ CZ * ceCs ^ (-(2 : ℝ)) := mul_nonneg hCZ_0 (Real.rpow_pos_of_pos ceCs_pos _).le
          calc ceCs ^ (k + 1) * ‖iteratedDeriv (k + 1) uctZ1 (lineC u)‖
              ≤ ceCs ^ (k + 1) * (CZ * (ceCs ^ (-((2 : ℝ) + ((k + 1 : ℕ) : ℝ))) * |u| ^ (-((2 : ℝ) + ((k + 1 : ℕ) : ℝ))))) :=
                mul_le_mul_of_nonneg_left hZk (pow_nonneg ceCs_pos.le _)
            _ = (CZ * (ceCs ^ (k + 1) * ceCs ^ (-((2 : ℝ) + ((k + 1 : ℕ) : ℝ))))) * |u| ^ (-((2 : ℝ) + ((k + 1 : ℕ) : ℝ))) := by ring
            _ ≤ (CZ * ceCs ^ (-(2 : ℝ))) * |u| ^ (-((k + 1 : ℕ) : ℝ)) := by
                rw [hcs_p]; exact mul_le_mul_of_nonneg_left hu_p hcs_nn
            _ ≤ MHZ * |u| ^ (-((k + 1 : ℕ) : ℝ)) := by
                have : CZ * ceCs ^ (-(2 : ℝ)) ≤ MHZ := by dsimp only [MHZ]; linarith [norm_nonneg (2 * uctC)]
                gcongr
      rw [hev_y.iteratedDeriv_eq]
      exact (cpow_line_mul_bound (α := m52) hMHZ0 hu_ne hh_cd hh_bd j hj).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · push Not at hu2
      have humem : u ∈ Icc (1 : ℝ) 2 ∪ Icc (-2) (-1) := by
        rcases le_or_gt 0 u with h0 | h0
        · left; rw [abs_of_nonneg h0] at hu hu2; exact ⟨hu, hu2.le⟩
        · right; rw [abs_of_neg h0] at hu hu2; exact ⟨by linarith, by linarith⟩
      have hMj : M_f j ≤ max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) := by
        interval_cases j
        · exact le_max_of_le_left (le_max_left _ _)
        · exact le_max_of_le_left (le_max_right _ _)
        · exact le_max_of_le_right (le_max_left _ _)
        · exact le_max_of_le_right (le_max_right _ _)
      have hupos : 0 < |u| := by linarith
      have hpow : (1 : ℝ) ≤ 2 ^ (11 / 2 : ℝ) * |u| ^ (m52 - j) := by
        have hjr : (j : ℝ) ≤ 3 := by exact_mod_cast hj
        have hexp : m52 - j = -((5 / 2 : ℝ) + j) := by dsimp only [m52]; ring
        rw [hexp, Real.rpow_neg hupos.le]
        have h1 : |u| ^ ((5 / 2 : ℝ) + j) ≤ 2 ^ (11 / 2 : ℝ) := by
          calc |u| ^ ((5 / 2 : ℝ) + j) ≤ 2 ^ ((5 / 2 : ℝ) + j) := Real.rpow_le_rpow hupos.le hu2.le (by positivity)
            _ ≤ 2 ^ (11 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        calc (1 : ℝ) = |u| ^ ((5 / 2 : ℝ) + j) * (|u| ^ ((5 / 2 : ℝ) + j))⁻¹ :=
              (mul_inv_cancel₀ (Real.rpow_pos_of_pos hupos _).ne').symm
          _ ≤ 2 ^ (11 / 2 : ℝ) * (|u| ^ ((5 / 2 : ℝ) + j))⁻¹ := by gcongr
      calc ‖iteratedDeriv j wg1YB u‖ ≤ M_f j := hMf j u humem
        _ ≤ max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 1 := by linarith
        _ ≤ CM * |u| ^ (m52 - j) := by
            dsimp only [CM]
            calc max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 1
                ≤ max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * (2 ^ (11 / 2 : ℝ) * |u| ^ (m52 - j)) :=
                  mul_le_mul_of_nonneg_left hpow (le_max_of_le_left (le_max_of_le_left (hMf0 0)))
              _ = (max (max (M_f 0) (M_f 1)) (max (M_f 2) (M_f 3)) * 2 ^ (11 / 2 : ℝ)) * |u| ^ (m52 - j) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (by positivity)
  · -- R_bound
    have hu_ne : u ≠ 0 := abs_pos.mp hu0
    have hfun : wg1YB = fun t : ℝ => (lineC t) ^ ((1 / 2 : ℝ) : ℂ) * (-((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE (lineC t)) := by
      funext t
      have h1 := congrFun hy_eq t
      rw [h1]; unfold uctF1Ext uctC
      push_cast; ring
    rw [hfun]
    have hh : ∀ m ≤ 3, ‖iteratedDeriv m (fun t : ℝ => -((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE (lineC t)) u‖ ≤
        (8 * Be) * |u| ^ (-(m : ℝ)) := fun m hm => by
      have hm1 := hBe m hm u (abs_le.mp hu2.le)
      have h8 := one_le_eight_rpow_neg hm hu0 hu2
      calc ‖iteratedDeriv m (fun t : ℝ => -((ceK : ℂ) / (Real.sqrt π : ℂ)) * uctE (lineC t)) u‖
          ≤ Be * 1 := by linarith
        _ ≤ Be * (8 * |u| ^ (-(m : ℝ))) := mul_le_mul_of_nonneg_left h8 hBe_pos
        _ = (8 * Be) * |u| ^ (-(m : ℝ)) := by ring
    exact (cpow_line_mul_bound (α := 1 / 2) (MH := 8 * Be) (mul_nonneg (by norm_num) hBe_pos)
      hu_ne he_cd.contDiffAt hh j hj).trans
      (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (by positivity))

private lemma cuspEdge_integrable {α η C_A C_Y : ℝ} (hα0 : 0 < α) (hη : 0 < η) (hCY : 0 ≤ C_Y)
    {c L : ℝ} (hc : 1 ≤ c) {A Y Y₀ R : ℝ → ℂ}
    (hA : CuspAmplitude η C_A A) (hY : CuspProfile α C_Y Y Y₀ R) :
    Integrable (fun τ : ℝ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * A τ * Y (c ^ (1 / 3 : ℝ) * τ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hY_int, _⟩ := cusp_Y_integrable hα0 hCY hY
  have hc_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hY_scaled : Integrable (fun τ : ℝ => Y (c ^ (1 / 3 : ℝ) * τ)) :=
    hY_int.comp_mul_left' hc_pos.ne'
  have hc1 : Continuous (fun τ : ℝ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * A τ) :=
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.mul (contDiff_edgePhi L).continuous)))).mul
      hA.contDiff.continuous
  have hCA : 0 ≤ C_A := by
    have hA00 := hA.deriv_bound 0 (by omega) 0
    simp only [iteratedDeriv_zero, abs_zero, mul_zero, Real.exp_zero, mul_one] at hA00
    exact (norm_nonneg _).trans hA00
  refine (hY_scaled.norm.const_mul C_A).mono' (hc1.aestronglyMeasurable.mul hY_scaled.aestronglyMeasurable) ?_
  filter_upwards with τ
  rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hA0 := hA.deriv_bound 0 (by omega) τ
  simp only [iteratedDeriv_zero] at hA0
  have hexp : Real.exp (-η * |τ|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg τ])
  exact mul_le_mul_of_nonneg_right (hA0.trans (mul_le_of_le_one_right hCA hexp)) (norm_nonneg _)

private lemma shift_rpow_factor {c L p : ℝ} (hc : 0 < c) (hL : 0 ≤ L) (_hp : 0 ≤ p) :
    (1 + c ^ (2 / 3 : ℝ) * L) ^ (-p) =
      c ^ (-(2 / 3 * p : ℝ)) * (L + c ^ (-(2 / 3 : ℝ))) ^ (-p) := by
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hc_m23 : 0 < c ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have heq : 1 + c ^ (2 / 3 : ℝ) * L = c ^ (2 / 3 : ℝ) * (L + c ^ (-(2 / 3 : ℝ))) := by
    have hmul : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hc]; simp
    calc 1 + c ^ (2 / 3 : ℝ) * L = c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) + c ^ (2 / 3 : ℝ) * L := by rw [hmul]
      _ = _ := by ring
  rw [heq, Real.mul_rpow hc23.le (by linarith), ← Real.rpow_mul hc.le]
  congr 2; ring

lemma ctWg1_normDensity_split :
    ∃ c₀ : ℝ, 64 ≤ c₀ ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      normDensity (ctWg1 ε c) c ξ = normDensity (wg1PartA ε c) c ξ + normDensity (wg1PartB ε c) c ξ := by
  obtain ⟨cA, CA, hcA64, _, hAA⟩ := wg1AmpA_cuspAmplitude
  obtain ⟨cB, CB, hcB64, _, hAB⟩ := wg1AmpB_cuspAmplitude
  obtain ⟨CYA, hCYA0, hYA⟩ := wg1YA_cuspProfile
  obtain ⟨CYB, hCYB0, hYB⟩ := wg1YB_cuspProfile
  refine ⟨max cA cB, le_max_of_le_left hcA64, fun {ε c ξ} hε hc hξ => ?_⟩
  have hcA : cA ≤ c := (le_max_left cA cB).trans hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hiA : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I)) := by
    rw [show (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I)) =
      _ from funext (wg1PartA_edge_eq hε hc0 hξ)]
    exact cuspEdge_integrable (by norm_num) (by positivity) hCYA0 hc1 (hAA hε hcA) hYA
  have hiB : Integrable (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartB ε c ((τ : ℂ) * Complex.I)) := by
    rw [show (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartB ε c ((τ : ℂ) * Complex.I)) =
      _ from funext (wg1PartB_edge_eq hε hc0 hξ)]
    exact cuspEdge_integrable (by norm_num) (by positivity) hCYB0 hc1 (hAB hε ((le_max_right cA cB).trans hc)) hYB
  unfold normDensity
  have hpt : (fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * ctWg1 ε c ((τ : ℂ) * Complex.I)) =
      fun τ : ℝ => mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartA ε c ((τ : ℂ) * Complex.I) +
        mellinK0 c ((τ : ℂ) * Complex.I) ξ * wg1PartB ε c ((τ : ℂ) * Complex.I) := funext fun τ => by
    rw [ctWg1_eq_add]; ring
  rw [hpt, integral_add hiA hiB, Complex.add_re]
  ring

theorem ctWg1_partB_bound :
    ∃ c₀ C_B : ℝ, 64 ≤ c₀ ∧ 0 ≤ C_B ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      |normDensity (wg1PartB ε c) c ξ| ≤ C_B * c ^ (-(2 / 3 : ℝ)) ∧
        (0 ≤ Real.log (Real.pi ^ 2 * ξ) →
          |normDensity (wg1PartB ε c) c ξ| ≤
            C_B * c ^ (-(5 / 3 : ℝ)) * (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨cB, CB, hcB64, _, hAB⟩ := wg1AmpB_cuspAmplitude
  obtain ⟨CYB, hCYB0, hYB⟩ := wg1YB_cuspProfile
  obtain ⟨K, hK0, hcusp⟩ := fct_cusp_edge (α := 1 / 2) (η := Real.pi / 8) (C_A := 1) (C_Y := CYB)
    (by norm_num) (by norm_num) (by positivity) zero_le_one hCYB0
  let CB1 : ℝ := max CB 1
  have hCB1 : 0 < CB1 := by positivity
  refine ⟨cB, K * CB1, hcB64, mul_nonneg hK0 hCB1.le, fun {ε c ξ} hε hc hξ => ?_⟩
  have hc0 : 0 < c := by linarith [hcB64.trans hc]
  have hc1 : 1 ≤ c := by linarith
  let s : ℝ := CB1 * c ^ (-(2 / 3 : ℝ))
  have hs0 : 0 < s := mul_pos hCB1 (Real.rpow_pos_of_pos hc0 _)
  let A' : ℝ → ℂ := fun τ => ((s⁻¹ : ℝ) : ℂ) * wg1AmpB ε c τ
  have hAB_c := hAB hε hc
  have hA' : CuspAmplitude (Real.pi / 8) 1 A' :=
    { contDiff := contDiff_const.mul hAB_c.contDiff
      deriv_bound := fun j hj τ => by
        rw [show A' = ((s⁻¹ : ℝ) : ℂ) • wg1AmpB ε c from rfl, iteratedDeriv_const_smul_field, norm_smul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
        have hbd := hAB_c.deriv_bound j hj τ
        calc s⁻¹ * ‖iteratedDeriv j (wg1AmpB ε c) τ‖
            ≤ s⁻¹ * (CB * c ^ (-(2 / 3 : ℝ)) * Real.exp (-(Real.pi / 8) * |τ|)) :=
              mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hs0.le)
          _ ≤ s⁻¹ * (s * Real.exp (-(Real.pi / 8) * |τ|)) := by
              have hcb : CB ≤ CB1 := le_max_left CB 1
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcb (Real.rpow_pos_of_pos hc0 _).le)
                (Real.exp_pos _).le) (inv_nonneg.mpr hs0.le)
          _ = (s⁻¹ * s) * Real.exp (-(Real.pi / 8) * |τ|) := by ring
          _ = 1 * Real.exp (-(Real.pi / 8) * |τ|) := by rw [inv_mul_cancel₀ hs0.ne'] }
  have hJ_eq : ∀ L : ℝ, cuspEdgeJ c L (wg1AmpB ε c) wg1YB = (s : ℂ) * cuspEdgeJ c L A' wg1YB := fun L => by
    unfold cuspEdgeJ
    have hpt : (fun τ : ℝ => Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * wg1AmpB ε c τ *
        wg1YB (c ^ (1 / 3 : ℝ) * τ)) =
        fun τ : ℝ => (s : ℂ) * (Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * A' τ *
          wg1YB (c ^ (1 / 3 : ℝ) * τ)) := by
      funext τ; dsimp only [A']
      have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
      calc Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) * wg1AmpB ε c τ * wg1YB (c ^ (1 / 3 : ℝ) * τ)
          = (s : ℂ) * ((s⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) *
              wg1AmpB ε c τ * wg1YB (c ^ (1 / 3 : ℝ) * τ)) := by
            rw [Complex.ofReal_inv, mul_inv_cancel₀ hsC, one_mul]
        _ = (s : ℂ) * (Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) *
              (((s⁻¹ : ℝ) : ℂ) * wg1AmpB ε c τ) * wg1YB (c ^ (1 / 3 : ℝ) * τ)) := by ring
    rw [hpt, integral_const_mul]; ring
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ)
  have hnorm_nd : |normDensity (wg1PartB ε c) c ξ| ≤ s * ‖cuspEdgeJ c L A' wg1YB‖ := by
    rw [wg1PartB_normDensity hε hc0 hξ, hJ_eq L]
    have hre : |(cuspEdgeJ c L A' wg1YB).re| ≤ ‖cuspEdgeJ c L A' wg1YB‖ := Complex.abs_re_le_norm _
    rw [show ((s : ℂ) * cuspEdgeJ c L A' wg1YB).re = s * (cuspEdgeJ c L A' wg1YB).re by simp,
      abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left hre hs0.le
  have hcJ := hcusp c hc1 A' wg1YB (fun _ => 0) wg1YB hA' hYB
  refine ⟨?_, fun hL => ?_⟩
  · calc |normDensity (wg1PartB ε c) c ξ| ≤ s * ‖cuspEdgeJ c L A' wg1YB‖ := hnorm_nd
      _ ≤ s * K := mul_le_mul_of_nonneg_left (hcJ.1 L) hs0.le
      _ = (K * CB1) * c ^ (-(2 / 3 : ℝ)) := by dsimp only [s]; ring
  · have hrp := hcJ.2 L hL
    have hsh := shift_rpow_factor (p := 3 / 2) hc0 hL (by norm_num)
    have hrp' : (1 + c ^ (2 / 3 : ℝ) * L) ^ (-(1 / 2 : ℝ) - 1) =
        c ^ (-(1 : ℝ)) * (L + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℝ) - 1) = -(3 / 2 : ℝ) by ring, hsh]; norm_num
    calc |normDensity (wg1PartB ε c) c ξ| ≤ s * ‖cuspEdgeJ c L A' wg1YB‖ := hnorm_nd
      _ ≤ s * (K * (1 + c ^ (2 / 3 : ℝ) * L) ^ (-(1 / 2 : ℝ) - 1)) := mul_le_mul_of_nonneg_left hrp hs0.le
      _ = K * CB1 * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 : ℝ))) * (L + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ)) := by
          rw [hrp']; dsimp only [s]; ring
      _ = K * CB1 * c ^ (-(5 / 3 : ℝ)) * (L + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num

theorem ctWg1_partA_bound :
    ∃ c₀ C_A : ℝ, 64 ≤ c₀ ∧ 0 ≤ C_A ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      |normDensity (wg1PartA ε c) c ξ| ≤ C_A ∧
        (0 ≤ Real.log (Real.pi ^ 2 * ξ) →
          |normDensity (wg1PartA ε c) c ξ| ≤
            C_A * c ^ (-(5 / 3 : ℝ)) * (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(5 / 2 : ℝ))) := by
  obtain ⟨cA, CA, hcA64, hCA0, hAA⟩ := wg1AmpA_cuspAmplitude
  obtain ⟨CYA, hCYA0, hYA⟩ := wg1YA_cuspProfile
  obtain ⟨K, hK0, hcusp⟩ := fct_cusp_edge (α := 3 / 2) (η := Real.pi / 8) (C_A := CA) (C_Y := CYA)
    (by norm_num) (by norm_num) (by positivity) hCA0 hCYA0
  refine ⟨cA, K, hcA64, hK0, fun {ε c ξ} hε hc hξ => ?_⟩
  have hc0 : 0 < c := by linarith [hcA64.trans hc]
  have hc1 : 1 ≤ c := by linarith
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ)
  have hnorm_nd : |normDensity (wg1PartA ε c) c ξ| ≤ ‖cuspEdgeJ c L (wg1AmpA ε c) wg1YA‖ := by
    rw [wg1PartA_normDensity hε hc0 hξ]
    exact Complex.abs_re_le_norm _
  have hcJ := hcusp c hc1 (wg1AmpA ε c) wg1YA _ _ (hAA hε hc) hYA
  refine ⟨hnorm_nd.trans (hcJ.1 L), fun hL => ?_⟩
  have hsh := shift_rpow_factor (p := 5 / 2) hc0 hL (by norm_num)
  have hrp' : (1 + c ^ (2 / 3 : ℝ) * L) ^ (-(3 / 2 : ℝ) - 1) =
      c ^ (-(5 / 3 : ℝ)) * (L + c ^ (-(2 / 3 : ℝ))) ^ (-(5 / 2 : ℝ)) := by
    rw [show (-(3 / 2 : ℝ) - 1) = -(5 / 2 : ℝ) by ring, hsh]; norm_num
  calc |normDensity (wg1PartA ε c) c ξ| ≤ ‖cuspEdgeJ c L (wg1AmpA ε c) wg1YA‖ := hnorm_nd
    _ ≤ K * (1 + c ^ (2 / 3 : ℝ) * L) ^ (-(3 / 2 : ℝ) - 1) := hcJ.2 L hL
    _ = K * c ^ (-(5 / 3 : ℝ)) * (L + c ^ (-(2 / 3 : ℝ))) ^ (-(5 / 2 : ℝ)) := by rw [hrp']; ring

/-- **`(fct:hg1-mac)`**: macroscopic bound for `normDensity (ctWg1 ε c) c ξ` on `L = log(π² ξ) > 0`. -/
theorem ctWg1_mac_bound :
    ∃ c₀ C : ℝ, 64 ≤ c₀ ∧ 0 ≤ C ∧ ∀ {ε c ξ : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c → 0 < ξ →
      0 < Real.log (Real.pi ^ 2 * ξ) →
        |normDensity (ctWg1 ε c) c ξ| ≤
          C * c ^ (-(5 / 3 : ℝ)) *
            (Real.log (Real.pi ^ 2 * ξ) ^ (-(5 / 2 : ℝ)) + Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨cS, hcS64, hsp⟩ := ctWg1_normDensity_split
  obtain ⟨cA, CA, hcA64, hCA0, hA⟩ := ctWg1_partA_bound
  obtain ⟨cB, CB, hcB64, hCB0, hB⟩ := ctWg1_partB_bound
  refine ⟨max cS (max cA cB), CA + CB, le_max_of_le_left hcS64, add_nonneg hCA0 hCB0,
    fun {ε c ξ} hε hc hξ hL => ?_⟩
  have hc0 : 0 < c := by linarith [hcS64.trans ((le_max_left cS _).trans hc)]
  rw [hsp hε ((le_max_left cS _).trans hc) hξ]
  have hLA := (hA hε ((le_max_left cA cB).trans ((le_max_right cS _).trans hc)) hξ).2 hL.le
  have hLB := (hB hε ((le_max_right cA cB).trans ((le_max_right cS _).trans hc)) hξ).2 hL.le
  have hL_le : Real.log (Real.pi ^ 2 * ξ) ≤ Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ)) :=
    le_add_of_nonneg_right (Real.rpow_pos_of_pos hc0 _).le
  have hrpA : (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(5 / 2 : ℝ)) ≤
      Real.log (Real.pi ^ 2 * ξ) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hL hL_le (by norm_num)
  have hrpB : (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ)) ≤
      Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hL hL_le (by norm_num)
  have hCA_c : CA * c ^ (-(5 / 3 : ℝ)) * (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(5 / 2 : ℝ)) ≤
      (CA + CB) * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(5 / 2 : ℝ)) := by
    have hnn : 0 ≤ c ^ (-(5 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
    calc CA * c ^ (-(5 / 3 : ℝ)) * (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(5 / 2 : ℝ))
        ≤ CA * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(5 / 2 : ℝ)) := by gcongr
      _ ≤ (CA + CB) * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(5 / 2 : ℝ)) := by
          gcongr; linarith
  have hCB_c : CB * c ^ (-(5 / 3 : ℝ)) * (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ)) ≤
      (CA + CB) * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
    have hnn : 0 ≤ c ^ (-(5 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc0 _).le
    calc CB * c ^ (-(5 / 3 : ℝ)) * (Real.log (Real.pi ^ 2 * ξ) + c ^ (-(2 / 3 : ℝ))) ^ (-(3 / 2 : ℝ))
        ≤ CB * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by gcongr
      _ ≤ (CA + CB) * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
          gcongr; linarith
  calc |normDensity (wg1PartA ε c) c ξ + normDensity (wg1PartB ε c) c ξ|
      ≤ |normDensity (wg1PartA ε c) c ξ| + |normDensity (wg1PartB ε c) c ξ| := abs_add_le _ _
    _ ≤ (CA + CB) * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(5 / 2 : ℝ)) +
        (CA + CB) * c ^ (-(5 / 3 : ℝ)) * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := add_le_add (hLA.trans hCA_c) (hLB.trans hCB_c)
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.ctWg1_partB_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_partB_bound

/-- info: 'FormalResearch.SignUncertainty.ctWg1_partA_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_partA_bound

/-- info: 'FormalResearch.SignUncertainty.ctWg1_mac_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctWg1_mac_bound

end FormalResearch.SignUncertainty