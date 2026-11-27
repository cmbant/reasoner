/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctLeftEdgeBound
public import FormalResearch.SignUncertainty.FctRayShift
public import FormalResearch.SignUncertainty.FctSplittingCauchyLogLog
public import FormalResearch.SignUncertainty.FctSplittingRest
public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Unconditional `log log` bound and `FctSplittingStmt` (`fct:splitting` (2))

Paper I (`constant_terms_five.tex`), Lemma FCT.6 (`fct:splitting` (2)):
combines the uniform left-edge bound `fctPhiC_left_edge_bound` (`Re ζ = 0`),
the unconditional interior descent bound `fctDescent_uncond` (`Re ζ = 5/16`),
and linear-in-`|Im ζ|` ray growth on `0 < Re ζ ≤ 5/16` (via `fctRay_shift_of_solve`
and `fctWarpKA_left_ray_bound`) in `PhragmenLindelof.vertical_strip` to prove
a uniform bound on `‖Φ_c(ζ)‖` across `0 ≤ Re ζ ≤ 5/16`.

Feeding this into `fctPhiHat_loglog_of_left` discharges `FctSplittingRestStmt`
and `FctSplittingStmt (fctPhiHat h)` unconditionally for `K₄ ≥ 1` and any
`h : FctWarpSolveStmt K4`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

private lemma fctPhiC_conj_band {K4 ε c L1 α : ℝ}
    (hD_conj : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    fctPhiC K4 ε c L1 α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctPhiC K4 ε c L1 α ζ) := by
  have hS : ζ ∈ closedStrip := ⟨h0, h1.le⟩
  unfold fctPhiC
  rw [fctPsi_conj hD_conj h0 h1, hD_conj ζ hS, ctHG_conj ε hS]
  simp only [map_div₀, map_mul, Complex.conj_ofReal]

private lemma fctPhiC_eq_shift_div_rayN {K4 ε c L1 α : ℝ} {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2) :
    fctPhiC K4 ε c L1 α ζ =
      (c : ℂ) * (ζ * ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ζ)) /
        fctRayN K4 ε c L1 α ζ := by
  have hN : fctRayN K4 ε c L1 α ζ ≠ 0 := fctRayN_ne_zero h0 h1
  have hK0 : mellinK0 c ζ (fctXi1 L1) ≠ 0 := mellinK0_ne_zero c (by linarith) _
  have hD : fctDcompAt K4 c α ζ ≠ 0 := fctDcompAt_ne_zero ζ
  have hH : ctHG ε ζ ≠ 0 := ctHG_ne_zero_of_band ε h0 h1
  unfold fctPhiC fctPsi fctRayN fctWarpKA
  field_simp [hK0, hD, hH]

private lemma integral_exp_neg_Ioi_zero : ∫ s in Ioi (0 : ℝ), Real.exp (-s) = 1 := by
  have hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -Real.exp (-x)) (Real.exp (-s)) s := fun s _ => by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-s) * (-1)) s :=
      (hasDerivAt_id s).neg.exp
    exact ((h1.neg).congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => by simp)
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).congr_fun
      (fun x _ => by simp) measurableSet_Ioi
  have hlim : Tendsto (fun x : ℝ => -Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  have hI := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simpa using hI

/-- **Uniform left-strip bound on `Φ_c`** (`0 ≤ Re ζ ≤ 5/16`):
from `fctPhiC_left_edge_bound` on `Re ζ = 0`, `fctDescent_uncond` on `Re ζ = 5/16`,
and linear vertical-ray growth in `PhragmenLindelof.vertical_strip`. -/
theorem fctPhiC_left_strip_bound {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    ∃ c₀ M : ℝ, 0 ≤ M ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ ∈ closedStrip, ζ.re ≤ 5 / 16 →
        ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ ≤ M := by
  obtain ⟨c0_L, M_L, hML0, hL_bd⟩ := fctPhiC_left_edge_bound hK4 h
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0_D, hcD_fn⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨c0_s, hc0s1, hshift⟩ := fctRay_shift_of_solve hK4 h
  obtain ⟨C_l, c0_r, hCl0, hc0r1, hray_bd⟩ := fctWarpKA_left_ray_bound hK4 h
  obtain ⟨C_desc, c0_desc, hDesc⟩ := fctDescent_uncond hK4 h
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c₀ : ℝ := max (max (max c0_L c0_D) (max c0_s c0_r)) (max c0_desc 1) with hc₀
  set M : ℝ := max M_L (|C_desc| / Real.log 2 + 1) with hM
  refine ⟨c₀, M, le_trans hML0 (le_max_left _ _), fun ε c hε hc ζ hζ hζ_le => ?_⟩
  have hc1 : 1 ≤ c := hc.trans' ((le_max_right _ _).trans (le_max_right _ _))
  have hcpos : 0 < c := by linarith
  have hcL : c0_L ≤ c := hc.trans' (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  have hcD : c0_D ≤ c := hc.trans' (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _))
  have hcs : c0_s ≤ c := hc.trans' (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
  have hcr : c0_r ≤ c := hc.trans' (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _))
  have hc_desc : c0_desc ≤ c := hc.trans' ((le_max_left _ _).trans (le_max_right _ _))
  have hcD' := hcD_fn ε c hε hcD
  set L1 : ℝ := fctWarpL1 h ε c
  set α : ℝ := fctWarpAlpha h ε c
  -- Linear growth on the open strip `0 < Re ζ < 5/16`
  set K_box_set : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 5 / 16 ∧ |w.im| ≤ 1}
  have hKbox_compact : IsCompact K_box_set := by
    have hcl : IsClosed K_box_set :=
      (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
    refine (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset hcl fun w hw => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_nonneg hw.1] at h1
    linarith [hw.2.1, hw.2.2]
  have hphi_cont_left : ContinuousOn (fctPhiC K4 ε c L1 α) {w : ℂ | w ∈ closedStrip ∧ w.re < 7 / 16} :=
    fctPhiC_continuousOn_left hcpos hcD'.cont hcD'.bd
  have hKbox_sub : K_box_set ⊆ {w : ℂ | w ∈ closedStrip ∧ w.re < 7 / 16} := fun w hw =>
    ⟨⟨hw.1, by linarith [hw.2.1]⟩, by linarith [hw.2.1]⟩
  obtain ⟨M_box, hMbox⟩ := hKbox_compact.exists_bound_of_continuousOn (hphi_cont_left.mono hKbox_sub)
  set K_lin : ℝ := max (c * C_l) |M_box|
  have hKlin0 : 0 ≤ K_lin := le_trans (abs_nonneg M_box) (le_max_right _ _)
  have hpos_im_lin : ∀ w : ℂ, 0 < w.re → w.re ≤ 5 / 16 → 1 ≤ w.im →
      ‖fctPhiC K4 ε c L1 α w‖ ≤ c * C_l * (1 + w.im) := fun w hw0 hw1 hwim => by
    have hsh := hshift ε c hε hcs w.re w.im hw0 (by linarith) (by linarith)
    have hw_eq : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := by apply Complex.ext <;> simp
    rw [hw_eq] at hsh
    have hw_half : w.re < 1 / 2 := by linarith
    have hN0 : fctRayN K4 ε c L1 α w ≠ 0 := fctRayN_ne_zero hw0 hw_half
    have hNpos : 0 < ‖fctRayN K4 ε c L1 α w‖ := norm_pos_iff.mpr hN0
    set B_ray : ℝ := C_l * (1 + w.im) * ‖fctRayN K4 ε c L1 α w‖
    have hB0 : 0 ≤ B_ray := by positivity
    have hcont_ray : ContinuousOn (fun s : ℝ => fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)) (Ici 0) :=
      (fctWarpKA_continuousOn hcpos hcD'.cont).comp (by fun_prop) fun s _ =>
        ⟨by simp; linarith, by simp; linarith, fun h0 => by
          have := congr_arg Complex.re h0; simp at this; linarith⟩
    have hmaj : ∀ s : ℝ, 0 ≤ s → ‖fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)‖ ≤ B_ray * Real.exp (-s) := by
      intro s hs
      have hb0 := hray_bd ε c hε hcr w hw0.le (by linarith) hwim s hs
      have hexp_s : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
      have hpoly : 1 + w.im + s ≤ (1 + w.im) * Real.exp s := by
        have h1w : (1 : ℝ) ≤ 1 + w.im := by linarith
        calc 1 + w.im + s ≤ (1 + w.im) * (1 + s) := by nlinarith
          _ ≤ (1 + w.im) * Real.exp s := mul_le_mul_of_nonneg_left hexp_s (by linarith)
      have hexp2 : Real.exp s * Real.exp (-2 * s) = Real.exp (-s) := by
        rw [← Real.exp_add]; congr 1; ring
      calc ‖fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)‖
          ≤ C_l * (1 + w.im + s) * Real.exp (-2 * s) * ‖fctRayN K4 ε c L1 α w‖ := hb0
        _ ≤ C_l * ((1 + w.im) * Real.exp s) * Real.exp (-2 * s) * ‖fctRayN K4 ε c L1 α w‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hCl0) (Real.exp_pos _).le)
              (norm_nonneg _)
        _ = B_ray * (Real.exp s * Real.exp (-2 * s)) := by simp only [B_ray]; ring
        _ = B_ray * Real.exp (-s) := by rw [hexp2]
    have hdom_int : IntegrableOn (fun s : ℝ => B_ray * Real.exp (-s)) (Ioi 0) :=
      ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).congr_fun
        (fun x _ => by simp) measurableSet_Ioi).const_mul B_ray
    have hray_int : IntegrableOn (fun s : ℝ => fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)) (Ioi 0) :=
      hdom_int.mono' ((hcont_ray.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact hmaj s hs.le)
    have hI_bd : ‖∫ s in Ioi (0 : ℝ), fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)‖ ≤ B_ray := by
      have h1 := norm_integral_le_integral_norm (f := fun s : ℝ => fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I))
        (μ := volume.restrict (Ioi 0))
      have h2 : (∫ s in Ioi (0 : ℝ), ‖fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)‖) ≤
          ∫ s in Ioi (0 : ℝ), B_ray * Real.exp (-s) := by
        refine setIntegral_mono_on hray_int.norm hdom_int measurableSet_Ioi fun s hs => hmaj s hs.le
      have h3 : ∫ s in Ioi (0 : ℝ), B_ray * Real.exp (-s) = B_ray := by
        rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
      exact h1.trans (h2.trans_eq h3)
    change w * ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * w) =
      -(Complex.I * ∫ s in Ioi (0 : ℝ), fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)) at hsh
    rw [fctPhiC_eq_shift_div_rayN hw0 hw_half, hsh, norm_div, norm_mul, norm_neg, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    calc c * ‖∫ s in Ioi (0 : ℝ), fctWarpKA K4 ε c L1 α (w + (s : ℂ) * Complex.I)‖ / ‖fctRayN K4 ε c L1 α w‖
        ≤ c * (C_l * (1 + w.im) * ‖fctRayN K4 ε c L1 α w‖) / ‖fctRayN K4 ε c L1 α w‖ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hI_bd hcpos.le) (norm_nonneg _)
      _ = c * C_l * (1 + w.im) := by field_simp [hNpos.ne']
  have hlin_strip : ∀ w : ℂ, 0 < w.re → w.re ≤ 5 / 16 →
      ‖fctPhiC K4 ε c L1 α w‖ ≤ K_lin * (1 + |w.im|) := fun w hw0 hw1 => by
    rcases le_or_gt 1 |w.im| with him | him
    · rcases le_total 0 w.im with hwim | hwim
      · rw [abs_of_nonneg hwim] at him ⊢
        exact (hpos_im_lin w hw0 hw1 him).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · rw [abs_of_nonpos hwim] at him ⊢
        have hconj := fctPhiC_conj_band (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α)
          hcD'.conj hw0.le (by linarith)
        rw [← RCLike.norm_conj (fctPhiC K4 ε c L1 α w), ← hconj]
        exact (hpos_im_lin (starRingEnd ℂ w) (by simpa using hw0) (by simpa using hw1) (by simpa using him)).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by simp; linarith))
    · have hw_mem : w ∈ K_box_set := ⟨hw0.le, hw1, him.le⟩
      have hb := (hMbox w hw_mem).trans (le_abs_self M_box)
      have h1y : (1 : ℝ) ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
      calc ‖fctPhiC K4 ε c L1 α w‖ ≤ |M_box| := hb
        _ ≤ |M_box| * (1 + |w.im|) := le_mul_of_one_le_right (abs_nonneg _) h1y
        _ ≤ K_lin * (1 + |w.im|) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith [abs_nonneg w.im])
  -- Apply `PhragmenLindelof.vertical_strip` on `0 ≤ Re ≤ 5/16`
  have hdiffcl : DiffContOnCl ℂ (fctPhiC K4 ε c L1 α) (Complex.re ⁻¹' Ioo 0 (5 / 16)) := by
    refine ⟨?_, ?_⟩
    · have hsub : Complex.re ⁻¹' Ioo (0 : ℝ) (5 / 16) ⊆ {w : ℂ | 0 < w.re ∧ w.re < 1 / 2} :=
        fun w hw => ⟨hw.1, by linarith [hw.2]⟩
      have hPhi_eq : fctPhiC K4 ε c L1 α = fun w => fctFint K4 ε c L1 α w + 1 := by
        ext w; unfold fctFint; ring
      rw [hPhi_eq]
      exact ((fctFint_differentiableOn_band hcpos hcD'.hol hcD'.cont hcD'.bd).mono hsub).add_const 1
    · set Kcl : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 5 / 16}
      have hKcl_closed : IsClosed Kcl :=
        (isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)
      have hcl_sub : closure (Complex.re ⁻¹' Ioo (0 : ℝ) (5 / 16)) ⊆ Kcl :=
        closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) hKcl_closed
      have hKcl_sub : Kcl ⊆ {w : ℂ | w ∈ closedStrip ∧ w.re < 7 / 16} := fun w hw =>
        ⟨⟨hw.1, by linarith [hw.2]⟩, by linarith [hw.2]⟩
      exact hphi_cont_left.mono (hcl_sub.trans hKcl_sub)
  have hgrowth : ∃ c_pl < Real.pi / (5 / 16 - 0), ∃ B,
      fctPhiC K4 ε c L1 α =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo 0 (5 / 16))]
        fun z => Real.exp (B * Real.exp (c_pl * |z.im|)) := by
    refine ⟨(1 : ℝ), ?_, K_lin, Asymptotics.IsBigO.of_bound 1 ?_⟩
    · rw [sub_zero, lt_div_iff₀ (by norm_num : (0 : ℝ) < 5 / 16)]
      linarith [Real.pi_gt_three]
    · rw [Filter.eventually_inf_principal]
      refine Filter.Eventually.of_forall fun z hz => ?_
      rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hlin := hlin_strip z hz.1 hz.2.le
      have hexp1 : 1 + |z.im| ≤ Real.exp |z.im| := by linarith [Real.add_one_le_exp |z.im|]
      have hexp2 : K_lin * Real.exp |z.im| ≤ Real.exp (K_lin * Real.exp (1 * |z.im|)) := by
        rw [one_mul]; linarith [Real.add_one_le_exp (K_lin * Real.exp |z.im|)]
      exact hlin.trans ((mul_le_mul_of_nonneg_left hexp1 hKlin0).trans hexp2)
  have hleft_edge : ∀ z : ℂ, z.re = 0 → ‖fctPhiC K4 ε c L1 α z‖ ≤ M := fun z hz => by
    have hz_eq : z = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz]
    rw [hz_eq]
    exact (hL_bd ε c hε hcL z.im).trans (le_max_left _ _)
  have hright_edge : ∀ z : ℂ, z.re = 5 / 16 → ‖fctPhiC K4 ε c L1 α z‖ ≤ M := fun z hz => by
    have hz_eq : z = ((5 / 16 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp [hz]
    have hc_inv_le : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
    have hlog_le : Real.log 2 ≤ Real.log (2 + |z.im|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
    have hF_bd := hDesc ε c hε hc_desc (5 / 16) z.im le_rfl (by norm_num)
    rw [← hz_eq] at hF_bd
    have hphi_eq : fctPhiC K4 ε c L1 α z = fctFint K4 ε c L1 α z + 1 := by
      unfold fctFint; ring
    have hnorm : ‖fctPhiC K4 ε c L1 α z‖ ≤ |C_desc| / Real.log 2 + 1 := by
      rw [hphi_eq]
      calc ‖fctFint K4 ε c L1 α z + 1‖
          ≤ ‖fctFint K4 ε c L1 α z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ C_desc * c⁻¹ / Real.log (2 + |z.im|) + 1 := by
            have := add_le_add_left hF_bd 1
            simpa only [norm_one] using this.trans_eq (by ring)
        _ ≤ |C_desc| * 1 / Real.log 2 + 1 := by
            have hc_abs : C_desc * c⁻¹ ≤ |C_desc| * 1 :=
              mul_le_mul (le_abs_self C_desc) hc_inv_le (by positivity) (abs_nonneg C_desc)
            have hdiv : C_desc * c⁻¹ / Real.log (2 + |z.im|) ≤ |C_desc| * 1 / Real.log 2 := by
              by_cases hCd : 0 ≤ C_desc * c⁻¹
              · exact div_le_div₀ (by positivity) hc_abs hlog2_pos hlog_le
              · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hCd)
                  (Real.log_nonneg (by linarith [abs_nonneg z.im]))).trans (by positivity)
            linarith
        _ = |C_desc| / Real.log 2 + 1 := by ring
    exact hnorm.trans (le_max_right _ _)
  exact PhragmenLindelof.vertical_strip (a := 0) (b := 5 / 16) (f := fctPhiC K4 ε c L1 α)
    hdiffcl hgrowth hleft_edge hright_edge hζ.1 hζ_le

/-- **Unconditional `FctSplittingRestStmt h`** (`fct:splitting` (2), `log log` growth on `S̄`). -/
theorem fctSplittingRest_uncond {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    FctSplittingRestStmt h := by
  obtain ⟨c0l, Ml, hMl0, hl⟩ := fctPhiC_left_strip_bound hK4 h
  have hll4_pos : 0 < Real.log (Real.log 4) := log_log_four_pos
  have hleft_ll : ∃ c₀ M : ℝ, 0 ≤ M ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      ∀ ζ ∈ closedStrip, ζ.re ≤ 5 / 16 →
        ‖fctPhiC K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ζ‖ ≤
          M * Real.log (Real.log (4 + |ζ.im|)) := by
    refine ⟨c0l, Ml / Real.log (Real.log 4), by positivity, fun ε c hε hc ζ hζ hζ_le => ?_⟩
    have h1 : Ml = (Ml / Real.log (Real.log 4)) * Real.log (Real.log 4) := by field_simp [hll4_pos.ne']
    have h2 : (Ml / Real.log (Real.log 4)) * Real.log (Real.log 4) ≤
        (Ml / Real.log (Real.log 4)) * Real.log (Real.log (4 + |ζ.im|)) :=
      mul_le_mul_of_nonneg_left log_log_four_le (by positivity)
    exact (hl ε c hε hc ζ hζ hζ_le).trans ((le_of_eq h1).trans h2)
  obtain ⟨c₀, M, hM0, hmain⟩ := fctPhiHat_loglog_of_left hK4 (fctDescent_uncond hK4 h) hleft_ll
  exact ⟨c₀, fun ε c hε hc => ⟨⟨M, hM0, fun ζ hζ => hmain ε c hε hc ζ hζ⟩⟩⟩

/-- **Unconditional `FctSplittingStmt (fctPhiHat h)`** (`fct:splitting` (1)-(2)) from `fct:warp-asymp` (1) (`K₄ ≥ 1`). -/
theorem fctSplitting_uncond {K4 : ℝ} (hK4 : 1 ≤ K4) (h : FctWarpSolveStmt K4) :
    FctSplittingStmt (fctPhiHat h) :=
  fctSplitting_of_rest hK4 (fctDescent_uncond hK4 h) (fctSplittingRest_uncond hK4 h)

/-- info: 'FormalResearch.SignUncertainty.fctPhiC_left_strip_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiC_left_strip_bound

/-- info: 'FormalResearch.SignUncertainty.fctSplittingRest_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplittingRest_uncond

/-- info: 'FormalResearch.SignUncertainty.fctSplitting_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplitting_uncond

end FormalResearch.SignUncertainty
