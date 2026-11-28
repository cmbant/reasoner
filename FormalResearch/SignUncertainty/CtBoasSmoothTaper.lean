/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasSfSmooth
public import FormalResearch.SignUncertainty.CtBoasLmin
public import FormalResearch.SignUncertainty.CtTransBand

/-!
# `HasDerivAt` and `C^{1,1}` bounds for `ctTaper ε c R` (`ct:boas` Step 3)

Provides `taperWDeriv`, `hasDerivAt_taperW`, `taperWDeriv_bounds`, and the main theorem
`ctTaper_hasDerivAt_and_lip`: for `c₁ ≤ c₁₀` and `c ≥ c₀(c₁)`, `ctTaper ε c R` has derivative
`taperGrad` on `(0, ∞)` vanishing above `Λ`, bounded by `C₀ L^{12}` / `C₁ L^{11}` on `[ctLv0 c / 4, Λ]`,
and `C₂`-Lipschitz on `[ctLv0 c / 4, ∞)`.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtCfu

/-! ### `HasDerivAt` and `C^{1,1}` bound for `taperW R` -/

/-- Derivative of `taperW R v` (`0` for `v ≤ 0` or `v ≥ R`, `24/R (v/R)^{11} (1 - (v/R)^{12})` on `(0, R)`). -/
noncomputable def taperWDeriv (R v : ℝ) : ℝ :=
  if 0 < v ∧ v < R then (24 / R) * (v / R) ^ 11 * (1 - (v / R) ^ 12) else 0

lemma hasDerivAt_taperW {R : ℝ} (hR : 0 < R) (v : ℝ) :
    HasDerivAt (taperW R) (taperWDeriv R v) v := by
  have hpoly : ∀ u : ℝ, HasDerivAt (fun t => 1 - (1 - (t / R) ^ 12) ^ 2)
      ((24 / R) * (u / R) ^ 11 * (1 - (u / R) ^ 12)) u := fun u => by
    have h1 : HasDerivAt (fun t : ℝ => t / R) R⁻¹ u :=
      ((hasDerivAt_id u).div_const R).congr_deriv (one_div R)
    have h2 : HasDerivAt (fun t : ℝ => (t / R) ^ 12) (12 * (u / R) ^ 11 * R⁻¹) u := by
      have hraw := (hasDerivAt_pow 12 (u / R)).comp u h1; exact hraw
    have h3 : HasDerivAt (fun t : ℝ => 1 - (t / R) ^ 12) (-(12 * (u / R) ^ 11 * R⁻¹)) u := h2.const_sub 1
    have h4 : HasDerivAt (fun t : ℝ => (1 - (t / R) ^ 12) ^ 2)
        (2 * (1 - (u / R) ^ 12) * (-(12 * (u / R) ^ 11 * R⁻¹))) u := by
      have hraw := (hasDerivAt_pow 2 (1 - (u / R) ^ 12)).comp u h3
      exact hraw.congr_deriv (by push_cast; ring)
    refine (h4.const_sub 1).congr_deriv ?_
    ring
  rcases lt_trichotomy v 0 with hv | hEq0 | hv
  · have hev : taperW R =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hv] with t ht
      unfold taperW taperX
      rw [min_eq_left (by linarith [Set.mem_Iio.1 ht]), max_eq_left (by linarith [Set.mem_Iio.1 ht])]
      norm_num
    have hnot : ¬ (0 < v ∧ v < R) := fun h => by linarith
    unfold taperWDeriv; simp only [hnot, ↓reduceIte]
    exact (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq hev
  · subst hEq0
    have hleft : HasDerivWithinAt (taperW R) 0 (Iic 0) 0 := by
      have hev : ∀ t ∈ Iic (0 : ℝ), taperW R t = 0 := fun t ht => by
        unfold taperW taperX
        rw [min_eq_left (by linarith [Set.mem_Iic.1 ht]), max_eq_left (Set.mem_Iic.1 ht)]
        norm_num
      exact ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt).congr hev (hev 0 le_rfl)
    have hright : HasDerivWithinAt (taperW R) 0 (Ici 0) 0 := by
      have hev : ∀ t ∈ Icc (0 : ℝ) R, taperW R t = 1 - (1 - (t / R) ^ 12) ^ 2 := fun t ht => by
        unfold taperW taperX; rw [min_eq_left ht.2, max_eq_right ht.1]; ring
      have h1 : HasDerivWithinAt (fun t => 1 - (1 - (t / R) ^ 12) ^ 2) 0 (Icc 0 R) 0 := by
        simpa using (hpoly 0).hasDerivWithinAt
      have h2 := h1.congr hev (hev 0 ⟨le_rfl, hR.le⟩)
      have hmem : Icc (0 : ℝ) R ∈ nhdsWithin (0 : ℝ) (Ici 0) := Icc_mem_nhdsGE_of_mem ⟨le_rfl, hR⟩
      exact h2.mono_of_mem_nhdsWithin hmem
    have hnot : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < R) := fun h => by linarith
    unfold taperWDeriv; simp only [hnot, ↓reduceIte]
    exact hasDerivWithinAt_univ.1 (by rw [← Iic_union_Ici]; exact hleft.union hright)
  · rcases lt_trichotomy v R with hvR | hEqR | hvR
    · have hev : taperW R =ᶠ[𝓝 v] fun t => 1 - (1 - (t / R) ^ 12) ^ 2 := by
        filter_upwards [Ioo_mem_nhds hv hvR] with t ht
        unfold taperW taperX
        rw [min_eq_left ht.2.le, max_eq_right ht.1.le]; ring
      unfold taperWDeriv; simp only [hv, hvR, and_self, ↓reduceIte]
      exact (hpoly v).congr_of_eventuallyEq hev
    · subst v
      have hleft : HasDerivWithinAt (taperW R) 0 (Iic R) R := by
        have hev : ∀ t ∈ Icc (0 : ℝ) R, taperW R t = 1 - (1 - (t / R) ^ 12) ^ 2 := fun t ht => by
          unfold taperW taperX; rw [min_eq_left ht.2, max_eq_right ht.1]; ring
        have h1 : HasDerivWithinAt (fun t => 1 - (1 - (t / R) ^ 12) ^ 2) 0 (Icc 0 R) R := by
          have hp := hpoly R
          have hz : (24 / R) * (R / R) ^ 11 * (1 - (R / R) ^ 12) = 0 := by
            rw [div_self hR.ne']; norm_num
          rw [hz] at hp; exact hp.hasDerivWithinAt
        have h2 := h1.congr hev (hev R ⟨hR.le, le_rfl⟩)
        have hmem : Icc (0 : ℝ) R ∈ nhdsWithin R (Iic R) := Icc_mem_nhdsLE_of_mem ⟨hR, le_rfl⟩
        exact h2.mono_of_mem_nhdsWithin hmem
      have hright : HasDerivWithinAt (taperW R) 0 (Ici R) R := by
        have hev : ∀ t ∈ Ici R, taperW R t = 1 := fun t ht => taperW_of_ge hR ht
        exact ((hasDerivAt_const R (1 : ℝ)).hasDerivWithinAt).congr hev (hev R le_rfl)
      have hnot : ¬ (0 < R ∧ R < R) := fun h => by linarith
      unfold taperWDeriv; simp only [hnot, ↓reduceIte]
      exact hasDerivWithinAt_univ.1 (by rw [← Iic_union_Ici]; exact hleft.union hright)
    · have hev : taperW R =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hvR] with t ht
        exact taperW_of_ge hR (Set.mem_Ioi.1 ht).le
      have hnot : ¬ (0 < v ∧ v < R) := fun h => by linarith
      unfold taperWDeriv; simp only [hnot, ↓reduceIte]
      exact (hasDerivAt_const v (1 : ℝ)).congr_of_eventuallyEq hev

lemma taperWDeriv_bounds {R : ℝ} (hR : 0 < R) :
    (∀ v, |taperWDeriv R v| ≤ 24 / R) ∧
    (∀ v, 0 ≤ v → v ≤ R → |taperWDeriv R v| ≤ 24 / R * (v / R) ^ 11) ∧
    (∀ v₁ v₂, |taperWDeriv R v₁ - taperWDeriv R v₂| ≤ 900 / R ^ 2 * |v₁ - v₂|) := by
  have h_pt : ∀ v, |taperWDeriv R v| ≤ 24 / R := fun v => by
    unfold taperWDeriv
    split_ifs with h
    · have h0 : 0 ≤ v / R := div_nonneg h.1.le hR.le
      have h1 : v / R ≤ 1 := (div_le_one hR).2 h.2.le
      have hp1 : (v / R) ^ 11 ≤ 1 := pow_le_one₀ h0 h1
      have hp2 : (v / R) ^ 12 ≤ 1 := pow_le_one₀ h0 h1
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg h0 11),
        abs_of_nonneg (by linarith)]
      calc 24 / R * (v / R) ^ 11 * (1 - (v / R) ^ 12) ≤ 24 / R * 1 * 1 := by
            gcongr; linarith [pow_nonneg h0 12]
        _ = 24 / R := by ring
    · rw [abs_zero]; positivity
  have h_pow : ∀ v, 0 ≤ v → v ≤ R → |taperWDeriv R v| ≤ 24 / R * (v / R) ^ 11 := fun v hv0 hvR => by
    unfold taperWDeriv
    split_ifs with h
    · have h0 : 0 ≤ v / R := div_nonneg hv0 hR.le
      have hp2 : (v / R) ^ 12 ≤ 1 := pow_le_one₀ h0 ((div_le_one hR).2 hvR)
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg h0 11),
        abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg h0 12])
    · rw [abs_zero]; positivity
  have h_lip : ∀ v₁ v₂, |taperWDeriv R v₁ - taperWDeriv R v₂| ≤ 900 / R ^ 2 * |v₁ - v₂| := by
    let p : ℝ → ℝ := fun v => (24 / R) * (v / R) ^ 11 * (1 - (v / R) ^ 12)
    let p' : ℝ → ℝ := fun v => (24 / R ^ 2) * (11 * (v / R) ^ 10 - 23 * (v / R) ^ 22)
    have hpd : ∀ v, HasDerivAt p (p' v) v := fun v => by
      have hp_eq : p = fun t => (24 / R) * ((t / R) ^ 11 - (t / R) ^ 23) := funext fun t => by
        dsimp only [p]; ring
      rw [hp_eq]
      have h1 : HasDerivAt (fun t : ℝ => t / R) R⁻¹ v :=
        ((hasDerivAt_id v).div_const R).congr_deriv (one_div R)
      have h11 : HasDerivAt (fun t : ℝ => (t / R) ^ 11) (11 * (v / R) ^ 10 * R⁻¹) v := by
        have hraw := (hasDerivAt_pow 11 (v / R)).comp v h1
        exact hraw.congr_deriv (by push_cast; ring)
      have h23 : HasDerivAt (fun t : ℝ => (t / R) ^ 23) (23 * (v / R) ^ 22 * R⁻¹) v := by
        have hraw := (hasDerivAt_pow 23 (v / R)).comp v h1
        exact hraw.congr_deriv (by push_cast; ring)
      refine ((h11.sub h23).const_mul (24 / R)).congr_deriv ?_
      dsimp only [p']; ring
    have hp'_bd : ∀ v ∈ Icc (0 : ℝ) R, ‖p' v‖ ≤ 900 / R ^ 2 := fun v hv => by
      have h0 : 0 ≤ v / R := div_nonneg hv.1 hR.le
      have h1 : v / R ≤ 1 := (div_le_one hR).2 hv.2
      rw [Real.norm_eq_abs]; dsimp only [p']
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have hsub : |11 * (v / R) ^ 10 - 23 * (v / R) ^ 22| ≤ 34 := by
        calc _ ≤ |11 * (v / R) ^ 10| + |23 * (v / R) ^ 22| := abs_sub _ _
          _ ≤ 11 * 1 + 23 * 1 := by
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
              gcongr <;> exact pow_le_one₀ h0 h1
          _ = 34 := by norm_num
      exact (mul_le_mul_of_nonneg_left hsub (by positivity)).trans (by
        rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg R))
    have hlip_icc : ∀ a b, a ∈ Icc (0 : ℝ) R → b ∈ Icc (0 : ℝ) R → |p a - p b| ≤ 900 / R ^ 2 * |a - b| :=
      fun a b ha hb => by
        have hmv := (convex_Icc (0 : ℝ) R).norm_image_sub_le_of_norm_deriv_le
          (fun v _ => (hpd v).differentiableAt)
          (fun v hv => by rw [(hpd v).deriv]; exact hp'_bd v hv) hb ha
        simpa [Real.norm_eq_abs, Real.dist_eq] using hmv
    have hp0 : p 0 = 0 := by simp [p]
    have hpR : p R = 0 := by simp [p, div_self hR.ne']
    have h_eq_clamp : ∀ v, taperWDeriv R v = p (max 0 (min v R)) := fun v => by
      unfold taperWDeriv
      split_ifs with h
      · rw [min_eq_left h.2.le, max_eq_right h.1.le]
      · rcases le_or_gt v 0 with hv0 | hv0
        · rw [min_eq_left (hv0.trans hR.le), max_eq_left hv0, hp0]
        · have hvR : R ≤ v := by push Not at h; exact h hv0
          rw [min_eq_right hvR, max_eq_right hR.le, hpR]
    intro v₁ v₂
    rw [h_eq_clamp v₁, h_eq_clamp v₂]
    have hm1 : max 0 (min v₁ R) ∈ Icc (0 : ℝ) R := ⟨le_max_left _ _, max_le hR.le (min_le_right _ _)⟩
    have hm2 : max 0 (min v₂ R) ∈ Icc (0 : ℝ) R := ⟨le_max_left _ _, max_le hR.le (min_le_right _ _)⟩
    have hclamp : |max 0 (min v₁ R) - max 0 (min v₂ R)| ≤ |v₁ - v₂| := by
      have h1 : |min v₁ R - min v₂ R| ≤ |v₁ - v₂| := by
        rcases le_total v₁ R with a1 | a1 <;> rcases le_total v₂ R with a2 | a2
        · rw [min_eq_left a1, min_eq_left a2]
        · rw [min_eq_left a1, min_eq_right a2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · rw [min_eq_right a1, min_eq_left a2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · rw [min_eq_right a1, min_eq_right a2, sub_self, abs_zero]; exact abs_nonneg _
      have h2 : |max 0 (min v₁ R) - max 0 (min v₂ R)| ≤ |min v₁ R - min v₂ R| := by
        rcases le_total 0 (min v₁ R) with a1 | a1 <;> rcases le_total 0 (min v₂ R) with a2 | a2
        · rw [max_eq_right a1, max_eq_right a2]
        · rw [max_eq_right a1, max_eq_left a2, sub_zero, abs_of_nonneg a1, abs_of_nonneg (by linarith)]
          linarith
        · rw [max_eq_left a1, max_eq_right a2, zero_sub, abs_neg, abs_of_nonneg a2, abs_of_nonpos (by linarith)]
          linarith
        · rw [max_eq_left a1, max_eq_left a2, sub_self, abs_zero]; exact abs_nonneg _
      exact h2.trans h1
    exact (hlip_icc _ _ hm1 hm2).trans (mul_le_mul_of_nonneg_left hclamp (by positivity))
  exact ⟨h_pt, h_pow, h_lip⟩

private lemma ctTaperV_formula_on {ε c R ρ M : ℝ} (hW : PsiWin ε ρ M) (hc3 : 3 ≤ c) (hcM : 2 * M ≤ c)
    (hlam : ctLam c * M ≤ 1 / 2) (hR1 : 1 ≤ R) (hRw : -ρ < ctMu c * (-R)) (hRA : R ≤ langerRadius c) :
    let Λ := ctTaperLam ε c R
    TaperBand ε c R ∧
    (∀ L ∈ Ioc 0 Λ, ctTaperV ε c L = -ctUhat ε c (-(ctVprime c L)) ∧
      Real.exp L - 1 ≤ 5e-4 ∧ 0 < ctVprime c L ∧ ctVprime c L ≤ ctRprime ε c R ∧
      -ρ < ctMu c * (-(ctVprime c L))) ∧
    ctTaperV ε c Λ = R := by
  have hc : 0 < c := by linarith
  have hK := langerScale_pos hc
  have hmu := ctMu_pos hc
  obtain ⟨u, hu, hv⟩ := exists_ctUhat_eq hW hc hlam hR1 hRw
  have hphi := ctPhi_eq hW hc hcM hRw hu hv
  have hr_eq : ctRprime ε c R = -u := by show -ctPhi ε c (-R) = -u; rw [hphi]
  have hr0 : 0 < ctRprime ε c R := by rw [hr_eq]; linarith [hu.2]
  have hrA : ctRprime ε c R ≤ langerRadius c := by
    have : ctRprime ε c R ≤ R := by rw [hr_eq]; linarith [hu.1]
    exact this.trans hRA
  obtain ⟨hE1, hE2, hE3⟩ := hankel_band_edge hc hr0 hrA
  have hLam : ctTaperLam ε c R = Real.log (Real.pi ^ 2 * hankelXi c (-(ctRprime ε c R))) := rfl
  rw [← hLam] at hE1 hE2 hE3
  have hTB : TaperBand ε c R := taperBand_of_window hW hc3 hcM hlam hR1 hRw hRA
  refine ⟨hTB, fun L hL => ?_, ?_⟩
  · have hexp : Real.exp L - 1 ≤ 5e-4 := by
      have := Real.exp_le_exp.2 hL.2
      linarith
    obtain ⟨h1, h2⟩ := ctUtildeXi_band hc hr0.le hrA hL.1.le hL.2
    have hv0 : 0 < ctVprime c L := mul_pos hK (ctChartG_pos hL.1 hexp)
    have hwin : -ρ < ctMu c * (-(ctVprime c L)) := by
      have : ctMu c * (-R) ≤ ctMu c * (-(ctVprime c L)) := by
        have hle : ctVprime c L ≤ R := h2.trans hTB.Rprime_le
        exact mul_le_mul_of_nonneg_left (by linarith) hmu.le
      linarith
    exact ⟨by unfold ctTaperV; rw [h1], hexp, hv0, h2, hwin⟩
  · obtain ⟨h1, -⟩ := ctUtildeXi_band hc hr0.le hrA hE1.le le_rfl
    have hV : ctTaperV ε c (ctTaperLam ε c R) = -ctUhat ε c (-(ctVprime c (ctTaperLam ε c R))) := by
      unfold ctTaperV; rw [h1]
    rw [hV, hE3, show -ctRprime ε c R = u by rw [hr_eq]; ring, hv, neg_neg]

private lemma ctTaper_V'_lip {ε c R ρ ρr Kψr M : ℝ}
    (hW : PsiWin ε ρ M) (hc3 : 3 ≤ c) (hcM : 2 * M ≤ c) (hTB : TaperBand ε c R)
    (hρr : 0 < ρr) (hKψ : 0 ≤ Kψr)
    (hlip : ∀ a₁ a₂ : ℝ, a₁ ∈ Ioo (-ρr) 0 → a₂ ∈ Ioo (-ρr) 0 →
      |deriv (ctPsi ε) a₁ - deriv (ctPsi ε) a₂| ≤ Kψr * |a₁ - a₂|)
    (hμ_bd : ctMu c * R ≤ ρr / 2)
    (hV_on : ∀ L ∈ Ioc 0 (ctTaperLam ε c R), ctTaperV ε c L = -ctUhat ε c (-(ctVprime c L)) ∧
      Real.exp L - 1 ≤ 5e-4 ∧ 0 < ctVprime c L ∧ ctVprime c L ≤ ctRprime ε c R ∧
      -ρ < ctMu c * (-(ctVprime c L))) :
    ∀ L₁ L₂, L₁ ∈ Ioc 0 (ctTaperLam ε c R) → L₂ ∈ Ioc 0 (ctTaperLam ε c R) →
      |(langerScale c * (-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * (-(ctVprime c L₁))))) -
       (langerScale c * (-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * (-(ctVprime c L₂)))))| ≤
        (15000 * langerKappa + 20 * Kψr * langerKappa ^ 2) * c ^ (2 / 3 : ℝ) * |L₁ - L₂| := by
  intro L₁ L₂ h1 h2
  have hc0 : 0 < c := by linarith
  set Λ := ctTaperLam ε c R
  let V' : ℝ → ℝ := fun L =>
    langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L) *
      (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * (-(ctVprime c L))))
  change |V' L₁ - V' L₂| ≤ _
  obtain ⟨-, hexp1, hv1, hvp1, hwin1⟩ := hV_on L₁ h1
  obtain ⟨-, hexp2, hv2, hvp2, hwin2⟩ := hV_on L₂ h2
  have hK := langerScale_pos hc0
  have hκ := langerKappa_pos
  have hK_eq : langerScale c = langerKappa * c ^ (2 / 3 : ℝ) := by unfold langerScale; ring
  have hmu_eq : ctMu c * langerScale c = (2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa := by
    unfold ctMu langerScale
    have hcp : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; norm_num
    calc _ = (2 : ℝ) ^ ((2 : ℝ) / 3) * langerKappa * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) := by ring
      _ = _ := by rw [hcp, mul_one]
  have h23 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) / 3 ≤ 1)
  have he_lip : ∀ x y, x ∈ Ioc 0 Λ → y ∈ Ioc 0 Λ → |Real.exp x - Real.exp y| ≤ 1.0005 * |x - y| := fun x y hx hy => by
    have hmv := (convex_Ioc 0 Λ).norm_image_sub_le_of_norm_deriv_le (f := Real.exp) (C := 1.0005)
      (fun z _ => (Real.hasDerivAt_exp z).differentiableAt)
      (fun z (hz : z ∈ Ioc 0 Λ) => by
        have := (hV_on z hz).2.1
        rw [Real.norm_eq_abs, Real.deriv_exp, abs_of_pos (Real.exp_pos z)]; linarith) hy hx
    simpa [Real.norm_eq_abs, Real.dist_eq] using hmv
  have hvp_lip : |ctVprime c L₁ - ctVprime c L₂| ≤ 1.005 * langerScale c * |L₁ - L₂| := by
    have hmv := (convex_Ioc 0 Λ).norm_image_sub_le_of_norm_deriv_le (f := ctVprime c) (C := 1.005 * langerScale c)
      (fun z (hz : z ∈ Ioc 0 Λ) => ((ctChartG_hasDerivAt hz.1.le (hV_on z hz).2.1).const_mul (langerScale c)).differentiableAt)
      (fun z (hz : z ∈ Ioc 0 Λ) => by
        have hz_exp := (hV_on z hz).2.1
        have hd := ((ctChartG_hasDerivAt hz.1.le hz_exp).const_mul (langerScale c)).deriv
        have hb := (ctChartG_deriv_bounds hz.1.le hz_exp).2
        have hb0 := (ctChartG_deriv_bounds hz.1.le hz_exp).1
        have he1 : Real.exp z ≤ 1.0005 := by linarith
        change |deriv (fun y => langerScale c * ctChartG y) z| ≤ _
        rw [hd, abs_mul, abs_of_nonneg hK.le, abs_of_nonneg (by nlinarith [Real.exp_pos z])]
        calc langerScale c * (-(ctYRD (Real.exp z - 1)) * Real.exp z) ≤ langerScale c * (1.004 * 1.0005) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left he1 (by norm_num))) hK.le
          _ ≤ 1.005 * langerScale c := by
              rw [mul_comm (langerScale c) (1.004 * 1.0005)]
              exact mul_le_mul_of_nonneg_right (by norm_num) hK.le) h2 h1
    simpa [Real.norm_eq_abs, Real.dist_eq] using hmv
  have hw1 : |Real.exp L₁ - 1| ≤ 5e-4 := by rw [abs_of_nonneg (by linarith [Real.one_le_exp h1.1.le])]; exact hexp1
  have hw2 : |Real.exp L₂ - 1| ≤ 5e-4 := by rw [abs_of_nonneg (by linarith [Real.one_le_exp h2.1.le])]; exact hexp2
  have hy_lip : |-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁ - -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂| ≤
      7010 * |L₁ - L₂| := by
    have hy_d := ctYRD_lip hw1 hw2
    have hy2_bd : |ctYRD (Real.exp L₂ - 1)| ≤ 1.004 := by
      have := abs_le.1 (ctYRD_add_one_le (hw2.trans (by norm_num)))
      rw [abs_le]; constructor <;> linarith
    have he1_bd : |Real.exp L₁| ≤ 1.0005 := by rw [abs_of_pos (Real.exp_pos _)]; linarith
    have hid : -(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁ - -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂ =
        -(ctYRD (Real.exp L₁ - 1) - ctYRD (Real.exp L₂ - 1)) * Real.exp L₁ -
          ctYRD (Real.exp L₂ - 1) * (Real.exp L₁ - Real.exp L₂) := by ring
    rw [hid]
    calc _ ≤ |-(ctYRD (Real.exp L₁ - 1) - ctYRD (Real.exp L₂ - 1)) * Real.exp L₁| +
            |ctYRD (Real.exp L₂ - 1) * (Real.exp L₁ - Real.exp L₂)| := abs_sub _ _
      _ = |ctYRD (Real.exp L₁ - 1) - ctYRD (Real.exp L₂ - 1)| * |Real.exp L₁| +
            |ctYRD (Real.exp L₂ - 1)| * |Real.exp L₁ - Real.exp L₂| := by
              rw [neg_mul, abs_neg, abs_mul, abs_mul]
      _ ≤ (7000 * |Real.exp L₁ - 1 - (Real.exp L₂ - 1)|) * 1.0005 +
            1.004 * (1.0005 * |L₁ - L₂|) := by gcongr; exact he_lip L₁ L₂ h1 h2
      _ = (7000 * 1.0005) * |Real.exp L₁ - Real.exp L₂| + 1.004 * 1.0005 * |L₁ - L₂| := by
            have : Real.exp L₁ - 1 - (Real.exp L₂ - 1) = Real.exp L₁ - Real.exp L₂ := by ring
            rw [this]; ring
      _ ≤ (7000 * 1.0005) * (1.0005 * |L₁ - L₂|) + 1.004 * 1.0005 * |L₁ - L₂| := by
            gcongr; exact he_lip L₁ L₂ h1 h2
      _ ≤ 7010 * |L₁ - L₂| := by
            rw [show (7000 * 1.0005 : ℝ) * (1.0005 * |L₁ - L₂|) + 1.004 * 1.0005 * |L₁ - L₂| =
              (7000 * 1.0005 * 1.0005 + 1.004 * 1.0005) * |L₁ - L₂| by ring]
            exact mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _)
  have hψ_lip : |1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) -
      (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂)))| ≤
      (10 * Kψr * langerKappa / c) * |L₁ - L₂| := by
    have ha_mem : ∀ {L}, L ∈ Ioc 0 Λ → ctMu c * -(ctVprime c L) ∈ Ioo (-ρr) 0 := fun {L} hL => by
      have hmv : ctVprime c L ≤ R := (hV_on L hL).2.2.2.1.trans hTB.Rprime_le
      have h1' : ctMu c * ctVprime c L ≤ ρr / 2 :=
        (mul_le_mul_of_nonneg_left hmv (ctMu_pos hc0).le).trans hμ_bd
      exact ⟨by linarith, mul_neg_of_pos_of_neg (ctMu_pos hc0) (by linarith [(hV_on L hL).2.2.1])⟩
    have hdiff_psi : |deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) -
        deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂))| ≤
        Kψr * |ctMu c * -(ctVprime c L₁) - ctMu c * -(ctVprime c L₂)| :=
      hlip _ _ (ha_mem h1) (ha_mem h2)
    have hstep1 : |ctMu c * -(ctVprime c L₁) - ctMu c * -(ctVprime c L₂)| ≤
        2 * 1.005 * langerKappa * |L₁ - L₂| := by
      rw [show ctMu c * -(ctVprime c L₁) - ctMu c * -(ctVprime c L₂) = -(ctMu c * (ctVprime c L₁ - ctVprime c L₂)) by ring,
        abs_neg, abs_mul, abs_of_pos (ctMu_pos hc0)]
      calc ctMu c * |ctVprime c L₁ - ctVprime c L₂|
          ≤ ctMu c * (1.005 * langerScale c * |L₁ - L₂|) :=
            mul_le_mul_of_nonneg_left hvp_lip (ctMu_pos hc0).le
        _ = 1.005 * (ctMu c * langerScale c) * |L₁ - L₂| := by ring
        _ = (2 : ℝ) ^ ((2 : ℝ) / 3) * (1.005 * langerKappa * |L₁ - L₂|) := by rw [hmu_eq]; ring
        _ ≤ 2 * (1.005 * langerKappa * |L₁ - L₂|) :=
            mul_le_mul_of_nonneg_right h23 (by positivity)
        _ = 2 * 1.005 * langerKappa * |L₁ - L₂| := by ring
    rw [show 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) -
        (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂))) =
        c⁻¹ * (deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) - deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂))) by ring,
      abs_mul, abs_of_pos (inv_pos.2 hc0)]
    calc c⁻¹ * |deriv (ctPsi ε) _ - deriv (ctPsi ε) _|
        ≤ c⁻¹ * (Kψr * (2 * 1.005 * langerKappa * |L₁ - L₂|)) :=
          mul_le_mul_of_nonneg_left (hdiff_psi.trans (mul_le_mul_of_nonneg_left hstep1 hKψ)) (inv_pos.2 hc0).le
      _ ≤ (10 * Kψr * langerKappa / c) * |L₁ - L₂| := by
          rw [div_eq_inv_mul]; nlinarith [mul_nonneg hKψ (mul_nonneg hκ.le (abs_nonneg (L₁ - L₂))), inv_pos.2 hc0]
  have hG1 : |-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂| ≤ 1.005 := by
    have h := (ctChartG_deriv_bounds h2.1.le hexp2).2
    have hb0 := (ctChartG_deriv_bounds h2.1.le hexp2).1
    rw [abs_of_nonneg (by nlinarith [Real.exp_pos L₂])]
    calc -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂ ≤ 1.004 * Real.exp L₂ := h
      _ ≤ 1.004 * 1.0005 := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      _ ≤ 1.005 := by norm_num
  have hD1 : |1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))| ≤ 3 / 2 := by
    have hd := ctUhat_deriv_bounds hW hc0 hcM (u := -(ctVprime c L₁)) (by linarith) (hV_on L₁ h1).2.2.2.2
    rw [abs_of_nonneg (by linarith [hd.1])]; exact hd.2
  dsimp only [V']
  have hprod_bd : |(-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁) *
        (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))) -
      (-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂) *
        (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂)))| ≤
      (15000 + 20 * Kψr * langerKappa) * |L₁ - L₂| := by
    rw [show (-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))) -
        (-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂))) =
        (-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁ - -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))) +
        -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂ *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) -
            (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂)))) by ring]
    have hinv1 : Kψr * langerKappa / c ≤ Kψr * langerKappa := by
      have hc1 : 1 ≤ c := by linarith
      exact div_le_self (by positivity) hc1
    calc _ ≤ |( -(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁ - -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂ ) *
            (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)))| +
            |-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂ *
            (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) -
              (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂))))| := abs_add_le _ _
      _ = |-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁ - -(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂| *
            |1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))| +
            |-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂| *
            |1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁)) -
              (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂)))| := by simp only [abs_mul]
      _ ≤ (7010 * |L₁ - L₂|) * (3 / 2) + 1.005 * ((10 * Kψr * langerKappa / c) * |L₁ - L₂|) := by gcongr
      _ = (7010 * 3 / 2) * |L₁ - L₂| + (10.05 * (Kψr * langerKappa / c)) * |L₁ - L₂| := by ring
      _ ≤ (15000 + 20 * Kψr * langerKappa) * |L₁ - L₂| := by
          have h1' : (7010 * 3 / 2 : ℝ) ≤ 15000 := by norm_num
          have h2' : 10.05 * (Kψr * langerKappa / c) ≤ 20 * (Kψr * langerKappa) := by
            have hc' : (10.05 : ℝ) ≤ 20 := by norm_num
            exact mul_le_mul hc' hinv1 (by positivity) (by norm_num)
          have hsum := add_le_add h1' h2'
          calc (7010 * 3 / 2) * |L₁ - L₂| + (10.05 * (Kψr * langerKappa / c)) * |L₁ - L₂|
              = (7010 * 3 / 2 + 10.05 * (Kψr * langerKappa / c)) * |L₁ - L₂| := by ring
            _ ≤ (15000 + 20 * (Kψr * langerKappa)) * |L₁ - L₂| :=
                mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
            _ = (15000 + 20 * Kψr * langerKappa) * |L₁ - L₂| := by ring
  rw [show langerScale c * (-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁) *
        (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))) -
      langerScale c * (-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂) *
        (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂))) =
      langerScale c * ((-(ctYRD (Real.exp L₁ - 1)) * Real.exp L₁) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₁))) -
        (-(ctYRD (Real.exp L₂ - 1)) * Real.exp L₂) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L₂)))) by ring,
    abs_mul, abs_of_nonneg hK.le, hK_eq]
  exact (mul_le_mul_of_nonneg_left hprod_bd (by positivity)).trans_eq (by ring)

private lemma ctTaperGrad_lip_on {ε c R c₁ Kψ Lmin : ℝ}
    (hc0 : 0 < c) (hc₁ : 0 < c₁) (hKψ : 0 ≤ Kψ) (hR0 : 0 < R) (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hLmin : 0 < Lmin) (_hC₂ : 0 ≤ (900 / c₁ ^ 4 * (4 * langerKappa) ^ 2 +
      24 / c₁ ^ 2 * (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2)) + 1)
    {Λ : ℝ} {V' taperGrad : ℝ → ℝ}
    (hV_eq : ∀ L ∈ Ioc 0 Λ, ctTaperV ε c L = -ctUhat ε c (-(ctVprime c L)))
    (hVd : ∀ L ∈ Ioc 0 Λ, HasDerivAt (fun x => -ctUhat ε c (-(ctVprime c x))) (V' L) L)
    (hV'_bd : ∀ L ∈ Ioc 0 Λ, |V' L| ≤ 4 * langerKappa * c ^ (2 / 3 : ℝ))
    (hV'_lip : ∀ L₁ L₂, L₁ ∈ Ioc 0 Λ → L₂ ∈ Ioc 0 Λ →
      |V' L₁ - V' L₂| ≤ (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2) * c ^ (2 / 3 : ℝ) * |L₁ - L₂|)
    (htg : ∀ L ≤ Λ, taperGrad L = taperWDeriv R (ctTaperV ε c L) * V' L)
    {L₁ L₂ : ℝ} (h1 : L₁ ∈ Icc Lmin Λ) (h2 : L₂ ∈ Icc Lmin Λ) :
    |taperGrad L₁ - taperGrad L₂| ≤
      ((900 / c₁ ^ 4 * (4 * langerKappa) ^ 2 +
        24 / c₁ ^ 2 * (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2)) + 1) * |L₁ - L₂| := by
  have hm1 : L₁ ∈ Ioc 0 Λ := ⟨lt_of_lt_of_le hLmin h1.1, h1.2⟩
  have hm2 : L₂ ∈ Ioc 0 Λ := ⟨lt_of_lt_of_le hLmin h2.1, h2.2⟩
  have hκ := langerKappa_pos
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  rw [htg L₁ h1.2, htg L₂ h2.2]
  have hV_lip : |ctTaperV ε c L₁ - ctTaperV ε c L₂| ≤ 4 * langerKappa * c ^ (2 / 3 : ℝ) * |L₁ - L₂| := by
    have hsub_icc : Icc Lmin Λ ⊆ Ioc 0 Λ := fun x hx => ⟨lt_of_lt_of_le hLmin hx.1, hx.2⟩
    rw [hV_eq L₁ hm1, hV_eq L₂ hm2]
    have hmv := (convex_Icc Lmin Λ).norm_image_sub_le_of_norm_deriv_le (C := 4 * langerKappa * c ^ (2 / 3 : ℝ))
      (fun z hz => (hVd z (hsub_icc hz)).differentiableAt)
      (fun z hz => by
        rw [Real.norm_eq_abs, (hVd z (hsub_icc hz)).deriv]
        exact hV'_bd z (hsub_icc hz)) h2 h1
    simpa [Real.norm_eq_abs, Real.dist_eq] using hmv
  have hw_d : |taperWDeriv R (ctTaperV ε c L₁) - taperWDeriv R (ctTaperV ε c L₂)| ≤
      900 / R ^ 2 * (4 * langerKappa * c ^ (2 / 3 : ℝ) * |L₁ - L₂|) :=
    ((taperWDeriv_bounds hR0).2.2 _ _).trans (mul_le_mul_of_nonneg_left hV_lip (by positivity))
  have hw_1 : |taperWDeriv R (ctTaperV ε c L₂)| ≤ 24 / R := (taperWDeriv_bounds hR0).1 _
  have hv_1 : |V' L₁| ≤ 4 * langerKappa * c ^ (2 / 3 : ℝ) := hV'_bd L₁ hm1
  have hv_lip := hV'_lip L₁ L₂ hm1 hm2
  have hKψ_nn : 0 ≤ (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2) * c ^ (2 / 3 : ℝ) := by positivity
  have hid : taperWDeriv R (ctTaperV ε c L₁) * V' L₁ - taperWDeriv R (ctTaperV ε c L₂) * V' L₂ =
      (taperWDeriv R (ctTaperV ε c L₁) - taperWDeriv R (ctTaperV ε c L₂)) * V' L₁ +
        taperWDeriv R (ctTaperV ε c L₂) * (V' L₁ - V' L₂) := by ring
  rw [hid]
  have hR2_le : 900 / R ^ 2 ≤ 900 / (c₁ ^ 4 * (c ^ (2 / 3 : ℝ)) ^ 2) := by
    refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
    calc c₁ ^ 4 * (c ^ (2 / 3 : ℝ)) ^ 2 = (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ^ 2 := by ring
      _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hRlo 2
  have hR1_le : 24 / R ≤ 24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hRlo
  have ht1 : |taperWDeriv R (ctTaperV ε c L₁) - taperWDeriv R (ctTaperV ε c L₂)| * |V' L₁| ≤
      (900 / (c₁ ^ 4 * (c ^ (2 / 3 : ℝ)) ^ 2) * (4 * langerKappa * c ^ (2 / 3 : ℝ) * |L₁ - L₂|)) *
        (4 * langerKappa * c ^ (2 / 3 : ℝ)) :=
    mul_le_mul (hw_d.trans (mul_le_mul_of_nonneg_right hR2_le (by positivity))) hv_1
      (abs_nonneg _) (by positivity)
  have ht2 : |taperWDeriv R (ctTaperV ε c L₂)| * |V' L₁ - V' L₂| ≤
      (24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ))) *
        ((15000 * langerKappa + 20 * Kψ * langerKappa ^ 2) * c ^ (2 / 3 : ℝ) * |L₁ - L₂|) :=
    mul_le_mul (hw_1.trans hR1_le) hv_lip (abs_nonneg _) (by positivity)
  calc _ ≤ |(taperWDeriv R (ctTaperV ε c L₁) - taperWDeriv R (ctTaperV ε c L₂)) * V' L₁| +
          |taperWDeriv R (ctTaperV ε c L₂) * (V' L₁ - V' L₂)| := abs_add_le _ _
    _ = |taperWDeriv R (ctTaperV ε c L₁) - taperWDeriv R (ctTaperV ε c L₂)| * |V' L₁| +
          |taperWDeriv R (ctTaperV ε c L₂)| * |V' L₁ - V' L₂| := by simp only [abs_mul]
    _ ≤ (900 / (c₁ ^ 4 * (c ^ (2 / 3 : ℝ)) ^ 2) * (4 * langerKappa * c ^ (2 / 3 : ℝ) * |L₁ - L₂|)) *
          (4 * langerKappa * c ^ (2 / 3 : ℝ)) +
          (24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ))) *
            ((15000 * langerKappa + 20 * Kψ * langerKappa ^ 2) * c ^ (2 / 3 : ℝ) * |L₁ - L₂|) :=
          add_le_add ht1 ht2
    _ = (900 / c₁ ^ 4 * (4 * langerKappa) ^ 2 +
          24 / c₁ ^ 2 * (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2)) * |L₁ - L₂| := by
          field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

/-- **Concrete `ctTaper` regularity on `(0, ∞)` and `[ctLv0 c / 4, ∞)`** (`ct:boas` Step 3):
for `c₁ ≤ c₁₀` and `c ≥ c₀(c₁)`, `ctTaper ε c R` has continuous derivative `taperGrad` on `(0, ∞)`
vanishing above `Λ`, bounded by `C₀ L^{12}` / `C₁ L¹¹` on `[ctLv0 c / 4, Λ]`, and `C₂`-Lipschitz
on `[ctLv0 c / 4, ∞)`. -/
theorem ctTaper_hasDerivAt_and_lip : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → ∃ C₀ C₁ C₂ c₀ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 3 ≤ c₀ ∧
      ∀ {ε c R : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
          TaperBand ε c R ∧
          ∃ taperGrad : ℝ → ℝ,
            (∀ L ∈ Ioi (0 : ℝ), HasDerivAt (ctTaper ε c R) (taperGrad L) L) ∧
            (∀ L ∈ Ioi (0 : ℝ), 0 ≤ ctTaper ε c R L ∧ ctTaper ε c R L ≤ 1) ∧
            (∀ L ∈ Icc (ctLv0 c / 4) (ctTaperLam ε c R),
              ctTaper ε c R L ≤ C₀ * L ^ 12 ∧ |taperGrad L| ≤ C₁ * L ^ 11) ∧
            (∀ L, ctTaperLam ε c R < L → taperGrad L = 0) ∧
            (∀ L, ctLv0 c / 4 ≤ L → |taperGrad L| ≤ C₁) ∧
            (∀ L₁ L₂, ctLv0 c / 4 ≤ L₁ → ctLv0 c / 4 ≤ L₂ →
              |taperGrad L₁ - taperGrad L₂| ≤ C₂ * |L₁ - L₂|) := by
  obtain ⟨ρ, M, hρ, hM, hpm⟩ := ct_window_pm
  obtain ⟨ρp, Kψp, hρp, hKψp, hlip_p⟩ := ctPsi_deriv_lip (ε := 1) (Or.inl rfl)
  obtain ⟨ρm, Kψm, hρm, hKψm, hlip_m⟩ := ctPsi_deriv_lip (ε := -1) (Or.inr rfl)
  obtain ⟨κ₀, hκ₀, cL, hcL1, hLv0⟩ := ctLv0_facts
  have hκ := langerKappa_pos
  set ρ₀ : ℝ := min ρ (min ρp ρm) with hρ₀
  have hρ₀_pos : 0 < ρ₀ := lt_min hρ (lt_min hρp hρm)
  set Kψ : ℝ := max Kψp Kψm with hKψ
  have hKψ_nn : 0 ≤ Kψ := le_trans hKψp (le_max_left _ _)
  set A₁ : ℝ := min (ρ₀ / (16 * 2)) (langerKappa * 4.94e-4 / 16) with hA₁
  have hA₁_pos : 0 < A₁ := lt_min (by positivity) (by positivity)
  refine ⟨Real.sqrt A₁, Real.sqrt_pos.2 hA₁_pos, fun c₁ hc₁ hle => ?_⟩
  have hc₁_sq : c₁ ^ 2 ≤ A₁ := by
    have := pow_le_pow_left₀ hc₁.le hle 2
    rwa [Real.sq_sqrt hA₁_pos.le] at this
  have hc₁2 : 4 * (2 : ℝ) ^ (2 / 3 : ℝ) * c₁ ^ 2 ≤ ρ₀ / 2 := by
    have h23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
      have : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    have hc1A : c₁ ^ 2 ≤ ρ₀ / 32 := (hc₁_sq.trans (min_le_left _ _)).trans_eq (by ring)
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 / 3 : ℝ)]
  have hc₁K : 4 * c₁ ^ 2 ≤ langerKappa * 4.94e-4 := by
    have hc1A : c₁ ^ 2 ≤ langerKappa * 4.94e-4 / 16 := hc₁_sq.trans (min_le_right _ _)
    linarith
  set C_rat : ℝ := 3 * langerKappa / c₁ ^ 2 with hCrat
  set C₀ : ℝ := 2 * C_rat ^ 12 + 1 with hC₀
  set C₁ : ℝ := (96 * C_rat ^ 11 + 96) * langerKappa / c₁ ^ 2 with hC₁
  set C₂ : ℝ := (900 / c₁ ^ 4 * (4 * langerKappa) ^ 2 +
    24 / c₁ ^ 2 * (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2)) + 1 with hC₂
  have hc_ev : ∃ c₀ : ℝ, 3 ≤ c₀ ∧ ∀ c, c₀ ≤ c →
      cL ≤ c ∧ 2 * M ≤ c ∧ ctLam c * M ≤ 1 / 2 ∧
      1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) ∧ (0.998 / 4) * langerKappa * κ₀ * c ^ (12 / 21 : ℝ) ≥ 1 := by
    have hev1 : ∀ᶠ c : ℝ in atTop, 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
      have ht : Tendsto (fun c : ℝ => c₁ ^ 2 * c ^ (2 / 3 : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).const_mul_atTop (by positivity)
      exact (ht.eventually_ge_atTop 1)
    have hev2 : ∀ᶠ c : ℝ in atTop, 1 ≤ (0.998 / 4) * langerKappa * κ₀ * c ^ (12 / 21 : ℝ) := by
      have ht : Tendsto (fun c : ℝ => (0.998 / 4) * langerKappa * κ₀ * c ^ (12 / 21 : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).const_mul_atTop (by positivity)
      exact (ht.eventually_ge_atTop 1)
    have hev3 : ∀ᶠ c : ℝ in atTop, ctLam c * M ≤ 1 / 2 := by
      have ht : Tendsto (fun c : ℝ => ctLam c * M) atTop (𝓝 ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * 0 * M)) := by
        unfold ctLam
        exact ((tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)))).mul_const M
      rw [mul_zero, zero_mul] at ht
      exact ht.eventually (Iic_mem_nhds (by norm_num))
    obtain ⟨B, hB⟩ := ((Filter.eventually_ge_atTop (max 3 (max cL (2 * M)))).and
      (hev1.and (hev2.and hev3))).exists_forall_of_atTop
    exact ⟨B, le_trans (le_max_left _ _) (hB B le_rfl).1, fun c hc =>
      ⟨le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hB c hc).1,
       le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hB c hc).1,
       (hB c hc).2.2.2, (hB c hc).2.1, (hB c hc).2.2.1⟩⟩
  obtain ⟨c₀, hc₀3, hc₀_prop⟩ := hc_ev
  refine ⟨C₀, C₁, C₂, c₀, by positivity, by positivity, by positivity, hc₀3, ?_⟩
  intro ε c R hε hc hRlo hRhi
  obtain ⟨hcL, hcM, hlamM, hR1_lb, hv_quarter⟩ := hc₀_prop c hc
  have hc3 : 3 ≤ c := hc₀3.trans hc
  have hc0 : 0 < c := by linarith
  have hK := langerScale_pos hc0
  have hR1 : 1 ≤ R := hR1_lb.trans hRlo
  have hR0 : 0 < R := by linarith
  have hW : PsiWin ε ρ M := (hpm ε hε).1
  have hμR : ctMu c * R ≤ ρ₀ / 2 := by
    have e : ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hRhi (ctMu_pos hc0).le
    have hcprod : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have h1 : ctMu c * R ≤ 4 * (2 : ℝ) ^ (2 / 3 : ℝ) * c₁ ^ 2 := calc
      ctMu c * R ≤ ctMu c * (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) := e
      _ = 4 * (2 : ℝ) ^ (2 / 3 : ℝ) * c₁ ^ 2 * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) := by
          unfold ctMu; ring
      _ = 4 * (2 : ℝ) ^ (2 / 3 : ℝ) * c₁ ^ 2 := by rw [hcprod, mul_one]
    exact h1.trans hc₁2
  have hRw : -ρ < ctMu c * (-R) := by
    linarith [min_le_left ρ (min ρp ρm)]
  have hRA : R ≤ langerRadius c := by
    calc R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := hRhi
      _ ≤ (langerKappa * 4.94e-4) * c ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hc₁K (Real.rpow_nonneg hc0.le _)
      _ = langerRadius c := by unfold langerRadius langerScale; ring
  obtain ⟨hTB, hV_on, hV_Lam⟩ := ctTaperV_formula_on hW hc3 hcM hlamM hR1 hRw hRA
  set Λ := ctTaperLam ε c R with hΛ
  let V' : ℝ → ℝ := fun L =>
    langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L) *
      (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * (-(ctVprime c L))))
  let taperGrad : ℝ → ℝ := fun L => if L ≤ Λ then taperWDeriv R (ctTaperV ε c L) * V' L else 0
  have hVd : ∀ L ∈ Ioc 0 Λ, HasDerivAt (fun x => -ctUhat ε c (-(ctVprime c x))) (V' L) L := by
    intro L hL
    obtain ⟨-, hexp, hv0, -, hwin⟩ := hV_on L hL
    have hg := ctChartG_hasDerivAt hL.1.le hexp
    have h1 : HasDerivAt (fun x => -(ctVprime c x)) (-(langerScale c * (-(ctYRD (Real.exp L - 1)) * Real.exp L))) L :=
      (hg.const_mul (langerScale c)).neg
    have hU := ctUhat_hasDerivAt hW hc0 (u := -(ctVprime c L)) (by linarith) hwin
    have hcomp := (hU.comp L h1).neg
    change HasDerivAt (fun x => -ctUhat ε c (-ctVprime c x)) _ L at hcomp
    exact hcomp.congr_deriv (by dsimp only [V']; ring)
  have hV'_bd : ∀ L ∈ Ioc 0 Λ, |V' L| ≤ 4 * langerKappa * c ^ (2 / 3 : ℝ) := by
    intro L hL
    obtain ⟨-, hexp, hv0, -, hwin⟩ := hV_on L hL
    have hD := ctUhat_deriv_bounds hW hc0 hcM (u := -(ctVprime c L)) (by linarith) hwin
    have hgd := ctChartG_deriv_bounds hL.1.le hexp
    have he1 : Real.exp L ≤ 1 + 5e-4 := by linarith
    have hK_eq : langerScale c = langerKappa * c ^ (2 / 3 : ℝ) := by unfold langerScale; ring
    dsimp only [V']
    have h1 : 0 ≤ -(ctYRD (Real.exp L - 1)) * Real.exp L := by nlinarith [Real.exp_pos L]
    have h2 : -(ctYRD (Real.exp L - 1)) * Real.exp L ≤ 1.004 * 1.0005 := by
      calc -(ctYRD (Real.exp L - 1)) * Real.exp L ≤ 1.004 * Real.exp L := hgd.2
        _ ≤ 1.004 * (1 + 5e-4) := mul_le_mul_of_nonneg_left he1 (by norm_num)
        _ = 1.004 * 1.0005 := by norm_num
    rw [abs_mul, abs_mul, abs_of_nonneg hK.le, abs_of_nonneg h1, abs_of_nonneg (by linarith [hD.1]), hK_eq]
    calc langerKappa * c ^ (2 / 3 : ℝ) * (-(ctYRD (Real.exp L - 1)) * Real.exp L) *
          (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * -(ctVprime c L)))
        ≤ (langerKappa * c ^ (2 / 3 : ℝ)) * (1.004 * 1.0005) * (3 / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) hD.2
            (by linarith [hD.1]) (by positivity)
      _ = (1.004 * 1.0005 * (3 / 2)) * (langerKappa * c ^ (2 / 3 : ℝ)) := by ring
      _ ≤ 4 * (langerKappa * c ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 4 * langerKappa * c ^ (2 / 3 : ℝ) := by ring
  have hc23_pos : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  refine ⟨hTB, taperGrad, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    rcases lt_trichotomy L Λ with hlt | hEq | hgt
    · have hev : ctTaper ε c R =ᶠ[𝓝 L] fun x => taperW R (-ctUhat ε c (-(ctVprime c x))) := by
        filter_upwards [Ioo_mem_nhds hL hlt] with x hx
        have hmem : x ∈ Ioc 0 Λ := ⟨hx.1, hx.2.le⟩
        rw [ctTaper_eq_of_pos ε c R hx.1]
        unfold ctTaperVbar
        rw [if_pos hx.2.le, taper_min_eq, (hV_on x hmem).1]
      have hd1 := hVd L ⟨hL, hlt.le⟩
      have hd2 : HasDerivAt (fun x => taperW R (-ctUhat ε c (-ctVprime c x)))
          (taperWDeriv R (-ctUhat ε c (-ctVprime c L)) * V' L) L := by
        have hraw := (hasDerivAt_taperW hR0 (-ctUhat ε c (-(ctVprime c L)))).comp L hd1
        exact hraw
      have hgrad : taperGrad L = taperWDeriv R (ctTaperV ε c L) * V' L := if_pos hlt.le
      rw [hgrad, (hV_on L ⟨hL, hlt.le⟩).1]
      exact hd2.congr_of_eventuallyEq hev
    · subst L
      have hleft : HasDerivWithinAt (ctTaper ε c R) 0 (Iic Λ) Λ := by
        have hmem : Ioc 0 Λ ∈ nhdsWithin Λ (Iic Λ) := Ioc_mem_nhdsLE_of_mem ⟨hTB.inputs.Lam_pos, le_rfl⟩
        have hd1 : HasDerivWithinAt (fun x => taperW R (-ctUhat ε c (-(ctVprime c x)))) 0 (Ioc 0 Λ) Λ := by
          have hd_v := (hVd Λ ⟨hTB.inputs.Lam_pos, le_rfl⟩).hasDerivWithinAt (s := Ioc 0 Λ)
          have hv_val : -ctUhat ε c (-(ctVprime c Λ)) = R := by
            rw [← (hV_on Λ ⟨hTB.inputs.Lam_pos, le_rfl⟩).1, hV_Lam]
          have hd_w : HasDerivWithinAt (taperW R) (taperWDeriv R (-ctUhat ε c (-(ctVprime c Λ)))) univ
              (-ctUhat ε c (-(ctVprime c Λ))) := by
            rw [hv_val]
            exact (hasDerivAt_taperW hR0 R).hasDerivWithinAt (s := univ)
          have hcomp := hd_w.comp Λ hd_v (Set.mapsTo_univ _ _)
          have hwt0 : taperWDeriv R R = 0 := by unfold taperWDeriv; simp
          rw [hv_val, hwt0, zero_mul] at hcomp
          exact hcomp
        have heq_on : ∀ x ∈ Ioc 0 Λ, ctTaper ε c R x = taperW R (-ctUhat ε c (-(ctVprime c x))) := fun x hx => by
          rw [ctTaper_eq_of_pos ε c R hx.1]
          unfold ctTaperVbar
          rw [if_pos hx.2, taper_min_eq, (hV_on x hx).1]
        exact (hd1.congr heq_on (heq_on Λ ⟨hTB.inputs.Lam_pos, le_rfl⟩)).mono_of_mem_nhdsWithin hmem
      have hright : HasDerivWithinAt (ctTaper ε c R) 0 (Ici Λ) Λ := by
        have heq_on : ∀ x ∈ Ici Λ, ctTaper ε c R x = 1 := fun x hx => by
          rcases eq_or_lt_of_le hx with rfl | hgt
          · rw [ctTaper_eq_of_pos ε c R hTB.inputs.Lam_pos]; unfold ctTaperVbar
            rw [if_pos le_rfl, taper_min_eq, hV_Lam, taperW_of_ge hR0 le_rfl]
          · unfold ctTaper
            rw [if_neg (not_le.2 (hTB.inputs.Lam_pos.trans hgt)), if_neg (not_le.2 hgt)]
            exact taperW_of_ge hR0 le_rfl
        exact ((hasDerivAt_const Λ (1 : ℝ)).hasDerivWithinAt).congr heq_on (heq_on Λ le_rfl)
      have hgrad0 : taperGrad Λ = 0 := by
        have h1 : taperGrad Λ = taperWDeriv R (ctTaperV ε c Λ) * V' Λ := if_pos le_rfl
        rw [h1, hV_Lam]
        have : taperWDeriv R R = 0 := by unfold taperWDeriv; simp
        rw [this, zero_mul]
      rw [hgrad0]
      exact hasDerivWithinAt_univ.1 (by rw [← Iic_union_Ici]; exact hleft.union hright)
    · have hev : ctTaper ε c R =ᶠ[𝓝 L] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx
        unfold ctTaper
        rw [if_neg (not_le.2 (hTB.inputs.Lam_pos.trans (Set.mem_Ioi.1 hx))), if_neg (not_le.2 (Set.mem_Ioi.1 hx))]
        exact taperW_of_ge hR0 le_rfl
      have hgrad0 : taperGrad L = 0 := if_neg (not_le.2 hgt)
      rw [hgrad0]
      exact (hasDerivAt_const L (1 : ℝ)).congr_of_eventuallyEq hev
  · intro L _
    unfold ctTaper
    split_ifs <;> first | exact ⟨le_rfl, zero_le_one⟩ | exact ⟨taperW_nonneg hR0 _, taperW_le_one hR0 _⟩
  · intro L hL
    have hLv_pos : 0 < ctLv0 c := (hLv0 c hcL).1
    have hL0 : 0 < L := by linarith [hL.1]
    have hmem : L ∈ Ioc 0 Λ := ⟨hL0, hL.2⟩
    obtain ⟨-, hexp, -, -, -⟩ := hV_on L hmem
    have hV_nonneg : 0 ≤ ctTaperV ε c L := (hTB.inputs.v_pos L hL0 hL.2).le
    have hV_le_R' : ctTaperV ε c L ≤ R := by rw [← hV_Lam]; exact hTB.inputs.v_mono L Λ hL0 hL.2 le_rfl
    have hvp_ge : 1 / 2 ≤ ctVprime c L := by
      have hκ_lb := (hLv0 c hcL).2.2.2
      have hb_L := (ctVprime_bounds hc0 hL0.le hexp).1
      have hL_ge : κ₀ * (3 / 10) * c ^ (-(2 / 21 : ℝ)) ≤ L := by linarith [hL.1, hκ_lb]
      have hc47_pow : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 21 : ℝ)) = c ^ (12 / 21 : ℝ) := by
        rw [← Real.rpow_add hc0]; norm_num
      have hK_eq : langerScale c = langerKappa * c ^ (2 / 3 : ℝ) := by unfold langerScale; ring
      calc 1 / 2 ≤ (0.998 / 4) * langerKappa * κ₀ * c ^ (12 / 21 : ℝ) := by linarith [hv_quarter]
        _ ≤ 0.998 * (langerKappa * c ^ (2 / 3 : ℝ)) * (κ₀ * (3 / 10) * c ^ (-(2 / 21 : ℝ))) := by
            have hcoeff : (0.998 / 4 : ℝ) ≤ 0.998 * (3 / 10) := by norm_num
            calc (0.998 / 4) * langerKappa * κ₀ * c ^ (12 / 21 : ℝ)
                = (0.998 / 4) * (langerKappa * κ₀ * c ^ (12 / 21 : ℝ)) := by ring
              _ ≤ (0.998 * (3 / 10)) * (langerKappa * κ₀ * c ^ (12 / 21 : ℝ)) :=
                  mul_le_mul_of_nonneg_right hcoeff (by positivity)
              _ = 0.998 * (langerKappa * c ^ (2 / 3 : ℝ)) * (κ₀ * (3 / 10) * c ^ (-(2 / 21 : ℝ))) := by
                  rw [← hc47_pow]; ring
        _ ≤ 0.998 * langerScale c * L := by rw [hK_eq]; gcongr
        _ ≤ ctVprime c L := hb_L
    have hVR_le : ctTaperV ε c L / R ≤ C_rat * L := by
      have h1 : ctTaperV ε c L ≤ ctVprime c L + 1 / 2 := hTB.v_le L hL0 hL.2
      have h2 : ctTaperV ε c L ≤ 2 * ctVprime c L := by linarith
      have h3 := (ctVprime_bounds hc0 hL0.le hexp).2
      have h4 : ctTaperV ε c L ≤ 2.005 * langerScale c * L := by linarith
      have hK_eq : langerScale c = langerKappa * c ^ (2 / 3 : ℝ) := by unfold langerScale; ring
      calc ctTaperV ε c L / R ≤ (2.005 * langerScale c * L) / R :=
            div_le_div_of_nonneg_right h4 hR0.le
        _ ≤ (2.005 * langerKappa * c ^ (2 / 3 : ℝ) * L) / (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) := by
            rw [hK_eq]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hRlo
        _ = 2.005 * langerKappa / c₁ ^ 2 * L := by field_simp
        _ ≤ C_rat * L := by
            rw [hCrat]; exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (sq_nonneg c₁)) hL0.le
    refine ⟨?_, ?_⟩
    · rw [ctTaper_eq_of_pos ε c R hL0]
      unfold ctTaperVbar
      rw [← hΛ, if_pos hL.2, taper_min_eq]
      calc taperW R (ctTaperV ε c L) ≤ 2 * (ctTaperV ε c L / R) ^ 12 := taperW_le_pow hR0 hV_nonneg
        _ ≤ 2 * (C_rat * L) ^ 12 := by gcongr
        _ = 2 * C_rat ^ 12 * L ^ 12 := by ring
        _ ≤ C₀ * L ^ 12 := by
            rw [hC₀]
            exact mul_le_mul_of_nonneg_right (by linarith [pow_nonneg (show 0 ≤ C_rat by positivity) 12]) (pow_nonneg hL0.le 12)
    · have hgrad : taperGrad L = taperWDeriv R (ctTaperV ε c L) * V' L := by
        dsimp only [taperGrad]; simp only [hL.2, ↓reduceIte]
      rw [hgrad, abs_mul]
      have hw := (taperWDeriv_bounds hR0).2.1 (ctTaperV ε c L) hV_nonneg hV_le_R'
      have hv' := hV'_bd L hmem
      have hR_lb : 24 / R ≤ 24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hRlo
      calc |taperWDeriv R (ctTaperV ε c L)| * |V' L|
          ≤ (24 / R * (ctTaperV ε c L / R) ^ 11) * (4 * langerKappa * c ^ (2 / 3 : ℝ)) :=
            mul_le_mul hw hv' (abs_nonneg _) (by positivity)
        _ ≤ (24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) * (C_rat * L) ^ 11) * (4 * langerKappa * c ^ (2 / 3 : ℝ)) := by
            gcongr
        _ = (96 * C_rat ^ 11) * langerKappa / c₁ ^ 2 * L ^ 11 := by field_simp; ring
        _ ≤ C₁ * L ^ 11 := by
            rw [hC₁]; refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (sq_nonneg c₁)) (pow_nonneg hL0.le 11)
            exact mul_le_mul_of_nonneg_right (by linarith) hκ.le
  · intro L hL
    dsimp only [taperGrad]; simp only [not_le.2 hL, ↓reduceIte]
  · intro L hL
    have hLv_pos : 0 < ctLv0 c := (hLv0 c hcL).1
    by_cases hLΛ : L ≤ Λ
    · have hgrad : taperGrad L = taperWDeriv R (ctTaperV ε c L) * V' L := by
        dsimp only [taperGrad]; simp only [hLΛ, ↓reduceIte]
      rw [hgrad, abs_mul]
      have hw := (taperWDeriv_bounds hR0).1 (ctTaperV ε c L)
      have hv' := hV'_bd L ⟨by linarith, hLΛ⟩
      have hR_lb : 24 / R ≤ 24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hRlo
      calc |taperWDeriv R (ctTaperV ε c L)| * |V' L|
          ≤ (24 / (c₁ ^ 2 * c ^ (2 / 3 : ℝ))) * (4 * langerKappa * c ^ (2 / 3 : ℝ)) :=
            mul_le_mul (hw.trans hR_lb) hv' (abs_nonneg _) (by positivity)
        _ = 96 * langerKappa / c₁ ^ 2 := by field_simp; ring
        _ ≤ C₁ := by
            rw [hC₁]; refine div_le_div_of_nonneg_right ?_ (sq_nonneg c₁)
            exact mul_le_mul_of_nonneg_right (by linarith [pow_nonneg (show 0 ≤ C_rat by positivity) 11]) hκ.le
    · dsimp only [taperGrad]; simp only [hLΛ, ↓reduceIte, abs_zero]; positivity
  · have hV'_lip : ∀ L₁ L₂, L₁ ∈ Ioc 0 Λ → L₂ ∈ Ioc 0 Λ →
        |V' L₁ - V' L₂| ≤ (15000 * langerKappa + 20 * Kψ * langerKappa ^ 2) * c ^ (2 / 3 : ℝ) * |L₁ - L₂| := by
      intro L₁ L₂ h1 h2
      rcases hε with rfl | rfl
      · have hbd := ctTaper_V'_lip hW hc3 hcM hTB hρp hKψp hlip_p
          (hμR.trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)))
          hV_on L₁ L₂ h1 h2
        refine hbd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hc23_pos.le) (abs_nonneg _))
        have : Kψp ≤ Kψ := le_max_left _ _
        gcongr
      · have hbd := ctTaper_V'_lip hW hc3 hcM hTB hρm hKψm hlip_m
          (hμR.trans (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)))
          hV_on L₁ L₂ h1 h2
        refine hbd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hc23_pos.le) (abs_nonneg _))
        have : Kψm ≤ Kψ := le_max_right _ _
        gcongr
    have hC₂_nn : 0 ≤ C₂ := by positivity
    have hgrad_lip_on : ∀ L₁ L₂, L₁ ∈ Icc (ctLv0 c / 4) Λ → L₂ ∈ Icc (ctLv0 c / 4) Λ →
        |taperGrad L₁ - taperGrad L₂| ≤ C₂ * |L₁ - L₂| := fun L₁ L₂ h1 h2 => by
      rw [hC₂]
      exact ctTaperGrad_lip_on hc0 hc₁ hKψ_nn hR0 hRlo (div_pos (hLv0 c hcL).1 (by norm_num))
        (hC₂ ▸ hC₂_nn) (fun L hL => (hV_on L hL).1) hVd hV'_bd hV'_lip
        (fun L hL => by dsimp only [taperGrad]; simp only [hL, ↓reduceIte]) h1 h2
    have h0_ge : ∀ x, Λ ≤ x → taperGrad x = 0 := fun x hx => by
      dsimp only [taperGrad]
      rcases eq_or_lt_of_le hx with rfl | hlt
      · simp only [le_rfl, ↓reduceIte, hV_Lam]
        rw [show taperWDeriv R R = 0 by unfold taperWDeriv; simp, zero_mul]
      · simp only [not_le.2 hlt, ↓reduceIte]
    intro L₁ L₂ h1 h2
    rcases le_total L₁ Λ with a1 | a1 <;> rcases le_total L₂ Λ with a2 | a2
    · exact hgrad_lip_on L₁ L₂ ⟨h1, a1⟩ ⟨h2, a2⟩
    · rw [h0_ge L₂ a2, sub_zero, ← sub_zero (taperGrad L₁), ← h0_ge Λ le_rfl]
      have h1Λ : |L₁ - Λ| ≤ |L₁ - L₂| := by
        rw [abs_of_nonpos (sub_nonpos.2 a1), abs_of_nonpos (sub_nonpos.2 (a1.trans a2))]
        linarith
      exact (hgrad_lip_on L₁ Λ ⟨h1, a1⟩ ⟨h1.trans a1, le_rfl⟩).trans
        (mul_le_mul_of_nonneg_left h1Λ hC₂_nn)
    · rw [h0_ge L₁ a1, ← h0_ge Λ le_rfl, abs_sub_comm]
      have h2Λ : |L₂ - Λ| ≤ |L₁ - L₂| := by
        rw [abs_of_nonpos (sub_nonpos.2 a2), abs_of_nonneg (sub_nonneg.2 (a2.trans a1))]
        linarith
      exact (hgrad_lip_on L₂ Λ ⟨h2, a2⟩ ⟨h2.trans a2, le_rfl⟩).trans
        (mul_le_mul_of_nonneg_left h2Λ hC₂_nn)
    · rw [h0_ge L₁ a1, h0_ge L₂ a2, sub_self, abs_zero]
      exact mul_nonneg hC₂_nn (abs_nonneg _)

end FormalResearch.SignUncertainty
