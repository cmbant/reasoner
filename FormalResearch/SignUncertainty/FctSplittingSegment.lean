/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingDescent
public import FormalResearch.SignUncertainty.StripGExpansion
public import FormalResearch.SignUncertainty.FctPhiKillCore

/-!
# The segment integrand of `Ψ_c` (`(fct:A-Psi-def)`): continuity, the `|t|^{-1/2}` bound at `0`, integrability

Paper I (`constant_terms_five.tex`), proof of `fct:splitting` (3), "Factorization at the corner": `K₀A_ε = t^{-1/2} a(t)`.

For the concrete `f = K₀(·, ξ₁) A_ε = fctWarpKA` and `c > 0`, `D_{τ₁}` continuous and bounded on the closed strip (`CompData`):

* `fctWarpKA_continuousOn`: `f` is continuous on `{0 ≤ Re t < 1, t ≠ 0}`;
* `fctWarpKA_near_zero`: `‖f(t)‖ ≤ M ‖t‖^{-1/2}` for `0 < ‖t‖ ≤ r`, `0 ≤ Re t < 1` (`stripG = O(t²)` by `stripG_sub_le`, `φ_kill = O(t⁸)` by
  `phiKill_near_zero`, `H_*/G_ε = O(|t|^{-5/2})` by `ctHG_bound`);
* `fctWarpKA_segment_integrable`: the segment integrand `s ↦ f(sζ)` of `Ψ_c` is interval integrable on `[0, 1]` for `0 ≤ Re ζ < 1`.

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- `f(t) = K₀(t, ξ₁) A_ε(t)`, the integrand of `Ψ_c` and of `I_ε(L₁, α)`. -/
noncomputable def fctWarpKA (K4 ε c L1 α : ℝ) (t : ℂ) : ℂ :=
  mellinK0 c t (fctXi1 L1) * fctWarpA K4 ε c L1 α t

/-- `f` is continuous on `{0 ≤ Re t < 1, t ≠ 0}`. -/
lemma fctWarpKA_continuousOn {K4 ε c L1 α : ℝ} (hc : 0 < c) (hD : ContinuousOn (fctDcompAt K4 c α) closedStrip) :
    ContinuousOn (fctWarpKA K4 ε c L1 α) {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} := by
  set S : Set ℂ := {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} with hS
  have hSe : S ⊆ edgeStrip := fun t ht => by
    show |t.re| < 1
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2.1]
  have hSc : S ⊆ closedStrip := fun t ht => ⟨ht.1, ht.2.1.le⟩
  have hK0 : ContinuousOn (fun t : ℂ => mellinK0 c t (fctXi1 L1)) S :=
    (differentiableOn_mellinK0 hc _).continuousOn.mono hSe
  have hG : ContinuousOn stripG S := differentiableOn_stripG.continuousOn.mono hSe
  have ha : 0 < c ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hP : ContinuousOn (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ)))) S := by
    refine (FctPhiKill.differentiableOn_phiPQ 8 8 _).continuousOn.mono fun t ht => ?_
    intro h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.ofReal_re] at this
    linarith [ht.1]
  have hH : ContinuousOn (ctHG ε) S := (ctHG_continuousOn ε).mono fun t ht =>
    ⟨hSc ht, ht.2.2, fun h => by have := ht.2.1; rw [h] at this; simp at this⟩
  unfold fctWarpKA fctWarpA
  exact hK0.mul (((hG.add (continuousOn_const.mul hP)).mul (hD.mono hSc)).mul hH)

/-- **The corner bound `‖K₀A_ε(t)‖ ≤ M‖t‖^{-1/2}`** (`fct:splitting` (3)): for `c > 0`, `D_{τ₁}` bounded on the closed strip. -/
lemma fctWarpKA_near_zero {K4 ε c L1 α : ℝ} (hc : 0 < c) (hD : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ t : ℂ, 0 ≤ t.re → t.re < 1 → t ≠ 0 → ‖t‖ ≤ r →
      ‖fctWarpKA K4 ε c L1 α t‖ ≤ M * ‖t‖ ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB⟩ := hD
  set a : ℝ := c ^ (-(1 / 12 : ℝ)) with ha
  have hapos : 0 < a := Real.rpow_pos_of_pos hc _
  -- `K₀` bounded near `0`
  obtain ⟨B1, hB1⟩ : ∃ B1 : ℝ, ∀ t : ℂ, ‖t‖ ≤ 1 / 2 → ‖mellinK0 c t (fctXi1 L1)‖ ≤ B1 := by
    have hcomp : IsCompact (Metric.closedBall (0 : ℂ) (1 / 2)) := isCompact_closedBall _ _
    have hcont : ContinuousOn (fun t : ℂ => mellinK0 c t (fctXi1 L1)) (Metric.closedBall (0 : ℂ) (1 / 2)) :=
      (differentiableOn_mellinK0 hc _).continuousOn.mono fun t ht => by
        show |t.re| < 1
        have : |t.re| ≤ ‖t‖ := Complex.abs_re_le_norm t
        have h2 : ‖t‖ ≤ 1 / 2 := by simpa using ht
        linarith
    obtain ⟨B1, hB1⟩ := hcomp.exists_bound_of_continuousOn hcont
    exact ⟨B1, fun t ht => hB1 t (by simpa using ht)⟩
  -- `φ_kill` bound
  obtain ⟨Cφ, hCφ0, hCφ⟩ := FctPhiKill.phiKill_near_zero
  -- `H_*/G_ε` bound
  obtain ⟨MH, hMH⟩ := ctHG_bound ε
  obtain ⟨rH, hrH, hHb⟩ : ∃ rH : ℝ, 0 < rH ∧ ∀ ζ ∈ closedStrip, ζ ≠ 0 → ‖ζ‖ < rH →
      ‖ctHG ε ζ‖ ≤ MH * ‖ζ‖ ^ (-(5 / 2 : ℝ)) := by
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hMH
    obtain ⟨r, hr, hsub⟩ := hMH
    exact ⟨r, hr, fun ζ h1 h2 h3 => hsub ⟨by simpa using h3, h1, h2⟩⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨by simp, by simp⟩)
  set r : ℝ := min (min (min (1 / 4) (a / 2)) 1) (rH / 2) with hr
  have hrpos : 0 < r := by positivity
  set P : ℝ := ((Nat.choose 15 8 : ℝ) + Cφ) / a ^ 8 with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨r, |B1| * (2 + |L1| * P) * B * |MH|, hrpos, by positivity, fun t ht0 ht1 ht hrt => ?_⟩
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hr1 : r ≤ 1 / 4 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hra : r ≤ a / 2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr1' : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hrH' : r < rH := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have htr1 : ‖t‖ ≤ 1 / 4 := hrt.trans hr1
  -- the four factors
  have hK : ‖mellinK0 c t (fctXi1 L1)‖ ≤ |B1| := (hB1 t (by linarith)).trans (le_abs_self _)
  have hG : ‖stripG t‖ ≤ 2 * ‖t‖ ^ 2 := by
    have h := stripG_sub_le htr1
    have h1 : ‖(Real.pi ^ 2 / 12 : ℂ) * t ^ 2‖ ≤ ‖t‖ ^ 2 := by
      rw [norm_mul, norm_pow]
      have : ‖(Real.pi ^ 2 / 12 : ℂ)‖ ≤ 1 := by
        rw [show (Real.pi ^ 2 / 12 : ℂ) = ((Real.pi ^ 2 / 12 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        have : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
        linarith
      nlinarith [sq_nonneg ‖t‖]
    have hsq : ‖t‖ ^ 2 ≤ 1 / 16 := by nlinarith [norm_nonneg t]
    have h2 : 10 * ‖t‖ ^ 4 ≤ ‖t‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖t‖)]
    nlinarith [norm_sub_norm_le (stripG t) ((Real.pi ^ 2 / 12 : ℂ) * t ^ 2)]
  have hφ : ‖FctPhiKill.phiKill a t‖ ≤ P * ‖t‖ ^ 2 := by
    have h := hCφ (a := a) (z := t) hapos (hrt.trans hra)
    have hx : ‖t‖ / a ≤ 1 / 2 := by rw [div_le_iff₀ hapos]; linarith
    have hx0 : 0 ≤ ‖t‖ / a := by positivity
    have h8 : ‖(((Nat.choose 15 8 : ℝ)) : ℂ) * (t / a) ^ 8‖ = (Nat.choose 15 8 : ℝ) * (‖t‖ / a) ^ 8 := by
      rw [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Complex.norm_real, Real.norm_of_nonneg hapos.le]
    have h9 : (‖t‖ / a) ^ 9 ≤ (‖t‖ / a) ^ 8 := by
      rw [pow_succ]; nlinarith [pow_nonneg hx0 8]
    have h10 : (‖t‖ / a) ^ 8 ≤ ‖t‖ ^ 2 / a ^ 8 := by
      rw [div_pow]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc ‖t‖ ^ 8 = ‖t‖ ^ 2 * ‖t‖ ^ 6 := by ring
        _ ≤ ‖t‖ ^ 2 * 1 := by gcongr; exact pow_le_one₀ (norm_nonneg _) (hrt.trans hr1')
        _ = _ := mul_one _
    have h11 := norm_sub_norm_le (FctPhiKill.phiKill a t) ((((Nat.choose 15 8 : ℝ)) : ℂ) * (t / a) ^ 8)
    rw [h8] at h11
    have h12 : ‖FctPhiKill.phiKill a t‖ ≤ ((Nat.choose 15 8 : ℝ) + Cφ) * (‖t‖ / a) ^ 8 := by
      nlinarith [pow_nonneg hx0 8, mul_le_mul_of_nonneg_left h9 hCφ0, h, h11]
    refine h12.trans ?_
    rw [hP]
    calc ((Nat.choose 15 8 : ℝ) + Cφ) * (‖t‖ / a) ^ 8 ≤ ((Nat.choose 15 8 : ℝ) + Cφ) * (‖t‖ ^ 2 / a ^ 8) := by gcongr
      _ = _ := by ring
  have htS : t ∈ closedStrip := ⟨ht0, ht1.le⟩
  have hDb : ‖fctDcompAt K4 c α t‖ ≤ B := hB t htS
  have hHG : ‖ctHG ε t‖ ≤ |MH| * ‖t‖ ^ (-(5 / 2 : ℝ)) :=
    (hHb t htS ht (hrt.trans_lt hrH')).trans (by gcongr; exact le_abs_self _)
  have hsum : ‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill a t‖ ≤ (2 + |L1| * P) * ‖t‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hφ (abs_nonneg L1)]
  have hpow : ‖t‖ ^ 2 * ‖t‖ ^ (-(5 / 2 : ℝ)) = ‖t‖ ^ (-(1 / 2 : ℝ)) := by
    rw [show ‖t‖ ^ 2 = ‖t‖ ^ (2 : ℝ) by norm_cast, ← Real.rpow_add htpos]; norm_num
  unfold fctWarpKA fctWarpA
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖mellinK0 c t (fctXi1 L1)‖ * (‖stripG t + (L1 : ℂ) * FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ))) t‖ *
        ‖fctDcompAt K4 c α t‖ * ‖ctHG ε t‖)
      ≤ |B1| * (((2 + |L1| * P) * ‖t‖ ^ 2) * B * (|MH| * ‖t‖ ^ (-(5 / 2 : ℝ)))) := by
        gcongr
    _ = |B1| * (2 + |L1| * P) * B * |MH| * (‖t‖ ^ 2 * ‖t‖ ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [hpow]

/-- A function continuous on `(0, 1]` with `‖g s‖ ≤ M s^{-1/2}` near `0` is interval integrable on `[0, 1]`. -/
lemma intervalIntegrable_of_rpow_bound {g : ℝ → ℂ} (hg : ContinuousOn g (Ioc 0 1)) {r M : ℝ} (hr : 0 < r)
    (hb : ∀ s ∈ Ioc (0 : ℝ) r, ‖g s‖ ≤ M * s ^ (-(1 / 2 : ℝ))) : IntervalIntegrable g volume 0 1 := by
  set r' : ℝ := min r 1 with hr'
  have hr'pos : 0 < r' := lt_min hr one_pos
  have hr'1 : r' ≤ 1 := min_le_right _ _
  have h1 : IntervalIntegrable g volume 0 r' := by
    have hint : IntervalIntegrable (fun x : ℝ => M * x ^ (-(1 / 2 : ℝ))) volume 0 r' :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul M
    refine hint.mono_fun' ?_ ?_
    · rw [Set.uIoc_of_le hr'pos.le]
      exact (hg.mono (Ioc_subset_Ioc_right hr'1)).aestronglyMeasurable measurableSet_Ioc
    · rw [Set.uIoc_of_le hr'pos.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hb s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have h2 : IntervalIntegrable g volume r' 1 := by
    refine (hg.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hr'1]
    exact fun s hs => ⟨hr'pos.trans_le hs.1, hs.2⟩
  simpa using h1.trans h2

/-- **The segment integrand of `Ψ_c` is integrable** (`(fct:A-Psi-def)`): for `c > 0`, `D_{τ₁}` a `CompData`-type factor (continuous and bounded on the
closed strip) and `0 ≤ Re ζ < 1`, `s ↦ K₀(sζ, ξ₁) A_ε(sζ)` is interval integrable on `[0, 1]`. -/
lemma fctWarpKA_segment_integrable {K4 ε c L1 α : ℝ} (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    IntervalIntegrable (fun s : ℝ => fctWarpKA K4 ε c L1 α ((s : ℂ) * ζ)) volume 0 1 := by
  by_cases hζ : ζ = 0
  · subst hζ
    simp only [mul_zero]
    exact intervalIntegrable_const
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  obtain ⟨r, M, hr, hM, hbd⟩ := fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) hc hDb
  refine intervalIntegrable_of_rpow_bound (r := min 1 (r / ‖ζ‖)) (M := M * ‖ζ‖ ^ (-(1 / 2 : ℝ))) ?_ (lt_min one_pos (by positivity)) ?_
  · refine (fctWarpKA_continuousOn (ε := ε) (L1 := L1) hc hDc).comp (by fun_prop) fun s hs => ?_
    refine ⟨?_, ?_, ?_⟩
    · simpa using mul_nonneg hs.1.le h0
    · have : ((s : ℂ) * ζ).re = s * ζ.re := by simp
      rw [this]
      nlinarith [hs.1, hs.2]
    · exact mul_ne_zero (by exact_mod_cast hs.1.ne') hζ
  · intro s hs
    have hsn : ‖(s : ℂ) * ζ‖ = s * ‖ζ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
    have hre : ((s : ℂ) * ζ).re = s * ζ.re := by simp
    have hs1 : s ≤ 1 := hs.2.trans (min_le_left _ _)
    have hsr : s * ‖ζ‖ ≤ r := by
      have := hs.2.trans (min_le_right _ _)
      rwa [le_div_iff₀ hζn] at this
    have hb := hbd ((s : ℂ) * ζ) (by simpa using mul_nonneg hs.1.le h0) (by rw [hre]; nlinarith [hs.1])
      (mul_ne_zero (by exact_mod_cast hs.1.ne') hζ) (by rw [hsn]; exact hsr)
    refine hb.trans (le_of_eq ?_)
    rw [hsn, Real.mul_rpow hs.1.le hζn.le]
    ring

/-- **Measurability of `F` along a vertical line `Re t = σ`, `0 < σ < 1`** (so that the Cauchy integrands of `(fct:Fpm-def)` are measurable): the
segment integral `ζ ↦ ∫₀¹ f(sζ) ds` is measurable (parametric integral of the measurable extension of `f` by `0`), and `K₀`, `D_{τ₁}`, `H_*/G_ε` are continuous. -/
lemma fctFint_line_measurable {K4 ε c L1 α σ : ℝ} (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Measurable (fun y : ℝ => fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)) := by
  set R : Set ℂ := {t : ℂ | 0 ≤ t.re ∧ t.re < 1 ∧ t ≠ 0} with hR
  have hRm : MeasurableSet R := by
    have h1 : MeasurableSet {t : ℂ | 0 ≤ t.re} := measurableSet_le (measurable_const : Measurable fun _ : ℂ => (0 : ℝ)) Complex.measurable_re
    have h2 : MeasurableSet {t : ℂ | t.re < 1} := measurableSet_lt Complex.measurable_re (measurable_const : Measurable fun _ : ℂ => (1 : ℝ))
    have h3 : MeasurableSet {t : ℂ | t ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
    exact h1.inter (h2.inter h3)
  classical
  set fext : ℂ → ℂ := R.piecewise (fctWarpKA K4 ε c L1 α) (fun _ => 0) with hfext
  have hfm : Measurable fext :=
    (fctWarpKA_continuousOn hc hDc).measurable_piecewise continuousOn_const hRm
  have hΦ : StronglyMeasurable (fun ζ : ℂ => ∫ s in Ioc (0 : ℝ) 1, fext ((s : ℂ) * ζ)) := by
    refine StronglyMeasurable.integral_prod_right (f := fun (ζ : ℂ) (s : ℝ) => fext ((s : ℂ) * ζ)) ?_
    exact (hfm.comp (by fun_prop : Measurable fun p : ℂ × ℝ => (p.2 : ℂ) * p.1)).stronglyMeasurable
  set line : ℝ → ℂ := fun y => (σ : ℂ) + y * Complex.I with hline
  have hlc : Continuous line := by fun_prop
  have hlre : ∀ y, (line y).re = σ := fun y => by simp [hline]
  have hlne : ∀ y, line y ≠ 0 := fun y h => by
    have := congrArg Complex.re h; rw [hlre] at this; simp at this; linarith
  have hlS : ∀ y, line y ∈ edgeStrip := fun y => by
    show |(line y).re| < 1
    rw [hlre, abs_lt]; constructor <;> linarith
  have hlC : ∀ y, line y ∈ closedStrip := fun y => ⟨by rw [hlre]; linarith, by rw [hlre]; linarith⟩
  have hK0 : Continuous fun y => mellinK0 c (line y) (fctXi1 L1) :=
    ((differentiableOn_mellinK0 hc _).continuousOn).comp_continuous hlc hlS
  have hD : Continuous fun y => fctDcompAt K4 c α (line y) := hDc.comp_continuous hlc hlC
  have hH : Continuous fun y => ctHG ε (line y) := by
    refine (ctHG_continuousOn ε).comp_continuous hlc fun y => ⟨hlC y, hlne y, fun h => ?_⟩
    have := congrArg Complex.re h; rw [hlre] at this; simp at this; linarith
  have hΦl : Measurable fun y : ℝ => ∫ s in Ioc (0 : ℝ) 1, fext ((s : ℂ) * line y) := hΦ.measurable.comp hlc.measurable
  have hI : ∀ y : ℝ, (∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * line y)) =
      ∫ s in Ioc (0 : ℝ) 1, fext ((s : ℂ) * line y) := by
    intro y
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1)) fun s hs => ?_
    have hmem : (s : ℂ) * line y ∈ R := by
      refine ⟨?_, ?_, mul_ne_zero (by exact_mod_cast hs.1.ne') (hlne y)⟩
      · have : ((s : ℂ) * line y).re = s * σ := by simp [hline]
        rw [this]; nlinarith [hs.1]
      · have : ((s : ℂ) * line y).re = s * σ := by simp [hline]
        rw [this]; nlinarith [hs.1, hs.2]
    simp only [hfext, Set.piecewise_eq_of_mem _ _ _ hmem]
  have heq : (fun y : ℝ => fctFint K4 ε c L1 α (line y)) = fun y =>
      (c : ℂ) * ((mellinK0 c (line y) (fctXi1 L1))⁻¹ * (line y * ∫ s in Ioc (0 : ℝ) 1, fext ((s : ℂ) * line y))) /
        (fctDcompAt K4 c α (line y) * ctHG ε (line y)) - 1 := by
    funext y
    unfold fctFint fctPhiC fctPsi
    rw [← hI y]
    rfl
  show Measurable (fun y : ℝ => fctFint K4 ε c L1 α (line y))
  rw [heq]
  exact (((measurable_const.mul (hK0.measurable.inv.mul ((hlc.measurable).mul hΦl))).div (hD.measurable.mul hH.measurable))).sub measurable_const

/-- **Measurability of the Cauchy integrand in `y`** (`0 < σ < 1`, any `ζ`). -/
lemma fctCauchyIntegrand_measurable {K4 ε c L1 α σ : ℝ} (hc : 0 < c)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip) (hσ0 : 0 < σ) (hσ1 : σ < 1) (ζ : ℂ) :
    Measurable (fctCauchyIntegrand K4 ε c L1 α σ ζ) := by
  have hFm := fctFint_line_measurable (ε := ε) (L1 := L1) (α := α) hc hDc hσ0 hσ1
  unfold fctCauchyIntegrand fctKsp
  exact ((((by fun_prop : Measurable fun y : ℝ => (ζ / ((σ : ℂ) + y * Complex.I)) ^ 3).mul
    (by fun_prop : Measurable fun y : ℝ => (((σ : ℂ) + y * Complex.I + 1) / (ζ + 1)) ^ 2)).mul hFm).div
    (by fun_prop : Measurable fun y : ℝ => (σ : ℂ) + y * Complex.I - ζ))

/-- **The Cauchy integrand of `(fct:Fpm-def)` is integrable on `Re t = σ`** (`3/8 ≤ σ ≤ 7/16`, `Re ζ ≠ σ`) when `F` is bounded there. -/
lemma fctCauchyIntegrand_integrable {K4 ε c L1 α σ : ℝ} (hc : 0 < c) (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hσ : 3 / 8 ≤ σ) (hσ' : σ ≤ 7 / 16) {ζ : ℂ} (hd : ζ.re ≠ σ) {B : ℝ}
    (hF : ∀ y : ℝ, ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B) :
    Integrable (fctCauchyIntegrand K4 ε c L1 α σ ζ) := by
  obtain ⟨K, hK0, hK⟩ := fctKsp_div_le hσ hσ' hd
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF 0)
  have hm := fctCauchyIntegrand_measurable (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDc (by linarith : 0 < σ) (by linarith : σ < 1) ζ
  refine Integrable.mono' (integrable_inv_one_add_abs_sq.const_mul (K * B)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  unfold fctCauchyIntegrand
  rw [mul_div_right_comm, norm_mul]
  calc _ ≤ (K / (1 + |y|) ^ 2) * B := mul_le_mul (hK y) (hF y) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- **`FctSplittingIntStmt`** (no Bochner junk value in `fctPsi`, `fctCauchy`), from the descent bound `(fct:F-38-bnd)` (`K₄ ≥ 1`): the segment integrand is integrable by the
`|t|^{-1/2}` bound at `0` (`fctWarpKA_near_zero`) and continuity, and the Cauchy integrands by `|K_sp F/(t-ζ)| ≤ K (1+|y|)⁻²`. -/
theorem fctSplittingInt_of_descent {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    FctSplittingIntStmt h := by
  obtain ⟨C, c₀, hC⟩ := hD
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |fctWarpAlpha h ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨cD, hcD⟩ := fctDcomp_compData hK4 hα
  refine ⟨max (max c₀ cD) 1, fun ε c hε hc => ?_⟩
  have hc1 : 1 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hDD := hcD ε c hε ((le_max_right _ _).trans ((le_max_left _ _).trans hc))
  have hDc : ContinuousOn (fctDcompAt K4 c (fctWarpAlpha h ε c)) closedStrip := hDD.cont
  have hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c (fctWarpAlpha h ε c) ζ‖ ≤ B := hDD.bd
  have hFB : ∀ σ : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ∀ y : ℝ,
      ‖fctFint K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((σ : ℂ) + y * Complex.I)‖ ≤ |C| * c⁻¹ / Real.log 2 := by
    intro σ h1 h2 y
    refine (hC ε c hε ((le_max_left _ _).trans ((le_max_left _ _).trans hc)) σ y (by linarith) h2).trans ?_
    have hl : Real.log 2 ≤ Real.log (2 + |y|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg y])
    have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc C * c⁻¹ / Real.log (2 + |y|) ≤ |C| * c⁻¹ / Real.log (2 + |y|) := by
          gcongr
          · exact (Real.log_pos (by linarith [abs_nonneg y])).le
          · exact le_abs_self C
      _ ≤ |C| * c⁻¹ / Real.log 2 := by gcongr
  refine ⟨fun ζ h0 h1 => ?_, fun ζ h0 h1 => ?_, fun ζ h1 => ?_⟩
  · exact fctWarpKA_segment_integrable hcpos hDc hDb h0 (by linarith)
  · exact fctCauchyIntegrand_integrable hcpos hDc (by norm_num) le_rfl (by simpa using h1.ne) (hFB _ (by norm_num) le_rfl)
  · exact fctCauchyIntegrand_integrable hcpos hDc (σ := 3 / 8) le_rfl (by norm_num) (by simp; linarith) (hFB _ le_rfl (by norm_num))

/-- info: 'FormalResearch.SignUncertainty.fctSplittingInt_of_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplittingInt_of_descent

end FormalResearch.SignUncertainty
