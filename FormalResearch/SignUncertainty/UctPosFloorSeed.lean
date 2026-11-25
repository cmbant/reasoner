module

public import FormalResearch.SignUncertainty.UctAiryTrans
public import FormalResearch.SignUncertainty.HbUpperM1

/-!
# `uct:pos-floor` (1): the globally positive floor seed `S_pos = g₁ + g₁' - f₁/4` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:pos-floor` (1).

`S_pos` is the member `a = -1/4`, `b = c₀ = 1` of the one-level family `airySeedU2 a b c₀ = a f₁ + b g₁ + c₀ g₁'`, so
`exists_hankelEigenfn_lift` (`m ≥ 3`), `hasU2_airySeedU2`, `iDual_bound_e3_airySeed`, `window_translation_airySeed`, `o5_e6_airySeed`
and `hb_estimate_airySeed_uniform_val` apply to it (`m = 4` in the paper).  `S_pos = ceSb (1/4)`.

* `uctSpos_pos`: `S_pos > 0` on `ℝ`.  `uct_pos_floor_one`: the floor `S_pos(-x) ≥ c_pos (1+x)^{-3/2}`, `∫ S_pos = 1 + |a₁'|`,
  and the coefficients `β_∞ = 5/4`, `β_+ = 3/4`, which are linear functionals of the coefficients (`uctBetaInf`, `uctBetaPlus`; the
  asymptotic meaning of `β_∞` is the leading coefficient `(c₀ - a) g₀` of `hb_estimate_airySeed_uniform_val`, that of `β_+` is
  `uctSpos_right_tail` in `UctPosFloorTail`).
* `windowSmooth_ge`, `windowSmooth_floor_ray`, `windowSmooth_floor_compact`: floors of the B-spline smoothing of `S_pos`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `S_pos = g₁ + g₁' - f₁/4` (`(uct:Spos-def)`), the member `a = -1/4`, `b = c₀ = 1` of the one-level family. -/
noncomputable abbrev uctSpos : ℝ → ℝ := airySeedU2 (-1 / 4) 1 1

lemma uctSpos_eq_ceSb : uctSpos = ceSb (1 / 4) := by
  funext u; unfold uctSpos airySeedU2 ceSb; ring

lemma ceG1Deriv_mul_sq (u : ℝ) : ceG1Deriv airyDerivFirstZero u * (u - airyDerivFirstZero) ^ 2 = airyAi' u ^ 2 := by
  have h0 := airyDerivFirstZero_spec.2.2
  by_cases hu : u = airyDerivFirstZero
  · subst hu; simp [h0]
  · unfold ceG1Deriv
    rw [dslope_of_ne _ hu, slope_def_field, h0, sub_zero]
    have : u - airyDerivFirstZero ≠ 0 := sub_ne_zero.mpr hu
    field_simp


lemma airyDerivFirstZero_gt : airyZero 1 < airyDerivFirstZero := airyDerivFirstZero_spec.1
lemma airyDerivFirstZero_lt_zero : airyDerivFirstZero < 0 := airyDerivFirstZero_spec.2.1

lemma airyAi'_sq_ge (u : ℝ) : u * airyAi u ^ 2 ≤ airyAi' u ^ 2 := by
  have h := integral_Ioi_airyAi_sq u
  have : 0 ≤ ∫ t in Ioi u, airyAi t ^ 2 := integral_nonneg fun t => sq_nonneg _
  linarith

/-- Global positivity of `S_pos` (`uct:pos-floor` (1)). -/
theorem uctSpos_pos (u : ℝ) : 0 < uctSpos u := by
  rw [uctSpos_eq_ceSb]
  rcases le_or_gt u (airyZero 1) with hu | hu
  · exact ceSb_pos_of_le (by norm_num) hu
  · have hA : 0 < airyAi u := airyAi_pos_of_gt hu
    have ha1 := airyZero_one
    set a := airyZero 1 with ha
    set d := u - a with hd
    have hd0 : 0 < d := by linarith
    have hf : ceF1 u = airyAi u ^ 2 / d := by
      have := ceF1_mul_sub u; field_simp; linarith
    have hg : ceG1 a u = airyAi u ^ 2 / d ^ 2 := by
      have := ceG1_mul_sub_sq u; field_simp; linarith
    have hg' : 0 ≤ ceG1Deriv airyDerivFirstZero u := by unfold ceG1Deriv; positivity
    unfold ceSb
    rw [hf, hg]
    have hA2 : 0 < airyAi u ^ 2 := by positivity
    rcases le_or_gt d (7 / 2) with hd4 | hd4
    · -- window near the first zero
      have h1 : 0 < airyAi u ^ 2 / d ^ 2 - 1 / 4 * (airyAi u ^ 2 / d) := by
        have : airyAi u ^ 2 / d ^ 2 - 1 / 4 * (airyAi u ^ 2 / d) = airyAi u ^ 2 * (4 - d) / (4 * d ^ 2) := by
          field_simp
        rw [this]
        have : 0 < 4 - d := by linarith
        positivity
      linarith
    · -- u ≥ 1
      have hu1 : 1 ≤ u := by linarith [ha1.1]
      have hup : 0 < u := by linarith
      have hneg := airyDerivFirstZero_lt_zero
      have hgt := airyDerivFirstZero_gt
      set e := u - airyDerivFirstZero with he
      have he0 : 0 < e := by linarith
      have hed : e < d := by rw [he, hd]; linarith
      have hg'e : ceG1Deriv airyDerivFirstZero u = airyAi' u ^ 2 / e ^ 2 := by
        have := ceG1Deriv_mul_sq u; field_simp; linarith
      have hAi' := airyAi'_sq_ge u
      have hle : 1 / 4 * (airyAi u ^ 2 / d) ≤ ceG1Deriv airyDerivFirstZero u := by
        rw [hg'e]
        have h1 : u * airyAi u ^ 2 / e ^ 2 ≤ airyAi' u ^ 2 / e ^ 2 := div_le_div_of_nonneg_right hAi' (by positivity)
        have h2 : 1 / 4 * (airyAi u ^ 2 / d) ≤ u * airyAi u ^ 2 / e ^ 2 := by
          have hd2 : 0 < d := hd0
          have : u * airyAi u ^ 2 / e ^ 2 ≥ u * airyAi u ^ 2 / d ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith
          have h3 : 1 / 4 * (airyAi u ^ 2 / d) ≤ u * airyAi u ^ 2 / d ^ 2 := by
            have h4 : 0 ≤ 4 * u - d := by rw [hd]; linarith [ha1.1]
            have : u * airyAi u ^ 2 / d ^ 2 - 1 / 4 * (airyAi u ^ 2 / d) = airyAi u ^ 2 * (4 * u - d) / (4 * d ^ 2) := by
              field_simp
            have : 0 ≤ airyAi u ^ 2 * (4 * u - d) / (4 * d ^ 2) := by positivity
            linarith
          linarith
        linarith
      have : 0 < airyAi u ^ 2 / d ^ 2 := by positivity
      linarith


/-- `β_∞` of the one-level seed `a f₁ + b g₁ + c g₁'` (`β_∞(-f₁) = 1`, `β_∞(g₁) = 0`, `β_∞(g₁') = 1`, linear; `u1c:U2` (e22)-(e23)):
the leading coefficient `γ₀ = (c₀ - a) g₀` of the high-band estimate `hb_estimate_airySeed_uniform_val`. -/
def uctBetaInf (a _b c : ℝ) : ℝ := c - a

/-- `β_+` of the one-level seed (`β_+(f₁) = 1`, `β_+(g₁) = 0`, `β_+(g₁') = 1`, linear): the coefficient of
`(4π)^{-1} u^{-3/2} e^{-(4/3) u^{3/2}}` in the right-tail asymptotics (see `uctSpos_right_tail`). -/
def uctBetaPlus (a _b c : ℝ) : ℝ := a + c

/-- **`uct:pos-floor` (1)**: floor on the negative ray, integral and tail coefficients. -/
theorem uct_pos_floor_one :
    (∀ u : ℝ, 0 < uctSpos u) ∧
      (∃ cpos : ℝ, 0 < cpos ∧ ∀ x : ℝ, |airyZero 1| ≤ x → cpos * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ uctSpos (-x)) ∧
      ∫ u : ℝ, uctSpos u = 1 + |airyDerivFirstZero| ∧
      Integrable uctSpos ∧ uctBetaInf (-1 / 4) 1 1 = 5 / 4 ∧ uctBetaPlus (-1 / 4) 1 1 = 3 / 4 ∧ 0 < uctBetaPlus (-1 / 4) 1 1 := by
  refine ⟨uctSpos_pos, ?_, ?_, ?_, by norm_num [uctBetaInf], by norm_num [uctBetaPlus], by norm_num [uctBetaPlus]⟩
  · obtain ⟨C, hC, h⟩ := ceSb_lower_floor (b := 1 / 4) (by norm_num)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hneg : -x ≤ airyZero 1 := by
      have := airyZero_neg 1; rw [abs_of_neg this] at hx; linarith
    have := h (-x) hneg
    rw [abs_neg, abs_of_nonneg (by linarith [abs_nonneg (airyZero 1)])] at this
    rw [uctSpos_eq_ceSb]; exact this
  · rw [uctSpos_eq_ceSb]; exact ceSb_integral _
  · rw [uctSpos_eq_ceSb]; exact ceSb_integrable _


/-- A pointwise lower bound for the seed on `[y, y + δ₀]` passes to the B-spline smoothing at `y`. -/
lemma windowSmooth_ge {X : ℝ → ℝ} (hX : Continuous X) {δ₀ : ℝ} (hδ : 0 < δ₀) {m : ℕ} (hm : 1 ≤ m) (y g : ℝ)
    (hg : ∀ t ∈ Icc (0 : ℝ) δ₀, g ≤ X (y + t)) : g ≤ windowSmooth δ₀ m X y := by
  rw [windowSmooth_eq_bspline_integral hX hδ hm y]
  have h1 := bspline_setIntegral_one hm hδ
  have hint : IntegrableOn (fun t => X (y + t) * bspline m δ₀ t) (Icc (0 : ℝ) δ₀) := by
    have hb : IntegrableOn (bspline m δ₀) (Icc (0 : ℝ) δ₀) := by
      by_contra hcon
      rw [integral_undef hcon] at h1; norm_num at h1
    have hc : ContinuousOn (fun t => X (y + t)) (Icc (0 : ℝ) δ₀) := (hX.comp (continuous_const.add continuous_id)).continuousOn
    exact hb.continuousOn_mul hc isCompact_Icc |>.congr_fun (fun t _ => by ring) measurableSet_Icc
  have hb : IntegrableOn (bspline m δ₀) (Icc (0 : ℝ) δ₀) := by
    by_contra hcon
    rw [integral_undef hcon] at h1; norm_num at h1
  calc g = ∫ t in Icc (0 : ℝ) δ₀, g * bspline m δ₀ t := by rw [integral_const_mul, h1, mul_one]
    _ ≤ _ := setIntegral_mono_on (hb.const_mul g) hint measurableSet_Icc fun t ht =>
        mul_le_mul_of_nonneg_right (hg t ht) (bspline_nonneg m hδ t)

/-- Floor of the smoothed seed on the negative ray (`x ≥ |a₁| + 1`, smoothing width `≤ 1`). -/
lemma windowSmooth_floor_ray {δ₀ : ℝ} (hδ : 0 < δ₀) (hδ1 : δ₀ ≤ 1) {m : ℕ} (hm : 1 ≤ m) {cpos : ℝ}
    (hc : ∀ x : ℝ, |airyZero 1| ≤ x → cpos * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ uctSpos (-x)) (hcpos : 0 ≤ cpos)
    {x : ℝ} (hx : |airyZero 1| + 1 ≤ x) :
    cpos * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ windowSmooth δ₀ m uctSpos (-x) := by
  refine windowSmooth_ge (continuous_airySeedU2 _ _ _) hδ hm _ _ fun t ht => ?_
  have h1 := hc (x - t) (by linarith [ht.2, abs_nonneg (airyZero 1)])
  have e : -x + t = -(x - t) := by ring
  rw [e]
  refine le_trans ?_ h1
  have hx0 : 0 < 1 + (x - t) := by linarith [ht.2, abs_nonneg (airyZero 1)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 (by linarith [ht.1]) (by norm_num)) hcpos

/-- Compact floor of the smoothed seed. -/
lemma windowSmooth_floor_compact (A B : ℝ) : ∃ mX : ℝ, 0 < mX ∧ ∀ {δ₀ : ℝ}, 0 < δ₀ → ∀ {m : ℕ}, 1 ≤ m → ∀ y : ℝ,
    -A ≤ y → y + δ₀ ≤ B → mX ≤ windowSmooth δ₀ m uctSpos y := by
  by_cases hAB : -A ≤ B
  · obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hAB) (continuous_airySeedU2 (-1 / 4) 1 1).continuousOn
    refine ⟨uctSpos u₀, uctSpos_pos u₀, fun hδ m hm y hy hyB => ?_⟩
    refine windowSmooth_ge (continuous_airySeedU2 _ _ _) hδ hm _ _ fun t ht => ?_
    exact hmin ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact ⟨1, one_pos, fun hδ m hm y hy hyB => by linarith [hδ]⟩


/-- info: 'FormalResearch.SignUncertainty.uctSpos_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctSpos_pos

/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_one

/-- info: 'FormalResearch.SignUncertainty.windowSmooth_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowSmooth_ge

/-- info: 'FormalResearch.SignUncertainty.windowSmooth_floor_ray' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowSmooth_floor_ray

/-- info: 'FormalResearch.SignUncertainty.windowSmooth_floor_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms windowSmooth_floor_compact

end FormalResearch.SignUncertainty
