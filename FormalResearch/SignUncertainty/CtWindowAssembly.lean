module

public import FormalResearch.SignUncertainty.CtWindowTransport
public import FormalResearch.SignUncertainty.CtHalfMoment

/-!
# `ct:dyadic` (4), `window` Step W8: assembly of the window bound

Combines `CtWindowTransport.ct_window_of_half_moment` (`ct:cfu` (1) in the Hankel chart,
`ct:H2-orth` cancellation, sub-chart tail, and change of variable `x = φ_c(u)`),
`CtHalfMoment.hankel_neg_half_moment_le` (negative half-moment via the scale-`r` dyadic
absorption), and `CtDyadicCombined.taperBand_pm` (`0 ≤ ctRprime ε c R ≤ R`) to discharge the
remaining open piece `window` of `(ct:combined)`.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- **Window step of `ct:dyadic` (4) (`(ct:combined)`, `constant_terms_lower.tex`)**:
for every sufficiently small `c₁ > 0`, at every good radius
`R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]` in the violator regime `T < cξ(a₁)`,
`ctKin R ε c f + ctOscS1 R ε c f = O(c⁻¹ ctEta c₁ ε c f R + c^{-4/3} log c)`. -/
theorem ct_combined_window :
    ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
      CtDyadicBound c₁ fun R ε c f => ctKin R ε c f + ctOscS1 R ε c f := by
  obtain ⟨c₁₀, hc₁₀, hwin⟩ := ct_window_of_half_moment
  obtain ⟨C_half, c₀_half, hC_half, hc₀_half, hhm⟩ := hankel_neg_half_moment_le
  obtain ⟨γ_tb, hγ_tb, htb⟩ := taperBand_pm
  refine ⟨min c₁₀ (min γ_tb (1 / 200 : ℝ)), lt_min hc₁₀ (lt_min hγ_tb (by norm_num)),
    fun c₁ hc₁ hle => ?_⟩
  have hle1 : c₁ ≤ c₁₀ := hle.trans (min_le_left _ _)
  have hle2 : c₁ ≤ γ_tb := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle200 : c₁ ≤ 1 / 200 := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C_w, c₀_w, hC_w, hc₀_w, hw⟩ := hwin c₁ hc₁ hle1
  obtain ⟨c₀_tb, hc₀_tb, hband⟩ := htb c₁ hc₁ hle2
  refine ⟨C_w * (1 + C_half), max c₀_w (max c₀_half (max c₀_tb (max 1e14 ((1 / c₁) ^ 3)))), ?_⟩
  intro c hc ε hε T f hf hmass hT _hgap R hR _hgood
  have hc_w : c₀_w ≤ c := (le_max_left _ _).trans hc
  have hc_h : c₀_half ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc_tb : c₀_tb ≤ c :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
  have hc14 : 1e14 ≤ c :=
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hc_c1 : (1 / c₁) ^ 3 ≤ c :=
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hc0 : 0 < c := by linarith
  have h1_le_R : 1 ≤ R := by
    have hc123 : (1 / c₁) ^ 2 ≤ c ^ (2 / 3 : ℝ) := by
      have h1 : ((1 / c₁) ^ 3 : ℝ) ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hc_c1 (by norm_num)
      have h2 : ((1 / c₁) ^ (3 : ℕ) : ℝ) ^ (2 / 3 : ℝ) = (1 / c₁) ^ 2 := by
        rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]
        norm_num
      linarith only [h1, h2]
    have hmul : 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
      have h1 : c₁ ^ 2 * (1 / c₁) ^ 2 = 1 := by field_simp [hc₁.ne']
      calc (1 : ℝ) = c₁ ^ 2 * (1 / c₁) ^ 2 := h1.symm
        _ ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hc123 (by positivity)
    exact hmul.trans hR.1
  have hb_R := hband c hc_tb ε hε R hR.1 hR.2
  have hR'_0 : 0 ≤ ctRprime ε c R := by linarith [hb_R.Rprime_ge]
  have hR'_ub : ctRprime ε c R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have hc1sq : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by
      have : c₁ ^ 2 ≤ (1 / 200 : ℝ) ^ 2 := by nlinarith
      linarith
    have h4 : 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hc1sq (Real.rpow_nonneg hc0.le _)
    exact hb_R.Rprime_le.trans (hR.2.trans h4)
  have hw_R := hw c hc_w ε hε f hf.toIsHankelEigenfn hmass R hR
  have hhm_R := hhm c ε T (ctRprime ε c R) f hc_h hf hε hmass hT hR'_0 hR'_ub
  have hη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R :=
    mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f (by linarith only [h1_le_R]))
  have hc43 : 0 ≤ c ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hlog : 0 ≤ Real.log c := Real.log_nonneg (by linarith only [hc14])
  have hterm :
      c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ)) * Real.log c +
        c ^ (-(4 / 3 : ℝ)) *
          ∫ v in Set.Ioo (0 : ℝ) (ctRprime ε c R), (1 + v) ^ (1 / 2 : ℝ) * |hankelPsiR c f (-v)| ≤
      (1 + C_half) * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3 : ℝ)) * Real.log c) := by
    have hmul := mul_le_mul_of_nonneg_left hhm_R hc43
    have hadd_η : 0 ≤ C_half * (c⁻¹ * ctEta c₁ ε c f R) := mul_nonneg hC_half.le hη
    nlinarith only [hmul, hadd_η]
  exact hw_R.trans ((mul_le_mul_of_nonneg_left hterm hC_w).trans_eq (by ring))

/-- info: 'FormalResearch.SignUncertainty.ct_combined_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined_window

end FormalResearch.SignUncertainty
