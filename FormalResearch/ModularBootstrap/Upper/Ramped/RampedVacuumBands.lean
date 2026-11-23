module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumWindow

/-!
# The bands of the vacuum integral of the ramped comb (`rem:thmU` Step (5))

For the ramped design `D_*` the vacuum functional of `g = ½(h₀ - ĥ₀)` is `g_vac = ½h_{0,vac} - π ∫ h₀ V`
(`ramped_k7`), `h₀ V = rampedF`.  Besides the Langer window (`RampedVacuumIntegral`) three facts are needed.

* `rampedF_props`: `h₀ V` is continuous on `[0, ∞)` and integrable on `(0, ∞)`;
* `rampedF_lobe_nonpos`: `h₀ V ≤ 0` on the deep lobe `x ≤ ξ_*/2` (`B_{D_*} ≤ 0` to the left of the first zero
  `χ'_1 ≥ ξ_*`);
* `rampedF_far_le`: the far band `x ≥ ξ_* + 1/2` carries `∫ |h₀| V ≤ C_far √c'`, `C_far` absolute
  (`rampedFarBand`: `0 < B_{D_*} ≤ (1 + Cλ) B_ref`, `K6`(a) and `A_V`).

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window.Tail
  FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Holes

/-- The integrand `h₀ V` of the vacuum functional of the ramped design. -/
noncomputable def rampedF (prob : Crossing.FixedWeightProblem) (P : RampedParams) (d c' : ℝ) (t : ℝ) : ℝ :=
  combProfile c' (rampedComb P d c') t * prob.cardyV (c' / 12) t

theorem rampedF_props (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ContinuousOn (rampedF prob P d c') (Ici 0) ∧ IntegrableOn (rampedF prob P d c') (Ioi 0) := by
  obtain ⟨K, hK, hk7⟩ := ramped_k7 hw
  filter_upwards [hk7, ramped_phaseHyp,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop (12 * prob.totalShift), eventually_gt_atTop (0 : ℝ)]
    with c' hK7 hPh hin hcS hpos d hd0 hd1
  have hI := hin _ _ _ (hPh P d hd0 hd1).1 (hPh P d hd0 hd1).2.1
  obtain ⟨C, hC0, hdec, -⟩ := hK7 P d hd0 hd1
  have hcont := hI.continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := prob.w) prob.hw hpos hcont hdec
  exact ⟨hcont.mul (Crossing.continuous_cardyV prob (c' / 12)).continuousOn,
    integrableOn_mul_cardyV (prob := prob)
      (by linarith) hcont hk⟩

/-- The negative lobe `x ≤ ξ_*/2` carries `h₀ V ≤ 0`. -/
theorem rampedF_lobe_nonpos (prob : Crossing.FixedWeightProblem) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ∀ t ∈ Ioc 0 (c' * (xiStar / 2) ^ 2 / 3), rampedF prob P d c' t ≤ 0 := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [h_ev, eventually_ge_atTop (12 * prob.totalShift), eventually_gt_atTop (0 : ℝ)]
    with c' ⟨_, _, _, hgap⟩ hcS hcpos d hd0 hd1 t ht
  have hxs := xiStar_pos
  have hx := xOf_le_of_le hcpos (by linarith : 0 ≤ xiStar / 2) ht.2
  have hx1 : xOf c' t < designSite c' (rampedSigma d c') 1 :=
    lt_of_le_of_lt hx (by linarith [designSite_ramped_nonneg hcpos hd0 (k := 1) le_rfl])
  have hV : 0 ≤ prob.cardyV (c' / 12) t :=
    prob.cardyV_nonneg (by linarith) ht.1.le
  unfold rampedF
  refine mul_nonpos_of_nonpos_of_nonneg ?_ hV
  have hre := designComb_re_nonpos_of_lt hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4) le_rfl hgap
    (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') (xOf_nonneg c' t) hx1
  unfold combProfile combH0
  rw [Membership.sechSqProfile_ofReal, Complex.re_ofReal_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hre

/-- **Far band** (`rem:thmU` Step (5)): `∫_{x ≥ ξ_*+1/2} |h₀| V ≤ C_far √c'`, `C_far` absolute. -/
theorem rampedF_far_le (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) : ∃ Cf : ℝ, 0 < Cf ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
    (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedF prob P d c' t|) ≤ Cf * √c' := by
  obtain ⟨C, hC, hfb⟩ := rampedFarBand
  obtain ⟨CF, cF, hCF, hFb⟩ := cardyFarBound_prob prob hw (x₀ := xiStar + 1 / 2) (by linarith [xiStar_pos])
  obtain ⟨Cr, hCr, hrfar⟩ := refComb_far_bound (f := 1) le_rfl (η₀ := 1 / 4) (r₀ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hxs := xiStar_pos
  have hx0 : 0 < xiStar + 1 / 2 := by linarith
  refine ⟨4 * (2 * Cr) * CF * farConst + 1, ?_, fun P => ?_⟩
  · have := farConst_nonneg
    positivity
  have hlam_ev : ∀ᶠ c' in atTop, C * lambdaComb c' ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.const_mul C
    simp only [mul_zero] at ht
    exact ht.eventually_le_const zero_lt_one
  filter_upwards [hfb, eventually_ge_atTop cF, eventually_gt_atTop (0 : ℝ), hlam_ev, hrfar,
    eventually_ge_atTop (12 * prob.totalShift)]
    with c' hfb' hcF hc' hlam hrfar' hcS d hd0 hd1
  have hfin : ∀ x ∈ Ici (xiStar + 1 / 2), 0 < x ∧
      0 ≤ prob.cardyV (c' / 12) (c' * x ^ 2 / 3) ∧
      (2 * c' * x / 3) * (|combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| *
        prob.cardyV (c' / 12) (c' * x ^ 2 / 3)) ≤
        4 * (2 * Cr) * CF * √c' * (x ^ (1 / 2 : ℝ) * exp (-π * x)) := by
    intro x hx
    have hx' : xiStar + 1 / 2 ≤ x := hx
    have hxpos : 0 < x := by linarith
    obtain ⟨hv0, hw⟩ := hFb (c') hcF x hx'
    refine ⟨hxpos, hv0, ?_⟩
    obtain ⟨_, hBn⟩ := hfb' P d hd0 hd1 x hx'
    have hl2 : 1 + C * lambdaComb c' ≤ 2 := by linarith
    have hB : ‖rampedComb P d c' (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ 2 * Cr :=
      calc ‖rampedComb P d c' (x : ℂ)‖ * exp (c' * Bessel.besselL x)
          ≤ (2 * ‖refComb c' 1 (1 / 4) (x : ℂ)‖) * exp (c' * Bessel.besselL x) := by
            refine mul_le_mul_of_nonneg_right (hBn.trans ?_) (exp_pos _).le
            exact mul_le_mul_of_nonneg_right hl2 (norm_nonneg _)
        _ = 2 * (‖refComb c' 1 (1 / 4) (x : ℂ)‖ * exp (c' * Bessel.besselL x)) := by ring
        _ ≤ 2 * Cr := by have := hrfar' x hx'; linarith
    exact integrand_far_le (B := rampedComb P d c') hc' hxpos hv0 hB hw
  have := far_integral_le (B := rampedComb P d c')
    (V := fun c' t => prob.cardyV (c' / 12) t) hc' hx0
    (by have := hCr; have := hCF; positivity : (0 : ℝ) ≤ 4 * (2 * Cr) * CF * √c') hfin
  have hs : 0 ≤ √c' := Real.sqrt_nonneg _
  calc (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedF prob P d c' t|)
      = ∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |combProfile c' (rampedComb P d c') t| *
          prob.cardyV (c' / 12) t := by
        refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
        have ht0 : 0 ≤ t := le_trans (by positivity) ht
        unfold rampedF
        exact abs_profile_mul prob hcS _ ht0
    _ ≤ 4 * (2 * Cr) * CF * √c' * farConst := this
    _ ≤ (4 * (2 * Cr) * CF * farConst + 1) * √c' := by nlinarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedF_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedF_props

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedF_lobe_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedF_lobe_nonpos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedF_far_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedF_far_le

end FormalResearch.ModularBootstrap.Upper.Ramped
