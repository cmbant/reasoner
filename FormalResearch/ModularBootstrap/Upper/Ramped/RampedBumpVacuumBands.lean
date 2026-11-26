module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpPositive
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpPointwise
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumBands

/-!
# The bands of the vacuum integral of the bumped ramped comb, every weight (`fw:Ustar`, vacuum step)

For the bumped ramped comb `h₀^{(p)} = R_bump h₀^{D_*}` (`fw:e3.3`) the vacuum functional is
`g_vac = ½ h_{0,vac} - π ∫ h₀^{(p)} V` (`rampedBumped_k7`).  With `F_b = h₀^{(p)} V` (`rampedBumpF`):

* `rampedBump_props`: `F_b` is continuous on `[0, ∞)` and integrable on `(0, ∞)`;
* `rampedBump_lobe_nonpos`: `F_b ≤ 0` on the deep lobe `x ≤ ξ_*/2` (`R_bump ≥ 0`, `B_{D_*} ≤ 0` to the left of `χ'_1`);
* `rampedBump_far`: the far band `x ≥ ξ_* + 1/2` carries `∫ |F_b| ≤ C_far √c'`, `C_far` depending on `(w, K_b)` only
  (`R_bump ≤ K_b`, `rampedFarBand`, `K6`(a) and the order-`p` far Cardy bound `cardyFarBoundP_prob`).

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
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.Special
  FormalResearch.ModularBootstrap.Upper.Holes

/-- The integrand `h₀^{(p)} V` of the vacuum functional of the bumped ramped design with cut `N'`. -/
noncomputable def rampedBumpF (prob : Crossing.FixedWeightProblem) (bd : BumpData) (P : RampedParams)
    (d c' : ℝ) (N' : ℕ) (t : ℝ) : ℝ :=
  combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
    (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t * prob.cardyV (c' / 12) t

/-- `h₀^{(p)} = R_bump · h₀` on the profile (the value identity, `combProfile_bumped_eq`). -/
lemma rampedBump_profile_eq (bd : BumpData) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ (d : ℝ) (N' : ℕ), nCap P c' + 6 ≤ N' → ∀ t : ℝ,
      combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
        (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t =
        bumpFactor bd c' (1 / 4) (nCap P c' + 6) N' (xOf c' t) * combProfile c' (rampedComb P d c') t := by
  filter_upwards [combProfile_bumped_eq bd] with c' hval d N' hN' t
  have hN1 : 1 ≤ nCap P c' + 6 := by omega
  exact hval (nCap P c' + 6) N' (rampedSigma d c') (rampedEps P c') hN1 hN' t

/-- `h₀^{(p)} V = R_bump · h₀ V`. -/
lemma rampedBumpF_eq (prob : Crossing.FixedWeightProblem) (bd : BumpData) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ (d : ℝ) (N' : ℕ), nCap P c' + 6 ≤ N' → ∀ t : ℝ,
      rampedBumpF prob bd P d c' N' t =
        bumpFactor bd c' (1 / 4) (nCap P c' + 6) N' (xOf c' t) * rampedF prob P d c' t := by
  filter_upwards [rampedBump_profile_eq bd P] with c' h d N' hN' t
  unfold rampedBumpF rampedF
  rw [h d N' hN' t]
  ring

/-- Continuity on `[0, ∞)` and integrability on `(0, ∞)` of `F_b`, uniformly in the cut `N' ≥ n_cap + 6`. -/
theorem rampedBump_props (prob : Crossing.FixedWeightProblem) (bd : BumpData) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      ContinuousOn (rampedBumpF prob bd P d c' N') (Ici 0) ∧ IntegrableOn (rampedBumpF prob bd P d c' N') (Ioi 0) := by
  filter_upwards [rampedBumped_k7 prob bd, ramped_phaseHyp,
    bumped_phaseHyp bd 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop (12 * prob.totalShift), eventually_gt_atTop (0 : ℝ)]
    with c' hK7 hph hbph hin hcS hpos d hd0 hd1 N' hN'
  have hph' := hbph (nCap P c' + 6) N' (rampedSigma d c') (rampedEps P c') 1 (hph P d hd0 hd1) hN'
  have hI := hin N' _ _ hph'.1 hph'.2.1
  obtain ⟨C, hC0, hdec, -⟩ := hK7 P d hd0 hd1 N' hN'
  have hcont := hI.continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := prob.w) prob.hw hpos hcont hdec
  exact ⟨hcont.mul (Crossing.continuous_cardyV prob (c' / 12)).continuousOn,
    integrableOn_mul_cardyV (prob := prob) (by linarith) hcont hk⟩

/-- The negative lobe `x ≤ ξ_*/2` carries `F_b ≤ 0`. -/
theorem rampedBump_lobe_nonpos (prob : Crossing.FixedWeightProblem) (bd : BumpData) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      ∀ t ∈ Ioc 0 (c' * (xiStar / 2) ^ 2 / 3), rampedBumpF prob bd P d c' N' t ≤ 0 := by
  filter_upwards [rampedBumpF_eq prob bd P, rampedF_lobe_nonpos prob P,
    bumpFactor_one_le bd (η₀ := 1 / 4) (by norm_num) le_rfl] with c' heq hlobe hR1 d hd0 hd1 N' hN' t ht
  rw [heq d N' hN' t]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hR1 (nCap P c' + 6) N' (xOf c' t)])
    (hlobe d hd0 hd1 t ht)

/-- **Far band** (`fw:Ustar`, vacuum step): `∫_{x ≥ ξ_*+1/2} |F_b| ≤ C_far √c'`, `C_far` depending on `w` and the bump only. -/
theorem rampedBump_far (prob : Crossing.FixedWeightProblem) (bd : BumpData) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedBumpF prob bd P d c' N' t|) ≤ Cf * √c' := by
  obtain ⟨C, hC, hfb⟩ := rampedFarBand
  obtain ⟨CF, cF, hCF, hFb⟩ := cardyFarBoundP_prob prob (x₀ := xiStar + 1 / 2) (by linarith [xiStar_pos])
  obtain ⟨Cr, hCr, hrfar⟩ := refComb_far_bound (f := 1) le_rfl (η₀ := 1 / 4) (r₀ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hxs := xiStar_pos
  have hx0 : 0 < xiStar + 1 / 2 := by linarith
  set Kb : ℝ := bumpC bd (1 / 4) with hKb
  have hKb0 : 0 < Kb := bumpC_pos bd _
  set p : ℕ := prob.w - 1 with hp
  refine ⟨Kb * (4 * (2 * Cr) * CF * farConstP p) + 1, ?_, fun P => ?_⟩
  · have := farConstP_nonneg p
    positivity
  have hlam_ev : ∀ᶠ c' in atTop, C * lambdaComb c' ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.const_mul C
    simp only [mul_zero] at ht
    exact ht.eventually_le_const zero_lt_one
  filter_upwards [hfb, eventually_ge_atTop cF, eventually_gt_atTop (0 : ℝ), hlam_ev, hrfar,
    eventually_ge_atTop (12 * prob.totalShift), rampedBump_profile_eq bd P,
    bumpFactor_one_le bd (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le bd (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c' hfb' hcF hc' hlam hrfar' hcS hprofeq hR1 hRK d hd0 hd1 N' hN'
  have hCc : (0 : ℝ) ≤ Kb * (4 * (2 * Cr) * CF * √c') := by positivity
  set Bb : ℂ → ℂ := designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
    (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) with hBb
  have hfin : ∀ x ∈ Ici (xiStar + 1 / 2), 0 < x ∧
      0 ≤ |combProfile c' Bb (c' * x ^ 2 / 3)| * prob.cardyV (c' / 12) (c' * x ^ 2 / 3) ∧
      (2 * c' * x / 3) * (|combProfile c' Bb (c' * x ^ 2 / 3)| * prob.cardyV (c' / 12) (c' * x ^ 2 / 3)) ≤
        Kb * (4 * (2 * Cr) * CF * √c') * (x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x)) := by
    intro x hx
    have hx' : xiStar + 1 / 2 ≤ x := hx
    have hxpos : 0 < x := by linarith
    obtain ⟨hv0, hw⟩ := hFb (c') hcF x hx'
    obtain ⟨_, hBn⟩ := hfb' P d hd0 hd1 x hx'
    have hl2 : 1 + C * lambdaComb c' ≤ 2 := by linarith
    have hB : ‖rampedComb P d c' (x : ℂ)‖ * exp (c' * Bessel.besselL x) ≤ 2 * Cr :=
      calc ‖rampedComb P d c' (x : ℂ)‖ * exp (c' * Bessel.besselL x)
          ≤ (2 * ‖refComb c' 1 (1 / 4) (x : ℂ)‖) * exp (c' * Bessel.besselL x) := by
            refine mul_le_mul_of_nonneg_right (hBn.trans ?_) (exp_pos _).le
            exact mul_le_mul_of_nonneg_right hl2 (norm_nonneg _)
        _ = 2 * (‖refComb c' 1 (1 / 4) (x : ℂ)‖ * exp (c' * Bessel.besselL x)) := by ring
        _ ≤ 2 * Cr := by have := hrfar' x hx'; linarith
    have hbase := integrand_far_leP p (B := rampedComb P d c') hc' hxpos hv0 hB hw
    have hprof := hprofeq d N' hN' (c' * x ^ 2 / 3)
    rw [xOf_comp hc' hxpos.le] at hprof
    have hR1x := hR1 (nCap P c' + 6) N' x
    have hRKx := hRK (nCap P c' + 6) N' x hxpos.le
    set Rb : ℝ := bumpFactor bd c' (1 / 4) (nCap P c' + 6) N' x with hRb
    have habs : |combProfile c' Bb (c' * x ^ 2 / 3)| =
        Rb * |combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| := by
      rw [hprof, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Rb)]
    refine ⟨hxpos, by positivity, ?_⟩
    rw [habs]
    have hA0 : 0 ≤ |combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| * prob.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
      mul_nonneg (abs_nonneg _) hv0
    have hP : 0 ≤ (2 * c' * x / 3) := by positivity
    calc (2 * c' * x / 3) * (Rb * |combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| *
          prob.cardyV (c' / 12) (c' * x ^ 2 / 3))
        = Rb * ((2 * c' * x / 3) * (|combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| *
          prob.cardyV (c' / 12) (c' * x ^ 2 / 3))) := by ring
      _ ≤ Kb * (4 * (2 * Cr) * CF * √c' * (x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x))) :=
          mul_le_mul hRKx hbase (mul_nonneg hP hA0) hKb0.le
      _ = _ := by ring
  have hfar := far_integral_leP p (g := fun t => |combProfile c' Bb t| * prob.cardyV (c' / 12) t) hc'
    hx0 hCc hfin
  have hs : 0 ≤ √c' := Real.sqrt_nonneg _
  calc (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedBumpF prob bd P d c' N' t|)
      = ∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |combProfile c' Bb t| * prob.cardyV (c' / 12) t := by
        refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
        have ht0 : 0 ≤ t := le_trans (by positivity) ht
        exact abs_profile_mul prob hcS _ ht0
    _ ≤ Kb * (4 * (2 * Cr) * CF * √c') * farConstP p := hfar
    _ ≤ (Kb * (4 * (2 * Cr) * CF * farConstP p) + 1) * √c' := by
        have := farConstP_nonneg p
        nlinarith only [hs, this]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBump_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_props

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBump_lobe_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_lobe_nonpos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBump_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_far

end FormalResearch.ModularBootstrap.Upper.Ramped
