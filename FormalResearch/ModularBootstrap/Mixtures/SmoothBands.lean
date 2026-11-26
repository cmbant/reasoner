module

public import FormalResearch.ModularBootstrap.Mixtures.SmoothPointwise
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpVacuumBands

/-!
# The integrand of the vacuum functional for a smooth weight: continuity, integrability, lobe, far band

`positive_mixtures.tex`, Lemma PM.6 (`pmix:smooth`), proof, items 1-2 (deep lobe and outer band).  For a `SmoothWeight W`
and the bumped ramped comb of weight `w` (which depends on the weight only), `rampedBumpFS W bd P d c' N'` is the
integrand `h₀^{(p)} V` of the vacuum functional.  The three lemmas are the abstract-weight forms of `rampedBump_props`,
`rampedBump_lobe_nonpos`, `rampedBump_far` (`RampedBumpVacuumBands`, W-P6); the comb data (decay of `h₀`, the sign of `h₀`
on the lobe) are taken from the source-free `K7` conclusion and the lobe lemma at the trivial product `Q ≡ 1` of weight `w`.

* `rampedBump_props_S`: `F` continuous on `[0, ∞)` and integrable on `(0, ∞)` (continuity and `V ≤ C_d K_a`);
* `rampedBump_lobe_nonpos_S`: `F ≤ 0` on the deep lobe `t ≤ c'(ξ_*/2)²/3` (`V ≥ 0`, `h₀^{(p)} ≤ 0` there);
* `rampedBump_far_S`: `∫_{x ≥ ξ_*+1/2} |F| ≤ C_far √c'` (hypothesis (ii), the far-band bound with `K_2 = w - 1`).

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.FixedWeight FormalResearch.Special
  FormalResearch.ModularBootstrap.Upper.Window.Tail FormalResearch.ModularBootstrap.Upper.Hankel

/-- The integrand `h₀^{(p)} V` of the vacuum functional of the bumped ramped design with cut `N'`, for the weight family
of a `SmoothWeight`. -/
noncomputable def rampedBumpFS {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (bd : BumpData) (P : RampedParams)
    (d c' : ℝ) (N' : ℕ) (t : ℝ) : ℝ :=
  combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
    (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t * W.V c' t

/-- Continuity on `[0, ∞)` and integrability on `(0, ∞)` of `F_b`, uniformly in the cut `N' ≥ n_cap + 6`. -/
theorem rampedBump_props_S {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (bd : BumpData) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      ContinuousOn (rampedBumpFS W bd P d c' N') (Ici 0) ∧ IntegrableOn (rampedBumpFS W bd P d c' N') (Ioi 0) := by
  filter_upwards [rampedBumped_k7 (trivialProductProblem w hw) bd, ramped_phaseHyp,
    bumped_phaseHyp bd 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    eventually_ge_atTop W.c₀, eventually_gt_atTop (0 : ℝ)]
    with c' hK7 hph hbph hin hcS hpos d hd0 hd1 N' hN'
  have hph' := hbph (nCap P c' + 6) N' (rampedSigma d c') (rampedEps P c') 1 (hph P d hd0 hd1) hN'
  have hI := hin N' _ _ hph'.1 hph'.2.1
  obtain ⟨C, hC0, hdec, -⟩ := hK7 P d hd0 hd1 N' hN'
  have hcont := hI.continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := w) hw hpos hcont hdec
  refine ⟨hcont.mul (W.cont hcS).continuousOn, ?_⟩
  refine (hk.const_mul W.Cd).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact (hcont.mono Ioi_subset_Ici_self).mul (W.cont hcS).continuousOn |>.aestronglyMeasurable
      measurableSet_Ioi
  · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    unfold rampedBumpFS
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (W.nonneg hcS ht0)]
    calc |combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
          (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t| * W.V c' t
        ≤ |combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
          (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t| * (W.Cd * kernelK w (c' / 12) t) :=
          mul_le_mul_of_nonneg_left (W.dom hcS ht0) (abs_nonneg _)
      _ = W.Cd * (|combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
          (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t| * kernelK w (c' / 12) t) := by ring

/-- The negative lobe `x ≤ ξ_*/2` carries `F_b ≤ 0`. -/
theorem rampedBump_lobe_nonpos_S {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (bd : BumpData) (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      ∀ t ∈ Ioc 0 (c' * (xiStar / 2) ^ 2 / 3), rampedBumpFS W bd P d c' N' t ≤ 0 := by
  filter_upwards [rampedBump_lobe_nonpos (trivialProductProblem w hw) bd P, eventually_ge_atTop W.c₀,
    eventually_gt_atTop (0 : ℝ)] with c' hlobe hcS hpos d hd0 hd1 N' hN' t ht
  have h1 := hlobe d hd0 hd1 N' hN' t ht
  unfold rampedBumpF at h1
  have hKpos : 0 < (trivialProductProblem w hw).cardyV (c' / 12) t := by
    refine (trivialProductProblem w hw).cardyV_pos ?_ ht.1
    simp only [trivialProductProblem_totalShift]
    positivity
  have hneg : combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
      (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos hcon hKpos
    linarith
  unfold rampedBumpFS
  exact mul_nonpos_of_nonpos_of_nonneg hneg (W.nonneg hcS ht.1.le)

/-- **Far band** (`fw:Ustar`, vacuum step): `∫_{x ≥ ξ_*+1/2} |F_b| ≤ C_far √c'`, `C_far` depending on `w` and the bump only. -/
theorem rampedBump_far_S {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (bd : BumpData) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedBumpFS W bd P d c' N' t|) ≤ Cf * √c' := by
  obtain ⟨C, hC, hfb⟩ := rampedFarBand
  obtain ⟨CF, cF, hCF, hFb⟩ := W.far
  obtain ⟨Cr, hCr, hrfar⟩ := refComb_far_bound (f := 1) le_rfl (η₀ := 1 / 4) (r₀ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hxs := xiStar_pos
  have hx0 : 0 < xiStar + 1 / 2 := by linarith
  set Kb : ℝ := bumpC bd (1 / 4) with hKb
  have hKb0 : 0 < Kb := bumpC_pos bd _
  set p : ℕ := w - 1 with hp
  refine ⟨Kb * (4 * (2 * Cr) * CF * farConstP p) + 1, ?_, fun P => ?_⟩
  · have := farConstP_nonneg p
    positivity
  have hlam_ev : ∀ᶠ c' in atTop, C * lambdaComb c' ≤ 1 := by
    have ht := tendsto_lambdaComb_atTop.const_mul C
    simp only [mul_zero] at ht
    exact ht.eventually_le_const zero_lt_one
  filter_upwards [hfb, eventually_ge_atTop cF, eventually_gt_atTop (0 : ℝ), hlam_ev, hrfar,
    eventually_ge_atTop W.c₀, rampedBump_profile_eq bd P,
    bumpFactor_one_le bd (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le bd (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c' hfb' hcF hc' hlam hrfar' hcS hprofeq hR1 hRK d hd0 hd1 N' hN'
  have hCc : (0 : ℝ) ≤ Kb * (4 * (2 * Cr) * CF * √c') := by positivity
  set Bb : ℂ → ℂ := designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
    (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) with hBb
  have hfin : ∀ x ∈ Ici (xiStar + 1 / 2), 0 < x ∧
      0 ≤ |combProfile c' Bb (c' * x ^ 2 / 3)| * W.V c' (c' * x ^ 2 / 3) ∧
      (2 * c' * x / 3) * (|combProfile c' Bb (c' * x ^ 2 / 3)| * W.V c' (c' * x ^ 2 / 3)) ≤
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
    have hA0 : 0 ≤ |combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| * W.V c' (c' * x ^ 2 / 3) :=
      mul_nonneg (abs_nonneg _) hv0
    have hP : 0 ≤ (2 * c' * x / 3) := by positivity
    calc (2 * c' * x / 3) * (Rb * |combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| *
          W.V c' (c' * x ^ 2 / 3))
        = Rb * ((2 * c' * x / 3) * (|combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3)| *
          W.V c' (c' * x ^ 2 / 3))) := by ring
      _ ≤ Kb * (4 * (2 * Cr) * CF * √c' * (x ^ (1 / 2 : ℝ) * (1 + x) ^ p * exp (-π * x))) :=
          mul_le_mul hRKx hbase (mul_nonneg hP hA0) hKb0.le
      _ = _ := by ring
  have hfar := far_integral_leP p (g := fun t => |combProfile c' Bb t| * W.V c' t) hc'
    hx0 hCc hfin
  have hs : 0 ≤ √c' := Real.sqrt_nonneg _
  calc (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedBumpFS W bd P d c' N' t|)
      = ∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |combProfile c' Bb t| * W.V c' t := by
        refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
        have ht0 : 0 ≤ t := le_trans (by positivity) ht
        unfold rampedBumpFS
        rw [abs_mul, abs_of_nonneg (W.nonneg hcS ht0)]
    _ ≤ Kb * (4 * (2 * Cr) * CF * √c') * farConstP p := hfar
    _ ≤ (Kb * (4 * (2 * Cr) * CF * farConstP p) + 1) * √c' := by
        have := farConstP_nonneg p
        nlinarith only [hs, this]


/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rampedBump_props_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_props_S

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rampedBump_lobe_nonpos_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_lobe_nonpos_S

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rampedBump_far_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_far_S

end FormalResearch.ModularBootstrap.Mixtures
