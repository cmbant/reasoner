module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpVacuumBands
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpWindowPart
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuum

/-!
# The vacuum step of Lemma `U*(w)` for the bumped ramped comb, every weight (`fw:Ustar`, Step 5)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), vacuum step, with `upper_transfer.tex` (`ut:Vac`,
`ut:T`, `fw:e3.3`, `fw:e3.6`).

`rampedBumpVacuum`: for every bump `bd`, every `w = p + 1` problem and every `C_I, C_mid ≥ 1` there is `M_0 > 0` such that
for every `P` with these `C_I, C_mid` and `P.M_0 = M_0`, every cut `N' ≥ n_cap + 6` (a function of `c'`) and `c'` large, the
test function `g_w = ½(h₀^{(p)} - 𝓗_w h₀^{(p)})` of the bumped ramped comb at `d = M_0 c'^{-1/3}` has `g_vac > 0`.

The proof follows `rampedVacuum_prob` with three changes: the integrand is `F_b = R_bump h₀ V` (`rampedBump_props`,
`rampedBump_lobe_nonpos`, `rampedBump_far`), the window inequality is `rampedBump_pointwise` (weight `w`, bump multiplier,
`R_bump ≤ K_b` beyond `ξ_* + r_p` absorbed in the error `c₁ λ |σ|`), and `FK_c = FKc (qProb prob) 1 c'` carries
`(2ξ_*)^{w-1}`.

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
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Hankel

/-- **The vacuum step for the bumped ramped comb, every weight** (`fw:Ustar` Step 5): see the module docstring. -/
theorem rampedBumpVacuum (prob : Crossing.FixedWeightProblem) (bd : BumpData) (CI Cmid : ℝ) (hCI : 1 ≤ CI)
    (hCmid : 1 ≤ Cmid) :
    ∃ M0 : ℝ, 0 < M0 ∧ ∀ P : RampedParams, P.CI = CI → P.Cmid = Cmid → P.M0 = M0 →
      ∀ Nc : ℝ → ℕ, (∀ c' : ℝ, nCap P c' + 6 ≤ Nc c') →
      ∀ᶠ c' : ℝ in atTop, 0 < prob.gVac (c' / 12)
        (pairOdd (combProfile c' (designComb c' 1 (Nc c') (1 / 4)
            (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
            (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))))
          (hankelTransform prob.w (combProfile c' (designComb c' 1 (Nc c') (1 / 4)
            (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
            (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c')))))) := by
  obtain ⟨Cf, hCf, hfar⟩ := rampedBump_far prob bd
  obtain ⟨A0, hA0, hFK⟩ := FKc_mul_rpow_eq (qProb_pos prob)
  obtain ⟨P0, hP0I, hP0m⟩ : ∃ P0 : RampedParams, P0.CI = CI ∧ P0.Cmid = Cmid :=
    ⟨⟨CI, Cmid, 1, hCI, hCmid, one_pos⟩, rfl, rfl⟩
  obtain ⟨Cw, CE, hCw, hCE, hevW⟩ := rampedW_package P0
  obtain ⟨c1, c2, hc1, hc2, hpt⟩ := rampedBump_pointwise prob bd
  obtain ⟨T, hT, hwin⟩ := rampedWindow_part_gen c1 c2 hc1 hc2 Cw hCw
  have hCs := CStar_pos
  refine ⟨2 * (CE + T) + 2 + 2 * Cf / (A0 * CStar), by positivity, fun P hPI hPm hPM Nc hNc => ?_⟩
  have hη : ∀ c' : ℝ, rampedEta P c' = rampedEta P0 c' :=
    rampedEta_congr (hPI.trans hP0I.symm) (hPm.trans hP0m.symm)
  have hevW' : ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      (∀ u : ℝ, ‖designAiryW (rampedNode d c') (rampedEta P c') u‖ ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ))) ∧
      Continuous (fun u : ℝ => (designAiryW (rampedNode d c') (rampedEta P c') u).re) ∧
      Integrable (fun u : ℝ => (designAiryW (rampedNode d c') (rampedEta P c') u).re) ∧
      (∫ u : ℝ, (designAiryW (rampedNode d c') (rampedEta P c') u).re) ≤
        -d / 2 + CE * c' ^ (-(1 / 3 : ℝ)) := by
    filter_upwards [hevW] with c' h d hd0 hd1
    rw [hη c']
    exact h d hd0 hd1
  have hFc : ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ContinuousOn (rampedBumpF prob bd P d c' (Nc c')) (Ici 0) := by
    filter_upwards [rampedBump_props prob bd P] with c' h d hd0 hd1 using (h d hd0 hd1 (Nc c') (hNc c')).1
  have hpt' : ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ x ∈ langerX (1 / 2),
      (2 * c' * x / 3) * rampedBumpF prob bd P d c' (Nc c') (c' * x ^ 2 / 3) ≤
        FKc (qProb prob) 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') *
          (rampedWFun P d c' (sigmaOf c' x) + |rampedWFun P d c' (sigmaOf c' x)| *
            (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ)))) := by
    filter_upwards [hpt P] with c' h d hd0 hdD x hx
    exact h d hd0 hdD (Nc c') (hNc c') x hx
  have hwinP := hwin P CE (fun c' => FKc (qProb prob) 1 c')
    (fun d c' => rampedBumpF prob bd P d c' (Nc c')) (fun c' hc' => FKc_pos (qProb_pos prob) 1 hc')
    hevW' hFc hpt'
  have hr0 : Tendsto (fun c' : ℝ => P.M0 * c' ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).const_mul P.M0
  have hd_ev : ∀ᶠ c' : ℝ in atTop, rampedD P c' ≤ rampedD0 :=
    hr0.eventually_le_const rampedD0_pos
  have hbig : ∀ᶠ c' : ℝ in atTop, (2 ^ prob.m / (π * (CStar * A0)) + 1) ^ 2 ≤ c' := eventually_ge_atTop _
  filter_upwards [hwinP, hfar P, rampedBump_props prob bd P, rampedBump_lobe_nonpos prob bd P,
    rampedBumped_k7 prob bd, hd_ev, hbig] with c' hwn hf hprops hlobe hK7 hd hc
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc
  have hxs := xiStar_pos
  have hπ := Real.pi_pos
  have hd0 := rampedD_nonneg P c' hc'0
  have hd1 : rampedD P c' ≤ 1 := hd.trans rampedD0_le_one
  obtain ⟨hcont, hint⟩ := hprops (rampedD P c') hd0 hd1 (Nc c') (hNc c')
  have hneg := hlobe (rampedD P c') hd0 hd1 (Nc c') (hNc c')
  have hwin' := hwn (rampedD P c') hd0 hd
  have hfar' := hf (rampedD P c') hd0 hd1 (Nc c') (hNc c')
  have hsplit := split_integral_le (F := rampedBumpF prob bd P (rampedD P c') c' (Nc c'))
    (tS := c' * (xiStar / 2) ^ 2 / 3) (tΦ := c' * (xiStar + 1 / 2) ^ 2 / 3)
    (tN := c' * (xiStar + 1 / 2) ^ 2 / 3) (tR := c' * (xiStar + 1 / 2) ^ 2 / 3)
    (by positivity) (by positivity) (by nlinarith) le_rfl le_rfl hint hneg
  have hmid : (∫ t in Icc (c' * (xiStar + 1 / 2) ^ 2 / 3) (c' * (xiStar + 1 / 2) ^ 2 / 3),
      |rampedBumpF prob bd P (rampedD P c') c' (Nc c') t|) = 0 := by
    rw [Icc_self]
    exact setIntegral_measure_zero _ (by simp)
  rw [hmid, add_zero] at hsplit
  -- the algebra
  have hFKr := hFK c' hc'0
  have hsq : 0 < √c' := Real.sqrt_pos.mpr hc'0
  have hr : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
  have hdM : rampedD P c' = (2 * (CE + T) + 2 + 2 * Cf / (A0 * CStar)) * c' ^ (-(1 / 3 : ℝ)) := by
    unfold rampedD
    rw [hPM]
  have hIw : (∫ t in Ioi 0, rampedBumpF prob bd P (rampedD P c') c' (Nc c') t) ≤ -(CStar * A0) * √c' := by
    have h1 : FKc (qProb prob) 1 c' * CStar * (-rampedD P c' / 2 + (CE + T) * c' ^ (-(1 / 3 : ℝ))) =
        CStar * (FKc (qProb prob) 1 c' * c' ^ (-(1 / 3 : ℝ))) *
          (-(2 * (CE + T) + 2 + 2 * Cf / (A0 * CStar)) / 2 + (CE + T)) := by
      rw [hdM]; ring
    rw [h1, hFKr] at hwin'
    have h2 : CStar * (A0 * √c') * (-(2 * (CE + T) + 2 + 2 * Cf / (A0 * CStar)) / 2 + (CE + T)) =
        -(CStar * A0) * √c' - Cf * √c' := by
      field_simp
      ring
    rw [h2] at hwin'
    linarith
  obtain ⟨C, hC0, -, -, -, hid, hn⟩ := hK7 P (rampedD P c') hd0 hd1 (Nc c') (hNc c')
  have hre := congrArg Complex.re hid
  rw [← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
  have hhalf := (Complex.abs_re_le_norm _).trans hn
  have hsc : 2 ^ prob.m / (π * (CStar * A0)) + 1 ≤ √c' := by
    calc 2 ^ prob.m / (π * (CStar * A0)) + 1 = √((2 ^ prob.m / (π * (CStar * A0)) + 1) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √c' := Real.sqrt_le_sqrt hc
  have hgoal : (2 : ℝ) ^ prob.m < π * ((CStar * A0) * √c') := by
    have h1 : 2 ^ prob.m / (π * (CStar * A0)) < √c' := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have hgv := abs_le.mp hhalf
  rw [hre]
  have hIw' : (∫ t in Ioi 0, combProfile c' (designComb c' 1 (Nc c') (1 / 4)
        (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
        (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t * prob.cardyV (c' / 12) t) ≤
      -(CStar * A0) * √c' := hIw
  have hpi := mul_le_mul_of_nonneg_left hIw' hπ.le
  linarith only [hpi, hgv.1, hgoal]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBumpVacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumpVacuum

end FormalResearch.ModularBootstrap.Upper.Ramped
