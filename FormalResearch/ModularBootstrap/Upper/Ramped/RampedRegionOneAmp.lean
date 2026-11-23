module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOneGeom
public import FormalResearch.ModularBootstrap.Upper.Ramped.NearTipRatio

/-!
# From a lower bound on `W_D` to positivity of `2g` in Region I (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2): on Region I
`h_0 e^{c'L} ≍ c' |W_D(u)|` (`rampedComb_amplitude`), while the global bound `SD_G` of `ramped_phase_package` gives
`e^{c'L} |ĥ_0| ≤ K_G √(c'/x)`.

* `langerK_xiStar_le`: `K_*(x) = K(x, ξ_*)` is bounded above on `(ξ_*, ∞)` (by `log(π/(2 c_τ))`);
* `amp_factor`: the comb amplitude of `rampedComb_amplitude` is at least `D c' ‖W‖`, `D` absolute;
* `regionI_twoG_of_W`: there is an absolute `Q` such that `‖W_D(u)‖ ≥ Q c'^{-1/2}` implies `2g(c' x²/3) > 0` for
  `χ'_1 < x ≤ ξ_I`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel
  FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- `K_*(x) = K(x, ξ_*) ≤ log(π/(2 c_τ))` for `x > ξ_*`. -/
lemma langerK_xiStar_le : ∃ Kb : ℝ, ∀ x : ℝ, xiStar < x → langerK x xiStar ≤ Kb := by
  have hxs := xiStar_pos
  obtain ⟨cτ, hcτ, hcd⟩ := langerTau_deriv_ge_const_of (a := xiStar / 2) (by linarith)
  refine ⟨Real.log (π / (2 * cτ)), fun x hx => ?_⟩
  have hx0 : 0 < x := hxs.trans hx
  rw [langerK_xiStar hx0 hx.ne']
  have hτ : cτ * (x - xiStar) ≤ langerTau x := by
    have := langerTau_sub_ge (a := xiStar / 2) (c := cτ) (by linarith) hcd (by linarith) hx.le
    rwa [langerTau_xiStar, sub_zero] at this
  have hd : 0 < x - xiStar := sub_pos.2 hx
  have hτpos : 0 < langerTau x := lt_of_lt_of_le (by positivity) hτ
  rw [abs_of_pos hd, abs_of_pos hτpos]
  have hπ := Real.pi_pos
  have t1 : Real.tanh (π * (x - xiStar) / 2) ≤ π * (x - xiStar) / 2 :=
    tanh_le_self_R (by positivity)
  have t1p : 0 < Real.tanh (π * (x - xiStar) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 (by positivity)) (Real.cosh_pos _)
  have t2 : Real.tanh (π * (x + xiStar) / 2) < 1 := tanh_lt_one_R _
  have t2p : 0 < Real.tanh (π * (x + xiStar) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 (by positivity)) (Real.cosh_pos _)
  have hnum : Real.tanh (π * (x - xiStar) / 2) * Real.tanh (π * (x + xiStar) / 2) ≤ π * (x - xiStar) / 2 := by
    calc _ ≤ Real.tanh (π * (x - xiStar) / 2) * 1 := mul_le_mul_of_nonneg_left t2.le t1p.le
      _ ≤ _ := by linarith
  apply Real.log_le_log (div_pos (mul_pos t1p t2p) hτpos)
  rw [div_le_iff₀ hτpos]
  have : π / (2 * cτ) * (cτ * (x - xiStar)) = π * (x - xiStar) / 2 := by field_simp
  have h3 : π / (2 * cτ) * (cτ * (x - xiStar)) ≤ π / (2 * cτ) * langerTau x :=
    mul_le_mul_of_nonneg_left hτ (by positivity)
  linarith

lemma lambdaComb_rpow_three_halves {c' : ℝ} (hc' : 0 < c') :
    (lambdaComb c') ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
  have hk := kTip_pos
  unfold lambdaComb
  rw [← Real.rpow_mul (by positivity)]
  norm_num [Real.rpow_neg_one]

lemma CStar_pos' : 0 < CStar := by
  unfold CStar
  have := kappaAiry_pos
  have := Real.pi_pos
  positivity

/-- The comb amplitude of `rampedComb_amplitude` is at least `D c' ‖W‖` for `x > ξ_*`, `D` absolute. -/
lemma amp_factor {Camp : ℝ} (hCamp : 0 ≤ Camp) : ∃ D : ℝ, 0 < D ∧ ∀ c' : ℝ, 1 ≤ c' → ∀ x : ℝ, xiStar < x →
    ∀ w : ℝ, 0 ≤ w →
      D * c' * w ≤ Real.exp (-(Camp * c' ^ (-(2 / 3 : ℝ)))) *
        ((2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) *
          Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) *
          (CStar * kappaAiry * w)) := by
  obtain ⟨Kb, hKb⟩ := langerK_xiStar_le
  have hk := kTip_pos
  have hκ := kappaAiry_pos
  have hCS := CStar_pos'
  have hπ := Real.pi_pos
  have h2 : (0 : ℝ) < 2 * Real.sqrt 2 / π := by positivity
  set Bc : ℝ := (2 * Real.sqrt 2 / π) ^ (3 / 2 : ℝ) with hBc
  have hBc0 : 0 < Bc := Real.rpow_pos_of_pos h2 _
  set E1 : ℝ := Real.exp (-Camp) with hE1
  set E3 : ℝ := Real.exp (-(3 / 2) * (Kb + Real.log (2 * Real.sqrt 2 / π))) with hE3
  refine ⟨E1 * (Bc * kTip * E3 * (CStar * kappaAiry)), by positivity, ?_⟩
  intro c' hc'1 x hx w hw
  have hc'0 : 0 < c' := by linarith
  have hl := lambdaComb_pos' hc'0
  have hA1 : E1 ≤ Real.exp (-(Camp * c' ^ (-(2 / 3 : ℝ)))) := by
    apply Real.exp_le_exp.2
    have : c' ^ (-(2 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc'1 (by norm_num)
    nlinarith
  have hA3 : E3 ≤ Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) := by
    apply Real.exp_le_exp.2
    have := hKb x hx
    nlinarith
  have hB : (2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) = Bc * kTip * c' := by
    rw [show 2 * Real.sqrt 2 / (π * lambdaComb c') = (2 * Real.sqrt 2 / π) * (lambdaComb c')⁻¹ by
      field_simp]
    rw [Real.mul_rpow h2.le (inv_nonneg.2 hl.le), Real.inv_rpow hl.le, lambdaComb_rpow_three_halves hc'0,
      inv_inv]
    ring
  rw [hB]
  have hE30 : 0 < E3 := Real.exp_pos _
  have hE10 : 0 < E1 := Real.exp_pos _
  have hA30 : 0 < Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) := Real.exp_pos _
  calc E1 * (Bc * kTip * E3 * (CStar * kappaAiry)) * c' * w
      = E1 * (Bc * kTip * c' * E3 * (CStar * kappaAiry * w)) := by ring
    _ ≤ _ := by gcongr

/-- `e^{-πx} ≤ sech²(πx/2)` for `x ≥ 0`. -/
lemma sech_sq_lower {x : ℝ} (hx : 0 ≤ x) : Real.exp (-(π * x)) ≤ 1 / Real.cosh (π * x / 2) ^ 2 := by
  have hπ := Real.pi_pos
  have hy : 0 ≤ π * x / 2 := by positivity
  have hc : Real.cosh (π * x / 2) ≤ Real.exp (π * x / 2) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(π * x / 2)) ≤ Real.exp (π * x / 2) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hc0 := Real.cosh_pos (π * x / 2)
  have h2 : Real.cosh (π * x / 2) ^ 2 ≤ Real.exp (π * x) := by
    calc Real.cosh (π * x / 2) ^ 2 ≤ Real.exp (π * x / 2) ^ 2 := pow_le_pow_left₀ hc0.le hc 2
      _ = Real.exp (π * x) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.exp_neg, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_one (Real.exp_pos _)]
  exact h2

/-- **Region I from `W_D`** (`rem:thmU` Step (2)): there is an absolute `Q > 0` such that for `c'` large,
`d ∈ [0, d_0]` and `χ'_1 < x ≤ ξ_I`, `‖W_D(-κ σ(x))‖ ≥ Q c'^{-1/2}` implies `2g(c' x²/3) > 0`. -/
theorem regionI_twoG_of_W : ∃ Q : ℝ, 0 < Q ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d →
    d ≤ rampedD0 → ∀ x : ℝ, designSite c' (rampedSigma d c') 1 < x → x ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) →
      Q * c' ^ (-(1 / 2 : ℝ)) ≤ ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖ →
      0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x := by
  obtain ⟨K, A, C, KG, hK, hA, hC, hKG, hphase⟩ := ramped_phase_package
  obtain ⟨Camp, hCamp, hamp⟩ := rampedComb_amplitude
  obtain ⟨D, hD, hDamp⟩ := amp_factor hCamp.le
  obtain ⟨_, _, hgapev⟩ := siteGap_eventually_le
  have hxs := xiStar_pos
  set s0 : ℝ := Real.exp (-(π * (xiStar + 1))) with hs0
  have hs00 : 0 < s0 := Real.exp_pos _
  set r0 : ℝ := Real.sqrt (1 / xiStar) with hr0
  have hr00 : 0 < r0 := Real.sqrt_pos.2 (by positivity)
  refine ⟨(KG + 1) * r0 / (s0 * D), by positivity, fun P => ?_⟩
  have hsmall : ∀ᶠ c' : ℝ in atTop, c' ^ (-(3 / 5 : ℝ)) ≤ 1 / 2 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5))
    exact ht.eventually_le_const (by norm_num)
  filter_upwards [hphase, hamp P, hgapev, eventually_ge_atTop (1 : ℝ), hsmall]
    with c' hph hap hgp hc'1 hsm
  intro d hd hdD x hχx hxI hW
  have hc'0 : 0 < c' := by linarith
  have hl := lambdaComb_pos' hc'0
  have hσ1 : 0 ≤ rampedNode d c' 1 := rampedNode_nonneg hd c' le_rfl
  have hχsite : designSite c' (rampedSigma d c') 1 = langerTauInv (lambdaComb c' * rampedNode d c' 1) :=
    designSite_rampedSigma hc'0 d 1
  have hχge : xiStar ≤ designSite c' (rampedSigma d c') 1 := by
    rw [hχsite]; exact (langerTauInv_spec (mul_nonneg hl.le hσ1)).1
  have hxξ : xiStar < x := lt_of_le_of_lt hχge hχx
  have hx0 : 0 < x := hxs.trans hxξ
  have hxle : x ≤ xiStar + 1 / 2 := by linarith
  have hxX : x ∈ langerX (1 / 2) := ⟨by linarith, hxle⟩
  obtain ⟨_, hphase2, _, hphase4⟩ := hph P d hd (hdD.trans (by unfold rampedD0; exact min_le_left _ _))
  have hglob := hphase4 x hx0
  have hlow := (hap d hd hdD x hxX).1
  have hE : Real.exp (c' * slitL x) = Real.exp (c' * edgeL x) := by
    unfold slitL edgeL; rw [abs_of_nonneg hx0.le]
  rw [hE] at hlow
  have hDD := hDamp c' hc'1 x hxξ ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖
    (norm_nonneg _)
  -- `c' ^ (-1/2) * c' = √c'`
  have hsq : c' ^ (-(1 / 2 : ℝ)) * c' = Real.sqrt c' := by
    rw [Real.sqrt_eq_rpow]
    calc c' ^ (-(1 / 2 : ℝ)) * c' = c' ^ (-(1 / 2 : ℝ)) * c' ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = c' ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hc'0]; norm_num
  set Wn := ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖ with hWn
  set Ecomb := ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * edgeL x) with hEc
  have hcomb : (KG + 1) * r0 / s0 * Real.sqrt c' ≤ Ecomb := by
    have h1 : D * c' * ((KG + 1) * r0 / (s0 * D) * c' ^ (-(1 / 2 : ℝ))) ≤ D * c' * Wn :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    have h2 : D * c' * ((KG + 1) * r0 / (s0 * D) * c' ^ (-(1 / 2 : ℝ))) =
        (KG + 1) * r0 / s0 * Real.sqrt c' := by
      rw [← hsq]; field_simp
    linarith [hDD, hlow, h1, h2]
  have hEpos : 0 < Real.exp (c' * edgeL x) := Real.exp_pos _
  have hs0le : s0 ≤ 1 / Real.cosh (π * x / 2) ^ 2 := by
    refine le_trans ?_ (sech_sq_lower hx0.le)
    apply Real.exp_le_exp.2
    have := Real.pi_pos
    nlinarith
  have hsqrt : Real.sqrt (c' / x) ≤ Real.sqrt c' * r0 := by
    rw [hr0, ← Real.sqrt_mul hc'0.le]
    apply Real.sqrt_le_sqrt
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hxs hxξ.le) hc'0.le
  have hnorm0 : 0 ≤ ‖rampedComb P d c' (x : ℂ)‖ := norm_nonneg _
  have hcm : ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
      (c' * x ^ 2 / 3)‖ < 1 / Real.cosh (π * x / 2) ^ 2 *
        ‖designComb c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') (x : ℂ)‖ := by
    have hrc : designComb c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') =
        rampedComb P d c' := rfl
    rw [hrc]
    set Hn := ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
      (c' * x ^ 2 / 3)‖ with hHn
    set Sx := 1 / Real.cosh (π * x / 2) ^ 2 with hSx
    rw [← mul_lt_mul_iff_of_pos_left (a := Real.exp (c' * edgeL x)) hEpos]
    have hpos : 0 < Real.sqrt c' * r0 := by
      have := Real.sqrt_pos.2 hc'0
      positivity
    have e1 : Real.exp (c' * edgeL x) * Hn ≤ KG * (Real.sqrt c' * r0) :=
      hglob.trans (mul_le_mul_of_nonneg_left hsqrt hKG)
    have e2 : (KG + 1) * r0 * Real.sqrt c' ≤ s0 * Ecomb := by
      have := mul_le_mul_of_nonneg_left hcomb hs00.le
      calc (KG + 1) * r0 * Real.sqrt c' = s0 * ((KG + 1) * r0 / s0 * Real.sqrt c') := by field_simp
        _ ≤ _ := this
    have e3 : s0 * Ecomb ≤ Real.exp (c' * edgeL x) * (Sx * ‖rampedComb P d c' (x : ℂ)‖) := by
      have : Sx * Ecomb ≥ s0 * Ecomb := mul_le_mul_of_nonneg_right hs0le (by positivity)
      calc s0 * Ecomb ≤ Sx * Ecomb := this
        _ = _ := by rw [hEc]; ring
    nlinarith [e1, e2, e3, hpos]
  have hgap1 := hgp.2.2.2
  exact twoG_pos_of_lt hc'0 hgap1 (by omega) (rampedSigma d c') (rampedEps P c') hχx
    (by linarith) hcm

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerK_xiStar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerK_xiStar_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.amp_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_factor

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.regionI_twoG_of_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionI_twoG_of_W

end FormalResearch.ModularBootstrap.Upper.Ramped
