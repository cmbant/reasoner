module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOne
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpSeparation
public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIII

/-!
# Region I of Lemma `U*(w)`: the bumped ramped comb at every weight (`fw:Ustar` Step 3)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), Step 3: the ramp's Region I lower bound
`h₀^{ramp} e^{c'L} ≥ c_I C_I² √c'` is the weight-free `regionI_W_lower` (Lean) with the amplitude factor of
`rampedComb_amplitude`; the bump only raises `h₀` on the real axis (`R_bump ≥ 1`), and the order-`p` global bound
`fw:e1.3` (`twoGW_pos_of_lower`, through `bumped_regionI_pos`) closes it.

* `rampedRegionI_lower`: for every `A ≥ 0` there is `C_I ≥ 1` (absolute given `A`) such that for every `P` with `P.C_I = C_I`
  (any `C_mid`, `M_0`) and `c'` large, `A √c' < sech²(πx/2) ‖B_{D_*}(x)‖ e^{c' L(x)}` on Region I (`t_* + 1 ≤ t`, `x ≤ ξ_I`);
* `rampedBumped_regionI`: `2 g_w > 0` on Region I for the bumped ramped comb, with `C_I` chosen from the constant `A` of
  `bumped_regionI_pos`.  This is the paper's `C_I = C_I(w)`, depending on the order-`p` global-bound constant `K_p`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel
  Upper.Bump FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- **Region I, lower bound of the unbumped profile**: for every `A ≥ 0` there is `C_I ≥ 1` such that for every `P` with
`P.C_I = C_I`, `c'` large, `d ∈ [0, d_0]` and every `x ≥ 0` with `t_*(d) + 1 ≤ t`, `x ≤ ξ_I`:
`ξ_*/2 ≤ x` and `A √c' < h₀(x) e^{c' L(x)}` for the ramped design `D_*`. -/
theorem rampedRegionI_lower {A : ℝ} (hA : 0 ≤ A) : ∃ CI : ℝ, 1 ≤ CI ∧ ∀ P : RampedParams, P.CI = CI →
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ x : ℝ, 0 ≤ x →
      c' * designSite c' (rampedSigma d c') 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      x ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) →
      xiStar / 2 ≤ x ∧ A * √c' <
        (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') (x : ℂ)).re *
          Real.exp (c' * edgeL x) := by
  obtain ⟨Camp, hCamp, hamp⟩ := rampedComb_amplitude
  obtain ⟨D, hD, hDamp⟩ := amp_factor hCamp.le
  obtain ⟨_, _, hgapev⟩ := siteGap_eventually_le
  obtain ⟨c₁, hc₁, hgap⟩ := regionI_gap
  have hxs := xiStar_pos
  set s0 : ℝ := Real.exp (-(π * (xiStar + 1))) with hs0
  have hs00 : 0 < s0 := Real.exp_pos _
  obtain ⟨CI, hCI, hW⟩ := regionI_W_lower (Q := (A + 1) / (s0 * D)) (by positivity)
  refine ⟨CI, hCI, fun P hP => ?_⟩
  have hsmall : ∀ᶠ c' : ℝ in atTop, c' ^ (-(3 / 5 : ℝ)) ≤ 1 / 2 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5))
    exact ht.eventually_le_const (by norm_num)
  filter_upwards [hamp P, hW P hP, hgapev, eventually_ge_atTop (1 : ℝ), hsmall]
    with c' hap hw hgp hc'1 hsm
  intro d hd hdD x hx0 ht hxI
  have hc'0 : 0 < c' := by linarith
  obtain ⟨hχ0, hχx, -⟩ := hgap c' hc'1 d hd (hdD.trans rampedD0_le_one) x hx0 ht hxI
  have hxξ : xiStar < x := lt_of_le_of_lt hχ0 hχx
  have hx0' : 0 < x := hxs.trans hxξ
  have hxle : x ≤ xiStar + 1 / 2 := by linarith
  have hxX : x ∈ langerX (1 / 2) := ⟨by linarith, hxle⟩
  refine ⟨by linarith, ?_⟩
  have hlow := (hap d hd hdD x hxX).1
  have hE : Real.exp (c' * slitL x) = Real.exp (c' * edgeL x) := by
    unfold slitL edgeL; rw [abs_of_nonneg hx0'.le]
  rw [hE] at hlow
  have hWl := hw d hd hdD x hx0 ht hxI
  have hDD := hDamp c' hc'1 x hxξ ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖
    (norm_nonneg _)
  have hsq : c' ^ (-(1 / 2 : ℝ)) * c' = Real.sqrt c' := by
    rw [Real.sqrt_eq_rpow]
    calc c' ^ (-(1 / 2 : ℝ)) * c' = c' ^ (-(1 / 2 : ℝ)) * c' ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = c' ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hc'0]; norm_num
  set Wn := ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖ with hWn
  set Ecomb := ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * edgeL x) with hEc
  have hcomb : (A + 1) / s0 * Real.sqrt c' ≤ Ecomb := by
    have h1 : D * c' * ((A + 1) / (s0 * D) * c' ^ (-(1 / 2 : ℝ))) ≤ D * c' * Wn :=
      mul_le_mul_of_nonneg_left hWl (by positivity)
    have h2 : D * c' * ((A + 1) / (s0 * D) * c' ^ (-(1 / 2 : ℝ))) = (A + 1) / s0 * Real.sqrt c' := by
      rw [← hsq]; field_simp
    linarith only [hDD, hlow, h1, h2]
  have hs0le : s0 ≤ 1 / Real.cosh (π * x / 2) ^ 2 := by
    refine le_trans ?_ (sech_sq_lower hx0'.le)
    apply Real.exp_le_exp.2
    have := Real.pi_pos
    nlinarith only [this, hxle, hxs]
  -- the profile is `sech² · ‖B‖`
  have hf0 : 0 ≤ designSite c' (rampedSigma d c') 1 := xiStar_pos.le.trans (designSite_ramped_nonneg hc'0 hd le_rfl)
  obtain ⟨r, hr, hr0⟩ := designComb_real_nonneg hc'0 hgp.2.2.2 1 (nCap P c' + 6) (rampedSigma d c') (rampedEps P c')
    (by omega) hχx hf0
  have hnorm : ‖rampedComb P d c' (x : ℂ)‖ = r := by
    have : rampedComb P d c' (x : ℂ) = (r : ℂ) := hr
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hre : (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') (x : ℂ)).re =
      1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hr, Complex.ofReal_re]
  rw [hre]
  have hEcr : Ecomb = r * Real.exp (c' * edgeL x) := by rw [hEc, hnorm]
  have hEpos : 0 ≤ Ecomb := by rw [hEcr]; exact mul_nonneg hr0 (Real.exp_pos _).le
  have hsc : 0 < Real.sqrt c' := Real.sqrt_pos.2 hc'0
  have h3 : s0 * Ecomb ≤ 1 / Real.cosh (π * x / 2) ^ 2 * r * Real.exp (c' * edgeL x) := by
    have : s0 * Ecomb ≤ (1 / Real.cosh (π * x / 2) ^ 2) * Ecomb := mul_le_mul_of_nonneg_right hs0le hEpos
    calc s0 * Ecomb ≤ (1 / Real.cosh (π * x / 2) ^ 2) * Ecomb := this
      _ = _ := by rw [hEcr]; ring
  have h4 : (A + 1) * Real.sqrt c' ≤ s0 * Ecomb := by
    have := mul_le_mul_of_nonneg_left hcomb hs00.le
    calc (A + 1) * Real.sqrt c' = s0 * ((A + 1) / s0 * Real.sqrt c') := by field_simp
      _ ≤ _ := this
  nlinarith only [h3, h4, hsc]

/-- **Region I for the bumped ramped comb** (`fw:Ustar` Step 3): for every `p` and bump parameters `Pp`, there is `C_I ≥ 1` such
that for every `P` with `P.C_I = C_I` (any `C_mid`, `M_0`), `c'` large, `d ∈ [0, d_0]` and every `x ≥ 0` with
`t_*(d) + 1 ≤ t`, `x ≤ ξ_I`, the order-`p` test of the bumped ramped comb is positive. -/
theorem rampedBumped_regionI (p : ℕ) (Pp : RpParams p) :
    ∃ CI : ℝ, 1 ≤ CI ∧ ∀ P : RampedParams, P.CI = CI → ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 →
      ∀ x : ℝ, 0 ≤ x → c' * designSite c' (rampedSigma d c') 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
        x ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) →
        0 < twoGW p c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
          (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
          (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) x := by
  obtain ⟨A, hA0, hA⟩ := bumped_regionI_pos p Pp 1 le_rfl
  obtain ⟨CI, hCI, hlow⟩ := rampedRegionI_lower hA0
  refine ⟨CI, hCI, fun P hP => ?_⟩
  filter_upwards [hA, hlow P hP, ramped_phaseHyp] with c' hAc hl hph d hd hdD x hx0 ht hxI
  obtain ⟨hxh, hQ⟩ := hl d hd hdD x hx0 ht hxI
  obtain ⟨hfN, hadm, -⟩ := hph P d hd (hdD.trans rampedD0_le_one)
  exact hAc (nCap P c' + 6) (rampedBumpCut Pp.bumpData P c') (rampedSigma d c') (rampedEps P c') hfN
    (le_rampedBumpCut Pp.bumpData P c') hadm x hxh hQ

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedRegionI_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedRegionI_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBumped_regionI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumped_regionI

end FormalResearch.ModularBootstrap.Upper.Ramped
