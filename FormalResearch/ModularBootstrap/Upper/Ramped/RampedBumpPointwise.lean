module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpTheta
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpSeparation

/-!
# The pointwise window inequality for the bumped ramped comb, every weight (`fw:Ustar`, vacuum step)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), vacuum step.  For `x ∈ [ξ_*/2, ξ_* + 1/2]` the
integrand `(2/3) c' x h₀^{(p)}(c'x²/3) V(c'x²/3)` of the bumped ramped comb (`h₀^{(p)} = R_bump h₀`, `fw:e3.3`) is bounded by
`FK_c C_* κ σ'(x) (w(σ) + |w(σ)| (c₁ λ|σ| + c₂ c'^{-2/3}))` with `σ = τ(x)/λ`, `w(σ) = Re W_D(-κσ)`
(`rampedBump_pointwise`, every weight `w = p + 1`, uniformly in the cut `N' ≥ n_cap + 6`).

* `signed_amp_le_mul`: the signed amplitude step with the bump multiplier `1 ≤ R ≤ 1 + ε`;
* `bump_far_alg`: for `x > ξ_* + r` (multiplier `R ≤ K_b` only) the pointwise bound is `K_b`-crude, `≤ C |w|`, and is
  absorbed into the error `c₁ λ|σ|` since `λ|σ| = τ(x) ≥ τ(ξ_* + r)` there (so the constant `c₁` depends on `r_p`).

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.Special

/-- The signed amplitude step with a multiplier `1 ≤ R ≤ 1 + ε`: `R t ≤ G (w + (e^δ (1+ε) - 1) |w|)`. -/
lemma signed_amp_le_mul {t amp G w δ ε R : ℝ} (hG : 0 ≤ G)
    (hlo : Real.exp (-δ) * (G * |w|) ≤ amp) (hhi : amp ≤ Real.exp δ * (G * |w|))
    (ht : t ≤ amp) (hneg : w < 0 → t = -amp) (hR1 : 1 ≤ R) (hR2 : R ≤ 1 + ε) (hε : 0 ≤ ε) :
    R * t ≤ G * (w + (Real.exp δ * (1 + ε) - 1) * |w|) := by
  have h1 := signed_amp_le hG hlo hhi ht hneg
  have hamp0 : 0 ≤ amp := le_trans (by positivity) hlo
  have hRt : R * t ≤ t + ε * amp := by
    rcases le_or_gt 0 t with h0 | h0
    · nlinarith only [mul_le_mul_of_nonneg_right hR2 h0, mul_le_mul_of_nonneg_left ht hε]
    · nlinarith only [mul_le_mul_of_nonneg_right hR1 (neg_nonneg.mpr h0.le), mul_nonneg hε hamp0]
  have h2 : ε * amp ≤ ε * (Real.exp δ * (G * |w|)) := mul_le_mul_of_nonneg_left hhi hε
  nlinarith only [hRt, h1, h2]

/-- The far case: `Θ ≥ 0`, `|Θ - 1| ≤ c₁ L + c₂ s`, `L ≥ b₁ > 0` give `Θ (C |w|) ≤ w + (c₁' L + c₂' s) |w|` with
`c₁' = (1 + C) c₁ + (C + 1)/b₁`, `c₂' = (1 + C) c₂`. -/
lemma bump_far_alg {Θ w Cc c1 c2 b1 L s : ℝ} (hCc : 0 ≤ Cc)
    (hΘ : |Θ - 1| ≤ c1 * L + c2 * s) (hb1 : 0 < b1) (hL : b1 ≤ L) (hs : 0 ≤ s) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) :
    Θ * (Cc * |w|) ≤ w + (((1 + Cc) * c1 + (Cc + 1) / b1) * L + (1 + Cc) * c2 * s) * |w| := by
  have hL0 : 0 ≤ L := hb1.le.trans hL
  have hΘle : Θ ≤ 1 + (c1 * L + c2 * s) := by linarith [(abs_le.1 hΘ).2]
  have hq : Cc + 1 ≤ (Cc + 1) / b1 * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb1]
    nlinarith only [hL, hCc]
  have hE0 : 0 ≤ c1 * L + c2 * s := by positivity
  have key : (1 + (c1 * L + c2 * s)) * Cc ≤
      ((1 + Cc) * c1 + (Cc + 1) / b1) * L + (1 + Cc) * c2 * s - 1 := by
    have e : ((1 + Cc) * c1 + (Cc + 1) / b1) * L + (1 + Cc) * c2 * s - 1 =
        Cc * (c1 * L + c2 * s) + (c1 * L + c2 * s) + (Cc + 1) / b1 * L - 1 := by ring
    rw [e]
    nlinarith only [hq, hE0, hCc]
  have h1 : Θ * (Cc * |w|) ≤ (1 + (c1 * L + c2 * s)) * (Cc * |w|) :=
    mul_le_mul_of_nonneg_right hΘle (by positivity)
  have h2 := mul_le_mul_of_nonneg_right key (abs_nonneg w)
  nlinarith only [h1, h2, neg_abs_le w]

/-- **The pointwise window inequality for the bumped ramped comb, every weight** (`fw:Ustar`, vacuum step): for the bump
`bd`, there are `c₁, c₂ > 0` such that for every `P`, `c'` large, `d ∈ [0, d_0]`, every cut `N' ≥ n_cap + 6` and every
`x ∈ [ξ_*/2, ξ_* + 1/2]`:
`(2/3) c' x h₀^{(p)} V ≤ FK_c C_* κ σ'(x) (w(σ) + |w(σ)| (c₁ λ|σ| + c₂ c'^{-2/3}))`, `FK_c = FKc (qProb prob) 1 c'`. -/
theorem rampedBump_pointwise (prob : Crossing.FixedWeightProblem) (bd : BumpData) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ P : RampedParams,
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      ∀ x ∈ langerX (1 / 2),
      (2 * c' * x / 3) *
          (combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
              (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) (c' * x ^ 2 / 3) *
            prob.cardyV (c' / 12) (c' * x ^ 2 / 3)) ≤
        FKc (qProb prob) 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') *
          (rampedWFun P d c' (sigmaOf c' x) + |rampedWFun P d c' (sigmaOf c' x)| *
            (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ)))) := by
  obtain ⟨Ca, hCa, hampP⟩ := rampedComb_amplitude
  obtain ⟨K0, hK0, hKas⟩ := WeightAxioms.cardyV_asymptotic_real prob (half_pos xiStar_pos)
  have hxs := xiStar_pos
  set p : ℕ := prob.w - 1 with hp
  set Mx : ℝ := 2 * (xiStar + 1 / 2) with hMx
  have hMx0 : 0 < Mx := by rw [hMx]; positivity
  set Kb : ℝ := bumpC bd (1 / 4) with hKb
  set C'' : ℝ := bumpC' bd (1 / 4) with hC''
  have hKb0 : 0 < Kb := bumpC_pos bd _
  have hC''0 : 0 ≤ C'' := bumpC'_nonneg bd _
  set Ca' : ℝ := Ca + C'' with hCa'
  have hCa'0 : 0 < Ca' := by rw [hCa']; linarith
  obtain ⟨c1, c2, hc1, hc2, hth⟩ := theta_boundW prob ((K0 + 1) * Mx ^ p) Ca' (by positivity) hCa'0
  set b1 : ℝ := langerTau (xiStar + bd.r) with hb1def
  have hb1 : 0 < b1 := langerTau_pos_of_gt (by linarith [bd.r_pos])
  set Cc : ℝ := 2 * Kb with hCc
  refine ⟨(1 + Cc) * c1 + (Cc + 1) / b1, (1 + Cc) * c2, by positivity, by positivity, fun P => ?_⟩
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  have hδev := eventually_rpow_neg_le (p := 2 / 3) (ε := 1 / (2 * Ca')) (by norm_num) (by positivity)
  filter_upwards [hampP P, hth, ramped_phaseHyp,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num), h_ev, hδev,
    eventually_ge_atTop (max 1 (24 * prob.totalShift)), eventually_ge_atTop (1 : ℝ),
    combProfile_bumped_eq bd, bumpFactor_one_le bd (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le bd (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le_one_add bd (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c' hamp hthc hph hin ⟨_, _, _, hgap⟩ hδ hcS hc1' hval hR1 hRK hRnear d hd0 hdD N' hN' x hx
  have hc'0 : 0 < c' := by linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hlam : 0 < lambdaComb c' := lamPos hc'0
  have hd1 : d ≤ 1 := hdD.trans rampedD0_le_one
  -- the comb is real on the real axis
  have hPh := hph P d hd0 hd1
  have hI : InnerCombHyp c' (rampedComb P d c') :=
    hin (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') hPh.1 hPh.2.1
  have hBim : (rampedComb P d c' (x : ℂ)).im = 0 := hI.real x
  have hBnorm : ‖rampedComb P d c' (x : ℂ)‖ = |(rampedComb P d c' (x : ℂ)).re| := by
    have : rampedComb P d c' (x : ℂ) = (((rampedComb P d c' (x : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [hBim])
    conv_lhs => rw [this]
    rw [Complex.norm_real, Real.norm_eq_abs]
  set b : ℝ := (rampedComb P d c' (x : ℂ)).re with hb
  set w : ℝ := rampedWFun P d c' (sigmaOf c' x) with hwdef
  set δ : ℝ := Ca * c' ^ (-(2 / 3 : ℝ)) with hδdef
  set ε' : ℝ := C'' / c' with hε'def
  have hε'0 : 0 ≤ ε' := by positivity
  set δ' : ℝ := δ + ε' with hδ'def
  have hδ0 : 0 ≤ δ := by positivity
  have hrp : 0 < c' ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
  have hε'le : ε' ≤ C'' * c' ^ (-(2 / 3 : ℝ)) := by
    have : c'⁻¹ ≤ c' ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hc1' (by norm_num)
    calc ε' = C'' * c'⁻¹ := by rw [hε'def]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hC''0
  have hδ'le : δ' ≤ Ca' * c' ^ (-(2 / 3 : ℝ)) := by
    rw [hδ'def, hCa']; nlinarith only [hε'le]
  have hδ'12 : δ' ≤ 1 / 2 := by
    calc δ' ≤ Ca' * c' ^ (-(2 / 3 : ℝ)) := hδ'le
      _ ≤ Ca' * (1 / (2 * Ca')) := mul_le_mul_of_nonneg_left hδ hCa'0.le
      _ = 1 / 2 := by field_simp
  have hδ'0 : 0 ≤ δ' := by rw [hδ'def]; positivity
  have hδ12 : δ ≤ 1 / 2 := by linarith [hε'0]
  -- amplitude
  obtain ⟨hlo, hhi⟩ := hamp d hd0 hdD x hx
  have hWn : ‖designAiryW (rampedNode d c') (rampedEta P c') (-kappaAiry * sigmaOf c' x)‖ = |w| :=
    norm_designAiryW_ramped P hc'0 d _
  have hsl : slitL x = Bessel.besselL x := Upper.Window.Tail.slitL_eq_besselL hx0.le
  rw [hWn, hsl] at hlo hhi
  set G : ℝ := (2 * √2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) * Real.exp (-(3 / 2) * kS x) *
    (CStar * kappaAiry) with hG
  have hG0 : 0 ≤ G := by
    have hCs : 0 < CStar := by unfold CStar; have := kappaAiry_pos; positivity
    have := kappaAiry_pos
    positivity
  set amp : ℝ := ‖rampedComb P d c' (x : ℂ)‖ * Real.exp (c' * Bessel.besselL x) with hamp_def
  have hlo' : Real.exp (-δ) * (G * |w|) ≤ amp := by
    refine le_trans (le_of_eq ?_) hlo
    rw [hG, hδdef]; unfold kS; ring_nf
  have hhi' : amp ≤ Real.exp δ * (G * |w|) := by
    refine hhi.trans (le_of_eq ?_)
    rw [hG, hδdef]; unfold kS; ring_nf
  set t : ℝ := b * Real.exp (c' * Bessel.besselL x) with htdef
  have hexpL : 0 < Real.exp (c' * Bessel.besselL x) := Real.exp_pos _
  have ht : t ≤ amp := by
    rw [htdef, hamp_def, hBnorm]
    exact mul_le_mul_of_nonneg_right (le_abs_self b) hexpL.le
  have hneg : w < 0 → t = -amp := by
    intro hwneg
    have hσ1 := rampedW_neg_imp hc'0 d _ hwneg
    have hsite : designSite c' (rampedSigma d c') 1 = langerTauInv (lambdaComb c' * rampedNode d c' 1) :=
      designSite_rampedSigma hc'0 d 1
    have hn1 : 0 ≤ rampedNode d c' 1 := rampedNode_nonneg hd0 c' le_rfl
    have hτχ : langerTau (designSite c' (rampedSigma d c') 1) = lambdaComb c' * rampedNode d c' 1 := by
      rw [hsite]; exact langerTau_langerTauInv (mul_nonneg hlam.le hn1)
    have hχ0 : 0 < designSite c' (rampedSigma d c') 1 :=
      lt_of_lt_of_le hxs (designSite_ramped_nonneg hc'0 hd0 le_rfl)
    have hτx : langerTau x < lambdaComb c' * rampedNode d c' 1 := by
      have : langerTau x / lambdaComb c' < rampedNode d c' 1 := hσ1
      rw [div_lt_iff₀ hlam] at this; linarith
    have hxlt : x < designSite c' (rampedSigma d c') 1 :=
      (langerTau_strictMonoOn.lt_iff_lt (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 hχ0)).1 (by rw [hτχ]; exact hτx)
    have hre : b ≤ 0 := designComb_re_nonpos_of_lt hc'0 (by norm_num) (by norm_num) hgap
      (nCap P c' + 6) (rampedSigma d c') (rampedEps P c') hx0.le hxlt
    have : b = -‖rampedComb P d c' (x : ℂ)‖ := by rw [hBnorm, abs_of_nonpos hre]; ring
    rw [htdef, hamp_def, this]; ring
  -- the bump multiplier
  have hN1 : 1 ≤ nCap P c' + 6 := by omega
  set Rb : ℝ := bumpFactor bd c' (1 / 4) (nCap P c' + 6) N' x with hRbdef
  have hRb1 : 1 ≤ Rb := hR1 _ _ _
  have hRbK : Rb ≤ Kb := hRK _ _ _ hx0.le
  -- the integrand
  have hprof : combProfile c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
      (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) (c' * x ^ 2 / 3) =
      Rb * combProfile c' (rampedComb P d c') (c' * x ^ 2 / 3) := by
    have h := hval (nCap P c' + 6) N' (rampedSigma d c') (rampedEps P c') hN1 hN' (c' * x ^ 2 / 3)
    rw [xOf_comp hc'0 hx0.le] at h
    exact h
  rw [hprof, combProfile_ofReal_eq hc'0 hx0.le]
  set Vv : ℝ := prob.cardyV (c' / 12) (c' * x ^ 2 / 3) with hVv
  set Bc : ℝ := Vv / Bessel.besselAs (c' * Bessel.besselL x) with hBc
  have hVv0 : 0 ≤ Vv := prob.cardyV_nonneg (by linarith [prob.totalShift_nonneg, (le_max_right _ _).trans hcS]) (by positivity)
  have hzA : 0 < c' * Bessel.besselL x := by unfold Bessel.besselL; positivity
  have hBc0 : 0 ≤ Bc := div_nonneg hVv0 (Bessel.besselAs_pos hzA).le
  have hasy : |Bc - (2 * x) ^ p * prob.nullPoly (Real.exp (-4 * π * x))| ≤ ((K0 + 1) * Mx ^ p) / c' := by
    have h := hKas hcS hx.1
    have hP0 : 0 < (2 * x) ^ p := by positivity
    have hAA : 0 < Bessel.besselAs (c' * (2 * π * x / 3)) := by
      have := Bessel.besselAs_pos hzA; unfold Bessel.besselL at this; exact this
    have e : Bc - (2 * x) ^ p * prob.nullPoly (Real.exp (-4 * π * x)) =
        (2 * x) ^ p * (Vv / ((2 * x) ^ p * Bessel.besselAs (c' * (2 * π * x / 3))) -
          prob.nullPoly (Real.exp (-4 * π * x))) := by
      rw [hBc]; unfold Bessel.besselL; field_simp
    rw [e, abs_mul, abs_of_pos hP0]
    have hpx : (2 * x) ^ p ≤ Mx ^ p := pow_le_pow_left₀ (by linarith) (by rw [hMx]; linarith [hx.2]) p
    calc (2 * x) ^ p * |Vv / ((2 * x) ^ p * Bessel.besselAs (c' * (2 * π * x / 3))) -
          prob.nullPoly (Real.exp (-4 * π * x))|
        ≤ Mx ^ p * (K0 / c') :=
          mul_le_mul hpx h (abs_nonneg _) (by positivity)
      _ ≤ Mx ^ p * ((K0 + 1) / c') := by
          gcongr; linarith
      _ = _ := by ring
  have hdens := Cardy.cardy_density Vv hc'0 hx0
  have hexp : Real.exp (c' * Bessel.besselL x) * Real.exp (-(c' * Bessel.besselL x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hsech : 0 < 1 / cosh (π * x / 2) ^ 2 := by positivity
  have hpi := Real.pi_pos
  have hZ0 : 0 ≤ Bc * (√c' * √x / (√3 * π)) := by positivity
  have hHf : (2 * c' * x / 3) * (1 / cosh (π * x / 2) ^ 2 * b * Vv) =
      1 / cosh (π * x / 2) ^ 2 * t * (Bc * (√c' * √x / (√3 * π))) := by
    rw [← hdens, htdef]
    linear_combination ((2 * c' * x / 3) * (1 / cosh (π * x / 2) ^ 2 * b * Vv)) * (-hexp)
  have hHfR : (2 * c' * x / 3) * (Rb * (1 / cosh (π * x / 2) ^ 2 * b) * Vv) =
      1 / cosh (π * x / 2) ^ 2 * (Rb * t) * (Bc * (√c' * √x / (√3 * π))) := by
    calc (2 * c' * x / 3) * (Rb * (1 / cosh (π * x / 2) ^ 2 * b) * Vv)
        = Rb * ((2 * c' * x / 3) * (1 / cosh (π * x / 2) ^ 2 * b * Vv)) := by ring
      _ = Rb * (1 / cosh (π * x / 2) ^ 2 * t * (Bc * (√c' * √x / (√3 * π)))) := by rw [hHf]
      _ = _ := by ring
  have hid := density_identity_q (Bc := Bc) (qProb_pos prob) hc'0 hx0 hlam rfl
  set Θ : ℝ := mwt x * (Bc / (1 - Real.exp (-(4 * π * x))) ^ 2) / qProb prob with hΘ
  have hΘ0 : 0 ≤ Θ := by
    have hm : 0 ≤ mwt x := by
      unfold mwt
      have := mUnn_pos hx0
      have := mUnn_pos hxs
      have := deriv_langerTau_pos hx0
      positivity
    have hE : 0 < (1 - Real.exp (-(4 * π * x))) ^ 2 := by
      have := one_sub_exp_pos hx0; positivity
    have hq := qProb_pos prob
    rw [hΘ]; positivity
  have hE := hthc x hx Bc δ' hBc0 hasy hδ'0 hδ'le hδ'12
  set K : ℝ := FKc (qProb prob) 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') with hK
  have hK0 : 0 ≤ K := by
    have hF := FKc_pos (qProb_pos prob) 1 hc'0
    have hCs : 0 < CStar := by unfold CStar; have := kappaAiry_pos; positivity
    have := kappaAiry_pos
    have := deriv_langerTau_pos hx0
    rw [hK]; positivity
  have h3 : ∀ u : ℝ, (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (G * u) = K * (Θ * u) := by
    intro u
    have : 1 / cosh (π * x / 2) ^ 2 * (Bc * √c' * √x / (√3 * π)) * G = K * Θ := by
      rw [hG, hK, hΘ]; exact hid
    calc (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (G * u)
        = (1 / cosh (π * x / 2) ^ 2 * (Bc * √c' * √x / (√3 * π)) * G) * u := by ring
      _ = _ := by rw [this]; ring
  have hZs : 0 ≤ 1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π))) := mul_nonneg hsech.le hZ0
  have hLHS : (2 * c' * x / 3) * (Rb * (1 / cosh (π * x / 2) ^ 2 * (rampedComb P d c' (x : ℂ)).re) *
      prob.cardyV (c' / 12) (c' * x ^ 2 / 3)) =
      1 / cosh (π * x / 2) ^ 2 * (Rb * t) * (Bc * (√c' * √x / (√3 * π))) := hHfR
  rw [hLHS]
  have hLq : lambdaComb c' * |sigmaOf c' x| = |langerTau x| := by
    unfold sigmaOf
    rw [abs_div, abs_of_pos hlam]; field_simp
  by_cases hnear : x ≤ xiStar + bd.r
  · -- near the tip: `R ≤ 1 + C''/c'`
    have hRn : Rb ≤ 1 + ε' := hRnear _ _ _ hx0.le hnear
    have hbd := signed_amp_le_mul hG0 hlo' hhi' ht hneg hRb1 hRn hε'0
    have hX : Real.exp δ * (1 + ε') ≤ Real.exp δ' := by
      rw [hδ'def, Real.exp_add]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp ε']) (Real.exp_pos _).le
    have hX1 : Real.exp δ * (1 + ε') - 1 ≤ Real.exp δ' - 1 := by linarith
    have hbd2 : Rb * t ≤ G * (w + (Real.exp δ' - 1) * |w|) := by
      refine hbd.trans (mul_le_mul_of_nonneg_left ?_ hG0)
      have := mul_le_mul_of_nonneg_right hX1 (abs_nonneg w)
      linarith
    have h1 : 1 / cosh (π * x / 2) ^ 2 * (Rb * t) * (Bc * (√c' * √x / (√3 * π))) ≤
        (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (G * (w + (Real.exp δ' - 1) * |w|)) := by
      have := mul_le_mul_of_nonneg_left hbd2 hZs
      calc 1 / cosh (π * x / 2) ^ 2 * (Rb * t) * (Bc * (√c' * √x / (√3 * π)))
          = (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (Rb * t) := by ring
        _ ≤ _ := this
    have h2 := theta_alg (w := w) hΘ0 hδ'0 hE
    rw [h3] at h1
    have hE' : c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ)) ≤
        ((1 + Cc) * c1 + (Cc + 1) / b1) * lambdaComb c' * |sigmaOf c' x| +
          (1 + Cc) * c2 * c' ^ (-(2 / 3 : ℝ)) := by
      have hL0 : 0 ≤ lambdaComb c' * |sigmaOf c' x| := by positivity
      have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
      have h1' : 0 ≤ (Cc * c1 + (Cc + 1) / b1) * (lambdaComb c' * |sigmaOf c' x|) := by positivity
      have h2' : 0 ≤ Cc * c2 * c' ^ (-(2 / 3 : ℝ)) := by positivity
      nlinarith only [h1', h2']
    calc _ ≤ _ := h1
      _ ≤ K * (w + (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ))) * |w|) :=
          mul_le_mul_of_nonneg_left h2 hK0
      _ ≤ K * (w + (((1 + Cc) * c1 + (Cc + 1) / b1) * lambdaComb c' * |sigmaOf c' x| +
            (1 + Cc) * c2 * c' ^ (-(2 / 3 : ℝ))) * |w|) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          have := mul_le_mul_of_nonneg_right hE' (abs_nonneg w)
          linarith
      _ = _ := by rw [hK]; unfold sigmaOf; ring
  · -- beyond `ξ_* + r`: the crude bound `R ≤ K_b`
    push Not at hnear
    have hτb : b1 ≤ langerTau x :=
      langerTau_strictMonoOn.monotoneOn (Set.mem_Ioi.2 (by linarith [bd.r_pos] : 0 < xiStar + bd.r))
        (Set.mem_Ioi.2 hx0) hnear.le
    have hτpos : 0 < langerTau x := lt_of_lt_of_le hb1 hτb
    have hRt : Rb * t ≤ G * (Cc * |w|) := by
      have hamp0 : 0 ≤ amp := le_trans (by positivity) hlo'
      have hRt1 : Rb * t ≤ Kb * amp := by
        rcases le_or_gt 0 t with h0 | h0
        · exact (mul_le_mul hRbK ht h0 hKb0.le)
        · nlinarith only [mul_le_mul_of_nonneg_right hRb1 (neg_nonneg.mpr h0.le), mul_nonneg hKb0.le hamp0, h0]
      have hexp2 : Real.exp δ ≤ 2 := by
        have := exp_le_one_add_two_mul hδ0 hδ12
        linarith
      have h2 : amp ≤ 2 * (G * |w|) := hhi'.trans (mul_le_mul_of_nonneg_right hexp2 (by positivity))
      have := mul_le_mul_of_nonneg_left h2 hKb0.le
      rw [hCc]
      nlinarith only [hRt1, this]
    have h1 : 1 / cosh (π * x / 2) ^ 2 * (Rb * t) * (Bc * (√c' * √x / (√3 * π))) ≤
        (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (G * (Cc * |w|)) := by
      have := mul_le_mul_of_nonneg_left hRt hZs
      calc 1 / cosh (π * x / 2) ^ 2 * (Rb * t) * (Bc * (√c' * √x / (√3 * π)))
          = (1 / cosh (π * x / 2) ^ 2 * (Bc * (√c' * √x / (√3 * π)))) * (Rb * t) := by ring
        _ ≤ _ := this
    rw [h3] at h1
    have hθ1 : |Θ - 1| ≤ c1 * (lambdaComb c' * |sigmaOf c' x|) + c2 * c' ^ (-(2 / 3 : ℝ)) := by
      have hE2 : |Θ - 1| + Θ * (Real.exp δ' - 1) ≤
          c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ)) := hE
      have h0 : 0 ≤ Θ * (Real.exp δ' - 1) := mul_nonneg hΘ0 (by linarith [Real.add_one_le_exp δ'])
      linarith only [hE2, h0]
    have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
    have hfar := bump_far_alg (w := w) hCc0 hθ1 hb1 (by rw [hLq, abs_of_pos hτpos]; exact hτb) hrp.le
      hc1.le hc2.le
    calc _ ≤ _ := h1
      _ ≤ K * (w + (((1 + Cc) * c1 + (Cc + 1) / b1) * (lambdaComb c' * |sigmaOf c' x|) +
            (1 + Cc) * c2 * c' ^ (-(2 / 3 : ℝ))) * |w|) := mul_le_mul_of_nonneg_left hfar hK0
      _ = _ := by rw [hK]; unfold sigmaOf; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBump_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBump_pointwise

end FormalResearch.ModularBootstrap.Upper.Ramped
