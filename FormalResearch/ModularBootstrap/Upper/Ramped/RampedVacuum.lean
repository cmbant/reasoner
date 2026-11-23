module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumBands
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumIntegral

/-!
# The vacuum step of Lemma `U*` for the ramped comb (`rem:thmU` Step (5))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), Step (5).

`rampedVacuum`: for every `C_I, C_mid ≥ 1` there is `M_0 > 0` such that for every `P : RampedParams` with these
`C_I, C_mid` and `P.M0 = M_0`, eventually in `c'`, the test function `g = ½(h₀ - ĥ₀)` of the ramped design `D_*`
at `d = rampedD P c' = M_0 c'^{-1/3}` has `g_vac = virasoroProblem.gVac (c'/12) g > 0`.  The proof follows the
paper: `g_vac = ½h_{0,vac} - π∫h₀V` with `|h_{0,vac}| ≤ 8` (`ramped_k7`); `∫ h₀ V` is split at `x_0 = ξ_*/2` and
`x_1 = ξ_* + 1/2` (`split_integral_le`):

* the deep lobe `x ≤ x_0` is non-positive (`rampedF_lobe_nonpos`);
* the far band is `≤ C_far √c' = O(c'^{-1/3}) FK_c` (`rampedF_far_le`, `FKc_mul_rpow_eq`);
* the Langer window is `≤ FK_c C_* (-d/2 + (C_E + T) c'^{-1/3})` (`rampedWindow_part`, with `∫ Re W_D ≤ -d/2 + C_E c'^{-1/3}`
  from `rampedW_package`);

so `∫h₀V ≤ -A₀ C_* √c'` for `M_0 = 2(C_E + T) + 2 + 2 C_far/(A₀ C_*)` and `g_vac ≥ π A₀ C_* √c' - 4 > 0`.  The order of
constants is `C_I, C_mid, C_E, T, M_0, c_0`: `C_E` depends on `C_I, C_mid` only (`rampedEta_congr`), never on `M_0`.

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
  FormalResearch.ModularBootstrap.Upper.Hankel

/-- `FK_c c'^{-1/3} = A₀ √c'`: the window normalisation is `FK_c ≍ c'^{5/6}`. -/
lemma FKc_one_mul_rpow_eq : ∃ A0 : ℝ, 0 < A0 ∧ ∀ c' : ℝ, 0 < c' →
    FKc 1 1 c' * c' ^ (-(1 / 3 : ℝ)) = A0 * √c' := by
  have hxi := xiStar_pos
  have hπ := Real.pi_pos
  have hk := kTip_pos
  have hE := one_sub_exp_xiStar_pos
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = √xiStar * (1 - exp (-(4 * π * xiStar))) ^ 2 *
      (1 / cosh (π * xiStar / 2) ^ 2) / (√3 * π) := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = 2 * √2 / π := ⟨_, rfl⟩
  have hK1p : 0 < K1 := by rw [hK1]; positivity
  have hK2p : 0 < K2 := by rw [hK2]; positivity
  refine ⟨K1 * K2 ^ (3 / 2 : ℝ) * kTip ^ (1 / 3 : ℝ), by positivity, fun c' hc' => ?_⟩
  have hl := lamPos hc'
  have hm : 0 < kTip * c' := by positivity
  have hlam3 : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
    have h := kTip_mul_lam_rpow hc'
    field_simp
    linarith
  have hlm : lambdaComb c' * (kTip * c') = kTip ^ (1 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
    unfold lambdaComb
    rw [← Real.rpow_add_one hm.ne', Real.mul_rpow hk.le hc'.le]
    norm_num
  have hs : 0 < √c' := Real.sqrt_pos.mpr hc'
  have hr : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc']; norm_num
  have hFK : FKc 1 1 c' = K1 * K2 ^ (3 / 2 : ℝ) * (√c' * (lambdaComb c' * (kTip * c'))) := by
    rw [FKc_one]
    unfold FVc
    have e2 : 2 * √2 / (π * lambdaComb c') = K2 / lambdaComb c' := by
      rw [hK2]; field_simp
    rw [e2, Real.div_rpow hK2p.le hl.le, hlam3, hK1]
    field_simp
  rw [hFK, hlm]
  calc K1 * K2 ^ (3 / 2 : ℝ) * (√c' * (kTip ^ (1 / 3 : ℝ) * c' ^ (1 / 3 : ℝ))) * c' ^ (-(1 / 3 : ℝ))
      = K1 * K2 ^ (3 / 2 : ℝ) * kTip ^ (1 / 3 : ℝ) * √c' * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) := by ring
    _ = _ := by rw [hr]; ring

/-- `FK_c c'^{-1/3} = A₀ √c'` at every scale `q > 0`. -/
lemma FKc_mul_rpow_eq {q : ℝ} (hq : 0 < q) : ∃ A0 : ℝ, 0 < A0 ∧ ∀ c' : ℝ, 0 < c' →
    FKc q 1 c' * c' ^ (-(1 / 3 : ℝ)) = A0 * √c' := by
  obtain ⟨A0, hA0, h⟩ := FKc_one_mul_rpow_eq
  exact ⟨q * A0, by positivity, fun c' hc' => by rw [FKc_scale, mul_assoc, h c' hc']; ring⟩

lemma rampedEta_congr {P Q : RampedParams} (h1 : P.CI = Q.CI) (h2 : P.Cmid = Q.Cmid) (c' : ℝ) :
    rampedEta P c' = rampedEta Q c' := by
  funext k
  unfold rampedEta etaSq etaArg
  rw [h1, h2]

lemma rampedD_nonneg (P : RampedParams) (c' : ℝ) (hc' : 0 < c') : 0 ≤ rampedD P c' := by
  unfold rampedD
  have := P.M0_pos
  positivity

/-- **The vacuum step of Lemma `U*` for the ramped comb, every weight-one problem** (`rem:thmU` Step (5)): for every `C_I, C_mid ≥ 1`
there is `M_0 > 0` such that for every parameter set `P` with these `C_I, C_mid` and `P.M_0 = M_0`, eventually in
`c'`, the test function `g = ½(h₀ - ĥ₀)` of the ramped design `D_*` at `d = M_0 c'^{-1/3}` has positive vacuum
value `g_vac > 0`. -/
theorem rampedVacuum_prob (prob : Crossing.FixedWeightProblem) (hw : prob.w = 1) (CI Cmid : ℝ) (hCI : 1 ≤ CI) (hCmid : 1 ≤ Cmid) :
    ∃ M0 : ℝ, 0 < M0 ∧ ∀ P : RampedParams, P.CI = CI → P.Cmid = Cmid → P.M0 = M0 →
      ∀ᶠ c' : ℝ in atTop, 0 < prob.gVac (c' / 12)
        (pairOdd (combProfile c' (rampedComb P (rampedD P c') c'))
          (hankelTransform 1 (combProfile c' (rampedComb P (rampedD P c') c')))) := by
  obtain ⟨Cf, hCf, hfar⟩ := rampedF_far_le prob hw
  obtain ⟨A0, hA0, hFK⟩ := FKc_mul_rpow_eq (qProb_pos prob)
  obtain ⟨K, hK, hk7⟩ := ramped_k7 hw
  obtain ⟨P0, hP0I, hP0m⟩ : ∃ P0 : RampedParams, P0.CI = CI ∧ P0.Cmid = Cmid :=
    ⟨⟨CI, Cmid, 1, hCI, hCmid, one_pos⟩, rfl, rfl⟩
  obtain ⟨Cw, CE, hCw, hCE, hevW⟩ := rampedW_package P0
  obtain ⟨T, hT, hwin⟩ := rampedWindow_part prob hw Cw hCw
  have hCs := CStar_pos
  refine ⟨2 * (CE + T) + 2 + 2 * Cf / (A0 * CStar), by positivity, fun P hPI hPm hPM => ?_⟩
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
  have hFc : ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ContinuousOn (rampedF prob P d c') (Ici 0) := by
    filter_upwards [rampedF_props prob hw P] with c' h d hd0 hd1 using (h d hd0 hd1).1
  have hwinP := hwin P CE hevW' hFc
  have hr0 : Tendsto (fun c' : ℝ => P.M0 * c' ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).const_mul P.M0
  have hd_ev : ∀ᶠ c' : ℝ in atTop, rampedD P c' ≤ rampedD0 :=
    hr0.eventually_le_const rampedD0_pos
  have hbig : ∀ᶠ c' : ℝ in atTop, (2 ^ prob.m / (π * (CStar * A0)) + 1) ^ 2 ≤ c' := eventually_ge_atTop _
  filter_upwards [hwinP, hfar P, rampedF_props prob hw P, rampedF_lobe_nonpos prob P, hk7, hd_ev, hbig] with c' hwn hf hprops hlobe hK7 hd hc
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc
  have hxs := xiStar_pos
  have hπ := Real.pi_pos
  have hd0 := rampedD_nonneg P c' hc'0
  have hd1 : rampedD P c' ≤ 1 := hd.trans rampedD0_le_one
  obtain ⟨hcont, hint⟩ := hprops (rampedD P c') hd0 hd1
  have hneg := hlobe (rampedD P c') hd0 hd1
  have hwin' := hwn (rampedD P c') hd0 hd
  have hfar' := hf (rampedD P c') hd0 hd1
  have hsplit := split_integral_le (F := rampedF prob P (rampedD P c') c')
    (tS := c' * (xiStar / 2) ^ 2 / 3) (tΦ := c' * (xiStar + 1 / 2) ^ 2 / 3)
    (tN := c' * (xiStar + 1 / 2) ^ 2 / 3) (tR := c' * (xiStar + 1 / 2) ^ 2 / 3)
    (by positivity) (by positivity) (by nlinarith) le_rfl le_rfl hint hneg
  have hmid : (∫ t in Icc (c' * (xiStar + 1 / 2) ^ 2 / 3) (c' * (xiStar + 1 / 2) ^ 2 / 3),
      |rampedF prob P (rampedD P c') c' t|) = 0 := by
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
  have hIw : (∫ t in Ioi 0, rampedF prob P (rampedD P c') c' t) ≤ -(CStar * A0) * √c' := by
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
  obtain ⟨C, hC0, -, -, -, hid, hn⟩ := hK7 P (rampedD P c') hd0 hd1
  have hre := congrArg Complex.re hid
  rw [← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
  have hhalf : |((1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
      combH0 (rampedComb P (rampedD P c') c')
        (bAlpha c' (c' / 12 - prob.shiftSum s))).re| ≤ 2 ^ prob.m :=
    (Complex.abs_re_le_norm _).trans hn
  have hsc : 2 ^ prob.m / (π * (CStar * A0)) + 1 ≤ √c' := by
    calc 2 ^ prob.m / (π * (CStar * A0)) + 1 = √((2 ^ prob.m / (π * (CStar * A0)) + 1) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √c' := Real.sqrt_le_sqrt hc
  have hgoal : (2 : ℝ) ^ prob.m < π * ((CStar * A0) * √c') := by
    have h1 : 2 ^ prob.m / (π * (CStar * A0)) < √c' := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have hgv := abs_le.mp hhalf
  show 0 < prob.gVac (c' / 12) _
  rw [hre]
  have hIw' : (∫ t in Ioi 0, combProfile c' (rampedComb P (rampedD P c') c') t *
      prob.cardyV (c' / 12) t) ≤ -(CStar * A0) * √c' := hIw
  have hpi := mul_le_mul_of_nonneg_left hIw' hπ.le
  linarith only [hpi, hgv.1, hgoal]

/-- **The vacuum step of Lemma `U*` for the ramped comb** (`rem:thmU` Step (5)): for every `C_I, C_mid ≥ 1`
there is `M_0 > 0` such that for every parameter set `P` with these `C_I, C_mid` and `P.M_0 = M_0`, eventually in
`c'`, the test function `g = ½(h₀ - ĥ₀)` of the ramped design `D_*` at `d = M_0 c'^{-1/3}` has positive vacuum
value `g_vac > 0` (Virasoro: `rampedVacuum_prob` at `virasoroProblem`). -/
theorem rampedVacuum (CI Cmid : ℝ) (hCI : 1 ≤ CI) (hCmid : 1 ≤ Cmid) :
    ∃ M0 : ℝ, 0 < M0 ∧ ∀ P : RampedParams, P.CI = CI → P.Cmid = Cmid → P.M0 = M0 →
      ∀ᶠ c' : ℝ in atTop, 0 < Crossing.virasoroProblem.gVac (c' / 12)
        (pairOdd (combProfile c' (rampedComb P (rampedD P c') c'))
          (hankelTransform 1 (combProfile c' (rampedComb P (rampedD P c') c')))) :=
  rampedVacuum_prob Crossing.virasoroProblem rfl CI Cmid hCI hCmid

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.FKc_mul_rpow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FKc_mul_rpow_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedVacuum_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedVacuum_prob

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedVacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedVacuum

end FormalResearch.ModularBootstrap.Upper.Ramped
