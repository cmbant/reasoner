module

public import FormalResearch.ModularBootstrap.Mixtures.SmoothBands
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpWindowPart
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuum

/-!
# `pmix:smooth`: the universal smooth-multiplier vacuum transfer (Lemma PM.6)

`positive_mixtures.tex`, Lemma PM.6 (`pmix:smooth`).  Let `W : SmoothWeight w hw` carry the hypotheses (i)-(ii) of the
lemma (a smooth positive amplitude on the Langer window, the far-band bound with `K_2 = w - 1`, see `SmoothWeight`) and
let `h_0^{(p)}(·; d)` be the bumped ramped comb of weight `w` at `d = M_0 c'^{-1/3}` (`rampedBumpFS`, `rampedD`).

* `pmix_smooth_vacbound`: the paper's `(pmix:vacbound)`.  For fixed `C_I, C_mid ≥ 1` and the bump `bd` there are constants
  `K, K' ≥ 0` independent of `M_0` and `d ∈ [0, d_0]` with, for every `P` with these `C_I, C_mid`, every cut
  `N' ≥ n_cap + 6`, `c'` large and `d ∈ [0, d_0]`:
  `∫_0^∞ h_0^{(p)}(t; d) V(t) dt ≤ FK_c C_* (-d/2 + K c'^{-1/3}) + K' √c'`, `FK_c = FKc W.q 1 c'`
  (the paper writes `C_* q(ξ_*) FK_n [-3/8 d + K n^{-1/3}] + K' √n` with `FK_c` carrying `q` here, and the window
  coefficient `1/2` of `∫ W_D ≤ -d/2 + E_0` in the Lean form `pUnif_integral_le` of `pmix:punif`).
* `pmix_smooth`: the last assertion of the lemma: there is `M_0 > 0` such that for every `P` with these `C_I, C_mid`
  and `P.M_0 = M_0` (that is `d = M_0 c'^{-1/3}`) and every cut, `∫_0^∞ h_0^{(p)} V dt ≤ -√c'` for all large `c'`.

Proof: the three-way split of the paper, via `rampedWindow_part_gen` (window, with `rampedBump_pointwise_S`), the deep lobe
(`rampedBump_lobe_nonpos_S`, dropped) and the outer band (`rampedBump_far_S`).  All results are proved unconditionally;
`SmoothWeight` is the stated hypothesis.
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
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Window.Tail
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.Special

/-- **`(pmix:vacbound)`** of `pmix:smooth`: see the module docstring. -/
theorem pmix_smooth_vacbound {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (bd : BumpData) (CI Cmid : ℝ)
    (hCI : 1 ≤ CI) (hCmid : 1 ≤ Cmid) :
    ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧ ∀ P : RampedParams, P.CI = CI → P.Cmid = Cmid →
      ∀ Nc : ℝ → ℕ, (∀ c' : ℝ, nCap P c' + 6 ≤ Nc c') →
      ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 →
        (∫ t in Ioi 0, rampedBumpFS W bd P d c' (Nc c') t) ≤
          FKc W.q 1 c' * CStar * (-d / 2 + K * c' ^ (-(1 / 3 : ℝ))) + K' * √c' := by
  obtain ⟨Cf, hCf, hfar⟩ := rampedBump_far_S W bd
  obtain ⟨P0, hP0I, hP0m⟩ : ∃ P0 : RampedParams, P0.CI = CI ∧ P0.Cmid = Cmid :=
    ⟨⟨CI, Cmid, 1, hCI, hCmid, one_pos⟩, rfl, rfl⟩
  obtain ⟨Cw, CE, hCw, hCE, hevW⟩ := rampedW_package P0
  obtain ⟨c1, c2, hc1, hc2, hpt⟩ := rampedBump_pointwise_S W bd
  obtain ⟨T, hT, hwin⟩ := rampedWindow_part_gen c1 c2 hc1 hc2 Cw hCw
  refine ⟨CE + T, Cf, by positivity, hCf.le, fun P hPI hPm Nc hNc => ?_⟩
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
      ContinuousOn (rampedBumpFS W bd P d c' (Nc c')) (Ici 0) := by
    filter_upwards [rampedBump_props_S W bd P] with c' h d hd0 hd1 using (h d hd0 hd1 (Nc c') (hNc c')).1
  have hpt' : ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 → ∀ x ∈ langerX (1 / 2),
      (2 * c' * x / 3) * rampedBumpFS W bd P d c' (Nc c') (c' * x ^ 2 / 3) ≤
        FKc W.q 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') *
          (rampedWFun P d c' (sigmaOf c' x) + |rampedWFun P d c' (sigmaOf c' x)| *
            (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ)))) := by
    filter_upwards [hpt P] with c' h d hd0 hdD x hx
    exact h d hd0 hdD (Nc c') (hNc c') x hx
  have hwinP := hwin P CE (fun c' => FKc W.q 1 c')
    (fun d c' => rampedBumpFS W bd P d c' (Nc c')) (fun c' hc' => FKc_pos W.q_pos 1 hc')
    hevW' hFc hpt'
  filter_upwards [hwinP, hfar P, rampedBump_props_S W bd P, rampedBump_lobe_nonpos_S W bd P,
    eventually_gt_atTop (0 : ℝ)] with c' hwn hf hprops hlobe hc'0 d hd0 hdD
  have hxs := xiStar_pos
  have hd1 : d ≤ 1 := hdD.trans rampedD0_le_one
  obtain ⟨-, hint⟩ := hprops d hd0 hd1 (Nc c') (hNc c')
  have hneg := hlobe d hd0 hd1 (Nc c') (hNc c')
  have hwin' := hwn d hd0 hdD
  have hfar' := hf d hd0 hd1 (Nc c') (hNc c')
  have hsplit := split_integral_le (F := rampedBumpFS W bd P d c' (Nc c'))
    (tS := c' * (xiStar / 2) ^ 2 / 3) (tΦ := c' * (xiStar + 1 / 2) ^ 2 / 3)
    (tN := c' * (xiStar + 1 / 2) ^ 2 / 3) (tR := c' * (xiStar + 1 / 2) ^ 2 / 3)
    (by positivity) (by positivity) (by nlinarith) le_rfl le_rfl hint hneg
  have hmid : (∫ t in Icc (c' * (xiStar + 1 / 2) ^ 2 / 3) (c' * (xiStar + 1 / 2) ^ 2 / 3),
      |rampedBumpFS W bd P d c' (Nc c') t|) = 0 := by
    rw [Icc_self]
    exact setIntegral_measure_zero _ (by simp)
  rw [hmid, add_zero] at hsplit
  have hfar'' : (∫ t in Ici (c' * (xiStar + 1 / 2) ^ 2 / 3), |rampedBumpFS W bd P d c' (Nc c') t|) ≤
      Cf * √c' := hfar'
  linarith only [hsplit, hwin', hfar'']

/-- **`pmix:smooth`** (Lemma PM.6): there is `M_0 > 0` (independent of `n`, chosen after `C_I, C_mid`) such that for
every `P` with `P.C_I = C_I`, `P.C_mid = C_mid`, `P.M_0 = M_0` and every cut `N' ≥ n_cap + 6`, for all sufficiently large
`c'` the bumped ramped comb at `d = M_0 c'^{-1/3}` satisfies `∫_0^∞ h_0^{(p)}(t; d) V(t) dt ≤ -√c'`, for the weight family
`V` of a `SmoothWeight` (hypotheses (i)-(ii) of the lemma). -/
theorem pmix_smooth {w : ℕ} {hw : 1 ≤ w} (W : SmoothWeight w hw) (bd : BumpData) (CI Cmid : ℝ)
    (hCI : 1 ≤ CI) (hCmid : 1 ≤ Cmid) :
    ∃ M0 : ℝ, 0 < M0 ∧ ∀ P : RampedParams, P.CI = CI → P.Cmid = Cmid → P.M0 = M0 →
      ∀ Nc : ℝ → ℕ, (∀ c' : ℝ, nCap P c' + 6 ≤ Nc c') →
      ∀ᶠ c' : ℝ in atTop,
        (∫ t in Ioi 0, rampedBumpFS W bd P (rampedD P c') c' (Nc c') t) ≤ -√c' := by
  obtain ⟨K, K', hK, hK', hvac⟩ := pmix_smooth_vacbound W bd CI Cmid hCI hCmid
  obtain ⟨A0, hA0, hFK⟩ := FKc_mul_rpow_eq W.q_pos
  have hCs := CStar_pos
  refine ⟨2 * (K + (K' + 1) / (CStar * A0)), by positivity, fun P hPI hPm hPM Nc hNc => ?_⟩
  have hr0 : Tendsto (fun c' : ℝ => P.M0 * c' ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).const_mul P.M0
  have hd_ev : ∀ᶠ c' : ℝ in atTop, rampedD P c' ≤ rampedD0 :=
    hr0.eventually_le_const rampedD0_pos
  filter_upwards [hvac P hPI hPm Nc hNc, hd_ev, eventually_gt_atTop (0 : ℝ)] with c' hv hd hc'0
  have hd0 := rampedD_nonneg P c' hc'0
  have h1 := hv (rampedD P c') hd0 hd
  have hdM : rampedD P c' = (2 * (K + (K' + 1) / (CStar * A0))) * c' ^ (-(1 / 3 : ℝ)) := by
    unfold rampedD
    rw [hPM]
  have hFKr := hFK c' hc'0
  have h2 : FKc W.q 1 c' * CStar * (-rampedD P c' / 2 + K * c' ^ (-(1 / 3 : ℝ))) =
      CStar * (FKc W.q 1 c' * c' ^ (-(1 / 3 : ℝ))) * (-(2 * (K + (K' + 1) / (CStar * A0))) / 2 + K) := by
    rw [hdM]; ring
  rw [h2, hFKr] at h1
  have h3 : CStar * (A0 * √c') * (-(2 * (K + (K' + 1) / (CStar * A0))) / 2 + K) = -(K' + 1) * √c' := by
    field_simp
    ring
  rw [h3] at h1
  linarith only [h1]

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_smooth_vacbound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_smooth_vacbound

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_smooth

end FormalResearch.ModularBootstrap.Mixtures
