module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpFinal

/-!
# `pmix:ramped`: the ramped comb with a macroscopic bump at fixed weight `w ≥ 1` (Proposition PM.5)

`positive_mixtures.tex`, Proposition PM.5.  The statement does not involve the Cardy weight: the comb `h_0^{(p)} = R_bump h_0^{ramp}`
and its test function `g_w = ½ (h_0^{(p)} - 𝓗_w h_0^{(p)})` depend on the weight `w` only (and on the bump data of
`rpParams (w - 1)`), so it is the *source-free* W-P6 content at every weight, now packaged under the paper's label:

* (comb hypotheses) `InnerCombHyp` of the comb (the hypotheses (i), (iii) of `fw:FWM`), the decay of `h_0`, `ĥ_0` with the membership
  of `g_w` in the test class of every fixed-weight problem of weight `w` (`K7ConclusionW`, the hypotheses of `pmix:crossing`(b),
  proved for the trivial product `Q ≡ 1`, and transferred to any source by `k7_src`);
* (bump factor) `1 ≤ R_bump ≤ K_b` on `x ≥ 0` and `R_bump ≤ 1 + C/c'` on `x ≤ ξ_* + r_p` (`bumpFactor_one_le`, `bumpFactor_le`,
  `bumpFactor_le_one_add`, uniform in the cut);
* (positivity) `g_w(t; d) > 0` for all `t ≥ t_*(d) + 1`, with `t_*(d) = ξ̄ c' + A_opt c'^{1/3} + (A_opt/|a_1|) M_0 + O(c'^{-1/3})`
  at `d = M_0 c'^{-1/3}` (`rampedThreshold`).

Differences from the paper: (a) positivity is proved at `d = M_0 c'^{-1/3}` for each fixed `M_0 > 0`, with the threshold in `c'`
depending on `M_0`, not uniformly in `d ∈ [0, d_0]`; this is all that `pmix:smooth` and `pmix:o1` use (`d = M n^{-1/3}`, `M`
fixed); (b) the constants are the Lean `C_I, C_mid` of `rampedBumped_positive` (the order of choice `(r_p, X_p, η_big) → (C_I, C_mid) → M_0 → n_0`
is the paper's).  All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Ramped FormalResearch.Special

/-- **`g_w > 0` for `t ≥ t_* + 1`** (strict positivity of the bumped ramped test function), for `P` as in
`rampedBumped_positive`. -/
theorem rampedBumpG_pos (prob : FixedWeightProblem) (P : RampedParams)
    (hpos : ∀ᶠ c' : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → rampedTstar P c' + 1 ≤ c' * x ^ 2 / 3 →
        0 < twoGW (prob.w - 1) c' 1 (rampedBumpCut (rpParams (prob.w - 1)).bumpData P c') (1 / 4)
          (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
          (bumpEps (rpParams (prob.w - 1)).bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) x) :
    ∀ᶠ c' : ℝ in atTop, ∀ t : ℝ, rampedTstar P c' + 1 ≤ t → 0 < rampedBumpG prob P c' t := by
  set Pp := rpParams (prob.w - 1) with hPp
  filter_upwards [hpos, ramped_phaseHyp,
    bumped_phaseHyp Pp.bumpData 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    rampedD_mem P, eventually_gt_atTop (0 : ℝ), rampedBumped_k7 prob Pp.bumpData]
    with c' hP hph hbph hin hd hc' hK7 t ht
  have hd1 : rampedD P c' ≤ 1 := hd.2.trans rampedD0_le_one
  have hN := le_rampedBumpCut Pp.bumpData P c'
  obtain ⟨C, hC0, hd1', hd2', hT, -⟩ := hK7 P (rampedD P c') hd.1 hd1 _ hN
  have hph' := hbph (nCap P c' + 6) (rampedBumpCut Pp.bumpData P c') (rampedSigma (rampedD P c') c')
    (rampedEps P c') 1 (hph P (rampedD P c') hd.1 hd1) hN
  have hI : InnerCombHyp c' (rampedBumpComb prob P c') := hin _ _ _ hph'.1 hph'.2.1
  have ht0 : 0 < t := by
    have : 0 ≤ rampedTstar P c' := by unfold rampedTstar; positivity
    linarith
  have hx0 : 0 ≤ xOf c' t := xOf_nonneg c' t
  have hxt : c' * xOf c' t ^ 2 / 3 = t := by
    unfold xOf
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hpos' := hP (xOf c' t) hx0 (by rw [hxt]; exact ht)
  have hh : designProfile c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
      (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
      (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) ((xOf c' t : ℝ) : ℂ) =
      ((combProfile c' (rampedBumpComb prob P c') t : ℝ) : ℂ) := by
    have := hI.combProfile_eq (s := t) ht0
    rw [← combH0_designComb]
    exact this
  have e2 := hI.edgeHankelP_eq (prob.w - 1) hc' hd1' ht0
  rw [Nat.sub_add_cancel prob.hw] at e2
  unfold twoGW at hpos'
  rw [hxt, hh] at hpos'
  have e3 : edgeHankelP (prob.w - 1) c' (designProfile c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
      (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
      (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) t =
      ((hankelTransform prob.w (combProfile c' (rampedBumpComb prob P c')) t : ℝ) : ℂ) := by
    rw [← combH0_designComb]
    exact e2
  rw [e3] at hpos'
  simp only [Complex.sub_re, Complex.ofReal_re] at hpos'
  unfold rampedBumpG pairOdd
  linarith

/-- **`pmix:ramped`** (Proposition PM.5), weight `w ≥ 1`, `p = w - 1`, bump data `bd = (rpParams p).bumpData`.  There are
`C_I, C_mid ≥ 1` such that for every ramp parameter `P` with `P.C_I = C_I`, `P.C_mid ≥ C_mid` and `d = M_0 c'^{-1/3}`
(`M_0 = P.M_0 > 0`), for all sufficiently large `c'` (`c' = n`):

1. for every cut `N' ≥ n_cap + 6` the bumped comb `D = R_bump · D_*` satisfies the hypotheses of `fw:FWM` (`InnerCombHyp`), and
   `h_0^{(p)}, ĥ_0^{(p)}` decay like `C e^{-c'L - πx}` with `g_w` in the test class of the trivial product `Q ≡ 1`
   (`K7ConclusionW`, the hypotheses of `pmix:crossing`(b)); `1 ≤ R_bump ≤ K_b` on `x ≥ 0` and
   `R_bump ≤ 1 + C/c'` on `0 ≤ x ≤ ξ_* + r_p`;
2. `g_w(t; d) > 0` for all `t ≥ t_*(d) + 1`; and `|t_*(d) - (ξ̄ c' + A_opt c'^{1/3} + (A_opt/|a_1|) M_0)| ≤ C_t c'^{-1/3}`, `C_t` absolute.

The `K7ConclusionW` conclusion at a source (floor charge) is `k7_src`. -/
theorem pmix_ramped (w : ℕ) (hw : 1 ≤ w) :
    ∃ CI Cmid : ℝ, 1 ≤ CI ∧ 1 ≤ Cmid ∧ ∃ Ct : ℝ, 0 < Ct ∧
      ∀ P : RampedParams, P.CI = CI → Cmid ≤ P.Cmid →
      ∀ᶠ c' : ℝ in atTop,
        (∀ N' : ℕ, nCap P c' + 6 ≤ N' →
          InnerCombHyp c' (designComb c' 1 N' (1 / 4)
            (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
            (bumpEps (rpParams (w - 1)).bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) ∧
          K7ConclusionW (trivialProductProblem w hw) c' (designComb c' 1 N' (1 / 4)
            (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
            (bumpEps (rpParams (w - 1)).bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')))) ∧
        (∀ (N₀ N : ℕ) (x : ℝ), 1 ≤ bumpFactor (rpParams (w - 1)).bumpData c' (1 / 4) N₀ N x) ∧
        (∀ (N₀ N : ℕ) (x : ℝ), 0 ≤ x →
          bumpFactor (rpParams (w - 1)).bumpData c' (1 / 4) N₀ N x ≤ bumpC (rpParams (w - 1)).bumpData (1 / 4)) ∧
        (∀ (N₀ N : ℕ) (x : ℝ), 0 ≤ x → x ≤ xiStar + (rpParams (w - 1)).bumpData.r →
          bumpFactor (rpParams (w - 1)).bumpData c' (1 / 4) N₀ N x ≤
            1 + bumpC' (rpParams (w - 1)).bumpData (1 / 4) / c') ∧
        (∀ t : ℝ, rampedTstar P c' + 1 ≤ t → 0 < rampedBumpG (trivialProductProblem w hw) P c' t) ∧
        |rampedTstar P c' - (xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) + Aopt / |airyZero 1| * P.M0)| ≤
          Ct * c' ^ (-(1 / 3 : ℝ)) := by
  set triv := trivialProductProblem w hw with htriv
  set Pp := rpParams (triv.w - 1) with hPp
  obtain ⟨CI, C₀, hCI, hC₀, hpos⟩ := rampedBumped_positive (triv.w - 1) Pp
  obtain ⟨Ct, hCt, hthr⟩ := rampedThreshold
  refine ⟨CI, C₀, hCI, hC₀, Ct, hCt, fun P hP1 hP2 => ?_⟩
  filter_upwards [rampedBumpG_pos triv P (hpos P hP1 hP2), hthr P, ramped_phaseHyp,
    bumped_phaseHyp Pp.bumpData 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    rampedD_mem P, rampedBumped_k7 triv Pp.bumpData,
    bumpFactor_one_le Pp.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le Pp.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le_one_add Pp.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c' hg hT hph hbph hin hd hK7 hR1 hRK hRn
  refine ⟨fun N' hN' => ⟨?_, hK7 P (rampedD P c') hd.1 (hd.2.trans rampedD0_le_one) N' hN'⟩,
    fun N₀ N x => hR1 N₀ N x, fun N₀ N x hx => hRK N₀ N x hx, fun N₀ N x hx hxr => hRn N₀ N x hx hxr,
    hg, hT⟩
  have hph' := hbph (nCap P c' + 6) N' (rampedSigma (rampedD P c') c') (rampedEps P c') 1
    (hph P (rampedD P c') hd.1 (hd.2.trans rampedD0_le_one)) hN'
  exact hin N' _ _ hph'.1 hph'.2.1

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.rampedBumpG_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumpG_pos

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_ramped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_ramped

end FormalResearch.ModularBootstrap.Mixtures
