module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpRegionI
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpRegionII
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedThreshold

/-!
# Positivity of the bumped ramped comb for `t ≥ t_* + 1` at every weight (`fw:Ustar`, Steps 3-4)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), Steps 3 and 4.

* `rampedBumped_positive`: for every `p` and bump parameters `Pp`, there are `C_I`, `C₀ ≥ 1` such that for every
  `P : RampedParams` with `P.C_I = C_I`, `C₀ ≤ P.C_mid` (any `M_0 > 0`) and `c'` large,
  `2 g_w(c' x²/3) > 0` for the bumped ramped comb at `d = M_0 c'^{-1/3}`, for every `x ≥ 0` with
  `t ≥ t_*(P, c') + 1` (Region I, `rampedBumped_regionI`, and Region II, `rampedBumped_regionII`);
* `rampedBumped_k7`: Lemma `K7` (`fw:e3.4`) for the bumped ramped comb at every weight, uniformly in `P` and the cut.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing Upper.Comb Upper.Design
  Upper.Holes Upper.Positivity Upper.Hankel Upper.Bump Upper.Membership Upper.Assembly

/-- **`g_w > 0` for `t ≥ t_* + 1`, the bumped ramped comb** (`fw:Ustar` Steps 3-4): `C_I` is chosen from the bump data,
`C₀` is the separation / Region II constant, and every `P` with `P.C_I = C_I`, `P.C_mid ≥ C₀` works. -/
theorem rampedBumped_positive (p : ℕ) (Pp : RpParams p) :
    ∃ CI C₀ : ℝ, 1 ≤ CI ∧ 1 ≤ C₀ ∧ ∀ P : RampedParams, P.CI = CI → C₀ ≤ P.Cmid →
      ∀ᶠ c' : ℝ in atTop, ∀ x : ℝ, 0 ≤ x → rampedTstar P c' + 1 ≤ c' * x ^ 2 / 3 →
        0 < twoGW p c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
          (bumpSigma c' (nCap P c' + 6) (rampedSigma (rampedD P c') c'))
          (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) x := by
  obtain ⟨CI, hCI, hI⟩ := rampedBumped_regionI p Pp
  obtain ⟨C₀, hC₀, hII⟩ := rampedBumped_regionII p Pp
  refine ⟨CI, C₀, hCI, hC₀, fun P hP1 hP2 => ?_⟩
  filter_upwards [hI P hP1, hII P hP2, rampedD_mem P, eventually_ge_atTop (1 : ℝ)] with c' h1 h2 hd hc'1
  intro x hx0 ht
  by_cases hx : x ≤ xiStar + c' ^ (-(3 / 5 : ℝ))
  · refine h1 _ hd.1 hd.2 x hx0 ht ?_
    have hr : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have h3 : x ^ 2 ≤ (xiStar + c' ^ (-(3 / 5 : ℝ))) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ c')
    linarith
  · push Not at hx
    exact h2 _ hd.1 (hd.2.trans rampedD0_le_one) x hx.le

/-- **Lemma `K7` for the bumped ramped comb at every weight**, uniformly in `P` and `d ∈ [0, 1]`. -/
theorem rampedBumped_k7 (prob : FixedWeightProblem) (bd : BumpData) :
    ∀ᶠ c' : ℝ in atTop, ∀ (P : RampedParams) (d : ℝ), 0 ≤ d → d ≤ 1 → ∀ N' : ℕ, nCap P c' + 6 ≤ N' →
      K7ConclusionW prob c' (designComb c' 1 N' (1 / 4) (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
        (bumpEps bd c' (nCap P c' + 6) (1 / 4) (rampedEps P c'))) := by
  obtain ⟨K, hK, hk7⟩ := phase_k7W (prob := prob) 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl
    (P := 2) (by norm_num)
  filter_upwards [hk7, ramped_phaseHyp, bumped_phaseHyp bd 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl]
    with c' h1 h2 h3 P d hd hd1 N' hN'
  have := h3 (nCap P c' + 6) N' (rampedSigma d c') (rampedEps P c') 1 (h2 P d hd hd1) hN'
  norm_num at this
  exact h1 N' _ _ this

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBumped_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumped_positive

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBumped_k7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumped_k7

end FormalResearch.ModularBootstrap.Upper.Ramped
