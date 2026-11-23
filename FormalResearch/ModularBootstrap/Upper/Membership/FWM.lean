module

public import FormalResearch.ModularBootstrap.Upper.Membership.DecayIntegrability

/-!
# `FW-M` (`fw:FWM`) under the decay hypothesis, and non-vacuity

Combines `fwM_membership_vacuum` with `DecayIntegrability`: for a Fourier pair `(h, ĥ)` of continuous
real radial profiles at weight `w = prob.w` with the decay `|h|, |ĥ| ≤ C e^{-c' L(x) - πx}`
(`t = c' x²/3`, `L(x) = 2πx/3`; for the comb `h₀ = sech²(πb/2) B` this is the decay of Lemma `K7`
and, at weight `w`, the output of Lemma `FW-SD`), and a strip-continuous comb `H0`, the function
`g_w = ½ (h - ĥ)` lies in `Ā_w`, decays like the envelope, and has the vacuum identity
(`fwM_of_decay`).  The values at the vacuum points are bounded by `2^m` once `|h₀(b_α)| ≤ 2`
(`norm_vacuum_head_le`; the paper's `|h_{0,vac}| ≤ 8` is the case `Q = (1 - q)²`, `m = 2`:
`∑_s |(-1)^{|s|}| = 2^m = 4` values of modulus `≤ 2`).

`fwM_hypotheses_nonvacuous` shows the hypothesis package is satisfiable (self-dual Gaussian
`h = ĥ = e^{-2πt}`, `h₀(b) = e^{-2π c' b²/3}`), at every weight and every `c' > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms

lemma DecayBound.pairOdd {c' C : ℝ} {h ĥ : ℝ → ℝ} (hd : DecayBound c' C h)
    (hd' : DecayBound c' C ĥ) : DecayBound c' C (pairOdd h ĥ) := by
  intro t ht
  have h1 := hd t ht
  have h2 := hd' t ht
  unfold Membership.pairOdd
  rw [abs_div, abs_two]
  calc |h t - ĥ t| / 2 ≤ (|h t| + |ĥ t|) / 2 :=
        div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
    _ ≤ (decayEnv c' C t + decayEnv c' C t) / 2 := by gcongr
    _ = decayEnv c' C t := by ring

/-- **Lemma `FW-M` items 1-3 (`K7` at `w = 1`) under the decay hypothesis.** -/
theorem fwM_of_decay {prob : FixedWeightProblem} {c' C : ℝ} (hc' : 0 < c')
    (hS : prob.totalShift ≤ c' / 12) {h ĥ : ℝ → ℝ} {H0 : ℂ → ℂ}
    (hcont : ContinuousOn h (Ici 0)) (hcont' : ContinuousOn ĥ (Ici 0))
    (hd : DecayBound c' C h) (hd' : DecayBound c' C ĥ)
    (hF : 𝓕 (radialLift prob.w h) = radialLift prob.w ĥ)
    (hH : StripContinuation c' h H0) :
    TestClass prob (c' / 12) (pairOdd h ĥ) ∧ DecayBound c' C (pairOdd h ĥ) ∧
      ((prob.gVac (c' / 12) (pairOdd h ĥ) : ℝ) : ℂ) =
        (1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
            H0 (bAlpha c' (c' / 12 - prob.shiftSum s)) -
          (π : ℂ) * ((∫ t in Ioi (0 : ℝ), h t * prob.cardyV (c' / 12) t : ℝ) : ℂ) := by
  have hw := prob.hw
  have hp : RadialFourierPair prob.w h ĥ :=
    ⟨hcont, hcont', radialLift_integrable_of_decay hw hc' hcont hd,
      radialLift_integrable_of_decay hw hc' hcont' hd', hF⟩
  obtain ⟨hmem, hvac⟩ := fwM_membership_vacuum hc' hS hp
    (kernelIntegrable_of_decay hw hc' hcont hd) (kernelIntegrable_of_decay hw hc' hcont' hd') hH
  exact ⟨hmem, hd.pairOdd hd', hvac⟩

/-- The vacuum head `½ ∑_s (-1)^{|s|} h₀(b_{a - r_s})` is bounded by `2^m` when each value has
modulus `≤ 2` (`cmb:K7`: `|h_{0,vac}| ≤ 8` for `Q = (1-q)²`). -/
theorem norm_vacuum_head_le {prob : FixedWeightProblem} {c' : ℝ} {H0 : ℂ → ℂ}
    (hb : ∀ s : Finset (Fin prob.m), ‖H0 (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 2) :
    ‖(1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
        H0 (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ 2 ^ prob.m := by
  rw [norm_mul]
  have hsum : ‖∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
      H0 (bAlpha c' (c' / 12 - prob.shiftSum s))‖ ≤ ∑ _s : Finset (Fin prob.m), (2 : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hb s
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  push_cast at hsum
  calc ‖(1 / 2 : ℂ)‖ * _ ≤ (1 / 2) * (2 ^ prob.m * 2) := by
        rw [norm_div, norm_one, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 ^ prob.m := by ring

/-! ### Non-vacuity: the self-dual Gaussian -/

private lemma gauss_pair (w : ℕ) :
    Integrable (radialLift w (fun t => Real.exp (-2 * π * t))) ∧
      𝓕 (radialLift w (fun t => Real.exp (-2 * π * t))) =
        radialLift w (fun t => Real.exp (-2 * π * t)) := by
  have hb : 0 < ((π : ℝ) : ℂ).re := by simpa using Real.pi_pos
  have hlift : radialLift w (fun t => Real.exp (-2 * π * t)) =
      fun x : EuclideanSpace ℝ (Fin (2 * w)) => Complex.exp (-((π : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    ext x
    simp only [radialLift]
    rw [Complex.ofReal_exp]
    congr 1; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hlift]
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0
      (0 : EuclideanSpace ℝ (Fin (2 * w)))
  · ext ξ
    rw [hlift, fourier_gaussian_innerProductSpace hb ξ]
    have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) / 2 : ℂ) = (w : ℂ) := by
      rw [finrank_euclideanSpace_fin]
      push_cast; ring
    rw [hdim]
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have h1 : ((π : ℝ) : ℂ) / ((π : ℝ) : ℂ) = 1 := div_self hp
    rw [h1, Complex.one_cpow, one_mul]
    congr 1
    field_simp

/-- Quadratic bound behind the Gaussian decay. -/
private lemma gauss_decay {c' : ℝ} (hc' : 0 < c') (x : ℝ) :
    -(2 * π * c' / 3) * x ^ 2 + (2 * π * c' / 3 + π) * x ≤
      (2 * π * c' / 3) * ((1 + 3 / (2 * c')) / 2) ^ 2 := by
  have hA : 0 < 2 * π * c' / 3 := by positivity
  have hAμ : (2 * π * c' / 3) * (1 + 3 / (2 * c')) = 2 * π * c' / 3 + π := by
    field_simp
  have h3 : (2 * π * c' / 3 + π) * x =
      (2 * π * c' / 3) * (1 + 3 / (2 * c')) * x := by rw [hAμ]
  nlinarith [mul_nonneg hA.le (sq_nonneg (x - (1 + 3 / (2 * c')) / 2)), h3]

/-- **Non-vacuity of the `FW-M` hypotheses**: at every weight and every `c' > 0`, the self-dual
Gaussian `h = ĥ = e^{-2π t}` with `h₀(b) = e^{-2π c' b²/3}` satisfies the Fourier-pair, decay and
strip-continuation hypotheses of `fwM_of_decay`. -/
theorem fwM_hypotheses_nonvacuous (w : ℕ) {c' : ℝ} (hc' : 0 < c') :
    ∃ (h ĥ : ℝ → ℝ) (H0 : ℂ → ℂ) (C : ℝ),
      ContinuousOn h (Ici 0) ∧ ContinuousOn ĥ (Ici 0) ∧
      DecayBound c' C h ∧ DecayBound c' C ĥ ∧
      𝓕 (radialLift w h) = radialLift w ĥ ∧ StripContinuation c' h H0 := by
  refine ⟨fun t => Real.exp (-2 * π * t), fun t => Real.exp (-2 * π * t),
    fun b => Complex.exp (-(2 * (π : ℂ) * c' / 3) * b ^ 2),
    Real.exp ((2 * π * c' / 3) * ((1 + 3 / (2 * c')) / 2) ^ 2),
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * π * t)).continuousOn,
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * π * t)).continuousOn, ?_, ?_,
    (gauss_pair w).2, ?_⟩
  · intro t ht
    unfold decayEnv
    have hx := xOf_nonneg c' t
    have hx2 := sq_xOf hc' ht
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := gauss_decay hc' (xOf c' t)
    have ht' : t = c' * xOf c' t ^ 2 / 3 := by rw [hx2]; field_simp
    have h4 : 2 * π * t = 2 * π * c' / 3 * xOf c' t ^ 2 := by linear_combination (2 * π) * ht'
    linarith [this, h4]
  · intro t ht
    unfold decayEnv
    have hx := xOf_nonneg c' t
    have hx2 := sq_xOf hc' ht
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := gauss_decay hc' (xOf c' t)
    have ht' : t = c' * xOf c' t ^ 2 / 3 := by rw [hx2]; field_simp
    have h4 : 2 * π * t = 2 * π * c' / 3 * xOf c' t ^ 2 := by linear_combination (2 * π) * ht'
    linarith [this, h4]
  · refine ⟨?_, ?_, fun b => ?_⟩
    · exact (by fun_prop : Continuous fun b : ℂ =>
        Complex.exp (-(2 * (π : ℂ) * c' / 3) * b ^ 2)).continuousOn
    · exact (by fun_prop : Differentiable ℂ fun b : ℂ =>
        Complex.exp (-(2 * (π : ℂ) * c' / 3) * b ^ 2)).differentiableOn
    · rw [Complex.ofReal_exp]
      congr 1; push_cast; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fwM_of_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwM_of_decay

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.fwM_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwM_hypotheses_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.norm_vacuum_head_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_vacuum_head_le

end FormalResearch.ModularBootstrap.Upper.Membership
