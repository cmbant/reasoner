module

public import Mathlib
public import FormalResearch.Special.AiryCft2Ball

/-!
# The Airy-Poisson defect identity in its half-disc form (`ap:thmD`, proof of `(ct:rosc)`)

`constant_terms_lower.tex`, `ct:dyadic` (3), proof of `(ct:rosc)`: "since `H` is real on `ℝ`, `P_R(H) - I_R(H) = -Im A_+` with
`A_+ = ∫_{upper, R → -R} H(u) R_+(u) du`, `R_+ = (Bi - iAi)/Ai`".

`airy_defect_identity` is that **identity** (not a bound): for `Ai` with a zero-free circle `|u| = R` enclosing the zeros `a_1, …, a_N`
(`CftCircleData`) and `H` holomorphic on `|u| < R'`, `R' > R`, real-symmetric (`H(ū) = conj H(u)`),
`Σ_{n ≤ N} H(a_n)/Ai'(a_n)² - ∫_{-R}^{R} H = -Im A_+`, `A_+ = ∫_0^π (w i H(w)) R_+(w) dθ`, `w = R e^{iθ}`.

Proved (the proof of `cft2_defect_ball` with the two arc integrals kept: the lower one is `-conj` of the upper one by the symmetry).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- The upper arc integral `A_+ = ∫_{upper, R → -R} H R_+ du = ∫_0^π (w i H(w)) (Bi(w) - i Ai(w))/Ai(w) dθ`, `w = R e^{iθ}`. -/
noncomputable def airyArcPlus (R : ℝ) (H : ℂ → ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..π, (circleMap 0 R θ * I * H (circleMap 0 R θ)) *
    ((airyBiC (circleMap 0 R θ) - I * airyAiC (circleMap 0 R θ)) / airyAiC (circleMap 0 R θ))

/-- **Airy-Poisson defect identity, half-disc form** (`ap:thmD`; `(ct:rosc)` proof): `P_R(H) - ∫_{-R}^R H = -Im A_+`. -/
theorem airy_defect_identity {N : ℕ} {R R' : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R) (hRR : R < R')
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball 0 R'))
    (hsym : ∀ z ∈ ball (0 : ℂ) R', H ((starRingEnd ℂ) z) = (starRingEnd ℂ) (H z)) :
    (∑ n ∈ Finset.Icc 1 N, H (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-R)..R, H (x : ℂ) = ((-(airyArcPlus R H).im : ℝ) : ℂ) := by
  have hR := hD.radius_pos
  have hN := hD.entire
  obtain ⟨F, hF0, hF⟩ := hH.isExactOn_ball.with_val_at 0 0
  have hF' : ∀ z ∈ ball (0 : ℂ) R', HasDerivAt F (H z) z := fun z hz => hF z hz
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hNw : ∀ θ, airyAiC (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  have hHc : Continuous (fun θ : ℝ => H (w θ)) :=
    hH.continuousOn.comp_continuous hwc (fun θ => cft2_mem_ball hR hRR θ)
  set J : ℝ → ℂ := fun θ => (w θ * I) * H (w θ) with hJ
  have hJc : Continuous J := by rw [hJ]; exact (hwc.mul continuous_const).mul hHc
  set Rp : ℝ → ℂ := fun θ => airyBiC (w θ) / airyAiC (w θ) - I with hRp
  set Rm : ℝ → ℂ := fun θ => airyBiC (w θ) / airyAiC (w θ) + I with hRm
  have hMc : Continuous (fun θ => airyBiC (w θ)) := differentiable_airyBiC.continuous.comp hwc
  have hNc : Continuous (fun θ => airyAiC (w θ)) := hN.continuous.comp hwc
  have hQc : Continuous (fun θ => airyBiC (w θ) / airyAiC (w θ)) := hMc.div hNc hNw
  have hRpc : Continuous Rp := by rw [hRp]; exact hQc.sub continuous_const
  have hRmc : Continuous Rm := by rw [hRm]; exact hQc.add continuous_const
  have hcirc : ∮ z in C(0, R), H z * airyBiC z / airyAiC z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (airyBiC (w θ) / airyAiC (w θ)) := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, hJ, hw]
    ring
  have hΦc : Continuous (fun θ => J θ * (airyBiC (w θ) / airyAiC (w θ))) := hJc.mul hQc
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (airyBiC (w θ) / airyAiC (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← integral_add h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRp]
    ring
  have hlow : ∫ θ in π..(2 * π), J θ * (airyBiC (w θ) / airyAiC (w θ)) =
      (∫ θ in π..(2 * π), J θ * Rm θ) - I * (∫ θ in π..(2 * π), J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rm θ) volume π (2 * π) :=
      (hJc.mul hRmc).intervalIntegrable π (2 * π)
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume π (2 * π) :=
      (hJc.const_mul I).intervalIntegrable π (2 * π)
    rw [← intervalIntegral.integral_const_mul, ← integral_sub h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRm]
    ring
  have hJup : ∫ θ in (0 : ℝ)..π, J θ = F (-(R : ℂ)) - F R := by
    have := cft2_arc_ball hR hRR hF' hH 0 π
    rw [cftDef_circleMap_pi, cftDef_circleMap_zero] at this
    simpa using this
  have hJlow : ∫ θ in π..(2 * π), J θ = F R - F (-(R : ℂ)) := by
    have := cft2_arc_ball hR hRR hF' hH π (2 * π)
    rw [cftDef_circleMap_pi, cftDef_circleMap_two_pi] at this
    simpa using this
  have hdiam := cft2_diam_ball hR hRR hF' hH
  have hdiam' : ∫ x in (-R)..R, H (x : ℂ) = F R - F (-(R : ℂ)) := by simpa using hdiam
  have hres : ∮ z in C(0, R), H z * airyBiC z / airyAiC z =
      2 * π * I * ∑ i ∈ Finset.Icc 1 N, H (airyZero i : ℂ) * airyBiC (airyZero i : ℂ) /
        deriv airyAiC (airyZero i : ℂ) :=
    cft2_residue_ball hD hRR (H := fun z => H z * airyBiC z) (hH.mul differentiable_airyBiC.differentiableOn)
  rw [hcirc, ← integral_add_adjacent_intervals (hΦc.intervalIntegrable 0 π)
    (hΦc.intervalIntegrable π (2 * π)), hup, hlow, hJup, hJlow] at hres
  have hsum : (-(π : ℂ)) * (∑ n ∈ Finset.Icc 1 N, H (airyZero n : ℂ) * airyBiC (airyZero n : ℂ) /
      deriv airyAiC (airyZero n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N, H (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cftDef_airyBiC_at_zero n]
    have hd := airyZero_deriv_ne_zero n
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ, T = ∑ n ∈ Finset.Icc 1 N, H (airyZero n : ℂ) * airyBiC (airyZero n : ℂ) /
      deriv airyAiC (airyZero n : ℂ) := ⟨_, rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ A : ℂ, A = ∫ θ in (0 : ℝ)..π, J θ * Rp θ := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : ℂ, A = ∫ θ in π..(2 * π), J θ * Rm θ := ⟨_, rfl⟩
  rw [← hTdef, ← hA1def, ← hA2def] at hres
  rw [← hTdef] at hsum
  have key : (-(π : ℂ)) * T - (∫ x in (-R)..R, H (x : ℂ)) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(I / 2)) * hres - ((π : ℂ) * T + (F R - F (-(R : ℂ)))) * hI
  -- the lower arc is `-conj` of the upper one
  have hA1 : A1 = airyArcPlus R H := by
    rw [hA1def]; unfold airyArcPlus; refine integral_congr fun θ _ => ?_
    have h0 : airyAiC (circleMap 0 R θ) ≠ 0 := hNw θ
    simp only [hJ, hRp, hw]
    field_simp
  have hpt : ∀ s : ℝ, J (2 * π - s) * Rm (2 * π - s) = -(starRingEnd ℂ) (J s * Rp s) := by
    intro s
    have hws : w (2 * π - s) = (starRingEnd ℂ) (w s) := by
      simp only [hw, circleMap, zero_add, map_mul, Complex.conj_ofReal]
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      rw [show ((2 * π - s : ℝ) : ℂ) * I = -((s : ℂ) * I) + 2 * π * I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      congr 2; ring
    have hmem : w s ∈ ball (0 : ℂ) R' := cft2_mem_ball hR hRR s
    simp only [hJ, hRm, hRp, hws, map_mul, map_sub, map_div₀, map_add, Complex.conj_I,
      conj_airyBiC, conj_airyAiC, Complex.conj_conj]
    rw [hsym _ hmem]
    ring
  have hA2 : A2 = -(starRingEnd ℂ) A1 := by
    have h1 := intervalIntegral.integral_comp_sub_left (fun θ => J θ * Rm θ) (a := 0) (b := π) (2 * π)
    have e1 : 2 * π - π = π := by ring
    have e2 : 2 * π - 0 = 2 * π := by ring
    rw [e1, e2] at h1
    rw [hA2def, ← h1, hA1def]
    simp only [hpt]
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_of_le Real.pi_pos.le,
      MeasureTheory.integral_neg, integral_conj]
  have hfin : ((-(airyArcPlus R H).im : ℝ) : ℂ) = (I / 2) * (A1 + A2) := by
    rw [hA2, ← hA1]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
      ring
    · simp [Complex.mul_re, Complex.mul_im]
  rw [← hsum, key]
  exact hfin.symm

/-- info: 'FormalResearch.SignUncertainty.airy_defect_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_defect_identity

end FormalResearch.SignUncertainty
