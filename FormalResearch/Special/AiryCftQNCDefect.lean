module

public import FormalResearch.Special.AiryCft2Generic

/-!
# The residue-defect formula for a general pair `(N, M)`, integral form

Generic complex analysis (no Airy function here): the integral form of `cft2_defect_bound`.  For entire `N`, `M`, `f`, `S` the
finite set of the simple zeros of `N` in `|w| ≤ R` (all in `|w| < R`),

`‖-π Σ_{t∈S} f(t) M(t)/N'(t) - ∫_{-R}^{R} f‖ ≤ (R/2) (∫_0^π ‖f (M/N - i)‖ + ∫_π^{2π} ‖f (M/N + i)‖)(Re^{iθ}) dθ`

(`cft2_defect_bound_int`), the sup form `π R B` being the corollary `‖f (M/N ∓ i)‖ ≤ B`.  All **proved**; this is what lets the
Hardy-space arc bound (`AiryCftQArc`) replace the sup bound `C (1+r)^ν` for `P·Ai + Q·Ai'` and the Clark functions.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- **Residue-defect bound for a general pair `(N, M)`, integral form.** -/
theorem cft2_defect_bound_int {N M f : ℂ → ℂ} {R : ℝ} (hN : Differentiable ℂ N) (hM : Differentiable ℂ M)
    (hf : Differentiable ℂ f) (hR : 0 < R) (S : Finset ℂ)
    (hin : ∀ t ∈ S, ‖t‖ < R) (hz : ∀ t ∈ S, N t = 0) (hs : ∀ t ∈ S, deriv N t ≠ 0)
    (hc : ∀ w : ℂ, ‖w‖ ≤ R → N w = 0 → w ∈ S)     :
    ‖(-(π : ℂ)) * (∑ t ∈ S, f t * M t / deriv N t) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤
      (R / 2) * ((∫ θ in (0 : ℝ)..π, ‖f (circleMap 0 R θ) * (M (circleMap 0 R θ) / N (circleMap 0 R θ) - I)‖) +
        ∫ θ in π..(2 * π), ‖f (circleMap 0 R θ) * (M (circleMap 0 R θ) / N (circleMap 0 R θ) + I)‖) := by
  obtain ⟨c, s, hD, hsum⟩ := cft2_circleData_of_finset hN hR S hin hz hs hc
  obtain ⟨F, hF0, hF⟩ := (Differentiable.isExactOn_univ hf).with_val_at 0 0
  have hF' : ∀ z, HasDerivAt F (f z) z := fun z => hF z trivial
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hNw : ∀ θ, N (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  set J : ℝ → ℂ := fun θ => (w θ * I) * f (w θ) with hJ
  have hJc : Continuous J := by rw [hJ]; have := hf.continuous; fun_prop
  set Rp : ℝ → ℂ := fun θ => M (w θ) / N (w θ) - I with hRp
  set Rm : ℝ → ℂ := fun θ => M (w θ) / N (w θ) + I with hRm
  have hMc : Continuous (fun θ => M (w θ)) := hM.continuous.comp hwc
  have hNc : Continuous (fun θ => N (w θ)) := hN.continuous.comp hwc
  have hQc : Continuous (fun θ => M (w θ) / N (w θ)) := hMc.div hNc hNw
  have hRpc : Continuous Rp := by rw [hRp]; exact hQc.sub continuous_const
  have hRmc : Continuous Rm := by rw [hRm]; exact hQc.add continuous_const
  -- the circle integral as a `θ`-integral
  have hcirc : ∮ z in C(0, R), f z * M z / N z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (M (w θ) / N (w θ)) := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, hJ, hw]
    ring
  have hΦc : Continuous (fun θ => J θ * (M (w θ) / N (w θ))) := hJc.mul hQc
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (M (w θ) / N (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← integral_add h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRp]
    ring
  have hlow : ∫ θ in π..(2 * π), J θ * (M (w θ) / N (w θ)) =
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
    have := cftDef_arc hF' hf.continuous R 0 π
    rw [cftDef_circleMap_pi, cftDef_circleMap_zero] at this
    simpa using this
  have hJlow : ∫ θ in π..(2 * π), J θ = F R - F (-(R : ℂ)) := by
    have := cftDef_arc hF' hf.continuous R π (2 * π)
    rw [cftDef_circleMap_pi, cftDef_circleMap_two_pi] at this
    simpa using this
  have hdiam := cftDef_diam hF' hf.continuous R
  have hdiam' : ∫ x in (-R)..R, f (x : ℂ) = F R - F (-(R : ℂ)) := by simpa using hdiam
  -- the residue formula
  have hres : ∮ z in C(0, R), f z * M z / N z =
      2 * π * I * ∑ t ∈ S, f t * M t / deriv N t := by
    have h := cftCircle_residue hD (H := fun z => f z * M z) (hf.mul hM)
    rw [h]
    congr 1
    exact hsum (fun t => f t * M t / deriv N t)
  rw [hcirc, ← integral_add_adjacent_intervals (hΦc.intervalIntegrable 0 π)
    (hΦc.intervalIntegrable π (2 * π)), hup, hlow, hJup, hJlow] at hres
  -- estimates on the two arcs
  have hnorm : ∀ (θ : ℝ) (X : ℂ), ‖J θ * X‖ = R * ‖f (w θ) * X‖ := by
    intro θ X
    simp only [hJ, norm_mul, hwn θ, Complex.norm_I]
    ring
  have hA1 : ‖∫ θ in (0 : ℝ)..π, J θ * Rp θ‖ ≤
      R * ∫ θ in (0 : ℝ)..π, ‖f (w θ) * Rp θ‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    exact le_of_eq (intervalIntegral.integral_congr fun θ _ => hnorm θ (Rp θ))
  have hA2 : ‖∫ θ in π..(2 * π), J θ * Rm θ‖ ≤
      R * ∫ θ in π..(2 * π), ‖f (w θ) * Rm θ‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith [Real.pi_pos])).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    exact le_of_eq (intervalIntegral.integral_congr fun θ _ => hnorm θ (Rm θ))
  -- assemble
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ, T = ∑ t ∈ S, f t * M t / deriv N t := ⟨_, rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ A : ℂ, A = ∫ θ in (0 : ℝ)..π, J θ * Rp θ := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : ℂ, A = ∫ θ in π..(2 * π), J θ * Rm θ := ⟨_, rfl⟩
  rw [← hTdef, ← hA1def, ← hA2def] at hres
  rw [← hA1def] at hA1
  rw [← hA2def] at hA2
  rw [← hTdef]
  have key : (-(π : ℂ)) * T - (∫ x in (-R)..R, f (x : ℂ)) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(I / 2)) * hres - ((π : ℂ) * T + (F R - F (-(R : ℂ)))) * hI
  rw [key, norm_mul]
  have h2 : ‖I / 2‖ = 1 / 2 := by simp
  rw [h2]
  have h3 : ‖A1 + A2‖ ≤ R * (∫ θ in (0 : ℝ)..π, ‖f (w θ) * Rp θ‖) + R * ∫ θ in π..(2 * π), ‖f (w θ) * Rm θ‖ :=
    (norm_add_le _ _).trans (add_le_add hA1 hA2)
  have : (1 / 2 : ℝ) * ‖A1 + A2‖ ≤ (R / 2) * ((∫ θ in (0 : ℝ)..π, ‖f (w θ) * Rp θ‖) +
      ∫ θ in π..(2 * π), ‖f (w θ) * Rm θ‖) := by linarith
  exact this

/-- info: 'FormalResearch.Special.cft2_defect_bound_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cft2_defect_bound_int

end FormalResearch.Special
