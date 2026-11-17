module

public import FormalResearch.Special.AiryCftDefect

/-!
# Theorem D in integral form

Statement formalised (CFT/PR240 `AIRY_POISSON.md` Theorem D, integral form of the bound): for `f` entire and a zero-free
circle `|u| = R` enclosing the zeros `a_1, …, a_N` of `Ai`,

`|P_R(f) - I_R(f)| ≤ (R/2) (∫_0^π |f R₊|(Re^{iθ}) dθ + ∫_π^{2π} |f R₋|(Re^{iθ}) dθ)`,
`R_± = (Bi ∓ iAi)/Ai`, `P_R(f) = Σ_{n ≤ N} f(a_n)/Ai'(a_n)²`, `I_R(f) = ∫_{-R}^{R} f`

(`airyQ_defect_bound_int`; the sup form `airy_defect_bound` of `AiryCftDefect` has `π R M` for `M ≥ sup |f R_±|`).  With the
good-circle ratio bounds `|R_±| e ≤ 30 √π` this gives `|P_R - I_R| ≤ (R/2)·30√π ∫_0^{2π} (|f|/e)(Re^{iθ}) dθ`
(`airyQ_defect_le_arc`), i.e. `15 √π` times the *circle integral* of `|f|/e`, which is what the Hardy-space bound
of `AiryCftQArc` controls for all `f` in the class `𝒢` (the sup-form bound `C (1+r)^ν` needs `ν < -1`).
The proof is that of `airy_defect_bound` with the two estimates of the arc integrals `A_±` by their `L¹` norms.
Only the integral form of the estimate is new.  All **proved**.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- **Theorem D, integral form.** -/
theorem airyQ_defect_bound_int {N : ℕ} {R : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ‖(∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-R)..R, f (x : ℂ)‖ ≤
      (R / 2) * ((∫ θ in (0 : ℝ)..π,
          ‖f (circleMap 0 R θ) * ((airyBiC (circleMap 0 R θ) - I * airyAiC (circleMap 0 R θ)) /
            airyAiC (circleMap 0 R θ))‖) +
        ∫ θ in π..(2 * π),
          ‖f (circleMap 0 R θ) * ((airyBiC (circleMap 0 R θ) + I * airyAiC (circleMap 0 R θ)) /
            airyAiC (circleMap 0 R θ))‖) := by
  have hR := hD.radius_pos
  obtain ⟨F, hF0, hF⟩ := (Differentiable.isExactOn_univ hf).with_val_at 0 0
  have hF' : ∀ z, HasDerivAt F (f z) z := fun z => hF z trivial
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hAi : ∀ θ, airyAiC (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  set J : ℝ → ℂ := fun θ => (w θ * I) * f (w θ) with hJ
  have hJc : Continuous J := by rw [hJ]; have := hf.continuous; fun_prop
  set Rp : ℝ → ℂ := fun θ => (airyBiC (w θ) - I * airyAiC (w θ)) / airyAiC (w θ) with hRp
  set Rm : ℝ → ℂ := fun θ => (airyBiC (w θ) + I * airyAiC (w θ)) / airyAiC (w θ) with hRm
  have hBc : Continuous (fun θ => airyBiC (w θ)) := differentiable_airyBiC.continuous.comp hwc
  have hAc : Continuous (fun θ => airyAiC (w θ)) := differentiable_airyAiC.continuous.comp hwc
  have hRpc : Continuous Rp := by
    rw [hRp]; exact (hBc.sub (continuous_const.mul hAc)).div hAc hAi
  have hRmc : Continuous Rm := by
    rw [hRm]; exact (hBc.add (continuous_const.mul hAc)).div hAc hAi
  -- the circle integral as a `θ`-integral
  have hcirc : ∮ z in C(0, R), f z * airyBiC z / airyAiC z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (airyBiC (w θ) / airyAiC (w θ)) := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, hJ, hw]
    ring
  have hΦc : Continuous (fun θ => J θ * (airyBiC (w θ) / airyAiC (w θ))) :=
    hJc.mul (hBc.div hAc hAi)
  -- upper and lower halves
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (airyBiC (w θ) / airyAiC (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← integral_add h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRp]
    have := hAi θ
    field_simp
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
    have := hAi θ
    field_simp
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
  have hres := cftDef_residue hD hf
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
  obtain ⟨S, hSdef⟩ : ∃ S : ℂ, S = ∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ A : ℂ, A = ∫ θ in (0 : ℝ)..π, J θ * Rp θ := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : ℂ, A = ∫ θ in π..(2 * π), J θ * Rm θ := ⟨_, rfl⟩
  rw [← hSdef, ← hA1def, ← hA2def] at hres
  rw [← hA1def] at hA1
  rw [← hA2def] at hA2
  rw [← hSdef]
  have key : S - (∫ x in (-R)..R, f (x : ℂ)) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(I / 2)) * hres + (S - (F R - F (-(R : ℂ)))) * hI
  rw [key, norm_mul]
  have h2 : ‖I / 2‖ = 1 / 2 := by simp
  rw [h2]
  have h3 : ‖A1 + A2‖ ≤ R * (∫ θ in (0 : ℝ)..π, ‖f (w θ) * Rp θ‖) + R * ∫ θ in π..(2 * π), ‖f (w θ) * Rm θ‖ :=
    (norm_add_le _ _).trans (add_le_add hA1 hA2)
  have : (1 / 2 : ℝ) * ‖A1 + A2‖ ≤ (R / 2) * ((∫ θ in (0 : ℝ)..π, ‖f (w θ) * Rp θ‖) +
      ∫ θ in π..(2 * π), ‖f (w θ) * Rm θ‖) := by linarith
  exact this

/-- info: 'FormalResearch.Special.airyQ_defect_bound_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_defect_bound_int

end FormalResearch.Special
