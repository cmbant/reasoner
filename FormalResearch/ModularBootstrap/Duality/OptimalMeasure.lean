module

public import FormalResearch.ModularBootstrap.Duality.StrongDuality
public import FormalResearch.ModularBootstrap.Integration.StripTheoremA

/-!
# Corollary E1 (measure form), as far as it follows without Theorem C15

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex`, Corollary E1 (`ds:E1`), whose paper status is
"proved given Theorems E and C15".

Proved here, without C15:
* `corollary_E1_exact_gap`: whenever `T_V(c̃) > 0`, a crossing measure `ν_*(c)` exists whose gap
  is exactly `T_V(c̃)` (`ν_*` charges every `[T_V, T_V + ε)`), so `Δ_best = a + (gap of ν_*)`: the
  optimal bootstrap gap is attained by a (positive, exactly crossing-symmetric) measure;
* `corollary_E1_lower_bound`: combined with the unconditional `Integration.theoremA_T_V`, for all large `c'` such a measure exists and its gap is
  `≥ ξ̄ c' - C_A c'^{1/3}`.

Not covered (needs the constant-term/comb transfer theorem C15 or further inputs): the matching
upper bound `T_V(c) ≤ T_*(c) + O(1)` and hence `T_V(c) = T_*(c) + O(1)`; the clause
`liminf_j (τ_j - T_*)/c_j'^{1/3} ≥ 0` (it needs the sharp lower bound with the Airy constant
`A_opt`, not only Theorem A with an unspecified `C_A`); the (Gap) hypothesis of `sr:Σ₀`, `sr:Σ`
and the convergence of window measures to `μ_A` (spectral rigidity note).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

/-- `t₀(β) → 0` as `β ↓ 0`: every `T₀ > 0` admits `β₀ ∈ (0, 1/2]` with `t₀(β₀) ≤ T₀`. -/
lemma exists_beta0 {T₀ : ℝ} (hT₀ : 0 < T₀) : ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ t0 β₀ ≤ T₀ := by
  set η : ℝ := 3 * π / 2 * T₀ with hη
  have hηpos : 0 < η := by positivity
  let φ : ℝ → ℝ := fun β => β * Real.log 2 - β * Real.log β
  have hφc : Continuous φ := (continuous_id.mul continuous_const).sub Real.continuous_mul_log
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 0) := by
    have := hφc.continuousAt (x := 0)
    rw [ContinuousAt, hφ0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ev1 : ∀ᶠ β in 𝓝[>] (0 : ℝ), φ β < η := hlim.eventually (gt_mem_nhds hηpos)
  have ev2 : ∀ᶠ β in 𝓝[>] (0 : ℝ), β ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨β, hβ1, hβ2⟩ := (ev1.and ev2).exists
  refine ⟨β, hβ2.1, hβ2.2.le, ?_⟩
  have hlog : Real.log (2 / β) = Real.log 2 - Real.log β := Real.log_div (by norm_num) hβ2.1.ne'
  have hlog0 : 0 ≤ Real.log (2 / β) :=
    Real.log_nonneg (by rw [le_div_iff₀ hβ2.1]; linarith [hβ2.2])
  have hφeq : φ β = β * Real.log (2 / β) := by simp only [φ]; rw [hlog]; ring
  have hden : 3 / 4 ≤ 1 - β ^ 2 := by nlinarith [hβ2.1, hβ2.2]
  unfold t0
  rw [div_le_iff₀ (by have := Real.pi_pos; nlinarith)]
  have h1 : β * Real.log (2 / β) < η := by rw [← hφeq]; exact hβ1
  have h2 : 0 ≤ β * Real.log (2 / β) := mul_nonneg hβ2.1.le hlog0
  have : T₀ * (2 * π * (3 / 4)) ≤ T₀ * (2 * π * (1 - β ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden (by positivity)) hT₀.le
  have e : T₀ * (2 * π * (3 / 4)) = η := by rw [hη]; ring
  nlinarith

/-- **Corollary E1 (exact gap).** If `T_V(c̃) > 0` (and `c̃ ≥ 24`), there is a crossing measure
`ν_*` supported on `[T_V, ∞)` which charges every `[T_V, T_V + ε)`; i.e. a crossing measure with gap
exactly `T_V(c̃)`, so `Δ_best(c̃) = c̃/12 + T_V(c̃)` is attained. -/
theorem corollary_E1_exact_gap {cTilde : ℝ} (hc : 12 * virasoroProblem.totalShift ≤ cTilde)
    (hTV : 0 < virasoroProblem.T_V cTilde) :
    ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      meas.ν (Iio (virasoroProblem.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V cTilde + ε))) ∧
      virasoroProblem.Delta_best cTilde = cTilde / 12 + virasoroProblem.T_V cTilde := by
  obtain ⟨β₀, hβ₀, hβ₀2, hT⟩ := exists_beta0 (half_pos hTV)
  have S : DualSetup cTilde β₀ (virasoroProblem.T_V cTilde / 2) :=
    ⟨hc, hβ₀, hβ₀2, hT, half_pos hTV, by linarith⟩
  obtain ⟨meas, h1, h2, _⟩ := theorem_E_c S
  exact ⟨meas, h1, h2, rfl⟩

/-- **Corollary E1, lower-bound form** (Theorem A, unconditional): there
are `C_A > 0` and `c₁ ≥ 24` such that for every `c' ≥ c₁`, `T_V(c') ≥ ξ̄ c' - C_A c'^{1/3} > 0` and
there is a crossing measure with gap exactly `T_V(c')`. -/
theorem corollary_E1_lower_bound :
    ∃ C_A c₁ : ℝ, 0 < C_A ∧ 24 ≤ c₁ ∧ ∀ {c' : ℝ}, c₁ ≤ c' →
      0 < xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ∧
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_V c' ∧
      ∃ meas : AdmissibleCrossingMeasure virasoroProblem (c' / 12),
        meas.ν (Iio (virasoroProblem.T_V c')) = 0 ∧
        ∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V c' + ε)) := by
  obtain ⟨C_A, c_A, hCA, hc_A, hTV⟩ := Integration.theoremA_T_V
  have hxi : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  set M : ℝ := C_A / xiBar + 1 with hM
  have hM1 : 1 < M := by have : 0 < C_A / xiBar := div_pos hCA hxi; linarith
  refine ⟨C_A, max c_A (M ^ 3), hCA, hc_A.trans (le_max_left _ _), fun {c'} hc' => ?_⟩
  have hcA : c_A ≤ c' := (le_max_left _ _).trans hc'
  have hcM : M ^ 3 ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := lt_of_lt_of_le (by positivity) hcM
  have hpos : 0 < xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) := by
    set u : ℝ := c' ^ ((1 : ℝ) / 3) with hu
    have hu3 : u ^ 3 = c' := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hupos : 0 < u := Real.rpow_pos_of_pos hc0 _
    have hMu : M ≤ u := by
      by_contra hlt
      push Not at hlt
      have : u ^ 3 < M ^ 3 := pow_lt_pow_left₀ hlt hupos.le (by norm_num)
      linarith
    have hCx : C_A / xiBar < u := by linarith
    have : C_A < xiBar * u := by rwa [div_lt_iff₀ hxi, mul_comm] at hCx
    rw [← hu3]
    have hu1 : 1 ≤ u := by linarith
    have h2 : xiBar * u ≤ xiBar * u ^ 2 := by
      have : u ≤ u ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hxi.le
    have h3 : C_A < xiBar * u ^ 2 := lt_of_lt_of_le this h2
    have : 0 < u * (xiBar * u ^ 2 - C_A) := mul_pos hupos (by linarith)
    nlinarith
  have hbound := hTV hcA
  have hTVpos : 0 < virasoroProblem.T_V c' := lt_of_lt_of_le hpos hbound
  have hc24 : 24 ≤ c' := hc_A.trans hcA
  have hshift : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith
  obtain ⟨meas, h1, h2, _⟩ := corollary_E1_exact_gap hshift hTVpos
  exact ⟨hpos, hbound, meas, h1, h2⟩

/-- info: 'FormalResearch.ModularBootstrap.Duality.corollary_E1_exact_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.corollary_E1_exact_gap

/-- info: 'FormalResearch.ModularBootstrap.Duality.corollary_E1_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.corollary_E1_lower_bound

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_beta0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_beta0

/-- Non-vacuity of the standing hypotheses `DualSetup` of Theorem E: by
Theorem A (which gives `T_V(c') > 0` for large `c'`), the structure
`DualSetup` is satisfied by some `(c̃, β₀, T₀)`. -/
theorem dualSetup_nonvacuous :
    ∃ cTilde β₀ T₀ : ℝ, DualSetup cTilde β₀ T₀ := by
  obtain ⟨C_A, c₁, _, hc₁, hall⟩ := corollary_E1_lower_bound
  obtain ⟨hpos, hbound, _⟩ := hall (le_refl c₁)
  have hTV : 0 < virasoroProblem.T_V c₁ := lt_of_lt_of_le hpos hbound
  have hshift : 12 * virasoroProblem.totalShift ≤ c₁ := by
    rw [virasoroProblem_totalShift]; linarith
  obtain ⟨β₀, hβ₀, hβ₀2, hT⟩ := exists_beta0 (half_pos hTV)
  exact ⟨c₁, β₀, virasoroProblem.T_V c₁ / 2, hshift, hβ₀, hβ₀2, hT, half_pos hTV, by linarith⟩

/-- info: 'FormalResearch.ModularBootstrap.Duality.dualSetup_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.dualSetup_nonvacuous

end FormalResearch.ModularBootstrap.Duality
