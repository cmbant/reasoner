module

public import FormalResearch.ModularBootstrap.Duality.LimitMeasure

/-!
# Strong duality with attainment (Theorem E of `dual_spectrum.tex`)

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem E (`ds:E`).
Setting (`DualSetup`): Virasoro problem at `c̃ = c' = c - 1 ≥ 24`, `T_V(c) > 0`, `T₀ ∈ (0, T_V)`,
`β₀ ∈ (0, 1/2]` with `t₀(β₀) ≤ T₀`; `h`, `w_*`, `C₀` as in Lemma M (`Duality.DualMajorant`).

* `theorem_E_b`: for `T₀ ≤ T < T_V` there is a crossing measure `ν_T` (positive, (Z1), (Z2)) supported
  on `[T, ∞)` with `∫ w_* dν_T ≤ C₀`.
* `theorem_E_c`: there is a crossing measure `ν_*` supported on `[T_V, ∞)` with
  `∫ w_* dν_* ≤ C₀` and `min supp ν_* = T_V` (every `[T_V, T_V + ε)` carries mass).
* `theorem_E`: both, and `T_V(c) = max {τ : a crossing measure at gap τ exists}`
  (`IsGreatest`).

Route (differs from the paper's intermediate steps, same statement): finite moment problems in the
family `{Ξ_β}` (`MomentProblem`; finite-dimensional separation, Lemma M(b)); weak compactness of
the measures `w_* dν` on the compactification `[T₀, ∞] ≅ [0, 1]` with the finite-intersection
property in all `β > 0` simultaneously (`Compactness`, `MeasureCompactness`); transport back to
`ℝ` (`LimitMeasure`); nested compact sets for `T_n ↑ T_V` (this file). The paper's Laguerre functions
`ψ_k` and the odd-moment equivalence `MehlerOddMomentInput` are not used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

lemma zetaB_mono {T₀ T T' : ℝ} (hT : T₀ ≤ T) (hTT' : T ≤ T') (s : Ecoord) :
    zetaB T₀ T s ≤ zetaB T₀ T' s := by
  show max _ 0 ≤ max _ 0
  refine max_le_max ?_ le_rfl
  have : (1 + (T' - T₀))⁻¹ ≤ (1 + (T - T₀))⁻¹ := inv_anti₀ (by linarith) (by linarith)
  linarith

/-- **Theorem E (b)** (`dual_spectrum.tex`, `ds:E`): for `T₀ ≤ T < T_V` there is a crossing
measure supported on `[T, ∞)` with `∫ w_* dν ≤ C₀`. -/
theorem theorem_E_b {cTilde β₀ T₀ : ℝ} (S : DualSetup cTilde β₀ T₀) {T : ℝ} (hT₀T : T₀ ≤ T)
    (hTV : T < virasoroProblem.T_V cTilde) :
    ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      meas.ν (Iio T) = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 (cTilde / 12) β₀ := by
  obtain ⟨μ, hmass, hζ, hcross⟩ := exists_measure_exact S hT₀T hTV
  obtain ⟨meas, hsupp, hint, hle⟩ := exists_crossingMeasure_of_limit S μ hmass hcross
  exact ⟨meas, hsupp T hT₀T hζ, hint, hle⟩

/-- The crossing exactness condition on measures on `[0, 1]` is weakly closed. -/
lemma isClosed_crossing_exact {cTilde β₀ T₀ : ℝ} (S : DualSetup cTilde β₀ T₀) :
    IsClosed {μ : FiniteMeasure Ecoord | ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀) (by linarith [S.ha]) S.hβ₀ S.hT₀pos hβ x
        ∂(μ : Measure Ecoord) = crossingRHS (cTilde / 12) β} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun β => isClosed_iInter fun hβ => ?_
  exact isClosed_eq (continuous_integral_finiteMeasure _) continuous_const

/-- **Theorem E (c)**: the limit measure `ν_*` along `T_n ↑ T_V` is a crossing measure supported
on `[T_V, ∞)`, with `∫ w_* dν_* ≤ C₀` and `min supp ν_* = T_V`. -/
theorem theorem_E_c {cTilde β₀ T₀ : ℝ} (S : DualSetup cTilde β₀ T₀) :
    ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      meas.ν (Iio (virasoroProblem.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V cTilde + ε))) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 (cTilde / 12) β₀ := by
  set TV := virasoroProblem.T_V cTilde with hTVdef
  have hTV0 : T₀ < TV := S.hT₀V
  have hC0 : 0 < dualC0 (cTilde / 12) β₀ := dualC0_pos S.ha S.hβ₀ S.hβ₀2
  set C : ℝ≥0 := (dualC0 (cTilde / 12) β₀).toNNReal with hC
  have hCcoe : (C : ℝ) = dualC0 (cTilde / 12) β₀ := Real.coe_toNNReal _ hC0.le
  let Tn : ℕ → ℝ := fun n => TV - (TV - T₀) / (n + 2)
  have hTn0 : ∀ n, T₀ ≤ Tn n := fun n => by
    have : (TV - T₀) / (n + 2) ≤ TV - T₀ := by
      apply div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show T₀ ≤ TV - (TV - T₀) / (n + 2)
    linarith
  have hTnV : ∀ n, Tn n < TV := fun n => by
    have : 0 < (TV - T₀) / (n + 2) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      apply div_pos (by linarith) (by linarith)
    show TV - (TV - T₀) / (n + 2) < TV
    linarith
  have hTnmono : ∀ n, Tn n ≤ Tn (n + 1) := fun n => by
    show TV - (TV - T₀) / (n + 2) ≤ TV - (TV - T₀) / ((n + 1 : ℕ) + 2)
    have h1 : (TV - T₀) / (((n + 1 : ℕ) : ℝ) + 2) ≤ (TV - T₀) / (n + 2) := by
      apply div_le_div_of_nonneg_left (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      push_cast; linarith
    linarith
  let A : ℕ → Set (FiniteMeasure Ecoord) := fun n =>
    Kset C (zetaB T₀ (Tn n)) ∩ {μ : FiniteMeasure Ecoord | ∀ (β : ℝ) (hβ : 0 < β),
      ∫ x, FtildeB (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀) (by linarith [S.ha]) S.hβ₀ S.hT₀pos hβ x
        ∂(μ : Measure Ecoord) = crossingRHS (cTilde / 12) β}
  have hAcl : ∀ n, IsClosed (A n) := fun n => (isClosed_Kset C _).inter (isClosed_crossing_exact S)
  have hA0 : IsCompact (A 0) := (isCompact_Kset C _).inter_right (isClosed_crossing_exact S)
  have hAne : ∀ n, (A n).Nonempty := fun n => by
    obtain ⟨μ, hmass, hζ, hcross⟩ := exists_measure_exact S (hTn0 n) (hTnV n)
    refine ⟨μ, ⟨?_, hζ⟩, hcross⟩
    show μ.mass ≤ C
    rw [← NNReal.coe_le_coe, hCcoe]; exact hmass
  have hAmono : ∀ n, A (n + 1) ⊆ A n := by
    rintro n μ ⟨⟨hm, hζ⟩, hc⟩
    refine ⟨⟨hm, ?_⟩, hc⟩
    have h1 : ∫ x, zetaB T₀ (Tn n) x ∂(μ : Measure Ecoord) ≤
        ∫ x, zetaB T₀ (Tn (n + 1)) x ∂(μ : Measure Ecoord) :=
      integral_mono (BoundedContinuousFunction.integrable _ _)
        (BoundedContinuousFunction.integrable _ _) fun s => zetaB_mono (hTn0 n) (hTnmono n) s
    have h2 : 0 ≤ ∫ x, zetaB T₀ (Tn n) x ∂(μ : Measure Ecoord) :=
      integral_nonneg fun s => zetaB_nonneg _ _ s
    show ∫ x, zetaB T₀ (Tn n) x ∂(μ : Measure Ecoord) = 0
    have : ∫ x, zetaB T₀ (Tn (n + 1)) x ∂(μ : Measure Ecoord) = 0 := hζ
    linarith
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A hAmono
    hAne hA0 hAcl
  rw [mem_iInter] at hμ
  obtain ⟨⟨hm0, _⟩, hcross⟩ := hμ 0
  have hmass : (μ.mass : ℝ) ≤ dualC0 (cTilde / 12) β₀ := by
    rw [← hCcoe]; exact_mod_cast hm0
  obtain ⟨meas, hsupp, hint, hle⟩ := exists_crossingMeasure_of_limit S μ hmass hcross
  have hn : ∀ n, meas.ν (Iio (Tn n)) = 0 := fun n =>
    hsupp (Tn n) (hTn0 n) ((hμ n).1.2)
  have hTVzero : meas.ν (Iio TV) = 0 := by
    refine measure_mono_null (fun t ht => ?_) (measure_iUnion_null hn)
    simp only [mem_Iio] at ht
    obtain ⟨n, hn'⟩ := exists_nat_gt ((TV - T₀) / (TV - t))
    have hpos : 0 < TV - t := by linarith
    have : (TV - T₀) / (n + 2) < TV - t := by
      rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
      have := (div_lt_iff₀ hpos).1 hn'
      nlinarith
    refine mem_iUnion.2 ⟨n, ?_⟩
    show t < TV - (TV - T₀) / (n + 2)
    linarith
  refine ⟨meas, hTVzero, fun ε hε => ?_, hint, hle⟩
  by_contra hcon
  have hz : meas.ν (Iio (TV + ε)) = 0 := by
    exact nonpos_iff_eq_zero.1 (not_lt.1 hcon)
  have hcpos : 0 < cTilde := by
    have := S.hc; rw [virasoroProblem_totalShift] at this; linarith
  obtain ⟨_, hle', _⟩ := proposition_D1 virasoroProblem (cTilde := cTilde) (τ := TV + ε) S.hc hcpos
    (by linarith [S.hT₀pos]) ⟨meas, hz⟩
  linarith

/-- **Theorem E** (`dual_spectrum.tex`, `ds:E`; Virasoro problem, `c̃ = c' = c - 1`): in the
setting `DualSetup` (`T₀ ∈ (0, T_V)`, `β₀ ∈ (0,1/2]`, `t₀(β₀) ≤ T₀`),

* (b) for `T₀ ≤ T < T_V(c)` there is a crossing measure `ν_T` supported on `[T, ∞)` with
  `∫ w_* dν_T ≤ C₀`;
* (c) there is a crossing measure `ν_*` supported on `[T_V, ∞)` with `∫ w_* dν_* ≤ C₀` and
  `min supp ν_* = T_V`;
* hence `T_V(c) = max {τ : a crossing measure at gap τ exists}`.

Statement (a) of the paper (finite-order moment problems for the Laguerre functions `ψ_k`) is
replaced by `exists_atomic_approx` (finite families `Ξ_β`); see the module docstring. -/
theorem theorem_E {cTilde β₀ T₀ : ℝ} (S : DualSetup cTilde β₀ T₀) :
    (∀ T, T₀ ≤ T → T < virasoroProblem.T_V cTilde →
      ∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
        meas.ν (Iio T) = 0 ∧ Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
        ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 (cTilde / 12) β₀) ∧
    (∃ meas : AdmissibleCrossingMeasure virasoroProblem (cTilde / 12),
      meas.ν (Iio (virasoroProblem.T_V cTilde)) = 0 ∧
      (∀ ε : ℝ, 0 < ε → 0 < meas.ν (Iio (virasoroProblem.T_V cTilde + ε))) ∧
      Integrable (wStar (cTilde / 12) β₀) meas.ν ∧
      ∫ t, wStar (cTilde / 12) β₀ t ∂meas.ν ≤ dualC0 (cTilde / 12) β₀) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ HasCrossingMeasureAt virasoroProblem (cTilde / 12) τ}
      (virasoroProblem.T_V cTilde) := by
  have hcpos : 0 < cTilde := by
    have := S.hc; rw [virasoroProblem_totalShift] at this; linarith
  have hc := theorem_E_c S
  refine ⟨fun T hT hTV => theorem_E_b S hT hTV, hc, ?_, ?_⟩
  · obtain ⟨meas, h1, _⟩ := hc
    exact ⟨lt_trans S.hT₀pos S.hT₀V, meas, h1⟩
  · rintro τ ⟨hτ, hex⟩
    exact (proposition_D1 virasoroProblem (cTilde := cTilde) (τ := τ) S.hc hcpos hτ hex).2.1

/-- info: 'FormalResearch.ModularBootstrap.Duality.theorem_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.theorem_E

/-- info: 'FormalResearch.ModularBootstrap.Duality.theorem_E_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.theorem_E_b

/-- info: 'FormalResearch.ModularBootstrap.Duality.theorem_E_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.theorem_E_c

end FormalResearch.ModularBootstrap.Duality
