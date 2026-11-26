module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoLevelLower
public import FormalResearch.ModularBootstrap.TwoLevel.CorollaryTwoFourAllWeights

/-!
# Corollary SE.8: crossing measures with a prescribed first level, uniformly on a compact set of levels
(`soft_edge_two_level_stability.tex`, `se:3.3`)

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Corollary SE.8 (`se:3.3`).  In the setting of
Theorem SE.7 (`se:3.2`; the uniform two-level lower bound `theorem_W1prime_two`) at an arbitrary fixed weight `(w, Q)`
(`n = c̃`, `t_{1,n} = ξ̄ n + A_{1,n} n^{1/3}` = `levelTime A n`): for every compact `J ⊆ (-∞, A_opt)` there are
`n_J, D_J` such that for every `n ≥ n_J`, every `A ∈ J` and every `T ≤ ξ̄ n + A_2^*(A) n^{1/3} - D_J` there is a positive
crossing measure supported in `{t_{1,n}} ∪ [T, ∞)` with strictly positive mass at `t_{1,n}`.

* `se_crossing_corollary`: the statement above, at every fixed-weight problem, with the integrability and the
  `w_*`-moment bound of `constrained_strong_duality_two_level` (`β₀ = 1/2`) attached.  Proof as in the paper:
  `theorem_W1prime_two` (zero offset) shows that no feasible `g` exists on `{t₁} ∪ [τ, ∞)` for `τ = ξ̄ n + A_2^*(A) n^{1/3} - D₂ - 1`;
  constrained strong duality (`exists_crossingMeasure_of_not_feasible`, the two-level case
  `constrained_strong_duality_two_level`) gives a crossing measure on `{t₁} ∪ [τ, ∞) ⊆ {t₁} ∪ [T, ∞)`; the positive mass at
  `t₁` follows from the `O(1)` upper bound `TheoremC15UpperInput` (`theoremC15UpperInput_probW`, every weight) because
  `min_J A_2^* > A_opt`.

The Virasoro and fixed-weight cases are the same statement (`prob` arbitrary).  The offset form (`se:lip`,
`t_{1,n} = ξ̄ n + A₁ n^{1/3} + e_n`) is not stated here.  All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.TipFront

/-- **Corollary SE.8** (`se:3.3`) at every fixed weight `(w, Q)`, uniformly for the first level `A` in a compact
`J ⊆ (-∞, A_opt)`. -/
theorem se_crossing_corollary (prob : FixedWeightProblem) {J : Set ℝ} (hJ : IsCompact J)
    (hJsub : J ⊆ Iio Aopt) :
    ∃ n_J D_J : ℝ, ∀ n : ℝ, n_J ≤ n → ∀ A ∈ J, ∀ T : ℝ, T ≤ levelTime (A2star A) n - D_J →
      ∃ meas : AdmissibleCrossingMeasure prob (n / 12),
        meas.ν ({levelTime A n} ∪ Ici T)ᶜ = 0 ∧ 0 < meas.ν {levelTime A n} ∧
        Integrable (wStar (n / 12) (1 / 2)) meas.ν ∧
        ∫ t, wStar (n / 12) (1 / 2) t ∂meas.ν ≤ dualC0 prob (n / 12) (1 / 2) := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, fun n _ A hA => absurd hA (Set.notMem_empty A)⟩
  obtain ⟨c₂, D₂, hlow⟩ := theorem_W1prime_two prob (R_off := 0) le_rfl hJ hJsub
  obtain ⟨c₃, D, hc₃, hD, hTV⟩ := Upper.Ramped.theoremC15UpperInput_probW prob
  have hA₀ := hJ.sInf_mem hne
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = sInf J := ⟨_, rfl⟩
  rw [← hA₀def] at hA₀
  have hA₀lt : A₀ < Aopt := hJsub hA₀
  have hgap : 0 < A2star A₀ - Aopt := by linarith [(A2star_mem_Ioo hA₀lt).1]
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀ : ℝ, T₀ = max (t0Star prob.w (1 / 2)) 1 := ⟨_, rfl⟩
  obtain ⟨c₄, h4⟩ := eventually_atTop.mp (eventually_le_levelTime A₀ T₀)
  obtain ⟨c₅, h5⟩ := eventually_atTop.mp (eventually_le_levelTime Aopt (T₀ + D₂ + 1))
  obtain ⟨c₆, h6⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).eventually_gt_atTop ((D + D₂ + 1) / (A2star A₀ - Aopt)))
  refine ⟨max (max c₂ c₃) (max (max c₄ c₅) c₆), D₂ + 1, fun n hn A hA T hT => ?_⟩
  have hn₂ : c₂ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn₃ : c₃ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn₄ : c₄ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have hn₅ : c₅ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have hn₆ : c₆ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hshift : 12 * prob.totalShift ≤ n := (le_max_right _ _).trans (hc₃.trans hn₃)
  have hc0 : 0 < n := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₃.trans hn₃))
  have hAlt : A < Aopt := hJsub hA
  have hAA₀ : A₀ ≤ A := by rw [hA₀def]; exact csInf_le hJ.bddBelow hA
  have hA2 : A2star A₀ ≤ A2star A := (A2star_strictMonoOn.le_iff_le hA₀lt hAlt).2 hAA₀
  have hAopt2 : Aopt < A2star A := (A2star_mem_Ioo hAlt).1
  have hT₀pos : 0 < T₀ := by rw [hT₀def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have ht₁ : T₀ ≤ levelTime A n := (h4 n hn₄).trans (levelTime_mono hc0.le hAA₀)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = levelTime (A2star A) n - D₂ - 1 := ⟨_, rfl⟩
  have hτT : T ≤ τ := by rw [hτdef]; linarith
  have hτ₀ : T₀ ≤ τ := by
    have := levelTime_mono hc0.le hAopt2.le (c' := n)
    have h5' := h5 n hn₅
    rw [hτdef]; linarith
  have hτpos : 0 < τ := lt_of_lt_of_le hT₀pos hτ₀
  -- no feasible test on `{t₁} ∪ [τ, ∞)`
  have hno : ∀ g, ¬ prob.IsFeasibleOn (n / 12) ({levelTime A n} ∪ Ici τ) g := by
    rintro g ⟨h1, h2, h3⟩
    have hwf : prob.IsWeaklyFeasible (n / 12) τ g :=
      (show prob.IsFeasible (n / 12) τ g from ⟨h1, h2, fun t ht => h3 t (Or.inr ht)⟩).isWeaklyFeasible
    have h := hlow A hA n hn₂ τ g (levelTime A n) (by simp [levelTime]) (h3 _ (Or.inl rfl)) hwf
    have e : xiBar * n + A2star A * n ^ (1 / 3 : ℝ) - D₂ = levelTime (A2star A) n - D₂ := by
      unfold levelTime; norm_num
    rw [e, hτdef] at h
    linarith
  have S : DualSetupCore prob n (1 / 2) T₀ := by
    refine ⟨hc0, hshift, by norm_num, ?_, ?_, hT₀pos⟩
    · exact le_rfl
    · rw [hT₀def]; exact le_max_left _ _
  have hXc : IsClosed ({levelTime A n} ∪ Ici τ : Set ℝ) := isClosed_singleton.union isClosed_Ici
  have hX : ({levelTime A n} ∪ Ici τ : Set ℝ) ⊆ Ici T₀ := by
    rintro t (rfl | ht)
    · exact ht₁
    · exact hτ₀.trans ht
  obtain ⟨meas, hν, hint, hle⟩ := exists_crossingMeasure_of_not_feasible prob S hXc hX hno
  have hνT : meas.ν ({levelTime A n} ∪ Ici T)ᶜ = 0 := by
    refine measure_mono_null (fun t ht => ?_) hν
    rintro (h | h)
    · exact ht (Or.inl h)
    · exact ht (Or.inr (hτT.trans h))
  refine ⟨meas, hνT, ?_, hint, hle⟩
  by_contra hzero
  have hz1 : meas.ν {levelTime A n} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hzero)
  have hz : meas.ν (Iio τ) = 0 := by
    refine measure_mono_null (fun t ht => ?_) (measure_union_null hν hz1)
    by_cases h : t ∈ ({levelTime A n} ∪ Ici τ : Set ℝ)
    · rcases h with h | h
      · exact Or.inr h
      · exact absurd h (not_le.mpr ht)
    · exact Or.inl h
  have hD1 := (Duality.proposition_D1 prob (cTilde := n) hshift hc0 hτpos ⟨meas, hz⟩).2.1
  have hup := hTV hn₃
  have hdiff : levelTime (A2star A) n - TStar n = (A2star A - Aopt) * n ^ ((1 : ℝ) / 3) :=
    levelTime_sub (A2star A) Aopt n
  have hr := h6 n hn₆
  have hlt : D + D₂ + 1 < (A2star A₀ - Aopt) * n ^ ((1 : ℝ) / 3) := by
    rwa [div_lt_iff₀ hgap, mul_comm] at hr
  have hroot : 0 ≤ n ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc0.le _
  have hmono : (A2star A₀ - Aopt) * n ^ ((1 : ℝ) / 3) ≤ (A2star A - Aopt) * n ^ ((1 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_right (by linarith) hroot
  rw [hτdef] at hD1
  linarith

/-! ### Axiom check -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.se_crossing_corollary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms se_crossing_corollary

end FormalResearch.ModularBootstrap.TwoLevel
