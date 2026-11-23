module

public import FormalResearch.ModularBootstrap.Upper.Ramped.AiryProfile

/-!
# Lemma `P_unif` (`rem:profile`, `n2_ramped_comb.tex`): the packaged statement

Collects, for the ramped profile (`u_k = a_k` for `2 ≤ k ≤ N`, `u_k = u_k^W` beyond,
`ε_k = η_k gap^W_k`, `0 ≤ η_k ≤ 1/4` arbitrary) and the shift `d ∈ [0, 1]`, uniformly in `N`, `d`
and `η`:

* `pUnif_V_ramped`: the profile Lemma V (`ut:V`);
* `lemma_P_unif`: `‖W(u)‖ ≤ C (1 + |u|)^{-3/2} e(u)`, `1/2 ≤ R_1 ≤ C` (`N ≥ N₀`), and the bound
  (P-unif) on `E_0`; the same constant `C` serves all three;
* `pUnif_integral_le`: `∫ W ≤ -d/2 + E_0`, the form used by the vacuum step;
* `lemma_G_bound_unif`: the fixed-design growth bound (`lemma_G_bound`, `ut:G`) with a constant
  independent of `N`, `η_*`, `d`.

The general statements for an arbitrary admissible profile (`ProfHyp`) are `pUnif_bound`
(`ProfileBound.lean`), `profPi0_le_unif`, `profR1_bounds_unif` and `profV_identity`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma one_lt_abs_airyZero_one_sub_two : 1 < |airyZero 1 - airyZero 2| := by
  have h1 := airyZero_one.1
  have h2 := airyZero_two.2
  rw [abs_of_nonneg (by linarith [airyZero_strictAnti (le_refl 1)])]
  linarith

/-- **Lemma V for the ramped profile** (`ut:V`): for `d ∈ [0, 1]`,
`∫ W = ∑_n W(a_n)/Ai'(a_n)² = -d R_1 + ∑_{n ≥ 2} Π_n(d)` with
`Π_n(d) = Π_n(0)(1 - d/|a_n - a_1|) ∈ [0, Π_n(0)]`, hence `∫ W ≤ -d R_1 + E_0`. -/
theorem pUnif_V_ramped (N : ℕ) (η : ℕ → ℝ) (hη : AdmHeights η) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    (∀ n : ℕ, 2 ≤ n →
      profPi (designSiteU N) (rampedWidthU η) d n =
          profPi0 (designSiteU N) (rampedWidthU η) n * (1 - d / |airyZero n - airyZero 1|) ∧
        0 ≤ profPi (designSiteU N) (rampedWidthU η) d n ∧
        profPi (designSiteU N) (rampedWidthU η) d n ≤ profPi0 (designSiteU N) (rampedWidthU η) n) ∧
    HasSum (fun n : ℕ => profW (designSiteU N) (rampedWidthU η) d (airyZero (n + 1) : ℂ) /
        (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)
      (∫ x : ℝ, profW (designSiteU N) (rampedWidthU η) d (x : ℂ)) ∧
    (∫ x : ℝ, (profW (designSiteU N) (rampedWidthU η) d (x : ℂ)).re) =
      -d * profR1 (designSiteU N) (rampedWidthU η) +
        ∑' n : ℕ, profPi (designSiteU N) (rampedWidthU η) d (n + 2) ∧
    (∫ x : ℝ, (profW (designSiteU N) (rampedWidthU η) d (x : ℂ)).re) ≤
      -d * profR1 (designSiteU N) (rampedWidthU η) + profE0 (designSiteU N) (rampedWidthU η) := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  have hH : AiryProdTailHypothesis 1 (designSiteU N) (rampedWidthU η) :=
    ProfHyp.tailHyp (f := 1) le_rfl hC0 (hprof N η hη)
  obtain ⟨hpi, _, _, hid, hle⟩ := profV_identity (designSiteU N) (rampedWidthU η) hH d hd0
    (lt_of_le_of_lt hd1 one_lt_abs_airyZero_one_sub_two)
  exact ⟨fun n hn => ⟨rfl, (hpi n hn).1, (hpi n hn).2⟩,
    (profV_hasSum (designSiteU N) (rampedWidthU η) hH d).1, hid, hle⟩

/-- **Lemma `P_unif`** (`rem:profile`; with the profile Lemma V and Lemma E): there are constants
`C`, `N₀`, depending on nothing, such that for all `N ≥ N₀`, `d ∈ [0, 1]` and all heights
`0 ≤ η_k ≤ 1/4`, the Airy product `W` of the ramped profile satisfies
`‖W(u)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)` on `ℂ`, `1/2 ≤ R_1 ≤ C`, and
`E_0 ≤ C (∑_{n=2}^N η_n² n^{-4/3} + ∑_{n>N} (η_n² n^{-4/3} + n^{-10/3}))`. -/
theorem lemma_P_unif :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ∀ η : ℕ → ℝ, AdmHeights η →
      (∀ u : ℂ, ‖profW (designSiteU N) (rampedWidthU η) d u‖ ≤
        C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u) ∧
      (1 / 2 ≤ profR1 (designSiteU N) (rampedWidthU η) ∧
        profR1 (designSiteU N) (rampedWidthU η) ≤ C) ∧
      profE0 (designSiteU N) (rampedWidthU η) ≤ C *
        (∑ n ∈ Finset.Icc 2 N, η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) +
          ∑' m : ℕ, (η (N + 1 + m) ^ 2 * ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
            ((N + 1 + m : ℕ) : ℝ) ^ (-(10 / 3 : ℝ)))) := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  obtain ⟨C1, hC1, hG⟩ := pUnif_bound hC0
  obtain ⟨C2, N0, hR⟩ := profR1_bounds_unif hC0
  obtain ⟨C3, hC3, hE⟩ := pUnif_E0
  refine ⟨max C1 (max C2 C3), lt_max_of_lt_left hC1, max 1 N0, le_max_left _ _,
    fun N hN d hd0 hd1 η hη => ?_⟩
  have hP := hprof N η hη
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : N0 ≤ N := (le_max_right _ _).trans hN
  have hR' := hR N hN0 (designSiteU N) (rampedWidthU η) hP
    (fun k _ hkN => by simp [designSiteU, hkN])
  refine ⟨fun u => ?_, ⟨hR'.1, hR'.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩, ?_⟩
  · refine (hG d hd0 hd1 (designSiteU N) (rampedWidthU η) hP u).trans ?_
    have : 0 ≤ (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u; positivity
    nlinarith [le_max_left C1 (max C2 C3)]
  · refine (hE N hN1 η hη).trans ?_
    have hsum_nn : 0 ≤ ∑ n ∈ Finset.Icc 2 N, η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) +
        ∑' m : ℕ, (η (N + 1 + m) ^ 2 * ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
          ((N + 1 + m : ℕ) : ℝ) ^ (-(10 / 3 : ℝ))) := by
      refine add_nonneg (Finset.sum_nonneg fun n _ => by positivity) (tsum_nonneg fun m => by positivity)
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans' (le_max_right _ _)) hsum_nn

/-- The form of the vacuum inequality used downstream: for `N ≥ N₀`, `d ∈ [0, 1]` and arbitrary heights,
`∫ W ≤ -d/2 + E_0`. -/
theorem pUnif_integral_le :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ η : ℕ → ℝ, AdmHeights η →
      (∫ x : ℝ, (profW (designSiteU N) (rampedWidthU η) d (x : ℂ)).re) ≤
        -d / 2 + profE0 (designSiteU N) (rampedWidthU η) := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  obtain ⟨C2, N0, hR⟩ := profR1_bounds_unif hC0
  refine ⟨N0, fun N hN d hd0 hd1 η hη => ?_⟩
  have hR' := hR N hN (designSiteU N) (rampedWidthU η) (hprof N η hη)
    (fun k _ hkN => by simp [designSiteU, hkN])
  have hV := (pUnif_V_ramped N η hη d hd0 hd1).2.2.2
  nlinarith [hR'.1]

/-- **Lemma G (`ut:G`) uniformly over the fixed designs `D(N, η_*, d)`**: the constant in
`‖W(u)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)` is independent of `N`, `η_* ∈ [0, 1/4]` and `d ∈ [0, 1]`
(`lemma_G_bound` has `C = C(N, η_*, d)`). -/
theorem lemma_G_bound_unif :
    ∃ C > 0, ∀ (N : ℕ) (etaStar d : ℝ), 0 ≤ etaStar → etaStar ≤ 1 / 4 → 0 ≤ d → d ≤ 1 →
      ∀ u : ℂ, ‖designWindowW N etaStar d u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2 : ℝ)) * airyEnv u := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  obtain ⟨C1, hC1, hG⟩ := pUnif_bound hC0
  refine ⟨C1, hC1, fun N etaStar d h0 h1 hd0 hd1 u => ?_⟩
  have hη : AdmHeights (fun k => if k ≤ N then etaStar else 1 / 4) := fun k _ => by
    dsimp only
    split_ifs
    · exact ⟨h0, h1⟩
    · exact ⟨by norm_num, le_rfl⟩
  have hP := hprof N _ hη
  have heq : designWindowW N etaStar d =
      profW (designSiteU N) (rampedWidthU (fun k => if k ≤ N then etaStar else 1 / 4)) d := rfl
  rw [heq]
  exact hG d hd0 hd1 _ _ hP u

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_bound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_V_ramped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_V_ramped

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.lemma_P_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.lemma_P_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_integral_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.lemma_G_bound_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.lemma_G_bound_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.airyWindowProd_bound_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.airyWindowProd_bound_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.profPi0_le_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.profPi0_le_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.profR1_bounds_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.profR1_bounds_unif

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.profV_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.profV_identity

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_E0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.pUnif_E0

end FormalResearch.ModularBootstrap.Upper.Ramped
