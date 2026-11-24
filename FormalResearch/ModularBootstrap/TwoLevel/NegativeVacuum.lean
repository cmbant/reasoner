module

public import FormalResearch.ModularBootstrap.TwoLevel.Exclusion
public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumTail
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityFamily
public import FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

/-!
# `TwoZeroNegativeVacuum`: the window algebra of Step 1 of Theorem 2.5 (`virasoro_two_level.tex`, `gt:2.5`)

The two-simple-zero designs `D_j = negDesign α K (K + j) η_j u₂` (first zero `p = z₁ - η_j`, second zero `q = u₂`,
modified pairs `k = 3, …, K + j + 2` at the Clark nodes `z_k` (`k ≤ K`) and the Airy zeros `a_k`, half-widths
`η_j · gapWKB k`) have windows `W_j` with `∫ W_j → ∫ f_K` as `η_j → 0`, `j → ∞`.  Proof: by the Airy quadrature
`∫ W_j = Σ_ν Re W_j(a_ν)/Ai'(a_ν)²`.  The `ν ≤ K` node values converge (Tannery for infinite products,
`NegativeVacuumLimit`) to those of the Airy product with zero widths, which is `f_K` (`windowF_eq_winC`), so they
sum to `∫ f_K`; the nodes `ν > K` contribute `O(η_j² + N_j^{-1/3})` by Lemma E (`ut:E`, `NegativeVacuumTail`).

* `twoZeroNegativeVacuum`: **`TwoZeroNegativeVacuum`**, unconditionally;
* `theorem_two_five_of_T2`: **Theorem 2.5**, conditional only on `TwoSimpleZeroTransfer prob` (`ut:T2`).

All results are proved unconditionally (`theorem_two_five_of_T2` from T2 alone).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

/-- The design `negDesign` is the approximating design of the ideal datum `clarkDatum α z₁ q 0 K` with first zero
`z₁ - η`. -/
lemma negDesign_eq_idealDesignP (α : ℝ) (K n : ℕ) (η q : ℝ) :
    negDesign α K n η q = IdealApprox.idealDesignP (clarkDatum α (clarkNode α 1) q 0 K) (clarkNode α 1 - η) n η := by
  unfold negDesign IdealApprox.idealDesignP IdealApprox.idealDesign
  congr

/-- `∫ f_K` is the integral of the real ideal window of `clarkDatum α z₁ u₂ 0 K`. -/
lemma windowInt_eq_win (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    windowInt α K u₂ = ∫ u, (clarkDatum α (clarkNode α 1) u₂ 0 K).win u := by
  have hF : (clarkDatum α (clarkNode α 1) u₂ 0 K).F = windowF α K u₂ := by
    rw [IdealApprox.F_eq_winC _ (by simp [clarkDatum]; omega), windowF_eq_winC α hK u₂]
    have hl : IdealApprox.idealLim (clarkDatum α (clarkNode α 1) u₂ 0 K).s K = siteLim α K := by
      funext k
      unfold siteLim IdealApprox.idealLim
      by_cases hk : 3 ≤ k
      · simp [clarkDatum, hk, show k ≠ 0 by omega]
      · simp [hk]
    simp only [clarkDatum]
    rw [show (fun k => if k = 0 then airyZero k else clarkNode α k) = (clarkDatum α (clarkNode α 1) u₂ 0 K).s from rfl, hl]
  unfold windowInt IdealDatum.win
  rw [hF]

/-- The designs `negDesign α K (K + j) η_j u₂` have `∫ W_2 → ∫ f_K`. -/
theorem tendsto_intWr (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) {L : ℕ} (hL : 4 ≤ L) :
    Tendsto (fun j : ℕ => ∫ u, (negDesign α K (K + j) ((j : ℝ) + L)⁻¹ u₂).Wr u) atTop
      (𝓝 (windowInt α K u₂)) := by
  have hL' : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hηpos : ∀ j : ℕ, 0 < ((j : ℝ) + L)⁻¹ := fun j => by positivity
  have hη1 : ∀ j : ℕ, ((j : ℝ) + L)⁻¹ ≤ 1 / 4 := fun j => by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hηt : Tendsto (fun j : ℕ => ((j : ℝ) + L)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => (j : ℝ) + L) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact h1.inv_tendsto_atTop
  have hnj : ∀ j : ℕ, K ≤ K + j := fun j => Nat.le_add_right K j
  have hnjt : Tendsto (fun j : ℕ => K + j) atTop atTop := tendsto_atTop_mono (fun j : ℕ => Nat.le_add_left j K) tendsto_id
  have hp : Tendsto (fun j : ℕ => clarkNode α 1 - ((j : ℝ) + L)⁻¹) atTop
      (𝓝 (clarkDatum α (clarkNode α 1) u₂ 0 K).p) := by
    simpa [clarkDatum] using (tendsto_const_nhds (x := clarkNode α 1)).sub hηt
  have h := IdealApprox.ideal_tendsto_intWr_gen (clarkDatum α (clarkNode α 1) u₂ 0 K)
    (by simp [clarkDatum]; omega) hnjt hnj hηpos hη1 hηt hp
  rw [windowInt_eq_win α hK u₂]
  refine h.congr fun j => ?_
  rw [negDesign_eq_idealDesignP]

/-- **`TwoZeroNegativeVacuum`** (the window algebra of Step 1 of the proof of `gt:2.5`): if `∫ f_K < 0` at the
second zero `u₂`, then some admissible two-simple-zero design with second zero `q = u₂` and first zero
`p < z₁(α)` has `∫ W_2 < 0`.  Proof: the designs `negDesign α K (K + j) η_j u₂` with `η_j → 0` have
`∫ W_2 → ∫ f_K` (`tendsto_intWr`). -/
theorem twoZeroNegativeVacuum : TwoZeroNegativeVacuum := by
  intro α hα K hK u₂ hint
  have hu₂ : u₂ ≤ windowOptimum α K := (windowOptimum_isGreatest hα hK).2 (show windowInt α K u₂ ≤ 0 from hint.le)
  have hq : u₂ < clarkNode α 2 := lt_of_le_of_lt hu₂ (windowOptimum_lt hα hK)
  have hz12 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) α
  obtain ⟨L, hL⟩ := exists_nat_gt (max 4 (1 / (clarkNode α 1 - clarkNode α 2)))
  have hL4 : (4 : ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLd : 1 / (clarkNode α 1 - clarkNode α 2) < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hlim := tendsto_intWr α hK u₂ (L := L) (by exact_mod_cast hL4.le)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hint)).exists
  have hLpos : (0 : ℝ) < (j : ℝ) + L := by positivity
  have hηpos : (0 : ℝ) < ((j : ℝ) + L)⁻¹ := by positivity
  have hηd : ((j : ℝ) + L)⁻¹ < clarkNode α 1 - clarkNode α 2 := by
    have hd : 0 < clarkNode α 1 - clarkNode α 2 := by linarith
    rw [inv_lt_comm₀ hLpos hd]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h2 : ((clarkNode α 1 - clarkNode α 2))⁻¹ < L := by simpa using hLd
    linarith
  refine ⟨K + j, by omega, negDesign α K (K + j) ((j : ℝ) + L)⁻¹ u₂,
    negDesign_adm α hηpos hq hηd, rfl, ?_, hj⟩
  show clarkNode α 1 - ((j : ℝ) + L)⁻¹ < clarkNode α 1
  linarith

/-- **Theorem 2.5** (`virasoro_two_level.tex`, `gt:2.5`), conditional only on the two-simple-zero transfer
`ut:T2`: for `A₁ < A_opt`, `δ > 0` and all large `c'` there is `g ∈ Ā` with `g(t₁) ≥ 0`, `g > 0` on `[t₂, ∞)`,
`g_vac > 0`, and no crossing measure is supported on `{t₁} ∪ [t₂, ∞)`. -/
theorem theorem_two_five_of_T2 (prob : FixedWeightProblem) (hT : TwoSimpleZeroTransfer prob) {A₁ δ : ℝ}
    (hA₁ : A₁ < Aopt) (hδ : 0 < δ) :
    ∀ᶠ c' : ℝ in atTop,
      (∃ g : ℝ → ℝ, TestClass prob (c' / 12) g ∧ 0 < prob.gVac (c' / 12) g ∧
        0 ≤ g (levelTime A₁ c') ∧ ∀ t, levelTime (A2star A₁ + δ) c' ≤ t → 0 < g t) ∧
      ∀ meas : AdmissibleCrossingMeasure prob (c' / 12),
        ¬ meas.ν ({levelTime A₁ c'} ∪ Ici (levelTime (A2star A₁ + δ) c'))ᶜ = 0 :=
  theorem_two_five prob hT twoZeroNegativeVacuum hA₁ hδ

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_intWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_intWr

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroNegativeVacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroNegativeVacuum

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_five_of_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_five_of_T2

end FormalResearch.ModularBootstrap.TwoLevel
