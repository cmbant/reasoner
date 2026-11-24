module

public import FormalResearch.ModularBootstrap.TwoLevel.Exclusion
public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumTail

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

/-- The Airy quadrature of the window of a design in node form: `∫ W_2 = Σ_ν Re (W_2(a_ν)/Ai'(a_ν)²)`. -/
lemma intWr_hasSum {n : ℕ} (d : TwoZeroDesign n) :
    HasSum (fun m : ℕ => (nodeC d.p d.q d.site d.width (m + 1)).re) (∫ u, d.Wr u) := by
  have h := Complex.hasSum_re d.W_hasSum
  have hint : (∫ x : ℝ, d.W (x : ℂ)).re = ∫ u, d.Wr u := by
    have : ∫ x : ℝ, (d.W (x : ℂ)).re = (∫ x : ℝ, d.W (x : ℂ)).re := by
      simpa using integral_re d.W_integrable
    exact this.symm
  rw [hint] at h
  convert h using 2 with m
  have := winC_node d.p d.q d.site d.width (n := m + 1) (by omega)
  rw [← this]
  rfl

/-- Node decomposition of `∫ W_2` for the design `negDesign α K n η u₂`: nodes `ν ≤ K`, then the tail. -/
lemma intWr_decomp (α : ℝ) (K n : ℕ) (η u₂ : ℝ) :
    ∫ u, (negDesign α K n η u₂).Wr u =
      ∑ m ∈ Finset.range K, (nodeC (clarkNode α 1 - η) u₂ (siteSeq α K n) (widthSeq n η) (m + 1)).re +
        ∑' m : ℕ, (nodeC (clarkNode α 1 - η) u₂ (siteSeq α K n) (widthSeq n η) (K + 1 + m)).re := by
  have h := intWr_hasSum (negDesign α K n η u₂)
  rw [negDesign_site, negDesign_width] at h
  have h' : HasSum (fun m : ℕ => (nodeC (clarkNode α 1 - η) u₂ (siteSeq α K n) (widthSeq n η) (m + 1)).re)
      (∫ u, (negDesign α K n η u₂).Wr u) := h
  have hs := h'.summable.sum_add_tsum_nat_add K
  rw [h'.tsum_eq] at hs
  rw [← hs]
  congr 1
  refine tsum_congr fun m => ?_
  have : m + K + 1 = K + 1 + m := by omega
  simp only [this]

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
  have hfirst : Tendsto (fun j : ℕ => ∑ m ∈ Finset.range K, (nodeC (clarkNode α 1 - ((j : ℝ) + L)⁻¹) u₂
      (siteSeq α K (K + j)) (widthSeq (K + j) ((j : ℝ) + L)⁻¹) (m + 1)).re) atTop (𝓝 (windowInt α K u₂)) := by
    rw [windowInt_eq_sum α hK u₂]
    refine tendsto_finsetSum _ fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_nodeC α (nj := fun j : ℕ => K + j) (η := fun j : ℕ => ((j : ℝ) + L)⁻¹) (n := m + 1)
        (by omega) (by omega) u₂ hnj hnjt (fun j => (hηpos j).le) hη1 hηt)
  obtain ⟨M, hM0, N₀, hM⟩ := tail_sum_bound α hK u₂
  have hrate : Tendsto (fun j : ℕ => M * ((((j : ℝ) + L)⁻¹) ^ 2 + (((K + j) + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j : ℕ => (((K + j) + 2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_atTop_mono (fun j : ℕ => Nat.le_add_right (K + j) 2) hnjt)
    have h2 : Tendsto (fun j : ℕ => (((K + j) + 2 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1
    have h3 := ((hηt.pow 2).add h2).const_mul M
    simpa using h3
  have htail : Tendsto (fun j : ℕ => ∑' m : ℕ, (nodeC (clarkNode α 1 - ((j : ℝ) + L)⁻¹) u₂
      (siteSeq α K (K + j)) (widthSeq (K + j) ((j : ℝ) + L)⁻¹) (K + 1 + m)).re) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hrate
    filter_upwards [hnjt.eventually_ge_atTop N₀] with j hj
    rw [Real.norm_eq_abs]
    exact hM (K + j) (hnj j) (by omega) _ (hηpos j) (hη1 j)
  have := hfirst.add htail
  rw [add_zero] at this
  refine this.congr fun j => ?_
  exact (intWr_decomp α K (K + j) _ u₂).symm

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
