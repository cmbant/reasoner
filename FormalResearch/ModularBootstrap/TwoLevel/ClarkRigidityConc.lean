module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityRatio
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityFamilies

/-!
# Concentration on the Clark nodes (`virasoro_two_level.tex`, `gt:2.6`, Step 3)

For the windows `F_K` of `clarkDatum α z₁ z₂ 0 K` (zeros `z₁, z₂`, double zeros at `z_3, …, z_K`):

* `F_K ≥ 0` on `(-∞, z₂]`, `F_K(z₁) = 0`, and `∫ F_K = windowTail α K` (`integral_conc`: the node values are the terms
  `w_n(z₂ - z_n)` of `WindowOptimum`, nonzero only for `n > K`);
* `windowTail α K/windowWeight α K 2 → 0` (`windowTail_div_le`, the `K^{-1/15}` bound);
* on a compact subset of a gap `(z_{i+1}, z_i)`, `F_K ≥ m ρ_K` with `ρ_K = windowWeight α K 2` (`conc_hlow`, from
  `win_ratio_bounds`).

`concentration_nodes`: a measure carried by `{z₁} ∪ (-∞, z₂]` that satisfies the ideal inequalities for these windows is
carried by the Clark nodes.  All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

lemma clarkNode_eq_cNode (α : ℝ) {k : ℕ} (hk : 1 ≤ k) : clarkNode α k = cNode α (k - 1) := by
  unfold cNode; congr 1; omega

lemma not_node_of_gap (α : ℝ) {i : ℕ} {u : ℝ} (hu : u ∈ Ioo (cNode α (i + 1)) (cNode α i)) (j : ℕ) :
    u ≠ cNode α j := by
  rintro rfl
  rcases le_or_gt j i with h | h
  · have := (cNode_strictAnti α).antitone h; linarith [hu.2]
  · have := (cNode_strictAnti α).antitone (show i + 1 ≤ j by omega); linarith [hu.1]

/-- The node values of `F_K` for `p = z₁`, `m = 0`, `q = u₂` are the terms of the Clark summation of `WindowOptimum`. -/
lemma tau_clarkDatum_zero (α u₂ : ℝ) (K i : ℕ) :
    (clarkDatum α (clarkNode α 1) u₂ 0 K).tau α i = windowTerm α K u₂ (i + 1) := by
  unfold IdealDatum.tau windowTerm
  have : (clarkDatum α (clarkNode α 1) u₂ 0 K).Nr (cNode α i) = windowNr α K u₂ (clarkNode α (i + 1)) := by
    unfold IdealDatum.Nr windowNr
    have : ∏ k ∈ Finset.Icc 3 K, (cNode α i - (clarkDatum α (clarkNode α 1) u₂ 0 K).s k) ^ 2 =
        ∏ k ∈ Finset.Icc 3 K, (cNode α i - clarkNode α k) ^ 2 :=
      Finset.prod_congr rfl fun k hk => by
        rw [clarkDatum_s_of_ne α _ _ (by have := (Finset.mem_Icc.mp hk).1; omega)]
    simp only [clarkDatum, cNode] at this ⊢
    rw [this]
  rw [this]
  rfl

lemma integral_conc {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) :
    ∫ x, (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K).win x = windowTail α K := by
  have h1 := (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K).hasSum_tau hα (by simpa [clarkDatum] using (by omega : 2 ≤ K))
  have h2 := windowTail_hasSum hα hK
  have : (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K).tau α = fun n =>
      windowWeight α K (n + 1) * (clarkNode α 2 - clarkNode α (n + 1)) := by
    funext n
    rw [tau_clarkDatum_zero, windowTerm_eq α hK _ (by omega)]
  rw [this] at h1
  exact h1.unique h2

lemma tendsto_windowTail_div (α : ℝ) (hα : Real.sin α ≠ 0) :
    Tendsto (fun K : ℕ => windowTail α K / windowWeight α K 2) atTop (𝓝 0) := by
  obtain ⟨k0, h⟩ := exists_clark_nodeHyp α
  have hr : Tendsto (fun K : ℕ => (K : ℝ) ^ (-(1 / 15) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 15)).comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun K : ℕ => windowTailConst α k0 * (K : ℝ) ^ (-(1 / 15) : ℝ)) atTop (𝓝 0) := by
    simpa using hr.const_mul (windowTailConst α k0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with K hK
    have hρ := windowWeight_pos α hK (Or.inl rfl : 2 = 2 ∨ K < 2)
    refine div_nonneg ?_ hρ.le
    exact tsum_nonneg fun n => windowTail_term_nonneg α hK n
  · filter_upwards [eventually_ge_atTop (max k0 8)] with K hK
    exact windowTail_div_le hα h hK

lemma exists_airyZero_lt_neg (R : ℝ) : ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → airyZero k < -R := by
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (tendsto_airyNode.eventually (eventually_lt_atBot (-R)))
  refine ⟨i₀ + 1, fun k hk => ?_⟩
  have := hi₀ (k - 1) (by omega)
  unfold airyNode at this
  rwa [Nat.sub_add_cancel (by omega)] at this

lemma clark_Nr_pos (α p q : ℝ) (m K : ℕ) {u : ℝ} (hp : u < p) (hq : u < q)
    (hs : ∀ k ∈ Finset.Icc 3 K, u ≠ (clarkDatum α p q m K).s k) : 0 < (clarkDatum α p q m K).Nr u := by
  unfold IdealDatum.Nr
  refine mul_pos (mul_pos_of_neg_of_neg (sub_neg.2 hp) (sub_neg.2 hq)) (Finset.prod_pos fun k hk => ?_)
  have := sub_ne_zero.mpr (hs k hk)
  positivity

/-- **Lower bound on a gap**: on a compact subset of `(z_{i+1}, z_i)`, `i ≥ 1`, eventually `F_K ≥ m ρ_K`. -/
theorem conc_hlow {α : ℝ} {i : ℕ} (hi : 1 ≤ i) {K' : Set ℝ} (hK' : IsCompact K')
    (hsub : K' ⊆ Ioo (cNode α (i + 1)) (cNode α i)) :
    ∃ m : ℝ, 0 < m ∧ ∃ K₁ : ℕ, ∀ K, K₁ ≤ K → ∀ u ∈ K',
      m * windowWeight α K 2 ≤ (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K).win u := by
  obtain ⟨k0, h⟩ := exists_clark_nodeHyp α
  set R : ℝ := |cNode α (i + 1)| + |cNode α i| with hR
  have hRu : ∀ u ∈ K', |u| ≤ R := fun u hu => by
    have h1 := hsub hu
    rw [abs_le]
    constructor
    · have := neg_abs_le (cNode α (i + 1)); have := abs_nonneg (cNode α i); linarith [h1.1]
    · have := le_abs_self (cNode α i); have := abs_nonneg (cNode α (i + 1)); linarith [h1.2]
  obtain ⟨k₂, hk₂, hbd⟩ := win_ratio_bounds α (clarkNode α 1) (clarkNode α 2) 0 h R
  obtain ⟨k₁, hk₁⟩ := exists_airyZero_lt_neg R
  have hk₀3 : 3 ≤ max k₂ k₁ := by have := (le_max_right 0 3).trans hk₂; omega
  have hz2 : cNode α i ≤ clarkNode α 2 := by
    have := (cNode_strictAnti α).antitone hi
    simpa [cNode] using this
  have hz2neg : clarkNode α 2 < 0 := clarkNode_two_lt_zero α
  have hz1 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) α
  set δ0 := clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 (max k₂ k₁) with hδ0
  have hairy : ∀ u ∈ K', ∀ k, k₁ ≤ k → u ≠ airyZero k := by
    intro u hu k hk heq
    have h' := hRu u hu
    have := neg_abs_le u
    have := hk₁ k hk
    rw [← heq] at this
    linarith
  have hpos : ∀ u ∈ K', 0 < δ0.win u := by
    intro u hu
    have hg := hsub hu
    have hu2 : u < clarkNode α 2 := lt_of_lt_of_le hg.2 hz2
    refine δ0.win_pos (clark_Nr_pos α _ _ 0 _ (hu2.trans hz1) hu2 fun k hk => ?_) ?_
    · have hk3 := (Finset.mem_Icc.mp hk).1
      rw [clarkDatum_s_of_ne α _ _ (by omega), clarkNode_eq_cNode α (by omega)]
      exact not_node_of_gap α hg _
    · intro hA
      obtain ⟨j, hj⟩ := exists_airyNode_eq hA (by linarith)
      refine ⟨j + 1, Finset.mem_Icc.2 ⟨by omega, ?_⟩, hj⟩
      show j + 1 ≤ max k₂ k₁
      by_contra hcon
      exact hairy u hu (j + 1) (by omega) hj
  rcases K'.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, one_pos, 0, fun K _ u hu => by simp [hemp] at hu⟩
  obtain ⟨u₀, hu₀, hmin⟩ := hK'.exists_isMinOn hne
    (f := fun u => δ0.win u / windowWeight α (max k₂ k₁) 2)
    ((δ0.continuous_win.div_const _).continuousOn)
  have hρ0 : 0 < windowWeight α (max k₂ k₁) 2 := windowWeight_pos α hk₀3 (Or.inl rfl)
  have hμ : 0 < δ0.win u₀ / windowWeight α (max k₂ k₁) 2 := div_pos (hpos u₀ hu₀) hρ0
  refine ⟨(δ0.win u₀ / windowWeight α (max k₂ k₁) 2) / 4, by positivity, max k₂ k₁, fun K hK u hu => ?_⟩
  have hne' : ∀ k ∈ Finset.Ioc (max k₂ k₁) K, u ≠ airyZero k := fun k hk =>
    hairy u hu k (by have := (Finset.mem_Ioc.1 hk).1; have := le_max_right k₂ k₁; omega)
  obtain ⟨hlo, _⟩ := hbd (max k₂ k₁) (le_max_left _ _) K hK u (hRu u hu) hne' (hpos u hu).le
  have hρK : 0 < windowWeight α K 2 := windowWeight_pos α (hk₀3.trans hK) (Or.inl rfl)
  have h1 : δ0.win u₀ / windowWeight α (max k₂ k₁) 2 ≤ δ0.win u / windowWeight α (max k₂ k₁) 2 :=
    hmin hu
  have : (δ0.win u₀ / windowWeight α (max k₂ k₁) 2) / 4 ≤
      (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K).win u / windowWeight α K 2 := by linarith
  rwa [le_div_iff₀ hρK] at this

/-- **Concentration on the Clark nodes** (Step 3): a measure carried by `{z₁} ∪ (-∞, z₂]` satisfying the ideal
inequalities for the windows `F_K` (`K ≥ 3`) is carried by the nodes. -/
theorem concentration_nodes {α : ℝ} (hα : Real.sin α ≠ 0) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hae : ∀ᵐ u ∂ν, u = clarkNode α 1 ∨ u ≤ clarkNode α 2)
    (hI : ∀ K, 3 ≤ K → IdealIneq ν (clarkNode α 1 + 1)
      (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 K).win (clarkNode α 2) (windowTail α K)) :
    ν (Set.range (cNode α))ᶜ = 0 := by
  have hz1 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) α
  have hgap : ∀ i, 1 ≤ i → ν (Ioo (cNode α (i + 1)) (cNode α i)) = 0 := by
    intro i hi
    have hz2 : cNode α i ≤ clarkNode α 2 := by
      have := (cNode_strictAnti α).antitone hi
      simpa [cNode] using this
    refine concentration_of_ideal (z₁ := clarkNode α 1) (z₂ := clarkNode α 2) hz1 hae
      (G := fun K => (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 (K + 3)).win)
      (fun K => IdealDatum.continuous_win _) ?_ ?_
      (V := fun K => windowTail α (K + 3)) (ρ := fun K => windowWeight α (K + 3) 2)
      (fun K => windowWeight_pos α (by omega) (Or.inl rfl)) (fun K => hI (K + 3) (by omega)) ?_
      (O := Ioo (cNode α (i + 1)) (cNode α i)) isOpen_Ioo (fun u hu => (hu.2.trans_le hz2).le) ?_
    · intro K
      have h := (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 (K + 3)).win_spec (clarkNode α 1)
      have hD := windowDr_node_ne α (K + 3) (n := 1) le_rfl
      have hNr : (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 (K + 3)).Nr (clarkNode α 1) = 0 := by
        unfold IdealDatum.Nr; simp [clarkDatum]
      rw [hNr, mul_zero] at h
      have : (clarkDatum α (clarkNode α 1) (clarkNode α 2) 0 (K + 3)).win (clarkNode α 1) = 0 := by
        rcases mul_eq_zero.1 h with h0 | h0
        · exact h0
        · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.1 h0) hD
      rw [this]
    · intro K u hu
      exact IdealDatum.win_nonneg_of_le _ hu hz1
    · exact (tendsto_windowTail_div α hα).comp (tendsto_add_atTop_nat 3)
    · intro K' hK' hsub
      obtain ⟨m, hm, K₁, hK₁⟩ := conc_hlow hi hK' hsub
      exact ⟨m, hm, K₁, fun K hK u hu => hK₁ (K + 3) (by omega) u hu⟩
  have hrange : (Set.range (cNode α))ᶜ ⊆ {u | ¬(u = clarkNode α 1 ∨ u ≤ clarkNode α 2)} ∪
      ⋃ i : ℕ, Ioo (cNode α (i + 1 + 1)) (cNode α (i + 1)) := by
    intro u hu
    by_cases hc : u = clarkNode α 1 ∨ u ≤ clarkNode α 2
    · right
      have hu' : ∀ j, u ≠ cNode α j := fun j h => hu ⟨j, h.symm⟩
      have hlt : u < cNode α 1 := by
        rcases hc with h | h
        · exact absurd h (hu' 0)
        · exact lt_of_le_of_ne h (hu' 1)
      have hex : ∃ j, cNode α j < u := by
        obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_cNode α).eventually (eventually_lt_atBot u))
        exact ⟨N, hN N le_rfl⟩
      classical
      set j := Nat.find hex with hjdef
      have hj : cNode α j < u := Nat.find_spec hex
      have hj2 : 2 ≤ j := by
        by_contra hcon
        have : cNode α 1 ≤ cNode α j := (cNode_strictAnti α).antitone (by omega)
        linarith
      have hmin : ¬ cNode α (j - 1) < u := Nat.find_min hex (by omega)
      have hge : u ≤ cNode α (j - 1) := not_lt.1 hmin
      have hgt : u < cNode α (j - 1) := lt_of_le_of_ne hge (hu' (j - 1))
      refine mem_iUnion.2 ⟨j - 2, ?_⟩
      have e1 : j - 2 + 1 + 1 = j := by omega
      have e2 : j - 2 + 1 = j - 1 := by omega
      rw [e1, e2]
      exact ⟨hj, hgt⟩
    · left; exact hc
  exact measure_mono_null hrange (measure_union_null (ae_iff.1 hae)
    (measure_iUnion_null fun i => hgap (i + 1) (by omega)))

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.integral_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integral_conc

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.conc_hlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conc_hlow

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.concentration_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concentration_nodes

end FormalResearch.ModularBootstrap.TwoLevel
