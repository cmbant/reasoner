module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityConc

/-!
# Upper bounds for the node weights (`virasoro_two_level.tex`, `gt:2.6`, Step 5)

For the window family `F_K` of `clarkDatum α p q m K` the node values `τ^K_i = F_K(z_{i+1})/K_{i+1}` satisfy:

* `τ^K_i = 0` for `i < K` except at the single index `n - 1`, where `F_K(z_n) > 0`;
* for `i ≥ K`, `0 ≤ τ^K_i ≤ 2 w_{i+1}(z₂ - z_{i+1})` (the terms of `windowTail`), because
  `N_δ(z)/N_{std}(z) = gfac(z) → 1` as `z → -∞`;
* `τ^K_{n-1} ≥ c ρ_K` for a constant `c > 0` (`win_ratio_bounds`).

Hence `(V_K - τ^K_{n-1})/τ^K_{n-1} ≤ (2/c) windowTail α K/ρ_K → 0` (`up_family`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

lemma tendsto_ratio_atBot (c d : ℝ) : Tendsto (fun z : ℝ => (z - c) / (z - d)) atBot (𝓝 1) := by
  have h1 : Tendsto (fun z : ℝ => z - d) atBot atBot := by
    simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-d) tendsto_id
  have h2 : Tendsto (fun z : ℝ => (z - d)⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero.comp h1
  have h3 : Tendsto (fun z : ℝ => 1 + (d - c) * (z - d)⁻¹) atBot (𝓝 1) := by
    simpa using tendsto_const_nhds.add (h2.const_mul (d - c))
  refine h3.congr' ?_
  filter_upwards [eventually_lt_atBot d] with z hz
  have : z - d ≠ 0 := by linarith
  field_simp
  ring

/-- `gfac = N_δ/N_std`, the ratio of the numerators of `δ = (p, q, m)` and of the standard window. -/
noncomputable def gfac (α p q : ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  (z - p) / (z - clarkNode α 1) * ((z - q) / (z - clarkNode α 2)) *
    (if 3 ≤ m then ((z - airyZero m) / (z - clarkNode α m)) ^ 2 else 1)

lemma tendsto_gfac (α p q : ℝ) (m : ℕ) : Tendsto (gfac α p q m) atBot (𝓝 1) := by
  unfold gfac
  have h1 := tendsto_ratio_atBot p (clarkNode α 1)
  have h2 := tendsto_ratio_atBot q (clarkNode α 2)
  have h3 : Tendsto (fun z : ℝ => if 3 ≤ m then ((z - airyZero m) / (z - clarkNode α m)) ^ 2 else 1)
      atBot (𝓝 1) := by
    by_cases hm3 : 3 ≤ m
    · simpa [hm3] using (tendsto_ratio_atBot (airyZero m) (clarkNode α m)).pow 2
    · simp [hm3]
  simpa using (h1.mul h2).mul h3

lemma eventually_gfac_le (α p q : ℝ) (m : ℕ) : ∀ᶠ z in atBot, 0 ≤ gfac α p q m z ∧ gfac α p q m z ≤ 2 := by
  have h := tendsto_gfac α p q m
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    h.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with z h1 h2
  exact ⟨h1.le, h2.le⟩

lemma Nr_eq_gfac_mul (α p q : ℝ) (m : ℕ) {K : ℕ} (hK : max m 3 ≤ K) {z : ℝ}
    (hz : ∀ k ∈ Finset.Icc 1 K, z ≠ clarkNode α k) :
    (clarkDatum α p q m K).Nr z = gfac α p q m z * windowNr α K (clarkNode α 2) z := by
  have hmK : m ≤ K := (le_max_left _ _).trans hK
  have hz1 : z - clarkNode α 1 ≠ 0 := sub_ne_zero.mpr (hz 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩))
  have hz2 : z - clarkNode α 2 ≠ 0 := sub_ne_zero.mpr (hz 2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
  have hterm : ∀ k ∈ Finset.Icc 3 K, (z - (clarkDatum α p q m K).s k) ^ 2 =
      (z - clarkNode α k) ^ 2 * (if k = m then ((z - airyZero m) / (z - clarkNode α m)) ^ 2 else 1) := by
    intro k hk
    have hk3 := (Finset.mem_Icc.mp hk)
    by_cases hkm : k = m
    · subst hkm
      have hzk : z - clarkNode α k ≠ 0 :=
        sub_ne_zero.mpr (hz k (Finset.mem_Icc.2 ⟨by omega, hk3.2⟩))
      rw [clarkDatum_s_self]
      simp only [↓reduceIte]
      field_simp
    · rw [clarkDatum_s_of_ne α p q hkm]
      simp [hkm]
  have hprod : ∏ k ∈ Finset.Icc 3 K, (z - (clarkDatum α p q m K).s k) ^ 2 =
      (∏ k ∈ Finset.Icc 3 K, (z - clarkNode α k) ^ 2) *
        (if 3 ≤ m then ((z - airyZero m) / (z - clarkNode α m)) ^ 2 else 1) := by
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    by_cases hm3 : 3 ≤ m
    · simp [Finset.mem_Icc, hm3, hmK]
    · simp [Finset.mem_Icc, hm3]
  unfold IdealDatum.Nr windowNr gfac
  simp only [clarkDatum]
  have hprod' : ∏ k ∈ Finset.Icc 3 K, (z - (if k = m then airyZero k else clarkNode α k)) ^ 2 =
      (∏ k ∈ Finset.Icc 3 K, (z - clarkNode α k) ^ 2) *
        (if 3 ≤ m then ((z - airyZero m) / (z - clarkNode α m)) ^ 2 else 1) := hprod
  rw [hprod']
  field_simp

lemma tau_tail_eq (α p q : ℝ) (m : ℕ) {K : ℕ} (hK : max m 3 ≤ K) {i : ℕ} (hi : K ≤ i) :
    (clarkDatum α p q m K).tau α i =
      gfac α p q m (cNode α i) * windowTerm α K (clarkNode α 2) (i + 1) := by
  unfold IdealDatum.tau windowTerm
  have hz : ∀ k ∈ Finset.Icc 1 K, cNode α i ≠ clarkNode α k := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk)
    exact (clarkNode_lt_of_lt (n := k) (m := i + 1) hk1.1 (by omega) α).ne
  rw [Nr_eq_gfac_mul α p q m hK hz]
  simp only [clarkDatum, cNode]
  ring

lemma clarkNode_inj {α : ℝ} {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (h : clarkNode α k = clarkNode α n) :
    k = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have := clarkNode_lt_of_lt (n := k) (m := n) hk hl α; linarith
  · have := clarkNode_lt_of_lt (n := n) (m := k) hn hl α; linarith

/-- The hypotheses on `(m, n)`: the site at `k ≠ n` is the node `z_k`, and the site at `n` (if `n ≥ 3`) is `a_n`. -/
def UpIdx (m n : ℕ) : Prop := (n ≤ 2 ∧ m = 0) ∨ (3 ≤ n ∧ m = n)

lemma UpIdx.site_ne {m n : ℕ} (h : UpIdx m n) (α p q : ℝ) {K k : ℕ} (hn : 1 ≤ n) (hk : 3 ≤ k) :
    clarkNode α n ≠ (clarkDatum α p q m K).s k := by
  by_cases hkm : k = m
  · subst hkm
    rw [clarkDatum_s_self]
    exact clarkNode_ne_airyZero α hn (by omega)
  · rw [clarkDatum_s_of_ne α p q hkm]
    intro heq
    have := clarkNode_inj hn (by omega) heq
    subst this
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · exact hkm h2.symm

lemma tau_zero_of_lt (α p q : ℝ) {m n : ℕ} (hm : UpIdx m n)
    (hzero : ∀ n', 1 ≤ n' → n' ≤ 2 → n' ≠ n → clarkNode α n' = p ∨ clarkNode α n' = q)
    {K i : ℕ} (hiK : i < K) (hi : i ≠ n - 1) : (clarkDatum α p q m K).tau α i = 0 := by
  have hNr : (clarkDatum α p q m K).Nr (cNode α i) = 0 := by
    show (cNode α i - p) * (cNode α i - q) *
      ∏ k ∈ Finset.Icc 3 K, (cNode α i - (clarkDatum α p q m K).s k) ^ 2 = 0
    by_cases h3 : i + 1 ≤ 2
    · rcases hzero (i + 1) (by omega) h3 (by omega) with h | h
      · have : cNode α i - p = 0 := by unfold cNode; linarith
        rw [this]; simp
      · have : cNode α i - q = 0 := by unfold cNode; linarith
        rw [this]; simp
    · have hmem : i + 1 ∈ Finset.Icc 3 K := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hs : (clarkDatum α p q m K).s (i + 1) = cNode α i := by
        have hne : i + 1 ≠ m := by
          rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        rw [clarkDatum_s_of_ne α p q hne]; rfl
      rw [Finset.prod_eq_zero hmem (by rw [hs]; simp), mul_zero]
  unfold IdealDatum.tau
  rw [hNr, zero_div]

lemma tau_tail_bounds (α p q : ℝ) (m : ℕ) : ∃ K₂ : ℕ, ∀ K, max m 3 ≤ K → K₂ ≤ K → ∀ i, K ≤ i →
    0 ≤ (clarkDatum α p q m K).tau α i ∧
      (clarkDatum α p q m K).tau α i ≤ 2 * windowTerm α K (clarkNode α 2) (i + 1) := by
  obtain ⟨Z, hZ⟩ := eventually_atBot.1 (eventually_gfac_le α p q m)
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 ((tendsto_cNode α).eventually (eventually_le_atBot Z))
  refine ⟨K₂, fun K hK hK2 i hi => ?_⟩
  have hK3 : 3 ≤ K := (le_max_right _ _).trans hK
  have hg := hZ _ (hK₂ i (by omega))
  have hwt : 0 ≤ windowTerm α K (clarkNode α 2) (i + 1) := by
    rw [windowTerm_eq α hK3 _ (by omega)]
    have := windowTail_term_nonneg α hK3 i
    simpa using this
  rw [tau_tail_eq α p q m hK hi]
  exact ⟨mul_nonneg hg.1 hwt, by nlinarith [hg.2, hg.1]⟩

lemma tau_main_lower (α p q : ℝ) {m n : ℕ} (hn : 1 ≤ n) (hm : UpIdx m n)
    (hpos : 0 < (clarkNode α n - p) * (clarkNode α n - q)) :
    ∃ c : ℝ, 0 < c ∧ ∃ K₁ : ℕ, max m 3 ≤ K₁ ∧ ∀ K, K₁ ≤ K →
      c * windowWeight α K 2 ≤ (clarkDatum α p q m K).tau α (n - 1) := by
  obtain ⟨k0, h⟩ := exists_clark_nodeHyp α
  obtain ⟨k₂, hk₂, hbd⟩ := win_ratio_bounds α p q m h |clarkNode α n|
  have hk₂3 : 3 ≤ k₂ := (le_max_right _ _).trans hk₂
  have hNr : 0 < (clarkDatum α p q m k₂).Nr (clarkNode α n) := by
    unfold IdealDatum.Nr
    refine mul_pos hpos (Finset.prod_pos fun k hk => ?_)
    have := sub_ne_zero.mpr (hm.site_ne α p q (K := k₂) hn (Finset.mem_Icc.mp hk).1)
    positivity
  have hwin : 0 < (clarkDatum α p q m k₂).win (clarkNode α n) :=
    (clarkDatum α p q m k₂).win_pos hNr fun h0 => absurd h0 (clarkNode_airyAi_ne hn)
  have hρ0 : 0 < windowWeight α k₂ 2 := windowWeight_pos α hk₂3 (Or.inl rfl)
  have hcW := cWeight_pos α (n - 1)
  refine ⟨(1 / 4) * ((clarkDatum α p q m k₂).win (clarkNode α n) / windowWeight α k₂ 2) *
    cWeight α (n - 1), by positivity, k₂, hk₂, fun K hK => ?_⟩
  have hne : ∀ k ∈ Finset.Ioc k₂ K, clarkNode α n ≠ airyZero k := fun k hk =>
    clarkNode_ne_airyZero α hn (by have := (Finset.mem_Ioc.1 hk).1; omega)
  obtain ⟨hlo, _⟩ := hbd k₂ le_rfl K hK (clarkNode α n) le_rfl hne hwin.le
  have hρK : 0 < windowWeight α K 2 := windowWeight_pos α (hk₂3.trans hK) (Or.inl rfl)
  have h1 : (1 / 4) * ((clarkDatum α p q m k₂).win (clarkNode α n) / windowWeight α k₂ 2) *
      windowWeight α K 2 ≤ (clarkDatum α p q m K).win (clarkNode α n) := by
    rwa [le_div_iff₀ hρK] at hlo
  rw [← IdealDatum.win_cNode_mul_cWeight, ← clarkNode_eq_cNode α hn]
  have e : (1 / 4 * ((clarkDatum α p q m k₂).win (clarkNode α n) / windowWeight α k₂ 2) *
      cWeight α (n - 1)) * windowWeight α K 2 =
      ((1 / 4) * ((clarkDatum α p q m k₂).win (clarkNode α n) / windowWeight α k₂ 2) *
        windowWeight α K 2) * cWeight α (n - 1) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 hcW.le

theorem up_family {α : ℝ} (hα : Real.sin α ≠ 0) {p q : ℝ} {m n : ℕ} (hn : 1 ≤ n) (hm : UpIdx m n)
    (hzero : ∀ n', 1 ≤ n' → n' ≤ 2 → n' ≠ n → clarkNode α n' = p ∨ clarkNode α n' = q)
    (hpos : 0 < (clarkNode α n - p) * (clarkNode α n - q)) :
    (∀ᶠ K in atTop, 0 < (clarkDatum α p q m K).tau α (n - 1)) ∧
    (∀ᶠ K in atTop, ∀ i, i ≠ n - 1 → 0 ≤ (clarkDatum α p q m K).tau α i) ∧
    Tendsto (fun K : ℕ => ((∫ x, (clarkDatum α p q m K).win x) - (clarkDatum α p q m K).tau α (n - 1)) /
      (clarkDatum α p q m K).tau α (n - 1)) atTop (𝓝 0) := by
  obtain ⟨c, hc, K₁, hK₁, hlow⟩ := tau_main_lower α p q hn hm hpos
  obtain ⟨K₂, htail⟩ := tau_tail_bounds α p q m
  set K₀ := max (max K₁ K₂) n with hK₀
  have hall : ∀ K, K₀ ≤ K → max m 3 ≤ K ∧ K₂ ≤ K ∧ n ≤ K ∧ K₁ ≤ K := fun K hK =>
    ⟨hK₁.trans ((le_max_left _ _).trans ((le_max_left _ _).trans hK)),
      (le_max_right _ _).trans ((le_max_left _ _).trans hK), (le_max_right _ _).trans hK,
      (le_max_left _ _).trans ((le_max_left _ _).trans hK)⟩
  have hρpos : ∀ K, 3 ≤ K → 0 < windowWeight α K 2 := fun K hK => windowWeight_pos α hK (Or.inl rfl)
  have hτpos : ∀ K, K₀ ≤ K → 0 < (clarkDatum α p q m K).tau α (n - 1) := fun K hK => by
    obtain ⟨h1, _, _, h4⟩ := hall K hK
    have := hlow K h4
    have h3 : 3 ≤ K := (le_max_right _ _).trans h1
    have := hρpos K h3
    nlinarith [hlow K h4]
  have hnn : ∀ K, K₀ ≤ K → ∀ i, i ≠ n - 1 → 0 ≤ (clarkDatum α p q m K).tau α i := by
    intro K hK i hi
    obtain ⟨h1, h2, _, _⟩ := hall K hK
    by_cases hiK : i < K
    · rw [tau_zero_of_lt α p q hm hzero hiK hi]
    · exact (htail K h1 h2 i (not_lt.1 hiK)).1
  refine ⟨eventually_atTop.2 ⟨K₀, hτpos⟩, eventually_atTop.2 ⟨K₀, hnn⟩, ?_⟩
  -- the bound `0 ≤ (V - τ)/τ ≤ (2/c) windowTail/ρ`
  have hbound : ∀ K, K₀ ≤ K →
      0 ≤ ((∫ x, (clarkDatum α p q m K).win x) - (clarkDatum α p q m K).tau α (n - 1)) /
        (clarkDatum α p q m K).tau α (n - 1) ∧
      ((∫ x, (clarkDatum α p q m K).win x) - (clarkDatum α p q m K).tau α (n - 1)) /
        (clarkDatum α p q m K).tau α (n - 1) ≤ (2 / c) * (windowTail α K / windowWeight α K 2) := by
    intro K hK
    obtain ⟨h1, h2, h3, h4⟩ := hall K hK
    have hK3 : 3 ≤ K := (le_max_right _ _).trans h1
    have hτp := hτpos K hK
    have hV := (clarkDatum α p q m K).hasSum_tau hα (show 2 ≤ (clarkDatum α p q m K).K by
      show 2 ≤ K; omega)
    have hsum : ∑ i ∈ Finset.range K, (clarkDatum α p q m K).tau α i =
        (clarkDatum α p q m K).tau α (n - 1) := by
      rw [Finset.sum_eq_single (n - 1)]
      · intro i hi hne
        exact tau_zero_of_lt α p q hm hzero (Finset.mem_range.1 hi) hne
      · intro hn'; exact absurd (Finset.mem_range.2 (by omega)) hn'
    have hshift := (hasSum_nat_add_iff' K).2 hV
    rw [hsum] at hshift
    have hT := windowTail_hasSum hα hK3
    have hT' := (hasSum_nat_add_iff' K).2 hT
    rw [Finset.sum_eq_zero (fun i hi => windowTail_term_zero α (Finset.mem_range.mp hi)), sub_zero] at hT'
    have hle : (∫ x, (clarkDatum α p q m K).win x) - (clarkDatum α p q m K).tau α (n - 1) ≤
        2 * windowTail α K := by
      refine hasSum_le (fun i => ?_) hshift (hT'.mul_left 2)
      have := (htail K h1 h2 (i + K) (by omega)).2
      rw [windowTerm_eq α hK3 _ (by omega)] at this
      have e : i + K + 1 = K + i + 1 := by omega
      simpa [e, add_comm] using this
    have hge : 0 ≤ (∫ x, (clarkDatum α p q m K).win x) - (clarkDatum α p q m K).tau α (n - 1) :=
      hshift.nonneg fun i => (htail K h1 h2 (i + K) (by omega)).1
    have hlowK := hlow K h4
    have hρ := hρpos K hK3
    have hcρ : 0 < c * windowWeight α K 2 := by positivity
    constructor
    · exact div_nonneg hge hτp.le
    · calc _ ≤ (2 * windowTail α K) / (c * windowWeight α K 2) :=
            div_le_div₀ (by linarith) hle hcρ hlowK
        _ = (2 / c) * (windowTail α K / windowWeight α K 2) := by field_simp
  have hup : Tendsto (fun K : ℕ => (2 / c) * (windowTail α K / windowWeight α K 2)) atTop (𝓝 0) := by
    simpa using (tendsto_windowTail_div α hα).const_mul (2 / c)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (eventually_atTop.2 ⟨K₀, fun K hK => (hbound K hK).1⟩)
    (eventually_atTop.2 ⟨K₀, fun K hK => (hbound K hK).2⟩)

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.up_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms up_family

end FormalResearch.ModularBootstrap.TwoLevel
