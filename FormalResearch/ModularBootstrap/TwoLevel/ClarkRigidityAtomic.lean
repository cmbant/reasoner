module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityLimit

/-!
# The atomic inequality and concentration from ideal windows (`virasoro_two_level.tex`, `gt:2.6`)

An *ideal window* is a continuous `G : ℝ → ℝ` that satisfies the **ideal inequality**
`IdealIneq ν B G q V`: `∫ cutoff_{A,B} · G dν ≤ V` for every `A ≤ q - 2` (the limit of the basic inequality
`(I)` of `sr:Sigma`, `basic_inequality_of_support`, along design windows converging to `G`).

* `atomic_ineq_of_ideal` (Step 4, `sr:e2`): if `ν` is carried by a node sequence `z_i`, `G ≥ 0` on `(-∞, q]` and
  `IdealIneq ν B G q V`, then `Σ_i G(z_i) ν{z_i} ≤ V` (summably);
* `concentration_of_ideal` (Step 3): if ideal windows `G_K ≥ 0` have `V_K/ρ_K → 0` and `G_K ≥ m ρ_K` on a compact
  `K'` (eventually in `K`), then `ν(K') = 0`.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.Upper.Rigidity

/-- **Ideal inequality**: the limit of the basic inequality along design windows converging to the ideal window `G`. -/
def IdealIneq (ν : Measure ℝ) (B : ℝ) (G : ℝ → ℝ) (q V : ℝ) : Prop :=
  ∀ A : ℝ, A ≤ q - 2 → ∫ u, cutoff A B u * G u ∂ν ≤ V

/-- **Atomic inequality** (Step 4 of `sr:Sigma`) for a measure carried by the nodes. -/
theorem atomic_ineq_of_ideal {z : ℕ → ℝ} (hz : Tendsto z atTop atBot) (hanti : StrictAnti z)
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hconc : ν (Set.range z)ᶜ = 0) {B : ℝ}
    (hzB : ∀ i, z i ≤ B) {G : ℝ → ℝ} (hG : Continuous G) {q V : ℝ} (hnonneg : ∀ u, u ≤ q → 0 ≤ G u)
    (hI : IdealIneq ν B G q V) :
    Summable (fun i => G (z i) * (ν {z i}).toReal) ∧ ∑' i, G (z i) * (ν {z i}).toReal ≤ V := by
  have hinj : Function.Injective z := hanti.injective
  set t : ℕ → ℝ := fun i => G (z i) * (ν {z i}).toReal with ht
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ i, N₀ ≤ i → z i ≤ q :=
    eventually_atTop.1 (hz.eventually (eventually_le_atBot q))
  have ht_nonneg : ∀ i, N₀ ≤ i → 0 ≤ t i := fun i hi =>
    mul_nonneg (hnonneg _ (hN₀ i hi)) ENNReal.toReal_nonneg
  have hpartial : ∀ N, N₀ ≤ N → ∑ i ∈ Finset.range (N + 1), t i ≤ V := by
    intro N hN
    set A : ℝ := min (q - 2) (z N) with hA
    have hI' := hI A (min_le_left _ _)
    have hg : Continuous (fun u => cutoff A B u * G u) := (cutoff_continuous A B).mul hG
    have hcsg : HasCompactSupport (fun u => cutoff A B u * G u) := HasCompactSupport.mul_cutoff A B
    rw [node_integral_eq_tsum_atoms hinj hconc hg hcsg] at hI'
    have hsum : Summable (fun i => (cutoff A B (z i) * G (z i)) * (ν {z i}).toReal) :=
      node_summable_of_cs hz hcsg _
    have hterm : ∀ i, (cutoff A B (z i) * G (z i)) * (ν {z i}).toReal = cutoff A B (z i) * t i := by
      intro i; rw [ht]; ring
    simp_rw [hterm] at hsum hI'
    have hle : ∑ i ∈ Finset.range (N + 1), t i ≤ ∑' i, cutoff A B (z i) * t i := by
      calc ∑ i ∈ Finset.range (N + 1), t i
          = ∑ i ∈ Finset.range (N + 1), cutoff A B (z i) * t i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hzi : z N ≤ z i := by
              rcases hi'.eq_or_lt with h | h
              · rw [h]
              · exact (hanti h).le
            rw [cutoff_eq_one (A := A) (B := B), one_mul]
            · exact (min_le_right _ _).trans hzi
            · exact hzB i
        _ ≤ ∑' i, cutoff A B (z i) * t i := by
            refine Summable.sum_le_tsum _ (fun i hi => ?_) hsum
            have hi' : N₀ ≤ i := by
              have := Finset.mem_range.not.mp hi
              omega
            exact mul_nonneg (cutoff_nonneg _ _ _) (ht_nonneg i hi')
    exact hle.trans hI'
  have hpartial' : ∀ m, ∑ i ∈ Finset.range (N₀ + m), t i ≤ V := by
    intro m
    have h1 := hpartial (N₀ + m) (Nat.le_add_right _ _)
    have h2 : ∑ i ∈ Finset.range (N₀ + m), t i ≤ ∑ i ∈ Finset.range (N₀ + m + 1), t i := by
      rw [Finset.sum_range_succ]
      linarith [ht_nonneg (N₀ + m) (Nat.le_add_right _ _)]
    linarith
  have hsum : Summable t := by
    rw [← summable_nat_add_iff N₀]
    refine summable_of_sum_range_le (c := V - ∑ i ∈ Finset.range N₀, t i)
      (fun i => ht_nonneg _ (Nat.le_add_left _ _)) (fun m => ?_)
    have := hpartial' m
    rw [Finset.sum_range_add] at this
    have h3 : ∑ i ∈ Finset.range m, t (i + N₀) = ∑ i ∈ Finset.range m, t (N₀ + i) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    linarith
  refine ⟨hsum, ?_⟩
  refine le_of_tendsto hsum.hasSum.tendsto_sum_nat (eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hpartial' m

/-- **Concentration** (Step 3 of `sr:Sigma`): ideal windows `G_K ≥ 0` with `V_K/ρ_K → 0` that dominate `m ρ_K` on every
compact `K' ⊆ O` (`O ⊆ (-∞, z₂]` open) leave no mass on `O`, for a measure carried by `{z₁} ∪ (-∞, z₂]`. -/
theorem concentration_of_ideal {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {z₁ z₂ : ℝ} (hz : z₂ < z₁)
    (hae : ∀ᵐ u ∂ν, u = z₁ ∨ u ≤ z₂) {G : ℕ → ℝ → ℝ} (hGc : ∀ K, Continuous (G K))
    (hG1 : ∀ K, 0 ≤ G K z₁) (hG2 : ∀ K u, u ≤ z₂ → 0 ≤ G K u) {V ρ : ℕ → ℝ} (hρ : ∀ K, 0 < ρ K)
    (hI : ∀ K, IdealIneq ν (z₁ + 1) (G K) z₂ (V K))
    (hV : Tendsto (fun K => V K / ρ K) atTop (𝓝 0)) {O : Set ℝ} (hO : IsOpen O) (hOsub : O ⊆ Iic z₂)
    (hlow : ∀ K' : Set ℝ, IsCompact K' → K' ⊆ O →
      ∃ m : ℝ, 0 < m ∧ ∃ K₁ : ℕ, ∀ K, K₁ ≤ K → ∀ u ∈ K', m * ρ K ≤ G K u) :
    ν O = 0 := by
  rw [hO.measurableSet.measure_eq_iSup_isCompact]
  refine le_antisymm (iSup_le fun K' => iSup_le fun hK'O => iSup_le fun hK' => ?_) bot_le
  by_cases hne : K'.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  obtain ⟨m, hm, K₁, hK₁⟩ := hlow K' hK' hK'O
  obtain ⟨L, hL⟩ := hK'.bddBelow
  set A : ℝ := min (z₂ - 2) L with hA
  have hcut : ∀ u ∈ K', cutoff A (z₁ + 1) u = 1 := fun u hu =>
    cutoff_eq_one ((min_le_right _ _).trans (hL hu)) (by linarith [hOsub (hK'O hu), (show u ≤ z₂ from hOsub (hK'O hu))])
  have hbound : ∀ K, K₁ ≤ K → (ν K').toReal ≤ (1 / m) * (V K / ρ K) := by
    intro K hK
    have hf : Integrable (fun u => cutoff A (z₁ + 1) u * G K u) ν :=
      integrable_of_cs ((cutoff_continuous _ _).mul (hGc K)) (HasCompactSupport.mul_cutoff _ _)
    have hmain := const_mul_measure_le_integral hf hK'.measurableSet hK'.measure_lt_top
      (c := m * ρ K) (fun u hu => by rw [hcut u hu, one_mul]; exact hK₁ K hK u hu) (by
        filter_upwards [hae] with u hu _
        refine mul_nonneg (cutoff_nonneg _ _ _) ?_
        rcases hu with rfl | hu
        · exact hG1 K
        · exact hG2 K u hu)
    have hI' := hI K A (min_le_left _ _)
    have h1 : m * ρ K * (ν K').toReal ≤ V K := hmain.trans hI'
    have hρK := hρ K
    have h2 : (ν K').toReal * m ≤ V K / ρ K := by
      rw [le_div_iff₀ hρK]; nlinarith
    calc (ν K').toReal = (1 / m) * ((ν K').toReal * m) := by field_simp
      _ ≤ (1 / m) * (V K / ρ K) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hlim : Tendsto (fun K => (1 / m) * (V K / ρ K)) atTop (𝓝 0) := by
    simpa using hV.const_mul (1 / m)
  have h0 : (ν K').toReal ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨K₁, fun K hK => hbound K hK⟩)
  have hfin : ν K' ≠ ∞ := hK'.measure_lt_top.ne
  rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg) with h | h
  · rw [h]
  · exact absurd h hfin

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.atomic_ineq_of_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms atomic_ineq_of_ideal

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.concentration_of_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concentration_of_ideal

end FormalResearch.ModularBootstrap.TwoLevel
