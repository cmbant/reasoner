module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.VagueLimit

/-!
# Measures carried by a node sequence, and the weight inequalities (`spectral_rigidity.tex`, proof of `sr:Sigma`)

The node-level argument of `sr:Sigma` (and of `gt:2.6`, `virasoro_two_level.tex`) for an *arbitrary* strictly
decreasing node sequence `z : ℕ → ℝ`, `z i → -∞` (the Airy zeros for `sr:Sigma`, the Clark nodes `z_n(α)` for `gt:2.6`):

* `node_integral_eq_tsum_atoms`: for `ν` carried by `{z i}` and `g` continuous with compact support,
  `∫ g dν = Σ_i g(z i) ν{z i}` (Airy case: `Upper.Rigidity.integral_eq_tsum_atoms`);
* `weight_le_one_of_ratio`: from the atomic inequality `Σ x_i τ_i ≤ Σ τ_i` for a window whose node values `τ_i`
  are `≥ 0` off one main node `j`, `x_j ≤ 1 + (Σ_{i ≠ j} τ_i)/τ_j`;
* `weight_ge_one_of_ratio`: if all `0 ≤ x_i ≤ 1`, `(1 - x_j)(-τ_j) ≤ Σ_i max(τ_i, 0)`;
* `measure_eq_of_atoms`: a measure carried by the nodes whose atoms have weight `w i` is `Σ w_i δ_{z_i}`.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.Upper.Rigidity

section Atoms

variable {z : ℕ → ℝ}

lemma node_finite_support_of_cs (hz : Tendsto z atTop atBot) {g : ℝ → ℝ} (hcs : HasCompactSupport g) :
    {i : ℕ | g (z i) ≠ 0}.Finite := by
  obtain ⟨B, hB⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have h1 : ∀ᶠ i in atTop, z i < -(|B| + 1) := hz.eventually (eventually_lt_atBot _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h1
  refine (Set.finite_lt_nat N).subset fun i hi => ?_
  show i < N
  by_contra hcon
  have hlt := hN i (not_lt.mp hcon)
  have hmem : z i ∈ tsupport g := subset_tsupport _ hi
  have := hB hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have := abs_le.mp this
  linarith [le_abs_self B, this.1]

lemma node_summable_of_cs (hz : Tendsto z atTop atBot) {g : ℝ → ℝ} (hcs : HasCompactSupport g)
    (w : ℕ → ℝ) : Summable (fun i => g (z i) * w i) := by
  refine summable_of_ne_finset_zero (s := (node_finite_support_of_cs hz hcs).toFinset) fun i hi => ?_
  have : g (z i) = 0 := by
    by_contra h0
    exact hi ((node_finite_support_of_cs hz hcs).mem_toFinset.mpr h0)
  simp [this]

lemma node_measurableSet_range : MeasurableSet (Set.range z) :=
  (Set.countable_range _).measurableSet

/-- A measure concentrated on the nodes is the sum of its atoms. -/
lemma node_measure_eq_sum_atoms (hinj : Function.Injective z) {ν : Measure ℝ}
    (h : ν (Set.range z)ᶜ = 0) :
    ν = Measure.sum fun i => ν {z i} • Measure.dirac (z i) := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  have h1 : ν s = ν (s ∩ Set.range z) := by
    have := measure_inter_add_sdiff s (node_measurableSet_range (z := z)) (μ := ν)
    have h0 : ν (s \ Set.range z) = 0 := measure_mono_null (fun x hx => hx.2) h
    rw [h0, add_zero] at this
    exact this.symm
  have h2 : s ∩ Set.range z = ⋃ i, (s ∩ {z i}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, i, rfl⟩; exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hx, rfl⟩; exact ⟨hx, i, rfl⟩
  rw [h1, h2, measure_iUnion]
  · congr 1
    ext i
    rw [smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    by_cases hi : z i ∈ s
    · have : s ∩ {z i} = {z i} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · exact fun hx => hx.2
        · rintro rfl; exact ⟨hi, rfl⟩
      simp [this, Set.indicator_of_mem hi]
    · have : s ∩ {z i} = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro hx rfl; exact hi hx
      simp [this, Set.indicator_of_notMem hi]
  · intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => hij (hinj ?_)
    exact hxi.2.symm.trans hxj.2
  · intro i
    exact hs.inter (measurableSet_singleton _)

/-- **Atomic integral**: for `ν` concentrated on the nodes and `g` continuous with compact support,
`∫ g dν = Σ_i g(z i) ν{z i}`. -/
lemma node_integral_eq_tsum_atoms (hinj : Function.Injective z)
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (h : ν (Set.range z)ᶜ = 0) {g : ℝ → ℝ}
    (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∫ u, g u ∂ν = ∑' i, g (z i) * (ν {z i}).toReal := by
  have hint : Integrable g (Measure.sum fun i => ν {z i} • Measure.dirac (z i)) := by
    rw [← node_measure_eq_sum_atoms hinj h]; exact integrable_of_cs hg hcs
  calc ∫ u, g u ∂ν
      = ∫ u, g u ∂(Measure.sum fun i => ν {z i} • Measure.dirac (z i)) :=
        congrArg (fun m => ∫ u, g u ∂m) (node_measure_eq_sum_atoms hinj h)
    _ = ∑' i, g (z i) * (ν {z i}).toReal := by
        rw [integral_sum_measure hint]
        refine tsum_congr fun i => ?_
        rw [integral_smul_measure, integral_dirac, smul_eq_mul, mul_comm]

/-- A measure carried by the nodes with atom `w i` at `z i` is `Σ_i w_i δ_{z_i}`. -/
lemma measure_eq_of_atoms (hinj : Function.Injective z) {ν : Measure ℝ} {w : ℕ → ℝ}
    (h : ν (Set.range z)ᶜ = 0) (hw : ∀ i, (ν {z i}).toReal = w i) [IsLocallyFiniteMeasure ν] :
    ν = Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (z i) := by
  rw [node_measure_eq_sum_atoms hinj h]
  congr 1
  ext1 i
  congr 1
  rw [← hw i, ENNReal.ofReal_toReal]
  exact (measure_singleton_lt_top (μ := ν)).ne

end Atoms

section Weights

/-- The atomic inequality gives an upper bound for the weight at the main node `j`:
if `Σ x_i τ_i ≤ Σ τ_i` with `x ≥ 0` and `τ_i ≥ 0` for `i ≠ j`, then
`(x_j - 1) τ_j ≤ Σ_{i ≠ j} τ_i`. -/
theorem weight_le_one_of_ratio {x τ : ℕ → ℝ} {V : ℝ} (hx : ∀ i, 0 ≤ x i) {j : ℕ}
    (hτ : HasSum τ V) (hxτ : Summable fun i => x i * τ i) (hle : ∑' i, x i * τ i ≤ V)
    (hnn : ∀ i, i ≠ j → 0 ≤ τ i) :
    (x j - 1) * τ j ≤ V - τ j := by
  have hd : Summable fun i => (x i - 1) * τ i :=
    (hxτ.sub hτ.summable).congr fun i => by ring
  have hsum : ∑' i, (x i - 1) * τ i ≤ 0 := by
    have : ∑' i, (x i - 1) * τ i = ∑' i, x i * τ i - V := by
      rw [← hτ.tsum_eq, ← hxτ.tsum_sub hτ.summable]
      exact tsum_congr fun i => by ring
    rw [this]; linarith
  have h1 := hd.tsum_eq_add_tsum_ite j
  have hrest : ∑' i, (if i = j then (0 : ℝ) else (x i - 1) * τ i) ≥ -(V - τ j) := by
    have hs : Summable fun i => if i = j then (0 : ℝ) else τ i := by
      have := hτ.summable.update j 0
      convert this using 1
      funext i; simp [Function.update_apply]
    have hs2 : Summable fun i => if i = j then (0 : ℝ) else (x i - 1) * τ i := by
      have := hd.update j 0
      convert this using 1
      funext i; simp [Function.update_apply]
    have hτrest : ∑' i, (if i = j then (0 : ℝ) else τ i) = V - τ j := by
      have := hτ.summable.tsum_eq_add_tsum_ite j
      rw [hτ.tsum_eq] at this
      linarith
    have hcmp : ∑' i, -(if i = j then (0 : ℝ) else τ i) ≤ ∑' i, (if i = j then (0 : ℝ) else (x i - 1) * τ i) := by
      refine Summable.tsum_le_tsum (fun i => ?_) hs.neg hs2
      by_cases hi : i = j
      · simp [hi]
      · simp only [hi, ite_false]
        have := hnn i hi
        have := hx i
        nlinarith
    rw [tsum_neg, hτrest] at hcmp
    exact hcmp
  linarith

/-- If all `x_i ≤ 1`, `x ≥ 0`, `Σ x_i τ_i ≤ Σ τ_i`, then
`(1 - x_j)(-τ_j) ≤ Σ_i max(τ_i, 0)`. -/
theorem weight_ge_one_of_ratio {x τ : ℕ → ℝ} {V : ℝ} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {j : ℕ}
    (hτ : HasSum τ V) (hxτ : Summable fun i => x i * τ i) (hle : ∑' i, x i * τ i ≤ V) :
    (1 - x j) * (-τ j) ≤ ∑' i, max (τ i) 0 := by
  have hpos : Summable fun i => max (τ i) 0 := by
    refine Summable.of_norm_bounded hτ.summable.abs fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    rcases le_total 0 (τ i) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]
    · rw [max_eq_right h]; exact abs_nonneg _
  have hd : Summable fun i => (1 - x i) * τ i :=
    (hτ.summable.sub hxτ).congr fun i => by ring
  have hsum : 0 ≤ ∑' i, (1 - x i) * τ i := by
    have : ∑' i, (1 - x i) * τ i = V - ∑' i, x i * τ i := by
      rw [← hτ.tsum_eq, ← hτ.summable.tsum_sub hxτ]
      exact tsum_congr fun i => by ring
    rw [this]; linarith
  have h1 := hd.tsum_eq_add_tsum_ite j
  have hs2 : Summable fun i => if i = j then (0 : ℝ) else (1 - x i) * τ i := by
    have := hd.update j 0
    convert this using 1
    funext i; simp [Function.update_apply]
  have hs3 : Summable fun i => if i = j then (0 : ℝ) else max (τ i) 0 := by
    have := hpos.update j 0
    convert this using 1
    funext i; simp [Function.update_apply]
  have hcmp : ∑' i, (if i = j then (0 : ℝ) else (1 - x i) * τ i) ≤
      ∑' i, (if i = j then (0 : ℝ) else max (τ i) 0) := by
    refine Summable.tsum_le_tsum (fun i => ?_) hs2 hs3
    by_cases hi : i = j
    · simp [hi]
    · simp only [hi, ite_false]
      have h0 := (hx i).1
      have h1 := (hx i).2
      rcases le_total 0 (τ i) with h | h
      · rw [max_eq_left h]; nlinarith
      · rw [max_eq_right h]; nlinarith
  have hle2 : ∑' i, (if i = j then (0 : ℝ) else max (τ i) 0) ≤ ∑' i, max (τ i) 0 := by
    refine Summable.tsum_le_tsum (fun i => ?_) hs3 hpos
    by_cases hi : i = j
    · simp [hi]
    · simp [hi]
  have hx1 := (hx j).2
  linarith

end Weights

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.weight_le_one_of_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_le_one_of_ratio

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.weight_ge_one_of_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms weight_ge_one_of_ratio

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.node_integral_eq_tsum_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms node_integral_eq_tsum_atoms

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.measure_eq_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms measure_eq_of_atoms

end FormalResearch.ModularBootstrap.TwoLevel
