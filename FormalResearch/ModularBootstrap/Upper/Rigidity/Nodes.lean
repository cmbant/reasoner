module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.VagueLimit
public import FormalResearch.Special.AiryReal
public import FormalResearch.Special.AiryZeroOrder
public import FormalResearch.Special.AiryCftZeros
public import FormalResearch.Special.AiryClarkLabel

/-!
# Airy nodes and the quadrature measure `μ_A`

`airyNode i = a_{i+1}` (the `(i+1)`-st zero of `Ai`, so `airyNode 0 = a₁`), the weights
`1 / Ai'(a_n)²`, and the Airy quadrature measure
`μ_A = Σ_n δ_{a_n} / Ai'(a_n)²` of `spectral_rigidity.tex` (§1), as a `Measure ℝ`
(`airyMeasure`).  Also the atomic decomposition of a measure concentrated on the zeros of `Ai`:
`∫ g dν = Σ_i g(a_i) ν{a_i}` for continuous compactly supported `g`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

/-- The `(i+1)`-st zero of `Ai`: `airyNode i = a_{i+1}`, so `airyNode 0 = a₁ = airyZero 1`. -/
noncomputable def airyNode (i : ℕ) : ℝ := airyZero (i + 1)

/-- The quadrature weight `1 / Ai'(a_{i+1})²`. -/
noncomputable def airyNodeWeight (i : ℕ) : ℝ := 1 / (airyAi' (airyNode i)) ^ 2

lemma airyNode_zero : airyNode 0 = airyZero 1 := rfl

lemma airyAi_airyNode (i : ℕ) : airyAi (airyNode i) = 0 := airyAi_airyZero (i + 1)

lemma airyNode_neg (i : ℕ) : airyNode i < 0 := airyZero_neg (i + 1)

lemma airyAi'_airyNode_ne (i : ℕ) : airyAi' (airyNode i) ≠ 0 := by
  intro h0
  apply airyZero_deriv_ne_zero (i + 1)
  have := deriv_airyAiC_ofReal (airyNode i)
  unfold airyNode at this h0
  rw [this, h0]; simp

lemma airyNodeWeight_pos (i : ℕ) : 0 < airyNodeWeight i := by
  unfold airyNodeWeight
  have := airyAi'_airyNode_ne i
  positivity

lemma airyNode_strictAnti : StrictAnti airyNode :=
  strictAnti_nat_of_succ_lt fun i => airyZero_strictAnti (n := i + 1) (by omega)

lemma airyNode_injective : Function.Injective airyNode := airyNode_strictAnti.injective

lemma airyNode_le_airyNode_zero (i : ℕ) : airyNode i ≤ airyZero 1 :=
  airyNode_strictAnti.antitone (Nat.zero_le i)

lemma tendsto_airyNode : Tendsto airyNode atTop atBot := by
  refine tendsto_atBot.2 fun x => ?_
  obtain ⟨n, hn, hlt⟩ := exists_airyZero_lt x
  refine eventually_atTop.2 ⟨n, fun m hm => ?_⟩
  have : airyZero (m + 1) < airyZero n := airyZero_lt_of_lt (by omega) (by omega)
  exact (this.trans hlt).le

/-- Every zero `u ≤ 0` of `Ai` is some node. -/
lemma exists_airyNode_eq {u : ℝ} (hu : airyAi u = 0) (hu0 : u ≤ 0) : ∃ i, u = airyNode i := by
  obtain ⟨n, hn, rfl⟩ := exists_airyZero_eq hu hu0
  exact ⟨n - 1, by unfold airyNode; congr 1; omega⟩

/-- The Airy quadrature measure `μ_A = Σ_n δ_{a_n} / Ai'(a_n)²` (`spectral_rigidity.tex`, §1). -/
noncomputable def airyMeasure : Measure ℝ :=
  Measure.sum fun i : ℕ => ENNReal.ofReal (airyNodeWeight i) • Measure.dirac (airyNode i)

lemma finite_support_of_cs {g : ℝ → ℝ} (hcs : HasCompactSupport g) :
    {i : ℕ | g (airyNode i) ≠ 0}.Finite := by
  obtain ⟨B, hB⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have h1 : ∀ᶠ i in atTop, airyNode i < -(|B| + 1) := tendsto_airyNode.eventually (eventually_lt_atBot _)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h1
  refine (Set.finite_lt_nat N).subset fun i hi => ?_
  show i < N
  by_contra hcon
  have hlt := hN i (not_lt.mp hcon)
  have hmem : airyNode i ∈ tsupport g := subset_tsupport _ hi
  have := hB hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have := abs_le.mp this
  linarith [le_abs_self B, this.1]

lemma summable_of_cs {g : ℝ → ℝ} (hcs : HasCompactSupport g) (w : ℕ → ℝ) :
    Summable (fun i => g (airyNode i) * w i) := by
  refine summable_of_ne_finset_zero (s := (finite_support_of_cs hcs).toFinset) fun i hi => ?_
  have : g (airyNode i) = 0 := by
    by_contra h0
    exact hi ((finite_support_of_cs hcs).mem_toFinset.mpr h0)
  simp [this]

lemma measurableSet_range_airyNode : MeasurableSet (Set.range airyNode) :=
  (Set.countable_range _).measurableSet

/-- A measure concentrated on the zeros of `Ai` is the sum of its atoms. -/
lemma measure_eq_sum_atoms {ν : Measure ℝ} (h : ν (Set.range airyNode)ᶜ = 0) :
    ν = Measure.sum fun i => ν {airyNode i} • Measure.dirac (airyNode i) := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  have h1 : ν s = ν (s ∩ Set.range airyNode) := by
    have := measure_inter_add_sdiff s measurableSet_range_airyNode (μ := ν)
    have h0 : ν (s \ Set.range airyNode) = 0 := measure_mono_null (fun x hx => hx.2) h
    rw [h0, add_zero] at this
    exact this.symm
  have h2 : s ∩ Set.range airyNode = ⋃ i, (s ∩ {airyNode i}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, i, rfl⟩; exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hx, rfl⟩; exact ⟨hx, i, rfl⟩
  rw [h1, h2, measure_iUnion]
  · congr 1
    ext i
    rw [smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    by_cases hi : airyNode i ∈ s
    · have : s ∩ {airyNode i} = {airyNode i} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · exact fun hx => hx.2
        · rintro rfl; exact ⟨hi, rfl⟩
      simp [this, Set.indicator_of_mem hi]
    · have : s ∩ {airyNode i} = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro hx rfl; exact hi hx
      simp [this, Set.indicator_of_notMem hi]
  · intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => hij (airyNode_injective ?_)
    exact hxi.2.symm.trans hxj.2
  · intro i
    exact hs.inter (measurableSet_singleton _)

/-- **Atomic integral**: for `ν` concentrated on the zeros of `Ai` and `g` continuous with compact
support, `∫ g dν = Σ_i g(a_i) ν{a_i}`. -/
lemma integral_eq_tsum_atoms {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (h : ν (Set.range airyNode)ᶜ = 0) {g : ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∫ u, g u ∂ν = ∑' i, g (airyNode i) * (ν {airyNode i}).toReal := by
  have hint : Integrable g (Measure.sum fun i => ν {airyNode i} • Measure.dirac (airyNode i)) := by
    rw [← measure_eq_sum_atoms h]; exact integrable_of_cs hg hcs
  calc ∫ u, g u ∂ν
      = ∫ u, g u ∂(Measure.sum fun i => ν {airyNode i} • Measure.dirac (airyNode i)) :=
        congrArg (fun m => ∫ u, g u ∂m) (measure_eq_sum_atoms h)
    _ = ∑' i, g (airyNode i) * (ν {airyNode i}).toReal := by
        rw [integral_sum_measure hint]
        refine tsum_congr fun i => ?_
        rw [integral_smul_measure, integral_dirac, smul_eq_mul, mul_comm]

lemma integrable_airyMeasure {g : ℝ → ℝ} (hg : Continuous g)
    (hs : Summable fun i => g (airyNode i) * airyNodeWeight i) : Integrable g airyMeasure := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral airyMeasure
  rw [lintegral_sum_measure]
  have hterm : ∀ i, ∫⁻ u, ‖g u‖ₑ ∂(ENNReal.ofReal (airyNodeWeight i) • Measure.dirac (airyNode i)) =
      ENNReal.ofReal (|g (airyNode i) * airyNodeWeight i|) := by
    intro i
    rw [lintegral_smul_measure, lintegral_dirac' _ hg.measurable.eNorm, smul_eq_mul, mul_comm,
      abs_mul, abs_of_pos (airyNodeWeight_pos i), ENNReal.ofReal_mul (abs_nonneg _),
      Real.eNorm_eq_ofReal_abs]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg _) hs.abs]
  exact ENNReal.ofReal_lt_top

lemma integral_airyMeasure {g : ℝ → ℝ} (hg : Continuous g)
    (hs : Summable fun i => g (airyNode i) * airyNodeWeight i) :
    ∫ u, g u ∂airyMeasure = ∑' i, g (airyNode i) * airyNodeWeight i := by
  have hint := integrable_airyMeasure hg hs
  unfold airyMeasure at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun i => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal
    (airyNodeWeight_pos i).le, mul_comm]

lemma airyMeasure_singleton (i : ℕ) : airyMeasure {airyNode i} = ENNReal.ofReal (airyNodeWeight i) := by
  unfold airyMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    have hne : airyNode j ≠ airyNode i := airyNode_injective.ne hj
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator, hne]

lemma airyMeasure_compl_range : airyMeasure (Set.range airyNode)ᶜ = 0 := by
  unfold airyMeasure
  rw [Measure.sum_apply _ measurableSet_range_airyNode.compl]
  refine tsum_eq_zero_iff.2 fun i => ?_
  simp [Measure.dirac_apply' _ measurableSet_range_airyNode.compl, Set.indicator]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integral_eq_tsum_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integral_eq_tsum_atoms

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integral_airyMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integral_airyMeasure

end FormalResearch.ModularBootstrap.Upper.Rigidity
