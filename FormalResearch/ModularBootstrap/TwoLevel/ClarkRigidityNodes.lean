module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityAtoms
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumFunction
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Nodes

/-!
# The Clark nodes, their kernel weights and the Clark measure (`virasoro_two_level.tex`, `gt:2.6`)

With `z_n = clarkNode α n` (`n ≥ 1`) and `K_n = Ai'(z_n)² - z_n Ai(z_n)²`, the Clark measure is
`μ_α = Σ_{n ≥ 1} δ_{z_n}/K_n`.

* `clarkKernel_pos`: `K_n > 0` (`airyKer_pos'`, the diagonal of the Airy kernel is positive everywhere);
* `cNode α i = z_{i+1}`, `cWeight α i = 1/K_{i+1}`: the 0-indexed node sequence (`StrictAnti`, `→ -∞`);
* `clarkMeasure α`: `Σ_i cWeight α i • δ_{cNode α i}`, a locally finite measure with `clarkMeasure α {z_n} = 1/K_n`;
* **ideal windows** (`IdealDatum`): for reals `p, q`, `K ≥ 2` and sites `s_k` (`3 ≤ k ≤ K`), the entire function
  `F_δ` with `F_δ(u) ∏_{k ≤ K}(u - a_k)² = Ai(u)² (u - p)(u - q) ∏_{k=3}^K (u - s_k)²`
  (the window `W_𝔇` of a two-simple-zero design `𝔇` with ideal pairs, `ε_k → 0`, `N → ∞`), its bound `𝒢_{-5/2}`,
  and its Clark node values `τ_i(δ) = F_δ(z_i)/K_i` with `∫ F_δ = Σ_i τ_i(δ)` (`idealWin_hasSum`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

/-! ### The Clark nodes and the Clark measure -/

/-- `K_n = K(z_n, z_n) = Ai'(z_n)² - z_n Ai(z_n)²`, the Airy-kernel diagonal at the `n`-th Clark node. -/
noncomputable def clarkKernel (α : ℝ) (n : ℕ) : ℝ :=
  airyAi' (clarkNode α n) ^ 2 - clarkNode α n * airyAi (clarkNode α n) ^ 2

lemma clarkKernel_pos (α : ℝ) (n : ℕ) : 0 < clarkKernel α n := airyKer_pos' _

/-- The 0-indexed Clark nodes `z_{i+1}`. -/
noncomputable def cNode (α : ℝ) (i : ℕ) : ℝ := clarkNode α (i + 1)

/-- The 0-indexed Clark weights `1/K_{i+1}`. -/
noncomputable def cWeight (α : ℝ) (i : ℕ) : ℝ := (clarkKernel α (i + 1))⁻¹

lemma cWeight_pos (α : ℝ) (i : ℕ) : 0 < cWeight α i := inv_pos.2 (clarkKernel_pos α _)

lemma cNode_strictAnti (α : ℝ) : StrictAnti (cNode α) :=
  strictAnti_nat_of_succ_lt fun i => clarkNode_lt_of_lt (n := i + 1) (m := i + 2) (by omega) (by omega) α

lemma cNode_injective (α : ℝ) : Function.Injective (cNode α) := (cNode_strictAnti α).injective

lemma cNode_lt_airyNode (α : ℝ) (i : ℕ) : cNode α (i + 1) < airyNode i := by
  have := airyClarkNode_lt_airyZero (n := i + 2) (by omega) (Real.cos α / Real.sin α)
  simpa [cNode, clarkNode, airyClarkAngleNode, airyNode] using this

lemma tendsto_cNode (α : ℝ) : Tendsto (cNode α) atTop atBot := by
  have h1 : Tendsto (fun i => cNode α (i + 1)) atTop atBot :=
    tendsto_atBot_mono (fun i => (cNode_lt_airyNode α i).le) tendsto_airyNode
  exact (tendsto_add_atTop_iff_nat (f := cNode α) 1).1 h1

lemma airyNode_lt_cNode (α : ℝ) (i : ℕ) : airyNode i < cNode α i := by
  have := airyZero_lt_airyClarkNode (n := i + 1) (by omega) (Real.cos α / Real.sin α)
  simpa [cNode, clarkNode, airyClarkAngleNode, airyNode] using this

/-- The Clark measure `μ_α = Σ_{n ≥ 1} δ_{z_n(α)} / K(z_n, z_n)`. -/
noncomputable def clarkMeasure (α : ℝ) : Measure ℝ :=
  Measure.sum fun i : ℕ => ENNReal.ofReal (cWeight α i) • Measure.dirac (cNode α i)

lemma clarkMeasure_singleton (α : ℝ) (i : ℕ) :
    clarkMeasure α {cNode α i} = ENNReal.ofReal (cWeight α i) := by
  unfold clarkMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single i]
  · simp
  · intro j hj
    have hne : cNode α j ≠ cNode α i := (cNode_injective α).ne hj
    simp [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator, hne]

lemma clarkMeasure_compl_range (α : ℝ) : clarkMeasure α (Set.range (cNode α))ᶜ = 0 := by
  unfold clarkMeasure
  rw [Measure.sum_apply _ node_measurableSet_range.compl]
  refine tsum_eq_zero_iff.2 fun i => ?_
  simp [Measure.dirac_apply' _ node_measurableSet_range.compl, Set.indicator]

lemma clarkMeasure_Icc_lt_top (α a b : ℝ) : clarkMeasure α (Set.Icc a b) < ∞ := by
  have hfin : {i | cNode α i ∈ Set.Icc a b}.Finite := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_cNode α).eventually (eventually_lt_atBot a))
    refine (Set.finite_lt_nat N).subset fun i hi => ?_
    by_contra h
    exact absurd hi.1 (not_le.2 (hN i (not_lt.1 h)))
  unfold clarkMeasure
  rw [Measure.sum_apply _ measurableSet_Icc, tsum_eq_sum (s := hfin.toFinset)]
  · refine ENNReal.sum_lt_top.2 fun i _ => ?_
    simp only [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (prob_le_one (μ := Measure.dirac (cNode α i)) (s := Set.Icc a b)) ENNReal.one_lt_top)
  · intro i hi
    have : cNode α i ∉ Set.Icc a b := by simpa using hi
    simp [Measure.dirac_apply' _ measurableSet_Icc, Set.indicator, this]

instance (α : ℝ) : IsLocallyFiniteMeasure (clarkMeasure α) :=
  ⟨fun x => ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
    clarkMeasure_Icc_lt_top α _ _⟩⟩

/-- A measure carried by the Clark nodes with `ν{z_n} = 1/K_n` is the Clark measure. -/
lemma eq_clarkMeasure_of_atoms (α : ℝ) {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (h : ν (Set.range (cNode α))ᶜ = 0) (hw : ∀ i, (ν {cNode α i}).toReal = cWeight α i) :
    ν = clarkMeasure α :=
  measure_eq_of_atoms (cNode_injective α) h hw

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.clarkKernel_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clarkKernel_pos

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.eq_clarkMeasure_of_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_clarkMeasure_of_atoms

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.clarkMeasure_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clarkMeasure_singleton

end FormalResearch.ModularBootstrap.TwoLevel
