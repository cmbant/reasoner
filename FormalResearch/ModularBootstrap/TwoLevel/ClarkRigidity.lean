module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityMeasure
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigiditySequence
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityLimit
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityApprox

/-!
# Theorem 2.6: node-level Clark rigidity (`virasoro_two_level.tex`, `gt:2.6`)

For `A₁ < A_opt` and a two-level sequence `S` (`TwoLevelSequence`), the Cardy-normalised spectral measures `μ_j`
(`S.μ`) converge vaguely to the Clark measure `μ_α = Σ_n δ_{z_n}/K(z_n, z_n)`, `α = α(-A₁/c_*)`.

Inputs: the two-simple-zero transfer `TwoSimpleZeroTransfer prob` (`ut:T2`), and `TwoZeroIdealApprox`, the statement
about the explicit product windows alone that every admissible ideal datum is a limit of two-simple-zero windows
(pointwise, boundedly on compacta, with the vacuum integrals converging).  Nothing else is assumed:

* `TwoLevelSequence.twoLevelSupport`: `μ_j` is carried by `{s₁^{(j)}} ∪ (-∞, s₂^{(j)}]`, `s₁^{(j)} → z₁`,
  `limsup s₂^{(j)} ≤ z₂`;
* `locallyBounded_of_support`: local boundedness from one positive window (`p = z₁ - r`, `q = z₂ + r`);
* `theorem_two_six`: vague limits along ultrafilters are carried by the nodes (concentration), have `ν{z_n} ≤ 1/K_n`
  (upper windows) and `ν{z_n} ≥ 1/K_n` (lower windows), by `measure_eq_clarkMeasure`.

All results are proved from the two named hypotheses.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.Upper.Rigidity

namespace TwoLevelSequence

variable {prob : FixedWeightProblem} {A₁ : ℝ} (S : TwoLevelSequence prob A₁)

/-- The support data of the spectral measures of a two-level sequence, with `z₁ = -A₁/c_*` and
`z₂ = -A₂*(A₁)/c_*`. -/
noncomputable def twoLevelSupport (hA : A₁ < Aopt) :
    TwoLevelSupport S.μ (clarkNode (clarkAngle (-A₁ / cStar)) 1) (clarkNode (clarkAngle (-A₁ / cStar)) 2) where
  s₁ j := uAiry (S.c j) (S.t₁ j)
  s₂ j := uAiry (S.c j) (S.τ j)
  tendsto_s₁ := by
    rw [(clarkAngle_spec (mem_gap_one_of_lt_Aopt hA)).2]
    exact S.tendsto_uAiry_t₁
  s₂_le ε hε := by
    have h := S.eventually_uAiry_τ_le (A₁ := A₁) hε
    have e : -A2star A₁ / cStar = clarkNode (clarkAngle (-A₁ / cStar)) 2 := by
      rw [A2star_eq_neg_cStar_mul hA]
      have := cStar_pos
      field_simp
    rw [e] at h
    exact h
  null_top := S.μ_Ioi_null
  null_gap := S.spectral_gap_null

end TwoLevelSequence

/-- **Local boundedness from a positive two-simple-zero window** (`p = z₁ - r`, `q = z₂ + r`). -/
theorem locallyBounded_of_support {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)] {z₁ z₂ : ℝ}
    (hz : z₂ < z₁) (hz2 : z₂ < 0) (T : TwoLevelSupport μ z₁ z₂) (hP : DesignPropertyP μ twoZeroClass) :
    LocallyBounded μ := by
  set r : ℝ := min ((z₁ - z₂) / 4) (-z₂ / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  have hr1 : r ≤ (z₁ - z₂) / 4 := min_le_left _ _
  have hr2 : r ≤ -z₂ / 2 := min_le_right _ _
  set d : TwoZeroDesign 1 := ⟨z₁ - r, z₂ + r, fun _ => -1, fun _ => 1⟩ with hd
  have hadm : d.Adm := ⟨by show z₂ + r < z₁ - r; linarith, by show z₂ + r < 0; linarith,
    fun _ => by norm_num, Function.injective_of_subsingleton _, fun _ => one_pos⟩
  obtain ⟨T'⟩ := hP _ (twoZeroWin_mem le_rfl d hadm)
  refine mass_bound_of_positive_window T' (b := z₂ + r / 2) ?_ (E' := Icc (z₁ - r / 2) (z₁ + r / 2))
    isCompact_Icc ?_ ?_
  · show z₂ + r / 2 < z₂ + r; linarith
  · intro u hu
    show 0 < d.Wr u
    rcases hu with h | h
    · exact d.Wr_pos_of_lt hadm (by show u < z₂ + r; linarith)
    · exact d.Wr_pos_of_gt hadm (by show z₁ - r < u; linarith [h.1])
  · have e1 := T.s₂_le (r / 2) (by positivity)
    have e2 : ∀ᶠ j in atTop, T.s₁ j ∈ Icc (z₁ - r / 2) (z₁ + r / 2) :=
      T.tendsto_s₁.eventually (Icc_mem_nhds (by linarith) (by linarith))
    filter_upwards [e1, e2] with j h1 h2
    filter_upwards [ae_le_of_supp (T.null_top j), measure_eq_zero_iff_ae_notMem.1 (T.null_gap j)]
      with u hu1 hu2
    by_cases hh : u ≤ T.s₂ j
    · left; linarith
    · right
      push Not at hh
      have : T.s₁ j ≤ u := by
        by_contra hcon
        exact hu2 ⟨hh, not_le.1 hcon⟩
      have hu : u = T.s₁ j := le_antisymm hu1 this
      rw [hu]; exact h2

/-- **Theorem 2.6** (`gt:2.6`): the Cardy-normalised spectral measures of a two-level sequence converge vaguely to
the Clark measure `μ_α = Σ_n δ_{z_n}/K_n`, `α = α(-A₁/c_*)`.  Inputs: `TwoSimpleZeroTransfer` and
`TwoZeroIdealApprox`. -/
theorem theorem_two_six {prob : FixedWeightProblem} (hT : TwoSimpleZeroTransfer prob)
    (hAp : TwoZeroIdealApprox) {A₁ : ℝ} (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    IsVagueLimit atTop S.μ (clarkMeasure (clarkAngle (-A₁ / cStar))) := by
  have hu₁ := mem_gap_one_of_lt_Aopt hA
  have hα : Real.sin (clarkAngle (-A₁ / cStar)) ≠ 0 := sin_clarkAngle_ne_zero hu₁
  have hP : DesignPropertyP S.μ twoZeroClass := designPropertyP_twoZero hT S.toCrossingSequence
  set T := S.twoLevelSupport hA with hTdef
  have hz1 : clarkNode (clarkAngle (-A₁ / cStar)) 2 < clarkNode (clarkAngle (-A₁ / cStar)) 1 :=
    clarkNode_lt_of_lt le_rfl (by norm_num) _
  have hz2 : clarkNode (clarkAngle (-A₁ / cStar)) 2 < 0 := clarkNode_two_lt_zero _
  have hbd : LocallyBounded S.μ := locallyBounded_of_support hz1 hz2 T hP
  intro g hg hcs
  rw [Filter.tendsto_iff_ultrafilter]
  intro 𝒰 h𝒰
  obtain ⟨ν, hlf, hν⟩ := exists_vagueLimit S.μ hbd 𝒰 h𝒰
  have hae := T.ae_vagueLimit h𝒰 hν
  have hB := T.ae_le_eventually (show (0 : ℝ) < 1 by norm_num)
  have hI : ∀ δ : IdealDatum, δ.Adm →
      IdealIneq ν (clarkNode (clarkAngle (-A₁ / cStar)) 1 + 1) δ.win δ.q (∫ u, δ.win u) :=
    fun δ hδ => idealIneq_of_approx hbd h𝒰 hν hP hB (hAp δ hδ).some
  have := measure_eq_clarkMeasure hα hae hI
  rw [← this]
  exact hν g hg hcs

/-- **Corollary of Theorem 2.6**: the weight of the atom of `μ_j` at `s₁^{(j)} = u(t₁^{(j)})` tends to `1/K(u₁, u₁)`,
`K(u₁, u₁) = K₁ = Ai'(u₁)² - u₁ Ai(u₁)²`. -/
theorem tendsto_atom_weight {prob : FixedWeightProblem} (hT : TwoSimpleZeroTransfer prob)
    (hAp : TwoZeroIdealApprox) {A₁ : ℝ} (hA : A₁ < Aopt) (S : TwoLevelSequence prob A₁) :
    Tendsto (fun j => (S.μ j {uAiry (S.c j) (S.t₁ j)}).toReal) atTop
      (𝓝 (clarkKernel (clarkAngle (-A₁ / cStar)) 1)⁻¹) := by
  set α := clarkAngle (-A₁ / cStar) with hα
  have hvl := theorem_two_six hT hAp hA S
  set T := S.twoLevelSupport hA with hTdef
  have hz1 : clarkNode α 2 < clarkNode α 1 := clarkNode_lt_of_lt le_rfl (by norm_num) _
  set ε : ℝ := (clarkNode α 1 - clarkNode α 2) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨g, hgK, hgU, hgcs, hg01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_Icc : IsCompact (Icc (clarkNode α 1 - ε / 2) (clarkNode α 1 + ε / 2)))
    (isOpen_Ioo : IsOpen (Ioo (clarkNode α 1 - ε) (clarkNode α 1 + ε))).isClosed_compl
    (disjoint_compl_right_iff_subset.mpr (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩))
  have hlim := hvl g g.continuous hgcs
  -- the limit
  have hν : ∫ u, g u ∂(clarkMeasure α) = (clarkKernel α 1)⁻¹ := by
    rw [node_integral_eq_tsum_atoms (cNode_injective α) (clarkMeasure_compl_range α) g.continuous hgcs,
      tsum_eq_single 0]
    · rw [clarkMeasure_singleton, ENNReal.toReal_ofReal (cWeight_pos α 0).le]
      have h1 : g (cNode α 0) = 1 := hgK ⟨by show _ ≤ clarkNode α 1; linarith, by show clarkNode α 1 ≤ _; linarith⟩
      rw [h1, one_mul]; rfl
    · intro i hi
      have hle : cNode α i ≤ clarkNode α 2 := by
        have := (cNode_strictAnti α).antitone (show 1 ≤ i by omega); simpa [cNode] using this
      have : g (cNode α i) = 0 := hgU (by
        intro hmem; linarith [hmem.1, hle])
      rw [this, zero_mul]
  rw [hν] at hlim
  refine hlim.congr' ?_
  have e1 := T.s₂_le ε hε0
  have e2 : ∀ᶠ j in atTop, T.s₁ j ∈ Icc (clarkNode α 1 - ε / 2) (clarkNode α 1 + ε / 2) :=
    T.tendsto_s₁.eventually (Icc_mem_nhds (by linarith) (by linarith))
  filter_upwards [e1, e2] with j h1 h2
  have hae : ∀ᵐ u ∂(S.μ j), g u = Set.indicator {T.s₁ j} (fun _ => (1 : ℝ)) u := by
    filter_upwards [ae_le_of_supp (T.null_top j), measure_eq_zero_iff_ae_notMem.1 (T.null_gap j)]
      with u hu1 hu2
    by_cases hh : u ≤ T.s₂ j
    · have : g u = 0 := hgU (by intro hmem; linarith [hmem.1])
      rw [this]
      have hne : u ∉ ({T.s₁ j} : Set ℝ) := by
        intro hu; rw [mem_singleton_iff] at hu; subst hu
        linarith [h2.1]
      simp [hne]
    · push Not at hh
      have : T.s₁ j ≤ u := by
        by_contra hcon
        exact hu2 ⟨hh, not_le.1 hcon⟩
      have hu : u = T.s₁ j := le_antisymm hu1 this
      subst hu
      rw [hgK h2]; simp
  rw [integral_congr_ae hae, integral_indicator_const _ (measurableSet_singleton _)]
  simp only [Measure.real, smul_eq_mul, mul_one]
  rfl

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_two_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_two_six

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.locallyBounded_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms locallyBounded_of_support

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tendsto_atom_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_atom_weight

end FormalResearch.ModularBootstrap.TwoLevel
