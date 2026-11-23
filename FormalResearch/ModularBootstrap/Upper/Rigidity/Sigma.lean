module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Atoms

/-!
# Theorem `Σ` (`spectral_rigidity.tex`, `sr:Sigma`) at the abstract measure level

Setting (`SpectralData`): spectral measures `μ_j` in the Airy variable, supported on `u ≤ s_j`,
with (Gap) `limsup s_j ≤ a₁`.  Hypotheses: Property `sr:P` (`DesignPropertyP`) and the window algebra
of the three design families (`SameSiteFamily`, `DisplacedFamily`, `OmittedFamily`).  Conclusions
(`theorem_Sigma`):

1. (compactness) `μ_j(K) ≤ C_K` eventually for every compact `K`; along every ultrafilter
   `𝒰 ≤ atTop` a vague limit `ν` exists and `ν(a₁, ∞) = 0` (ultrafilters replace subsequences);
2. (concentration) every vague limit is carried by `{a_n}`;
3. (weights) `x_n = ν{a_n} Ai'(a_n)² ≤ 1`, and `x_n = 1` for all `n`; hence
   `μ_j → μ_A` vaguely along the whole sequence, and
4. (no escape) for every design test, `limsup_j ∫_{u < -R} Ψ_j dμ_j → 0` as `R → ∞`.

`theorem_sigma` restates this in the variables `(c_j, τ_j)` of the paper.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.FixedWeight

/-- **Step 7a** (`sr:Sigma`): `μ_j → μ_A` vaguely along the whole sequence. -/
theorem vagueLimit_airyMeasure (S : SpectralData) {𝒟 : Set Window}
    (hP : DesignPropertyP S.μ 𝒟) (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟)
    (Om : OmittedFamily 𝒟) : IsVagueLimit atTop S.μ airyMeasure := by
  have hbd := locallyBounded S hP F
  intro g hg hcs
  rw [Filter.tendsto_iff_ultrafilter]
  intro 𝒰 h𝒰
  obtain ⟨ν, hlf, hν⟩ := exists_vagueLimit S.μ hbd 𝒰 h𝒰
  have := hlf
  have hconc := concentration S hP F hbd h𝒰 hν
  have hx := atomWeight_eq_one S hbd hP F Dis Om h𝒰 hν hconc
  have : ∫ u, g u ∂ν = ∫ u, g u ∂airyMeasure := by
    rw [integral_eq_tsum_atoms hconc hg hcs, integral_airyMeasure hg (summable_of_cs hcs _)]
    refine tsum_congr fun i => ?_
    congr 1
    have := atomWeight_mul_weight ν i
    rw [hx i, one_mul] at this
    exact this.symm
  rw [← this]
  exact hν g hg hcs

/-- **Step 7b** (`sr:Sigma`): no positive pairing mass escapes: for every design test,
`limsup_j ∫_{u < -R} Ψ_j dμ_j → 0` as `R → ∞`. -/
theorem no_escape (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟) (Om : OmittedFamily 𝒟)
    {D : Window} (T : DesignTest S.μ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ j in atTop,
      ∫ u in Iio (-R), T.Ψ j u ∂(S.μ j) ≤ ε := by
  have hbd := locallyBounded S hP F
  have hv := vagueLimit_airyMeasure S hP F Dis Om
  have hpi := D.summable_pi
  have habs : Summable fun i => |D.pi i| := hpi.abs
  obtain ⟨N, hN⟩ := (eventually_atTop.1 ((tendsto_sum_nat_add (fun i => |D.pi i|)).eventually
    (gt_mem_nhds (half_pos hε))))
  refine ⟨max (1 - airyNode N) (|D.uF| + 3), fun R hR => ?_⟩
  have hR1 : 1 - airyNode N ≤ R := (le_max_left _ _).trans hR
  have hR2 : |D.uF| + 3 ≤ R := (le_max_right _ _).trans hR
  set A : ℝ := -R + 1 with hA
  set B : ℝ := airyZero 1 + 1 with hB
  set χ := cutoff A B with hχ
  have hlim := tendsto_cutoff_integral S hbd le_rfl hv T A B
  -- the model integral
  have hg : Continuous (fun u => χ u * D.W u) := (cutoff_continuous A B).mul D.continuous
  have hcsg : HasCompactSupport (fun u => χ u * D.W u) := HasCompactSupport.mul_cutoff A B
  have hmodel : ∫ u, χ u * D.W u ∂airyMeasure = ∑' i, χ (airyNode i) * D.pi i := by
    rw [integral_airyMeasure hg (summable_of_cs hcsg _)]
    refine tsum_congr fun i => ?_
    simp only [Window.pi]; ring
  -- deficit of the cutoff
  have hdef : D.V - ∑' i, χ (airyNode i) * D.pi i ≤ ε / 2 := by
    have hsχ : Summable fun i => χ (airyNode i) * D.pi i := by
      have := summable_of_cs hcsg (fun i => airyNodeWeight i)
      refine this.congr fun i => ?_
      simp only [Window.pi]; ring
    have hs : Summable fun i => (1 - χ (airyNode i)) * D.pi i := by
      have := hpi.sub hsχ
      refine this.congr fun i => ?_
      ring
    have hV : D.V - ∑' i, χ (airyNode i) * D.pi i = ∑' i, (1 - χ (airyNode i)) * D.pi i := by
      rw [← D.tsum_pi, ← hpi.tsum_sub hsχ]
      exact tsum_congr fun i => by ring
    rw [hV, ← hs.sum_add_tsum_nat_add N]
    have h0 : ∑ i ∈ Finset.range N, (1 - χ (airyNode i)) * D.pi i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : i < N := Finset.mem_range.mp hi
      have : χ (airyNode i) = 1 := by
        refine cutoff_eq_one (A := A) (B := B) ?_ ?_
        · have := airyNode_strictAnti.antitone hi'.le
          rw [hA]; linarith
        · exact (airyNode_le_airyNode_zero i).trans (by rw [hB]; linarith)
      rw [this]; ring
    rw [h0, zero_add]
    have hle : ∑' k, (1 - χ (airyNode (k + N))) * D.pi (k + N) ≤ ∑' k, |D.pi (k + N)| := by
      refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff N).2 hs)
        ((summable_nat_add_iff N).2 habs)
      have h1 := cutoff_nonneg A B (airyNode (k + N))
      have h2 := cutoff_le_one A B (airyNode (k + N))
      calc (1 - χ (airyNode (k + N))) * D.pi (k + N)
          ≤ (1 - χ (airyNode (k + N))) * |D.pi (k + N)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
        _ ≤ 1 * |D.pi (k + N)| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = |D.pi (k + N)| := one_mul _
    have := hN N le_rfl
    linarith
  -- eventual inequalities
  have e1 : ∀ᶠ j in atTop, A < T.θ j := by
    have := T.theta_tendsto
    refine this.eventually (lt_mem_nhds ?_)
    have := neg_abs_le D.uF
    rw [hA]; linarith
  have e2 := S.ae_le_of_gap (δ := 1) one_pos
  have e3 := T.limsup_le (ε / 4) (by positivity)
  have e4 : ∀ᶠ j in atTop, (∫ u, χ u * D.W u ∂airyMeasure) - ε / 4 <
      ∫ u, χ u * T.Ψ j u ∂(S.μ j) :=
    hlim.eventually (lt_mem_nhds (by linarith))
  filter_upwards [e1, e2, e3, e4] with j hj1 hj2 hj3 hj4
  have hind : Integrable ((Iio (-R)).indicator (T.Ψ j)) (S.μ j) :=
    (T.integrable_mu j).indicator measurableSet_Iio
  have hint1 : Integrable (fun u => χ u * T.Ψ j u) (S.μ j) := by
    refine (T.integrable_mu j).bdd_mul (c := 1) ?_ ?_
    · exact (cutoff_continuous A B).aestronglyMeasurable
    · exact Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg A B u)]; exact cutoff_le_one A B u
  have hle : ∫ u, (Iio (-R)).indicator (T.Ψ j) u ∂(S.μ j) + ∫ u, χ u * T.Ψ j u ∂(S.μ j) ≤
      ∫ u, T.Ψ j u ∂(S.μ j) := by
    rw [← integral_add hind hint1]
    refine integral_mono_ae (hind.add hint1) (T.integrable_mu j) ?_
    filter_upwards [hj2] with u hu
    by_cases h1 : u < -R
    · have hχ0 : χ u = 0 := cutoff_eq_zero (A := A) (B := B) (Or.inl (by rw [hA]; linarith))
      simp [Set.indicator_of_mem (show u ∈ Iio (-R) from h1), hχ0]
    · push Not at h1
      have hnot : u ∉ Iio (-R) := not_lt.mpr h1
      simp only [Set.indicator_of_notMem hnot, zero_add]
      by_cases h2 : u < A
      · have := T.nonneg j u (by linarith)
        have h3 := cutoff_le_one A B u
        nlinarith [cutoff_nonneg A B u]
      · push Not at h2
        have : χ u = 1 := cutoff_eq_one h2 (by rw [hB]; exact hu.trans (by linarith))
        rw [this]; linarith
  rw [integral_indicator measurableSet_Iio] at hle
  have := T.crossing j
  rw [hmodel] at hj4
  linarith

/-- **Theorem `Σ`** (`sr:Sigma`), abstract measure level.  See the module docstring. -/
theorem theorem_Sigma (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟) (Om : OmittedFamily 𝒟) :
    -- (1) compactness
    LocallyBounded S.μ ∧
    (∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop → ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      IsVagueLimit 𝒰 S.μ ν ∧ ν (Ioi (airyZero 1)) = 0) ∧
    -- (2) concentration and (3) weights for every vague limit
    (∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop → ∀ ν : Measure ℝ, IsLocallyFiniteMeasure ν →
      IsVagueLimit 𝒰 S.μ ν → ν (Set.range airyNode)ᶜ = 0 ∧
        (∀ i, atomWeight ν i ≤ 1) ∧ ∀ i, atomWeight ν i = 1) ∧
    -- whole-sequence vague convergence to `μ_A`
    IsVagueLimit atTop S.μ airyMeasure ∧
    -- (4) no escape of positive pairing mass
    (∀ D : Window, ∀ T : DesignTest S.μ D, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ᶠ j in atTop, ∫ u in Iio (-R), T.Ψ j u ∂(S.μ j) ≤ ε) := by
  have hbd := locallyBounded S hP F
  refine ⟨hbd, fun 𝒰 h𝒰 => ?_, fun 𝒰 h𝒰 ν hν hv => ?_, vagueLimit_airyMeasure S hP F Dis Om,
    fun D T ε hε => no_escape S hP F Dis Om T hε⟩
  · obtain ⟨ν, hlf, hν⟩ := exists_vagueLimit S.μ hbd 𝒰 h𝒰
    have := hlf
    exact ⟨ν, hlf, hν, vagueLimit_supp S h𝒰 hν⟩
  · have hconc := concentration S hP F hbd h𝒰 hv
    exact ⟨hconc, atomWeight_le_one S hbd hP F Dis h𝒰 hv hconc,
      atomWeight_eq_one S hbd hP F Dis Om h𝒰 hv hconc⟩

/-- **Theorem `Σ`** in the variables `(c_j, τ_j)` of the paper: the conclusions of
`theorem_Sigma` for the spectral data `SpectralData.ofGap`. -/
theorem theorem_sigma {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop) (hgap : GapCondition c τ)
    (μ : ℕ → Measure ℝ) [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hsupp : ∀ j, μ j (Ioi (uAiry (c j) (τ j))) = 0) {𝒟 : Set Window}
    (hP : DesignPropertyP μ 𝒟) (F : SameSiteFamily 𝒟) (Dis : DisplacedFamily 𝒟)
    (Om : OmittedFamily 𝒟) :
    LocallyBounded μ ∧
    (∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop → ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      IsVagueLimit 𝒰 μ ν ∧ ν (Ioi (airyZero 1)) = 0) ∧
    (∀ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ atTop → ∀ ν : Measure ℝ, IsLocallyFiniteMeasure ν →
      IsVagueLimit 𝒰 μ ν → ν (Set.range airyNode)ᶜ = 0 ∧
        (∀ i, atomWeight ν i ≤ 1) ∧ ∀ i, atomWeight ν i = 1) ∧
    IsVagueLimit atTop μ airyMeasure ∧
    (∀ D : Window, ∀ T : DesignTest μ D, ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ᶠ j in atTop, ∫ u in Iio (-R), T.Ψ j u ∂(μ j) ≤ ε) :=
  theorem_Sigma (SpectralData.ofGap hc hgap μ hsupp) hP F Dis Om

/-! ### The model `μ_j = μ_A` -/

lemma isLocallyFinite_airyMeasure : IsLocallyFiniteMeasure airyMeasure := by
  refine ⟨fun x => ?_⟩
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  have hfin : {i : ℕ | airyNode i ∈ Icc (x - 1) (x + 1)}.Finite := by
    have h1 : ∀ᶠ i in atTop, airyNode i < x - 1 := tendsto_airyNode.eventually (eventually_lt_atBot _)
    obtain ⟨N, hN⟩ := eventually_atTop.1 h1
    refine (Set.finite_lt_nat N).subset fun i hi => ?_
    show i < N
    by_contra hcon
    have := hN i (not_lt.mp hcon)
    linarith [hi.1]
  unfold airyMeasure
  rw [Measure.sum_apply _ measurableSet_Icc]
  have : ∀ i ∉ hfin.toFinset, (ENNReal.ofReal (airyNodeWeight i) • Measure.dirac (airyNode i))
      (Icc (x - 1) (x + 1)) = 0 := by
    intro i hi
    have : airyNode i ∉ Icc (x - 1) (x + 1) := fun h => hi (hfin.mem_toFinset.2 h)
    simp [Measure.dirac_apply' _ measurableSet_Icc, Set.indicator, this]
  rw [tsum_eq_sum this]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- **Consistency of the setting**: the Airy quadrature measure `μ_A` (`μ_j = μ_A`, `s_j = a₁`)
is spectral data in the sense of `SpectralData`, and carries a design test for every window
(`designPropertyP_nonvacuous`). -/
noncomputable def airySpectralData : SpectralData where
  μ := fun _ => airyMeasure
  s := fun _ => airyZero 1
  locFin := fun _ => isLocallyFinite_airyMeasure
  supp := fun _ => by
    refine measure_mono_null (t := (Set.range airyNode)ᶜ) (fun u hu => ?_) airyMeasure_compl_range
    intro ⟨i, hi⟩
    have : airyNode i ≤ airyZero 1 := airyNode_le_airyNode_zero i
    have hu' : airyZero 1 < u := hu
    rw [hi] at this
    linarith
  gap := fun δ hδ => Eventually.of_forall fun _ => by linarith

/-- The model `μ_A` carries a design test for every window: the design hypothesis `sr:P`
(`DesignPropertyP`) is satisfiable at the extremal spectral measure. -/
theorem airySpectralData_designPropertyP (𝒟 : Set Window) :
    DesignPropertyP airySpectralData.μ 𝒟 := designPropertyP_nonvacuous 𝒟

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.vagueLimit_airyMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.vagueLimit_airyMeasure

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.no_escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.no_escape

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_Sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_Sigma

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.isLocallyFinite_airyMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.isLocallyFinite_airyMeasure

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.airySpectralData_designPropertyP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.airySpectralData_designPropertyP

end FormalResearch.ModularBootstrap.Upper.Rigidity
