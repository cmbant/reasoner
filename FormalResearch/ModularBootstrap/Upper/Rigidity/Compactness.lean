module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Weights
public import FormalResearch.ModularBootstrap.Upper.Rigidity.SigmaZero

/-!
# Theorem `Σ`, Steps 1--4: compactness, concentration, atomic inequality

* `locallyBounded` (Step 2): `μ_j(K) ≤ C_K` for every compact `K`, eventually (design `𝔅_κ`,
  `W_𝔅 > 0` on the whole support).
* `vagueLimit_supp`: a vague limit lives on `u ≤ a₁` ((Gap)).
* `concentration` (Step 3): a vague limit is carried by the Airy zeros `{a_n}`.
* `atomic_inequality` (Step 4, `sr:e2`): for a vague limit carried by `{a_n}` and every design test,
  `Σ_n x_n Π_n ≤ V_𝔇`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special

lemma designRadius_lt_two : designRadius < 2 := by
  unfold designRadius
  have h1 : min |airyZero 1| |airyZero 1 - airyZero 2| ≤ |airyZero 1| := min_le_left _ _
  have h2 := (airyZero_one).1
  have h3 := (airyZero_one).2
  have h4 : |airyZero 1| = -airyZero 1 := abs_of_neg (airyZero_neg 1)
  linarith

lemma airyNode_zero_lt : airyNode 0 < 0 := airyNode_neg 0

/-- **Step 2** (`sr:Sigma`): the masses of compacta are eventually bounded. -/
theorem locallyBounded (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) : LocallyBounded S.μ := by
  intro K hK
  have hr := designRadius_pos
  set κ : ℝ := designRadius / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  have habs : |-κ| < designRadius := by rw [abs_neg, abs_of_pos hκ0]; linarith
  obtain ⟨T⟩ := hP _ (F.mem 0 (-κ) habs)
  set D := F.win 0 (-κ) with hD
  set K' : Set ℝ := K ∩ Iic (airyNode 0 + κ / 2) with hK'
  have hK'c : IsCompact K' := hK.inter_right isClosed_Iic
  have huF : D.uF = airyNode 0 + κ := by rw [hD, F.uF_eq]; ring
  have hsub : K ⊆ K' ∪ Ioi (airyNode 0 + κ / 2) := by
    intro u hu
    by_cases h : u ≤ airyNode 0 + κ / 2
    · exact Or.inl ⟨hu, h⟩
    · exact Or.inr (not_le.mp h)
  have hnull : ∀ᶠ j in atTop, S.μ j (Ioi (airyNode 0 + κ / 2)) = 0 := by
    filter_upwards [S.gap (κ / 4) (by positivity)] with j hj
    refine measure_mono_null (fun u hu => ?_) (S.supp j)
    show S.s j < u
    have : airyNode 0 + κ / 2 < u := hu
    rw [← airyNode_zero] at hj
    linarith
  have hK_le : ∀ᶠ j in atTop, (S.μ j K).toReal ≤ (S.μ j K').toReal := by
    filter_upwards [hnull] with j hj
    have h1 : S.μ j K ≤ S.μ j K' := by
      calc S.μ j K ≤ S.μ j (K' ∪ Ioi (airyNode 0 + κ / 2)) := measure_mono hsub
        _ ≤ S.μ j K' + S.μ j (Ioi (airyNode 0 + κ / 2)) := measure_union_le _ _
        _ = S.μ j K' := by rw [hj, add_zero]
    exact ENNReal.toReal_mono hK'c.measure_lt_top.ne h1
  by_cases hne : K'.Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := hK'c.exists_isMinOn hne D.continuous.continuousOn
    have hu₀le : u₀ ≤ airyNode 0 + κ / 2 := hu₀.2
    have hm : 0 < D.W u₀ := by
      rw [hD, F.W_eq]
      have hG : 0 < F.G 0 u₀ := F.G_pos 0 u₀ (by linarith)
      have : 0 < airyNode 0 - -κ - u₀ := by linarith
      positivity
    set m := D.W u₀ with hmdef
    refine ⟨2 * (D.V + 1) / m, ?_⟩
    have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 T.window_limit) K' hK'c
    have e1 := S.ae_le_of_gap (δ := κ / 4) (by positivity)
    have e2 : ∀ᶠ j in atTop, airyNode 0 + κ / 2 < T.θ j := by
      have := T.theta_tendsto
      rw [huF] at this
      exact this.eventually (lt_mem_nhds (by linarith))
    have e3 := T.limsup_le 1 one_pos
    have e4 : ∀ᶠ j in atTop, ∀ x ∈ K', dist (D.W x) (T.Ψ j x) < m / 2 :=
      Metric.tendstoUniformlyOn_iff.1 hunif (m / 2) (by positivity)
    filter_upwards [hK_le, e1, e2, e3, e4] with j hj0 hj1 hj2 hj3 hj4
    have hlow : ∀ u ∈ K', m / 2 ≤ T.Ψ j u := by
      intro u hu
      have h1 := hj4 u hu
      rw [Real.dist_eq] at h1
      have h2 := (abs_lt.mp h1).2
      have h3 : m ≤ D.W u := hmin hu
      linarith
    have hoff : ∀ᵐ u ∂(S.μ j), u ∉ K' → 0 ≤ T.Ψ j u := by
      filter_upwards [hj1] with u hu _
      have hu' : u ≤ airyNode 0 + κ / 4 := by rw [airyNode_zero]; exact hu
      exact T.nonneg j u (by linarith)
    have hmain := const_mul_measure_le_integral (T.integrable_mu j) hK'c.measurableSet
      hK'c.measure_lt_top hlow hoff
    rw [T.crossing j] at hmain
    have h5 : m / 2 * (S.μ j K').toReal ≤ D.V + 1 := hmain.trans hj3
    have h6 : (S.μ j K').toReal ≤ 2 * (D.V + 1) / m := by
      rw [le_div_iff₀ hm]; nlinarith
    exact hj0.trans h6
  · refine ⟨0, ?_⟩
    have hK'e : K' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    filter_upwards [hK_le] with j hj
    rw [hK'e] at hj
    simpa using hj

/-- A vague limit of the `μ_j` lives on `u ≤ a₁` (consequence of (Gap)). -/
theorem vagueLimit_supp (S : SpectralData) {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop)
    {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 S.μ ν) :
    ν (Ioi (airyZero 1)) = 0 := by
  have hδ : ∀ δ : ℝ, 0 < δ → ν (Ioi (airyZero 1 + δ)) = 0 := by
    intro δ hδ
    rw [(isOpen_Ioi (a := airyZero 1 + δ)).measurableSet.measure_eq_iSup_isCompact]
    refine le_antisymm (iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_) bot_le
    obtain ⟨f, hfK, hfU, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hK
      (isOpen_Ioi (a := airyZero 1 + δ)).isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKU)
    have hlim := hν f f.continuous hfcs
    have hzero : ∀ᶠ j in (𝒰 : Filter ℕ), ∫ u, f u ∂(S.μ j) = 0 := by
      refine Filter.Eventually.filter_mono h𝒰 ?_
      filter_upwards [S.ae_le_of_gap hδ] with j hj
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hj] with u hu
      exact hfU (by simpa using hu)
    have h0 : ∫ u, f u ∂ν = 0 :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun j hj => hj.symm))
    have h1 : ν K ≤ ENNReal.ofReal (∫ u, f u ∂ν) :=
      (integrable_of_cs f.continuous hfcs).measure_le_integral
        (Eventually.of_forall fun x => (hf01 x).1) (fun x hx => by simp [hfK hx])
    rw [h0] at h1
    simpa using h1
  have : Ioi (airyZero 1) = ⋃ n : ℕ, Ioi (airyZero 1 + 1 / ((n : ℝ) + 1)) := by
    ext u
    simp only [mem_Ioi, mem_iUnion]
    constructor
    · intro hu
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hu)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [this]
  exact measure_iUnion_null fun n => hδ _ (by positivity)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.locallyBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.locallyBounded

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.vagueLimit_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.vagueLimit_supp

end FormalResearch.ModularBootstrap.Upper.Rigidity
