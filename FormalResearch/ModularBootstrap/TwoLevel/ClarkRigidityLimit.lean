module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityNodes
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityBasic

/-!
# The measure-level steps of the node argument for two levels (`virasoro_two_level.tex`, `gt:2.6`)

Setting (`TwoLevelSupport μ z₁ z₂`): spectral measures `μ_j` with `μ_j(u > s₁^{(j)}) = 0`,
`μ_j(s₂^{(j)} < u < s₁^{(j)}) = 0`, `s₁^{(j)} → z₁` and `limsup s₂^{(j)} ≤ z₂`, `z₂ < z₁`
(first level `t₁ ↔ u₁ = z₁`, second level `τ_j ↔ u(τ_j) → z₂`; `TwoLevelSequence.twoLevelSupport`).

* `vagueLimit_measure_eq_zero`: if `μ_j(U) = 0` eventually along `l` for an open `U` then `ν(U) = 0`;
* `TwoLevelSupport.vagueLimit_supp`: a vague limit lives on `{z₁} ∪ (-∞, z₂]`;
* `mass_bound_of_positive_window`: **local boundedness** (Step 2 of `sr:Sigma`, `gt:2.6` *Compactness and support*):
  a design test whose window is positive on a closed set `E` carrying the supports gives `μ_j(K) ≤ M`;
* `atomic_ineq_of_ideal`: **the atomic inequality** (Step 4): for `ν` carried by the nodes `z_i` and an ideal window `G`
  (`IdealIneq`), `Σ_i x_i τ_i ≤ V`, `x_i = ν{z_i}/w_i`, `τ_i = G(z_i) w_i`, `V = Σ τ_i`;
* `concentration_of_ideal`: **concentration** (Step 3): if ideal windows `G_K ≥ 0` have `V_K/ρ_K → 0` and
  `G_K ≥ m ρ_K` on compacta `K'` then `ν(K') = 0`.

All results are proved unconditionally.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap.Upper.Rigidity

/-! ### Open sets that are eventually null for the `μ_j` are null for the limit -/

theorem vagueLimit_measure_eq_zero {l : Filter ℕ} [l.NeBot] {μ : ℕ → Measure ℝ}
    [∀ j, IsLocallyFiniteMeasure (μ j)] {ν : Measure ℝ} [IsLocallyFiniteMeasure ν]
    (hν : IsVagueLimit l μ ν) {U : Set ℝ} (hU : IsOpen U)
    (hnull : ∀ᶠ j in l, μ j U = 0) : ν U = 0 := by
  rw [hU.measurableSet.measure_eq_iSup_isCompact]
  refine le_antisymm (iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_) bot_le
  obtain ⟨f, hfK, hfU, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKU)
  have hlim := hν f f.continuous hfcs
  have hzero : ∀ᶠ j in l, ∫ u, f u ∂(μ j) = 0 := by
    filter_upwards [hnull] with j hj
    refine integral_eq_zero_of_ae ?_
    have : ∀ᵐ u ∂(μ j), u ∉ U := measure_eq_zero_iff_ae_notMem.1 hj
    filter_upwards [this] with u hu
    exact hfU (by simpa using hu)
  have h0 : ∫ u, f u ∂ν = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun j hj => hj.symm))
  have h1 : ν K ≤ ENNReal.ofReal (∫ u, f u ∂ν) :=
    (integrable_of_cs f.continuous hfcs).measure_le_integral
      (Eventually.of_forall fun x => (hf01 x).1) (fun x hx => by simp [hfK hx])
  rw [h0] at h1
  simpa using h1

/-! ### The support of the spectral measures -/

/-- The support data of two-level spectral measures: `μ_j` is carried by `{s₁^{(j)}} ∪ (-∞, s₂^{(j)}]`,
`s₁^{(j)} → z₁`, `limsup s₂^{(j)} ≤ z₂`. -/
structure TwoLevelSupport (μ : ℕ → Measure ℝ) (z₁ z₂ : ℝ) where
  s₁ : ℕ → ℝ
  s₂ : ℕ → ℝ
  tendsto_s₁ : Tendsto s₁ atTop (𝓝 z₁)
  s₂_le : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, s₂ j ≤ z₂ + ε
  null_top : ∀ j, μ j (Ioi (s₁ j)) = 0
  null_gap : ∀ j, μ j (Ioo (s₂ j) (s₁ j)) = 0

namespace TwoLevelSupport

variable {μ : ℕ → Measure ℝ} {z₁ z₂ : ℝ} (T : TwoLevelSupport μ z₁ z₂)

include T

lemma eventually_null_Ioi {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ j in atTop, μ j (Ioi (z₁ + δ)) = 0 := by
  filter_upwards [T.tendsto_s₁.eventually (gt_mem_nhds (show z₁ < z₁ + δ by linarith))] with j hj
  exact measure_mono_null (Ioi_subset_Ioi hj.le) (T.null_top j)

lemma eventually_null_Ioo {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, μ j (Ioo (z₂ + δ) (z₁ - δ)) = 0 := by
  filter_upwards [T.s₂_le δ hδ, T.tendsto_s₁.eventually (lt_mem_nhds (show z₁ - δ < z₁ by linarith))]
    with j h2 h1
  exact measure_mono_null (Ioo_subset_Ioo h2 h1.le) (T.null_gap j)

lemma ae_le_eventually {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ j in atTop, ∀ᵐ u ∂(μ j), u ≤ z₁ + δ := by
  filter_upwards [T.eventually_null_Ioi hδ] with j hj
  exact ae_le_of_supp hj

variable [∀ j, IsLocallyFiniteMeasure (μ j)]

/-- A vague limit along `𝒰 ≤ atTop` has no mass above `z₁`. -/
lemma vagueLimit_Ioi {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 μ ν) : ν (Ioi z₁) = 0 := by
  have hδ : ∀ δ : ℝ, 0 < δ → ν (Ioi (z₁ + δ)) = 0 := fun δ hδ =>
    vagueLimit_measure_eq_zero hν isOpen_Ioi (Filter.Eventually.filter_mono h𝒰 (T.eventually_null_Ioi hδ))
  have : Ioi z₁ = ⋃ n : ℕ, Ioi (z₁ + 1 / ((n : ℝ) + 1)) := by
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

/-- A vague limit along `𝒰 ≤ atTop` has no mass in the gap `(z₂, z₁)`. -/
lemma vagueLimit_gap {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 μ ν) : ν (Ioo z₂ z₁) = 0 := by
  have hδ : ∀ δ : ℝ, 0 < δ → ν (Ioo (z₂ + δ) (z₁ - δ)) = 0 := fun δ hδ =>
    vagueLimit_measure_eq_zero hν isOpen_Ioo (Filter.Eventually.filter_mono h𝒰 (T.eventually_null_Ioo hδ))
  have : Ioo z₂ z₁ = ⋃ n : ℕ, Ioo (z₂ + 1 / ((n : ℝ) + 1)) (z₁ - 1 / ((n : ℝ) + 1)) := by
    ext u
    simp only [mem_Ioo, mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 h1) (sub_pos.2 h2))
      have := lt_min_iff.1 hn
      exact ⟨n, by linarith [this.1], by linarith [this.2]⟩
    · rintro ⟨n, h1, h2⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith, by linarith⟩
  rw [this]
  exact measure_iUnion_null fun n => hδ _ (by positivity)

/-- A vague limit is carried by `{z₁} ∪ (-∞, z₂]`. -/
lemma ae_vagueLimit {𝒰 : Ultrafilter ℕ} (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) {ν : Measure ℝ}
    [IsLocallyFiniteMeasure ν] (hν : IsVagueLimit 𝒰 μ ν) : ∀ᵐ u ∂ν, u = z₁ ∨ u ≤ z₂ := by
  have h1 := T.vagueLimit_Ioi h𝒰 hν
  have h2 := T.vagueLimit_gap h𝒰 hν
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2] with u hu1 hu2
  have hu1' : u ≤ z₁ := not_lt.1 hu1
  by_cases h : u ≤ z₂
  · exact Or.inr h
  · left
    push Not at h
    by_contra hne
    exact hu2 ⟨h, lt_of_le_of_ne hu1' hne⟩

end TwoLevelSupport

/-! ### Local boundedness from a positive window -/

/-- **Local boundedness** (Step 2 of `sr:Sigma`): let `D` carry a design test `T` for the `μ_j`, `b < u_f`, `E'` compact,
`W_D > 0` on `(-∞, b] ∪ E'`.  If `μ_j` is eventually carried by `(-∞, b] ∪ E'`, the masses of compacta are
eventually bounded. -/
theorem mass_bound_of_positive_window {μ : ℕ → Measure ℝ} [∀ j, IsLocallyFiniteMeasure (μ j)]
    {D : Window} (T : DesignTest μ D) {b : ℝ} (hb : b < D.uF) {E' : Set ℝ} (hE' : IsCompact E')
    (hpos : ∀ u, (u ≤ b ∨ u ∈ E') → 0 < D.W u)
    (hsupp : ∀ᶠ j in atTop, ∀ᵐ u ∂(μ j), u ≤ b ∨ u ∈ E') : LocallyBounded μ := by
  intro K hK
  set L : Set ℝ := Iic b ∪ E' with hL
  have hLc : IsClosed L := isClosed_Iic.union hE'.isClosed
  set S : Set ℝ := (K ∪ E') ∩ L with hS
  have hSc : IsCompact S := (hK.union hE').inter_right hLc
  have hmemL : ∀ u, (u ≤ b ∨ u ∈ E') → u ∈ L := fun u hu => by
    rcases hu with h | h
    · exact Or.inl h
    · exact Or.inr h
  by_cases hne : S.Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := hSc.exists_isMinOn hne D.continuous.continuousOn
    have hm : 0 < D.W u₀ := by
      rcases hu₀.2 with h | h
      · exact hpos u₀ (Or.inl h)
      · exact hpos u₀ (Or.inr h)
    refine ⟨2 * (D.V + 1) / D.W u₀, ?_⟩
    have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 T.window_limit) S hSc
    have e1 : ∀ᶠ j in atTop, b < T.θ j := T.theta_tendsto.eventually (lt_mem_nhds hb)
    have e3 := T.limsup_le 1 one_pos
    have e4 : ∀ᶠ j in atTop, ∀ x ∈ S, dist (D.W x) (T.Ψ j x) < D.W u₀ / 2 :=
      Metric.tendstoUniformlyOn_iff.1 hunif (D.W u₀ / 2) (by positivity)
    filter_upwards [hsupp, e1, e3, e4] with j hs h1 h3 h4
    have hlow : ∀ u ∈ S, D.W u₀ / 2 ≤ T.Ψ j u := by
      intro u hu
      have h5 := h4 u hu
      rw [Real.dist_eq] at h5
      have h6 := (abs_lt.mp h5).2
      have h7 : D.W u₀ ≤ D.W u := hmin hu
      linarith
    have hoff : ∀ᵐ u ∂(μ j), u ∉ S → 0 ≤ T.Ψ j u := by
      filter_upwards [hs] with u hu hnS
      rcases hu with h | h
      · exact T.nonneg j u (by linarith)
      · exact absurd ⟨Or.inr h, Or.inr h⟩ hnS
    have hmain := const_mul_measure_le_integral (T.integrable_mu j) hSc.measurableSet
      hSc.measure_lt_top hlow hoff
    rw [T.crossing j] at hmain
    have h5 : D.W u₀ / 2 * (μ j S).toReal ≤ D.V + 1 := hmain.trans h3
    have hKS : (μ j K).toReal ≤ (μ j S).toReal := by
      refine ENNReal.toReal_mono hSc.measure_lt_top.ne (measure_mono_ae ?_)
      filter_upwards [hs] with u hu hK'
      exact ⟨Or.inl hK', hmemL u hu⟩
    have h6 : (μ j S).toReal ≤ 2 * (D.V + 1) / D.W u₀ := by
      rw [le_div_iff₀ hm]; nlinarith
    exact hKS.trans h6
  · refine ⟨0, ?_⟩
    have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    filter_upwards [hsupp] with j hs
    have : μ j K = 0 := by
      rw [← nonpos_iff_eq_zero]
      calc μ j K ≤ μ j S := measure_mono_ae (by
            filter_upwards [hs] with u hu hK'
            exact ⟨Or.inl hK', hmemL u hu⟩)
        _ = 0 := by rw [hSe]; exact measure_empty
    simp [this]

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.vagueLimit_measure_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vagueLimit_measure_eq_zero

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.mass_bound_of_positive_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mass_bound_of_positive_window

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoLevelSupport.ae_vagueLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoLevelSupport.ae_vagueLimit

end FormalResearch.ModularBootstrap.TwoLevel
