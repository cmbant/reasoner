module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Metrizable.Urysohn

/-!
# Vague compactness of measures with a weighted mass budget (generic space)

The compactness engine behind `ds:farkas` and `ds:E` (`dual_spectrum.tex`): a family of positive
measures `μ_j` on a locally compact, second countable Hausdorff space `Y` with a *weighted budget*
`∫ w dμ_j ≤ C` (`w > 0` continuous) has, along every ultrafilter on the index type, a vague limit
`ν`, and the limit keeps

* the budget `∫ w dν ≤ C` (`IsVagueLimitAlong.lintegral_le`),
* every closed support condition `μ_j (Zᶜ) = 0` (`IsVagueLimitAlong.measure_open_eq_zero`), and
* every moment `∫ f dμ_j → ∫ f dν` of a continuous `f` which is small compared with `w` at infinity
  inside the common support `Z` (`IsVagueLimitAlong.tendsto_integral`).

Mathlib has no vague topology, so the limit is defined by `IsVagueLimitAlong` (continuous compactly
supported test functions) and obtained from Riesz–Markov–Kakutani, as in
`Upper.Rigidity.exists_vagueLimit` (which is the case `Y = ℝ`, index `ℕ`, of
`exists_vagueLimitAlong`).  Ultrafilters replace subsequence extraction.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Duality

section Generic

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {𝒥 : Type*}

/-- `ν` is a vague limit of `μ j` along `l`: `∫ g dμ_j → ∫ g dν` for every continuous `g` with
compact support. -/
def IsVagueLimitAlong (l : Filter 𝒥) (μ : 𝒥 → Measure Y) (ν : Measure Y) : Prop :=
  ∀ g : Y → ℝ, Continuous g → HasCompactSupport g →
    Tendsto (fun j => ∫ u, g u ∂(μ j)) l (𝓝 (∫ u, g u ∂ν))

omit [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y] [BorelSpace Y] in
lemma abs_integral_le_of_support' {μ : Measure Y} [IsFiniteMeasureOnCompacts μ] {g : Y → ℝ}
    (hcs : HasCompactSupport g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    |∫ u, g u ∂μ| ≤ B * (μ (tsupport g)).toReal := by
  have hK : IsCompact (tsupport g) := hcs
  have hfin : μ (tsupport g) < ∞ := hK.measure_lt_top
  have hzero : ∀ x ∉ tsupport g, g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := tsupport g) (f := g) hfin
    (C := B) (fun x _ => by simpa [Real.norm_eq_abs] using hB x)
  simpa [Real.norm_eq_abs, Measure.real] using this

omit [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y] in
lemma integrable_of_cs' {μ : Measure Y} [IsFiniteMeasureOnCompacts μ] {g : Y → ℝ}
    (hg : Continuous g) (hcs : HasCompactSupport g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport hcs

omit [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
private lemma exists_bound_of_cs' {g : Y → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hg
  exact ⟨max B 0, le_max_right _ _, fun x => by
    have := hB x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)⟩

omit [SecondCountableTopology Y] in
/-- **Vague compactness** along an ultrafilter `𝒰` on an arbitrary index type (the case `Y = ℝ`,
index `ℕ` is `Upper.Rigidity.exists_vagueLimit`): a family of locally finite measures with
uniformly bounded masses of compact sets has a locally finite vague limit. -/
theorem exists_vagueLimitAlong (μ : 𝒥 → Measure Y) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hbd : ∀ K : Set Y, IsCompact K → ∃ M : ℝ, ∀ j, (μ j K).toReal ≤ M) (𝒰 : Ultrafilter 𝒥) :
    ∃ ν : Measure Y, IsFiniteMeasureOnCompacts ν ∧ IsVagueLimitAlong (𝒰 : Filter 𝒥) μ ν := by
  classical
  have hex : ∀ g : CompactlySupportedContinuousMap Y ℝ,
      ∃ L : ℝ, Tendsto (fun j => ∫ u, g u ∂(μ j)) (𝒰 : Filter 𝒥) (𝓝 L) := by
    intro g
    obtain ⟨B, hB0, hB⟩ := exists_bound_of_cs' g.continuous g.hasCompactSupport
    obtain ⟨M, hM⟩ := hbd (tsupport g) g.hasCompactSupport
    have hbound : ∀ j, (∫ u, g u ∂(μ j)) ∈ Icc (-(B * max M 0)) (B * max M 0) := by
      intro j
      have h1 := abs_integral_le_of_support' (μ := μ j) g.hasCompactSupport hB
      have h2 : B * (μ j (tsupport g)).toReal ≤ B * max M 0 :=
        mul_le_mul_of_nonneg_left ((hM j).trans (le_max_left _ _)) hB0
      exact abs_le.mp (h1.trans h2)
    have hbound' : ∀ᶠ j in (𝒰 : Filter 𝒥), (∫ u, g u ∂(μ j)) ∈
        Icc (-(B * max M 0)) (B * max M 0) := Eventually.of_forall hbound
    have hle : (𝒰.map fun j => ∫ u, g u ∂(μ j) : Filter ℝ) ≤
        𝓟 (Icc (-(B * max M 0)) (B * max M 0)) := by
      rw [le_principal_iff]
      exact hbound'
    obtain ⟨x, -, hx⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map fun j => ∫ u, g u ∂(μ j)) hle
    exact ⟨x, hx⟩
  choose Λ₀ hΛ₀ using hex
  have hint : ∀ (j : 𝒥) (g : CompactlySupportedContinuousMap Y ℝ), Integrable g (μ j) :=
    fun j g => integrable_of_cs' g.continuous g.hasCompactSupport
  have hadd : ∀ f g : CompactlySupportedContinuousMap Y ℝ, Λ₀ (f + g) = Λ₀ f + Λ₀ g := by
    intro f g
    refine tendsto_nhds_unique (hΛ₀ (f + g)) ?_
    have := (hΛ₀ f).add (hΛ₀ g)
    refine this.congr fun j => ?_
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    rw [integral_add (hint j f) (hint j g)]
  have hsmul : ∀ (r : ℝ) (f : CompactlySupportedContinuousMap Y ℝ), Λ₀ (r • f) = r * Λ₀ f := by
    intro r f
    refine tendsto_nhds_unique (hΛ₀ (r • f)) ?_
    have := (hΛ₀ f).const_mul r
    refine this.congr fun j => ?_
    simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
  have hmono : ∀ f g : CompactlySupportedContinuousMap Y ℝ, f ≤ g → Λ₀ f ≤ Λ₀ g := by
    intro f g hfg
    refine le_of_tendsto_of_tendsto (hΛ₀ f) (hΛ₀ g) (Eventually.of_forall fun j => ?_)
    exact integral_mono (hint j f) (hint j g) (fun u => hfg u)
  let Λ : CompactlySupportedContinuousMap Y ℝ →ₚ[ℝ] ℝ :=
    { toFun := Λ₀
      map_add' := hadd
      map_smul' := fun r f => by simpa using hsmul r f
      monotone' := hmono }
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, fun g hg hcs => ?_⟩
  have h1 := RealRMK.integral_rieszMeasure Λ ⟨⟨g, hg⟩, hcs⟩
  have h2 := hΛ₀ ⟨⟨g, hg⟩, hcs⟩
  simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk] at h1 h2
  rw [h1]
  exact h2

variable {l : Filter 𝒥} {μ : 𝒥 → Measure Y} {ν : Measure Y}

/-- A vague limit gives zero mass to an open set which is eventually null for the `μ j`. -/
theorem IsVagueLimitAlong.measure_open_eq_zero [l.NeBot] [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) {U : Set Y} (hU : IsOpen U)
    (h0 : ∀ᶠ j in l, μ j U = 0) : ν U = 0 := by
  rw [hU.measure_eq_iSup_isCompact ν]
  refine le_antisymm (iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_) bot_le
  obtain ⟨f, hfK, hfU, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKU)
  have hlim := hν f f.continuous hfcs
  have hz : ∀ᶠ j in l, ∫ u, f u ∂(μ j) = 0 := by
    filter_upwards [h0] with j hj
    have hae : f =ᵐ[μ j] 0 := by
      have : ∀ᵐ x ∂μ j, x ∉ U := measure_eq_zero_iff_ae_notMem.1 hj
      filter_upwards [this] with x hx
      exact hfU (by simpa using hx)
    rw [integral_congr_ae hae]; simp
  have hlim0 : Tendsto (fun j => ∫ u, f u ∂(μ j)) l (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono fun j hj => hj.symm)
  have hν0 : ∫ u, f u ∂ν = 0 := tendsto_nhds_unique hlim hlim0
  have hint := integrable_of_cs' (μ := ν) f.continuous hfcs
  have h1 : ν K ≤ ENNReal.ofReal (∫ u, f u ∂ν) :=
    hint.measure_le_integral (Eventually.of_forall fun x => (hf01 x).1)
      (fun x hx => by simp [hfK hx])
  rw [hν0] at h1
  simpa using h1

/-- Compact sets exhaust `Y`; cut-off functions `φ_n` with `φ_n = 1` on the `n`-th compact set. -/
private lemma exists_cutoff_seq (Y : Type*) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] :
    ∃ φ : ℕ → C(Y, ℝ), (∀ n, HasCompactSupport (φ n)) ∧ (∀ n x, φ n x ∈ Icc (0 : ℝ) 1) ∧
      (∀ n, EqOn (φ n) 1 (compactCovering Y n)) := by
  have : ∀ n, ∃ f : C(Y, ℝ), EqOn f 1 (compactCovering Y n) ∧ HasCompactSupport f ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun n => by
    obtain ⟨f, h1, -, h3, h4⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_compactCovering Y n) isClosed_empty (disjoint_empty _)
    exact ⟨f, h1, h3, h4⟩
  choose φ h1 h2 h3 using this
  exact ⟨φ, h2, h3, h1⟩

/-- **Lower semicontinuity of a weighted budget**: if `∫ w dμ_j ≤ C` eventually along `l` and `ν` is
a vague limit, then `∫ w dν ≤ C` (`w ≥ 0` continuous). -/
theorem IsVagueLimitAlong.lintegral_le [l.NeBot] [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) {w : Y → ℝ}
    (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ j in l, ∫⁻ y, ENNReal.ofReal (w y) ∂(μ j) ≤ ENNReal.ofReal C) :
    ∫⁻ y, ENNReal.ofReal (w y) ∂ν ≤ ENNReal.ofReal C := by
  obtain ⟨φ, hφcs, hφ01, hφK⟩ := exists_cutoff_seq Y
  have hKmeas : ∀ n, MeasurableSet (compactCovering Y n) := fun n =>
    (isCompact_compactCovering Y n).isClosed.measurableSet
  have hF : Measurable fun y => ENNReal.ofReal (w y) := ENNReal.measurable_ofReal.comp hw.measurable
  have hstep : ∀ n, ∫⁻ y in compactCovering Y n, ENNReal.ofReal (w y) ∂ν ≤ ENNReal.ofReal C := by
    intro n
    have hwφ : Continuous fun y => w y * φ n y := hw.mul (φ n).continuous
    have hcs : HasCompactSupport fun y => w y * φ n y := (hφcs n).mul_left
    have hint_ν := integrable_of_cs' (μ := ν) hwφ hcs
    have hle1 : ∫⁻ y in compactCovering Y n, ENNReal.ofReal (w y) ∂ν ≤
        ∫⁻ y, ENNReal.ofReal (w y * φ n y) ∂ν := by
      rw [← lintegral_indicator (hKmeas n)]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ compactCovering Y n
      · simp [hy, hφK n hy]
      · simp [hy]
    have hlim := hν _ hwφ hcs
    have hle2 : ∀ᶠ j in l, ∫ y, w y * φ n y ∂(μ j) ≤ C := by
      filter_upwards [hb] with j hj
      have hint := integrable_of_cs' (μ := μ j) hwφ hcs
      have h1 : ENNReal.ofReal (∫ y, w y * φ n y ∂(μ j)) ≤ ENNReal.ofReal C := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun y => mul_nonneg (hw0 y) (hφ01 n y).1)]
        refine le_trans (lintegral_mono fun y => ?_) hj
        exact ENNReal.ofReal_le_ofReal (by nlinarith [hw0 y, (hφ01 n y).2])
      exact (ENNReal.ofReal_le_ofReal_iff hC).1 h1
    have hν_le : ∫ y, w y * φ n y ∂ν ≤ C := le_of_tendsto hlim hle2
    refine hle1.trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hint_ν
      (Eventually.of_forall fun y => mul_nonneg (hw0 y) (hφ01 n y).1)]
    exact ENNReal.ofReal_le_ofReal hν_le
  have hmono : Monotone fun n => (compactCovering Y n).indicator fun y => ENNReal.ofReal (w y) :=
    fun m n hmn y => indicator_le_indicator_of_subset (compactCovering_subset Y hmn)
      (fun _ => zero_le) y
  have hsup : (fun y => ENNReal.ofReal (w y)) =
      fun y => ⨆ n, (compactCovering Y n).indicator (fun y => ENNReal.ofReal (w y)) y := by
    funext y
    obtain ⟨n, hn⟩ := mem_iUnion.1 (iUnion_compactCovering Y ▸ mem_univ y)
    refine le_antisymm ?_ (iSup_le fun m => indicator_le_self' (fun _ _ => zero_le) y)
    exact le_iSup_of_le n (by simp [hn])
  rw [hsup, lintegral_iSup (fun n => hF.indicator (hKmeas n)) hmono]
  refine iSup_le fun n => ?_
  rw [lintegral_indicator (hKmeas n)]
  exact hstep n

/-- **Moments pass to a vague limit** under a weighted budget: let `μ_j`, `ν` be null outside the
set `Z`, with `∫ w dμ_j ≤ C` and `∫ w dν ≤ C`, and let `f` be continuous with `|f| ≤ ε w` on `Z`
outside a compact set (for every `ε > 0`).  Then `∫ f dμ_j → ∫ f dν` along `l`. -/
theorem IsVagueLimitAlong.tendsto_integral [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    [IsFiniteMeasureOnCompacts ν] (hν : IsVagueLimitAlong l μ ν) {Z : Set Y}
    (hμZ : ∀ᶠ j in l, μ j Zᶜ = 0) (hνZ : ν Zᶜ = 0) {w : Y → ℝ} (hw : Continuous w)
    (hw0 : ∀ y, 0 ≤ w y) {C : ℝ} (hC : 0 ≤ C)
    (hbμ : ∀ᶠ j in l, ∫⁻ y, ENNReal.ofReal (w y) ∂(μ j) ≤ ENNReal.ofReal C)
    (hbν : ∫⁻ y, ENNReal.ofReal (w y) ∂ν ≤ ENNReal.ofReal C) {f : Y → ℝ} (hf : Continuous f)
    (hdecay : ∀ ε > 0, ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ Z, y ∉ K → |f y| ≤ ε * w y) :
    Tendsto (fun j => ∫ u, f u ∂(μ j)) l (𝓝 (∫ u, f u ∂ν)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (4 * (C + 1)) := by positivity
  set δ := ε / (4 * (C + 1)) with hδdef
  obtain ⟨K, hK, hKdec⟩ := hdecay δ hδ
  obtain ⟨φ, hφK, -, hφcs, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty
    (disjoint_empty _)
  have hfφ : Continuous fun y => f y * φ y := hf.mul φ.continuous
  have hfφcs : HasCompactSupport fun y => f y * φ y := hφcs.mul_left
  have hlim := hν _ hfφ hfφcs
  -- integrability of `w` and the tail
  have hwint : ∀ (m : Measure Y), ∫⁻ y, ENNReal.ofReal (w y) ∂m ≤ ENNReal.ofReal C →
      Integrable w m := fun m hm => by
    refine ⟨hw.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hw0)]
    exact lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  have htail : ∀ (m : Measure Y) [IsFiniteMeasureOnCompacts m], m Zᶜ = 0 →
      ∫⁻ y, ENNReal.ofReal (w y) ∂m ≤ ENNReal.ofReal C →
      Integrable (fun y => f y * (1 - φ y)) m ∧
        |∫ y, f y * (1 - φ y) ∂m| ≤ δ * C := by
    intro m _ hmZ hbm
    have hmae : ∀ᵐ y ∂m, y ∈ Z := by
      have : ∀ᵐ y ∂m, y ∉ Zᶜ := measure_eq_zero_iff_ae_notMem.1 hmZ
      filter_upwards [this] with y hy using by simpa using hy
    have hbound : ∀ᵐ y ∂m, ‖f y * (1 - φ y)‖ ≤ δ * w y := by
      filter_upwards [hmae] with y hy
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hyK : y ∈ K
      · simp [hφK hyK, mul_nonneg hδ.le (hw0 y)]
      · have h1 := hKdec y hy hyK
        have h2 : |1 - φ y| ≤ 1 := by
          rw [abs_of_nonneg (by linarith [(hφ01 y).2])]; linarith [(hφ01 y).1]
        calc |f y| * |1 - φ y| ≤ |f y| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ δ * w y := by linarith
    have hwi := hwint m hbm
    have hint : Integrable (fun y => f y * (1 - φ y)) m :=
      (hwi.const_mul δ).mono' ((hf.mul (continuous_const.sub φ.continuous)).aestronglyMeasurable)
        hbound
    refine ⟨hint, ?_⟩
    calc |∫ y, f y * (1 - φ y) ∂m| ≤ ∫ y, ‖f y * (1 - φ y)‖ ∂m := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := m)
            (fun y => f y * (1 - φ y))
      _ ≤ ∫ y, δ * w y ∂m := integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (hwi.const_mul δ) hbound
      _ = δ * ∫ y, w y ∂m := integral_const_mul _ _
      _ ≤ δ * C := by
          refine mul_le_mul_of_nonneg_left ?_ hδ.le
          have := (ofReal_integral_eq_lintegral_ofReal hwi (Eventually.of_forall hw0)).trans_le hbm
          exact (ENNReal.ofReal_le_ofReal_iff hC).1 this
  have hsplit : ∀ (m : Measure Y) [IsFiniteMeasureOnCompacts m], m Zᶜ = 0 →
      ∫⁻ y, ENNReal.ofReal (w y) ∂m ≤ ENNReal.ofReal C →
      ∫ y, f y ∂m = ∫ y, f y * φ y ∂m + ∫ y, f y * (1 - φ y) ∂m := by
    intro m _ hmZ hbm
    have h1 := integrable_of_cs' (μ := m) hfφ hfφcs
    have h2 := (htail m hmZ hbm).1
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have hδC : δ * C ≤ ε / 4 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hε, hC]
  have hev := (Metric.tendsto_nhds.1 hlim) (ε / 2) (by positivity)
  filter_upwards [hev, hμZ, hbμ] with j hj hZj hbj
  rw [Real.dist_eq] at hj ⊢
  rw [hsplit (μ j) hZj hbj, hsplit ν hνZ hbν]
  have ht1 := (htail (μ j) hZj hbj).2
  have ht2 := (htail ν hνZ hbν).2
  have := abs_add_three ((∫ y, f y * φ y ∂(μ j)) - ∫ y, f y * φ y ∂ν)
    (∫ y, f y * (1 - φ y) ∂(μ j)) (-∫ y, f y * (1 - φ y) ∂ν)
  rw [abs_neg] at this
  have e : ∫ y, f y * φ y ∂(μ j) + ∫ y, f y * (1 - φ y) ∂(μ j) -
      (∫ y, f y * φ y ∂ν + ∫ y, f y * (1 - φ y) ∂ν) =
      ((∫ y, f y * φ y ∂(μ j)) - ∫ y, f y * φ y ∂ν) +
        ∫ y, f y * (1 - φ y) ∂(μ j) + -∫ y, f y * (1 - φ y) ∂ν := by ring
  rw [e]
  linarith

omit [SecondCountableTopology Y] [BorelSpace Y] [T2Space Y] [LocallyCompactSpace Y] in
/-- A continuous function dominated by `w` outside a compact set, inside `Z`, is integrable for a
measure with finite `w`-budget which is null outside `Z`. -/
lemma integrable_of_decay [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y] {m : Measure Y}
    [IsFiniteMeasureOnCompacts m] {Z : Set Y} (hZ : m Zᶜ = 0) {w : Y → ℝ} (hw : Continuous w)
    (hw0 : ∀ y, 0 ≤ w y) (hb : ∫⁻ y, ENNReal.ofReal (w y) ∂m < ∞) {f : Y → ℝ}
    (hf : Continuous f) (hdec : ∃ K : Set Y, IsCompact K ∧ ∀ y ∈ Z, y ∉ K → |f y| ≤ w y) :
    Integrable f m := by
  obtain ⟨K, hK, hKd⟩ := hdec
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hwi : Integrable w m := ⟨hw.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hw0)]; exact hb⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hdom : Integrable (fun y => w y + K.indicator (fun _ => M) y) m := by
    refine hwi.add ?_
    exact (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  refine hdom.mono' hf.aestronglyMeasurable ?_
  have hmae : ∀ᵐ y ∂m, y ∈ Z := by
    have : ∀ᵐ y ∂m, y ∉ Zᶜ := measure_eq_zero_iff_ae_notMem.1 hZ
    filter_upwards [this] with y hy using by simpa using hy
  filter_upwards [hmae] with y hy
  by_cases hyK : y ∈ K
  · have h1 := hM y hyK
    simp only [Real.norm_eq_abs] at h1 ⊢
    simp only [hyK, indicator_of_mem]
    linarith [hw0 y]
  · have h1 := hKd y hy hyK
    simp only [Real.norm_eq_abs] at h1 ⊢
    simp only [hyK, indicator_of_notMem, not_false_eq_true, add_zero]
    exact h1

end Generic

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_vagueLimitAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_vagueLimitAlong

/-- info: 'FormalResearch.ModularBootstrap.Duality.IsVagueLimitAlong.lintegral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.IsVagueLimitAlong.lintegral_le

/-- info: 'FormalResearch.ModularBootstrap.Duality.IsVagueLimitAlong.tendsto_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.IsVagueLimitAlong.tendsto_integral

/-- info: 'FormalResearch.ModularBootstrap.Duality.IsVagueLimitAlong.measure_open_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.IsVagueLimitAlong.measure_open_eq_zero

end FormalResearch.ModularBootstrap.Duality
