module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Vague limits of locally bounded sequences of measures on `ℝ`

Compactness input for Theorem `Σ` (`spectral_rigidity.tex`, Step 2).  Mathlib has no vague topology,
so a *vague limit along a filter `l`* is defined by `IsVagueLimit`: `∫ g dμ_j → ∫ g dν` along `l`
for every continuous compactly supported `g : ℝ → ℝ`.

* `exists_vagueLimit`: a sequence of locally finite measures on `ℝ` with locally bounded masses
  (`LocallyBounded`) has, along every ultrafilter `𝒰 ≤ atTop`, a vague limit `ν` (locally finite).
  Proof: the limits `Λ g = lim_𝒰 ∫ g dμ_j` exist because bounded real sequences converge along an
  ultrafilter; `Λ` is a positive linear functional on `C_c(ℝ, ℝ)`, and Riesz–Markov–Kakutani
  (`RealRMK.rieszMeasure`) gives `ν`.  (Ultrafilters replace the subsequence/diagonal extraction:
  `Filter.tendsto_iff_ultrafilter` turns "every ultrafilter limit is `μ_A`" into convergence of the
  whole sequence.)
* `abs_integral_le_of_support`: `|∫ g dμ| ≤ B μ(tsupport g)` for `|g| ≤ B`.
* `IsVagueLimit.measure_le`: for a compact `K` and an open `U ⊇ K`,
  `limsup μ_j(K) ≤ ν(U)` (portmanteau, in the form used for `x₁ ≥ 1`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

/-- `ν` is a vague limit of `μ j` along `l`: `∫ g dμ_j → ∫ g dν` for every continuous `g` with
compact support. -/
def IsVagueLimit (l : Filter ℕ) (μ : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
    Tendsto (fun j => ∫ u, g u ∂(μ j)) l (𝓝 (∫ u, g u ∂ν))

/-- The masses of compact sets are eventually bounded (uniformly in the compact set's choice only
through `K`). -/
def LocallyBounded (μ : ℕ → Measure ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → ∃ M : ℝ, ∀ᶠ j in atTop, (μ j K).toReal ≤ M

lemma abs_integral_le_of_support {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {g : ℝ → ℝ}
    (hcs : HasCompactSupport g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    |∫ u, g u ∂μ| ≤ B * (μ (tsupport g)).toReal := by
  have hK : IsCompact (tsupport g) := hcs
  have hfin : μ (tsupport g) < ∞ := hK.measure_lt_top
  have hzero : ∀ x ∉ tsupport g, g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := tsupport g) (f := g) hfin
    (C := B) (fun x _ => by simpa [Real.norm_eq_abs] using hB x)
  simpa [Real.norm_eq_abs, Measure.real] using this

lemma integrable_of_cs {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : Continuous g) (hcs : HasCompactSupport g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport hcs

private lemma exists_bound_of_cs {g : ℝ → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hg
  exact ⟨max B 0, le_max_right _ _, fun x => by
    have := hB x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)⟩

/-- **Vague compactness** (Step 2 of `sr:Sigma`): along every ultrafilter `𝒰 ≤ atTop`, a sequence of
locally finite measures with locally bounded masses has a locally finite vague limit. -/
theorem exists_vagueLimit (μ : ℕ → Measure ℝ) [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hbd : LocallyBounded μ) (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) :
    ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧ IsVagueLimit 𝒰 μ ν := by
  classical
  -- limits exist
  have hex : ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      ∃ L : ℝ, Tendsto (fun j => ∫ u, g u ∂(μ j)) 𝒰 (𝓝 L) := by
    intro g
    obtain ⟨B, hB0, hB⟩ := exists_bound_of_cs g.continuous g.hasCompactSupport
    obtain ⟨M, hM⟩ := hbd (tsupport g) g.hasCompactSupport
    have hM' : ∀ᶠ j in (𝒰 : Filter ℕ), (μ j (tsupport g)).toReal ≤ M := h𝒰 hM
    have hbound : ∀ᶠ j in (𝒰 : Filter ℕ),
        (∫ u, g u ∂(μ j)) ∈ Icc (-(B * max M 0)) (B * max M 0) := by
      filter_upwards [hM'] with j hj
      have h1 := abs_integral_le_of_support (μ := μ j) g.hasCompactSupport hB
      have h2 : B * (μ j (tsupport g)).toReal ≤ B * max M 0 :=
        mul_le_mul_of_nonneg_left (hj.trans (le_max_left _ _)) hB0
      exact abs_le.mp (h1.trans h2)
    have hle : (𝒰.map fun j => ∫ u, g u ∂(μ j) : Filter ℝ) ≤ 𝓟 (Icc (-(B * max M 0)) (B * max M 0)) := by
      rw [le_principal_iff]
      exact hbound
    obtain ⟨x, -, hx⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map fun j => ∫ u, g u ∂(μ j)) hle
    exact ⟨x, hx⟩
  choose Λ₀ hΛ₀ using hex
  have hint : ∀ (j : ℕ) (g : CompactlySupportedContinuousMap ℝ ℝ), Integrable g (μ j) :=
    fun j g => integrable_of_cs g.continuous g.hasCompactSupport
  have hadd : ∀ f g : CompactlySupportedContinuousMap ℝ ℝ, Λ₀ (f + g) = Λ₀ f + Λ₀ g := by
    intro f g
    refine tendsto_nhds_unique (hΛ₀ (f + g)) ?_
    have := (hΛ₀ f).add (hΛ₀ g)
    refine this.congr fun j => ?_
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    rw [integral_add (hint j f) (hint j g)]
  have hsmul : ∀ (r : ℝ) (f : CompactlySupportedContinuousMap ℝ ℝ), Λ₀ (r • f) = r * Λ₀ f := by
    intro r f
    refine tendsto_nhds_unique (hΛ₀ (r • f)) ?_
    have := (hΛ₀ f).const_mul r
    refine this.congr fun j => ?_
    simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
  have hmono : ∀ f g : CompactlySupportedContinuousMap ℝ ℝ, f ≤ g → Λ₀ f ≤ Λ₀ g := by
    intro f g hfg
    refine le_of_tendsto_of_tendsto (hΛ₀ f) (hΛ₀ g) (Eventually.of_forall fun j => ?_)
    exact integral_mono (hint j f) (hint j g) (fun u => hfg u)
  let Λ : CompactlySupportedContinuousMap ℝ ℝ →ₚ[ℝ] ℝ :=
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

/-- Portmanteau for vague limits: if `μ_j(K) ≥ b` eventually along `l` for a compact `K`, then
`ν(U) ≥ b` for every open `U ⊇ K`. -/
theorem IsVagueLimit.le_measure_of_eventually {l : Filter ℕ} [l.NeBot] {μ : ℕ → Measure ℝ}
    [∀ j, IsLocallyFiniteMeasure (μ j)] {ν : Measure ℝ}
    (hν : IsVagueLimit l μ ν) {K U : Set ℝ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {b : ℝ} (hb : ∀ᶠ j in l, b ≤ (μ j K).toReal) : ENNReal.ofReal b ≤ ν U := by
  obtain ⟨f, hfK, hfU, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
    (disjoint_compl_right_iff_subset.mpr hKU)
  have hlim := hν f f.continuous hfcs
  have hle : ∀ᶠ j in l, b ≤ ∫ u, f u ∂(μ j) := by
    filter_upwards [hb] with j hj
    have hint := integrable_of_cs (μ := μ j) f.continuous hfcs
    have h1 : μ j K ≤ ENNReal.ofReal (∫ u, f u ∂(μ j)) :=
      hint.measure_le_integral (Eventually.of_forall fun x => (hf01 x).1)
        (fun x hx => by simp [hfK hx])
    have hnn : 0 ≤ ∫ u, f u ∂(μ j) := integral_nonneg fun x => (hf01 x).1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal hnn] at this
    linarith
  have hb' : b ≤ ∫ u, f u ∂ν := ge_of_tendsto hlim hle
  calc ENNReal.ofReal b ≤ ENNReal.ofReal (∫ u, f u ∂ν) := ENNReal.ofReal_le_ofReal hb'
    _ ≤ ν U := integral_le_measure (fun x _ => (hf01 x).2) (fun x hx => by simp [hfU hx])

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.exists_vagueLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.exists_vagueLimit

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.IsVagueLimit.le_measure_of_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.IsVagueLimit.le_measure_of_eventually

end FormalResearch.ModularBootstrap.Upper.Rigidity
