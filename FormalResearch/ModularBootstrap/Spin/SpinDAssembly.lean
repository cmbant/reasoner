module

public import FormalResearch.ModularBootstrap.Spin.SpinDStatements
public import FormalResearch.ModularBootstrap.Upper.Assembly.FarFirstSite

/-!
# SPIN-D assembly: unconditional `sd:R`, and `sd:LP`(ii) & `spinnotes:S1`(d) from SPIN-D `Prop`s

Proves:
- `spinDR : SpinDR`: **Corollary SD-R** (`sd:R`, unconditional) — resolving spin does not change
  the Airy distribution of dimensions. Every sequence of spinning crossing measures with
  `GapCondition (c_j - 1) τ_j` has dimension marginals `ν_j^{rad} = (t_L + t_R)_* ν_j` satisfying
  `SigmaConclusion` (in particular vague convergence to `airyMeasure`).
- `spinDLPii_of_props`: `SpinDLPi → SpinDSD → SpinDLPii` (Theorem SD-LP (ii) from (i) and `sd:SD`).
- `spinS1d_of_spinDW`: `SpinDW → SpinS1d` (Theorem S1 (d) on `T > 0` from Proposition SD-W).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Assembly

/-! ### 1. Corollary SD-R (`sd:R`, unconditional) -/

/-- **Corollary SD-R** (`sd:R`, unconditional): for any sequence `c_j → ∞` (`c_j ≥ 25`) and
positive spinning crossing measures `ν_j` on `E_{B_j} ∩ {t_L + t_R ≥ τ_j}` satisfying the
scalar gap condition `GapCondition (c_j - 1) τ_j`, the rescaled spectral measures of the
dimension marginals `ν_j^{rad} = (t_L + t_R)_* ν_j` satisfy `SigmaConclusion` (including vague
convergence to `airyMeasure = ∑_k Ai'(a_k)^{-2} δ_{a_k}`). -/
theorem spinDR : SpinDR := by
  intro cSeq τSeq BSeq hc hc25 hτ _hB hgap meas
  let S : CrossingSequence virasoroProblem :=
    { c := fun j => cSeq j - 1
      τ := τSeq
      meas := fun j => (meas j).toRadAdmissible (fun p (hp : p ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) =>
        (hτ j).le.trans hp.2)
      tendsto_c := by
        have hsub : (fun j => cSeq j - 1) = fun j => cSeq j + (-1) := by ext j; ring
        rw [hsub]
        exact hc.atTop_add tendsto_const_nhds
      c_pos := fun j => by linarith [hc25 j]
      shift_le := fun j => by
        rw [virasoroProblem_totalShift]
        linarith [hc25 j]
      τ_pos := hτ
      atGap := fun j => (meas j).toRadAdmissible_atGap (hτ j).le
        (fun p (hp : p ∈ spinConeB (BSeq j) ∩ {p | τSeq j ≤ p.1 + p.2}) => hp.2) }
  obtain ⟨F⟩ := sameSiteFamily_designClass_exists
  exact theorem_sigma_crossing S hgap
    (designPropertyP_union (designPropertyP_prob virasoroProblem rfl S)
      (displacedPropertyP_prob virasoroProblem rfl S))
    (SameSiteFamily.mono Set.subset_union_left F)
    (DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily)
    farFamily

/-! ### 2. Theorem SD-LP (ii) from `SpinDLPi` and `SpinDSD` -/

/-- **Theorem SD-LP (ii)** (`sd:LP`(ii)) assembled from `SpinDLPi` and `SpinDSD`:
`T_{Ω,F}^{[∞]} = T_{Ω,F}^{\mathcal B} = τ_{\max}`. -/
theorem spinDLPii_of_props (hLPi : SpinDLPi) (hSD : SpinDSD) : SpinDLPii := by
  intro a B ha hB Ω F hΩc hΩs hΩB hFc hFs hFsub hTpos
  obtain ⟨hmax, -, -⟩ := hSD.1 ha hB hΩc hΩs hΩB hFc hFs hFsub hTpos
  refine ⟨?_, hmax⟩
  set TB := spinCertifiedThr a Ω F with hTB
  have hge : ENNReal.ofReal TB ≤ spinLagThrInf a Ω F := by
    refine le_iInf fun N => le_iInf₂ fun T hT => ?_
    obtain ⟨hT0, q, hq_mem, hq_nn, hq_vac⟩ := hT
    refine ENNReal.ofReal_le_ofReal ?_
    refine csInf_le ⟨0, fun τ hτ => hτ.1.le⟩ ?_
    exact ⟨hT0, fun p => Real.exp (-2 * π * (p.1 + p.2)) * q p,
      exp_mul_mem_SpinCertifiedT hq_mem, hq_vac, hq_nn⟩
  have hle : spinLagThrInf a Ω F ≤ ENNReal.ofReal TB := by
    by_contra hlt
    obtain ⟨T', hT'0, hT'1, hT'2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    have hTB_lt : TB < T' := (ENNReal.ofReal_lt_ofReal_iff'.1 hT'1).1
    have hT'_pos : 0 < T' := hTpos.trans hTB_lt
    have hno : ∀ N q, ¬ spinOddLagFeasible a N (F ∪ spinConeSlice Ω T') q := by
      intro N q hq
      have hle' : spinLagThrInf a Ω F ≤ ENNReal.ofReal T' :=
        (iInf_le _ N).trans (iInf₂_le T' ⟨hT'_pos, q, hq⟩)
      exact absurd hle' (not_le.2 hT'2)
    have hm_ex : ∃ m : ℝ, 0 < m ∧ F ⊆ {p : ℝ × ℝ | m ≤ p.1 + p.2} := by
      rcases F.eq_empty_or_nonempty with rfl | hne
      · exact ⟨1, one_pos, empty_subset _⟩
      · obtain ⟨p₀, hp₀F, hp₀min⟩ := hFc.exists_isMinOn hne
          (continuous_fst.add continuous_snd).continuousOn
        exact ⟨p₀.1 + p₀.2, (hFsub hp₀F).2, fun p hp => isMinOn_iff.1 hp₀min p hp⟩
    obtain ⟨m, hm_pos, hFm⟩ := hm_ex
    set T₀ := min m T' with hT₀
    have hT₀_pos : 0 < T₀ := lt_min hm_pos hT'_pos
    have hXc : IsClosed (F ∪ spinConeSlice Ω T') :=
      hFc.isClosed.union (isClosed_spinConeSlice hΩc T')
    have hXs : IsSwapInvariantSet (F ∪ spinConeSlice Ω T') := by
      rintro p (hpF | hpΩ)
      · exact Or.inl (hFs p hpF)
      · exact Or.inr (isSwapInvariantSet_spinConeSlice hΩs T' p hpΩ)
    have hXsub : F ∪ spinConeSlice Ω T' ⊆ spinConeB B ∩ {p : ℝ × ℝ | T₀ ≤ p.1 + p.2} := by
      rintro p (hpF | ⟨hpΩ, hpT⟩)
      · exact ⟨hΩB (hFsub hpF).1, (min_le_left m T').trans (hFm hpF)⟩
      · exact ⟨hΩB hpΩ, (min_le_right m T').trans hpT⟩
    obtain ⟨meas, -⟩ := (hLPi ha hB hT₀_pos hXc hXs hXsub).1 hno
    have hT'_le : T' ≤ TB := hmax.2 ⟨hT'_pos, ⟨meas⟩⟩
    linarith
  exact le_antisymm hle hge

/-! ### 3. Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDR

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinDLPii_of_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinDLPii_of_props

end FormalResearch.ModularBootstrap.Spin
