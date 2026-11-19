module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ThmAAssemblySoft
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblySoft
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyLower
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero
public import FormalResearch.JacobiEigenvectors.TheoremA.NegTransport
public import FormalResearch.JacobiEigenvectors.TheoremB.NegColumns

/-!
# Paper J: the soft labels `SoftLabels` / `SoftLabelsLo` from the chart (thm:A (i), item 1)

Source: Paper J `thmA.tex`, proof of `thm:A (i)`, paragraph "Location and labels"; `Prop.thaW2` (3): the soft eigenvalues `X_i` within `delta_0` of the band end carry the label `i` and satisfy
`|X_i - X_s^+ - Sigma_i^{(h)}(...)| <= C h^{M+1}`; Step 0 (`stepZero`) supplies its premise `X_i <= X_s^+ + C_{s0} h^2`.

## Proved here (axiom-pinned)

* `softLabels_of_chart`: `SoftLabels T Kidx K M CI.softUpL` (the labelled soft rule of the upper band end) for every chart data `CI` of order `m >= max M 1`, `0 < t0`, and the standing assumption `StdAssump` of the
  frozen family at index `Kidx` (the paper's "`t_0` small").  It is `propThaW2_proved` (1)--(4) plus `stepZero`, with `h^{m+1} <= h^{M+1}` (`h <= 1`, `Lm = 1`).
* `softLabelsLo_of_chart`: the same for the lower band end, by transport along the negation `negFamily` (`NegTransport`, `NegColumns`).

## Differences from the paper

* The paper's "`t_0` small" is the premise `hstdK`, discharged by `stdAssump_trunc` / `ChartInputs.restrict` in the callers (`thmSmoSpec`).

## Not formalised

The Layer-4 phase `SoftPhaseInputs` (consumed by `softUpWindow`, `softLoWindow` after this module); the Layer-1 inputs behind the chart fields.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

section Labels

variable {T : SymbolFamily Par} {K : Set Par} {M Kidx m : ℕ} {t0 : ℝ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- `h^{m+1} <= h^{M+1}` for `h <= 1`, `M <= m`. -/
private lemma pow_le_pow_of_M {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) {M m : ℕ} (hM : M ≤ m) : h ^ (m + 1) ≤ h ^ (M + 1) :=
  pow_le_pow_of_le_one h0 h1 (by omega)

/-- **`SoftLabels` from `propThaW2_proved` and Step 0** (upper window): the labelled rule `PropThaW2 (3)` at the eigenvalues within `delta_0` of the band end (Step 0 supplies the premise `X_i <= X_s^+ + Cs0 h^2`;
`h^{m+1} <= h^{M+1}`, `Lm = 1`). -/
theorem softLabels_of_chart (CI : ChartInputs T K Kidx t0 m (2 * Kidx) U V cPC CPC) (ht0 : 0 < t0) (hm : 1 ≤ m) (hMm : M ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily T Kidx) (paramSet K t0) Kidx r) : SoftLabels T Kidx K M CI.softUpL := by
  obtain ⟨r, hr⟩ := hstdK
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero (frozenFamily T Kidx) (paramSet K t0) Kidx r hr
  have hr2 : StdAssump (frozenFamily T Kidx) (paramSet K t0) (2 * Kidx / 2) r := by rw [two_mul_div_two_nat]; exact hr
  obtain ⟨Cc, h0, clam, Clam, hh0, hclam, H⟩ :=
    propThaW2_proved CI.softUpL CI.softUpR Cs cPC CPC CI.pc hm (fun h _ _ => le_rfl) CI.mirror_up r hr2
  set n0 : ℕ := max CI.softUpL.N0 CI.softUpR.N0 with hn0
  refine ⟨|Cc|, min (min (min h0 hs0) (T.L / ((n0 : ℝ) + 1))) (min t0 1),
    lt_min (lt_min (lt_min hh0 hs0p) (div_pos T.L_pos (by positivity))) (lt_min ht0 one_pos), ?_⟩
  intro μ hμ N hN Xs Um hE i hi
  have hpos : 0 < T.step N := FormalResearch.JB.stepSize_pos T.L_pos N
  have hN1 : T.step N ≤ h0 := hN.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hN2 : T.step N ≤ hs0 := hN.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hN3 : T.step N ≤ T.L / ((n0 : ℝ) + 1) := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hNt : T.step N ≤ t0 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN4 : T.step N ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hn0N : n0 ≤ N := le_of_step_le hN3
  have hp : (μ, T.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  have hEf : IsEigenSystem ((frozenFamily T Kidx).jacobiMat (μ, T.step N) N) Xs Um := by
    rw [frozenFamily_jacobiMat_at_step]; exact hE
  have hS0 : ∀ j, Xs j ≤ (frozenFamily T Kidx).bandHi (μ, T.step N) + Cs * (frozenFamily T Kidx).step N ^ 2 :=
    fun j => (hsp (μ, T.step N) hp N hN2 Xs Um hEf j).2
  obtain ⟨-, hB, -⟩ := H (μ, T.step N) hp N hn0N hN1
  have := hB Xs Um hEf hS0 i hi
  simp only [mul_one] at this
  refine this.trans ?_
  have := pow_le_pow_of_M hpos.le hN4 hMm
  exact (mul_le_mul_of_nonneg_right (le_abs_self Cc) (pow_nonneg hpos.le _)).trans
    (mul_le_mul_of_nonneg_left this (abs_nonneg _))

/-- **`SoftLabelsLo`** (lower window): the same for the chart `softLoL` of `negFamily (frozenFamily T Kidx)`; Step 0 for the gauge family is `stepZero` for `negFamily (frozenFamily T Kidx)`
(`TheoremB.stdAssump_neg`). -/
theorem softLabelsLo_of_chart (CI : ChartInputs T K Kidx t0 m (2 * Kidx) U V cPC CPC) (ht0 : 0 < t0) (hm : 1 ≤ m) (hMm : M ≤ m)
    (hstdK : ∃ r, StdAssump (frozenFamily T Kidx) (paramSet K t0) Kidx r) : SoftLabelsLo T Kidx K M CI.softLoL := by
  obtain ⟨r, hr⟩ := hstdK
  have hrn : StdAssump (negFamily (frozenFamily T Kidx)) (paramSet K t0) Kidx r := TheoremB.stdAssump_neg hr
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero (negFamily (frozenFamily T Kidx)) (paramSet K t0) Kidx r hrn
  have hrn2 : StdAssump (negFamily (frozenFamily T Kidx)) (paramSet K t0) (2 * Kidx / 2) r := by rw [two_mul_div_two_nat]; exact hrn
  obtain ⟨Cc, h0, clam, Clam, hh0, hclam, H⟩ :=
    propThaW2_proved CI.softLoL CI.softLoR Cs cPC CPC CI.pc hm (fun h _ _ => le_rfl) CI.mirror_lo r hrn2
  set n0 : ℕ := max CI.softLoL.N0 CI.softLoR.N0 with hn0
  refine ⟨|Cc|, min (min (min h0 hs0) (T.L / ((n0 : ℝ) + 1))) (min t0 1),
    lt_min (lt_min (lt_min hh0 hs0p) (div_pos T.L_pos (by positivity))) (lt_min ht0 one_pos), ?_⟩
  intro μ hμ N hN Xs Um hE i hi
  have hpos : 0 < T.step N := FormalResearch.JB.stepSize_pos T.L_pos N
  have hN1 : T.step N ≤ h0 := hN.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hN2 : T.step N ≤ hs0 := hN.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hN3 : T.step N ≤ T.L / ((n0 : ℝ) + 1) := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hNt : T.step N ≤ t0 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN4 : T.step N ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hn0N : n0 ≤ N := le_of_step_le hN3
  have hp : (μ, T.step N) ∈ paramSet K t0 := ⟨hμ, ⟨by linarith, hNt⟩⟩
  have hS0 : ∀ j, Xs j ≤ (negFamily (frozenFamily T Kidx)).bandHi (μ, T.step N) + Cs * (negFamily (frozenFamily T Kidx)).step N ^ 2 :=
    fun j => (hsp (μ, T.step N) hp N hN2 Xs Um hE j).2
  obtain ⟨-, hB, -⟩ := H (μ, T.step N) hp N hn0N hN1
  have := hB Xs Um hE hS0 i hi
  simp only [mul_one] at this
  refine this.trans ?_
  have := pow_le_pow_of_M hpos.le hN4 hMm
  exact (mul_le_mul_of_nonneg_right (le_abs_self Cc) (pow_nonneg hpos.le _)).trans
    (mul_le_mul_of_nonneg_left this (abs_nonneg _))

end Labels

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLabels_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLabels_of_chart

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLabelsLo_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLabelsLo_of_chart

end FormalResearch.JacobiEigenvectors.TheoremA

end
