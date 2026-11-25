module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyLower
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeDt

/-!
# Paper J, Layer 2: the chart-level premises `hone`, `hzero` of `corEigenS1_of_windows` for the soft windows (L2.E)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (a) ("`Sigma_0 = S_0^{(t)}` and `Sigma_1 = 0` for the phase of every window"); `thm:smo-BSr`, "Soft windows" (`Sigma_+ = pi mu_0 + ...`, `pi mu_0 = S_0^{(t)}` near `X_s^+(t)`, eq:cha-mu0) and
the lower edge `Sigma_- = pi L - Sigma_+(-X, t, h)`.

## Proved here (axiom-pinned)

* `intervalIntegrable_arccos_of_continuousOn`: the `S_0` integrand `arccos((X - B_0)/(2 sqrt E_0))` is interval integrable for *any* continuous `G_0, B_0` (a bounded measurable function; no positivity of `G_0` is needed).
* `frozen_arccos_integrable`: the `S_0` integrand of the frozen symbols `G_0 + t G_1`, `B_0 + t B_1` is integrable for every `t` (from `(D_1)`).
* `softSigma_zero_eventually`: for `X` in the window and below `X_s^+(mu, 0)`, `Sigma_{+,0}(mu; X, t) = actionS0 Fz (mu, t) X` for all `t` near `0` (the chart's own `mu0_S0` at the parameter `(mu, t)`; `X <= X_s^+(mu, t)` for `t` near `0` by the continuity of `t -> X_s^+(mu, t)`, `SoftPhaseInputs.bandHi_reg`; the chart range `X_s^+(t) - X <= delta_0` by `bandHi_close` and `w + rho <= delta_0`).
* `softSigma_one`: `Sigma_{+,1} = 0` (odd index).
* `softLoSigma_zero_eventually`: the lower analogue, `Sigma_{-,0}(mu; X, t) = actionS0 (frozenFamily T Kidx) (mu, t) X` for `t` near `0`, via the mirror family: `mu0_S0` of the chart of `negFamily (frozenFamily T Kidx)` at `-X`, `actionS0_neg` (`arccos(-w) = pi - arccos w`)
  and `negFrozen_bandHi` (`X_s^+(negFamily) = -X_s^-`); the integrability the reflection needs is `intervalIntegrable_arccos_of_continuousOn` for the frozen symbols `G_0 + t G_1`, `B_0 + t B_1`.
* `softLoSigma_one`: `Sigma_{-,1} = 0`.

## Differences from the paper

None.  The paper's "near `t = 0`" is the filter `nhds 0`; the soft chart fields (`mu0_S0` at every `(mu, t)` of the chart's parameter set) are used as stated; no field was added to `SoftPhaseInputs`.

## Not formalised

The bulk analogue is `BulkPhaseInputs.Sigma_zero` / `Sigma_one`, used directly in `Assembly/ThmAi.lean` (`layer4_windows`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology MeasureTheory FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

variable {Par : Type*} [TopologicalSpace Par]

/-- The `S_0` integrand is interval integrable for continuous `G_0, B_0` (bounded by `pi`, measurable). -/
lemma intervalIntegrable_arccos_of_continuousOn {L : ℝ} (hL : 0 < L) {G0 B0 : ℝ → ℝ} (hG : ContinuousOn G0 (Icc 0 L))
    (hB : ContinuousOn B0 (Icc 0 L)) (X : ℝ) :
    IntervalIntegrable (fun u => Real.arccos ((X - B0 u) / (2 * Real.sqrt (E0 L G0 u)))) volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
  have hG' : AEMeasurable G0 (volume.restrict (Ioc 0 L)) :=
    (hG.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hB' : AEMeasurable B0 (volume.restrict (Ioc 0 L)) :=
    (hB.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hE : AEMeasurable (E0 L G0) (volume.restrict (Ioc 0 L)) := by
    have : E0 L G0 = fun s => s * (L - s) * G0 s := rfl
    rw [this]
    exact ((measurable_id.mul (measurable_const.sub measurable_id)).aemeasurable).mul hG'
  have hf : AEMeasurable (fun u => Real.arccos ((X - B0 u) / (2 * Real.sqrt (E0 L G0 u)))) (volume.restrict (Ioc 0 L)) :=
    Real.continuous_arccos.measurable.comp_aemeasurable
      ((aemeasurable_const.sub hB').div (aemeasurable_const.mul (Real.continuous_sqrt.measurable.comp_aemeasurable hE)))
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) := ⟨by simp⟩
  refine (integrable_const Real.pi).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have h0 := Real.arccos_nonneg ((X - B0 u) / (2 * Real.sqrt (E0 L G0 u)))
  have h1 := Real.arccos_le_pi ((X - B0 u) / (2 * Real.sqrt (E0 L G0 u)))
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- The `S_0` integrand of the frozen symbols `G_0 + t G_1`, `B_0 + t B_1` is interval integrable (`(H1)`, `(D_1)`: the jets `G_0, G_1, B_0, B_1` are continuous), for every `t`. -/
lemma frozen_arccos_integrable (T : SymbolFamily Par) (K : Set Par) (Kidx : ℕ) (hH : HypOn T K) (hD1 : DM T K 1) {μ : Par} (hμ : μ ∈ K) (t X : ℝ) :
    IntervalIntegrable (fun u => Real.arccos ((X - (frozenFamily T Kidx).B 0 (μ, t) u) /
      (2 * Real.sqrt (E0 (frozenFamily T Kidx).L ((frozenFamily T Kidx).G 0 (μ, t)) u)))) volume 0 (frozenFamily T Kidx).L := by
  obtain ⟨g, -, hG2, hB2, hG1, hB1⟩ := dm1_data T K hH hD1 hμ
  rw [frozen_G0, frozen_B0]
  exact intervalIntegrable_arccos_of_continuousOn (L := T.L) T.L_pos
    (hG2.continuousOn.add (continuousOn_const.mul hG1.continuousOn))
    (hB2.continuousOn.add (continuousOn_const.mul hB1.continuousOn)) X

section Soft

variable {Fz : SymbolFamily (Par × ℝ)} {K : Set Par} {t0 : ℝ} {M : ℕ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {C : SoftEdgeChart Fz (paramSet K t0) m q U V Lm}

/-- `Sigma_{+,1} = 0`. -/
lemma softSigma_one (μ : Par) (X t : ℝ) : softSigma C μ 1 X t = 0 := by
  simp [softSigma]

/-- **`Sigma_{+,0} = S_0^{(t)}` for small `t`** at an energy `X` of the window and below `X_s^+(mu, 0)`: the chart's `mu0_S0` at the parameter `(mu, t)`. -/
lemma softSigma_zero_eventually (SI : SoftPhaseInputs Fz (paramSet K t0) K t0 M C) (ht0 : 0 < t0) {μ : Par} (hμ : μ ∈ K) {X : ℝ}
    (hX : X ∈ Icc (Fz.bandHi (μ, 0) - SI.w) (Fz.bandHi (μ, 0) + SI.w)) (hlt : X < Fz.bandHi (μ, 0)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), softSigma C μ 0 X t = actionS0 Fz (μ, t) X := by
  have hnh : Icc (-t0) t0 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) ht0
  have hcont : ContinuousAt (fun t : ℝ => Fz.bandHi (μ, t)) 0 :=
    ((SI.bandHi_reg μ hμ).continuousOn).continuousAt hnh
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), X < Fz.bandHi (μ, t) := hcont.eventually (lt_mem_nhds hlt)
  filter_upwards [hnh, hev] with t ht hlt'
  have hmem : (μ, t) ∈ paramSet K t0 := ⟨hμ, ht⟩
  have hcl := abs_le.mp (SI.bandHi_close μ hμ t ht)
  have hδ : Fz.bandHi (μ, t) - X ≤ C.δ0 := by
    have := SI.window_in_chart
    linarith [hX.1, hcl.2]
  have h := C.mu0_S0 (μ, t) hmem X hlt'.le hδ
  have e : softSigma C μ 0 X t = Real.pi * C.muS 0 (μ, t) (Fz.bandHi (μ, t) - X) := by
    simp [softSigma]
  rw [e, h]
  rfl

end Soft

section Lower

variable {T : SymbolFamily Par} {K : Set Par} {t0 : ℝ} {M Kidx : ℕ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {C : SoftEdgeChart (negFamily (frozenFamily T Kidx)) (paramSet K t0) m q U V Lm}

/-- `Sigma_{-,1} = 0`. -/
lemma softLoSigma_one (L : ℝ) (μ : Par) (X t : ℝ) : softLoSigma L C μ 1 X t = 0 := by
  simp [softLoSigma, softSigma]

/-- **`Sigma_{-,0} = S_0^{(t)}` for small `t`** at an energy `X` of the lower window and above `X_s^-(mu)`, through the mirror family: `Sigma_{-,0}(X, t) = pi L - pi mu_0(-X)` and `pi mu_0 = S_0(negFamily)`, `S_0(negFamily, -X) = pi L - S_0(frozen, X)`.
The integrability of the frozen `S_0` integrand is the premise `hint` (continuity of the frozen symbols). -/
lemma softLoSigma_zero_eventually (SI : SoftPhaseInputs (negFamily (frozenFamily T Kidx)) (paramSet K t0) K t0 M C) (ht0 : 0 < t0)
    {μ : Par} (hμ : μ ∈ K) {X : ℝ} (hX : X ∈ Icc (T.bandLo μ - SI.w) (T.bandLo μ + SI.w)) (hlt : T.bandLo μ < X)
    (hint : ∀ t ∈ Icc (-t0) t0, IntervalIntegrable (fun u => Real.arccos ((X - (frozenFamily T Kidx).B 0 (μ, t) u) /
      (2 * Real.sqrt (E0 (frozenFamily T Kidx).L ((frozenFamily T Kidx).G 0 (μ, t)) u)))) volume 0 (frozenFamily T Kidx).L) :
    ∀ᶠ t in 𝓝 (0 : ℝ), softLoSigma T.L C μ 0 X t = actionS0 (frozenFamily T Kidx) (μ, t) X := by
  have hnh : Icc (-t0) t0 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) ht0
  have hb0 := negFrozen_bandHi_zero T Kidx μ
  have hcont : ContinuousAt (fun t : ℝ => (negFamily (frozenFamily T Kidx)).bandHi (μ, t)) 0 :=
    ((SI.bandHi_reg μ hμ).continuousOn).continuousAt hnh
  have hlt0 : -X < (negFamily (frozenFamily T Kidx)).bandHi (μ, 0) := by rw [hb0]; linarith
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), -X < (negFamily (frozenFamily T Kidx)).bandHi (μ, t) := hcont.eventually (lt_mem_nhds hlt0)
  filter_upwards [hnh, hev] with t ht hlt'
  have hmem : (μ, t) ∈ paramSet K t0 := ⟨hμ, ht⟩
  have hcl := abs_le.mp (SI.bandHi_close μ hμ t ht)
  rw [hb0] at hcl
  have hδ : (negFamily (frozenFamily T Kidx)).bandHi (μ, t) - (-X) ≤ C.δ0 := by
    have := SI.window_in_chart
    linarith [hX.2, hcl.2]
  have h := C.mu0_S0 (μ, t) hmem (-X) hlt'.le hδ
  have hS : Real.pi * C.muS 0 (μ, t) ((negFamily (frozenFamily T Kidx)).bandHi (μ, t) - -X) =
      actionS0 (negFamily (frozenFamily T Kidx)) (μ, t) (-X) := h
  have e : softSigma C μ 0 (-X) t = Real.pi * C.muS 0 (μ, t) ((negFamily (frozenFamily T Kidx)).bandHi (μ, t) - -X) := by
    simp [softSigma]
  have hneg := actionS0_neg (frozenFamily T Kidx) (μ, t) (-X) (by simpa using hint t ht)
  unfold softLoSigma
  rw [ite_eq_left rfl, e, hS, hneg, neg_neg]
  have hL : (frozenFamily T Kidx).L = T.L := rfl
  rw [hL]
  ring

end Lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.intervalIntegrable_arccos_of_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.intervalIntegrable_arccos_of_continuousOn

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.frozen_arccos_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.frozen_arccos_integrable

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softSigma_zero_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softSigma_zero_eventually

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_zero_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.softLoSigma_zero_eventually

end FormalResearch.JacobiEigenvectors.TheoremA
