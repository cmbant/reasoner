module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFarPhase
public import FormalResearch.SignUncertainty.CtBoasSigmaLip
public import FormalResearch.SignUncertainty.CtBoasPlbField
public import FormalResearch.SignUncertainty.CtBoasPointwise
public import FormalResearch.SignUncertainty.CtDyadicTaperChart
public import FormalResearch.SignUncertainty.FctVacuumField
public import FormalResearch.SignUncertainty.HankelBandAssembly

/-!
# `ct:boas-ineq`: measurability of the concrete band data

The regularity hypotheses of `BoasSetting` for the concrete objects of `ct:boas`: the phase `X = boasX c ε`
(`tau0` is monotone, `edgePhi L τ = Lτ + edgePhi 0 τ` with `edgePhi 0` continuous, `θ_ε` continuous), the frequency
`ν = boasNu c`, the taper `ctTaper ε c R` (monotone, from `TaperReg`), the Gaussian step `sf = 𝔰_far ∘ Δ`
(monotone: `sFar_eq_Iio`) and the weight `boasE c wt`.  **Proved**, unconditional.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies

lemma measurable_boasNu (c : ℝ) : Measurable (boasNu c) :=
  measurable_const.mul FctSym.tau0_measurable

lemma measurable_boasX (c ε : ℝ) : Measurable (boasX c ε) := by
  have h1 : Measurable fun L : ℝ => edgePhi L (tau0 L) := by
    have : (fun L : ℝ => edgePhi L (tau0 L)) = fun L => L * tau0 L + edgePhi 0 (tau0 L) := by
      funext L
      unfold edgePhi; ring
    rw [this]
    exact (measurable_id.mul FctSym.tau0_measurable).add (continuous_edgePhi_zero.measurable.comp FctSym.tau0_measurable)
  have h2 : Measurable fun L : ℝ => CtOuter.outerTheta ε (tau0 L) :=
    (CtOuter.contDiff_outerTheta ε).continuous.measurable.comp FctSym.tau0_measurable
  unfold boasX
  exact (measurable_const.mul h1).sub h2

lemma TaperReg.monotone_of_nonpos {wt : ℝ → ℝ} {A Kw : ℝ} (h : TaperReg wt A Kw) (h0 : ∀ L, L ≤ 0 → wt L = 0) :
    Monotone wt := by
  intro L L' hLL
  by_cases hL : L ≤ 0
  · rw [h0 L hL]; exact (h.mem L').1
  · exact h.mono L L' (not_le.1 hL) hLL

lemma measurable_ctTaper {ε c R A : ℝ} (I : TaperChartInputs ε c R A) : Measurable (ctTaper ε c R) :=
  (I.reg.monotone_of_nonpos fun _ hL => ctTaper_nonpos ε c R hL).measurable

lemma monotone_sFar_comp {c : ℝ} (hc : 1 < c) : Monotone fun L : ℝ => sFar c (c * (Real.exp L / π ^ 2)) := by
  have hW : 0 < farW c := by unfold farW; linarith
  intro L L' hLL
  simp only [sFar_eq_Iio]
  have hΔ : c * (Real.exp L / π ^ 2) ≤ c * (Real.exp L' / π ^ 2) := by
    have := Real.exp_le_exp.2 hLL
    gcongr
  refine setIntegral_mono_set ((integrable_gaussK hW).integrableOn) (ae_of_all _ fun y => gaussK_nonneg' _ _ hW)
    (ae_of_all _ fun y (hy : y ∈ Iio (c * (Real.exp L / π ^ 2) - farD c)) => ?_)
  show y ∈ Iio (c * (Real.exp L' / π ^ 2) - farD c)
  simp only [mem_Iio] at hy ⊢; linarith

lemma measurable_sFar_comp {c : ℝ} (hc : 1 < c) : Measurable fun L : ℝ => sFar c (c * (Real.exp L / π ^ 2)) :=
  (monotone_sFar_comp hc).measurable

lemma measurable_boasWf (c : ℝ) : Measurable (boasWf c) := by
  unfold boasWf
  exact (Measurable.sqrt (by fun_prop)).div (measurable_const.mul FctSym.tau0_measurable)

lemma measurable_boasE {c : ℝ} {wt : ℝ → ℝ} (hw : Measurable wt) : Measurable (boasE c wt) := by
  unfold boasE
  have hW := measurable_boasWf c
  refine hw.mul ?_
  exact ((((measurable_const.mul ((measurable_const.add (FctSym.tau0_measurable.pow_const 2)))).div
    FctSym.tau0_measurable).mul (hW.pow_const 2)).add (hW.div FctSym.tau0_measurable)).add
    (hW.div (measurable_id.min measurable_const))

end FormalResearch.SignUncertainty
