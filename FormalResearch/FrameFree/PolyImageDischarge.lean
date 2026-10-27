import FormalResearch.FrameFree.ZClosureDischarge
import FormalResearch.FrameFree.PolyImageAll

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate InnerProductSpace BigOperators
open FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

/-!
# `PolyImageClosure` discharged

Namespace `FormalResearch.FrameFree.SupportRate`.  `PolyImageClosure` (`ZClosureDischarge`), the Euclidean density of
a polynomial image in its Zariski closure, is proved in `PolyImageAll` (Chevalley, Noether normalization, a
norm argument, and the continuity of roots of a monic polynomial; no dimension theory).  This file removes the
hypothesis from the consequences recorded in `ZClosureDischarge`: `SupportRateUpper` and `cor:calibrated`.
-/

namespace FormalResearch.FrameFree.SupportRate

/-- **Euclidean density of a polynomial image in its Zariski closure** (proved). -/
theorem polyImageClosure : PolyImageClosure :=
  fun _ _ Φ z h => PolyImage.polyImageClosure_all Φ z h

theorem zClosureSup {n : ℕ} (ψ : Ψ n) : ZClosureSup ψ :=
  zClosureSup_of_polyImageClosure polyImageClosure ψ

/-- **`SupportRateUpper`** (hard half of `thm:supportrate`), unconditional. -/
theorem supportRateUpper {n : ℕ} (ψ : Ψ n) : Helstrom.SupportRateUpper ψ :=
  supportRateUpper_of_polyImageClosure polyImageClosure ψ

/-- **`cor:calibrated`**, unconditional. -/
theorem tendsto_of_calibrated {n : ℕ} (ψ : Ψ n) (hψ : nsq ψ = 1) (hcal : Ceilings.FCΘ ψ = FKΘ ψ) :
    Filter.Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (Pe k ψ)) Filter.atTop (nhds (CK ψ)) :=
  tendsto_of_calibrated_of_polyImageClosure polyImageClosure ψ hψ hcal

end FormalResearch.FrameFree.SupportRate
