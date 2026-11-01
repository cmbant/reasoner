import FormalResearch.FourQubitEntropy.GOData.GOConst
import FormalResearch.FourQubitEntropy.GOGlue.Target

open Finset

namespace FormalResearch.FourQubitEntropy.GO
open GOProbe.PQ

set_option maxRecDepth 100000

/-- The scale `mapDen · grid` of `lit`. -/
def litScale : ℕ := GOProbe.mapDen * GOProbe.gridC

/-- `lit · (den_T den_R) = scale · (den_R · target - den_T · remainders)` as sorted sparse polynomials. -/
def identCheck : Bool :=
  GOProbe.eqSP (GOProbe.scaleSP ((pTarget.den * pRem.den : ℕ) : ℤ) GOProbe.lit)
    (GOProbe.sumSP [GOProbe.scaleSP ((litScale * pRem.den : ℕ) : ℤ) pTarget.p,
            GOProbe.scaleSP (-((litScale * pTarget.den : ℕ) : ℤ)) pRem.p])


theorem identCheck_true : identCheck = true := by native_decide

/-- `ev x lit = (mapDen · grid) (sliceTarget - R_sq - R_ax)` at every point. -/
theorem lit_ev (h : identCheck = true) (x : ℕ → ℝ) :
    GOProbe.ev x GOProbe.lit = (litScale : ℝ) * (sliceTarget (restr x) - (GOProbe.Rsq x + GOProbe.Rax x)) := by
  have e := GOProbe.eqSP_sound _ _ h
  have e2 := congrArg (GOProbe.ev x) e
  rw [GOProbe.ev_scaleSP, GOProbe.ev_sumSP] at e2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    GOProbe.ev_scaleSP] at e2
  have hT := pTarget_val x
  have hR := pRem_val x
  have dT : (pTarget.den : ℝ) ≠ 0 := by exact_mod_cast pTarget.hden.ne'
  have dR : (pRem.den : ℝ) ≠ 0 := by exact_mod_cast pRem.hden.ne'
  unfold GOProbe.PQ.val at hT hR
  rw [div_eq_iff dT] at hT
  rw [div_eq_iff dR] at hR
  push_cast at e2
  have hne : (pTarget.den : ℝ) * pRem.den ≠ 0 := mul_ne_zero dT dR
  apply mul_left_cancel₀ hne
  rw [e2, hT, hR]
  ring

end FormalResearch.FourQubitEntropy.GO
