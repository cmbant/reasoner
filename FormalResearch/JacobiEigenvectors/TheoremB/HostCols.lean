module

public import Mathlib
public import FormalResearch.JB.JBOneStepDef
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B, L3.5b: `host0_col`, `host1_col` of every chart from `prop:tha-splice (c)`

Source: Paper J, `app_thmB` (I1) and `prop:tha-splice` (c) (`PropThaSpliceTwoOrders`).

`hostCols_of_twoOrders`: if `PropThaSpliceTwoOrders CP spl` holds (and the premises of `PropThbInputs`), there are `C ≥ 0` and `h₀ > 0` such that for `h ≤ h₀` every column `j` of the hosts `compMatrix CI0 spl` and `compMatrix CI1 (spl1 spl)` satisfies
`‖(host0 - U) e_j‖₂ ≤ C h^m` and `‖(host1 - U) e_j‖₂ ≤ C h^{m+1} log(1/h)` (the forms of `JB.Chart.Ok.host0_col`, `host1_col`; the host fields of a soft chart *are* these two matrices, for the actual splice `spl`, see `softUp_host0_eq_left`).
The columns bound `C * etaR m (m+1) h` of `PropThaSpliceTwoOrders` is `h^{m+1} log(1/h)` for even `m` and `h^{m+1}` for odd `m`; the latter is `≤ h^{m+1} log(1/h)` once `h ≤ e^{-1}`.

**Differences from the paper**: none.  **Not formalised**: the bulk charts' hosts at the *extreme* splices (they need `SplicesInWindow` for those splices: the bulk analogue is `BulkOneStep2`).
-/

@[expose] public section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

variable {Par : Type*} [TopologicalSpace Par]
variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

theorem etaR_next_le {m : ℕ} {h : ℝ} (hh : 0 < h) (hl : Real.exp (-1) ≥ h) :
    etaR m (m + 1) h ≤ h ^ (m + 1) * Real.log (1 / h) := by
  have hlog : 1 ≤ Real.log (1 / h) := by
    have : Real.exp 1 ≤ 1 / h := by
      rw [le_div_iff₀ hh]
      have := mul_le_mul_of_nonneg_left hl (Real.exp_pos 1).le
      rw [← Real.exp_add] at this
      simpa using this
    have h2 := Real.log_le_log (Real.exp_pos 1) this
    simpa using h2
  have hp : 0 < h ^ (m + 1) := pow_pos hh _
  unfold etaR
  rw [if_neg (by omega)]
  split_ifs
  · exact le_rfl
  · nlinarith

/-- **host0_col, host1_col from prop:tha-splice (c)**: see the module docstring. -/
theorem hostCols_of_twoOrders (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hS : PropThaSpliceTwoOrders CP spl) (hm : 1 ≤ m) (hK : Kidx = (m + 1) / 2) (hq : q = 2 * Kidx) (hKc : IsCompact K)
    (hH : HypOn F K) (hD : DM F K (2 * Kidx + 1)) (hs : CP.SplicesInWindow spl) :
    ∃ C h0 : ℝ, 0 ≤ C ∧ 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1),
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI0 spl μ N Xs i j - Um i j) ≤ C * F.step N ^ m ∧
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i j - Um i j) ≤
            C * F.step N ^ (m + 1) * Real.log (1 / F.step N) := by
  obtain ⟨C, h0, hh0, H⟩ := hS hm hK hq hKc hH hD hs
  refine ⟨max C 0, min h0 (Real.exp (-1)), le_max_right _ _, lt_min hh0 (Real.exp_pos _), fun μ hμ N hN ht Xs Um hE j => ?_⟩
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  obtain ⟨c0, c1⟩ := H μ hμ N (hN.trans (min_le_left _ _)) ht Xs Um hE j
  have hCm : C ≤ max C 0 := le_max_left _ _
  have hp1 : 0 < F.step N ^ m := pow_pos hpos _
  have hp2 : 0 < F.step N ^ (m + 1) := pow_pos hpos _
  refine ⟨?_, ?_⟩
  · refine c0.trans ?_
    unfold etaR
    rw [if_pos rfl]
    exact mul_le_mul_of_nonneg_right hCm hp1.le
  · refine c1.trans ?_
    have e := etaR_next_le (m := m) hpos (hN.trans (min_le_right _ _))
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    calc C * etaR m (m + 1) (F.step N) ≤ max C 0 * etaR m (m + 1) (F.step N) := by
          refine mul_le_mul_of_nonneg_right hCm ?_
          unfold etaR
          rw [if_neg (by omega)]
          split_ifs
          · have h1 : F.step N ≤ Real.exp (-1) := hN.trans (min_le_right _ _)
            have h2 : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.2 (by norm_num)
            rw [Real.exp_zero] at h2
            have h3 : 1 ≤ 1 / F.step N := by
              rw [le_div_iff₀ hpos]; linarith
            have := Real.log_nonneg h3
            positivity
          · positivity
      _ ≤ max C 0 * (F.step N ^ (m + 1) * Real.log (1 / F.step N)) := mul_le_mul_of_nonneg_left e hC0
      _ = _ := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.hostCols_of_twoOrders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.hostCols_of_twoOrders

end FormalResearch.JacobiEigenvectors.TheoremB

end
