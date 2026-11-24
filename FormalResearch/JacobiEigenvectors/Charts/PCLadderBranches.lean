module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCLadder
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvCompact
public import FormalResearch.JacobiEigenvectors.Charts.PCOrigin

/-!
# Paper J, charts (WP1a): the PC ladder for the actual branch pairs of patches 2 and 3

`pc_symplecticLadder` (`Charts/PCLadder.lean`) takes the derivative, ODE and Wronskian facts of a branch
pair as premises.  This file discharges them for the actual parabolic cylinder functions `pcU, pcV`:
* `pcMinus pcU pcV` (patch 2, the `-` pair of `lem:cha-PCenv`), both for `a ≤ 0` and `a > 0`;
* `pcSwap pcU pcV` (patch 3, the swapped pair of `app_thmA` Step 2).

So `pcMinus_symplecticLadder` and `pcSwap_symplecticLadder` are `SymplecticLadder`s with no premise
beyond the evenness of the shift (`charts.tex` `eq:cha-PC`).  The Wronskians are DLMF 12.2.10
(`pc_wronsk`) and 12.2.11 (`ut_neg_wronsk`, `a > 0`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Engine

/-- `g` solves `g'' = (z²/4 + a) g` with derivative `g'`. -/
def PCOdePair (a : ℝ) (g g' : ℝ → ℝ) : Prop :=
  (∀ z, HasDerivAt g (g' z) z) ∧ ∀ z, HasDerivAt g' ((z ^ 2 / 4 + a) * g z) z

lemma PCOdePair.deriv_eq {a : ℝ} {g g' : ℝ → ℝ} (h : PCOdePair a g g') : deriv g = g' :=
  funext fun z => (h.1 z).deriv

lemma PCOdePair.ladder_facts {a : ℝ} {g g' : ℝ → ℝ} (h : PCOdePair a g g') :
    (∀ z, HasDerivAt g (deriv g z) z) ∧ ∀ z, HasDerivAt (deriv g) ((z ^ 2 / 4 + a) * g z) z := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [h.deriv_eq]; exact h.1 z
  · rw [h.deriv_eq]; exact h.2 z

lemma pcOdePair_U (a c : ℝ) : PCOdePair a (fun z => c * pcU a z) (fun z => c * pcUD a z) :=
  ⟨fun z => (hasDerivAt_pcU a z).const_mul c,
   fun z => ((hasDerivAt_pcUD a z).const_mul c).congr_deriv (by ring)⟩

lemma pcOdePair_V (a c : ℝ) : PCOdePair a (fun z => c * pcV a z) (fun z => c * pcVD a z) :=
  ⟨fun z => (hasDerivAt_pcV a z).const_mul c,
   fun z => ((hasDerivAt_pcVD a z).const_mul c).congr_deriv (by ring)⟩

lemma pcOdePair_U_neg (a c : ℝ) :
    PCOdePair a (fun z => c * pcU a (-z)) (fun z => -(c * pcUD a (-z))) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · have h := ((hasDerivAt_pcU a (-z)).comp z (hasDerivAt_neg z)).const_mul c
    exact h.congr_deriv (by simp [Function.comp_def]; ring)
  · have h := (((hasDerivAt_pcUD a (-z)).comp z (hasDerivAt_neg z)).const_mul c).neg
    exact h.congr_deriv (by simp [Function.comp_def]; ring)

lemma pcOdePair_V_neg (a c : ℝ) :
    PCOdePair a (fun z => c * pcV a (-z)) (fun z => -(c * pcVD a (-z))) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · have h := ((hasDerivAt_pcV a (-z)).comp z (hasDerivAt_neg z)).const_mul c
    exact h.congr_deriv (by simp [Function.comp_def]; ring)
  · have h := (((hasDerivAt_pcVD a (-z)).comp z (hasDerivAt_neg z)).const_mul c).neg
    exact h.congr_deriv (by simp [Function.comp_def]; ring)

/-- The constant of `vt`. -/
private def cV (a : ℝ) : ℝ := Real.sqrt (Real.pi / 2) * (kappaBal a)⁻¹

private lemma kappaBal_mul_cV (a : ℝ) :
    kappaBal a * cV a * Real.sqrt (2 / Real.pi) = 1 := by
  have hκ := (kappaBal_pos a).ne'
  have hpi : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  calc kappaBal a * cV a * Real.sqrt (2 / Real.pi)
      = (kappaBal a * (kappaBal a)⁻¹) * (Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi)) := by
        unfold cV; ring
    _ = 1 := by rw [mul_inv_cancel₀ hκ, hpi, one_mul]

private lemma pcU_wronsk' (a z : ℝ) :
    pcU a z * pcVD a z - pcUD a z * pcV a z = Real.sqrt (2 / Real.pi) := by
  simpa [deriv_pcU, deriv_pcV] using pc_wronsk a z

/-! ### The branch pairs as explicit functions -/

lemma pcMinus_zero_eq (a : ℝ) : pcMinus pcU pcV a 0 = fun z => kappaBal a * pcU a (-z) := by
  funext z; by_cases ha : a ≤ 0 <;> simp [pcMinus, ha, ut]

lemma pcMinus_one_eq_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    pcMinus pcU pcV a 1 = fun z => -cV a * pcV a (-z) := by
  funext z; simp [pcMinus, ha, vt, cV]

lemma pcMinus_one_eq_of_pos {a : ℝ} (ha : 0 < a) :
    pcMinus pcU pcV a 1 = fun z => -kappaBal a * pcU a z := by
  funext z; simp [pcMinus, not_le.mpr ha]

lemma pcSwap_zero_eq_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    pcSwap pcU pcV a 0 = fun z => cV a * pcV a z := by
  funext z; simp [pcSwap, ha, vt, cV]

lemma pcSwap_zero_eq_of_pos {a : ℝ} (ha : 0 < a) :
    pcSwap pcU pcV a 0 = fun z => kappaBal a * pcU a (-z) := by
  funext z; simp [pcSwap, not_le.mpr ha]

lemma pcSwap_one_eq (a : ℝ) : pcSwap pcU pcV a 1 = fun z => -kappaBal a * pcU a z := by
  funext z; by_cases ha : a ≤ 0 <;> simp [pcSwap, ha, ut]

/-! ### ODE facts -/

lemma pcMinus_odePair (α : Fin 2) (a : ℝ) :
    ∃ g', PCOdePair a (pcMinus pcU pcV a α) g' := by
  fin_cases α
  · exact ⟨_, (pcMinus_zero_eq a) ▸ pcOdePair_U_neg a (kappaBal a)⟩
  · by_cases ha : a ≤ 0
    · exact ⟨_, (pcMinus_one_eq_of_nonpos ha) ▸ pcOdePair_V_neg a (-cV a)⟩
    · exact ⟨_, (pcMinus_one_eq_of_pos (not_le.mp ha)) ▸ pcOdePair_U a (-kappaBal a)⟩

lemma pcSwap_odePair (α : Fin 2) (a : ℝ) :
    ∃ g', PCOdePair a (pcSwap pcU pcV a α) g' := by
  fin_cases α
  · by_cases ha : a ≤ 0
    · exact ⟨_, (pcSwap_zero_eq_of_nonpos ha) ▸ pcOdePair_V a (cV a)⟩
    · exact ⟨_, (pcSwap_zero_eq_of_pos (not_le.mp ha)) ▸ pcOdePair_U_neg a (kappaBal a)⟩
  · exact ⟨_, (pcSwap_one_eq a) ▸ pcOdePair_U a (-kappaBal a)⟩

/-! ### Wronskians -/

lemma pcMinus_wronsk (a z : ℝ) :
    pcMinus pcU pcV a 0 z * deriv (pcMinus pcU pcV a 1) z -
      deriv (pcMinus pcU pcV a 0) z * pcMinus pcU pcV a 1 z = 1 := by
  rw [pcMinus_zero_eq, (pcOdePair_U_neg a (kappaBal a)).deriv_eq]
  by_cases ha : a ≤ 0
  · rw [pcMinus_one_eq_of_nonpos ha, (pcOdePair_V_neg a (-cV a)).deriv_eq]
    have hw := pcU_wronsk' a (-z)
    calc kappaBal a * pcU a (-z) * -(-cV a * pcVD a (-z)) -
          -(kappaBal a * pcUD a (-z)) * (-cV a * pcV a (-z))
        = kappaBal a * cV a * (pcU a (-z) * pcVD a (-z) - pcUD a (-z) * pcV a (-z)) := by ring
      _ = 1 := by rw [hw, kappaBal_mul_cV]
  · have hpos : 0 < a := not_le.mp ha
    rw [pcMinus_one_eq_of_pos hpos, (pcOdePair_U a (-kappaBal a)).deriv_eq]
    have hw := ut_neg_wronsk hpos.le z
    rw [← kappaBal_eq_kappaBalPos hpos] at hw
    have hd : deriv (fun w => pcU a (-w)) z = -pcUD a (-z) := by
      simpa using congrFun (pcOdePair_U_neg a 1).deriv_eq z
    rw [hd, deriv_pcU] at hw
    calc kappaBal a * pcU a (-z) * (-kappaBal a * pcUD a z) -
          -(kappaBal a * pcUD a (-z)) * (-kappaBal a * pcU a z)
        = kappaBal a * pcU a z * (kappaBal a * -pcUD a (-z)) -
            kappaBal a * pcUD a z * (kappaBal a * pcU a (-z)) := by ring
      _ = 1 := hw

lemma pcSwap_wronsk (a z : ℝ) :
    pcSwap pcU pcV a 0 z * deriv (pcSwap pcU pcV a 1) z -
      deriv (pcSwap pcU pcV a 0) z * pcSwap pcU pcV a 1 z = 1 := by
  by_cases ha : a ≤ 0
  · rw [pcSwap_zero_eq_of_nonpos ha, pcSwap_one_eq, (pcOdePair_V a (cV a)).deriv_eq,
      (pcOdePair_U a (-kappaBal a)).deriv_eq]
    have hw := pcU_wronsk' a z
    calc cV a * pcV a z * (-kappaBal a * pcUD a z) - cV a * pcVD a z * (-kappaBal a * pcU a z)
        = kappaBal a * cV a * (pcU a z * pcVD a z - pcUD a z * pcV a z) := by ring
      _ = 1 := by rw [hw, kappaBal_mul_cV]
  · have hpos : 0 < a := not_le.mp ha
    have h0 : pcSwap pcU pcV a 0 = pcMinus pcU pcV a 0 := by
      rw [pcSwap_zero_eq_of_pos hpos, pcMinus_zero_eq]
    have h1 : pcSwap pcU pcV a 1 = pcMinus pcU pcV a 1 := by
      rw [pcSwap_one_eq, pcMinus_one_eq_of_pos hpos]
    rw [h0, h1]; exact pcMinus_wronsk a z

/-! ### The ladders -/

/-- **The PC ladder of patch 2 (`charts.tex` `eq:cha-PC`) for the actual `-` pair `pcMinus pcU pcV`**:
a `SymplecticLadder` for every coordinate `ζ` and even shift `μh`, with no further premise. -/
theorem pcMinus_symplecticLadder {γ : ℝ} (ζ μh : ℝ → ℝ) (hμ_even : ∀ h, μh (-h) = μh h)
    {pp qq : ℝ → ℝ → ℝ} :
    SymplecticLadder γ ddPC d2PC pp qq (pcPiP ζ μh) (pcPiM ζ μh) (wPC (pcMinus pcU pcV) ζ μh)
      Real.sqrt :=
  pc_symplecticLadder ζ μh hμ_even (pcMinus pcU pcV)
    (fun α a z => ((pcMinus_odePair α a).choose_spec.ladder_facts).1 z)
    (fun α a z => ((pcMinus_odePair α a).choose_spec.ladder_facts).2 z)
    pcMinus_wronsk

/-- **The PC ladder of patch 3 (`charts.tex` `eq:cha-PC`) for the actual swapped pair `pcSwap pcU pcV`**:
a `SymplecticLadder` for every coordinate `ζ` and even shift `μh`, with no further premise. -/
theorem pcSwap_symplecticLadder {γ : ℝ} (ζ μh : ℝ → ℝ) (hμ_even : ∀ h, μh (-h) = μh h)
    {pp qq : ℝ → ℝ → ℝ} :
    SymplecticLadder γ ddPC d2PC pp qq (pcPiP ζ μh) (pcPiM ζ μh) (wPC (pcSwap pcU pcV) ζ μh)
      Real.sqrt :=
  pc_symplecticLadder ζ μh hμ_even (pcSwap pcU pcV)
    (fun α a z => ((pcSwap_odePair α a).choose_spec.ladder_facts).1 z)
    (fun α a z => ((pcSwap_odePair α a).choose_spec.ladder_facts).2 z)
    pcSwap_wronsk

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcMinus_symplecticLadder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pcMinus_symplecticLadder

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcSwap_symplecticLadder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pcSwap_symplecticLadder

end FormalResearch.JacobiEigenvectors.Charts
