/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctPhysicalBudgetConcrete
public import FormalResearch.SignUncertainty.FctHN

/-!
# `hR` of Lemma FCT.7b (b): reduction to the two factors (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`) (a), (b) and the first bullet of (c).

`hR` of `fctMainHankel_bump_fields_concrete` asks for `R - 1 ∈ (M_R, -1, 0)` on `[3δ_L/2, ∞)`, `R = O/F`, `O = I_osc^{warp}`
(`physOscDatum`), `F = (L̃/(L - L₁)) I_fl(L̃)` (`physF`), `L̃ = L - s`.  Unfolding the definitions (`fct:warp-asymp` (3)),
for `L̃ > 0`, `L ≠ L₁`:
`O/F = [P(L̃)/I_fl(L̃)] · [‖L̃ - L₁ Φ(L̃)‖/L̃]`, with `P = I_osc^{DH₀}(1 + Δ_curv ∘ τ₀)` (`vacP`) and `Φ = φ_kill(iτ₀(·); a)`.
So `R = (1 + Q̃)(1 + Ñ)` where

* `Q̃(L) = P(L̃)/I_fl(L̃) - 1 = r₀ e^v (1 + Δ_curv)(τ₀(L̃)) - 1` is the compensator-and-curvature factor of 7b (b);
* `Ñ(L) = ‖L̃ - L₁Φ(L̃)‖/L̃ - 1 = |1 - L₁ φ_kill(iτ₀(L̃); a)/L̃| - 1` is the `φ_kill` factor of 7b (a), fourth item.

`physR_symW_of_factors` proves `hR` from the **two named hypotheses** `hQ`, `hN` (each: `∈ (M, -1, 0)` on `[3δ_L/2, ∞)`, with
constants independent of `c`, the paper's `O_{K₄}(L^{1-r})`, resp. `C_r min(L^3, c^{-2/3}L^{-1}) L^{-r} ≤ C_r L^{1-r}`):
the classes are combined by the calculus of `FctSymCal` (`(1+Q̃)(1+Ñ) - 1 = Q̃ + Ñ + Q̃Ñ`, class arithmetic `(-1,0)+(-1,0)=(-2,0) ≤ (-1,0)`).
`hN` is **proved** (`hN_physical`, `FctHN.lean`: `τ₀'/τ₀` is a scale-invariant symbol, `FctTauA.lean`, composed with `φ_kill(it; a)`, `FctNSymbol.lean`);
`physR_symW_of_factors` is `physR_symW_of_QN` with it inserted, so `hQ` is the only remaining symbol-class input.

Class: proved under the explicit hypothesis `hQ` (and `hT1`, the size input of `physL1_le`).  Axiom guard at the end.
-/

@[expose] public section

open Set
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD FormalResearch.CohnElkies

/-- **`hR` from the two factors `hQ`, `hN`** (Lemma FCT.7b (b); see the module docstring; the algebra of `physR_symW_of_factors`).  `Q̃`, `Ñ` are the two factors of
`R = O/F` for the physical datum; `hT1` is the size input `T₁ = Δ₅ + O(c⁻¹)` of `physL1_le`, giving `|s|, |L₁| ≤ 3δ_L/4`. -/
theorem physR_symW_of_QN (kind : StripKernelChoice) (K4 : ℝ) (T1 αf : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹)
    (hQ : ∃ (c₀ MQ : ℝ) (KQ : ℕ → ℝ), 0 ≤ MQ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MQ (-1) 0) KQ
        (fun x => vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) (x - physShift ε c) / uctIfl (x - physShift ε c) - 1))
    (hN : ∃ (c₀ MN : ℝ) (KN : ℕ → ℝ), 0 ≤ MN ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MN (-1) 0) KN
        (fun x => ‖((x - physShift ε c : ℝ) : ℂ) - (physL1 T1 ε c : ℂ) * vacPhi (c ^ (-(1 / 12 : ℝ))) (x - physShift ε c)‖ /
          (x - physShift ε c) - 1)) :
    ∃ (c₀ MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MR (-1) 0) KR
        (fun x => physOscDatum kind K4 T1 αf ε c x / physF (physShift ε c) (physL1 T1 ε c) x - 1) := by
  obtain ⟨cQ, MQ, KQ, hMQ, hQ⟩ := hQ
  obtain ⟨cN, MN, KN, hMN, hN⟩ := hN
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  refine ⟨max cs (max cQ cN), MQ + MN + MQ * MN,
    fun r => (KQ r + KN r) + SymW.Kmul KQ KN r, by positivity, fun ε c hε hc => ?_⟩
  have hcs' : cs ≤ c := (le_max_left _ _).trans hc
  have hcQ : cQ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hcN : cN ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  obtain ⟨hδ0, -, hs, hL1, -, -, -, -, -⟩ := hsc ε c hε hcs'
  have hQc := hQ ε c hε hcQ
  have hNc := hN ε c hε hcN
  clear hsc hQ hN
  generalize physDelta c = δ at *
  have hxpos : ∀ x ∈ Ici (3 / 2 * δ), 0 < x := fun x hx => by have : 3 / 2 * δ ≤ x := hx; linarith
  have hM1 : MQ ≤ MQ + MN + MQ * MN := by nlinarith [mul_nonneg hMQ hMN]
  have hM2 : MN ≤ MQ + MN + MQ * MN := by nlinarith [mul_nonneg hMQ hMN]
  have hQ' := hQc.of_le (w' := pw (MQ + MN + MQ * MN) (-1) 0) (K' := KQ) (fun x hx =>
    pw_le_pw hM1 hMQ le_rfl le_rfl (hxpos x hx)) (fun _ => le_rfl)
  have hN' := hNc.of_le (w' := pw (MQ + MN + MQ * MN) (-1) 0) (K' := KN) (fun x hx =>
    pw_le_pw hM2 hMN le_rfl le_rfl (hxpos x hx)) (fun _ => le_rfl)
  have hP := (hQc.mul hNc).of_le (w' := pw (MQ + MN + MQ * MN) (-1) 0) (K' := SymW.Kmul KQ KN) (fun x hx => by
    rw [pw_mul _ _ _ _ _ _ x (hxpos x hx)]
    exact pw_le_pw (M := MQ * MN) (M' := MQ + MN + MQ * MN) (α := -1 + -1) (α' := -1) (β := 0 + 0) (β' := 0)
      (by nlinarith [mul_nonneg hMQ hMN]) (mul_nonneg hMQ hMN) (by norm_num) (by norm_num) (hxpos x hx))
    (fun _ => le_rfl)
  have hsum := (hQ'.add hN').add hP
  refine hsum.congr (U := Ioi δ) isOpen_Ioi (fun x hx => ?_) (fun x hx => ?_)
  · have : 3 / 2 * δ ≤ x := hx
    exact lt_of_lt_of_le (by linarith) this
  · have hxδ : δ < x := hx
    have hu : 0 < x - physShift ε c := by linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    have hxL : 0 < x - physL1 T1 ε c := by linarith [(abs_le.mp hL1).2]
    have hfl : 0 < uctIfl (x - physShift ε c) := by
      unfold uctIfl
      exact mul_pos uctAlphaFl_pos (Real.rpow_pos_of_pos hu _)
    simp only [physOscDatum, physOsc, physF]
    generalize physShift ε c = s at *
    generalize physL1 T1 ε c = L1 at *
    field_simp
    ring

/-- **`hR` from the compensator-and-curvature factor `hQ` alone** (Lemma FCT.7b (b)): the `φ_kill` factor `hN` (7b (a), fourth item) is
proved (`hN_physical`).  `hT1` is the size input `T₁ = Δ₅ + O(c⁻¹)` of `physL1_le`. -/
theorem physR_symW_of_factors (kind : StripKernelChoice) (K4 : ℝ) (T1 αf : ℝ → ℝ → ℝ)
    (hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹)
    (hQ : ∃ (c₀ MQ : ℝ) (KQ : ℕ → ℝ), 0 ≤ MQ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MQ (-1) 0) KQ
        (fun x => vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) (x - physShift ε c) / uctIfl (x - physShift ε c) - 1)) :
    ∃ (c₀ MR : ℝ) (KR : ℕ → ℝ), 0 ≤ MR ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MR (-1) 0) KR
        (fun x => physOscDatum kind K4 T1 αf ε c x / physF (physShift ε c) (physL1 T1 ε c) x - 1) :=
  physR_symW_of_QN kind K4 T1 αf hT1 hQ (hN_physical T1 hT1)

/-- **The fields `bump_profile` and `physical_budget` of `FctMainHankelInputs` for the concrete physical datum, with `hT` proved and `hR` replaced by
`hQ` alone** (`fctMainHankel_bump_fields_concrete` with `hR` derived from `hQ` by `physR_symW_of_factors`; `hN` is proved; `T₁ = I.T1`, `α = I.alpha`).
Remaining inputs: `hdef` (the definition `(fct:B-physical)`) and `hQ` (7b (b): `r₀ e^v (1 + Δ_curv) ∘ τ₀ - 1 ∈ (M, -1, 0)`). -/
theorem fctMainHankel_bump_fields_concrete_of_factors {χ : ℝ → ℝ} (hχ : IsCutoff χ) (kind : StripKernelChoice) {K4 : ℝ}
    (hK4 : 1 ≤ K4) (I : FctMainHankelInputs)
    (hdef : ∀ ε c K1 : ℝ, I.Bphys ε c K1 = physBump χ (1 / I.Nc ε c) c (physDelta c) (physShift ε c) K1 K4
      (physOscDatum kind K4 I.T1 I.alpha ε c) (physF (physShift ε c) (physL1 I.T1 ε c)) (fun L => tau0 L ^ 4 * uctIfl L))
    (hQ : ∃ (c₀ MQ : ℝ) (KQ : ℕ → ℝ), 0 ≤ MQ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MQ (-1) 0) KQ
        (fun x => vacP kind K4 c (I.alpha ε c) (c ^ (-(1 / 4 : ℝ))) (x - physShift ε c) /
          uctIfl (x - physShift ε c) - 1)) :
    type_of% I.bump_profile ∧ type_of% I.physical_budget := by
  obtain ⟨C, c₀, hw⟩ := I.warp_zero
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |I.T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨C, c₀, fun ε c hε hc => (hw ε c hε hc).1⟩
  exact fctMainHankel_bump_fields_concrete hχ kind hK4 I hdef
    (physR_symW_of_factors kind K4 I.T1 I.alpha hT1 hQ)

/-- info: 'FormalResearch.SignUncertainty.FctSym.fctMainHankel_bump_fields_concrete_of_factors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctMainHankel_bump_fields_concrete_of_factors

/-- info: 'FormalResearch.SignUncertainty.FctSym.physR_symW_of_QN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physR_symW_of_QN

/-- info: 'FormalResearch.SignUncertainty.FctSym.physR_symW_of_factors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physR_symW_of_factors

end FormalResearch.SignUncertainty.FctSym
