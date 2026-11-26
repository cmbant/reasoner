/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctGT
public import FormalResearch.SignUncertainty.FctNSymbol
public import FormalResearch.SignUncertainty.FctPhysicalBudgetConcrete
public import FormalResearch.SignUncertainty.FctVacuumConcrete

/-!
# `hQ` of Lemma FCT.7b (b): reduction to `t`-symbol bounds of the three factors `r₀`, `e^v`, `1 + Δ_curv`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b) and (c): `Q̃(L) = r₀ e^v (1 + Δ_curv)(τ₀(L̃)) - 1`
(`vacP(L̃)/I_fl(L̃) - 1`, `I_osc^{H₀}/I_fl = r₀∘τ₀`, `stripR0_eq_div`).

`QTSym kind K4 αf` states the paper's `t`-level bounds, with one constant sequence `P` (independent of `c, ε`) and
`tm = τ₀(3δ_L/4)` (the left end of the range `t = τ₀(L̃)`, `L ≥ 3δ_L/2`):

* (R) `r₀ - 1 = O(t²)` and `r₀ = O(t^{-8})` with all `t`-derivatives (`|t^j ∂_t^j (r₀ - 1)| ≤ P_j min(t², 1)`,
  `|t^j ∂_t^j r₀| ≤ P_j min(1, t^{-8})`; `r₀` is even and smooth, `r₀(0) = 1`, `fct:comp-D` (1); decay of `H₀(it)`);
* (V) the same for `e^{v} - 1` on `t ≥ tm` (`fct:comp-D` (1): `|v^{(r)}| ≤ C_r τ₁^{2-r}`, `supp v ⊆ (-10τ₁, 10τ₁)`, `v(0) = 0`);
* (D) the same for `Δ_curv` on `t ≥ tm` (`fct:comp-D` (1) and `(fct:th-tail)`).

`hQ_of_QTSym`: `QTSym` implies `hQ` of `physR_symW_of_factors`.  The change of variable `L ↦ τ₀(L̃)`, the three class transfers
(`tTransfer_usym`) and the algebra `R₀E D - 1 = (R₀ - 1) + R₀(E - 1) + R₀E(D - 1)` are proved; `QTSym` is the only input.

Class: proved under the explicit hypothesis `QTSym` (three `t`-symbol statements about explicit functions).
-/

@[expose] public section

open Set Filter Topology
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctMoment

/-- **The `t`-symbol inputs of Lemma FCT.7b (b)** (see the module docstring). -/
def QTSym (kind : StripKernelChoice) (K4 : ℝ) (αf : ℝ → ℝ → ℝ) : Prop :=
  ∃ (c₀ : ℝ) (P : ℕ → ℝ), (∀ j, 0 ≤ P j) ∧
    (ContDiffOn ℝ ∞ (stripR0 kind) (Ioi 0) ∧
      (∀ j : ℕ, ∀ t : ℝ, 0 < t → |t ^ j * iteratedDeriv j (fun u => stripR0 kind u - 1) t| ≤ P j * min (t ^ 2) 1) ∧
      (∀ j : ℕ, ∀ t : ℝ, 0 < t → |t ^ j * iteratedDeriv j (fun u => stripR0 kind u - 0) t| ≤ P j * min 1 ((t ^ 8)⁻¹))) ∧
    ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (ContDiffOn ℝ ∞ (fun t => Real.exp (vTotal kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) t)) (Ioi 0) ∧
        (∀ j : ℕ, ∀ t : ℝ, tau0 (3 / 4 * physDelta c) ≤ t →
          |t ^ j * iteratedDeriv j (fun u => Real.exp (vTotal kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) u) - 1) t| ≤
            P j * min (t ^ 2) 1) ∧
        (∀ j : ℕ, ∀ t : ℝ, tau0 (3 / 4 * physDelta c) ≤ t →
          |t ^ j * iteratedDeriv j (fun u => Real.exp (vTotal kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) u) - 1) t| ≤
            P j * min 1 ((t ^ 8)⁻¹))) ∧
      (ContDiffOn ℝ ∞ (fun t => 1 + stripDeltaCurv c (fctThetaD (v0 kind K4 (c ^ (-(1 / 4 : ℝ))))) t) (Ioi 0) ∧
        (∀ j : ℕ, ∀ t : ℝ, tau0 (3 / 4 * physDelta c) ≤ t →
          |t ^ j * iteratedDeriv j (stripDeltaCurv c (fctThetaD (v0 kind K4 (c ^ (-(1 / 4 : ℝ)))))) t| ≤
            P j * min (t ^ 2) 1) ∧
        (∀ j : ℕ, ∀ t : ℝ, tau0 (3 / 4 * physDelta c) ≤ t →
          |t ^ j * iteratedDeriv j (stripDeltaCurv c (fctThetaD (v0 kind K4 (c ^ (-(1 / 4 : ℝ)))))) t| ≤
            P j * min 1 ((t ^ 8)⁻¹)))

/-- The factorisation `vacP(L)/I_fl(L) = e^{v(t)} r₀(t) (1 + Δ_curv(t))`, `t = τ₀(L)`, `L > 0`. -/
lemma vacP_div_Ifl (kind : StripKernelChoice) (K4 c α τ₁ : ℝ) {L : ℝ} (hL : 0 < L) :
    vacP kind K4 c α τ₁ L / uctIfl L =
      Real.exp (vTotal kind K4 c α τ₁ (tau0 L)) * stripR0 kind (tau0 L) *
        (1 + stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁)) (tau0 L)) := by
  have h := stripR0_eq_div (kind := kind) (tau0_pos hL)
  rw [ceEll_tau0 hL |> fun e => (show uctM (tau0 L) = L from e)] at h
  have hfl : uctIfl L ≠ 0 := by
    unfold uctIfl
    exact (mul_pos uctAlphaFl_pos (Real.rpow_pos_of_pos hL _)).ne'
  unfold vacP stripIoscD
  rw [h]
  field_simp


/-- The base parameters `(ε, c)`. -/
structure QPar where
  ε : ℝ
  c : ℝ

/-- **`hQ` from `QTSym`** (see the module docstring). -/
theorem hQ_of_QTSym (kind : StripKernelChoice) (K4 : ℝ) (αf : ℝ → ℝ → ℝ) (hQT : QTSym kind K4 αf) :
    ∃ (c₀ MQ : ℝ) (KQ : ℕ → ℝ), 0 ≤ MQ ∧ ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      SymW (Ici (3 / 2 * physDelta c)) (pw MQ (-1) 0) KQ
        (fun x => vacP kind K4 c (αf ε c) (c ^ (-(1 / 4 : ℝ))) (x - physShift ε c) /
          uctIfl (x - physShift ε c) - 1) := by
  obtain ⟨c₁, P, hP, ⟨hRsm, hRS2, hRL8⟩, hVD⟩ := hQT
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales (fun ε c => ctDelta5 ε c) ⟨0, 0, fun ε c _ _ => by simp⟩
  obtain ⟨M, hM0, hT⟩ := tTransfer_usym P hP 1 zero_le_one
  set H : QPar → Prop := fun q => (q.ε = 1 ∨ q.ε = -1) ∧ max cs c₁ ≤ q.c with hH
  -- scales
  have hsc' : ∀ q, H q → 0 < physDelta q.c ∧ |physShift q.ε q.c| ≤ 3 / 2 * physDelta q.c / 2 ∧ 6 * physDelta q.c ≤ 1 := by
    intro q hq
    obtain ⟨h0, -, hs, -, -, -, -, -, h6⟩ := hsc q.ε q.c hq.1 ((le_max_left _ _).trans hq.2)
    exact ⟨h0, hs, h6⟩
  let tm : QPar → ℝ := fun q => tau0 (3 / 4 * physDelta q.c)
  let φR : QPar → GPar := fun q => ⟨stripR0 kind, 1, 0, physShift q.ε q.c, 3 / 2 * physDelta q.c, tm q⟩
  let φE : QPar → GPar := fun q => ⟨fun t => Real.exp (vTotal kind K4 q.c (αf q.ε q.c) (q.c ^ (-(1 / 4 : ℝ))) t), 1, 1,
    physShift q.ε q.c, 3 / 2 * physDelta q.c, tm q⟩
  let φD : QPar → GPar := fun q => ⟨fun t => 1 + stripDeltaCurv q.c (fctThetaD (v0 kind K4 (q.c ^ (-(1 / 4 : ℝ))))) t, 1, 1,
    physShift q.ε q.c, 3 / 2 * physDelta q.c, tm q⟩
  have hbasic : ∀ q, H q → 0 < 3 / 2 * physDelta q.c ∧ 3 / 2 * physDelta q.c ≤ 1 / 2 ∧
      |physShift q.ε q.c| ≤ 3 / 2 * physDelta q.c / 2 ∧ tm q ≤ tau0 (3 / 2 * physDelta q.c / 2) := by
    intro q hq
    obtain ⟨h0, hs, h6⟩ := hsc' q hq
    exact ⟨by linarith, by linarith, hs, le_of_eq (by simp only [tm]; congr 1; ring)⟩
  have hGR : ∀ q, H q → GHyp P 1 (φR q) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hbasic q hq
    refine ⟨hRsm, h1, h2, h3, (by show |(0 : ℝ) - 1| ≤ 1; norm_num), h4, fun j t ht => hRS2 j t ?_, fun j t ht => hRL8 j t ?_⟩ <;>
      exact lt_of_lt_of_le (tau0_pos (by linarith [(hsc' q hq).1])) ht
  have hGE : ∀ q, H q → GHyp P 1 (φE q) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hbasic q hq
    have hv := hVD q.ε q.c hq.1 ((le_max_right _ _).trans hq.2)
    exact ⟨hv.1.1, h1, h2, h3, (by show |(1 : ℝ) - 1| ≤ 1; norm_num), h4, hv.1.2.1, hv.1.2.2⟩
  have hGD : ∀ q, H q → GHyp P 1 (φD q) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hbasic q hq
    have hv := hVD q.ε q.c hq.1 ((le_max_right _ _).trans hq.2)
    have e : (fun u => (1 + stripDeltaCurv q.c (fctThetaD (v0 kind K4 (q.c ^ (-(1 / 4 : ℝ))))) u) - 1) =
        stripDeltaCurv q.c (fctThetaD (v0 kind K4 (q.c ^ (-(1 / 4 : ℝ))))) := by funext u; ring
    refine ⟨hv.2.1, h1, h2, h3, (by show |(1 : ℝ) - 1| ≤ 1; norm_num), h4, fun j t ht => ?_, fun j t ht => ?_⟩
    · show |t ^ j * iteratedDeriv j (fun u => (1 + stripDeltaCurv q.c (fctThetaD (v0 kind K4 (q.c ^ (-(1 / 4 : ℝ))))) u) - 1) t| ≤ _
      rw [e]; exact hv.2.2.1 j t ht
    · show |t ^ j * iteratedDeriv j (fun u => (1 + stripDeltaCurv q.c (fctThetaD (v0 kind K4 (q.c ^ (-(1 / 4 : ℝ))))) u) - 1) t| ≤ _
      rw [e]; exact hv.2.2.2 j t ht
  set S : QPar → Set ℝ := fun q => Ici (3 / 2 * physDelta q.c) with hS
  have hSpos : ∀ q, H q → ∀ x ∈ S q, 0 < x := fun q hq x hx => lt_of_lt_of_le (hbasic q hq).1 hx
  let fR : QPar → ℝ → ℝ := fun q x => stripR0 kind (tau0 (x - physShift q.ε q.c))
  let fE : QPar → ℝ → ℝ := fun q x =>
    Real.exp (vTotal kind K4 q.c (αf q.ε q.c) (q.c ^ (-(1 / 4 : ℝ))) (tau0 (x - physShift q.ε q.c)))
  let fD : QPar → ℝ → ℝ := fun q x =>
    1 + stripDeltaCurv q.c (fctThetaD (v0 kind K4 (q.c ^ (-(1 / 4 : ℝ))))) (tau0 (x - physShift q.ε q.c))
  have XR : USym H S (fun _ => pw M (-1) 0) (fun q x => fR q x - 1) := hT.comap φR hGR
  have XE : USym H S (fun _ => pw M (-1) 0) (fun q x => fE q x - 1) := hT.comap φE hGE
  have XD : USym H S (fun _ => pw M (-1) 0) (fun q x => fD q x - 1) := hT.comap φD hGD
  have one_add : ∀ {f : QPar → ℝ → ℝ}, USym H S (fun _ => pw M (-1) 0) (fun q x => f q x - 1) →
      USym H S (fun _ _ => 1 + M) f := by
    intro f hX
    have a1 := (USym.const (H := H) (S := S) hSpos (fun _ => (1 : ℝ))).of_le (w' := fun _ _ => 1 + M)
      (fun q hq x hx => by simp only [abs_one]; linarith)
    have a2 := hX.of_le (w' := fun _ _ => 1 + M) (fun q hq x hx => by
      have := pw_const_le (M := M) (α := -1) (β := 0) hM0 (by norm_num) le_rfl (hSpos q hq x hx)
      linarith)
    exact (a1.add a2).congr (U := fun _ => univ) (fun _ _ => isOpen_univ) (fun _ _ => subset_univ _)
      (fun q hq x hx => by simp only; ring)
  have fRu := one_add XR
  have fEu := one_add XE
  set M' : ℝ := M + (1 + M) * M + ((1 + M) * (1 + M)) * M with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have T1 := XR.of_le (w' := fun _ => pw M' (-1) 0) (fun q hq x hx =>
    pw_le_pw (by rw [hM']; nlinarith [mul_nonneg hM0 hM0]) hM0 le_rfl le_rfl (hSpos q hq x hx))
  have T2 := (fRu.mul XE).of_le (w' := fun _ => pw M' (-1) 0) (fun q hq x hx => by
    show (1 + M) * pw M (-1) 0 x ≤ pw M' (-1) 0 x
    rw [pw_smul]
    exact pw_le_pw (by rw [hM']; nlinarith [mul_nonneg hM0 hM0]) (by positivity) le_rfl le_rfl (hSpos q hq x hx))
  have T3 := ((fRu.mul fEu).mul XD).of_le (w' := fun _ => pw M' (-1) 0) (fun q hq x hx => by
    show (1 + M) * (1 + M) * pw M (-1) 0 x ≤ pw M' (-1) 0 x
    rw [pw_smul]
    exact pw_le_pw (by rw [hM']; nlinarith [mul_nonneg hM0 hM0]) (by positivity) le_rfl le_rfl (hSpos q hq x hx))
  have hsum := (T1.add T2).add T3
  have hfin := hsum.congr (U := fun q => Ioi (physShift q.ε q.c)) (fun _ _ => isOpen_Ioi)
    (fun q hq x hx => by
      have := (hsc' q hq).2.1
      have h0 := (hsc' q hq).1
      have hx' : 3 / 2 * physDelta q.c ≤ x := hx
      show physShift q.ε q.c < x
      linarith [(abs_le.mp this).2])
    (g := fun q x => vacP kind K4 q.c (αf q.ε q.c) (q.c ^ (-(1 / 4 : ℝ))) (x - physShift q.ε q.c) /
      uctIfl (x - physShift q.ε q.c) - 1) (fun q hq x hx => by
      have hxs : 0 < x - physShift q.ε q.c := sub_pos.mpr hx
      simp only [fR, fE, fD]
      rw [vacP_div_Ifl kind K4 q.c _ _ hxs]
      ring)
  obtain ⟨K, hK⟩ := hfin
  exact ⟨max cs c₁, M', K, hM'0, fun ε c hε hc => hK ⟨ε, c⟩ ⟨hε, hc⟩⟩

/-- info: 'FormalResearch.SignUncertainty.FctSym.hQ_of_QTSym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hQ_of_QTSym

end FormalResearch.SignUncertainty.FctSym
