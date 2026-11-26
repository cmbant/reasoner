/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctDJetDeriv
public import FormalResearch.SignUncertainty.FctDJetU
public import FormalResearch.SignUncertainty.FctChartAcomp

/-!
# `(fct:dJ-jets)` for the chart (F2a, `fct:comp-cfu`)

`ChartSetup.dJ_jets`, `ChartSetup.dJ_jets_A0`: the first two lines of `(fct:dJ-jets)` in one parameter direction `v`;
`ChartSetup.dJ_jets_u`, `ChartSetup.dJ_jets_u_A0`: the `ℓ`-derivative (third) line, in a second direction `u`, for the
amplitude `J = Jfun S.V H τ2` of the compensated chart: `|∂_Y^n (J(p₀+v) - J(p₀))| ≤ C_n |e| max(Y, A_0)^{max(0,4-n)}` (`n ≤ 13`).
The paper's `H = (1+G)^{1/2}` is any `C^{16}` function on an open set containing the range of `τ2 · Y V²`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section DJet
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace ChartSetup
variable (S : ChartSetup P)

lemma V_bounds {q : P × ℝ} (hq : q ∈ S.Ω ×ˢ Yint) : 9 / 10 ≤ S.V q ∧ S.V q ≤ 6 / 5 := by
  have h := S.D_bounds (q := (q.1, S.Z q)) ⟨hq.1, S.Z_mem hq⟩
  have hD0 : 0 < S.D (q.1, S.Z q) := by linarith [h.1]
  simp only [ChartSetup.V]
  constructor
  · rw [le_inv_comm₀ (by norm_num) hD0]; linarith [h.2]
  · rw [inv_le_comm₀ hD0 (by norm_num)]; linarith [h.1]

/-- `(fct:dJ-jets)`, first two lines, for the chart: segment `p₀ + t v` in the chart domain, `A ≥ 0` on it, `A ≤ A_max`. -/
theorem dJ_jets {β : ℝ} (hβ : 4 ≤ β) (v : P) (θ : P × ℝ → ℝ) (e : ℝ) {H : ℝ → ℝ} {T : Set ℝ} {τ2 : ℝ}
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    (hT : IsOpen T) (hH : JCΦ 16 T H (Φb^[3] β) 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ2 * (q.2 * S.V q ^ 2) ∈ T)
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ S.Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, S.A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => Jfun S.V H τ2 (p0 + v, s)) Y - iteratedDeriv n (fun s : ℝ => Jfun S.V H τ2 (p0, s)) Y| ≤
      |e| * CJ n (Φb^[3] β) * max Y Amax ^ (4 - n) := by
  have hβ3 : 4 ≤ Φb^[3] β := le_trans hβ (Φb_iter_ge 3 β)
  have hβ8 : 8 ≤ Φb^[3] β := by
    have h1 := Φb_ge2 β
    have h2 : Φb^[1] β ≤ Φb^[3] β := Φb_iter_mono (by norm_num) β
    have h3 : max 1 β = β := max_eq_right (by linarith)
    simp only [Function.iterate_one] at h2
    linarith
  have hV : JCΦ 16 (S.Ω ×ˢ Yint) S.V (Φb^[3] β) 0 := by
    have := (S.V_jc hβ).mono_m (show 1 ≤ 3 by norm_num)
    simpa [JCΦ] using this
  have hA : JCΦ 16 S.Ω S.A (Φb^[3] β) 0 := by simpa [JCΦ] using S.A_jc hβ
  exact J_diff_jets_Y S.hΩ hβ8 v e hV hA hθ (fun p hp => S.A_mem hp) (fun q hq => S.hz hq) (S.hode v θ e hψ)
    (fun q hq => S.V_bounds hq) hT hH hτ hHT hseg hA0 hAm hY hY0 hn

/-- `(fct:dJ-jets)`, first two lines, with the weight `max(Y, A_0)`, `A_0 = A(p₀)`: the segment `p₀ + t v` lies on rays down to
`ℓ = 0` (`ZeroPath`) at constant `ℓ`. -/
theorem dJ_jets_A0 {β : ℝ} (hβ : 4 ≤ β)
    (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) (v : P) (θ : P × ℝ → ℝ) (e : ℝ)
    {H : ℝ → ℝ} {T : Set ℝ} {τ2 : ℝ}
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    (hT : IsOpen T) (hH : JCΦ 16 T H (Φb^[3] β) 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ2 * (q.2 * S.V q ^ 2) ∈ T)
    {p0 : P} (hzp : ∀ t ∈ Icc (0 : ℝ) 1, S.ZeroPath (p0 + t • v))
    (hℓ : ∀ t ∈ Icc (0 : ℝ) 1, S.ℓ (p0 + t • v) = S.ℓ p0) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ}
    (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => Jfun S.V H τ2 (p0 + v, s)) Y - iteratedDeriv n (fun s : ℝ => Jfun S.V H τ2 (p0, s)) Y| ≤
      |e| * (16 * CJ n (Φb^[3] β)) * max Y (S.A p0) ^ (4 - n) := by
  have h00 : S.ZeroPath p0 := by simpa using hzp 0 (left_mem_Icc.mpr zero_le_one)
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v) ∧ S.A (p0 + t • v) ≤ 2 * S.A p0 := fun t ht => by
    have := S.A_comp hρ h00 (hzp t ht) (hℓ t ht)
    exact ⟨(S.A_comp hρ (hzp t ht) (hzp t ht) rfl).1, this.2⟩
  have h := S.dJ_jets hβ v θ e hψ hθ hT hH hτ hHT (fun t ht => (hzp t ht).1) (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2) hY hY0 hn
  have hA0 : 0 ≤ S.A p0 := (S.A_comp hρ h00 h00 rfl).1
  refine h.trans ?_
  have hK : 0 ≤ |e| * CJ n (Φb^[3] β) := by
    have : 0 ≤ Φb^[3] β := Φb_iter_nonneg (by linarith) 3
    exact mul_nonneg (abs_nonneg _) (CJ_nonneg n this)
  have := max_two_pow_le hY0 hA0 (m := 4 - n) (by omega)
  calc _ = |e| * CJ n (Φb^[3] β) * max Y (2 * S.A p0) ^ (4 - n) := by ring
    _ ≤ |e| * CJ n (Φb^[3] β) * (16 * max Y (S.A p0) ^ (4 - n)) := mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

/-- `(fct:dJ-jets)`, third line, for the chart: `|∂_Y^n ∂_u (J(p₀+v) - J(p₀))| ≤ C |e| max(Y, A_max)^{max(0,3-n)}`, `n ≤ 12`. -/
theorem dJ_jets_u {β : ℝ} (hβ : 4 ≤ β) (v u : P) (hu : ‖u‖ ≤ 1) (θ : P × ℝ → ℝ) (e : ℝ) {H : ℝ → ℝ} {T : Set ℝ}
    {τ2 : ℝ}
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    (hT : IsOpen T) (hH : JCΦ 16 T H (Φb^[3] β) 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ2 * (q.2 * S.V q ^ 2) ∈ T)
    {p0 : P} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p0 + t • v ∈ S.Ω) (hA0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v)) {Amax : ℝ}
    (hAm : ∀ t ∈ Icc (0 : ℝ) 1, S.A (p0 + t • v) ≤ Amax) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ} (hn : n ≤ 12) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun S.V H τ2) (p0 + v, s) (u, 0)) Y -
        iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun S.V H τ2) (p0, s) (u, 0)) Y| ≤
      |e| * CJu n (Φb^[3] β) * max Y Amax ^ (3 - n) := by
  have hβ8 : 8 ≤ Φb^[3] β := by
    have h1 := Φb_ge2 β
    have h2 : Φb^[1] β ≤ Φb^[3] β := Φb_iter_mono (by norm_num) β
    have h3 : max 1 β = β := max_eq_right (by linarith)
    simp only [Function.iterate_one] at h2
    linarith
  have hV : JCΦ 16 (S.Ω ×ˢ Yint) S.V (Φb^[3] β) 0 := by
    have := (S.V_jc hβ).mono_m (show 1 ≤ 3 by norm_num)
    simpa [JCΦ] using this
  have hA : JCΦ 16 S.Ω S.A (Φb^[3] β) 0 := by simpa [JCΦ] using S.A_jc hβ
  exact Ju_diff_jets_Y S.hΩ hβ8 v u hu e hV hA hθ (fun p hp => S.A_mem hp) (fun q hq => S.hz hq) (S.hode v θ e hψ)
    (fun q hq => S.V_bounds hq) hT hH hτ hHT hseg hA0 hAm hY hY0 hn

/-- `(fct:dJ-jets)`, third line, with the weight `max(Y, A_0)`, `A_0 = A(p₀)`, for the segment `p₀ + t v` at constant `ℓ`. -/
theorem dJ_jets_u_A0 {β : ℝ} (hβ : 4 ≤ β)
    (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) (v u : P) (hu : ‖u‖ ≤ 1)
    (θ : P × ℝ → ℝ) (e : ℝ) {H : ℝ → ℝ} {T : Set ℝ} {τ2 : ℝ}
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    (hT : IsOpen T) (hH : JCΦ 16 T H (Φb^[3] β) 0) (hτ : |τ2| ≤ 1)
    (hHT : ∀ q ∈ S.Ω ×ˢ Yint, τ2 * (q.2 * S.V q ^ 2) ∈ T)
    {p0 : P} (hzp : ∀ t ∈ Icc (0 : ℝ) 1, S.ZeroPath (p0 + t • v))
    (hℓ : ∀ t ∈ Icc (0 : ℝ) 1, S.ℓ (p0 + t • v) = S.ℓ p0) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ}
    (hn : n ≤ 12) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun S.V H τ2) (p0 + v, s) (u, 0)) Y -
        iteratedDeriv n (fun s : ℝ => fderiv ℝ (Jfun S.V H τ2) (p0, s) (u, 0)) Y| ≤
      |e| * (16 * CJu n (Φb^[3] β)) * max Y (S.A p0) ^ (3 - n) := by
  have h00 : S.ZeroPath p0 := by simpa using hzp 0 (left_mem_Icc.mpr zero_le_one)
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v) ∧ S.A (p0 + t • v) ≤ 2 * S.A p0 := fun t ht => by
    have := S.A_comp hρ h00 (hzp t ht) (hℓ t ht)
    exact ⟨(S.A_comp hρ (hzp t ht) (hzp t ht) rfl).1, this.2⟩
  have h := S.dJ_jets_u hβ v u hu θ e hψ hθ hT hH hτ hHT (fun t ht => (hzp t ht).1) (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2) hY hY0 hn
  have hA0 : 0 ≤ S.A p0 := (S.A_comp hρ h00 h00 rfl).1
  refine h.trans ?_
  have hK : 0 ≤ |e| * CJu n (Φb^[3] β) := by
    have : 0 ≤ Φb^[3] β := Φb_iter_nonneg (by linarith) 3
    exact mul_nonneg (abs_nonneg _) (CJu_nonneg n this)
  have := max_two_pow_le hY0 hA0 (m := 3 - n) (by omega)
  calc _ = |e| * CJu n (Φb^[3] β) * max Y (2 * S.A p0) ^ (3 - n) := by ring
    _ ≤ |e| * CJu n (Φb^[3] β) * (16 * max Y (S.A p0) ^ (3 - n)) := mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

end ChartSetup

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.dJ_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.dJ_jets

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.dJ_jets_A0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.dJ_jets_A0

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.dJ_jets_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.dJ_jets_u

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.dJ_jets_u_A0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.dJ_jets_u_A0

end DJet
end FormalResearch.SignUncertainty
