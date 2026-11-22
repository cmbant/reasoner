module

public import FormalResearch.ModularBootstrap.FixedWeight.DualMajorant
public import FormalResearch.ModularBootstrap.Duality.MomentProblem

/-!
# Fixed-Weight Finite Moment Problems for Theorem E (`dual_spectrum.tex`, `ds:E`(a))

Generalises `Duality.MomentProblem` from `virasoroProblem` to every `prob : FixedWeightProblem`
with `c̃ > 0`, `c̃ ≥ 12 S`, and `T_V(c̃) > 0`:

* `DualSetup prob cTilde β₀ T₀`: standing hypotheses of Theorem E (`c̃ > 0`, `c̃ ≥ 12 S`,
  `0 < β₀ ≤ 1/2`, `t₀^*(w, β₀) ≤ T₀`, `0 < T₀ < T_V(c̃)`), with conversions to/from
  `Duality.DualSetup` at `virasoroProblem`.
* `crossingRHS prob a β`: `∫₀^∞ Ξ_β^{(w)}(t) ρ_C(t) dt`.
* `dual_inequality`, `exists_atomic_approx`: Theorem E(a) for every `(w, Q)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-- Standing hypotheses of Theorem E (`dual_spectrum.tex`, "Strong duality with attainment")
for a fixed-weight problem `prob`: `c̃ > 0`, `c̃ ≥ 12 ∑ μ_l`, `0 < T₀ < T_V(c̃)`, and
`β₀ ∈ (0, 1/2]` with `t₀^*(w, β₀) ≤ T₀`. -/
structure DualSetup (prob : FixedWeightProblem) (cTilde β₀ T₀ : ℝ) : Prop where
  hc_pos : 0 < cTilde
  hc : 12 * prob.totalShift ≤ cTilde
  hβ₀ : 0 < β₀
  hβ₀2 : β₀ ≤ 1 / 2
  hT₀ : t0Star prob.w β₀ ≤ T₀
  hT₀pos : 0 < T₀
  hT₀V : T₀ < prob.T_V cTilde

lemma DualSetup.ha {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}
    (h : DualSetup prob cTilde β₀ T₀) : prob.totalShift ≤ cTilde / 12 := by
  linarith [h.hc]

lemma DualSetup.ha_pos {prob : FixedWeightProblem} {cTilde β₀ T₀ : ℝ}
    (h : DualSetup prob cTilde β₀ T₀) : 0 < cTilde / 12 := by
  linarith [h.hc_pos]

/-- Convert a Virasoro `Duality.DualSetup` to `FixedWeight.DualSetup virasoroProblem`. -/
lemma DualSetup.of_virasoro {cTilde β₀ T₀ : ℝ} (h : Duality.DualSetup cTilde β₀ T₀) :
    DualSetup virasoroProblem cTilde β₀ T₀ where
  hc_pos := by have := h.hc; rw [virasoroProblem_totalShift] at this; linarith
  hc := h.hc
  hβ₀ := h.hβ₀
  hβ₀2 := h.hβ₀2
  hT₀ := by
    rw [t0Star_eq_t0 h.hβ₀ (by linarith [h.hβ₀2]), virasoroProblem_w, t0_one]
    exact h.hT₀
  hT₀pos := h.hT₀pos
  hT₀V := h.hT₀V

/-- Convert `FixedWeight.DualSetup virasoroProblem` back to `Duality.DualSetup`. -/
lemma DualSetup.to_virasoro {cTilde β₀ T₀ : ℝ} (h : DualSetup virasoroProblem cTilde β₀ T₀) :
    Duality.DualSetup cTilde β₀ T₀ where
  hc := h.hc
  hβ₀ := h.hβ₀
  hβ₀2 := h.hβ₀2
  hT₀ := by
    have ht := h.hT₀
    rwa [t0Star_eq_t0 h.hβ₀ (by linarith [h.hβ₀2]), virasoroProblem_w, t0_one] at ht
  hT₀pos := h.hT₀pos
  hT₀V := h.hT₀V

/-- The crossing right-hand side `a_β = ∫₀^∞ Ξ_β^{(w)}(t) ρ_C(t) dt` (`ρ_C = 2π V`). -/
noncomputable def crossingRHS (prob : FixedWeightProblem) (a β : ℝ) : ℝ :=
  ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyDensity a t

lemma gVac_thermalDiff_eq_neg (prob : FixedWeightProblem) (a β : ℝ) :
    prob.gVac a (thermalDiff prob.w β) = -crossingRHS prob a β := by
  unfold FixedWeightProblem.gVac crossingRHS FixedWeightProblem.cardyDensity
  have heq : (fun t => thermalDiff prob.w β t * (2 * π * prob.cardyV a t)) =
      fun t => (2 * π) * (thermalDiff prob.w β t * prob.cardyV a t) := by ext t; ring
  rw [heq, integral_const_mul]
  ring

/-- No feasible test exists at `T < T_V`. -/
lemma not_feasible_of_lt_T_V (prob : FixedWeightProblem) {cTilde T : ℝ}
    (hT : 0 < T) (hTV : T < prob.T_V cTilde) {g : ℝ → ℝ} (hg : prob.IsFeasible (cTilde / 12) T g) :
    False := by
  have : prob.T_V cTilde ≤ T := by
    unfold FixedWeightProblem.T_V
    exact csInf_le ⟨0, fun T' hT' => hT'.1.le⟩ ⟨hT, g, hg⟩
  linarith

/-- The dual inequality at general `(w, Q)`: any `(l, μ)` with `μ ≥ 0` and
`∑ l_i Ξ_{β_i}/w_* + μ ≥ 0` on `[T, ∞)` satisfies `∑ l_i a_{β_i} + μ C₀ ≥ 0`
(otherwise `g_λ + μ h` would be feasible at `T < T_V`). -/
lemma dual_inequality (prob : FixedWeightProblem) {cTilde β₀ T₀ T : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) (hT₀T : T₀ ≤ T) (hTV : T < prob.T_V cTilde)
    {ι : Type*} [Fintype ι] (β : ι → ℝ) (hβ : ∀ i, 0 < β i)
    (l : ι → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hnn : ∀ t, T ≤ t →
      0 ≤ ∑ i, l i * (thermalDiff prob.w (β i) t / wStar (cTilde / 12) β₀ t) + μ) :
    0 ≤ ∑ i, l i * crossingRHS prob (cTilde / 12) (β i) + μ * dualC0 prob (cTilde / 12) β₀ := by
  by_contra hneg
  push Not at hneg
  have ha := S.ha
  have ha0 := S.ha_pos
  have hTpos : 0 < T := lt_of_lt_of_le S.hT₀pos hT₀T
  set a := cTilde / 12 with ha_def
  let g : ℝ → ℝ := fun t => (∑ i, l i * thermalDiff prob.w (β i) t) + μ * hMaj prob.w a β₀ t
  have hXi : ∀ i, TestClass prob a (thermalDiff prob.w (β i)) := fun i =>
    thermalDiff_mem_TestClass prob ha (hβ i)
  have hsum := Duality.testClass_sum (a := a) (Finset.univ : Finset ι) l
    (fun i => thermalDiff prob.w (β i)) (fun i _ => hXi i)
  have hhM := hMaj_mem_TestClass prob (β₀ := β₀) ha ha0
  have hgT : TestClass prob a g := hsum.add (hhM.smul μ)
  have hvac : prob.gVac a g =
      ∑ i, l i * prob.gVac a (thermalDiff prob.w (β i)) + μ * prob.gVac a (hMaj prob.w a β₀) := by
    have := prob.gVac_add hsum (hhM.smul μ)
    rw [prob.gVac_smul μ hhM, Duality.gVac_sum _ l _ (fun i _ => hXi i)] at this
    exact this
  have hvac' : prob.gVac a g =
      -(∑ i, l i * crossingRHS prob a (β i) + μ * dualC0 prob a β₀) := by
    rw [hvac, hMaj_vac prob ha ha0]
    simp_rw [gVac_thermalDiff_eq_neg]
    have hsum_neg : ∑ i, l i * -crossingRHS prob a (β i) = -∑ i, l i * crossingRHS prob a (β i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_neg]
    ring
  refine not_feasible_of_lt_T_V prob (cTilde := cTilde) hTpos hTV (g := g) ⟨hgT, ?_, ?_⟩
  · rw [hvac']; linarith
  · intro t ht
    have hw := wStar_pos ha0.le S.hβ₀ (hTpos.le.trans ht)
    have hM := wStar_le_hMaj prob.hw ha0 S.hβ₀ (by linarith [S.hβ₀2]) S.hT₀ (hT₀T.trans ht)
    have h1 := hnn t ht
    have h2 : 0 ≤ (∑ i, l i * thermalDiff prob.w (β i) t + μ * wStar a β₀ t) / wStar a β₀ t := by
      have heq : (∑ i, l i * thermalDiff prob.w (β i) t + μ * wStar a β₀ t) / wStar a β₀ t =
          ∑ i, l i * (thermalDiff prob.w (β i) t / wStar a β₀ t) + μ := by
        rw [add_div, Finset.sum_div, mul_div_assoc, div_self hw.ne', mul_one]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [heq]; exact h1
    have h4 : 0 ≤ ∑ i, l i * thermalDiff prob.w (β i) t + μ * wStar a β₀ t := by
      rcases div_nonneg_iff.mp h2 with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h (not_le.mpr hw)
    show 0 ≤ (∑ i, l i * thermalDiff prob.w (β i) t) + μ * hMaj prob.w a β₀ t
    nlinarith [mul_le_mul_of_nonneg_left hM hμ]

/-- **Theorem E(a) (`dual_spectrum.tex`, `ds:E`)** for every fixed weight `(w, Q)`:
for `T₀ ≤ T < T_V(c̃)`, a finite set `B ⊂ (0, ∞)`, and `ε > 0`, there is a finite positive atomic
measure `∑_k (c_k / w_*(t_k)) δ_{t_k}` on `[T, ∞)` with `∑ c_k ≤ C₀` and
`|∫ Ξ_β dν - ∫ Ξ_β ρ_C dt| < ε` for `β ∈ B`. -/
theorem exists_atomic_approx (prob : FixedWeightProblem) {cTilde β₀ T₀ T : ℝ}
    (S : DualSetup prob cTilde β₀ T₀) (hT₀T : T₀ ≤ T) (hTV : T < prob.T_V cTilde)
    (B : Finset ℝ) (hB : ∀ β ∈ B, 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℝ), (∀ k, T ≤ t k) ∧ (∀ k, 0 ≤ c k) ∧
      ∑ k, c k ≤ dualC0 prob (cTilde / 12) β₀ ∧
      ∀ β ∈ B, |∑ k, c k * (thermalDiff prob.w β (t k) / wStar (cTilde / 12) β₀ (t k)) -
        crossingRHS prob (cTilde / 12) β| < ε := by
  have hC0 : 0 < dualC0 prob (cTilde / 12) β₀ :=
    dualC0_pos prob S.ha_pos S.hβ₀ (by linarith [S.hβ₀2])
  obtain ⟨N, x, c, hc, hs, hd⟩ := farkas_approx (ι := B) (X := {t : ℝ // T ≤ t})
    (fun i x => thermalDiff prob.w i x.1 / wStar (cTilde / 12) β₀ x.1)
    (fun i => crossingRHS prob (cTilde / 12) i) hC0
    (fun l μ hμ hnn => dual_inequality prob S hT₀T hTV (fun i : B => (i : ℝ))
      (fun i => hB i i.2) l hμ (fun t ht => hnn ⟨t, ht⟩)) hε
  refine ⟨N, fun k => (x k).1, c, fun k => (x k).2, hc, hs, fun β hβ => ?_⟩
  exact hd ⟨β, hβ⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.dual_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.dual_inequality

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_atomic_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_atomic_approx

end FormalResearch.ModularBootstrap.FixedWeight