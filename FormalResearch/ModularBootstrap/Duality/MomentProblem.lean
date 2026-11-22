module

public import FormalResearch.ModularBootstrap.Duality.DualMajorant
public import FormalResearch.ModularBootstrap.Duality.Farkas

/-!
# Finite moment problems for Theorem E (`dual_spectrum.tex`, `ds:E`(a))

For `T₀ ≤ T < T_V` the finitely many crossing equations `∫ Ξ_β dν = ∫ Ξ_β ρ_C dt`
(`β` in a finite set `B`) have, up to any `ε > 0`, a positive atomic solution `ν` on `[T, ∞)` with
`∫ w_* dν ≤ C₀`. This is the finite-dimensional separation argument of the paper
(Lemma M(b) is what turns a separating `(λ, μ)` into a feasible test `g_λ + μ h ∈ \overline{\mathcal A}`
at `T`, contradicting `T < T_V`).

The paper uses the Laguerre functions `ψ_k` (odd `k ≤ 2P-1`) as the finite family; here the family
is `{Ξ_β : β ∈ B}` for finite `B ⊂ (0, ∞)`. This avoids Laguerre polynomials and the
`MehlerOddMomentInput`-type equivalence of odd moments with all `Ξ_β` (the limit step then gives
the crossing equation for all `β > 0` at once).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

/-- The standing hypotheses of Theorem E (`dual_spectrum.tex`, "Strong duality with attainment"):
the Virasoro problem at `c̃ = c' = c - 1 ≥ 24` (the paper takes `c ≥ 40`), `T_V(c) > 0` (here
`T₀ ∈ (0, T_V)`), and `β₀ ∈ (0, 1/2]` with `t₀(β₀) ≤ T₀`. -/
structure DualSetup (cTilde β₀ T₀ : ℝ) : Prop where
  hc : 12 * virasoroProblem.totalShift ≤ cTilde
  hβ₀ : 0 < β₀
  hβ₀2 : β₀ ≤ 1 / 2
  hT₀ : t0 β₀ ≤ T₀
  hT₀pos : 0 < T₀
  hT₀V : T₀ < virasoroProblem.T_V cTilde

lemma DualSetup.ha {cTilde β₀ T₀ : ℝ} (h : DualSetup cTilde β₀ T₀) : 2 ≤ cTilde / 12 := by
  have := h.hc; rw [virasoroProblem_totalShift] at this; linarith

/-! ### Finite sums of test functions -/

lemma testClass_zero (prob : FixedWeightProblem) (a : ℝ) : TestClass prob a (fun _ => 0) where
  cont := continuousOn_const
  int_lift := by
    have : radialLift prob.w (fun _ => (0 : ℝ)) = fun _ => 0 := by ext x; simp [radialLift]
    rw [this]; exact integrable_zero _ _ _
  fourier_odd := by
    have : radialLift prob.w (fun _ => (0 : ℝ)) = fun _ => 0 := by ext x; simp [radialLift]
    rw [this]; ext ξ; simp [Real.fourier_eq]
  int_cardy := by simp

lemma testClass_sum {prob : FixedWeightProblem} {a : ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, TestClass prob a (g i)) :
    TestClass prob a (fun t => ∑ i ∈ s, c i * g i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using testClass_zero prob a
  | insert j s hj ih =>
    have h1 := (hg j (Finset.mem_insert_self _ _)).smul (c j)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have := h1.add h2
    simpa [Finset.sum_insert hj] using this

lemma gVac_sum {prob : FixedWeightProblem} {a : ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, TestClass prob a (g i)) :
    prob.gVac a (fun t => ∑ i ∈ s, c i * g i t) = ∑ i ∈ s, c i * prob.gVac a (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold FixedWeightProblem.gVac; simp
  | insert j s hj ih =>
    have h1 := (hg j (Finset.mem_insert_self _ _)).smul (c j)
    have h2 := testClass_sum (a := a) s c g fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have e : (fun t => ∑ i ∈ insert j s, c i * g i t) =
        fun t => c j * g j t + ∑ i ∈ s, c i * g i t := by
      ext t; rw [Finset.sum_insert hj]
    rw [e, prob.gVac_add h1 h2, prob.gVac_smul _ (hg j (Finset.mem_insert_self _ _)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi), Finset.sum_insert hj]

/-- The crossing right-hand side `a_β = ∫ Ξ_β ρ_C dt` (`ρ_C = 2π V`). -/
noncomputable def crossingRHS (a β : ℝ) : ℝ :=
  ∫ t in Ioi 0, thermalDiff 1 β t * virasoroProblem.cardyDensity a t

lemma gVac_thermalDiff_eq_neg {a : ℝ} (β : ℝ) :
    virasoroProblem.gVac a (thermalDiff 1 β) = -crossingRHS a β := by
  unfold FixedWeightProblem.gVac crossingRHS FixedWeightProblem.cardyDensity
  have : (fun t => thermalDiff 1 β t * (2 * π * virasoroProblem.cardyV a t)) =
      fun t => (2 * π) * (thermalDiff 1 β t * virasoroProblem.cardyV a t) := by ext t; ring
  rw [this, integral_const_mul]; ring

/-- No feasible test exists at `T < T_V` (strict feasibility of `g` at `T > 0` forces `T_V ≤ T`). -/
lemma not_feasible_of_lt_T_V {cTilde T : ℝ} (hT : 0 < T) (hTV : T < virasoroProblem.T_V cTilde)
    {g : ℝ → ℝ} (hg : virasoroProblem.IsFeasible (cTilde / 12) T g) : False := by
  have : virasoroProblem.T_V cTilde ≤ T := by
    unfold FixedWeightProblem.T_V
    exact csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT, g, hg⟩
  linarith

/-- The dual inequality: any `(l, μ)` with `μ ≥ 0` and `Σ l_i Ξ_{β_i}/w_* + μ ≥ 0` on `[T, ∞)`
satisfies `Σ l_i a_{β_i} + μ C₀ ≥ 0` (else `g_λ + μ h` would be feasible at `T < T_V`). -/
lemma dual_inequality {cTilde β₀ T₀ T : ℝ} (S : DualSetup cTilde β₀ T₀) (hT₀T : T₀ ≤ T)
    (hTV : T < virasoroProblem.T_V cTilde) {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (hβ : ∀ i, 0 < β i) (l : ι → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hnn : ∀ t, T ≤ t →
      0 ≤ ∑ i, l i * (thermalDiff 1 (β i) t / wStar (cTilde / 12) β₀ t) + μ) :
    0 ≤ ∑ i, l i * crossingRHS (cTilde / 12) (β i) + μ * dualC0 (cTilde / 12) β₀ := by
  by_contra hneg
  push Not at hneg
  have ha := S.ha
  have ha0 : 0 < cTilde / 12 := by linarith
  have hts : virasoroProblem.totalShift ≤ cTilde / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  have hTpos : 0 < T := lt_of_lt_of_le S.hT₀pos hT₀T
  set a := cTilde / 12 with ha_def
  let g : ℝ → ℝ := fun t => (∑ i, l i * thermalDiff 1 (β i) t) + μ * hMaj a β₀ t
  have hXi : ∀ i, TestClass virasoroProblem a (thermalDiff 1 (β i)) := fun i =>
    thermalDiff_mem_TestClass virasoroProblem hts (hβ i)
  have hsum := testClass_sum (a := a) (Finset.univ : Finset ι) l (fun i => thermalDiff 1 (β i))
    (fun i _ => hXi i)
  have hhM := hMaj_mem_TestClass (β₀ := β₀) ha
  have hgT : TestClass virasoroProblem a g := hsum.add (hhM.smul μ)
  have hvac : virasoroProblem.gVac a g =
      ∑ i, l i * virasoroProblem.gVac a (thermalDiff 1 (β i)) + μ * virasoroProblem.gVac a (hMaj a β₀) := by
    have := virasoroProblem.gVac_add hsum (hhM.smul μ)
    rw [virasoroProblem.gVac_smul μ hhM, gVac_sum _ l _ (fun i _ => hXi i)] at this
    exact this
  have hvac' : virasoroProblem.gVac a g =
      -(∑ i, l i * crossingRHS a (β i) + μ * dualC0 a β₀) := by
    rw [hvac, hMaj_vac ha]
    simp only [gVac_thermalDiff_eq_neg]
    have : ∑ i, l i * -crossingRHS a (β i) = -∑ i, l i * crossingRHS a (β i) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  refine not_feasible_of_lt_T_V (cTilde := cTilde) hTpos hTV (g := g) ⟨hgT, ?_, ?_⟩
  · rw [hvac']; linarith
  · intro t ht
    have hw := wStar_pos ha0.le S.hβ₀ (hTpos.le.trans ht)
    have hM := wStar_le_hMaj ha0 S.hβ₀ S.hβ₀2 S.hT₀ (hT₀T.trans ht)
    have h1 := hnn t ht
    have h2 : 0 ≤ (∑ i, l i * thermalDiff 1 (β i) t + μ * wStar a β₀ t) / wStar a β₀ t := by
      have : (∑ i, l i * thermalDiff 1 (β i) t + μ * wStar a β₀ t) / wStar a β₀ t =
          ∑ i, l i * (thermalDiff 1 (β i) t / wStar a β₀ t) + μ := by
        rw [add_div, Finset.sum_div, mul_div_assoc, div_self hw.ne', mul_one]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; exact h1
    have h3 := (div_nonneg_iff.1 h2)
    have h4 : 0 ≤ ∑ i, l i * thermalDiff 1 (β i) t + μ * wStar a β₀ t := by
      rcases h3 with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h (not_le.2 hw)
    show 0 ≤ (∑ i, l i * thermalDiff 1 (β i) t) + μ * hMaj a β₀ t
    nlinarith [mul_le_mul_of_nonneg_left hM hμ]

/-- **Theorem E(a) (finite-order form).** For `T₀ ≤ T < T_V`, a finite set `B` of positive `β`
and `ε > 0` there is a finite positive atomic measure `Σ_k (c_k / w_*(t_k)) δ_{t_k}` on `[T, ∞)`
(here recorded by its points `t_k ≥ T` and weights `c_k ≥ 0` for `w_* dν`) with
`Σ c_k ≤ C₀` and `|∫ Ξ_β dν - ∫ Ξ_β ρ_C dt| < ε` for `β ∈ B`. -/
theorem exists_atomic_approx {cTilde β₀ T₀ T : ℝ} (S : DualSetup cTilde β₀ T₀) (hT₀T : T₀ ≤ T)
    (hTV : T < virasoroProblem.T_V cTilde) (B : Finset ℝ) (hB : ∀ β ∈ B, 0 < β) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℝ), (∀ k, T ≤ t k) ∧ (∀ k, 0 ≤ c k) ∧
      ∑ k, c k ≤ dualC0 (cTilde / 12) β₀ ∧
      ∀ β ∈ B, |∑ k, c k * (thermalDiff 1 β (t k) / wStar (cTilde / 12) β₀ (t k)) -
        crossingRHS (cTilde / 12) β| < ε := by
  have hC0 : 0 < dualC0 (cTilde / 12) β₀ := dualC0_pos S.ha S.hβ₀ S.hβ₀2
  obtain ⟨N, x, c, hc, hs, hd⟩ := farkas_approx (ι := B) (X := {t : ℝ // T ≤ t})
    (fun i x => thermalDiff 1 i x.1 / wStar (cTilde / 12) β₀ x.1)
    (fun i => crossingRHS (cTilde / 12) i) hC0
    (fun l μ hμ hnn => dual_inequality S hT₀T hTV (fun i : B => (i : ℝ))
      (fun i => hB i i.2) l hμ (fun t ht => hnn ⟨t, ht⟩)) hε
  refine ⟨N, fun k => (x k).1, c, fun k => (x k).2, hc, hs, fun β hβ => ?_⟩
  exact hd ⟨β, hβ⟩

/-- info: 'FormalResearch.ModularBootstrap.Duality.dual_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.dual_inequality

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_atomic_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_atomic_approx

end FormalResearch.ModularBootstrap.Duality
